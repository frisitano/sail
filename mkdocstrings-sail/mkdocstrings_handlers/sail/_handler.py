"""mkdocstrings handler for Sail.

Renders definitions from a ``sail --doc`` docinfo bundle: heading with a
stable ``<kind>-<id>`` anchor, doc comment as Markdown, and the definition
source highlighted with the bundled Sail lexer. Function calls and register
uses *inside* the source are wrapped in ``<autoref>`` elements, which
mkdocs-autorefs resolves to wherever those definitions are rendered in the
site — cross-page, with no path computation here.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, ClassVar, Mapping, Optional

from markupsafe import Markup, escape
from mkdocstrings import BaseHandler, CollectionError, get_logger
from pygments.token import STANDARD_TYPES, Text as TextToken

from ._bundle import Bundle, BundleError, Clause, Definition
from ._index import IndexReference, LspIndex
from ._lexer import SailLexer

logger = get_logger(__name__)

_DEFAULT_OPTIONS: dict[str, Any] = {
    "kind": None,  # restrict lookup to one definition kind (function, type, ...)
    "heading_level": 2,
    "show_comment": True,
    "show_source": True,
    "link_code": True,
    "toc_label": None,
}


def _token_class(ttype) -> str:
    while ttype is not None:
        cls = STANDARD_TYPES.get(ttype)
        if cls is not None:
            return cls
        ttype = ttype.parent
    return ""


def _comment_summary(comment: Optional[str]) -> Optional[str]:
    """First sentence of a doc comment as tooltip-safe plain text."""
    if not comment:
        return None
    text = " ".join(comment.replace("`", "").replace("*", "").split())
    for stop in (". ", ".\n"):
        if stop in text:
            text = text[: text.index(stop) + 1]
            break
    return text[:140] or None


def _lexical_tokens(text: str) -> list[tuple[int, int, str]]:
    """Fallback highlight segments from the bundled regex lexer."""
    tokens = []
    for pos, ttype, value in SailLexer().get_tokens_unprocessed(text):
        cls = _token_class(ttype) if ttype is not TextToken else ""
        tokens.append((pos, pos + len(value), cls))
    return tokens


def _highlight_linked(
    text: str, links: list[tuple[int, int, str]], tokens: list[tuple[int, int, str]] | None = None
) -> str:
    """Render source as HTML, wrapping link spans in <autoref> elements.

    ``links`` are non-overlapping (relative start, relative end, anchor)
    triples; ``tokens`` are non-overlapping (start, end, css class)
    highlight segments (semantic when a sail-lsp index is configured,
    lexical otherwise). Segments are split at every boundary so anchors and
    highlight spans nest cleanly.
    """
    if tokens is None:
        tokens = _lexical_tokens(text)
    # links may be (start, end, anchor) or (start, end, anchor, tooltip)
    links = sorted(
        ((start, end, anchor, rest[0] if rest else None) for start, end, anchor, *rest in links),
        key=lambda link: link[:3],
    )
    tokens = sorted(tokens)

    bounds = {0, len(text)}
    for start, end, _, _ in links:
        bounds.update((start, end))
    for start, end, _ in tokens:
        bounds.update((start, end))
    points = sorted(p for p in bounds if 0 <= p <= len(text))

    out = []
    open_until = None
    close_tag = ""
    link_i = 0
    token_i = 0
    for a, b in zip(points, points[1:]):
        if open_until is not None and a >= open_until:
            out.append(close_tag)
            open_until = None
        while link_i < len(links) and links[link_i][1] <= a:
            link_i += 1
        if open_until is None and link_i < len(links) and links[link_i][0] == a:
            _, end, anchor, tooltip = links[link_i]
            out.append(f'<autoref identifier="{escape(anchor)}" optional>')
            if tooltip:
                out.append(f'<span title="{escape(tooltip)}">')
                close_tag = "</span></autoref>"
            else:
                close_tag = "</autoref>"
            open_until = end
        while token_i < len(tokens) and tokens[token_i][1] <= a:
            token_i += 1
        cls = ""
        if token_i < len(tokens) and tokens[token_i][0] <= a < tokens[token_i][1]:
            cls = tokens[token_i][2]
        segment = escape(text[a:b])
        out.append(f'<span class="{cls}">{segment}</span>' if cls else str(segment))
    if open_until is not None:
        out.append(close_tag)
    return "".join(out)


class SailHandler(BaseHandler):
    """A mkdocstrings handler backed by Sail docinfo bundles."""

    name: ClassVar[str] = "sail"
    domain: ClassVar[str] = "sail"
    fallback_theme: ClassVar[str] = "material"

    extra_css = """
    .sail-source .autorefs { color: inherit; border-bottom: 1px dotted currentcolor; }
    .sail-source .autorefs:hover { border-bottom-style: solid; }
    .doc-sail-kind { font-size: 0.65em; font-weight: 400; opacity: 0.7; margin-right: 0.4em; }
    """

    def __init__(self, config: Mapping[str, Any], base_dir: Path, **kwargs: Any) -> None:
        super().__init__(**kwargs)
        bundle = config.get("bundle")
        if bundle is None:
            raise CollectionError("The Sail handler needs a 'bundle' path (sail --doc output) in its configuration")
        self._bundle_path = Path(base_dir, bundle)
        self._bundle: Optional[Bundle] = None
        lsp_index = config.get("lsp_index")
        self._lsp_index_path = Path(base_dir, lsp_index) if lsp_index else None
        self._lsp_index: Optional[LspIndex] = None
        self._global_options: Mapping[str, Any] = config.get("options", {})

    @property
    def bundle(self) -> Bundle:
        if self._bundle is None:
            try:
                self._bundle = Bundle.load(self._bundle_path)
            except BundleError as error:
                raise CollectionError(str(error)) from error
        return self._bundle

    @property
    def lsp_index(self) -> Optional[LspIndex]:
        if self._lsp_index is None and self._lsp_index_path is not None:
            try:
                self._lsp_index = LspIndex.load(self._lsp_index_path)
            except (OSError, ValueError, json.JSONDecodeError) as error:
                raise CollectionError(f"Cannot load sail-lsp index {self._lsp_index_path}: {error}") from error
        return self._lsp_index

    # sail/sourceMap kinds -> docinfo bundle kinds for direct anchor lookup
    _REF_KINDS = {
        "type": "type",
        "union": "type",
        "struct": "type",
        "enum": "type",
        "register": "register",
        "mapping": "mapping",
        "let": "let",
        "constant": "let",
    }

    def _resolve_reference(self, ref: IndexReference) -> tuple[Optional[str], Optional[Definition]]:
        if ref.kind in ("function", "val"):
            try:
                definition = self.bundle.find(ref.name)
                return definition.anchor, definition
            except BundleError:
                return None, None
        mapped = self._REF_KINDS.get(ref.kind)
        if mapped is not None:
            try:
                definition = self.bundle.find(ref.name, kind=mapped)
                return definition.anchor, definition
            except BundleError:
                pass
        # constructors, enum members, and anything else docinfo has no
        # section for: anchor at whichever definition contains the target
        owner = self.bundle.definition_at(ref.target_file, ref.target_start)
        return (owner.anchor, owner) if owner else (None, None)

    def _tooltip(self, signature: Optional[str], definition: Optional[Definition]) -> Optional[str]:
        summary = _comment_summary(definition.comment) if definition is not None else None
        if signature and summary:
            return f"{signature} — {summary}"
        return signature or summary

    def _clause_links(self, data: Definition, clause: Clause) -> list[tuple[int, int, str, Optional[str]]]:
        index = self.lsp_index
        links: list[tuple[int, int, str, Optional[str]]] = []
        for start, end, record in clause.records_within(data.links):
            target = None
            try:
                target = self.bundle.find(record.identifier, kind=None if record.kind == "function" else record.kind)
            except BundleError:
                pass
            signature = index.signature(record.kind, record.identifier) if index is not None else None
            links.append((start, end, record.anchor, self._tooltip(signature, target)))
        if index is not None and clause.file is not None and clause.start is not None and index.has_file(clause.file):
            for ref in index.references_within(clause.file, clause.start, clause.end):
                if any(ref.start < end and ref.end > start for start, end, _, _ in links):
                    continue  # docinfo's compiler-proven links win
                anchor, target = self._resolve_reference(ref)
                if anchor is not None:
                    signature = index.signature(ref.kind, ref.name)
                    links.append((ref.start, ref.end, anchor, self._tooltip(signature, target)))
        return sorted(links, key=lambda link: link[:3])

    def _clause_tokens(self, clause: Clause) -> Optional[list[tuple[int, int, str]]]:
        index = self.lsp_index
        if index is not None and clause.file is not None and clause.start is not None and index.has_file(clause.file):
            tokens = index.tokens_within(clause.file, clause.start, clause.end)
            if tokens:
                return tokens
        return None  # fall back to the regex lexer

    def get_options(self, local_options: Mapping[str, Any]) -> Mapping[str, Any]:
        unknown = set(local_options) - set(_DEFAULT_OPTIONS)
        if unknown:
            logger.warning(f"Unknown Sail handler options: {', '.join(sorted(unknown))}")
        return {**_DEFAULT_OPTIONS, **self._global_options, **local_options}

    def collect(self, identifier: str, options: Mapping[str, Any]) -> Definition:
        try:
            return self.bundle.find(identifier, kind=options.get("kind"))
        except BundleError as error:
            raise CollectionError(str(error)) from error

    def get_aliases(self, identifier: str) -> tuple[str, ...]:
        # Called with the rendered heading id ("function-step"); alias the bare
        # identifier ("step") to it when the bare lookup resolves to the same
        # definition, so `[step][]` works in prose.
        kind, _, bare = identifier.partition("-")
        if not bare:
            return ()
        try:
            definition = self.bundle.find(bare)
        except (BundleError, CollectionError):
            return ()
        return (bare,) if definition.anchor == identifier else ()

    def render(self, data: Definition, options: Mapping[str, Any], *, locale: str | None = None) -> str:
        heading_level = int(options["heading_level"])
        parts = [f'<div class="doc doc-sail doc-{escape(data.kind)}">']
        heading = Markup('<span class="doc-sail-kind">{kind} </span><code>{id}</code>').format(
            kind=data.kind, id=data.identifier
        )
        attributes = {}
        signature = self.lsp_index.signature(data.kind, data.identifier) if self.lsp_index is not None else None
        if signature:
            attributes["title"] = signature
        parts.append(
            str(
                self.do_heading(
                    heading,
                    heading_level,
                    role=data.kind,
                    id=data.anchor,
                    toc_label=options.get("toc_label") or data.identifier,
                    **attributes,
                )
            )
        )
        if options["show_comment"] and data.comment:
            parts.append(str(self.do_convert_markdown(data.comment.strip(), heading_level + 1)))
        if options["show_source"]:
            for clause in data.clauses:
                links = self._clause_links(data, clause) if options["link_code"] else []
                code = _highlight_linked(clause.text, links, tokens=self._clause_tokens(clause))
                parts.append(f'<div class="sail-source language-sail highlight"><pre><code>{code}</code></pre></div>')
        parts.append("</div>")
        return "".join(parts)


def get_handler(
    theme: str,
    custom_templates: str | None = None,
    mdx: Any = (),
    mdx_config: Any = None,
    handler_config: Mapping[str, Any] | None = None,
    tool_config: Any = None,
    **kwargs: Any,
) -> SailHandler:
    """Return an instance of the Sail handler (mkdocstrings entry point)."""
    config_file = getattr(tool_config, "config_file_path", None) or (tool_config or {}).get("config_file_path")
    base_dir = Path(config_file).parent if config_file else Path.cwd()
    return SailHandler(
        config=handler_config or {},
        base_dir=base_dir,
        theme=theme,
        custom_templates=custom_templates,
        mdx=mdx,
        mdx_config=mdx_config or {},
    )
