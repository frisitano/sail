"""mkdocstrings handler for Sail.

Renders definitions from a ``sail --doc`` docinfo bundle: heading with a
stable ``<kind>-<id>`` anchor, doc comment as Markdown, and the definition
source highlighted with the bundled Sail lexer. Function calls and register
uses *inside* the source are wrapped in ``<autoref>`` elements, which
mkdocs-autorefs resolves to wherever those definitions are rendered in the
site — cross-page, with no path computation here.
"""

from __future__ import annotations

from pathlib import Path
from typing import Any, ClassVar, Mapping, Optional

from markupsafe import Markup, escape
from mkdocstrings import BaseHandler, CollectionError, get_logger
from pygments.token import STANDARD_TYPES, Text as TextToken

from ._bundle import Bundle, BundleError, Definition
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


def _highlight_linked(text: str, links: list[tuple[int, int, str]]) -> str:
    """Highlight Sail source, wrapping link spans in <autoref> elements.

    ``links`` are non-overlapping (relative start, relative end, anchor)
    triples. Tokens are split at link boundaries so anchors and highlight
    spans nest cleanly.
    """
    bounds = sorted({b for start, end, _ in links for b in (start, end)})
    anchors = {start: (end, anchor) for start, end, anchor in links}

    out = []
    open_until = None

    def emit(pos: int, ttype, value: str) -> None:
        nonlocal open_until
        if open_until is not None and pos >= open_until:
            out.append("</autoref>")
            open_until = None
        if pos in anchors and open_until is None:
            end, anchor = anchors[pos]
            out.append(f'<autoref identifier="{escape(anchor)}" optional>')
            open_until = end
        cls = _token_class(ttype) if ttype is not TextToken else ""
        if cls:
            out.append(f'<span class="{cls}">{escape(value)}</span>')
        else:
            out.append(str(escape(value)))

    for pos, ttype, value in SailLexer().get_tokens_unprocessed(text):
        # split the token at any link boundary that falls inside it
        offset = pos
        remaining = value
        for bound in bounds:
            if offset < bound < offset + len(remaining):
                head, remaining = remaining[: bound - offset], remaining[bound - offset :]
                emit(offset, ttype, head)
                offset = bound
        if remaining:
            emit(offset, ttype, remaining)
    if open_until is not None:
        out.append("</autoref>")
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
        self._global_options: Mapping[str, Any] = config.get("options", {})

    @property
    def bundle(self) -> Bundle:
        if self._bundle is None:
            try:
                self._bundle = Bundle.load(self._bundle_path)
            except BundleError as error:
                raise CollectionError(str(error)) from error
        return self._bundle

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
        heading = Markup('<span class="doc-sail-kind">{kind}</span><code>{id}</code>').format(
            kind=data.kind, id=data.identifier
        )
        parts.append(
            str(
                self.do_heading(
                    heading,
                    heading_level,
                    role=data.kind,
                    id=data.anchor,
                    toc_label=options.get("toc_label") or data.identifier,
                )
            )
        )
        if options["show_comment"] and data.comment:
            parts.append(str(self.do_convert_markdown(data.comment.strip(), heading_level + 1)))
        if options["show_source"]:
            for clause in data.clauses:
                links = clause.links_within(data.links) if options["link_code"] else []
                code = _highlight_linked(clause.text, links)
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
