"""Generate a spec book directly from Sail sources ("literate Sail").

Prose lives in the sources, so no intermediary Markdown files are needed:

- ``/*md ... */`` comments hold Markdown prose. They are ordinary Sail
  comments (ignored by the compiler, preserved by ``sail --fmt``) and are
  interleaved with definitions by source position — a block at the top of a
  file with a ``# Title`` heading is the module doc (and names the page), a
  ``## Section`` block between definitions opens a section, and so on.
- ``/*! ... */`` doc comments attach to the following definition and are
  rendered under its heading, as usual.

For each source file containing definitions, a page is emitted with the
``/*md`` blocks and ``::: name`` directives in source order. Identifiers
already rendered by hand-authored pages under ``docs/`` are skipped, so
authored chapters and generated pages can coexist.

Usage::

    sail-book-gen --root . --project model.sail_project --module core \
                  --book book
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
from pathlib import Path
from typing import Optional

from ._bundle import Bundle
from ._eips import EipIndex, link_eip_references
from ._lsp import project_files

_HOVER_JS = Path(__file__).parent / "assets/sail-hover.js"

_HEADING = re.compile(r"^#\s+(.+)$", re.M)


def markdown_blocks(text: str) -> list[tuple[int, str]]:
    """Extract (offset, markdown) for each ``/*md ... */`` block.

    Handles Sail's nested block comments; the marker must be followed by
    whitespace.
    """
    blocks = []
    i = 0
    while True:
        i = text.find("/*md", i)
        if i < 0:
            return blocks
        after = i + 4
        if after < len(text) and text[after] not in " \t\r\n":
            i = after
            continue
        depth = 1
        j = after
        while j < len(text) - 1 and depth:
            if text[j : j + 2] == "/*":
                depth += 1
                j += 2
            elif text[j : j + 2] == "*/":
                depth -= 1
                j += 2
            else:
                j += 1
        content = text[after : j - 2] if depth == 0 else text[after:]
        blocks.append((i, content.strip("\r\n")))
        i = j


def page_items(bundle: Bundle, file: str, text: str, excluded: set[str]) -> list[tuple[str, ...]]:
    """('md', text) and ('def', kind, name) entries for a file, in source order."""
    entries: list[tuple[int, tuple[str, ...]]] = [(offset, ("md", block)) for offset, block in markdown_blocks(text)]
    function_names = {name for kind, name in bundle.identifiers() if kind == "function"}
    for kind, name in bundle.identifiers():
        if kind in ("anchor", "span") or (kind == "val" and name in function_names) or name in excluded:
            continue
        definition = bundle.find(name, kind=kind)
        for clause in definition.clauses:
            if clause.file == file and clause.start is not None:
                entries.append((clause.start, ("def", kind, name)))
                break
    return [item for _, item in sorted(entries, key=lambda entry: entry[0])]


def render_page(
    file: str, items: list[tuple[str, ...]], eips: Optional[EipIndex] = None
) -> tuple[str, str]:
    """Render a page; returns (nav title, markdown). The first ``/*md`` block's
    leading ``# heading`` names the page; otherwise the file path does."""
    title = Path(file).stem
    out = []
    eips_seen: set[int] = set()
    if not (items and items[0][0] == "md" and _HEADING.match(items[0][1])):
        out.append(f"# `{file}`\n")
    else:
        title = _HEADING.match(items[0][1]).group(1).strip()
    for item in items:
        if item[0] == "md":
            block = item[1]
            if eips is not None:
                block = link_eip_references(block, eips_seen, hover=True)
            out.append(block + "\n")
        else:
            _, kind, name = item
            out.append(f"::: {name}\n    options:\n      kind: {kind}\n")
    if eips is not None:
        for n in sorted(eips_seen):
            card = eips.card_html(n)
            if card:
                out.append(card + "\n")
    return title, "\n".join(out)


def render_mod_page(text: str, eips: Optional[EipIndex] = None) -> str:
    """Render a directory's mod.md overview, with EIP references linked."""
    if eips is None:
        return text
    eips_seen: set[int] = set()
    out = link_eip_references(text, eips_seen, hover=True)
    for n in sorted(eips_seen):
        card = eips.card_html(n)
        if card:
            out += "\n" + card + "\n"
    return out


_CONFIG_TEMPLATE = """site_name: "{site_name}"
theme:
  name: material
  features:
    - content.code.copy
    - content.tooltips
    - navigation.top
    - search.highlight
plugins:
  - search
  - literate-nav:
      nav_file: SUMMARY.md
  - section-index
  - autorefs:
      link_titles: false
  - mkdocstrings:
      default_handler: sail
      handlers:
        sail:
          bundle: doc/doc.json
          lsp_index: doc/lsp-index.json{eips_config}
markdown_extensions:
  - admonition
  - attr_list
  - toc:
      permalink: true
  - pymdownx.superfences
extra:
  version:
    provider: mike
extra_javascript:
  - assets/sail-hover.js
"""


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", default=".", help="project root (paths must match the docinfo bundle)")
    parser.add_argument("--project", required=True, help="a .sail_project file")
    parser.add_argument("--module", required=True, help="project module to resolve")
    parser.add_argument("--variable", action="append", default=[], help="project variable NAME=VALUE (repeatable)")
    parser.add_argument("--sail", default="sail", help="sail binary for --list-files")
    parser.add_argument("--book", required=True, help="book directory (holds mkdocs.yml, docs/, doc/doc.json)")
    parser.add_argument("--site-name", default="Sail Specification")
    parser.add_argument("--eips", help="local ethereum/EIPs EIPS/ directory for EIP hover cards")
    parser.add_argument("--no-config", action="store_true", help="do not (re)write mkdocs.yml")
    args = parser.parse_args(argv)

    root = Path(args.root).resolve()
    book = Path(args.book)
    eips = EipIndex(Path(args.eips).resolve()) if args.eips else None
    bundle = Bundle.load(book / "doc/doc.json")
    files = project_files(args.sail, root, args.project, args.module, args.variable)

    # identifiers rendered by hand-authored pages are not re-rendered
    excluded: set[str] = set()
    for page in (book / "docs").glob("*.md"):
        for match in re.finditer(r"^::: (\S+)", page.read_text(), re.M):
            excluded.add(match.group(1))

    pages = []
    definitions = 0
    for file in files:
        source = root / file
        if not source.exists():
            continue
        items = page_items(bundle, file, source.read_text(), excluded)
        if not items:
            continue
        definitions += sum(1 for item in items if item[0] == "def")
        title, markdown = render_page(file, items, eips)
        page = str(Path(file).with_suffix(".md"))
        path = book / "docs/reference" / page
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(markdown)
        pages.append((file, "reference/" + page, title))

    # a mod.md in a source directory is its section overview; rendered as
    # the directory's index page (mkdocs-section-index attaches it to the
    # nav section, making the section title clickable)
    mod_files = []
    for directory in sorted({str(Path(file).parent) for file in files if (root / file).exists()}):
        mod = root / directory / "mod.md"
        if mod.exists():
            mod_files.append(mod)
            markdown = render_mod_page(mod.read_text(), eips)
            path = book / "docs/reference" / directory / "index.md"
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(markdown)

    assets = book / "docs/assets"
    assets.mkdir(parents=True, exist_ok=True)
    shutil.copy(_HOVER_JS, assets / "sail-hover.js")

    # pre-render every referenced EIP as an on-demand hover fragment
    if eips is not None:
        from ._eips import _EIP_REF

        numbers: set[int] = set()
        for source in [root / file for file in files] + mod_files:
            if source.exists():
                numbers.update(int(m.group(1)) for m in _EIP_REF.finditer(source.read_text()))
        fragments = assets / "eips"
        fragments.mkdir(exist_ok=True)
        rendered = 0
        for n in sorted(numbers):
            html = eips.render_full_html(n)
            if html:
                (fragments / f"eip-{n}.html").write_text(html)
                rendered += 1
        print(f"rendered {rendered} EIP hover fragments", file=sys.stderr)

    # a home page is required for the site root; generate one if not authored
    index = book / "docs/index.md"
    if not index.exists():
        toc = "\n".join(f"- [{title}]({page})" for _, page, title in pages)
        index.write_text(f"# {args.site_name}\n\n## Modules\n\n" + toc + "\n")

    # navigation lives in docs/SUMMARY.md (mkdocs-literate-nav); generate a
    # default covering everything when none is authored
    summary = book / "docs/SUMMARY.md"
    if not summary.exists():
        summary.write_text("- [Home](index.md)\n- *.md\n- reference/*\n")

    if not args.no_config:
        eips_config = f"\n          eips_dir: {Path(args.eips).resolve()}" if args.eips else ""
        (book / "mkdocs.yml").write_text(
            _CONFIG_TEMPLATE.format(site_name=args.site_name, eips_config=eips_config)
        )

    print(
        f"generated {len(pages)} pages covering {definitions} definitions"
        + (f" (excluded {len(excluded)} hand-rendered ids)" if excluded else ""),
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
