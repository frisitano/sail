#!/usr/bin/env python3
"""Generate a full reference book over a Sail project: one page per source
file with ::: directives for every definition, in source order, plus nav."""

import re
import sys
from pathlib import Path

from mkdocstrings_handlers.sail import Bundle

BOOK = Path(sys.argv[1])          # book dir containing mkdocs.yml, docs/, doc/doc.json
FILE_ORDER = sys.argv[2].split()  # project files in compilation order

bundle = Bundle.load(BOOK / "doc/doc.json")

# definitions already rendered by hand-authored pages are skipped
excluded = set()
for page in (BOOK / "docs").glob("*.md"):
    for match in re.finditer(r"^::: (\S+)", page.read_text(), re.M):
        excluded.add(match.group(1))

# collect (file -> [(start, kind, name)]), one entry per definition
by_file = {}
function_names = set(kind_name[1] for kind_name in bundle.identifiers() if kind_name[0] == "function")
for kind, name in bundle.identifiers():
    if kind in ("anchor", "span"):
        continue
    if kind == "val" and name in function_names:
        continue  # the function rendering covers it
    if name in excluded:
        continue
    definition = bundle.find(name, kind=kind)
    clause = next((c for c in definition.clauses if c.file and c.start is not None), None)
    if clause is None or clause.file not in FILE_ORDER:
        continue
    by_file.setdefault(clause.file, []).append((clause.start, kind, name))

# one page per file, definitions in source order
ref_dir = BOOK / "docs/reference"
pages = []
for file in FILE_ORDER:
    items = sorted(by_file.get(file, []))
    if not items:
        continue
    page = file.removesuffix(".sail") + ".md"
    pages.append((file, page))
    out = [f"# `{file}`\n"]
    for _, kind, name in items:
        out.append(f"::: {name}\n    options:\n      kind: {kind}\n")
    path = ref_dir / page
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(out))

# nested nav mirroring the directory tree, in compilation order
def nav_tree(pages):
    root = {}
    for file, page in pages:
        node = root
        parts = file.removesuffix(".sail").split("/")
        for part in parts[:-1]:
            node = node.setdefault(part + "/", {})
        node[parts[-1]] = "reference/" + page
    return root

def emit(node, indent):
    lines = []
    for key, value in node.items():
        if isinstance(value, dict):
            lines.append(f'{indent}- "{key.rstrip("/")}":')
            lines.extend(emit(value, indent + "    "))
        else:
            lines.append(f'{indent}- "{key}": {value}')
    return lines

nav_ref = "\n".join(emit(nav_tree(pages), "      "))

(BOOK / "mkdocs.yml").write_text(f"""site_name: "EVM Sail Specification (mkdocstrings-sail demo)"
theme:
  name: material
  features:
    - content.code.copy
    - content.tooltips
    - navigation.tabs
    - navigation.top
    - search.highlight
plugins:
  - search
  - autorefs:
      link_titles: false
  - mkdocstrings:
      default_handler: sail
      handlers:
        sail:
          bundle: doc/doc.json
          lsp_index: doc/lsp-index.json
markdown_extensions:
  - admonition
  - toc:
      permalink: true
  - pymdownx.superfences
  - pymdownx.highlight
extra:
  version:
    provider: mike
nav:
  - Walkthrough:
      - Interpreter: index.md
      - Machine state: machine.md
  - Reference:
{nav_ref}
""")

count = sum(len(v) for v in by_file.values())
print(f"generated {len(pages)} reference pages covering {count} definitions "
      f"(excluded {len(excluded)} hand-rendered ids)")
