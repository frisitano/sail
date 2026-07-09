# Change Log

## 0.0.4

- Add `sail_lsp` integration for Sail source navigation, generated-C navigation, source-graph, include-path, local `let`/let-pattern/struct-pattern, `foreach` loop-binder, match-arm pattern/guard/inline/multi-line/list-cons, mapping-clause binder, function-clause/vector-subrange pattern binder, parameter, enum member, union constructor, field, and keyword completions, document highlights, hover/type/documentation commands, diagnostics, formatting, snippets, and project selection.
- Add `sail.lsp.json` artifact-manifest discovery for generated C, sidecar maps, docinfo, and project metadata.
- Emit `out.sail_lsp.json` from the C backend when generated-C LSP maps are requested.
- Add VSCode `sail` task definitions for checking files/projects and generating C with LSP sidecars.
- Refresh LSP caches and open-document diagnostics after watched Sail source, project, manifest, sidecar, docinfo, or generated C/C++ changes.
- Add packaging scripts for checking, building a `.vsix`, and local extension installation.

## 0.4

- Add keywords and operators
- Icon

## 0.3

- Fix curly braces

## 0.2

- Add keywords

## 0.1

- Initial release
