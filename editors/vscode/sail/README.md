# sail README

Visual Studio Code support for the Sail ISA specification language.

<img src="images/sail_icon.png" alt="icon" width="200"/>

## Features

- Syntax highlighting and language configuration for `.sail` and `.sail_project` files.
- Sail language-server integration through the compiler-owned `sail_lsp` executable.
- Default Go to Definition for Sail identifiers resolves to Sail source definitions.
- `Sail: Go to Generated C` jumps to generated C output when `sail_lsp` can find a generated C file and sidecar map.
- Go to Definition inside a `{ c: "function_name" }` string jumps to the exact C symbol.
- Hover, `Sail: Show Type`, and `Sail: Show Documentation` can read documentation info JSON emitted by the Sail documentation backend, with source-comment fallback when docinfo is not available.
- `Sail: Choose Project File` and `Sail: Set Project Modules` configure project-backed checks from the command palette.
- Document symbols, workspace symbols, source-graph, include-path, local `let`/let-pattern/struct-pattern, `foreach` loop-binder, match-arm pattern/guard/inline/multi-line/list-cons, mapping-clause binder, function-clause/vector-subrange pattern binder, parameter, enum member, union constructor, field, and keyword completions, textual references, document highlights, semantic highlighting, generated-C name display, snippets, compiler-backed diagnostics, compiler-backed formatting, command-palette checks, and VSCode tasks.

## Setup

Install or build `sail_lsp` so it is on your `PATH`, or set `sail.lsp.path` to its location.

From a Sail source checkout:

```sh
dune build @install src/bin/sail_lsp.exe
```

For local extension testing:

```sh
cd editors/vscode/sail
npm install
npm run check
npm run package
code --install-extension sail-*.vsix
```

Generated-C navigation works best with a sidecar map:

```sh
sail -c --c-emit-lsp-map model.sail
```

This emits both `out.c.symbols.json` and `out.sail_lsp.json` by default. Use `--c-lsp-map FILE` and `--c-lsp-index FILE` to choose explicit paths, or `--c-emit-lsp-index` to emit the artifact manifest without naming it explicitly.

`sail_lsp` auto-discovers `*.symbols.json` files under the workspace and uses each sidecar's `cFile` metadata when present. If discovery is ambiguous or your generated output lives outside the workspace, set:

- `sail.cOutput`: generated C implementation file.
- `sail.cMap`: generated sidecar JSON file, such as `out.c.symbols.json`.
- `sail.docinfo`: documentation info JSON, commonly `doc.json`.

For repeatable builds, keep the backend-emitted `out.sail_lsp.json` artifact manifest with the generated output, or put a `sail.lsp.json` manifest at the workspace root. Manifest paths are resolved relative to the manifest file:

```json
{
  "schema": "sail.lsp.artifacts",
  "version": 1,
  "projectFile": "model.sail_project",
  "projectModules": [],
  "artifacts": {
    "cOutput": "build/model.c",
    "cMap": "build/model.c.symbols.json",
    "docinfo": "build/doc.json"
  }
}
```

Build tooling can aggregate multiple generated targets in one manifest by making `artifacts` an array. Top-level project settings apply to each artifact unless an artifact overrides them:

```json
{
  "schema": "sail.lsp.artifacts",
  "version": 1,
  "projectFile": "model.sail_project",
  "projectModules": [],
  "artifacts": [
    {
      "cOutput": "build/c/model.c",
      "cMap": "build/c/model.c.symbols.json"
    },
    {
      "cOutput": "build/cpp/model.cpp",
      "cMap": "build/cpp/model.cpp.symbols.json",
      "docinfo": "build/docs/doc.json"
    }
  ]
}
```

The extension discovers `sail.lsp.json`, `.sail_lsp.json`, `out.sail_lsp.json`, and `out.sail_artifacts.json` under the workspace, preferring root manifests when present. You can also point at any manifest with `sail.artifactIndex`. Explicit `sail.cOutput`, `sail.cMap`, `sail.docinfo`, and `sail.projectFile` settings take precedence. VSCode watches Sail sources, `.sail_project` files, manifests, `*.symbols.json`, docinfo JSON, and generated C/C++ outputs so build-task rewrites refresh generated-C navigation and documentation without restarting the language server.

Project checks can use the same `.sail_project` setup as command-line Sail:

- `sail.projectFile`: project file used for diagnostics and `Sail: Check Current File`.
- `sail.projectModules`: module names to check. Leave empty to check all modules.
- `sail.projectAllModules`: pass `-all_modules` when `sail.projectModules` is empty.
- `sail.diagnostics.enable`: enable diagnostics on open and save.

Use `Sail: Choose Project File` to pick from workspace `.sail_project` files, and `Sail: Set Project Modules` to write the module list without editing JSON settings by hand.

## Tasks

The extension contributes a `sail` task type. VSCode's `Tasks: Run Task` command offers tasks for the active Sail file and the configured project:

- `Check <file>` runs `sail -no_color -just_check <file>`.
- `Check Project` runs `sail -no_color -just_check -project <projectFile> ...`.
- `Generate C for <file>` runs `sail -c --c-emit-lsp-map <file>`, which also emits generated-C navigation sidecars.

For stable workspace tasks, add entries like:

```json
{
  "version": "2.0.0",
  "tasks": [
    {
      "label": "Sail: Check project",
      "type": "sail",
      "task": "checkProject",
      "projectFile": "model.sail_project",
      "projectAllModules": true,
      "group": "test"
    },
    {
      "label": "Sail: Generate C",
      "type": "sail",
      "task": "generateC",
      "file": "model.sail",
      "emitLspMap": true,
      "group": "build"
    }
  ]
}
```

When no docinfo JSON is configured or discovered, `sail_lsp` uses contiguous `//` comments or immediately preceding `/* ... */` blocks as fallback documentation for declarations.

`Format Document` and `Sail: Format Current File` call `sail -fmt -fmt_emit stdout` on saved files.

## Release Notes

The extension is published as `rems-project.sail`. Before publishing a new `.vsix`, confirm marketplace access for the `rems-project` publisher, run `npm run check`, package with `npm run package`, and smoke-test the generated extension with `code --install-extension sail-*.vsix`.

## Known Issues

The first `sail_lsp` implementation uses lightweight source indexing for symbols and references. Compiler-backed diagnostics currently run on open/save and watched source/project/manifest changes rather than every edit, and proof-backend navigation is left for a later language-server layer.
