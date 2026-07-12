#!/usr/bin/env bash
# End-to-end test: generate a docinfo bundle from the fixture spec, build
# the integration site with mkdocs-material + this handler, and assert on
# the rendered HTML. Requires `uv` and a built `sail` (repo root).
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pkg_dir="$(dirname "$here")"
repo_root="$(dirname "$pkg_dir")"
sail="${SAIL:-$repo_root/sail}"
fixture="$here/fixture"
site_src="$here/integration"

if ! command -v uv >/dev/null; then echo "SKIP: uv not installed"; exit 0; fi
if [ ! -x "$sail" ]; then echo "SKIP: sail not built at $sail"; exit 0; fi

echo "== generating docinfo bundle from tests/fixture"
rm -rf "$site_src/doc" "$site_src/site"
(cd "$fixture" && "$sail" --doc --doc-format identity --doc-embed plain --doc-embed-with-location \
    --doc-bundle doc.json -o "$site_src/doc" spec/lib/util.sail spec/core/machine.sail)

echo "== building site with mkdocs --strict"
(cd "$site_src" && uv run --with-editable "$pkg_dir" --with mkdocs-material mkdocs build --strict -d site)

check() { # check <file> <pattern> <description>
    if ! grep -qF "$2" "$site_src/site/$1"; then
        echo "FAIL: $3 — pattern not found in $1: $2"
        exit 1
    fi
    echo "ok: $3"
}

check index.html 'id="function-step"' "stable anchor on rendered definition"
check index.html '<span class="k">function</span>' "Sail lexer highlighting"
check index.html 'href="definitions/#function-increment"' "in-code link resolves cross-page via autorefs"
check index.html '#register-PC' "in-code register link"
check index.html 'Advance the machine' "doc comment rendered"
check definitions/index.html 'id="type-word"' "type anchor"
check definitions/index.html 'The machine word type.' "type doc comment rendered (docinfo comment on types)"
check definitions/index.html 'id="val-increment"' "kind-disambiguated val rendering"
check definitions/index.html 'id="mapping-flag_bit"' "mapping rendering"
check definitions/index.html 'href="#mapping-flag_bit"' "mapping application links to mapping anchor"

if grep -qF '<autoref' "$site_src/site/index.html"; then
    echo "FAIL: unresolved <autoref> left in output"
    exit 1
fi
echo "ok: no unresolved autorefs"

# Second pass with a sail-lsp semantic index, when the binary is available
lsp_binary="${SAIL_LSP:-$(command -v sail_lsp || true)}"
if [ -n "$lsp_binary" ]; then
    echo "== generating sail-lsp index"
    (cd "$fixture" && uv run --with-editable "$pkg_dir" sail-lsp-index \
        --binary "$lsp_binary" --root . --output "$site_src/doc/lsp-index.json")
    echo "== building site with lsp index"
    (cd "$site_src" && uv run --with-editable "$pkg_dir" --with mkdocs-material \
        mkdocs build --strict -f mkdocs-lsp.yml -d site-lsp)
    check_lsp() {
        if ! grep -qF "$2" "$site_src/site-lsp/$1"; then
            echo "FAIL: $3 — pattern not found in $1: $2"
            exit 1
        fi
        echo "ok: $3"
    }
    check_lsp definitions/index.html 'href="#type-word"' "type reference links via lsp index"
    check_lsp index.html 'class="nf"' "semantic token classes from lsp index"
    check_lsp definitions/index.html 'href="#mapping-flag_bit"' "docinfo links still win with lsp index"
else
    echo "sail_lsp not found, skipping lsp index pass (set SAIL_LSP to enable)"
fi

echo "PASS: mkdocstrings-sail integration"
