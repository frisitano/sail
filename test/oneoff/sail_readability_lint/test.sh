#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "$TEST_DIR/../../.." && pwd)
SAIL=${SAIL:-sail}
DUNE=${DUNE:-dune}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/sail_readability_lint.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

"$SAIL" --no-color --no-memo-z3 --lint-readability --just-check \
  "$TEST_DIR/model.sail" >"$TMP_DIR/source.stdout" 2>"$TMP_DIR/source.stderr"

for rule in \
  sail-redundant-bool \
  sail-identity-conditional \
  sail-trivial-alias \
  sail-constant-conditional \
  sail-duplicate-branches \
  sail-empty-conditional \
  sail-conditional-assignment \
  sail-else-after-terminal \
  sail-prefer-early-return \
  sail-nested-else-if \
  sail-single-use-temporary \
  sail-dead-pure-binding \
  sail-nested-function-call \
  sail-function-call-condition
do
  grep -Fq "Readability lint [$rule]" "$TMP_DIR/source.stderr"
done

if test "$(grep -Fc 'Readability lint [sail-prefer-early-return]' "$TMP_DIR/source.stderr")" -ne 1; then
  echo 'the early-return rule did not distinguish a tail guard from a non-tail conditional' >&2
  exit 1
fi

"$SAIL" --no-color --no-memo-z3 --lint-readability --just-check \
  "$TEST_DIR/clean_model.sail" >"$TMP_DIR/clean.stdout" 2>"$TMP_DIR/clean.stderr"

if grep -Eq 'sail-(nested-function-call|function-call-condition)' "$TMP_DIR/clean.stderr"; then
  echo 'named intermediates or an ordinary operator condition were incorrectly diagnosed' >&2
  exit 1
fi

if test "$(grep -Fc 'Readability lint [sail-else-after-terminal]' "$TMP_DIR/source.stderr")" -ne 1; then
  echo 'the explicit-else rule did not distinguish an explicit branch from a terminal guard' >&2
  exit 1
fi

if grep -Fq 'Readability lint [sail-nested-else-if]' "$TMP_DIR/clean.stderr"; then
  echo 'a direct else-if chain was incorrectly diagnosed as a nested conditional' >&2
  exit 1
fi

if test "$(grep -Fc 'Readability lint [sail-duplicate-branches]' "$TMP_DIR/source.stderr")" -ne 1; then
  echo 'the duplicate-branch rule ignored effects or overlapped the empty-conditional rule' >&2
  exit 1
fi

if grep -E 'meaningful_(effectful|pure)_binding|effectful_temporary' "$TMP_DIR/source.stderr" \
  | grep -Eq 'trivial-alias|single-use|dead-pure'; then
  echo 'a meaningful or effectful binding was incorrectly diagnosed' >&2
  exit 1
fi

"$SAIL" --no-color --no-memo-z3 --lint-readability -O -c \
  --c-no-main --c-no-rts --c-preserve double_not --c-preserve meaningful_effectful_binding \
  "$TEST_DIR/model.sail" -o "$TMP_DIR/model" >"$TMP_DIR/jib.stdout" 2>"$TMP_DIR/jib.stderr"

grep -Fq 'Jib readability lint [jib-declaration-assignment-split]' "$TMP_DIR/jib.stderr"

if grep -F 'effectful_temporary' "$TMP_DIR/jib.stderr" | grep -Fq 'jib-dead-pure-temporary'; then
  echo 'an effectful call result was incorrectly diagnosed as a dead pure temporary' >&2
  exit 1
fi

test -s "$TMP_DIR/model.c"

(cd "$REPO_ROOT" && "$DUNE" exec --release test/oneoff/sail_readability_lint/jib_rules.exe)
