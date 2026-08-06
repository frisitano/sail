#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/sail_readability_lint.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

"$SAIL" --no-color --no-memo-z3 --lint-readability --just-check \
  "$TEST_DIR/model.sail" >"$TMP_DIR/source.stdout" 2>"$TMP_DIR/source.stderr"

for rule in \
  sail-redundant-bool \
  sail-identity-conditional \
  sail-trivial-alias
do
  grep -Fq "Readability lint [$rule]" "$TMP_DIR/source.stderr"
done

if grep -F 'meaningful_effectful_binding' "$TMP_DIR/source.stderr" | grep -Eq 'trivial-alias|single-use'; then
  echo 'meaningful effectful binding was incorrectly diagnosed' >&2
  exit 1
fi

"$SAIL" --no-color --no-memo-z3 --lint-readability -O -c \
  --c-no-main --c-no-rts --c-preserve double_not --c-preserve meaningful_effectful_binding \
  "$TEST_DIR/model.sail" -o "$TMP_DIR/model" >"$TMP_DIR/jib.stdout" 2>"$TMP_DIR/jib.stderr"

grep -Eq 'Jib readability lint \[(jib-declaration-assignment-split|jib-single-use-pure-temporary|jib-unit-plumbing)\]' \
  "$TMP_DIR/jib.stderr"

test -s "$TMP_DIR/model.c"
