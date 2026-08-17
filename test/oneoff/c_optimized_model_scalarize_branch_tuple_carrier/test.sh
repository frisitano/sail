#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_optimized_model_scalarize_branch_tuple_carrier.XXXXXX")
cleanup() {
  if [ "${KEEP_TEST_TMP:-0}" = 1 ]; then
    printf 'preserved test output: %s\n' "$TMP_DIR" >&2
  else
    rm -rf "$TMP_DIR"
  fi
}
trap cleanup EXIT

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-specialize \
  --c-package branch_tuple --c-output-dir "$TMP_DIR/generated" \
  --c-preserve advance --c-preserve advance_managed \
  --c-preserve choose_pair --c-preserve choose_managed \
  "$TEST_DIR/model.sail_project"

SOURCE="$TMP_DIR/generated/src/spec/model.c"
test -f "$SOURCE"

sed -n '/^bool choose_pair(/,/^}/p' "$SOURCE" > "$TMP_DIR/choose_pair.c"
grep -Fq 'switch (operation)' "$TMP_DIR/choose_pair.c"
grep -Fq 'advance' "$TMP_DIR/choose_pair.c"
if grep -Eq '(struct tuple_|\.tup[0-9]|tmp_|result_)' "$TMP_DIR/choose_pair.c"; then
  echo 'optimized extraction retained a projected tuple carrier across branch arms' >&2
  exit 1
fi

sed -n '/^uint8_t choose_managed(/,/^}/p' "$SOURCE" > "$TMP_DIR/choose_managed.c"
grep -Fq 'switch (operation)' "$TMP_DIR/choose_managed.c"
grep -Fq 'advance_managed' "$TMP_DIR/choose_managed.c"
if grep -Eq '(struct tuple_|\.tup[0-9]|tmp_|result_)' "$TMP_DIR/choose_managed.c"; then
  echo 'optimized extraction retained a projected managed tuple carrier across branch arms' >&2
  exit 1
fi
