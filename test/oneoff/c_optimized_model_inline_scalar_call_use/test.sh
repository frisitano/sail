#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_optimized_model_inline_scalar_call_use.XXXXXX")
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
  --c-optimized-model --c-package inline_call --c-output-dir "$TMP_DIR/generated" \
  --c-preserve next_byte --c-preserve call_in_return_comparison \
  --c-preserve call_in_eager_guard --c-preserve external_call_in_return \
  --c-preserve call_in_short_circuit \
  "$TEST_DIR/model.sail_project"

SOURCE="$TMP_DIR/generated/src/spec/model.c"
test -f "$SOURCE"

sed -n '/^bool call_in_return_comparison(/,/^}/p' "$SOURCE" > "$TMP_DIR/return.c"
grep -Fq 'return (bool)((next_byte(value)) == UINT64_C(0x2));' "$TMP_DIR/return.c"
if grep -Eq '(tmp_|result_|[A-Za-z0-9_]*_result_[A-Za-z0-9_]*)' "$TMP_DIR/return.c"; then
  echo 'optimized extraction retained a one-use scalar call result before its return' >&2
  exit 1
fi

sed -n '/^uint8_t call_in_eager_guard(/,/^}/p' "$SOURCE" > "$TMP_DIR/guard.c"
grep -Fq 'if ((next_byte(value)) == UINT64_C(0x2)) {' "$TMP_DIR/guard.c"
if grep -Eq '(tmp_|result_|[A-Za-z0-9_]*_result_[A-Za-z0-9_]*)' "$TMP_DIR/guard.c"; then
  echo 'optimized extraction retained a one-use scalar call result before its eager guard' >&2
  exit 1
fi

sed -n '/^bool external_call_in_return(/,/^}/p' "$SOURCE" > "$TMP_DIR/extern.c"
grep -Eq 'uint8_t [A-Za-z0-9_]+ = external_byte\(value\);' "$TMP_DIR/extern.c"

sed -n '/^bool call_in_short_circuit(/,/^}/p' "$SOURCE" > "$TMP_DIR/short_circuit.c"
grep -Eq 'uint8_t [A-Za-z0-9_]+ = next_byte\(value\);' "$TMP_DIR/short_circuit.c"
