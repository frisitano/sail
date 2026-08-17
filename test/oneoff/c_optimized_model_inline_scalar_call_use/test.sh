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
  --c-optimized-model --c-specialize --c-package inline_call --c-output-dir "$TMP_DIR/generated" \
  --c-preserve next_byte --c-preserve call_in_return_comparison \
  --c-preserve call_in_eager_guard --c-preserve external_call_in_return \
  --c-preserve call_in_short_circuit --c-preserve field_snapshot_into_call \
  --c-preserve converted_field_into_external_call --c-preserve updated_record_into_call \
  --c-preserve updated_record_into_return \
  "$TEST_DIR/model.sail_project"

SOURCE="$TMP_DIR/generated/src/spec/model.c"
test -f "$SOURCE"

sed -n '/^bool call_in_return_comparison(/,/^}/p' "$SOURCE" > "$TMP_DIR/return.c"
grep -Eq 'return \(bool\)\(\(next_byte[A-Za-z0-9_]*\(value\)\) == UINT(8|64)_C\((0x)?2\)\);' "$TMP_DIR/return.c"
if grep -Eq '(tmp_|result_|[A-Za-z0-9_]*_result_[A-Za-z0-9_]*)' "$TMP_DIR/return.c"; then
  echo 'optimized extraction retained a one-use scalar call result before its return' >&2
  exit 1
fi

sed -n '/^uint8_t call_in_eager_guard(/,/^}/p' "$SOURCE" > "$TMP_DIR/guard.c"
grep -Eq 'if \(\(next_byte[A-Za-z0-9_]*\(value\)\) == UINT(8|64)_C\((0x)?2\)\) \{' "$TMP_DIR/guard.c"
if grep -Eq '(tmp_|result_|[A-Za-z0-9_]*_result_[A-Za-z0-9_]*)' "$TMP_DIR/guard.c"; then
  echo 'optimized extraction retained a one-use scalar call result before its eager guard' >&2
  exit 1
fi

sed -n '/^bool external_call_in_return(/,/^}/p' "$SOURCE" > "$TMP_DIR/extern.c"
grep -Eq 'uint8_t [A-Za-z0-9_]+ = external_byte\(value\);' "$TMP_DIR/extern.c"

sed -n '/^bool call_in_short_circuit(/,/^}/p' "$SOURCE" > "$TMP_DIR/short_circuit.c"
grep -Fq 'if (enabled) {' "$TMP_DIR/short_circuit.c"
if grep -Eq 'return .*enabled.*next_byte' "$TMP_DIR/short_circuit.c"; then
  echo 'optimized extraction made an unconditional scalar call conditional through a C short circuit' >&2
  exit 1
fi

sed -n '/^void field_snapshot_into_call(/,/^}/p' "$SOURCE" > "$TMP_DIR/field_call.c"
grep -Fq 'consume_byte(holder.value);' "$TMP_DIR/field_call.c"
if grep -Eq '(tmp_|result_|[A-Za-z0-9_]*_result_[A-Za-z0-9_]*)' "$TMP_DIR/field_call.c"; then
  echo 'optimized extraction retained a one-use scalar field snapshot before its call' >&2
  exit 1
fi

sed -n '/^uint8_t converted_field_into_external_call(/,/^}/p' "$SOURCE" > "$TMP_DIR/converted_field_call.c"
grep -Eq 'external_byte\(\(?\(uint8_t\)holder\.value\)?\)' "$TMP_DIR/converted_field_call.c"
if grep -Eq '^  uint8_t ([A-Za-z0-9_]+);[[:space:]]*$' "$TMP_DIR/converted_field_call.c"; then
  echo 'optimized extraction separated a converted external-call result declaration from its assignment' >&2
  exit 1
fi

sed -n '/^void updated_record_into_call(/,/^}/p' "$SOURCE" > "$TMP_DIR/updated_record_call.c"
grep -Fq 'consume_pair(((struct Pair){.left = pair.left, .right = value}));' "$TMP_DIR/updated_record_call.c"
if grep -Eq '(tmp_|result_|struct Pair [A-Za-z0-9_]+;)' "$TMP_DIR/updated_record_call.c"; then
  echo 'optimized extraction retained a one-use functional record update before its call' >&2
  exit 1
fi

sed -n '/^struct Pair updated_record_into_return(/,/^}/p' "$SOURCE" > "$TMP_DIR/updated_record_return.c"
grep -Fq 'return ((struct Pair){.left = pair.left, .right = value});' "$TMP_DIR/updated_record_return.c"
if grep -Eq '(tmp_|result_|struct Pair [A-Za-z0-9_]+;)' "$TMP_DIR/updated_record_return.c"; then
  echo 'optimized extraction retained a one-use functional record update before its return' >&2
  exit 1
fi
