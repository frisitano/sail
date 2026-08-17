#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_optimized_model_inline_boolean_guard.XXXXXX")
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
  --c-optimized-model --c-package inline_guard --c-output-dir "$TMP_DIR/generated" \
  --c-preserve added_is_nonzero --c-preserve called_boolean_guard --c-preserve external_boolean_guard \
  "$TEST_DIR/model.sail_project"

SOURCE="$TMP_DIR/generated/src/spec/model.c"
test -f "$SOURCE"
sed -n '/^uint8_t called_boolean_guard(/,/^}/p' "$SOURCE" > "$TMP_DIR/called_boolean_guard.c"
grep -Fq 'if (added_is_nonzero(left, right)) {' "$TMP_DIR/called_boolean_guard.c"
if grep -Eq 'bool (tmp_|result_|[A-Za-z0-9_]*_result_[A-Za-z0-9_]*)' \
    "$TMP_DIR/called_boolean_guard.c"; then
  echo 'optimized extraction retained a one-use boolean call result before its guard' >&2
  exit 1
fi

sed -n '/^uint8_t external_boolean_guard(/,/^}/p' "$SOURCE" > "$TMP_DIR/external_boolean_guard.c"
grep -Eq 'bool [A-Za-z0-9_]+ = external_predicate\(value\);' "$TMP_DIR/external_boolean_guard.c"
grep -Eq 'if \([A-Za-z0-9_]+\) \{' "$TMP_DIR/external_boolean_guard.c"
