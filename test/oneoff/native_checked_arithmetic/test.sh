#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/native_checked_arithmetic.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

OUT="$TMP_DIR/native_checked_arithmetic"
"$SAIL" --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  "$TEST_DIR/../../c/native_checked_arithmetic.sail" -o "$OUT"

# Word splitting is intentional for compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS "$TEST_DIR/runner.c" "$SAIL_DIR"/lib/*.c \
  -I "$TMP_DIR" -I "$SAIL_DIR/lib" $GMP_LIBS -o "$OUT.bin"

"$OUT.bin"

expect_failure() {
  mode=$1
  message=$2
  if "$OUT.bin" "$mode" >"$TMP_DIR/$mode.out" 2>"$TMP_DIR/$mode.err"; then
    echo "$mode unexpectedly completed" >&2
    exit 1
  fi
  test ! -s "$TMP_DIR/$mode.out"
  grep -Fq "$message" "$TMP_DIR/$mode.err"
}

expect_failure uadd 'uint64_t addition overflow'
expect_failure usub 'uint64_t subtraction underflow'
expect_failure umul 'uint64_t multiplication overflow'
expect_failure udiv 'uint64_t division by zero'
expect_failure umod 'uint64_t modulo by zero'
expect_failure iadd 'int64_t addition overflow'
expect_failure isub 'int64_t subtraction overflow'
expect_failure imul 'int64_t multiplication overflow'
expect_failure idiv 'int64_t division overflow'
expect_failure imod 'int64_t modulo overflow'

grep -Fq 'sail_checked_u64_add' "$OUT.c"
grep -Fq 'sail_checked_i64_mul' "$OUT.c"
