#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)

SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_repr_newtype_boundaries.XXXXXX")

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

trap 'rm -rf "$TMP_DIR"' EXIT

run_sail() {
  if [ -n "${SAIL_PLUGIN:-}" ]; then
    "$SAIL" -plugin "$SAIL_PLUGIN" "$@"
  else
    "$SAIL" "$@"
  fi
}

expect_boundary_failure() {
  name=$1
  expected=$2
  output="$TMP_DIR/$name"

  run_sail --no-color -O -c --c-specialize "$TEST_DIR/$name.sail" -o "$output"
  # Word splitting is intentional for user/compiler and pkg-config flags.
  # shellcheck disable=SC2086
  "$CC" ${CFLAGS:-} $GMP_CFLAGS "$output.c" "$SAIL_DIR"/lib/*.c -I "$SAIL_DIR/lib" $GMP_LIBS -o "$output.bin"

  if "$output.bin" > "$output.result" 2> "$output.err"; then
    echo "$name unexpectedly crossed its native integer representation boundary" >&2
    exit 1
  fi

  test ! -s "$output.result"
  grep -Fq "$expected" "$output.err"
}

expect_boundary_failure negative 'Sail C backend: negative integer cannot be represented as uint64_t'
grep -Fq 'INT64_C(-1)' "$TMP_DIR/negative.c"
if grep -Fq 'neg_int(' "$TMP_DIR/negative.c"; then
  echo 'bounded negative literal detoured through the Sail integer runtime' >&2
  exit 1
fi
expect_boundary_failure overflow 'Sail C backend: integer value is outside the uint64_t domain'
expect_boundary_failure nat_overflow 'Sail C backend: integer value is outside the uint64_t domain'
expect_boundary_failure negative_u8 'Sail C backend: negative integer cannot be represented as uint8_t'
expect_boundary_failure overflow_u8 'Sail C backend: integer value is outside the uint8_t domain'
