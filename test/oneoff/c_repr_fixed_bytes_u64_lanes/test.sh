#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
SOURCE="$TEST_DIR/../../c/c_repr_fixed_bytes_u64_lanes.sail"
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_repr_fixed_bytes_u64_lanes.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

run_sail() {
  if [ -n "${SAIL_PLUGIN:-}" ]; then
    "$SAIL" -plugin "$SAIL_PLUGIN" "$@"
  else
    "$SAIL" "$@"
  fi
}

run_sail --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve lane_address_equal \
  --c-preserve lane_address_byte \
  --c-preserve lane_address_update \
  --c-preserve lane_b256_equal \
  --c-preserve lane_b256_fill \
  --c-preserve lane_b256_to_u256 \
  --c-preserve u256_to_lane_b256 \
  "$SOURCE" -o "$TMP_DIR/model"

grep -Fq 'typedef struct { uint64_t lanes[3]; } sail_fixed_bytes_u64_lanes_20;' "$TMP_DIR/model.h"
grep -Fq 'typedef struct { uint64_t lanes[4]; } sail_fixed_bytes_u64_lanes_32;' "$TMP_DIR/model.h"
grep -Fq 'sail_fixed_bytes_u64_lanes_20 zlane_address_update(sail_fixed_bytes_u64_lanes_20, uint8_t, uint64_t);' "$TMP_DIR/model.h"
grep -Fq 'sail_fixed_bytes_u64_lanes_32 zlane_b256_fill(uint64_t);' "$TMP_DIR/model.h"

extract_function() {
  function_name=$1
  awk -v needle=" z${function_name}(" '
    index($0, needle) { printing = 1 }
    printing { print }
    printing && /^}$/ { exit }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/$function_name.body"
  test -s "$TMP_DIR/$function_name.body"
}

assert_native_function() {
  function_name=$1
  expected=$2
  extract_function "$function_name"
  grep -Fq "$expected" "$TMP_DIR/$function_name.body"
  if grep -Eq 'sail_int|mpz_|lbits|CONVERT_OF|sail_fixed_bytes_[0-9]+|\.bytes' \
      "$TMP_DIR/$function_name.body"; then
    echo "$function_name crossed the native lane representation boundary" >&2
    exit 1
  fi
}

assert_native_function lane_address_equal 'eq_fixed_bytes_u64_lanes_20('
assert_native_function lane_address_byte 'fast_unsigned_vector_access_fixed_bytes_u64_lanes_20('
assert_native_function lane_address_update 'fast_unsigned_vector_update_fixed_bytes_u64_lanes_20('
assert_native_function lane_b256_equal 'eq_fixed_bytes_u64_lanes_32('
assert_native_function lane_b256_fill 'fast_unsigned_vector_init_fixed_bytes_u64_lanes_32('
assert_native_function lane_b256_to_u256 'zfrom_bytes_le'
assert_native_function u256_to_lane_b256 'zto_bytes_le'
grep -Fq 'u256_from_fixed_bytes_u64_lanes_32(zv)' "$TMP_DIR/model.c"
grep -Fq 'fixed_bytes_u64_lanes_32_from_u256(zb)' "$TMP_DIR/model.c"

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

# Word splitting is intentional for user/compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS -std=gnu11 -I "$SAIL_DIR/lib" -I "$TMP_DIR" \
  "$TMP_DIR/model.c" "$TEST_DIR/runner.c" "$SAIL_DIR"/lib/*.c $GMP_LIBS -o "$TMP_DIR/runner"
"$TMP_DIR/runner"
