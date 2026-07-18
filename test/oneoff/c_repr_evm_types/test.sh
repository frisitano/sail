#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
SOURCE="$TEST_DIR/../../c/c_repr_evm_types.sail"
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_repr_evm_types.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

run_sail() {
  if [ -n "${SAIL_PLUGIN:-}" ]; then
    "$SAIL" -plugin "$SAIL_PLUGIN" "$@"
  else
    "$SAIL" "$@"
  fi
}

run_sail --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve u256_add \
  --c-preserve u256_sub \
  --c-preserve u256_mul \
  --c-preserve u256_and \
  --c-preserve u256_or \
  --c-preserve u256_xor \
  --c-preserve u256_not \
  --c-preserve u256_equal \
  --c-preserve u256_bit \
  --c-preserve u256_shift_left \
  --c-preserve u256_shift_right \
  --c-preserve u256_arith_shift_right \
  --c-preserve u256_from_byte \
  --c-preserve u256_from_lbits \
  --c-preserve u256_low_byte \
  --c-preserve u256_middle_word \
  --c-preserve u256_to_nat \
  --c-preserve limb_unsigned \
  --c-preserve limb_signed \
  --c-preserve limb_shift_left \
  --c-preserve limb_shift_right \
  --c-preserve byte_arith_shift_right \
  --c-preserve address_equal \
  --c-preserve address_equal_vector \
  --c-preserve address_byte \
  --c-preserve address_update \
  --c-preserve address_from_vector \
  --c-preserve address_to_vector \
  --c-preserve b160_equal \
  --c-preserve b256_equal \
  --c-preserve b256_fill \
  --c-preserve b384_equal \
  --c-preserve b384_byte \
  --c-preserve b384_update \
  --c-preserve keep_bytes20_inc \
  --c-preserve bytes20_inc_byte \
  --c-preserve bytes20_inc_update \
  "$SOURCE" -o "$TMP_DIR/model"

grep -Fq 'typedef struct { uint64_t limbs[4]; } sail_u256;' "$TMP_DIR/model.h"
grep -Fq 'typedef struct { uint8_t bytes[20]; } sail_fixed_bytes_20;' "$TMP_DIR/model.h"
grep -Fq 'typedef struct { uint8_t bytes[32]; } sail_fixed_bytes_32;' "$TMP_DIR/model.h"
grep -Fq 'typedef struct { uint8_t bytes[48]; } sail_fixed_bytes_48;' "$TMP_DIR/model.h"
grep -Fq 'sail_u256 zu256_add(sail_u256, sail_u256);' "$TMP_DIR/model.h"
grep -Fq 'sail_u256 zu256_from_lbits(lbits);' "$TMP_DIR/model.h"
grep -Fq 'void zu256_to_nat(sail_int *rop, sail_u256);' "$TMP_DIR/model.h"
grep -Fq 'uint64_t zu256_bit(sail_u256, uint64_t);' "$TMP_DIR/model.h"
grep -Fq 'sail_fixed_bytes_20 zaddress_update(sail_fixed_bytes_20, uint64_t, uint64_t);' "$TMP_DIR/model.h"
grep -Fq 'sail_fixed_bytes_32 zb256_fill(uint64_t);' "$TMP_DIR/model.h"
grep -Fq 'sail_fixed_bytes_20 zbytes20_inc_update(sail_fixed_bytes_20, uint64_t, uint64_t);' "$TMP_DIR/model.h"

# Container width is structural. Only the bit start is dynamic; the slice width
# is compiled into the selected helper/mask.
grep -Fq 'u256_extract_u64(const sail_u256 value, const uint64_t start)' "$TMP_DIR/model.c"
grep -Fq 'sail_lbits_to_u64_array(result.limbs, 4, value);' "$TMP_DIR/model.c"
grep -Fq 'sail_lbits_from_u64_array(result, value.limbs, 4, UINT64_C(256));' "$TMP_DIR/model.c"
awk '/^static inline sail_u256 u256_of_lbits\(/,/^}/' \
  "$TMP_DIR/model.c" > "$TMP_DIR/u256_of_lbits.helper"
awk '/^static inline void lbits_of_u256\(/,/^}/' \
  "$TMP_DIR/model.c" > "$TMP_DIR/lbits_of_u256.helper"
test -s "$TMP_DIR/u256_of_lbits.helper"
test -s "$TMP_DIR/lbits_of_u256.helper"
if grep -Eq 'mpz_|\.bits' \
    "$TMP_DIR/u256_of_lbits.helper" "$TMP_DIR/lbits_of_u256.helper"; then
  echo 'u256 conversion helper depends directly on a runtime lbits representation' >&2
  exit 1
fi
if grep -Eq 'u256_extract[^\n]*width|const unsigned width' "$TMP_DIR/model.c"; then
  echo 'u256 extraction retained a runtime width parameter' >&2
  exit 1
fi

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
  if grep -Eq 'sail_int|mpz_|lbits|CONVERT_OF' "$TMP_DIR/$function_name.body"; then
    echo "$function_name crossed a Sail/GMP representation boundary" >&2
    exit 1
  fi
}

assert_native_function u256_add 'u256_add('
assert_native_function u256_sub 'u256_sub('
assert_native_function u256_mul 'u256_mul('
assert_native_function u256_and 'u256_and('
assert_native_function u256_or 'u256_or('
assert_native_function u256_xor 'u256_xor('
assert_native_function u256_not 'u256_not('
assert_native_function u256_equal 'eq_u256('
assert_native_function u256_bit 'u256_bit('
assert_native_function u256_shift_left 'u256_shiftl_u64('
assert_native_function u256_shift_right 'u256_shiftr_u64('
assert_native_function u256_arith_shift_right 'u256_arith_shiftr_u64('
assert_native_function u256_from_byte 'u256_of_fbits('
# This is an intentional generic ABI bridge: its source argument really is
# bits(160), so lbits appears in the signature. The bridge implementation must
# still avoid an intermediate sail_int/GMP conversion and use the isolated
# representation adapter above.
extract_function u256_from_lbits
grep -Fq 'u256_of_lbits(' "$TMP_DIR/u256_from_lbits.body"
if grep -Eq 'sail_int|mpz_|CONVERT_OF' "$TMP_DIR/u256_from_lbits.body"; then
  echo 'u256_from_lbits crossed an integer/GMP representation boundary' >&2
  exit 1
fi
assert_native_function u256_low_byte 'u256_extract_u64('
assert_native_function u256_middle_word 'u256_extract_u64('
# This preserved function is the deliberate mixed-representation control.  It
# proves that pruning native-only output does not remove bridges required by a
# real generic result.
extract_function u256_to_nat
grep -Fq 'lbits_of_u256(' "$TMP_DIR/u256_to_nat.body"
grep -Fq 'sail_unsigned' "$TMP_DIR/u256_to_nat.body"
grep -Fq 'sail_int' "$TMP_DIR/u256_to_nat.body"
assert_native_function limb_unsigned '((uint64_t) zvalue)'
assert_native_function limb_signed 'fast_signed(zvalue, 64)'
assert_native_function limb_shift_left '? UINT64_C(0) : ((zvalue << zamount)'
assert_native_function limb_shift_right 'safe_rshift(zvalue, zamount)'
assert_native_function byte_arith_shift_right 'safe_rshift(zvalue, zamount)'
assert_native_function address_equal 'eq_fixed_bytes_20('
extract_function address_equal_vector
if grep -Fq 'eq_fixed_bytes_20(' "$TMP_DIR/address_equal_vector.body"; then
  echo 'mixed fixed-bytes/generic equality selected an incompatible native helper' >&2
  exit 1
fi
assert_native_function address_byte 'fast_unsigned_vector_access_fixed_bytes_20('
assert_native_function address_update 'fast_unsigned_vector_update_fixed_bytes_20('
assert_native_function b160_equal 'eq_fixed_bytes_20('
assert_native_function b256_equal 'eq_fixed_bytes_32('
assert_native_function b256_fill 'fast_unsigned_vector_init_fixed_bytes_32('
assert_native_function b384_equal 'eq_fixed_bytes_48('
assert_native_function b384_byte 'fast_unsigned_vector_access_fixed_bytes_48('
assert_native_function b384_update 'fast_unsigned_vector_update_fixed_bytes_48('
assert_native_function bytes20_inc_byte 'fast_unsigned_vector_access_fixed_bytes_20('
assert_native_function bytes20_inc_update 'fast_unsigned_vector_update_fixed_bytes_20('

# A second extraction from the same source preserves only native entry points.
# Dead generic declarations and fallback definitions must not force their
# compatibility helpers into otherwise runtime-free optimized output.
run_sail --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve u256_add \
  --c-preserve address_equal \
  --c-preserve b256_fill \
  "$SOURCE" -o "$TMP_DIR/native_only"

for generated_file in "$TMP_DIR/native_only.c" "$TMP_DIR/native_only.h"; do
  if grep -Eq 'sail_int|(^|[^[:alnum:]_])lbits([^[:alnum:]_]|$)' "$generated_file"; then
    echo "native-only specialized output retained Sail integer/bitvector compatibility code" >&2
    exit 1
  fi
done

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
  -c "$TMP_DIR/native_only.c" -o "$TMP_DIR/native_only.o"
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS -std=gnu11 -I "$SAIL_DIR/lib" -I "$TMP_DIR" \
  "$TMP_DIR/model.c" "$TEST_DIR/runner.c" "$SAIL_DIR"/lib/*.c $GMP_LIBS -o "$TMP_DIR/runner"
"$TMP_DIR/runner"
