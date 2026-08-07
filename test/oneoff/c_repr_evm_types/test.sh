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
  --c-preserve b256_to_u256 \
  --c-preserve u256_to_b256 \
  --c-preserve address_to_word \
  --c-preserve word_to_address \
  --c-preserve address_alias_low_byte \
  --c-preserve word_address_alias_low_byte \
  --c-preserve word_low_byte \
  --c-preserve limb_unsigned \
  --c-preserve limb_signed \
  --c-preserve limb_shift_left \
  --c-preserve limb_shift_right \
  --c-preserve limb_shift_left_in_range \
  --c-preserve limb_shift_right_in_range \
  --c-preserve byte_widen_identity \
  --c-preserve byte_sign_identity \
  --c-preserve byte_truncate_identity \
  --c-preserve byte_unsigned_extend_truncate_roundtrip \
  --c-preserve byte_sign_extend_truncate_roundtrip \
  --c-preserve word_truncate_byte \
  --c-preserve byte_sign_widen \
  --c-preserve byte_unsigned_extend_truncate_seven \
  --c-preserve byte_sign_extend_truncate_nine \
  --c-preserve byte_arith_shift_right \
  --c-preserve multiply_bit_words \
  --c-preserve multiply_masked_bytes \
  --c-preserve shift_noncontiguous_mask \
  --c-preserve multiply_sliced_bytes \
  --c-preserve multiply_concatenated_bytes \
  --c-preserve concatenate_distinct_sources \
  --c-preserve multiply_inserted_byte \
  --c-preserve insert_byte_at \
  --c-preserve insert_byte_at_unproven \
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

grep -Fq 'typedef struct { uint64_t limbs[4]; } u256;' "$TMP_DIR/model.h"
grep -Fq 'typedef struct { uint8_t bytes[20]; } bytes20;' "$TMP_DIR/model.h"
grep -Fq 'typedef struct { uint8_t bytes[32]; } bytes32;' "$TMP_DIR/model.h"
grep -Fq 'typedef struct { uint8_t bytes[48]; } bytes48;' "$TMP_DIR/model.h"
grep -Eq '^u256 zu256_add\(u256( [[:alnum:]_]+)?, u256( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^u256 zu256_from_lbits\(lbits( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^void zu256_to_nat\(sail_int \*rop, u256( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^uint64_t zu256_bit\(u256( [[:alnum:]_]+)?, uint8_t( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^bytes20 zaddress_update\(bytes20( [[:alnum:]_]+)?, uint8_t( [[:alnum:]_]+)?, uint64_t( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^bytes32 zb256_fill\(uint64_t( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^bytes20 zbytes20_inc_update\(bytes20( [[:alnum:]_]+)?, uint8_t( [[:alnum:]_]+)?, uint64_t( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^u256 zb256_to_u256\(bytes32( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^bytes32 zu256_to_b256\(u256( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^u256 zaddress_to_word\(bytes20( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^bytes20 zword_to_address\(u256( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^uint64_t zaddress_alias_low_byte\(bytes20( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"
grep -Eq '^uint64_t zword_address_alias_low_byte\(u256( [[:alnum:]_]+)?\);$' "$TMP_DIR/model.h"

# Container width is structural. Only the bit start is dynamic; the slice width
# is compiled into the selected helper/mask.
grep -Fq 'u256_extract_u64(const u256 value, const uint64_t start)' "$TMP_DIR/model.c"
grep -Fq 'sail_lbits_to_u64_array(result.limbs, 4, value);' "$TMP_DIR/model.c"
grep -Fq 'sail_lbits_from_u64_array(result, value.limbs, 4, UINT64_C(256));' "$TMP_DIR/model.c"
awk '/^static inline u256 u256_of_lbits\(/,/^}/' \
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
assert_native_function b256_to_u256 'zfrom_bytes_le'
assert_native_function u256_to_b256 'zto_bytes_le'
assert_native_function address_to_word 'zfrom_bytes_le'
assert_native_function word_to_address 'zto_bytes_le'
assert_native_function address_alias_low_byte 'fast_unsigned_vector_access_bytes20('
assert_native_function word_address_alias_low_byte 'zaddress_alias_low_byte('
assert_native_function word_low_byte 'u256_extract_u64('
if grep -Fq 'u256_and(' "$TMP_DIR/word_to_address.body"; then
  echo 'word_to_address masked bits that the fixed-byte conversion already drops' >&2
  exit 1
fi
grep -Fq 'u256_from_bytes20(zv)' "$TMP_DIR/model.c"
grep -Fq 'bytes20_from_u256(zb)' "$TMP_DIR/model.c"
grep -Fq 'u256_from_bytes32(zv)' "$TMP_DIR/model.c"
grep -Fq 'bytes32_from_u256(zb)' "$TMP_DIR/model.c"
# This preserved function is the deliberate mixed-representation control.  It
# proves that pruning native-only output does not remove bridges required by a
# real generic result.
extract_function u256_to_nat
grep -Fq 'u256_unsigned(' "$TMP_DIR/u256_to_nat.body"
grep -Fq 'sail_int' "$TMP_DIR/u256_to_nat.body"
awk '/^static inline void u256_unsigned\(/,/^}/' \
  "$TMP_DIR/model.c" > "$TMP_DIR/u256_unsigned.helper"
grep -Fq 'sail_int_from_u64_array(result, value.limbs, 4);' \
  "$TMP_DIR/u256_unsigned.helper"
if grep -Eq '(^|[^[:alnum:]_])lbits([^[:alnum:]_]|$)|sail_unsigned' \
    "$TMP_DIR/u256_unsigned.helper"; then
  echo 'u256-to-integer conversion detoured through lbits' >&2
  exit 1
fi
assert_native_function limb_unsigned 'uint64_t'
assert_native_function limb_signed 'fast_signed(zvalue, 64)'
assert_native_function limb_shift_left '? UINT64_C(0) : ((zvalue << zamount)'
assert_native_function limb_shift_right 'safe_rshift(zvalue, zamount)'
assert_native_function limb_shift_left_in_range 'zvalue << zamount'
if grep -Fq '>= UINT64_C(64)' "$TMP_DIR/limb_shift_left_in_range.body"; then
  echo 'proved in-range left shift retained its generic C guard' >&2
  exit 1
fi
assert_native_function limb_shift_right_in_range '(zvalue >> zamount)'
if grep -Fq 'safe_rshift' "$TMP_DIR/limb_shift_right_in_range.body"; then
  echo 'proved in-range right shift retained its generic C helper' >&2
  exit 1
fi
assert_native_function byte_widen_identity '= zvalue;'
assert_native_function byte_sign_identity '= zvalue;'
assert_native_function byte_truncate_identity '= zvalue;'
assert_native_function byte_unsigned_extend_truncate_roundtrip '= zvalue;'
assert_native_function byte_sign_extend_truncate_roundtrip '= zvalue;'
for function_name in byte_unsigned_extend_truncate_roundtrip byte_sign_extend_truncate_roundtrip; do
  if grep -Eq 'fast_(zero|sign)_extend|safe_rshift|UINT64_MAX' "$TMP_DIR/$function_name.body"; then
    echo "$function_name retained an extension/truncation round trip" >&2
    exit 1
  fi
done
assert_native_function word_truncate_byte 'UINT64_C(0xFF)'
if grep -Fq 'safe_rshift(zvalue' "$TMP_DIR/word_truncate_byte.body"; then
  echo 'word_truncate_byte retained a generic slice helper for a proven start' >&2
  exit 1
fi
assert_native_function byte_sign_widen 'fast_sign_extend(zvalue, 8, 16)'
assert_native_function byte_unsigned_extend_truncate_seven 'UINT64_C(0x7F)'
assert_native_function byte_sign_extend_truncate_nine 'fast_sign_extend(zvalue, 8, 16)'
grep -Fq 'UINT64_C(0x1FF)' "$TMP_DIR/byte_sign_extend_truncate_nine.body"
assert_native_function byte_arith_shift_right '(zvalue >> zamount)'
if grep -Eq 'safe_rshift|>= UINT64_C\(8\)' "$TMP_DIR/byte_arith_shift_right.body"; then
  echo 'byte_arith_shift_right retained a generic C guard for a proven count' >&2
  exit 1
fi

# Result-bound facts remain attached to calls even when the source and clone
# ABIs are both bits(64).  Equal proof partitions are shared, while the
# preserved full-width control retains its u128 multiplication.
assert_native_function multiply_bit_words 'u128_mul_u64_u64('
assert_native_function multiply_masked_bytes 'multiply_bit_words'
grep -Fq 'UINT64_C(0xFF) & (zvalue >> UINT64_C(8))' "$TMP_DIR/multiply_masked_bytes.body"
if grep -Fq '= (zvalue >> UINT64_C(8));' "$TMP_DIR/multiply_masked_bytes.body"; then
  echo 'multiply_masked_bytes retained its private shift temporary' >&2
  exit 1
fi
assert_native_function shift_noncontiguous_mask 'UINT64_C(0x00000000000000F5)'
grep -Fq '= (zvalue >> UINT64_C(8));' "$TMP_DIR/shift_noncontiguous_mask.body"
assert_native_function multiply_sliced_bytes 'multiply_bit_words'
assert_native_function multiply_concatenated_bytes 'multiply_bit_words'
grep -Fq 'zvalue & UINT64_C(0xFFFF)' "$TMP_DIR/multiply_concatenated_bytes.body"
grep -Fq '>> 8' "$TMP_DIR/multiply_concatenated_bytes.body"
grep -Fq '<< 8' "$TMP_DIR/multiply_concatenated_bytes.body"
if grep -Fq 'UINT64_C(0xFF) &' "$TMP_DIR/multiply_concatenated_bytes.body"; then
  echo 'multiply_concatenated_bytes retained its private slice/concat web' >&2
  exit 1
fi
assert_native_function concatenate_distinct_sources '<< 8) |'
if grep -Fq 'UINT64_C(0xFFFF)' "$TMP_DIR/concatenate_distinct_sources.body"; then
  echo 'concatenate_distinct_sources incorrectly fused slices from distinct sources' >&2
  exit 1
fi
assert_native_function multiply_inserted_byte 'multiply_bit_words'
awk '
  /^u128 zmultiply_bit_words[^(]+\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/multiply_bit_words.clones"
test "$(grep -Ec '^u128 zmultiply_bit_words[^(]+\(' "$TMP_DIR/multiply_bit_words.clones")" -eq 2
grep -Eq 'uint16_t [^;]+;' "$TMP_DIR/multiply_bit_words.clones"
grep -Eq 'uint32_t [^;]+;' "$TMP_DIR/multiply_bit_words.clones"
if grep -Eq 'u128_mul_u64_u64|sail_native_conversion_failure|sail_int|mpz_|lbits|CONVERT_OF' \
    "$TMP_DIR/multiply_bit_words.clones"; then
  echo 'proof-specialized multiply clone retained a wide or managed operation' >&2
  exit 1
fi
grep -Fq '& ~(UINT64_C(0xFF) <<' "$TMP_DIR/multiply_inserted_byte.body"
assert_native_function insert_byte_at '& ~(UINT64_C(0xFF) << zstart)'
grep -Fq '| (zvalue << zstart)' "$TMP_DIR/insert_byte_at.body"
extract_function insert_byte_at_unproven
grep -Fq 'set_slice(' "$TMP_DIR/insert_byte_at_unproven.body"
if ! grep -Eq 'sail_int|lbits|CONVERT_OF' "$TMP_DIR/insert_byte_at_unproven.body"; then
  echo 'insert_byte_at_unproven unexpectedly selected native fixed-width insertion' >&2
  exit 1
fi
assert_native_function address_equal 'eq_bytes20('
assert_native_function address_equal_vector 'eq_bytes20('
assert_native_function address_byte 'fast_unsigned_vector_access_bytes20('
assert_native_function address_update 'fast_unsigned_vector_update_bytes20('
assert_native_function b160_equal 'eq_bytes20('
assert_native_function b256_equal 'eq_bytes32('
assert_native_function b256_fill 'fast_unsigned_vector_init_bytes32('
assert_native_function b384_equal 'eq_bytes48('
assert_native_function b384_byte 'fast_unsigned_vector_access_bytes48('
assert_native_function b384_update 'fast_unsigned_vector_update_bytes48('
assert_native_function bytes20_inc_byte 'fast_unsigned_vector_access_bytes20('
assert_native_function bytes20_inc_update 'fast_unsigned_vector_update_bytes20('

# A second extraction from the same source preserves only native entry points.
# Dead generic declarations and fallback definitions must not force their
# compatibility helpers into otherwise runtime-free optimized output.
run_sail --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve u256_add \
  --c-preserve address_equal \
  --c-preserve b256_fill \
  --c-preserve b256_to_u256 \
  --c-preserve u256_to_b256 \
  --c-preserve address_to_word \
  --c-preserve word_to_address \
  --c-preserve word_address_alias_low_byte \
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
