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
if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

"$SAIL" "$@" --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve proven_u64_add_32 --c-preserve proven_u64_sub_95 \
  --c-preserve proven_u64_mul --c-preserve proven_u64_div \
  --c-preserve proven_u64_mod --c-preserve proven_i64_add \
  --c-preserve proven_i64_sub --c-preserve proven_i64_mul \
  --c-preserve proven_i64_div --c-preserve proven_i64_mod \
  --c-preserve proven_i128_add --c-preserve proven_i128_sub \
  --c-preserve proven_i128_mul --c-preserve proven_i128_div \
  --c-preserve proven_i128_mod --c-preserve mixed_i128_u64_lte \
  --c-preserve mixed_u64_i128_lte --c-preserve mixed_i8_u8_lt \
  --c-preserve bounded_signed_lt \
  --c-preserve path_narrow_signed_lt \
  --c-preserve checked_u64_add --c-preserve checked_u64_sub \
  --c-preserve checked_u64_mul --c-preserve checked_u64_div \
  --c-preserve checked_u64_mod --c-preserve checked_i64_add \
  --c-preserve power_two_tdiv --c-preserve power_two_tmod \
  --c-preserve power_two_ediv --c-preserve power_two_emod \
  --c-preserve mixed_u64_u8_div --c-preserve mixed_u64_u8_mod \
  --c-preserve mixed_u32_negative_i8_div \
  --c-preserve checked_i64_sub --c-preserve checked_i64_mul \
  --c-preserve checked_i64_div --c-preserve checked_i64_mod \
  --c-preserve signed_tdiv_by_eight --c-preserve signed_tmod_by_eight \
  --c-preserve signed_ediv_by_eight --c-preserve signed_emod_by_eight \
  --c-preserve mixed_i64_i8_div --c-preserve mixed_i64_i8_mod \
  --c-preserve signed_u64_difference \
  "$TEST_DIR/../../c/native_checked_arithmetic.sail" -o "$OUT"

# Word splitting is intentional for compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS "$TEST_DIR/runner.c" "$SAIL_DIR"/lib/*.c \
  -I "$TMP_DIR" -I "$SAIL_DIR/lib" $GMP_LIBS -o "$OUT.bin"

"$OUT.bin"

# Fixed-width arithmetic has no runtime overflow/division checks.
if grep -Eq 'sail_checked_(u64|i64)_(add|sub|mul|div|mod)' "$OUT.c"; then
  echo "generated C contains checked fixed-width arithmetic" >&2
  exit 1
fi

# An ABI representation is not itself an arithmetic proof. Broad add/sub/mul
# operations use a wider fixed carrier before converting back to the ABI;
# they must not silently perform the operation at uint64_t/int64_t width.
grep -Fq 'u128_add_u64' "$OUT.c"
grep -Fq 'u128_mul_u64' "$OUT.c"
for target in zchecked_i64_add zchecked_i64_sub zchecked_i64_mul
do
  awk -v target="$target" '
    $0 ~ ("^.* " target "\\(") { in_function = 1 }
    in_function && /__int128/ { found_wide = 1 }
    in_function && /sail_native_conversion_failure/ { found_checked_boundary = 1 }
    in_function && /^}/ { exit !found_wide || !found_checked_boundary }
    END { if (!in_function) exit 2 }
  ' "$OUT.c"
done

# Broad signed division and remainder still include zero and MIN / -1, so
# they remain in Sail's mathematical-integer runtime. The guarded unsigned
# versions are checked below and lower natively on their nonzero branch.
for target in zchecked_i64_div zchecked_i64_mod
do
  awk -v target="$target" '
    $0 ~ ("^.* " target "\\(") { in_function = 1 }
    in_function && /(tdiv_int|tmod_int)/ { found_math = 1 }
    in_function && /^}/ { exit !found_math }
    END { if (!in_function) exit 2 }
  ' "$OUT.c"
done

# An exact semantic divisor range and a nonnegative dividend prove that both
# truncating and Euclidean division by eight have unsigned shift/mask semantics.
# The explicit proof-carrying JIB operations omit the divisor entirely.
for target in zpower_two_tdiv zpower_two_ediv
do
  awk -v target="$target" '
    $0 ~ ("^.* " target "\\(") { in_function = 1 }
    in_function && />> 3/ { found_shift = 1 }
    in_function && /[[:space:]]\/[[:space:]]/ { found_divide = 1 }
    in_function && /^}/ { exit !found_shift || found_divide }
    END { if (!in_function) exit 2 }
  ' "$OUT.c"
done
for target in zpower_two_tmod zpower_two_emod
do
  awk -v target="$target" '
    $0 ~ ("^.* " target "\\(") { in_function = 1 }
    in_function && /& .*UINT64_C\(7\)/ { found_mask = 1 }
    in_function && /[[:space:]]%[[:space:]]/ { found_remainder = 1 }
    in_function && /^}/ { exit !found_mask || found_remainder }
    END { if (!in_function) exit 2 }
  ' "$OUT.c"
done

# A fixed signed representation does not prove a nonnegative dividend.
# Truncating operations keep C's signed rounding semantics, while Euclidean
# operations retain their mathematical helpers rather than being rewritten.
awk '
  /^int64_t zsigned_tdiv_by_eight\(/ { in_function = 1 }
  in_function && /zvalue.*\/.*\(int64_t\)zdivisor/ { found_divide = 1 }
  in_function && /integer_operand/ { found_widened_operand = 1 }
  in_function && />> 3/ { found_shift = 1 }
  in_function && /^}/ { exit !found_divide || found_widened_operand || found_shift }
  END { if (!in_function) exit 2 }
' "$OUT.c"
awk '
  /^int64_t zsigned_tmod_by_eight\(/ { in_function = 1 }
  in_function && /zvalue.*%.*\(int64_t\)zdivisor/ { found_remainder = 1 }
  in_function && /integer_operand/ { found_widened_operand = 1 }
  in_function && /UINT64_C\(7\)/ { found_mask = 1 }
  in_function && /^}/ { exit !found_remainder || found_widened_operand || found_mask }
  END { if (!in_function) exit 2 }
' "$OUT.c"
for target in zsigned_ediv_by_eight zsigned_emod_by_eight
do
  awk -v target="$target" '
    $0 ~ ("^.* " target "\\(") { in_function = 1 }
    in_function && /(ediv_int|emod_int)/ { found_math = 1 }
    in_function && /(>> 3|UINT64_C\(7\))/ { found_strength_reduction = 1 }
    in_function && /^}/ { exit !found_math || found_strength_reduction }
    END { if (!in_function) exit 2 }
  ' "$OUT.c"
done

# Mixed fixed operands retain their independently proved ABI widths. The
# operation records a separate semantic result carrier: the u64 quotient stays
# u64, while the remainder bounded by the u8 divisor is computed into u8.
grep -Eq '^uint64_t zmixed_u64_u8_div\(uint64_t [^,]+, uint8_t [^)]+\);$' "$OUT.h"
grep -Eq '^uint64_t zmixed_u64_u8_mod\(uint64_t [^,]+, uint8_t [^)]+\);$' "$OUT.h"
awk '
  /^uint64_t zmixed_u64_u8_div\(/ { in_function = 1 }
  in_function && /zleft.*\/.*\(uint64_t\)zright/ { found_mixed_divide = 1 }
  in_function && /uint64_t .*integer_operand/ { found_widened_operand = 1 }
  in_function && /^}/ { exit !found_mixed_divide || found_widened_operand }
  END { if (!in_function) exit 2 }
' "$OUT.c"
awk '
  /^uint64_t zmixed_u64_u8_mod\(/ { in_function = 1 }
  in_function && /zleft.*%.*\(uint64_t\)zright/ { found_mixed_remainder = 1 }
  in_function && /= \(\(uint8_t\).*zleft.*%/ { found_narrow_result = 1 }
  in_function && /uint64_t .*integer_operand/ { found_widened_operand = 1 }
  in_function && /^}/ { exit !found_mixed_remainder || !found_narrow_result || found_widened_operand }
  END { if (!in_function) exit 2 }
' "$OUT.c"

grep -Eq '^int64_t zmixed_i64_i8_div\(int64_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
grep -Eq '^int64_t zmixed_i64_i8_mod\(int64_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
awk '
  /^int64_t zmixed_i64_i8_div\(/ { in_function = 1 }
  in_function && /zleft.*\/.*\(int64_t\)zright/ { found_mixed_divide = 1 }
  in_function && /int64_t .*integer_operand/ { found_widened_operand = 1 }
  in_function && /^}/ { exit !found_mixed_divide || found_widened_operand }
  END { if (!in_function) exit 2 }
' "$OUT.c"
awk '
  /^int64_t zmixed_i64_i8_mod\(/ { in_function = 1 }
  in_function && /zleft.*%.*\(int64_t\)zright/ { found_mixed_remainder = 1 }
  in_function && /= \(\(int8_t\).*zleft.*%/ { found_narrow_result = 1 }
  in_function && /int64_t .*integer_operand/ { found_widened_operand = 1 }
  in_function && /^}/ { exit !found_mixed_remainder || !found_narrow_result || found_widened_operand }
  END { if (!in_function) exit 2 }
' "$OUT.c"

# A negative signed operand cannot be converted to an equally wide unsigned
# arithmetic carrier without changing its semantic value.  Keep the fixed
# representations, but fall back to a sufficiently wide signed operation.
grep -Eq '^int64_t zmixed_u32_negative_i8_div\(uint32_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
awk '
  /^int64_t zmixed_u32_negative_i8_div\(/ { in_function = 1 }
  in_function && /\(int64_t\)[[:space:]]*zleft.*\/.*\(int64_t\)[[:space:]]*zright/ { found_exact_signed = 1 }
  in_function && /[[:space:]]\/[[:space:]]/ && /uint(32|64)_t/ { found_inexact_unsigned = 1 }
  in_function && /^}/ { exit !found_exact_signed || found_inexact_unsigned }
  END { if (!in_function) exit 2 }
' "$OUT.c"

# A mathematical result remains mathematical even when both operands use a
# represented uint64 ABI. The subtraction must happen after widening.
grep -Eq '^void zsigned_u64_difference\(sail_int \*rop, uint64_t [^,]+, uint64_t [^)]+\);$' "$OUT.h"
awk '
  /^void zsigned_u64_difference\(/ { in_function = 1 }
  in_function && /sub_int/ { found_wide_sub = 1 }
  in_function && / - / { found_native_sub = 1 }
  in_function && /^}/ { exit !found_wide_sub || found_native_sub }
  END { if (!in_function) exit 2 }
' "$OUT.c"

# A dependent result bound proves this addition cannot overflow its native
# representation, so the generated C uses the machine operation directly.
grep -Eq '^uint64_t zproven_u64_add_32\(uint64_t [^)]+\);$' "$OUT.h"
awk '
  /^uint64_t zproven_u64_add_32\(/ { in_function = 1 }
  in_function && /\+ .*UINT64_C\(32\)/ { found_add = 1 }
  in_function && /^}/ { exit !found_add }
  END { if (!in_function) exit 2 }
' "$OUT.c"

grep -Eq '^uint64_t zproven_u64_sub_95\(uint64_t [^)]+\);$' "$OUT.h"
awk '
  /^uint64_t zproven_u64_sub_95\(/ { in_function = 1 }
  in_function && /- .*UINT64_C\(95\)/ { found_sub = 1 }
  in_function && /^}/ { exit !found_sub }
  END { if (!in_function) exit 2 }
' "$OUT.c"

grep -Eq '^uint16_t zproven_u64_mul\(uint8_t [^,]+, uint8_t [^)]+\);$' "$OUT.h"
grep -Fq ' = (zleft * zright);' "$OUT.c"

# Division and modulo additionally require a proof that the divisor is nonzero;
# signed division must also exclude INT64_MIN / -1.
grep -Eq '^void zproven_u64_div\(sail_int \*rop, uint8_t [^,]+, uint8_t [^)]+\);$' "$OUT.h"
grep -Eq '^void zproven_u64_mod\(sail_int \*rop, uint8_t [^,]+, uint8_t [^)]+\);$' "$OUT.h"
grep -Fq '(zleft / zright)' "$OUT.c"
grep -Fq '(zleft % zright)' "$OUT.c"

grep -Eq '^int16_t zproven_i64_add\(int8_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
grep -Eq '^int16_t zproven_i64_sub\(int8_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
grep -Eq '^int16_t zproven_i64_mul\(int8_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
grep -Eq '^void zproven_i64_div\(sail_int \*rop, int8_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
grep -Eq '^void zproven_i64_mod\(sail_int \*rop, int8_t [^,]+, int8_t [^)]+\);$' "$OUT.h"
grep -Fq ' = (zleft + zright);' "$OUT.c"
grep -Fq ' = (zleft - zright);' "$OUT.c"
grep -Fq ' = (zleft * zright);' "$OUT.c"
grep -Fq '(zleft / zright)' "$OUT.c"
grep -Fq '(zleft % zright)' "$OUT.c"

# Signed values whose honest semantic envelope exceeds i64 use the native
# signed 128-bit carrier.  The same proof-gated arithmetic rules apply: there
# are no overflow checks or saturating fallbacks in the generated operation.
grep -Eq '^__int128 zproven_i128_add\(__int128 [^,]+, __int128 [^)]+\);$' "$OUT.h"
grep -Eq '^__int128 zproven_i128_sub\(__int128 [^,]+, __int128 [^)]+\);$' "$OUT.h"
grep -Eq '^__int128 zproven_i128_mul\(__int128 [^,]+, __int128 [^)]+\);$' "$OUT.h"
grep -Eq '^__int128 zproven_i128_div\(u128 [^,]+, u128 [^)]+\);$' "$OUT.h"
grep -Eq '^__int128 zproven_i128_mod\(u128 [^,]+, u128 [^)]+\);$' "$OUT.h"
for operator in '+' '-' '*'
do
  grep -Fq " = (zleft $operator zright);" "$OUT.c"
done
grep -Fq 'u128_div(zleft, zright)' "$OUT.c"
grep -Fq 'u128_mod(zleft, zright)' "$OUT.c"
grep -Eq '^bool zmixed_i128_u64_lte\(__int128 [^,]+, uint64_t [^)]+\);$' "$OUT.h"
grep -Eq '^bool zmixed_u64_i128_lte\(uint64_t [^,]+, __int128 [^)]+\);$' "$OUT.h"
if awk '
  /^bool zmixed_i128_u64_lte\(/ { in_function = 1 }
  in_function && /(sail_int|lteq_int|lt_int)/ { found_wide = 1 }
  in_function && /^}/ { exit found_wide }
  END { if (!in_function) exit 2 }
' "$OUT.c"; then :; else
  echo "mixed i128/u64 comparison used arbitrary-precision integers" >&2
  exit 1
fi
if awk '
  /^bool zmixed_u64_i128_lte\(/ { in_function = 1 }
  in_function && /(sail_int|lteq_int|lt_int)/ { found_wide = 1 }
  in_function && /^}/ { exit found_wide }
  END { if (!in_function) exit 2 }
' "$OUT.c"; then :; else
  echo "mixed u64/i128 comparison used arbitrary-precision integers" >&2
  exit 1
fi
grep -Eq '^bool zmixed_i8_u8_lt\(int8_t [^,]+, uint8_t [^)]+\);$' "$OUT.h"
awk '
  /^bool zmixed_i8_u8_lt\(/ { in_function = 1 }
  in_function && /zleft.*<.*zright/ { found_native_comparison = 1 }
  in_function && /(sail_int|cmp_int)/ { found_math = 1 }
  in_function && /^}/ { exit !found_native_comparison || found_math }
  END { if (!in_function) exit 2 }
' "$OUT.c"
grep -Eq '^bool zpath_narrow_signed_lt\(int64_t [^,]+, int64_t [^)]+\);$' "$OUT.h"
awk '
  /^bool zpath_narrow_signed_lt\(/ { in_function = 1 }
  in_function && /zbounded_signed_lt.*\(int8_t\).*zleft.*\(int8_t\).*zright/ { found_narrow_call = 1 }
  in_function && /sail_native_conversion_failure/ { found_checked_conversion = 1 }
  in_function && /^}/ { exit !found_narrow_call || found_checked_conversion }
  END { if (!in_function) exit 2 }
' "$OUT.c"
if grep -Fq 'if (u128_is_zero(divisor))' "$OUT.c"; then
  echo "u128 division retained a runtime zero-divisor check" >&2
  exit 1
fi
if grep -Fq 'if (divisor != UINT64_C(0))' "$OUT.c"; then
  echo "u128/u64 division retained a runtime zero-divisor check" >&2
  exit 1
fi
