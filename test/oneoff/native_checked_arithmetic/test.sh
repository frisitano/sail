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
  --c-preserve proven_u64_add_32 --c-preserve proven_u64_sub_95 \
  --c-preserve proven_u64_mul --c-preserve proven_u64_div \
  --c-preserve proven_u64_mod --c-preserve proven_i64_add \
  --c-preserve proven_i64_sub --c-preserve proven_i64_mul \
  --c-preserve proven_i64_div --c-preserve proven_i64_mod \
  --c-preserve proven_i128_add --c-preserve proven_i128_sub \
  --c-preserve proven_i128_mul --c-preserve proven_i128_div \
  --c-preserve proven_i128_mod --c-preserve mixed_i128_u64_lte \
  --c-preserve mixed_u64_i128_lte \
  --c-preserve checked_u64_add --c-preserve checked_u64_sub \
  --c-preserve checked_u64_mul --c-preserve checked_u64_div \
  --c-preserve checked_u64_mod --c-preserve checked_i64_add \
  --c-preserve checked_i64_sub --c-preserve checked_i64_mul \
  --c-preserve checked_i64_div --c-preserve checked_i64_mod \
  --c-preserve signed_u64_difference \
  "$TEST_DIR/../../c/native_checked_arithmetic.sail" -o "$OUT"

# Word splitting is intentional for compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS "$TEST_DIR/runner.c" "$SAIL_DIR"/lib/*.c \
  -I "$TMP_DIR" -I "$SAIL_DIR/lib" $GMP_LIBS -o "$OUT.bin"

"$OUT.bin"

# Fixed-width arithmetic has no runtime overflow/division checks. Operations
# without a source proof remain in Sail's mathematical integer domain.
if grep -Eq 'sail_checked_(u64|i64)_(add|sub|mul|div|mod)' "$OUT.c"; then
  echo "generated C contains checked fixed-width arithmetic" >&2
  exit 1
fi
grep -Fq 'add_int' "$OUT.c"
grep -Fq 'mult_int' "$OUT.c"

# An ABI representation is not an arithmetic proof.  The unbounded carrier
# operations below must stay in Sail's mathematical-integer runtime even
# though their arguments and results cross the ABI as uint64_t/int64_t.
for target in \
  zchecked_u64_add zchecked_u64_mul zchecked_u64_div zchecked_u64_mod \
  zchecked_i64_add zchecked_i64_sub zchecked_i64_mul \
  zchecked_i64_div zchecked_i64_mod
do
  awk -v target="$target" '
    $0 ~ ("^.* " target "\\(") { in_function = 1 }
    in_function && /(add_int|sub_int|mult_int|tdiv_int|tmod_int)/ { found_math = 1 }
    in_function && /^}/ { exit !found_math }
    END { if (!in_function) exit 2 }
  ' "$OUT.c"
done

# A mathematical result remains mathematical even when both operands use a
# represented uint64 ABI. The subtraction must happen after widening.
grep -Fq 'void zsigned_u64_difference(sail_int *rop, uint64_t, uint64_t);' "$OUT.h"
awk '
  /^void zsigned_u64_difference\(/ { in_function = 1 }
  in_function && /sub_int/ { found_wide_sub = 1 }
  in_function && / - / { found_native_sub = 1 }
  in_function && /^}/ { exit !found_wide_sub || found_native_sub }
  END { if (!in_function) exit 2 }
' "$OUT.c"

# A dependent result bound proves this addition cannot overflow its native
# representation, so the generated C uses the machine operation directly.
grep -Fq 'uint64_t zproven_u64_add_32(uint64_t);' "$OUT.h"
awk '
  /^uint64_t zproven_u64_add_32\(/ { in_function = 1 }
  in_function && /\+ UINT64_C\(32\)/ { found_add = 1 }
  in_function && /^}/ { exit !found_add }
  END { if (!in_function) exit 2 }
' "$OUT.c"

grep -Fq 'uint64_t zproven_u64_sub_95(uint64_t);' "$OUT.h"
awk '
  /^uint64_t zproven_u64_sub_95\(/ { in_function = 1 }
  in_function && /- UINT64_C\(95\)/ { found_sub = 1 }
  in_function && /^}/ { exit !found_sub }
  END { if (!in_function) exit 2 }
' "$OUT.c"

grep -Fq 'uint64_t zproven_u64_mul(uint64_t, uint64_t);' "$OUT.h"
grep -Fq ' = (zleft * zright);' "$OUT.c"

# Division and modulo additionally require a proof that the divisor is nonzero;
# signed division must also exclude INT64_MIN / -1.
grep -Fq 'void zproven_u64_div(sail_int *rop, uint64_t, uint64_t);' "$OUT.h"
grep -Fq 'void zproven_u64_mod(sail_int *rop, uint64_t, uint64_t);' "$OUT.h"
grep -Fq '(zleft / zright)' "$OUT.c"
grep -Fq '(zleft % zright)' "$OUT.c"

grep -Fq 'int64_t zproven_i64_add(int64_t, int64_t);' "$OUT.h"
grep -Fq 'int64_t zproven_i64_sub(int64_t, int64_t);' "$OUT.h"
grep -Fq 'int64_t zproven_i64_mul(int64_t, int64_t);' "$OUT.h"
grep -Fq 'void zproven_i64_div(sail_int *rop, int64_t, int64_t);' "$OUT.h"
grep -Fq 'void zproven_i64_mod(sail_int *rop, int64_t, int64_t);' "$OUT.h"
grep -Fq ' = (zleft + zright);' "$OUT.c"
grep -Fq ' = (zleft - zright);' "$OUT.c"
grep -Fq ' = (zleft * zright);' "$OUT.c"
grep -Fq '(zleft / zright)' "$OUT.c"
grep -Fq '(zleft % zright)' "$OUT.c"

# Signed values whose honest semantic envelope exceeds i64 use the native
# signed 128-bit carrier.  The same proof-gated arithmetic rules apply: there
# are no overflow checks or saturating fallbacks in the generated operation.
grep -Fq '__int128 zproven_i128_add(__int128, __int128);' "$OUT.h"
grep -Fq '__int128 zproven_i128_sub(__int128, __int128);' "$OUT.h"
grep -Fq '__int128 zproven_i128_mul(__int128, __int128);' "$OUT.h"
grep -Fq '__int128 zproven_i128_div(sail_u128, sail_u128);' "$OUT.h"
grep -Fq '__int128 zproven_i128_mod(sail_u128, sail_u128);' "$OUT.h"
for operator in '+' '-' '*'
do
  grep -Fq " = (zleft $operator zright);" "$OUT.c"
done
grep -Fq 'u128_div(zleft, zright)' "$OUT.c"
grep -Fq 'u128_mod(zleft, zright)' "$OUT.c"
grep -Fq 'bool zmixed_i128_u64_lte(__int128, uint64_t);' "$OUT.h"
grep -Fq 'bool zmixed_u64_i128_lte(uint64_t, __int128);' "$OUT.h"
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
if grep -Fq 'if (u128_is_zero(divisor))' "$OUT.c"; then
  echo "u128 division retained a runtime zero-divisor check" >&2
  exit 1
fi
if grep -Fq 'if (divisor != UINT64_C(0))' "$OUT.c"; then
  echo "u128/u64 division retained a runtime zero-divisor check" >&2
  exit 1
fi
