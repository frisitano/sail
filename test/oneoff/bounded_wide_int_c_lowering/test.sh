#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/bounded_wide_int_c_lowering.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

OUT="$TMP_DIR/model"
if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi
"$SAIL" "$@" --no-color --no-memo-z3 -c --c-specialize --c-no-main \
  --c-preserve add_widen_128 --c-preserve mul_widen_128 \
  --c-preserve add_widen_256 \
  --c-preserve add_256_128 --c-preserve mul_256_128 \
  --c-preserve sub_256_128 --c-preserve div_256_128 \
  --c-preserve mod_256_128 --c-preserve lt_256_128 \
  --c-preserve eq_256_128 --c-preserve neq_128_256 \
  --c-preserve lt_128_256 --c-preserve sub_128_256 \
  --c-preserve div_128_256 --c-preserve mod_128_256 \
  "$TEST_DIR/model.sail" -o "$OUT"

grep -Fq 'u256_add_u128_u128(zleft, zright)' "$OUT.c"
grep -Fq 'u256_mul_u128_u128(zleft, zright)' "$OUT.c"
grep -Fq 'u256_mul_u128(zleft, zright)' "$OUT.c"
grep -Fq 'u256_div_u128(zleft, zright)' "$OUT.c"
grep -Fq 'u256_eq_u128(zleft, zright)' "$OUT.c"
grep -Fq 'u256_eq_u128(zright, zleft)' "$OUT.c"
grep -Fq 'u128_lt_u256(zleft, zright)' "$OUT.c"
grep -Fq 'u128_sub_u256(zleft, zright)' "$OUT.c"
grep -Fq 'u128_div_u256(zleft, zright)' "$OUT.c"
grep -Fq 'u128_mod_u256(zleft, zright)' "$OUT.c"
if sed -n '/^sail_u256 zadd_widen_128(/,/^}/p' "$OUT.c" | grep -Fq sail_int; then
  echo 'widened fixed-width operation retained sail_int' >&2
  exit 1
fi

# Storage representations do not change mathematical integer semantics. Two
# u256 operands can sum to 257 bits, so this operation must widen to the native
# u320 representation rather than silently becoming modular u256 arithmetic.
sed -n '/^sail_u320 zadd_widen_256(/,/^}/p' "$OUT.c" > "$TMP_DIR/add_widen_256.c"
grep -Fq 'u320_add_widen(zleft, zright)' "$TMP_DIR/add_widen_256.c"
if grep -Fq 'sail_int' "$TMP_DIR/add_widen_256.c"; then
  echo '257-bit mathematical addition retained sail_int' >&2
  exit 1
fi
if grep -Fq 'u256_add(' "$TMP_DIR/add_widen_256.c"; then
  echo '257-bit mathematical addition was silently lowered as modular u256' >&2
  exit 1
fi

# Word splitting is intentional for compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} -std=gnu11 -O2 -shared -fPIC $GMP_CFLAGS \
  "$OUT.c" "$SAIL_DIR"/lib/*.c -I "$TMP_DIR" -I "$SAIL_DIR/lib" \
  $GMP_LIBS -o "$TMP_DIR/model.so"

MODEL_LIB="$TMP_DIR/model.so" python3 "$TEST_DIR/property_test.py"
