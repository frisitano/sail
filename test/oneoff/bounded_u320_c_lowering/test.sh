#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/bounded_u320_c_lowering.XXXXXX")
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
  --c-preserve top_level_int_identity \
  --c-preserve max_u64_holder \
  --c-preserve add_u320 --c-preserve sub_u320 --c-preserve mul_u320 \
  --c-preserve add_u320_u64 --c-preserve sub_u320_u64 \
  --c-preserve mul_u320_u64 --c-preserve div_u320_u64 \
  --c-preserve mod_u320_u64 --c-preserve div_u320 \
  --c-preserve mod_u320 --c-preserve lt_u320 \
  --c-preserve lteq_u320 --c-preserve gt_u320 --c-preserve gteq_u320 \
  --c-preserve eq_u320 --c-preserve neq_u320 \
  --c-preserve lt_u320_u64 --c-preserve eq_u320_u64 \
  --c-preserve widen_u320_to_nat \
  "$TEST_DIR/model.sail" -o "$OUT"

grep -Fq 'typedef struct { uint64_t limbs[5]; } sail_u320;' "$OUT.h"
grep -Fq 'UINT64_C(18446744073709551615)' "$OUT.c"
sed -n '/^.* ztop_level_int_identity(/,/^}/p' "$OUT.c" | grep -Fq 'sail_int'
if grep -Fq 'convert_mach_uint_of_sail_string' "$OUT.c"; then
  echo "u64::MAX retained a managed string conversion" >&2
  exit 1
fi
grep -Fq 'u320_add_widen(zleft, zright)' "$OUT.c"
grep -Fq 'u320_sub(zleft, zright)' "$OUT.c"
grep -Fq 'u320_mul_widen(zleft, zright)' "$OUT.c"
grep -Fq 'u320_add_widen(zleft, zright)' "$OUT.c"
grep -Fq 'u320_mul_widen(zleft, zright)' "$OUT.c"
grep -Fq 'u320_div_u64(zleft, zright)' "$OUT.c"
grep -Fq 'u320_mod_u64(zleft, zright)' "$OUT.c"
grep -Fq 'u320_div(zleft, zright)' "$OUT.c"
grep -Fq 'u320_mod(zleft, zright)' "$OUT.c"
grep -Fq 'u320_lt(zleft, zright)' "$OUT.c"
grep -Fq 'eq_u320(zleft, zright)' "$OUT.c"
# The public wrapper may call a specialized fixed-representation callee rather
# than inline it.  Require the actual conversion call somewhere in generated
# code without assuming that it is textually inside the wrapper.
grep -Eq '^[[:space:]]+u320_unsigned\(' "$OUT.c"

# Strict mode is a post-specialization audit, not a representation-selection
# mode. A completely bounded program must therefore lower byte-for-byte
# identically with and without the audit enabled.
NONSTRICT_AUDIT_OUT="$TMP_DIR/audit-off/model"
STRICT_AUDIT_OUT="$TMP_DIR/audit-on/model"
mkdir -p "$(dirname "$NONSTRICT_AUDIT_OUT")" "$(dirname "$STRICT_AUDIT_OUT")"
"$SAIL" "$@" --no-color --no-memo-z3 -c --c-specialize --c-no-main \
  --c-preserve max_u64_holder \
  "$TEST_DIR/model.sail" -o "$NONSTRICT_AUDIT_OUT"
"$SAIL" "$@" --no-color --no-memo-z3 -c --c-specialize \
  --c-require-bounded-int --c-no-main \
  --c-preserve max_u64_holder \
  "$TEST_DIR/model.sail" -o "$STRICT_AUDIT_OUT"
cmp -s "$NONSTRICT_AUDIT_OUT.c" "$STRICT_AUDIT_OUT.c"
cmp -s "$NONSTRICT_AUDIT_OUT.h" "$STRICT_AUDIT_OUT.h"

STRICT_OUT="$TMP_DIR/strict"
if "$SAIL" "$@" --no-color --no-memo-z3 -c --c-specialize \
  --c-require-bounded-int --c-no-main \
  --c-preserve widen_u320_to_nat \
  "$TEST_DIR/model.sail" -o "$STRICT_OUT" \
  >"$TMP_DIR/strict.log" 2>&1
then
  echo "--c-require-bounded-int accepted an intentionally managed nat" >&2
  exit 1
fi
grep -Fq 'cannot select a native integer representation' "$TMP_DIR/strict.log"

for function in \
  add_u320 sub_u320 mul_u320 add_u320_u64 sub_u320_u64 \
  mul_u320_u64 div_u320_u64 mod_u320_u64 div_u320 mod_u320 \
  lt_u320 lteq_u320 gt_u320 gteq_u320 eq_u320 neq_u320 \
  lt_u320_u64 eq_u320_u64
do
  if sed -n "/^.* z${function}(/,/^}/p" "$OUT.c" | grep -Fq sail_int; then
    echo "$function retained sail_int" >&2
    exit 1
  fi
done

# Word splitting is intentional for compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} -std=gnu11 -O2 -shared -fPIC $GMP_CFLAGS \
  "$OUT.c" "$SAIL_DIR"/lib/*.c -I "$TMP_DIR" -I "$SAIL_DIR/lib" \
  $GMP_LIBS -o "$TMP_DIR/model.so"

CARGO_TARGET_DIR="$TMP_DIR/cargo-target" MODEL_LIB="$TMP_DIR/model.so" \
  cargo run --quiet --manifest-path "$TEST_DIR/Cargo.toml"
