#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
else
  GMP_CFLAGS=
fi

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_native_integer_widths.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize \
  --c-require-bounded-int --c-no-main \
  --c-preserve keep_u8 --c-preserve keep_u16 --c-preserve keep_u32 --c-preserve keep_u64 \
  --c-preserve keep_i8 --c-preserve keep_i16 --c-preserve keep_i32 --c-preserve keep_i64 \
  --c-preserve multiply_tiny --c-preserve multiply_u8_exact \
  --c-preserve multiply_u16_exact --c-preserve multiply_u32_exact \
  --c-preserve multiply_u8_wrapping --c-preserve multiply_u16_wrapping \
  --c-preserve multiply_u32_wrapping \
  --c-preserve add_u32_exact --c-preserve add_u8_wrapping \
  --c-preserve add_u16_wrapping --c-preserve add_u32_wrapping \
  --c-preserve keep_annotated_u8 --c-preserve keep_annotated_u16 \
  --c-preserve keep_annotated_u32 --c-preserve keep_annotated_u64 \
  --c-preserve keep_annotated_i8 --c-preserve keep_annotated_i16 \
  --c-preserve keep_annotated_i32 --c-preserve keep_annotated_i64 \
  "$TEST_DIR/model.sail" -o "$TMP_DIR/model"

for width in 8 16 32 64; do
  grep -Fq "uint${width}_t zkeep_u${width}(uint${width}_t);" "$TMP_DIR/model.h"
  grep -Fq "int${width}_t zkeep_i${width}(int${width}_t);" "$TMP_DIR/model.h"
  grep -Fq "uint${width}_t zkeep_annotated_u${width}(uint${width}_t);" "$TMP_DIR/model.h"
  grep -Fq "int${width}_t zkeep_annotated_i${width}(int${width}_t);" "$TMP_DIR/model.h"
done

# Semantic ranges, rather than the source spelling of a broad integer type,
# select the carrier of each operation.
grep -Fq 'uint8_t zmultiply_tiny(uint8_t, uint8_t);' "$TMP_DIR/model.h"
grep -Fq 'uint16_t zmultiply_u8_exact(uint8_t, uint8_t);' "$TMP_DIR/model.h"
grep -Fq 'uint32_t zmultiply_u16_exact(uint16_t, uint16_t);' "$TMP_DIR/model.h"
grep -Fq 'uint64_t zmultiply_u32_exact(uint32_t, uint32_t);' "$TMP_DIR/model.h"
grep -Fq 'uint8_t zmultiply_u8_wrapping(uint8_t, uint8_t);' "$TMP_DIR/model.h"
grep -Fq 'uint16_t zmultiply_u16_wrapping(uint16_t, uint16_t);' "$TMP_DIR/model.h"
grep -Fq 'uint32_t zmultiply_u32_wrapping(uint32_t, uint32_t);' "$TMP_DIR/model.h"
grep -Fq 'uint64_t zadd_u32_exact(uint32_t, uint32_t);' "$TMP_DIR/model.h"
grep -Fq 'uint8_t zadd_u8_wrapping(uint8_t, uint8_t);' "$TMP_DIR/model.h"
grep -Fq 'uint16_t zadd_u16_wrapping(uint16_t, uint16_t);' "$TMP_DIR/model.h"
grep -Fq 'uint32_t zadd_u32_wrapping(uint32_t, uint32_t);' "$TMP_DIR/model.h"

awk '
  /^uint8_t zmultiply_tiny\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/multiply_tiny.c"
grep -Fq '((uint8_t)(((uint32_t)' "$TMP_DIR/multiply_tiny.c"

awk '
  /^uint64_t zmultiply_u32_exact\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/multiply_u32_exact.c"
if grep -Fq 'sail_int' "$TMP_DIR/multiply_u32_exact.c"; then
  echo 'exact u32 multiplication fell back to mathematical integer lowering' >&2
  exit 1
fi
grep -Eq '= \([^;]+ \* [^;]+\);' "$TMP_DIR/multiply_u32_exact.c"

for width in 8 16; do
  awk -v width="$width" '
    $0 ~ "^uint" width "_t zmultiply_u" width "_wrapping\\(" { printing = 1 }
    printing { print }
    printing && /^}$/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/multiply_u${width}_wrapping.c"
  grep -Fq "((uint${width}_t)(((uint32_t)" "$TMP_DIR/multiply_u${width}_wrapping.c"
  if grep -Eq 'sail_int|mult_int|tmod_(int|nat)' "$TMP_DIR/multiply_u${width}_wrapping.c"; then
    echo "u${width} wrapping multiplication fell back to mathematical integer lowering" >&2
    exit 1
  fi
done

awk '
  /^uint32_t zmultiply_u32_wrapping\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/multiply_u32_wrapping.c"
grep -Eq '= \([^;]+ \* [^;]+\);' "$TMP_DIR/multiply_u32_wrapping.c"
if grep -Eq 'sail_int|mult_int|tmod_(int|nat)' "$TMP_DIR/multiply_u32_wrapping.c"; then
  echo 'u32 wrapping multiplication changed carrier or fell back to mathematical integer lowering' >&2
  exit 1
fi

for width in 8 16 32; do
  awk -v width="$width" '
    $0 ~ "^uint" width "_t zadd_u" width "_wrapping\\(" { printing = 1 }
    printing { print }
    printing && /^}$/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/add_u${width}_wrapping.c"
  if grep -Eq 'sail_int|add_(int|atom)|tmod_(int|nat)' "$TMP_DIR/add_u${width}_wrapping.c"; then
    echo "u${width} wrapping addition fell back to mathematical integer lowering" >&2
    exit 1
  fi
done
grep -Fq '((uint8_t)(((uint32_t)' "$TMP_DIR/add_u8_wrapping.c"
grep -Fq '((uint16_t)(((uint32_t)' "$TMP_DIR/add_u16_wrapping.c"
grep -Eq '= \([^;]+ \+ [^;]+\);' "$TMP_DIR/add_u32_wrapping.c"

awk '
  /^uint64_t zadd_u32_exact\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/add_u32_exact.c"
grep -Eq '= \([^;]+ \+ [^;]+\);' "$TMP_DIR/add_u32_exact.c"
if grep -Fq 'sail_int' "$TMP_DIR/add_u32_exact.c"; then
  echo 'exact u32 addition fell back to mathematical integer lowering' >&2
  exit 1
fi

if grep -Fq 'sail_int' "$TMP_DIR/model.h"; then
  echo 'bounded native-width API exposed sail_int' >&2
  exit 1
fi

# Word splitting is intentional for compiler, user, and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS -std=c11 -c "$TMP_DIR/model.c" -I "$SAIL_DIR/lib" -o "$TMP_DIR/model.o"
