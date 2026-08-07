#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_anf_conversion_binding.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize --c-no-main \
  --c-preserve little_endian_u32 "$TEST_DIR/model.sail" -o "$TMP_DIR/model"

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

# Compiling the generated translation unit catches conversion bindings whose
# definitions were incorrectly removed while their canonical JIB names remain
# live in subsequent shift/or expressions.
# Word splitting is intentional for compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS -std=gnu11 -Werror -I "$SAIL_DIR/lib" -I "$TMP_DIR" \
  "$TMP_DIR/model.c" "$TEST_DIR/runner.c" "$SAIL_DIR"/lib/*.c $GMP_LIBS -o "$TMP_DIR/runner"
"$TMP_DIR/runner"
