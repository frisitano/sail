#!/bin/sh

set -eu

cd "$(dirname "$0")"

trap 'rm -f mangled.c mangled.h readable.c readable.h readable.bin sail_smt_cache' EXIT

SAIL=${SAIL:-sail}
CC=${CC:-cc}
SAIL_DIR=$($SAIL --dir)

if command -v pkg-config >/dev/null 2>&1 && pkg-config --exists gmp; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

"$SAIL" --no-color --no-memo-z3 -O -c --c-specialize provenance.sail -o mangled
grep -Fq 'zoption' mangled.h

"$SAIL" --no-color --no-memo-z3 -O -c --c-specialize --c-no-mangle provenance.sail -o readable

grep -Fq 'struct tuple_bits_8_bits_8' readable.h
grep -Fq 'struct option_of_B8' readable.h
grep -Eq 'uint64_t left([,);]|$)' readable.c
grep -Eq 'uint64_t right([,);]|$)' readable.c
grep -Fq 'uint64_t result_1;' readable.c
grep -Fq 'uint64_t tmp;' readable.c

if grep -Eq 'z[0-9]+zE[0-9]+|zz5(list|vec|union)' readable.c readable.h; then
  echo "opaque generated C identifiers remain under --c-no-mangle" >&2
  exit 1
fi

"$CC" ${CFLAGS:-} $GMP_CFLAGS readable.c "$SAIL_DIR"/lib/*.c \
  -I "$SAIL_DIR"/lib $GMP_LIBS -o readable.bin
./readable.bin
