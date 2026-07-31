#!/bin/sh

set -eu

cd "$(dirname "$0")"

trap 'rm -f mangled.c mangled.h historical.c historical.h historical.bin sail_smt_cache' EXIT

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

"$SAIL" --no-color --no-memo-z3 -O -c --c-specialize names.sail -o mangled
grep -Fq 'zoption' mangled.h

"$SAIL" --no-color --no-memo-z3 -O -c --c-specialize --c-no-mangle names.sail -o historical

# --c-no-mangle preserves valid source identifiers.
grep -Fq 'uint64_t add_pair(struct ztuple_z8z5bv8zCz0z5bv8z9);' historical.h
grep -Fq 'uint64_t increment_twice(uint64_t);' historical.h
grep -Fq 'uint64_t left;' historical.c
grep -Fq 'uint64_t right;' historical.c
grep -Fq 'uint64_t tmp;' historical.c

# Structural types, monomorphized functions, and compiler-generated locals
# keep their historical zencoded spelling rather than source-provenance names.
grep -Fq 'struct ztuple_z8z5bv8zCz0z5bv8z9 {' historical.h
grep -Fq 'void zkeep_ifzIB8zK(struct zoptionzIB8zK *rop, bool, uint64_t);' historical.h
grep -Eq 'uint64_t z[0-9]+zE[0-9]+;' historical.c

# C-keyword fallback and the resulting collision use the established suffixing
# behavior: `restrict` becomes `zrestrict`, then source `zrestrict` gets `1`.
grep -Fq 'uint64_t zrestrict(uint64_t);' historical.h
grep -Fq 'uint64_t zrestrict1(uint64_t);' historical.h

"$CC" ${CFLAGS:-} $GMP_CFLAGS historical.c "$SAIL_DIR"/lib/*.c \
  -I "$SAIL_DIR"/lib $GMP_LIBS -o historical.bin
./historical.bin
