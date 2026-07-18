#!/bin/sh

set -eu

cd "$(dirname "$0")"

trap 'rm -f default.c default.h specialized.c specialized.h sail_smt_cache' EXIT

SAIL=${SAIL:-sail}
SOURCE=../../c/c_repr_containers.sail

"$SAIL" --no-color --no-memo-z3 -O -c "$SOURCE" -o default
grep -Fq '// union option<i>' default.h
grep -Fq 'sail_int zdirect;' default.h
grep -Fq 'struct { sail_int zGas; };' default.h

"$SAIL" --no-color --no-memo-z3 -O -c --c-specialize "$SOURCE" -o specialized
grep -Fq '// union option<U64>' specialized.h
grep -Fq 'uint64_t zdirect;' specialized.h
grep -Fq 'struct { uint64_t zGas; };' specialized.h
grep -Fq 'struct { uint64_t zSomezIU64zK; };' specialized.h
grep -Fq 'CONVERT_OF(mach_uint, sail_int)' specialized.c
if grep -Fq 'CONVERT_OF(zoptionzIU64zK, zoptionzIizK)' specialized.c; then
  echo "generic option conversion was not lowered field-by-field" >&2
  exit 1
fi
