#!/bin/sh

set -eu

cd "$(dirname "$0")"

trap 'rm -f unspliced.c unspliced.h spliced.c spliced.h spliced_rocq.v spliced_rocq_types.v sail_smt_cache' EXIT

SAIL=${SAIL:-sail}

# The source newtype uses the mathematical nat representation without a splice.
"$SAIL" --no-color -O -c base.sail -o unspliced
grep -Fq 'struct zgas_box {sail_int zvalue;};' unspliced.h
grep -Fq 'void zpack_gas(sail_int *rop, sail_int);' unspliced.h

# Replacing the newtype in place preserves its splice-file c_repr attribute.
"$SAIL" --no-color -O -c --c-specialize --splice replacement.sail base.sail -o spliced
grep -Fq 'struct zgas_box {uint64_t zvalue;};' spliced.h
grep -Fq 'uint64_t zpack_gas(sail_int);' spliced.h
grep -Fq 'void zunpack_gas(sail_int *rop, uint64_t);' spliced.h
grep -Fq 'CONVERT_OF(mach_uint, sail_int)' spliced.c
grep -Fq 'CONVERT_OF(sail_int, mach_uint)' spliced.c

# c_repr remains C-only; other backends see the nominal Sail newtype.
"$SAIL" --no-color --rocq --splice replacement.sail -o spliced_rocq base.sail
grep -Fq 'Inductive gas :=' spliced_rocq_types.v
grep -Fq '| Gas : Z -> gas.' spliced_rocq_types.v
grep -Fq 'Record gas_box := { gas_box_value : gas; }.' spliced_rocq_types.v
