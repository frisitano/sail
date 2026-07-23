#!/bin/sh

set -eu

cd "$(dirname "$0")"

trap 'rm -f bounded_int_repr.c bounded_int_repr.h bounded_int_repr_rocq.v bounded_int_repr_rocq_types.v' EXIT

SAIL=${SAIL:-sail}
"$SAIL" --no-color -O -c ../../c/bounded_int_repr.sail -o bounded_int_repr

# Native arguments, returns, and aggregate fields retain their signedness.
grep -Fq 'uint64_t zcharge_gas(uint64_t, uint64_t);' bounded_int_repr.h
grep -Fq 'int64_t zadd_small_i64(int64_t, int64_t);' bounded_int_repr.h
grep -Fq '  uint64_t zgas_value;' bounded_int_repr.h
grep -Fq '  int64_t zsigned_value;' bounded_int_repr.h

# Explicit int and mixed-signedness boundaries use sail_int.
grep -Fq 'void zgas_to_int(sail_int *rop, uint64_t);' bounded_int_repr.h
grep -Fq 'void zmixed_add(sail_int *rop, uint64_t, int64_t);' bounded_int_repr.h
grep -Fq 'CONVERT_OF(sail_int, mach_uint)' bounded_int_repr.c
grep -Fq 'CONVERT_OF(sail_int, mach_int)' bounded_int_repr.c

# Homogeneous gas operations and the full-width literal remain native.
grep -Fq '= (!(zremaining < zcost));' bounded_int_repr.c
grep -Fq '= (zremaining - zcost);' bounded_int_repr.c
if grep -Eq 'sail_checked_(u64|i64)_(add|sub|mul|div|mod)' bounded_int_repr.c; then
  echo "generated C contains checked fixed-width arithmetic" >&2
  exit 1
fi
grep -Fq '= (zlhs < zrhs);' bounded_int_repr.c
grep -Fq 'UINT64_C(18446744073709551615)' bounded_int_repr.c

# Bounded singleton literals retain the aggregate element representation;
# constructing a schedule or literal vector must not allocate sail_int values.
for function_name in zliteral_blob_schedule zliteral_precompile_ids; do
  awk -v function_name="$function_name" '
    $0 ~ function_name "\\(" { in_function = 1 }
    in_function && /sail_int/ { found_runtime = 1 }
    in_function && /^}/ { exit found_runtime }
    END { if (!in_function) exit 2 }
  ' bounded_int_repr.c
done
grep -Fq 'zupdate_fraction = UINT64_C(11684671);' bounded_int_repr.c

# print_int is a deliberate arbitrary-precision boundary, never the signed fast path.
grep -Fq 'print_int("gas direct = "' bounded_int_repr.c
if grep -Fq 'fast_print_int("gas direct = "' bounded_int_repr.c; then
  echo 'full-width uint64_t incorrectly used the signed print fast path' >&2
  exit 1
fi

# Rocq keeps the nominal type, mathematical integer carrier, and Sail body.
"$SAIL" --no-color --rocq -o bounded_int_repr_rocq ../../c/bounded_int_repr.sail
grep -Fq 'Inductive gas :=' bounded_int_repr_rocq_types.v
grep -Fq '| Gas : Z -> gas.' bounded_int_repr_rocq_types.v
grep -Fq 'Definition c_gas_identity (value : gas) : gas := value.' bounded_int_repr_rocq.v
grep -Fq 'Definition gas_to_int' bounded_int_repr_rocq.v
grep -Fq ': Z := value.' bounded_int_repr_rocq.v
grep -Fq 'Z.sub (remaining) (cost)' bounded_int_repr_rocq.v
