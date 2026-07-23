#!/bin/sh

set -eu

cd "$(dirname "$0")"

trap 'rm -f c_repr_nat_newtype_default.c c_repr_nat_newtype_default.h c_repr_nat_newtype.c c_repr_nat_newtype.h c_repr_nat_newtype_rocq.v c_repr_nat_newtype_rocq_types.v sail_smt_cache' EXIT

SAIL=${SAIL:-sail}

# Without specialization the C backend retains the mathematical representation.
"$SAIL" --no-color --no-memo-z3 -O -c ../../c/c_repr_nat_newtype.sail -o c_repr_nat_newtype_default
grep -Fq 'struct zgas_box {sail_int zvalue;};' c_repr_nat_newtype_default.h
grep -Fq 'void zpack_gas(sail_int *rop, sail_int);' c_repr_nat_newtype_default.h

"$SAIL" --no-color --no-memo-z3 -O -c --c-specialize ../../c/c_repr_nat_newtype.sail -o c_repr_nat_newtype

# The nominal nat-backed type is native at C ABI and aggregate boundaries.
grep -Fq 'struct zgas_box {uint64_t zvalue;};' c_repr_nat_newtype.h
grep -Fq 'uint64_t zincrement(uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zadd(uint64_t, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zsubtract(uint64_t, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zmultiply(uint64_t, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zdivide(uint64_t, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zremainder(uint64_t, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zlow_byte(uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zto_limb(uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zreverse_index(uint64_t);' c_repr_nat_newtype.h
grep -Fq 'bool zoperation_is_zzero(struct zrepresented_operation);' c_repr_nat_newtype.h
grep -Fq 'bool zboxed_index_is_zzero(struct zindex_box);' c_repr_nat_newtype.h
grep -Fq 'bool zboxed_index_differs(struct zindex_box, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zvector_read(sail_fixed_bytes_4, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'sail_fixed_bytes_4 zvector_write(sail_fixed_bytes_4, uint64_t, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zpack_gas(sail_int);' c_repr_nat_newtype.h
grep -Fq 'void zunpack_gas(sail_int *rop, uint64_t);' c_repr_nat_newtype.h

# A representation annotation controls storage and ABI shape; it is not a
# proof that an unbounded nat operation fits.  Unproved arithmetic remains
# mathematical and narrows only at the explicit represented boundary.
if grep -Eq 'sail_checked_(u64|i64)_(add|sub|mul|div|mod)' c_repr_nat_newtype.c; then
  echo "generated C contains checked fixed-width arithmetic" >&2
  exit 1
fi
grep -Fq 'add_int' c_repr_nat_newtype.c
grep -Fq 'sub_int' c_repr_nat_newtype.c
grep -Fq 'mult_int' c_repr_nat_newtype.c
grep -Fq 'tdiv_int' c_repr_nat_newtype.c
grep -Fq 'tmod_int' c_repr_nat_newtype.c

# Proven bounded arithmetic, comparisons, bit extraction, and fixed-vector
# indexing stay entirely in their native representations.
for function_name in zlow_byte zto_limb zreverse_index zoperation_is_zzero zboxed_index_is_zzero zboxed_index_differs; do
  awk -v function_name="$function_name" '
    $0 ~ "^(uint64_t|bool) " function_name "\\(" { in_function = 1 }
    in_function && /sail_int/ { found_runtime = 1 }
    in_function && /^}/ { exit found_runtime }
    END { if (!in_function) exit 2 }
  ' c_repr_nat_newtype.c
done
grep -Fq '(UINT64_C(31) - zindex)' c_repr_nat_newtype.c
grep -Fq 'safe_rshift(zvalue, UINT64_C(0))' c_repr_nat_newtype.c
for function_name in zvector_read zvector_write; do
  awk -v function_name="$function_name" '
    $0 ~ function_name "\\(" { in_function = 1 }
    in_function && /sail_int/ { found_runtime = 1 }
    in_function && /^}/ { exit found_runtime }
    END { if (!in_function) exit 2 }
  ' c_repr_nat_newtype.c
done
grep -Fq 'fast_unsigned_vector_access_fixed_bytes_4(zvalues, zindex)' c_repr_nat_newtype.c
grep -Fq 'fast_unsigned_vector_update_fixed_bytes_4(' c_repr_nat_newtype.c
grep -Fq '(zleft < zright)' c_repr_nat_newtype.c
grep -Fq '(zleft == zright)' c_repr_nat_newtype.c
grep -Fq ' != zexpected);' c_repr_nat_newtype.c
# Crossings to and from an ordinary mathematical nat remain explicit and
# range-validated; this is conversion checking, not checked arithmetic.
grep -Fq 'CONVERT_OF(mach_uint, sail_int)' c_repr_nat_newtype.c
grep -Fq 'CONVERT_OF(sail_int, mach_uint)' c_repr_nat_newtype.c
grep -Fq 'UINT64_C(18446744073709551615)' c_repr_nat_newtype.c

# Rocq ignores the C-only representation choice and retains the Sail model.
"$SAIL" --no-color --no-memo-z3 --rocq -o c_repr_nat_newtype_rocq ../../c/c_repr_nat_newtype.sail
grep -Fq 'Inductive gas :=' c_repr_nat_newtype_rocq_types.v
grep -Fq '| Gas : Z -> gas.' c_repr_nat_newtype_rocq_types.v
grep -Fq 'Record gas_box := { gas_box_value : gas; }.' c_repr_nat_newtype_rocq_types.v
grep -Fq 'Definition pack_gas (value : Z) (*0 <=? value*) : gas := Gas (value).' c_repr_nat_newtype_rocq.v
grep -Fq 'Definition unpack_gas' c_repr_nat_newtype_rocq.v
grep -Fq ': Z := value.' c_repr_nat_newtype_rocq.v
