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
grep -Fq 'uint64_t zvector_read(zz5vecz8z5bv8z9, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'void zvector_write(zz5vecz8z5bv8z9 *rop, zz5vecz8z5bv8z9, uint64_t, uint64_t);' c_repr_nat_newtype.h
grep -Fq 'uint64_t zpack_gas(sail_int);' c_repr_nat_newtype.h
grep -Fq 'void zunpack_gas(sail_int *rop, uint64_t);' c_repr_nat_newtype.h

# Operators on represented payloads lower directly to native C.
grep -Fq 'sail_checked_u64_add(zvalue, UINT64_C(1))' c_repr_nat_newtype.c
grep -Fq 'sail_checked_u64_add(zleft, zright)' c_repr_nat_newtype.c
grep -Fq 'sail_checked_u64_sub(zleft, zright)' c_repr_nat_newtype.c
grep -Fq 'sail_checked_u64_mul(zleft, zright)' c_repr_nat_newtype.c
grep -Fq 'sail_checked_u64_div(zleft, zright)' c_repr_nat_newtype.c
grep -Fq 'sail_checked_u64_mod(zleft, zright)' c_repr_nat_newtype.c

# Native payload arithmetic must not detour through sail_int before being
# wrapped back into the annotated newtype.
for function_name in zincrement zadd zsubtract zmultiply zdivide zremainder zlow_byte zto_limb zreverse_index zoperation_is_zzero zboxed_index_is_zzero zboxed_index_differs; do
  awk -v function_name="$function_name" '
    $0 ~ "^(uint64_t|bool) " function_name "\\(" { in_function = 1 }
    in_function && /sail_int/ { found_runtime = 1 }
    in_function && /^}/ { exit found_runtime }
    END { if (!in_function) exit 2 }
  ' c_repr_nat_newtype.c
done
grep -Fq 'sail_checked_u64_sub(UINT64_C(31), zindex)' c_repr_nat_newtype.c
grep -Fq 'safe_rshift(zvalue, UINT64_C(0))' c_repr_nat_newtype.c
for function_name in zvector_read zvector_write; do
  awk -v function_name="$function_name" '
    $0 ~ function_name "\\(" { in_function = 1 }
    in_function && /sail_int/ { found_runtime = 1 }
    in_function && /^}/ { exit found_runtime }
    END { if (!in_function) exit 2 }
  ' c_repr_nat_newtype.c
done
grep -Fq 'fast_unsigned_vector_access_zz5vecz8z5bv8z9(zvalues, zindex)' c_repr_nat_newtype.c
grep -Fq 'fast_unsigned_vector_update_zz5vecz8z5bv8z9(' c_repr_nat_newtype.c
grep -Fq '(zleft < zright)' c_repr_nat_newtype.c
grep -Fq '(zleft == zright)' c_repr_nat_newtype.c
grep -Fq ' != zexpected);' c_repr_nat_newtype.c
if grep -Eq '(add_int|sub_int|mult_int|tdiv_int|tmod_int)\(' c_repr_nat_newtype.c; then
  echo "represented nat operators unexpectedly used the mathematical integer runtime" >&2
  exit 1
fi

# Crossings to and from an ordinary mathematical nat remain explicit and checked.
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
