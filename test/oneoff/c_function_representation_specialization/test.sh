#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_function_representation_specialization.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize --c-no-main \
  --c-preserve add_reward \
  --c-preserve add_full \
  --c-preserve exact_add_full \
  --c-preserve non_power_of_two_addmod \
  --c-preserve wrapping_sub_full \
  --c-preserve wrapping_sub_u64 \
  --c-preserve wrapping_sub_u8 \
  --c-preserve non_power_of_two_submod \
  --c-preserve truncating_submod \
  --c-preserve wrapping_truncating_sub_ordered \
  --c-preserve ordered_non_power_of_two_submod \
  --c-preserve wrapping_add_u128 \
  --c-preserve wrapping_mul_u128_result \
  --c-preserve wrapping_mul_u64 \
  --c-preserve wrapping_mul_u64_reverse \
  --c-preserve wrapping_mul_u128 \
  --c-preserve wrapping_mul_u128_reverse \
  --c-preserve wrapping_mul_full \
  --c-preserve exact_mul_u64 \
  --c-preserve non_power_of_two_mulmod \
  --c-preserve shared_product_mulmod \
  --c-preserve interleaved_mulmod \
  --c-preserve full_addmod \
  --c-preserve full_mulmod \
  --c-preserve narrow_after_guard \
  --c-preserve word_words_for_bytes \
  --c-preserve native_words_for_bytes \
  --c-preserve full_u64_words_for_bytes \
  --c-preserve unbounded_dependent_add \
  --c-preserve bounded_dependent_tiny_add \
  --c-preserve bounded_dependent_tiny_sub \
  --c-preserve bounded_dependent_tiny_mul \
  --c-preserve smaller_tiny_square_le \
  --c-preserve tiny_square_le \
  --c-preserve medium_square_le \
  --c-preserve tiny_forwarded_square_le \
  --c-preserve medium_forwarded_square_le \
  --c-preserve tiny_caller_bounded_wrapping_mul \
  --c-preserve wide_caller_bounded_wrapping_mul \
  --c-preserve unbounded_dependent_mul \
  --c-preserve guarded_u64_tiny_square \
  --c-preserve else_guarded_u64_tiny_square \
  --c-preserve is_tiny_u64 \
  --c-preserve forwarded_is_tiny_u64 \
  --c-preserve predicate_sensitive_square_le \
  --c-preserve helper_guarded_u64_tiny_square \
  --c-preserve is_not_tiny_u64 \
  --c-preserve negated_helper_guarded_square \
  --c-preserve recursive_is_tiny_u64 \
  --c-preserve recursive_predicate_guarded_square \
  --c-preserve unsound_mixed_predicate \
  --c-preserve unsound_predicate_guarded_square \
  --c-preserve comparison_fold_true \
  --c-preserve comparison_fold_false \
  --c-preserve comparison_fold_forwarded \
  --c-preserve comparison_fold_unknown \
  --c-preserve comparison_fold_after_mutation \
  --c-preserve path_proven_shift_left \
  --c-preserve path_proven_shift_right \
  --c-preserve path_proven_arith_shift_right \
  --c-preserve predicate_proven_shift_left \
  --c-preserve unknown_shift_left \
  --c-preserve invalidated_shift_left \
  --c-preserve path_proven_slice \
  --c-preserve predicate_proven_slice \
  --c-preserve unknown_slice \
  --c-preserve invalidated_u64_square \
  --c-preserve bounded_integer_box_value \
  --c-preserve mutable_unbounded_accumulator \
  --c-preserve bounded_guarded_loop \
  --c-preserve unbounded_guarded_loop \
  --c-preserve signed_state_gas_lifecycle \
  --c-preserve bounded_throw_if_zero \
  --c-preserve bounded_guarded_ediv \
  --c-preserve bounded_recursive_once \
  --c-preserve bounded_recursive_countdown \
  --c-preserve aggregate_local_length \
  --c-preserve aggregate_constructor_fact \
  --c-preserve invalidated_aggregate_constructor_fact \
  --c-preserve bounded_callee_result \
  --c-preserve recursive_bounded_callee \
  --c-preserve consume_bounded_callee_result \
  --c-preserve consume_recursive_bounded_callee \
  --c-preserve unbounded_callee_result \
  --c-preserve consume_unbounded_callee_result \
  --c-preserve aggregate_encoded_length \
  --c-preserve bounded_guarded_comparison \
  "$TEST_DIR/model.sail" -o "$TMP_DIR/model"

# Immutable top-level initializers use their complete proven lifetime.  The
# 256-bit literal temporary must therefore share the destination's native u256
# representation rather than leaving a one-use arbitrary-precision integer.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize \
  --c-require-bounded-int --c-no-main \
  "$TEST_DIR/top_level_bound.sail" -o "$TMP_DIR/top_level_bound"
grep -Fq 'sail_u256 zWORD_ALL_ONES;' "$TMP_DIR/top_level_bound.c"
grep -Fq '((sail_u256){{UINT64_C(18446744073709551615), UINT64_C(18446744073709551615), UINT64_C(18446744073709551615), UINT64_C(18446744073709551615)}})' "$TMP_DIR/top_level_bound.c"
if grep -Fq 'convert_u256_of_sail_string' "$TMP_DIR/top_level_bound.c"; then
  echo 'fixed-width u256 literal was materialized through a runtime decimal parser' >&2
  exit 1
fi

# A concrete source signature keeps its canonical ABI, while a narrower
# proof at a call site seeds a representation clone.  The caller must select
# that clone directly instead of widening the bounded argument first.
"$SAIL" "$@" --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve concrete_add \
  --c-preserve concrete_specialization \
  "$TEST_DIR/concrete_signature.sail" -o "$TMP_DIR/concrete_signature"
grep -Fq 'sail_u256 zconcrete_add(sail_u256, sail_u256);' "$TMP_DIR/concrete_signature.h"
grep -Eq 'sail_u256 zconcrete_add.*repr.*\(sail_u256, uint8_t\);' "$TMP_DIR/concrete_signature.h"
awk '
  /^sail_u256 zconcrete_special.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/concrete_signature.c" > "$TMP_DIR/concrete_specialization.c"
grep -Eq 'zconcrete_add.*repr.*\(' "$TMP_DIR/concrete_specialization.c"
if grep -Fq 'u256_of_mach_int(' "$TMP_DIR/concrete_specialization.c"; then
  echo 'concrete representation specialization widened its bounded argument' >&2
  exit 1
fi

# The per-function clone budget is a correctness boundary, not permission to
# merge distinct proof outcomes.  This model needs separate u8- and u16-body
# clones with the same uint8_t ABI, so a limit of one must reject extraction.
if "$SAIL" "$@" --no-color --no-memo-z3 -O -c --c-specialize \
  --c-specialization-limit 1 --c-no-main \
  --c-preserve tiny_budgeted_square \
  --c-preserve medium_budgeted_square \
  "$TEST_DIR/specialization_limit.sail" -o "$TMP_DIR/specialization_limit" \
  >"$TMP_DIR/specialization_limit.log" 2>&1
then
  echo 'specialization budget silently weakened a caller proof' >&2
  exit 1
fi
grep -Fq 'Function budgeted_square requires more than 1 C representation specializations' \
  "$TMP_DIR/specialization_limit.log"

# A path-refined mathematical integer can call a fixed-width helper without
# asking bounds specialization to clone the already-lowered helper body with
# the wider caller representation.  The precise-call pass inserts the proved
# conversion at the edge while the native Slice remains over uint8_t.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize --c-no-main \
  --c-preserve from_wide \
  "$TEST_DIR/bounds_only_widening.sail" -o "$TMP_DIR/bounds_only_widening"
grep -Fq 'uint64_t zlowered_byte(uint8_t);' "$TMP_DIR/bounds_only_widening.h"
grep -Fq 'CONVERT_OF(mach_uint, sail_int)(zvalue)' "$TMP_DIR/bounds_only_widening.c"
if grep -Eq 'zlowered_byte.*repr' "$TMP_DIR/bounds_only_widening.h"; then
  echo 'bounds-only specialization cloned a fixed-width helper with a wider representation' >&2
  exit 1
fi

# Fixed-vector helpers use the same return convention as their call sites.
# In the standard backend a fixed vector is managed even when its elements are
# copyable, so internal construction must retain the output-parameter ABI.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize --c-no-main \
  --c-preserve zero_bytes32 \
  "$TEST_DIR/standard_fixed_vector.sail" -o "$TMP_DIR/standard_fixed_vector"
grep -Eq 'static void internal_vector_init_.*\([^,]+ \*rop, const int64_t len\)' \
  "$TMP_DIR/standard_fixed_vector.c"
grep -Eq 'internal_vector_init_.*\(&[^,]+, INT64_C\(32\)\);' \
  "$TMP_DIR/standard_fixed_vector.c"
GMP_CFLAGS=$(${PKG_CONFIG:-pkg-config} --cflags gmp)
"${CC:-cc}" ${CFLAGS:-} $GMP_CFLAGS -std=c11 -Wall -Werror=implicit-function-declaration \
  -I "$TEST_DIR/../../../lib" -c "$TMP_DIR/standard_fixed_vector.c" \
  -o "$TMP_DIR/standard_fixed_vector.o"

# A recursive clone may reuse itself only when the recursive call remains
# inside the bounds which justified that clone's pruned branches.  Starting at
# 1..8 removes the zero branch, but the recursive edge reaches 0..7 and must
# therefore target a second clone which retains the base case.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize --c-no-main \
  --c-preserve descending_to_zero \
  --c-preserve positive_countdown \
  --c-preserve ascending_to_eight \
  --c-preserve low_countup \
  "$TEST_DIR/recursive_bound_partition.sail" -o "$TMP_DIR/recursive_bound_partition"
test "$(grep -Ec 'unit zdescending_to_zzero.*repr.*\(uint8_t\);' \
  "$TMP_DIR/recursive_bound_partition.h")" -eq 2
test "$(grep -Ec 'unit zascending_to_eight.*repr.*\(uint8_t\);' \
  "$TMP_DIR/recursive_bound_partition.h")" -eq 2

# A terminating zero guard is part of the source proof context.  Preserve it
# across ANF/JIB lowering so non-negative Euclidean division can use the native
# quotient operation without materialising sail_int operands.
awk '
  /^uint64_t zbounded_guarded_ediv\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/bounded_guarded_ediv.c"
# Mixed-width operands may be promoted into a fixed native temporary after
# final call-graph representation propagation.  What matters is that the body
# still contains native C division rather than an arbitrary-integer helper.
grep -Fq ' / ' "$TMP_DIR/bounded_guarded_ediv.c"
if grep -Eq 'ediv_int|sail_int' "$TMP_DIR/bounded_guarded_ediv.c"; then
  echo 'guarded bounded Euclidean division retained arbitrary-precision arithmetic' >&2
  exit 1
fi

# Once every reachable call has been redirected to a proved representation
# clone, the generic mathematical-integer implementation is dead and must not
# remain in optimized C.  Keeping it would reintroduce sail_int/GMP even though
# no execution path can call it.
for function_name in top_add middle_add; do
  if grep -Fq "sail_u256 z${function_name}(sail_u256, sail_u256);" "$TMP_DIR/model.h"; then
    echo "unreachable generic implementation ${function_name} was retained" >&2
    exit 1
  fi
done

# A full-width caller keeps the canonical u256/u256 body alive. Its explicit
# modulo-2^256 observation is one wrapping operation, so no exact u320
# intermediate is needed.
grep -Fq 'sail_u256 zleaf_add(sail_u256, sail_u256);' "$TMP_DIR/model.h"
awk '
  /^sail_u256 zleaf_add\(sail_u256 zleft, sail_u256 zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/full_width_leaf_add.c"
grep -Fq 'u256_add(zleft, zright)' "$TMP_DIR/full_width_leaf_add.c"
if grep -Eq 'u320_add_widen|u320_mod|sail_int' "$TMP_DIR/full_width_leaf_add.c"; then
  echo 'proved full-width wrapping addition retained an exact wide intermediate' >&2
  exit 1
fi

# Without a modulo-2^256 observation, or with a different modulus, addition
# remains exact and must not inherit wrapping semantics from its destination.
awk '
  /^sail_u320 zexact_add_full\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/exact_addition.c"
grep -Fq 'u320_add_widen(zleft, zright)' "$TMP_DIR/exact_addition.c"
if grep -Fq 'u256_add(zleft, zright)' "$TMP_DIR/exact_addition.c"; then
  echo 'exact full-width addition was incorrectly made wrapping' >&2
  exit 1
fi

awk '
  /^sail_u256 znon_power_of_two_addmod\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/non_power_of_two_addition.c"
grep -Fq 'u320_add_widen(zleft, zright)' "$TMP_DIR/non_power_of_two_addition.c"
grep -Fq 'u320_mod(' "$TMP_DIR/non_power_of_two_addition.c"
if grep -Fq 'u256_add(zleft, zright)' "$TMP_DIR/non_power_of_two_addition.c"; then
  echo 'non-power-of-two reduction was incorrectly made wrapping addition' >&2
  exit 1
fi

# The same semantic evidence projects onto the fixed u128 carrier and selects
# its mixed-width wrapping helpers; it is not specific to the u256 EVM case.
awk '
  /^sail_u128 zwrapping_(add|mul)_u128/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/u128_wrapping_arithmetic.c"
grep -Fq 'u128_add_u64(zleft, zright)' "$TMP_DIR/u128_wrapping_arithmetic.c"
grep -Fq 'u128_mul_u64(zleft, zright)' "$TMP_DIR/u128_wrapping_arithmetic.c"
if grep -Eq 'u256_(add|mul)|u256_mod|sail_int' "$TMP_DIR/u128_wrapping_arithmetic.c"; then
  echo 'proved u128 wrapping arithmetic retained an exact wider intermediate' >&2
  exit 1
fi

# Euclidean remainder makes subtraction modulo 2^N a low-bit observation even
# when the mathematical difference is negative.  Truncating remainder does
# not have that property and must retain its exact signed intermediate.
awk '
  /^sail_u256 zwrapping_sub_(full|u64)\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/wrapping_subtractions.c"
grep -Fq 'u256_sub(zleft, zright)' "$TMP_DIR/wrapping_subtractions.c"
grep -Fq 'u256_sub_u64(zleft, zright)' "$TMP_DIR/wrapping_subtractions.c"
if grep -Eq 'emod_int|sail_int' "$TMP_DIR/wrapping_subtractions.c"; then
  echo 'proved wrapping subtraction retained Euclidean remainder machinery' >&2
  exit 1
fi

awk '
  /^uint8_t zwrapping_sub_u8\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/wrapping_subtraction_u8.c"
grep -Fq '((uint8_t)(((uint32_t)zleft) - ((uint32_t)zright)))' "$TMP_DIR/wrapping_subtraction_u8.c"
if grep -Eq 'emod_int|sail_int' "$TMP_DIR/wrapping_subtraction_u8.c"; then
  echo 'proved u8 wrapping subtraction retained arbitrary-precision arithmetic' >&2
  exit 1
fi

awk '
  /^sail_u256 znon_power_of_two_submod\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/non_power_of_two_subtraction.c"
grep -Fq 'emod_int(' "$TMP_DIR/non_power_of_two_subtraction.c"
if grep -Fq 'u256_sub_u64(zleft, zright)' "$TMP_DIR/non_power_of_two_subtraction.c"; then
  echo 'non-power-of-two subtraction reduction was incorrectly made wrapping' >&2
  exit 1
fi

awk '
  /^void ztruncating_submod\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/truncating_subtraction.c"
grep -Fq 'sub_int(' "$TMP_DIR/truncating_subtraction.c"
grep -Fq 'tmod_int(' "$TMP_DIR/truncating_subtraction.c"
if grep -Fq 'u256_sub_u64(zleft, zright)' "$TMP_DIR/truncating_subtraction.c"; then
  echo 'truncating subtraction reduction was incorrectly treated as low bits' >&2
  exit 1
fi

# Truncating remainder does observe low bits when the source constraints prove
# the subtraction non-negative.  The interval projection alone cannot recover
# the relation between two full-width operands; the callsite proof certificate
# is established while the symbolic Sail environment is still available.
awk '
  /^sail_u256 zordered_truncating_submod\(sail_u256 zleft, sail_u256 zright\)/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/ordered_truncating_subtraction.c"
grep -Fq 'u256_sub(zleft, zright)' "$TMP_DIR/ordered_truncating_subtraction.c"
if grep -Eq 'tmod_int|sub_int|sail_int' "$TMP_DIR/ordered_truncating_subtraction.c"; then
  echo 'symbolically proved non-negative truncating subtraction retained exact arithmetic' >&2
  exit 1
fi

# The non-negativity proof only changes the interpretation of truncating
# remainder.  It does not make an arbitrary modulus a low-bit observation.
# The rejected web must still consume the proof-carrying subtraction marker as
# native exact arithmetic instead of leaking an arbitrary-precision sub_int.
# Its native u256 remainder remains explicit because this modulus is not a
# low-bit mask.
awk '
  /^sail_u256 zordered_non_power_of_two_submod\(sail_u256 zleft, sail_u256 zright\)/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/ordered_non_power_of_two_subtraction.c"
grep -Fq 'u256_sub(zleft, zright)' "$TMP_DIR/ordered_non_power_of_two_subtraction.c"
grep -Fq 'u256_mod(' "$TMP_DIR/ordered_non_power_of_two_subtraction.c"
if grep -Fq 'sub_int(zleft, zright)' "$TMP_DIR/ordered_non_power_of_two_subtraction.c"; then
  echo 'rejected proof-bearing subtraction leaked an arbitrary-precision marker fallback' >&2
  exit 1
fi

# Exact generic ADDMOD/MULMOD equations remain the sole Sail source, while
# their all-u256 representation clones call overflow-safe native reducers.
grep -Fq 'u256_addmod(zleft, zright, zmodulus)' "$TMP_DIR/model.c"
grep -Fq 'u256_mulmod(zleft, zright, zmodulus)' "$TMP_DIR/model.c"
if grep -Eq '__sail_u256_(addmod|mulmod)' "$TMP_DIR/model.c"; then
  echo 'representation-specialized modular arithmetic extern was not lowered' >&2
  exit 1
fi

# The demanded variants carry uint64_t through every local call boundary.
grep -Eq 'sail_u256 ztop_add.*repr.*\(sail_u256, uint64_t\);' "$TMP_DIR/model.h"
grep -Eq 'sail_u256 zmiddle_add.*repr.*\(sail_u256, uint64_t\);' "$TMP_DIR/model.h"
grep -Eq 'sail_u256 zleaf_add.*repr.*\(sail_u256, uint64_t\);' "$TMP_DIR/model.h"

# Widening happens at the arithmetic operation, not at an intermediate call.
grep -Fq 'u256_add_u64(' "$TMP_DIR/model.c"
awk '
  /^sail_u256 z(top_add|middle_add|leaf_add).*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_functions.c"
if grep -Eq 'u256_of_fbits\(zright\)|u256_of_u64\(zright\)' "$TMP_DIR/specialized_functions.c"; then
  echo 'specialized local-call chain widened its uint64_t argument early' >&2
  exit 1
fi

# The source-level multiply and truncating modulo form one semantic wrapping
# operation. Its u256/u64 representation clone must select the mixed-width
# wrapping helper directly, including when the source operands are reversed.
awk '
  /^sail_u256 zleaf_mul.*repr.*\(sail_u256 zleft, uint64_t zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_wrapping_multiplications.c"
test "$(grep -Fc 'u256_mul_u64(zleft, zright)' "$TMP_DIR/specialized_wrapping_multiplications.c")" -eq 2
if grep -Eq 'u320_mul|u320_mod|sail_int' "$TMP_DIR/specialized_wrapping_multiplications.c"; then
  echo 'proved mixed-width wrapping multiplication retained an exact wide intermediate' >&2
  exit 1
fi

awk '
  /^sail_u256 zleaf_mul.*repr.*\(sail_u256 zleft, sail_u128 zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_u256_u128_wrapping_multiplications.c"
test "$(grep -Fc 'u256_mul_u128(zleft, zright)' "$TMP_DIR/specialized_u256_u128_wrapping_multiplications.c")" -eq 2
if grep -Eq 'u320_mul|u320_mod|sail_int' "$TMP_DIR/specialized_u256_u128_wrapping_multiplications.c"; then
  echo 'proved u256/u128 wrapping multiplication retained an exact wide intermediate' >&2
  exit 1
fi

awk '
  /^sail_u256 zleaf_mul\(sail_u256 zleft, sail_u256 zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/full_width_wrapping_multiplication.c"
grep -Fq 'u256_mul(zleft, zright)' "$TMP_DIR/full_width_wrapping_multiplication.c"
if grep -Eq 'u320_mul|u320_mod|sail_int' "$TMP_DIR/full_width_wrapping_multiplication.c"; then
  echo 'proved full-width wrapping multiplication retained an exact wide intermediate' >&2
  exit 1
fi

# Without the explicit modulo-2^256 semantic web, multiplication must remain
# exact. A different modulus likewise may not inherit wrapping semantics merely
# because its result is eventually stored in a u256.
awk '
  /^sail_u320 zexact_mul_u64\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/exact_multiplication.c"
grep -Fq 'u320_mul_widen(zleft, zright)' "$TMP_DIR/exact_multiplication.c"
if grep -Fq 'u256_mul_u64(' "$TMP_DIR/exact_multiplication.c"; then
  echo 'exact mixed-width multiplication was incorrectly made wrapping' >&2
  exit 1
fi

awk '
  /^sail_u256 znon_power_of_two_mulmod\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/non_power_of_two_multiplication.c"
grep -Fq 'u320_mul_widen(zleft, zright)' "$TMP_DIR/non_power_of_two_multiplication.c"
grep -Fq 'u320_mod(' "$TMP_DIR/non_power_of_two_multiplication.c"
if grep -Fq 'u256_mul_u64(' "$TMP_DIR/non_power_of_two_multiplication.c"; then
  echo 'non-power-of-two reduction was incorrectly made wrapping' >&2
  exit 1
fi

awk '
  /^sail_u256 zshared_product_mulmod\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/shared_product_multiplication.c"
grep -Fq 'u320_mul_widen(zleft, zright)' "$TMP_DIR/shared_product_multiplication.c"
grep -Fq 'u320_mod(' "$TMP_DIR/shared_product_multiplication.c"
if grep -Fq 'u256_mul_u64(' "$TMP_DIR/shared_product_multiplication.c"; then
  echo 'multiplication with another exact-product use was incorrectly made wrapping' >&2
  exit 1
fi

# Web discovery follows the product's def-use chain rather than requiring the
# arithmetic and reduction to occupy a fixed adjacent instruction window.  An
# independent side effect may remain scheduled between those nodes.
awk '
  /^sail_u256 zinterleaved_mulmod\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/interleaved_multiplication.c"
grep -Fq 'u256_mul_u64(zleft, zright)' "$TMP_DIR/interleaved_multiplication.c"
if grep -Eq 'u320_mul|u320_mod|sail_int' "$TMP_DIR/interleaved_multiplication.c"; then
  echo 'dependency-connected wrapping multiplication retained an exact wide intermediate' >&2
  exit 1
fi


# The opposite direction remains a separate, proof-backed narrowing path: the
# guarded word is stored as u256, but its typed occurrence is word_bit_count.
grep -Fq 'u256_extract_u64(' "$TMP_DIR/model.c"

# A single unbounded semantic helper is cloned at the fixed representation
# and exact interval demanded by each bounded caller. The word clone may need
# arbitrary precision because word_max + 31 is 257 bits. The bounded native
# clones use the smallest proved carrier: u8 for 0..255 and u64 for full u64.
grep -Eq 'sail_u256 zwords_for_bytes.*repr.*\(sail_u256\);' "$TMP_DIR/model.h"
test "$(grep -Ec 'uint64_t zwords_for_bytes.*repr.*\(uint64_t\);' "$TMP_DIR/model.h")" -eq 1
test "$(grep -Ec 'uint8_t zwords_for_bytes.*repr.*\(uint8_t\);' "$TMP_DIR/model.h")" -eq 1
awk '
  /^uint(8|64)_t zwords_for_bytes.*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_integer_helpers.c"
if grep -Fq 'sail_int' "$TMP_DIR/specialized_integer_helpers.c"; then
  echo 'specialized bounded-integer helper fell back to sail_int' >&2
  exit 1
fi
grep -Fq 'u128_add_u64(' "$TMP_DIR/specialized_integer_helpers.c"

# Caller semantic intervals participate in body specialization independently
# of the function ABI. Both wrappers pass uint8_t and return bool, but the
# 0..8 caller proves an 8-bit square while the 0..200 caller needs a 16-bit
# exact product. They must therefore demand distinct clones and body carriers.
test "$(grep -Ec '^bool zcaller_sensitive_square_le.*\(uint8_t\);' "$TMP_DIR/model.h")" -eq 2
awk '
  /^bool zcaller_sensitive_square_le.*\(uint8_t zvalue\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/caller_sensitive_square_le.c"
test "$(grep -Fc '((uint8_t)(((uint32_t)zvalue) * ((uint32_t)zvalue)))' "$TMP_DIR/caller_sensitive_square_le.c")" -eq 1
test "$(grep -Fc '((uint16_t)(((uint32_t)' "$TMP_DIR/caller_sensitive_square_le.c")" -eq 1
if grep -Eq 'sail_int|mult_int' "$TMP_DIR/caller_sensitive_square_le.c"; then
  echo 'caller-sensitive body specialization fell back to arbitrary precision' >&2
  exit 1
fi

# Bounds [0, 7] and [0, 8] choose the same complete lowering outcome for the
# leaf body, so they share one representation clone.  Equivalent proof
# partitions must not create duplicate C functions.
awk '
  /^bool z(smaller_tiny|tiny)_square_le\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/equivalent_tiny_square_callers.c"
test "$(grep -Eo 'zcaller_sensitive_square_le[^ (]*repr[^ (]*' \
  "$TMP_DIR/equivalent_tiny_square_callers.c" | sort -u | wc -l | tr -d ' ')" -eq 1

# A forwarding body can have identical local carriers while its argument
# proof selects a materially different callee specialization.  Outgoing call
# edges therefore participate in the body fingerprint: the tight caller uses
# a forwarding clone and reaches the tight square clone, while the broad
# caller remains on the canonical forwarding/callee path.
grep -Eq 'bool zforward_caller_sensitive_square_le.*repr.*\(uint8_t\);' "$TMP_DIR/model.h"
awk '
  /^bool ztiny_forwarded_square_le\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/tiny_forwarded_square_le.c"
grep -Eq 'zforward_caller_sensitive_square_le.*repr.*\(' "$TMP_DIR/tiny_forwarded_square_le.c"
awk '
  /^bool zforward_caller_sensitive_square_le.*repr.*\(uint8_t zvalue\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/tight_forwarding_clone.c"
grep -Eq 'zcaller_sensitive_square_le.*repr.*\(' "$TMP_DIR/tight_forwarding_clone.c"
awk '
  /^bool zmedium_forwarded_square_le\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/medium_forwarded_square_le.c"
grep -Eq 'zforward_caller_sensitive_square_le\(zvalue\)' "$TMP_DIR/medium_forwarded_square_le.c"
if grep -Eq 'zforward_caller_sensitive_square_le.*repr.*\(' "$TMP_DIR/medium_forwarded_square_le.c"; then
  echo 'broad forwarding caller was routed through the strict specialization' >&2
  exit 1
fi

# Web discovery retains a provisional modulo-2^N candidate when the generic
# callee proves non-negativity but has no source upper bound. The tiny caller's
# propagated ranges discharge the deferred operand-fit obligation in the clone,
# allowing the same body-specialization pipeline to select wrapping uint8_t
# multiplication without an exact sail_int product or remainder.
grep -Eq 'uint8_t zcaller_bounded_wrapping_mul.*repr.*\(uint8_t, uint8_t\);' "$TMP_DIR/model.h"
awk '
  /^uint8_t zcaller_bounded_wrapping_mul.*repr.*\(uint8_t zleft, uint8_t zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/caller_bounded_wrapping_mul.c"
grep -Fq '((uint8_t)(((uint32_t)zleft) * ((uint32_t)zright)))' "$TMP_DIR/caller_bounded_wrapping_mul.c"
if grep -Eq 'sail_int|mult_int|tmod_int' "$TMP_DIR/caller_bounded_wrapping_mul.c"; then
  echo 'caller-proved wrapping web retained exact arbitrary-precision arithmetic' >&2
  exit 1
fi

# A wider caller reaches the same provisional web but does not satisfy its
# operand-fit obligation. It must keep the exact product and reduction rather
# than selecting byte-width wrapping multiplication from non-negativity alone.
grep -Eq 'uint8_t zcaller_bounded_wrapping_mul.*repr.*\(uint16_t, uint16_t\);' "$TMP_DIR/model.h"
awk '
  /^uint8_t zcaller_bounded_wrapping_mul.*repr.*\(uint16_t zleft, uint16_t zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/wide_caller_bounded_wrapping_mul.c"
if grep -Fq '((uint8_t)(((uint32_t)zleft) * ((uint32_t)zright)))' "$TMP_DIR/wide_caller_bounded_wrapping_mul.c"; then
  echo 'underproved wrapping web was selected for operands wider than the modulus' >&2
  exit 1
fi
if grep -Eq 'sail_int|mult_int' "$TMP_DIR/wide_caller_bounded_wrapping_mul.c"; then
  echo 'rejected wrapping web lost the caller-proved exact native product' >&2
  exit 1
fi

# Every SSA-numbered return variable must use the clone's declared result
# representation. Here the arguments remain u64 while the caller deliberately
# demands an unbounded result; native operand types must not leak into the
# sail_int return pointer.
grep -Fq '(sail_int *rop, uint64_t, uint64_t);' "$TMP_DIR/model.h"
awk '
  /^void zdependent_add.*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_unbounded_result.c"
grep -Fq 'add_int(' "$TMP_DIR/specialized_unbounded_result.c"
if grep -Eq '\(\*\([^)]*\)\) = (u128_|\([^;]+ \+ [^;]+\))' "$TMP_DIR/specialized_unbounded_result.c"; then
  echo 'specialized clone wrote native arithmetic directly into a sail_int result' >&2
  exit 1
fi

# Symbolic atom bounds remain available at the arithmetic operation.  The
# complete operand/result lifetime is 0..64 at most, so add, ordered subtract,
# and multiply all use a uint8_t logical carrier.  The uint32_t casts below are
# only C's integer-promotion discipline; no wider value is stored.
for operation in add sub mul; do
  grep -Eq "uint8_t zdependent_tiny_${operation}.*\(uint8_t, uint8_t\);" "$TMP_DIR/model.h"
  awk -v operation="$operation" '
    $0 ~ "^uint8_t zdependent_tiny_" operation ".*\\(" { printing = 1 }
    printing { print }
    printing && /^}$/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/dependent_tiny_${operation}.c"
  grep -Fq '((uint8_t)(((uint32_t)' "$TMP_DIR/dependent_tiny_${operation}.c"
  if grep -Eq 'sail_int|u128_|uint16_t|int16_t' "$TMP_DIR/dependent_tiny_${operation}.c"; then
    echo "symbolic tiny ${operation} lost its uint8_t semantic lifetime" >&2
    exit 1
  fi
done
grep -Fq ' + ' "$TMP_DIR/dependent_tiny_add.c"
grep -Fq ' - ' "$TMP_DIR/dependent_tiny_sub.c"
grep -Fq ' * ' "$TMP_DIR/dependent_tiny_mul.c"

# A native operand ABI is not itself a proof that an exact mathematical result
# fits a native carrier.  With no upper bounds on the dependent result, the
# multiplication clone deliberately retains Sail's arbitrary-precision path.
grep -Fq 'void zunbounded_dependent_mul(sail_int *rop, uint64_t, uint64_t);' "$TMP_DIR/model.h"
awk '
  /^void zdependent_mul.*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_unbounded_multiplication.c"
grep -Fq 'mult_int(' "$TMP_DIR/specialized_unbounded_multiplication.c"
if grep -Eq '\(\*\([^)]*\)\) = (u128_|\([^;]+ \* [^;]+\))' "$TMP_DIR/specialized_unbounded_multiplication.c"; then
  echo 'underconstrained multiplication was unsafely lowered to a native result' >&2
  exit 1
fi

# A comparison guard refines only the true control-flow edge. The parameter
# keeps its full uint64_t ABI, but the call edge carries value <= 8 into the
# dependent helper and demands a separate clone whose exact square is uint8_t.
# The unguarded caller above must continue to use its arbitrary-precision clone.
grep -Eq 'uint8_t zdependent_mul.*repr.*\(uint64_t, uint64_t\);' "$TMP_DIR/model.h"
awk '
  /^uint8_t zdependent_mul.*repr.*\(uint64_t zleft, uint64_t zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/guarded_dependent_multiplication.c"
grep -Fq '((uint8_t)(((uint32_t)((uint8_t) zleft)) * ((uint32_t)((uint8_t) zright))))' \
  "$TMP_DIR/guarded_dependent_multiplication.c"
if grep -Eq 'sail_int|mult_int|u128_|sail_native_conversion_failure' "$TMP_DIR/guarded_dependent_multiplication.c"; then
  echo 'branch-refined multiplication clone lost its uint8_t semantic carrier' >&2
  exit 1
fi

# Negating the same relation refines the opposite edge as well: value > 8 on
# the then edge implies value <= 8 on the else edge.
awk '
  /^uint8_t zelse_guarded_u64_tiny_square\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/else_guarded_u64_tiny_square.c"
grep -Eq 'zdependent_mul.*repr.*\(zvalue, zvalue\)' "$TMP_DIR/else_guarded_u64_tiny_square.c"

# Boolean helper calls retain their source function boundaries.  Their
# interprocedural predicate summaries nevertheless carry value <= 8 through a
# forwarding helper and refine only the true branch.  The resulting dependent
# multiplication uses the same unchecked native u8 specialization as a local
# comparison; no generated C bounds check or helper-body inlining is needed.
awk '
  /^bool zhelper_guarded_u64_tiny_square\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/helper_guarded_u64_tiny_square.c"
grep -Fq 'zforwarded_is_tiny_u64(zvalue)' "$TMP_DIR/helper_guarded_u64_tiny_square.c"
grep -Eq 'zpredicate_sensitive_square_le.*repr.*\(zvalue\)' "$TMP_DIR/helper_guarded_u64_tiny_square.c"
if grep -Eq 'sail_native_conversion_failure|zvalue *>|zvalue >' "$TMP_DIR/helper_guarded_u64_tiny_square.c"; then
  echo 'interprocedural predicate refinement inserted a generated bounds check' >&2
  exit 1
fi

awk '
  /^bool zpredicate_sensitive_square_le.*repr.*\(uint64_t zvalue\)/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/predicate_sensitive_square_le.c"
grep -Fq '((uint8_t)(((uint32_t)((uint8_t) zvalue)) * ((uint32_t)((uint8_t) zvalue))))' \
  "$TMP_DIR/predicate_sensitive_square_le.c"
grep -Fq 'u128_mul_u64(' "$TMP_DIR/predicate_sensitive_square_le.c"

# A negated helper summary refines its false edge.  The call remains visible,
# while the dependent body uses the same tight specialization selected above.
awk '
  /^bool znegated_helper_guarded_square\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/negated_helper_guarded_square.c"
grep -Fq 'zis_not_tiny_u64(zvalue)' "$TMP_DIR/negated_helper_guarded_square.c"
grep -Eq 'zpredicate_sensitive_square_le.*repr.*\(zvalue\)' "$TMP_DIR/negated_helper_guarded_square.c"
if grep -Eq 'sail_native_conversion_failure|zvalue *>|zvalue >' "$TMP_DIR/negated_helper_guarded_square.c"; then
  echo 'negated predicate refinement inserted a generated bounds check' >&2
  exit 1
fi

# An unresolved recursive boolean result is not a refinement certificate.  It
# must keep its call boundary and cannot justify the u8 dependent-multiply
# specialization merely because one recursive base case returns true.
awk '
  /^bool zrecursive_predicate_guarded_square\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/recursive_predicate_guarded_square.c"
grep -Fq 'zrecursive_is_tiny_u64(zvalue)' "$TMP_DIR/recursive_predicate_guarded_square.c"
helper_target=$(grep -Eo 'zpredicate_sensitive_square_le[^ (]*' "$TMP_DIR/helper_guarded_u64_tiny_square.c" | head -n 1)
negated_target=$(grep -Eo 'zpredicate_sensitive_square_le[^ (]*' "$TMP_DIR/negated_helper_guarded_square.c" | head -n 1)
recursive_target=$(grep -Eo 'zpredicate_sensitive_square_le[^ (]*' "$TMP_DIR/recursive_predicate_guarded_square.c" | head -n 1)
test "$helper_target" = "$negated_target"
if test "$helper_target" = "$recursive_target"; then
  echo 'unresolved recursive predicate unsafely justified the tight specialization' >&2
  exit 1
fi

# A helper with a constant-return path is not a refinement certificate either:
# true does not imply value <= 8.  Its caller must select the same broad clone
# as the unresolved recursive control, without inlining the helper.
awk '
  /^bool zunsound_predicate_guarded_square\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/unsound_predicate_guarded_square.c"
grep -Fq 'zunsound_mixed_predicate(zvalue)' "$TMP_DIR/unsound_predicate_guarded_square.c"
unsound_target=$(grep -Eo 'zpredicate_sensitive_square_le[^ (]*' "$TMP_DIR/unsound_predicate_guarded_square.c" | head -n 1)
test "$unsound_target" = "$recursive_target"

# Interval facts prove both true and false comparison outcomes before C
# emission. Their impossible arms, including the observable helper call, must
# leave neither a branch nor a specialization demand behind.
for function_name in comparison_fold_true comparison_fold_false; do
  awk -v function_name="$function_name" '
    $0 ~ "^uint64_t z" function_name "\\(" { printing = 1 }
    printing { print }
    printing && /^}/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/$function_name.c"
  if grep -Fq 'zcomparison_unreachable_specialization' "$TMP_DIR/$function_name.c"; then
    echo "$function_name retained a call from a proved unreachable arm" >&2
    exit 1
  fi
  if grep -Fq 'if (' "$TMP_DIR/$function_name.c"; then
    echo "$function_name retained a comparison proved constant" >&2
    exit 1
  fi
done
if grep -Eq 'zcomparison_unreachable_specialization.*repr' "$TMP_DIR/model.h"; then
  echo 'a proved unreachable call created a representation specialization demand' >&2
  exit 1
fi

# A predicate summary may establish the fact in the caller without copying or
# inlining the helper body. The outer helper call remains, while the
# contradictory nested edge is removed without a runtime guard.
awk '
  /^uint64_t zcomparison_fold_forwarded\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/comparison_fold_forwarded.c"
grep -Fq 'zforwarded_is_tiny_u64(zvalue)' "$TMP_DIR/comparison_fold_forwarded.c"
if grep -Fq 'zcomparison_observable_path(' "$TMP_DIR/comparison_fold_forwarded.c"; then
  echo 'forwarded predicate proof retained a contradictory nested call' >&2
  exit 1
fi

# Unknown comparisons and facts invalidated by mutation remain dynamic. This
# is the negative control against manufacturing reachability proofs.
for function_name in comparison_fold_unknown comparison_fold_after_mutation; do
  awk -v function_name="$function_name" '
    $0 ~ "^uint64_t z" function_name "\\(" { printing = 1 }
    printing { print }
    printing && /^}/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/$function_name.c"
  grep -Fq 'zcomparison_observable_path(' "$TMP_DIR/$function_name.c"
  grep -Fq 'if (' "$TMP_DIR/$function_name.c"
done

# Shift safety is discharged after path analysis. Direct and forwarded bounds
# therefore select unchecked native C operations while preserving the guarding
# branch/helper call; this is proof propagation, not function inlining.
for function_name in path_proven_shift_left path_proven_shift_right path_proven_arith_shift_right predicate_proven_shift_left; do
  awk -v function_name="$function_name" '
    $0 ~ "^uint64_t z" function_name "\\(" { printing = 1 }
    printing { print }
    printing && /^}/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/$function_name.c"
  if grep -Eq 'safe_rshift|>= UINT64_C\((32|64)\)' "$TMP_DIR/$function_name.c"; then
    echo "$function_name retained a C shift guard despite a semantic path proof" >&2
    exit 1
  fi
done
grep -Fq 'zforwarded_is_tiny_u64(zamount)' "$TMP_DIR/predicate_proven_shift_left.c"

# An unconstrained count and a saved predicate invalidated by mutation cannot
# justify an unchecked C shift. Both retain the defined fallback guard.
for function_name in unknown_shift_left invalidated_shift_left; do
  awk -v function_name="$function_name" '
    $0 ~ "^uint64_t z" function_name "\\(" { printing = 1 }
    printing { print }
    printing && /^}/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/$function_name.c"
  grep -Fq '>= UINT64_C(64)' "$TMP_DIR/$function_name.c"
done

# Slice extraction has the same C-definedness obligation as a right shift.
# Proved starts use a direct shift; an unknown start uses the safe primitive.
for function_name in path_proven_slice predicate_proven_slice; do
  awk -v function_name="$function_name" '
    $0 ~ "^uint64_t z" function_name "\\(" { printing = 1 }
    printing { print }
    printing && /^}/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/$function_name.c"
  if grep -Fq 'safe_rshift(zvalue, zstart)' "$TMP_DIR/$function_name.c"; then
    echo "$function_name retained a safe slice shift despite a semantic path proof" >&2
    exit 1
  fi
done
grep -Fq 'zforwarded_is_tiny_u64(zstart)' "$TMP_DIR/predicate_proven_slice.c"
awk '
  /^uint64_t zunknown_slice\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/unknown_slice.c"
grep -Fq 'safe_rshift(zvalue, zstart)' "$TMP_DIR/unknown_slice.c"

# A saved condition is valid across unrelated instructions, but writing one
# of its operands invalidates it. The replacement value is unconstrained, so
# this call must select the arbitrary-precision result clone rather than reuse
# the branch-refined uint8_t body.
awk '
  /^void zinvalidated_u64_square\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/invalidated_u64_square.c"
grep -Eq 'zdependent_mul.*repr.*\(&' "$TMP_DIR/invalidated_u64_square.c"
if grep -Eq 'zdependent_mul.*repr.*\(zcurrent, zcurrent\)' "$TMP_DIR/invalidated_u64_square.c"; then
  echo 'stale branch fact survived a write to one of its operands' >&2
  exit 1
fi

# Specializing a result does not change the stored representation of an
# aggregate field. The generated clone narrows at that field-read boundary.
grep -Eq 'uint8_t zinteger_box_value.*repr.*\(struct zIntegerBox\);' "$TMP_DIR/model.h"
awk '
  /^uint8_t zinteger_box_value.*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_aggregate_reader.c"
grep -Fq 'CONVERT_OF(mach_uint, sail_int)' "$TMP_DIR/specialized_aggregate_reader.c"

# A mutable variable keeps the representation required by its declared
# semantic type. Its small initializer must not silently narrow unbounded nat
# storage, because later assignments need not fit that initializer's type.
awk '
  /^void zmutable_unbounded_accumulator\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/mutable_unbounded_accumulator.c"
grep -Fq 'COPY(sail_int)' "$TMP_DIR/mutable_unbounded_accumulator.c"
if grep -Fq 'CONVERT_OF(mach_uint, sail_int)' "$TMP_DIR/mutable_unbounded_accumulator.c"; then
  echo 'mutable unbounded nat was narrowed from its initializer' >&2
  exit 1
fi

# Loop headers join the initial entry with every back edge.  The true guard
# proves current < 8 before the increment, so the loop-carried update remains
# within the original u8 input envelope and requires no arbitrary arithmetic.
awk '
  /^void zbounded_guarded_loop\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/bounded_guarded_loop.c"
grep -Fq 'uint8_t zcurrent;' "$TMP_DIR/bounded_guarded_loop.c"
grep -Eq 'zcurrent = .*uint8_t.*\+.*zcurrent|zcurrent = .*zcurrent.*\+.*uint8_t' "$TMP_DIR/bounded_guarded_loop.c"
if grep -Eq 'add_int|sail_int zcurrent' "$TMP_DIR/bounded_guarded_loop.c"; then
  echo 'guarded loop lost its inductive u8 invariant' >&2
  exit 1
fi

# The same control-flow machinery must not invent a finite range for a loop
# whose carried value starts as an unbounded nat.  Its accumulator remains a
# managed integer even though the independent iteration counter is bounded.
awk '
  /^void zunbounded_guarded_loop\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/unbounded_guarded_loop.c"
grep -Fq 'COPY(sail_int)' "$TMP_DIR/unbounded_guarded_loop.c"
grep -Fq 'add_int(' "$TMP_DIR/unbounded_guarded_loop.c"

# A signed value spanning the full u64 input range needs i128.  Mixed-width
# operands must be promoted before subtraction, and the complete arithmetic
# lifetime must remain free of arbitrary-precision integers.
grep -Fq '__int128 zsigned_state_gas_lifecycle(uint64_t, uint64_t, uint8_t);' "$TMP_DIR/model.h"
awk '
  /^__int128 zsigned_state_gas_lifecycle\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/signed_state_gas_lifecycle.c"
if grep -Fq 'sail_int' "$TMP_DIR/signed_state_gas_lifecycle.c"; then
  echo 'signed i128 arithmetic lifetime fell back to sail_int' >&2
  exit 1
fi
grep -Fq '(__int128)' "$TMP_DIR/signed_state_gas_lifecycle.c"

# Exception bookkeeping names remain stable map keys during lifetime analysis.
# In particular, analyzing a specialized throwing helper must terminate and
# retain the caller-proven u64 representation.
grep -Eq 'uint64_t zthrow_if_zzero.*repr.*\(uint64_t\);' "$TMP_DIR/model.h"

# A recursive edge reuses its current representation clone. It must not
# recursively invoke specialization or enqueue one clone per decreasing bound.
test "$(grep -Ec 'unit zrecursive_once.*repr.*\(uint64_t, bool\);' "$TMP_DIR/model.h")" -eq 1
awk '
  /^unit zrecursive_once.*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_recursive_once.c"
test "$(grep -Ec 'zrecursive_once.*repr.*\(' "$TMP_DIR/specialized_recursive_once.c")" -ge 2

# The nonzero branch proves that subtracting one stays in u64. Assignment
# ranges accumulated under that path proof keep the recursive temporary in
# u64, so the back edge targets the current clone without generating a wider
# i128 variant.
test "$(grep -Ec 'unit zrecursive_countdown.*repr.*\(uint64_t\);' "$TMP_DIR/model.h")" -eq 1
test "$(grep -Ec 'unit zrecursive_countdown.*repr.*\(__int128\);' "$TMP_DIR/model.h")" -eq 0
awk '
  /^unit zrecursive_countdown.*repr.*\(uint64_t/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_recursive_countdown.c"
test "$(grep -Ec 'zrecursive_countdown.*repr.*\(' "$TMP_DIR/specialized_recursive_countdown.c")" -ge 2
if grep -Eq '__int128|sail_int' "$TMP_DIR/specialized_recursive_countdown.c"; then
  echo 'guarded recursive countdown widened despite its decreasing u64 invariant' >&2
  exit 1
fi

# A native-width aggregate field may pass through a source local before it
# reaches a generic helper.  Whole-body lifetime propagation must retain that
# width and demand the u64 helper clone without changing the canonical ABI.
grep -Eq 'uint64_t zgeneric_local_length.*repr.*\(uint64_t\);' "$TMP_DIR/model.h"
awk '
  /^uint64_t zaggregate_local_length\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/aggregate_local_length.c"
grep -Eq 'zgeneric_local_length.*repr.*\(' "$TMP_DIR/aggregate_local_length.c"
if grep -Fq 'sail_int' "$TMP_DIR/aggregate_local_length.c"; then
  echo 'native aggregate local fell back to sail_int before a generic call' >&2
  exit 1
fi

# Constructor facts survive JIB's field-write, whole-aggregate-copy, and
# field-read sequence.  Although this source aggregate still owns a managed
# nat field, the recovered value and its generic call edge are proved u8.
grep -Eq 'zgeneric_local_length.*repr.*\([^;]*uint8_t\);' "$TMP_DIR/model.h"
awk '
  /^void zaggregate_constructor_fact\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/aggregate_constructor_fact.c"
grep -Fq 'uint8_t zrecovered;' "$TMP_DIR/aggregate_constructor_fact.c"
grep -Eq 'zgeneric_local_length.*repr.*\(' "$TMP_DIR/aggregate_constructor_fact.c"

# Replacing the field with an unbounded nat replaces its constructor fact.
# The later read and call must not reuse the original u8 proof.
awk '
  /^void zinvalidated_aggregate_constructor_fact\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/invalidated_aggregate_constructor_fact.c"
grep -Fq 'COPY(sail_int)' "$TMP_DIR/invalidated_aggregate_constructor_fact.c"
grep -Eq 'zgeneric_local_length\(.*zgh' "$TMP_DIR/invalidated_aggregate_constructor_fact.c"
if grep -Eq 'zgeneric_local_length.*repr.*\(' "$TMP_DIR/invalidated_aggregate_constructor_fact.c"; then
  echo 'aggregate field mutation retained a stale constructor bound' >&2
  exit 1
fi

# Return summaries carry semantic result bounds back across call edges before
# representation selection.  The source ABI still returns an unbounded nat,
# while these callers demand u64 -> u8 clones and square the results natively.
grep -Eq 'uint8_t zbounded_callee_result.*repr.*\(uint64_t\);' "$TMP_DIR/model.h"
grep -Eq 'uint8_t zrecursive_bounded_callee.*repr.*\(uint64_t\);' "$TMP_DIR/model.h"
for function_name in consume_bounded_callee_result consume_recursive_bounded_callee; do
  awk -v function_name="$function_name" '
    $0 ~ "^bool z" function_name "\\(" { printing = 1 }
    printing { print }
    printing && /^}$/ { printing = 0 }
  ' "$TMP_DIR/model.c" > "$TMP_DIR/${function_name}.c"
  grep -Fq 'uint8_t zbounded;' "$TMP_DIR/${function_name}.c"
  grep -Fq '((uint8_t)(((uint32_t)zbounded) * ((uint32_t)zbounded)))' \
    "$TMP_DIR/${function_name}.c"
  if grep -Eq 'sail_int|mult_int' "$TMP_DIR/${function_name}.c"; then
    echo "callee return bound was not propagated into ${function_name}" >&2
    exit 1
  fi
done

# Recursive strongly connected components are summarized to a fixed point.
# The bounded recursive clone must call a representation clone, not fall back
# through the managed source ABI on its back edge.
awk '
  /^uint8_t zrecursive_bounded_callee.*repr.*\(uint8_t zvalue\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/recursive_bounded_callee.c"
grep -Eq 'zrecursive_bounded_callee.*repr.*\(' "$TMP_DIR/recursive_bounded_callee.c"
if grep -Fq 'sail_int' "$TMP_DIR/recursive_bounded_callee.c"; then
  echo 'recursive return-summary clone fell back to a managed integer' >&2
  exit 1
fi

# An unconstrained identity callee has no finite return proof.  Its caller is
# the conservative control and must retain exact arbitrary-precision multiply.
awk '
  /^bool zconsume_unbounded_callee_result\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/consume_unbounded_callee_result.c"
grep -Fq 'sail_int' "$TMP_DIR/consume_unbounded_callee_result.c"
grep -Fq 'mult_int(' "$TMP_DIR/consume_unbounded_callee_result.c"

# Generic argument and result positions carry independent proof-backed
# representations.  A full-u64 payload length plus RLP-style framing headroom
# therefore specializes one generic source body as u64 -> u128.
grep -Eq 'sail_u128 zgeneric_encoded_length.*repr.*\(uint64_t\);' "$TMP_DIR/model.h"
awk '
  /^sail_u128 zaggregate_encoded_length\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/aggregate_encoded_length.c"
grep -Eq 'zgeneric_encoded_length.*repr.*\(' "$TMP_DIR/aggregate_encoded_length.c"
if grep -Fq 'sail_int' "$TMP_DIR/aggregate_encoded_length.c"; then
  echo 'dependent u64-to-u128 generic call fell back to sail_int' >&2
  exit 1
fi

# A representation clone may prove a generic comparison even when one source
# operand is too large for either operand's native carrier.  Fold the guard
# from the clone's complete argument interval, and remove the now-dead literal
# temporary rather than retaining GMP solely for `2^256`.
grep -Eq 'bool zguarded_comparison.*repr.*\(sail_u128\);' "$TMP_DIR/model.h"
awk '
  /^bool zguarded_comparison.*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_guarded_comparison.c"
if grep -Fq 'sail_int' "$TMP_DIR/specialized_guarded_comparison.c"; then
  echo 'proved generic guard retained an arbitrary-precision literal temporary' >&2
  exit 1
fi
