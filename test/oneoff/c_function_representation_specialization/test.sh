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
  --c-preserve full_addmod \
  --c-preserve full_mulmod \
  --c-preserve narrow_after_guard \
  --c-preserve word_words_for_bytes \
  --c-preserve native_words_for_bytes \
  --c-preserve full_u64_words_for_bytes \
  --c-preserve unbounded_dependent_add \
  --c-preserve bounded_integer_box_value \
  --c-preserve mutable_unbounded_accumulator \
  --c-preserve signed_state_gas_lifecycle \
  --c-preserve bounded_throw_if_zero \
  --c-preserve bounded_recursive_once \
  --c-preserve bounded_recursive_countdown \
  --c-preserve aggregate_local_length \
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

# A concrete signature may not acquire a narrower ABI merely because one
# caller happens to supply a bounded representation. The source must expose
# that semantic variability through an explicit quantified parameter.
if "$SAIL" "$@" --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve rejected_concrete_specialization \
  "$TEST_DIR/concrete_signature.sail" -o "$TMP_DIR/concrete_signature" \
  2>"$TMP_DIR/concrete_signature.err"
then
  echo 'concrete function signature was silently representation-specialized' >&2
  exit 1
fi
grep -Fq 'Function concrete_add has a concrete Sail argument 2' "$TMP_DIR/concrete_signature.err"
grep -Fq 'Quantify this position with appropriate semantic bounds' "$TMP_DIR/concrete_signature.err"

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

# A full-width caller keeps the canonical u256/u256 body alive.  Its explicit
# modulo-2^256 source semantics select wrapping u256 addition without ever
# materialising the otherwise 257-bit mathematical sum.
grep -Fq 'sail_u256 zleaf_add(sail_u256, sail_u256);' "$TMP_DIR/model.h"
awk '
  /^sail_u256 zleaf_add\(sail_u256 zleft, sail_u256 zright\)/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/full_width_leaf_add.c"
grep -Fq 'u256_add(zleft, zright)' "$TMP_DIR/full_width_leaf_add.c"
if grep -Fq 'sail_int' "$TMP_DIR/full_width_leaf_add.c"; then
  echo 'modulo-2^256 full-width addition fell back to sail_int' >&2
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


# The opposite direction remains a separate, proof-backed narrowing path: the
# guarded word is stored as u256, but its typed occurrence is word_bit_count.
grep -Fq 'u256_extract_u64(' "$TMP_DIR/model.c"

# A single unbounded semantic helper is cloned at the fixed representation
# and exact interval demanded by each bounded caller. The word clone may need
# arbitrary precision because word_max + 31 is 257 bits. Both u64 clones must
# remain native even though one input is 0..255 and the other is full u64.
grep -Eq 'sail_u256 zwords_for_bytes.*repr.*\(sail_u256\);' "$TMP_DIR/model.h"
test "$(grep -Ec 'uint64_t zwords_for_bytes.*repr.*\(uint64_t\);' "$TMP_DIR/model.h")" -eq 2
awk '
  /^uint64_t zwords_for_bytes.*repr.*\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/specialized_integer_helpers.c"
if grep -Fq 'sail_int' "$TMP_DIR/specialized_integer_helpers.c"; then
  echo 'specialized bounded-integer helper fell back to sail_int' >&2
  exit 1
fi
grep -Fq 'u128_add_u64(' "$TMP_DIR/specialized_integer_helpers.c"

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

# Specializing a result does not change the stored representation of an
# aggregate field. The generated clone narrows at that field-read boundary.
grep -Eq 'uint64_t zinteger_box_value.*repr.*\(struct zIntegerBox\);' "$TMP_DIR/model.h"
awk '
  /^uint64_t zinteger_box_value.*repr.*\(/ { printing = 1 }
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

# A signed value spanning the full u64 input range needs i128.  Mixed-width
# operands must be promoted before subtraction, and the complete arithmetic
# lifetime must remain free of arbitrary-precision integers.
grep -Fq '__int128 zsigned_state_gas_lifecycle(uint64_t, uint64_t, uint64_t);' "$TMP_DIR/model.h"
awk '
  /^__int128 zsigned_state_gas_lifecycle\(/ { printing = 1 }
  printing { print }
  printing && /^}$/ { printing = 0 }
' "$TMP_DIR/model.c" > "$TMP_DIR/signed_state_gas_lifecycle.c"
if grep -Fq 'sail_int' "$TMP_DIR/signed_state_gas_lifecycle.c"; then
  echo 'signed i128 arithmetic lifetime fell back to sail_int' >&2
  exit 1
fi
grep -Fq '((__int128)' "$TMP_DIR/signed_state_gas_lifecycle.c"

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

# If path-insensitive analysis gives the guarded recursive argument a wider
# representation, queue exactly one alternate clone. That clone's stable
# recursive edge must target itself rather than creating further demands.
test "$(grep -Ec 'unit zrecursive_countdown.*repr.*\(uint64_t\);' "$TMP_DIR/model.h")" -eq 1
test "$(grep -Ec 'unit zrecursive_countdown.*repr.*\(__int128\);' "$TMP_DIR/model.h")" -eq 1

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
