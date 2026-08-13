#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_optimized_model_modules.XXXXXX")
cleanup() {
  if [ "${KEEP_TEST_TMP:-0}" = 1 ]; then
    printf 'preserved test output: %s\n' "$TMP_DIR" >&2
  else
    rm -rf "$TMP_DIR"
  fi
}
trap cleanup EXIT

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

HOST_INCLUDE="$TMP_DIR/ffi/optimized/include/evmsail/host"
mkdir -p "$HOST_INCLUDE"
cp "$TEST_DIR/host-sentinel.txt" "$HOST_INCLUDE/sentinel.txt"
cp "$TEST_DIR/external_types.h" "$HOST_INCLUDE/types.h"

"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail --c-output-dir "$TMP_DIR/ffi/optimized" \
  --c-optimized-include-dir "$TMP_DIR/ffi/optimized/include" \
  --c-optimized-external-type pair=evmsail/host/types.h \
  --c-optimized-external-type byte_slice=evmsail/host/types.h \
  --c-optimized-external-type byte_slice_small=evmsail/host/types.h \
  --c-optimized-external-type canonical_slice=evmsail/host/types.h \
  --c-optimized-external-type canonical_list=evmsail/host/types.h \
  --c-optimized-byte-pointer-field byte_slice.bytes=test_bytes_at \
  --c-optimized-byte-pointer-field byte_slice_small.bytes=test_bytes_at \
  --c-optimized-byte-pointer-field analyzed_code.bytes=test_bytes_at \
  --c-optimized-byte-pointer-type jump_table_index=test_jumpdests_at \
  --c-preserve-type pair --c-preserve-type byte_slice --c-preserve-type byte_slice_small --c-preserve-type canonical_slice \
  --c-preserve-type canonical_list \
  --c-preserve-type analyzed_code \
  --c-preserve-type sample_choice --c-preserve-type erased_unit_choice \
  --c-preserve-type wide_word --c-preserve-type four_bytes --c-preserve-type twenty_bytes --c-preserve-type lane_five_bytes --c-preserve-type fixed_ids \
  --c-preserve-type fixed_ids_box --c-preserve-type equality_pair \
  --c-preserve pair_sum --c-preserve sample_choice_value --c-preserve added_is_nonzero \
  --c-preserve boolean_cleanup --c-preserve positive_branch --c-preserve early_wide_guard --c-preserve widened_tuple_match \
  --c-preserve repeated_branch \
  --c-preserve repeated_call_branch --c-preserve boolean_value_join --c-preserve boolean_comparison_join \
  --c-preserve call_discard_internal_parameter --c-preserve call_discard_computed_parameter \
  --c-preserve preserve_unused_parameter \
  --c-preserve widen_optional_byte \
  --c-preserve test_gas --c-preserve test_gas_alias --c-preserve test_fixed_bytes_zero \
  --c-preserve test_fixed_bytes_one --c-preserve test_lane_bytes --c-preserve twenty_bytes_equal \
  --c-preserve runtime_label_test --c-preserve runtime_pair --c-preserve always_fatal --c-preserve fatal_error \
  --c-preserve terminal_assertion \
  --c-preserve decrement_byte --c-preserve increment_to --c-preserve count_four \
  --c-preserve increment_to_via_call \
  --c-preserve wide_identity --c-preserve aggregate_early_return \
  --c-preserve widen_byte --c-preserve conditional_wide_return --c-preserve narrow_then_decrement \
  --c-preserve widen_three_byte --c-preserve narrow_wide_byte \
  --c-preserve narrow_word_remainder --c-preserve masked_high_nibble \
  --c-preserve one_bit_is_set \
  --c-preserve unsigned_le_signed --c-preserve signed_lt_unsigned --c-preserve unsigned_eq_signed \
  --c-preserve guarded_blob_gas_add \
  --c-preserve u256 --c-preserve nested_wide_identity \
  --c-preserve wide_pair_identity \
  --c-preserve four_bytes_identity \
  --c-preserve identity_one --c-preserve identity_two --c-preserve branch_one --c-preserve branch_five \
  --c-preserve byte_slice_at --c-preserve byte_slice_small_at \
  --c-preserve canonical_slice_len \
  --c-preserve canonical_list_count --c-preserve canonical_list_identity \
  --c-preserve canonical_list_count_after_identity \
  --c-preserve byte_slice_same_start \
  --c-preserve byte_slice_next --c-preserve byte_slice_advance --c-preserve byte_slice_distance \
  --c-preserve jumpdest_from_offset --c-preserve empty_jumpdest --c-preserve empty_direct_jumpdest \
  --c-preserve allocated_jumpdest --c-preserve guarded_host_mix --c-preserve guarded_host_slice \
  --c-preserve reset_then_mix --c-preserve reset_via_host --c-preserve guarded_reset \
  --c-preserve reset_when_pair \
  --c-preserve guarded_wide_offset \
  --c-preserve widened_host_call \
  --c-preserve analyzed_code_at --c-preserve analyzed_code_copy \
  --c-preserve main --c-preserve run --c-preserve step --c-preserve pick_fixed_id --c-preserve pick_initialized_id \
  --c-preserve pick_guarded_id --c-preserve pick_test_discount \
  --c-preserve machine_pick_zero --c-preserve reset_counter --c-preserve preserve_counter_snapshot \
  --c-preserve make_public_pair --c-preserve save_pair_then_read --c-preserve initialized_comparison_return \
  --c-preserve call_specialized_comparison --c-preserve call_specialized_enum_comparison \
  --c-preserve conditional_word --c-preserve conditional_bool --c-preserve conditional_bool_false \
  --c-preserve terminal_choice --c-preserve terminal_enum_match --c-preserve terminal_enum_grouped \
  --c-preserve state_passing_outcome --c-preserve state_passing_guard --c-preserve call_state_passing_guard \
  --c-preserve state_passing_guard_failed \
  --c-preserve terminal_enum_match_or_fatal \
  --c-preserve fatal_guard_result_is_unread \
  --c-preserve terminal_unit_variant_match \
  --c-preserve terminal_fixed_bytes_match \
  --c-preserve catch_byte \
  "$TEST_DIR/model.sail_project"

SPEC_INCLUDE="$TMP_DIR/ffi/optimized/include"
SPEC_SOURCE="$TMP_DIR/ffi/optimized/src/spec"

for module in base host_contracts machine entry; do
  test -f "$SPEC_INCLUDE/evmsail/spec/$module.h"
  test -f "$SPEC_SOURCE/$module.c"
done
test -f "$SPEC_INCLUDE/evmsail/spec.h"
test -f "$SPEC_INCLUDE/evmsail/spec/abi.h"
test -f "$SPEC_INCLUDE/evmsail/spec/support.h"
printf '%s\n' base.c host_contracts.c machine.c entry.c > "$TMP_DIR/expected-sources.list"
cmp "$TMP_DIR/expected-sources.list" "$SPEC_SOURCE/sources.list"
cmp "$TEST_DIR/host-sentinel.txt" "$HOST_INCLUDE/sentinel.txt"

grep -Fq '#include "evmsail/spec/base.h"' "$SPEC_INCLUDE/evmsail/spec.h"
grep -Fq '#include "evmsail/host/types.h"' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint16_t pair_sum(struct pair value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t canonical_slice_len(TestBytes value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t canonical_list_count(TestList value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'TestList canonical_list_identity(TestList value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t canonical_list_count_after_identity(TestList value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'enum state_passing_outcome state_passing_guard(uint8_t read_only, uint32_t *restrict state, bool fail);' "$SPEC_INCLUDE/evmsail/spec/machine.h"
sed -n '/^enum state_passing_outcome state_passing_guard(/,/^}/p' "$SPEC_SOURCE/machine.c" > "$TMP_DIR/state_passing_guard.c"
grep -Eq '\(\*state\) = (UINT32_C\(0\)|\(uint32_t\)STATE_PASSING_ZERO);' \
  "$TMP_DIR/state_passing_guard.c"
grep -Fq 'return StateFailed;' "$TMP_DIR/state_passing_guard.c"
grep -Fq 'return StateContinue;' "$TMP_DIR/state_passing_guard.c"
if grep -Eq 'tuple_|rop[0-9]|\(\*state\) = \(\*state\)' "$TMP_DIR/state_passing_guard.c"; then
  echo 'state-passing lowering retained a tuple, positional output, or self-assignment' >&2
  exit 1
fi
sed -n '/^enum state_passing_outcome forward_state_passing_guard(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/forward_state_passing_guard.c"
grep -Fq 'return state_passing_guard(read_only, state, fail);' \
  "$TMP_DIR/forward_state_passing_guard.c"
if grep -Eq 'tuple_|rop[0-9]|state_passing_outcome_[0-9]' \
    "$TMP_DIR/forward_state_passing_guard.c"; then
  echo 'nested state-passing call retained an aggregate or one-use result local' >&2
  exit 1
fi
sed -n '/^bool state_passing_guard_failed(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/state_passing_guard_failed.c"
grep -Eq 'state_passing_guard\(read_only, &state_after(_[0-9]+)*, fail\)' \
  "$TMP_DIR/state_passing_guard_failed.c"
if grep -Eq 'tuple_|\.tup[0-9]|rop[0-9]' "$TMP_DIR/state_passing_guard_failed.c"; then
  echo 'non-state-returning caller retained a state-passing tuple carrier' >&2
  exit 1
fi
if grep -Fq 'struct canonical_slice' "$SPEC_INCLUDE/evmsail/spec/base.h"; then
  echo 'optimized extraction emitted a nominal definition for a canonically named external representation' >&2
  exit 1
fi
if grep -Fq 'struct canonical_list' "$SPEC_INCLUDE/evmsail/spec/base.h"; then
  echo 'optimized extraction emitted a managed nominal definition for an external representation' >&2
  exit 1
fi
if grep -Fq 'bool eq_anything(' "$SPEC_INCLUDE/evmsail/spec/base.h"; then
  echo 'optimized extraction exposed a polymorphic compiler intrinsic as a C ABI symbol' >&2
  exit 1
fi
grep -Fq 'extern const uint16_t TEST_GAS;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'const uint16_t TEST_GAS = UINT16_C(21000);' "$SPEC_SOURCE/base.c"
test "$(grep -Fc 'TEST_GAS =' "$SPEC_SOURCE/base.c")" -eq 1
grep -Fq 'extern const uint16_t TEST_GAS_ALIAS;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'const uint16_t TEST_GAS_ALIAS = UINT16_C(21000);' "$SPEC_SOURCE/base.c"
if grep -Eq 'create_letbind_[0-9]+\(void\).*TEST_GAS_ALIAS' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction retained runtime initialization for a scalar constant alias' >&2
  exit 1
fi
grep -Fq 'extern const vector_17_uint_16 TEST_DISCOUNT;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'const vector_17_uint_16 TEST_DISCOUNT = {' "$SPEC_SOURCE/base.c"
grep -Fq '.len = 17,' "$SPEC_SOURCE/base.c"
grep -Fq 'UINT16_C(256), UINT16_C(16), UINT16_C(15)' "$SPEC_SOURCE/base.c"
grep -Fq 'UINT16_C(3), UINT16_C(2),' "$SPEC_SOURCE/base.c"
grep -Fq 'UINT16_C(1)' "$SPEC_SOURCE/base.c"
grep -Fq 'extern const bytes4 TEST_FIXED_BYTES_ZERO;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'const bytes4 TEST_FIXED_BYTES_ZERO = {' "$SPEC_SOURCE/base.c"
grep -Fq '.bytes = {' "$SPEC_SOURCE/base.c"
grep -Fq 'extern const bytes4 TEST_FIXED_BYTES_ONE;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'const bytes4 TEST_FIXED_BYTES_ONE = {' "$SPEC_SOURCE/base.c"
grep -Fq 'INT64_C(1), INT64_C(0), INT64_C(0), INT64_C(0)' "$SPEC_SOURCE/base.c"
if grep -Fq 'test_word_to_four(' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction retained an explicitly static-evaluable fixed-byte initializer call' >&2
  exit 1
fi
grep -Fq 'typedef struct { uint64_t lanes[1]; } lane_bytes5;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'extern const lane_bytes5 TEST_LANE_BYTES;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'const lane_bytes5 TEST_LANE_BYTES = {' "$SPEC_SOURCE/base.c"
grep -Fq 'UINT64_C(4886718345)' "$SPEC_SOURCE/base.c"
awk '
  /^uint8_t decrement_byte\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/decrement_byte.c"
grep -Eq 'uint8_t result[^;]* = value;' "$TMP_DIR/decrement_byte.c"
if grep -Eq 'unit [A-Za-z0-9_]+;' "$TMP_DIR/decrement_byte.c"; then
  echo 'optimized extraction retained an unread unit branch result' >&2
  exit 1
fi
if grep -Eq 'uint8_t result[^;]*;' "$TMP_DIR/decrement_byte.c" && \
   ! grep -Eq 'uint8_t result[^;]* = value;' "$TMP_DIR/decrement_byte.c"; then
  echo 'optimized extraction split an adjacent scalar declaration and initialization' >&2
  exit 1
fi
sed -n \
  '/^uint8_t increment_to(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/increment_to.c"
grep -Fq 'while (current < limit)' "$TMP_DIR/increment_to.c"
if grep -Eq 'goto |while_[0-9]+:|wend_[0-9]+:|bool tmp_' "$TMP_DIR/increment_to.c"; then
  echo 'optimized extraction retained JIB loop labels or its condition temporary' >&2
  exit 1
fi
sed -n \
  '/^uint8_t count_four(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/count_four.c"
grep -Eq 'while \(_?index <= [A-Za-z0-9_]+\)' "$TMP_DIR/count_four.c"
if grep -Eq 'goto |for_start_[0-9]+:|for_end_[0-9]+:' "$TMP_DIR/count_four.c"; then
  echo 'optimized extraction retained JIB foreach labels or back edge' >&2
  exit 1
fi
sed -n \
  '/^uint8_t increment_to_via_call(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/increment_to_via_call.c"
grep -Fq 'while (true)' "$TMP_DIR/increment_to_via_call.c"
grep -Fq 'break;' "$TMP_DIR/increment_to_via_call.c"
if grep -Eq 'goto |while_[0-9]+:|wend_[0-9]+:' "$TMP_DIR/increment_to_via_call.c"; then
  echo 'optimized extraction retained JIB labels around a called loop condition' >&2
  exit 1
fi
sed -n \
  '/^u256 aggregate_early_return(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/aggregate_early_return.c"
test "$(grep -Fc 'return result;' "$TMP_DIR/aggregate_early_return.c")" -eq 1
test "$(grep -Fc 'return ' "$TMP_DIR/aggregate_early_return.c")" -eq 1
grep -Eq 'result = wide_identity\(result\);' "$TMP_DIR/aggregate_early_return.c"
if grep -Fq 'return wide_identity(result);' "$TMP_DIR/aggregate_early_return.c"; then
  echo 'optimized extraction retained multiple returns that disable aggregate NRVO' >&2
  exit 1
fi
awk '
  /^bool added_is_nonzero\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/added_is_nonzero.c"
grep -Eq 'uint16_t [A-Za-z0-9_]+ = add_byte\(left, right\);' "$TMP_DIR/added_is_nonzero.c"
awk '
  /^uint8_t boolean_cleanup\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/boolean_cleanup.c"
grep -Fq 'if (flag)' "$TMP_DIR/boolean_cleanup.c"
if grep -Eq '!\(!|== true|!= false|tmp_|result_' "$TMP_DIR/boolean_cleanup.c"; then
  echo 'optimized extraction retained trivial boolean scaffolding' >&2
  exit 1
fi
if grep -REq '!\([A-Za-z_][A-Za-z0-9_.]*\)' "$SPEC_SOURCE"; then
  echo 'optimized extraction parenthesized an atomic boolean negation' >&2
  exit 1
fi
if ! grep -REq 'if \(!flag\) \{' "$SPEC_SOURCE"; then
  echo 'optimized extraction did not simplify an atomic fixed assertion' >&2
  exit 1
fi
if grep -REq '^[[:space:]]*if .* goto [A-Za-z_][A-Za-z0-9_]*;' "$SPEC_SOURCE"; then
  echo 'optimized extraction emitted an unbraced conditional jump' >&2
  exit 1
fi
if grep -REq '^[[:space:]]*if .*__builtin_trap\(\);$' "$SPEC_SOURCE"; then
  echo 'optimized extraction emitted an unbraced fixed assertion' >&2
  exit 1
fi
if grep -REq '^[[:space:]]*if \((true|false)\)' "$SPEC_SOURCE"; then
  echo 'optimized extraction retained a literal conditional branch' >&2
  exit 1
fi
awk '
  /^bool boolean_value_join\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
  /^bool boolean_comparison_join\(/ { printing = 1 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/boolean_value_context.c"
grep -Fq 'return (bool)(first && second);' "$TMP_DIR/boolean_value_context.c"
grep -Fq 'return (bool)((left == right) || flag);' "$TMP_DIR/boolean_value_context.c"
awk '
  /^uint8_t positive_branch\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/positive_branch.c"
grep -Fq 'if (flag)' "$TMP_DIR/positive_branch.c"
grep -Fq 'return UINT8_C(1);' "$TMP_DIR/positive_branch.c"
if grep -Fq 'if (!(flag))' "$TMP_DIR/positive_branch.c"; then
  echo 'optimized extraction retained a leading negative branch' >&2
  exit 1
fi
if grep -Fq '} else {' "$TMP_DIR/positive_branch.c"; then
  echo 'optimized extraction retained else after a terminal value return' >&2
  exit 1
fi
awk '
  /^bool early_wide_guard\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/early_wide_guard.c"
grep -Fq 'return true;' "$TMP_DIR/early_wide_guard.c"
if grep -Eq 'goto |end_function_|result_' "$TMP_DIR/early_wide_guard.c"; then
  echo 'optimized extraction retained a mutable join for an early scalar return' >&2
  exit 1
fi
sed -n \
  '/^struct tuple_uint_16_uint_16 widened_tuple_match(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/widened_tuple_match.c"
test "$(grep -Fc 'return ((struct tuple_uint_16_uint_16){' "$TMP_DIR/widened_tuple_match.c")" -eq 3
grep -Fq '.tup0 = UINT16_C(1), .tup1 = UINT16_C(2)' "$TMP_DIR/widened_tuple_match.c"
grep -Fq '.tup0 = UINT16_C(3), .tup1 = UINT16_C(4)' "$TMP_DIR/widened_tuple_match.c"
grep -Fq '.tup0 = UINT16_C(5), .tup1 = UINT16_C(6)' "$TMP_DIR/widened_tuple_match.c"
grep -Fq 'switch (choice)' "$TMP_DIR/widened_tuple_match.c"
if grep -Eq 'goto |finish_match_|tmp_|result_' "$TMP_DIR/widened_tuple_match.c"; then
  echo 'optimized extraction retained a mutable join or labels for a widened tuple match' >&2
  exit 1
fi
sed -n \
  '/^uint8_t terminal_enum_match(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/terminal_enum_match.c"
test "$(grep -Fc 'return UINT8_C(' "$TMP_DIR/terminal_enum_match.c")" -eq 4
grep -Fq 'switch (choice)' "$TMP_DIR/terminal_enum_match.c"
test "$(grep -Fc 'case Terminal' "$TMP_DIR/terminal_enum_match.c")" -eq 4
if grep -Fq 'default:' "$TMP_DIR/terminal_enum_match.c"; then
  echo 'optimized extraction retained a default arm instead of explicit exhaustive enum cases' >&2
  exit 1
fi
if grep -Eq 'goto |finish_match_|tmp_|result_' "$TMP_DIR/terminal_enum_match.c"; then
  echo 'optimized extraction retained a mutable join or labels for a terminal enum match' >&2
  exit 1
fi
sed -n \
  '/^uint8_t terminal_enum_grouped(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/terminal_enum_grouped.c"
grep -Fq 'switch (choice)' "$TMP_DIR/terminal_enum_grouped.c"
test "$(grep -Fc 'case Terminal' "$TMP_DIR/terminal_enum_grouped.c")" -eq 4
test "$(grep -Fc 'return UINT8_C(1);' "$TMP_DIR/terminal_enum_grouped.c")" -eq 1
test "$(grep -Fc 'return UINT8_C(2);' "$TMP_DIR/terminal_enum_grouped.c")" -eq 1
if grep -Eq 'default:|/\* complete \*/' "$TMP_DIR/terminal_enum_grouped.c"; then
  echo 'optimized extraction failed to group identical exhaustive enum arms' >&2
  exit 1
fi
sed -n \
  '/^uint8_t terminal_enum_match_or_fatal(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/terminal_enum_match_or_fatal.c"
test "$(grep -Fc 'return UINT8_C(' "$TMP_DIR/terminal_enum_match_or_fatal.c")" -eq 2
grep -Fq 'fatal_error(TestFatal);' "$TMP_DIR/terminal_enum_match_or_fatal.c"
grep -Fq 'switch (choice)' "$TMP_DIR/terminal_enum_match_or_fatal.c"
test "$(grep -Fc 'case Terminal' "$TMP_DIR/terminal_enum_match_or_fatal.c")" -eq 4
if grep -Fq 'default:' "$TMP_DIR/terminal_enum_match_or_fatal.c"; then
  echo 'optimized extraction retained a default arm for an exhaustive fatal enum match' >&2
  exit 1
fi
if grep -Fq '    return;' "$TMP_DIR/terminal_enum_match_or_fatal.c"; then
  echo 'optimized extraction appended a void return after a noreturn match arm' >&2
  exit 1
fi
if grep -Eq 'goto |finish_match_|uint8_t (tmp_|result_)' "$TMP_DIR/terminal_enum_match_or_fatal.c"; then
  echo 'optimized extraction retained a mutable join for a fatal match arm' >&2
  exit 1
fi

sed -n \
  '/^uint8_t fatal_guard_result_is_unread(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/fatal_guard_result_is_unread.c"
grep -Fq 'if (flag)' "$TMP_DIR/fatal_guard_result_is_unread.c"
grep -Fq 'fatal_error(TestFatal);' "$TMP_DIR/fatal_guard_result_is_unread.c"
grep -Fq 'return UINT8_C(7);' "$TMP_DIR/fatal_guard_result_is_unread.c"
sed -n \
  '/^void terminal_unit_variant_match(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/terminal_unit_variant_match.c"
grep -Fq 'switch (choice.kind)' "$TMP_DIR/terminal_unit_variant_match.c"
test "$(grep -Fc 'case Kind_' "$TMP_DIR/terminal_unit_variant_match.c")" -eq 3
if grep -Fq 'default:' "$TMP_DIR/terminal_unit_variant_match.c"; then
  echo 'optimized extraction retained a default arm instead of explicit exhaustive variant cases' >&2
  exit 1
fi
grep -Fq 'terminal_unit_empty(' "$TMP_DIR/terminal_unit_variant_match.c"
grep -Fq 'terminal_unit_other_empty(' "$TMP_DIR/terminal_unit_variant_match.c"
grep -Fq 'terminal_unit_byte(' "$TMP_DIR/terminal_unit_variant_match.c"
test "$(grep -Fc '    return;' "$TMP_DIR/terminal_unit_variant_match.c")" -eq 3
if grep -Fq '  {' "$TMP_DIR/terminal_unit_variant_match.c" || \
   grep -Fq '    break;' "$TMP_DIR/terminal_unit_variant_match.c"; then
  echo 'optimized extraction retained redundant scopes or a fallthrough break in a terminal unit match' >&2
  exit 1
fi
if grep -Fq 'if (choice.kind' "$TMP_DIR/terminal_unit_variant_match.c"; then
  echo 'optimized extraction lowered a terminal unit variant match as an if ladder' >&2
  exit 1
fi
sed -n \
  '/^uint8_t terminal_assertion(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/terminal_assertion.c"
grep -Fq '__builtin_trap();' "$TMP_DIR/terminal_assertion.c"
if grep -Fq 'sail_match_failure' "$TMP_DIR/terminal_assertion.c"; then
  echo 'optimized extraction emitted a match failure after a terminal assertion' >&2
  exit 1
fi
sed -n \
  '/^uint8_t terminal_fixed_bytes_match(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/terminal_fixed_bytes_match.c"
test "$(grep -Fc 'return UINT8_C(' "$TMP_DIR/terminal_fixed_bytes_match.c")" -eq 3
test "$(grep -Fc 'eq_bytes4(bytes,' "$TMP_DIR/terminal_fixed_bytes_match.c")" -eq 2
if grep -Eq 'goto |finish_match_|tmp_|result_' "$TMP_DIR/terminal_fixed_bytes_match.c"; then
  echo 'optimized extraction retained a mutable join or labels for a guarded fixed-byte match' >&2
  exit 1
fi
awk '
  /^uint8_t repeated_branch\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/repeated_branch.c"
grep -Fq 'if (first || second)' "$TMP_DIR/repeated_branch.c"
test "$(grep -Fc 'return UINT8_C(1);' "$TMP_DIR/repeated_branch.c")" -eq 1
if grep -Fq 'else if' "$TMP_DIR/repeated_branch.c"; then
  echo 'optimized extraction retained adjacent conditional arms with identical bodies' >&2
  exit 1
fi
awk '
  /^uint16_t repeated_call_branch\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/repeated_call_branch.c"
grep -Fq 'if (first || second)' "$TMP_DIR/repeated_call_branch.c"
test "$(grep -Fc 'add_byte(value, UINT8_C(1))' "$TMP_DIR/repeated_call_branch.c")" -eq 1
if grep -Fq 'else if' "$TMP_DIR/repeated_call_branch.c"; then
  echo 'optimized extraction retained duplicate calls in adjacent conditional arms' >&2
  exit 1
fi
grep -Fq 'uint8_t discard_internal_parameter(uint8_t value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'return discard_internal_parameter(value);' "$SPEC_SOURCE/base.c"
if grep -Fq 'discard_internal_parameter(UINT8_C(7), value)' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction retained a call operand for a dead internal parameter' >&2
  exit 1
fi
sed -n \
  '/^uint8_t call_discard_computed_parameter(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/call_discard_computed_parameter.c"
grep -Fq 'return discard_computed_parameter(value);' "$TMP_DIR/call_discard_computed_parameter.c"
if grep -Fq 'pure_parameter_value(' "$TMP_DIR/call_discard_computed_parameter.c"; then
  echo 'optimized extraction retained a pure producer for a discarded call operand' >&2
  exit 1
fi
grep -Fq 'uint8_t preserve_unused_parameter(uint8_t unused);' "$SPEC_INCLUDE/evmsail/spec/base.h"
sed -n \
  '/^uint8_t preserve_unused_parameter(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/preserve_unused_parameter.c"
grep -Fq '(void)unused;' "$TMP_DIR/preserve_unused_parameter.c"
if grep -REq '^[[:space:]]+unit [A-Za-z0-9_]+;' "$SPEC_SOURCE"; then
  echo 'optimized extraction retained a standalone unit payload temporary' >&2
  exit 1
fi
grep -Fq 'uint8_t sample_choice_value(struct sample_choice value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'struct byte_slice byte_slice_at(uint8_t off, uint8_t len);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'test_bytes_at((uint64_t)off)' "$SPEC_SOURCE/base.c"
grep -Fq 'struct analyzed_code {' "$SPEC_INCLUDE/evmsail/spec/base.h"
test "$(grep -Fc 'const uint8_t *' "$HOST_INCLUDE/types.h")" -ge 3
grep -Fq 'test_jumpdests_at((uint64_t)off)' "$SPEC_SOURCE/base.c"
grep -Eq 'uint8_t \* *jumpdest_from_offset\(uint8_t off\);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'extern uint8_t * const EMPTY_DIRECT_JUMP_TABLE;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Eq 'uint8_t \* const EMPTY_DIRECT_JUMP_TABLE = (NULL|INT64_C\(0\));' "$SPEC_SOURCE/base.c"
if grep -Rq 'let_end_[0-9]' "$SPEC_SOURCE"; then
  echo 'optimized extraction retained an untargeted top-level let label' >&2
  exit 1
fi
grep -Fq '_Noreturn void fatal_error(enum fatal_reason _reason);' \
  "$SPEC_INCLUDE/evmsail/spec/host_contracts.h"
test "$(grep -RhF '_Noreturn void fatal_error(enum fatal_reason _reason);' "$SPEC_INCLUDE/evmsail/spec" | wc -l | tr -d ' ')" -eq 1
if grep -Rq 'SAIL_TEST_' "$SPEC_SOURCE"; then
  echo 'optimized modular extraction emitted unused unit-test tables' >&2
  exit 1
fi
grep -Eq 'uint8_t \* *empty_direct_jumpdest\(void\);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'typedef uint64_t unit;' "$SPEC_INCLUDE/evmsail/spec/abi.h"
grep -Fq 'typedef struct { uint8_t bytes[4]; } bytes4;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'typedef struct { uint8_t bytes[20]; } test_bytes20;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'memcmp(op1.bytes, op2.bytes, 8) != 0' "$SPEC_INCLUDE/evmsail/spec/support.h"
grep -Fq 'memcmp(op1.bytes + 8, op2.bytes + 8, 8) != 0' "$SPEC_INCLUDE/evmsail/spec/support.h"
grep -Fq 'memcmp(op1.bytes + 16, op2.bytes + 16, 4) == 0' "$SPEC_INCLUDE/evmsail/spec/support.h"
grep -Fq '#include "evmsail/spec/abi.h"' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'static inline bool EQUAL(sample_choice)' "$SPEC_INCLUDE/evmsail/spec/support.h"
sed -n \
  '/^static inline bool EQUAL(sample_choice)/,/^static inline struct sample_choice /p' \
  "$SPEC_INCLUDE/evmsail/spec/support.h" > "$TMP_DIR/sample_choice_equal.c"
grep -Fq 'switch (op1.kind)' "$TMP_DIR/sample_choice_equal.c"
grep -Fq 'case Kind_InputChoice:' "$TMP_DIR/sample_choice_equal.c"
grep -Fq 'return (bool)(op1.variants.InputChoice == op2.variants.InputChoice);' \
  "$TMP_DIR/sample_choice_equal.c"
if grep -Fq 'break;' "$TMP_DIR/sample_choice_equal.c"; then
  echo 'optimized variant equality retained an unreachable break after return' >&2
  exit 1
fi
sed -n \
  '/^static inline bool EQUAL(erased_unit_choice)/,/^static inline struct erased_unit_choice /p' \
  "$SPEC_INCLUDE/evmsail/spec/support.h" > "$TMP_DIR/erased_unit_choice_equal.c"
grep -Fq 'case Kind_ByteChoice:' "$TMP_DIR/erased_unit_choice_equal.c"
grep -Fq 'return (bool)(op1.variants.ByteChoice == op2.variants.ByteChoice);' \
  "$TMP_DIR/erased_unit_choice_equal.c"
grep -Fq 'case Kind_EmptyChoice:' "$TMP_DIR/erased_unit_choice_equal.c"
grep -Fq 'case Kind_OtherEmptyChoice:' "$TMP_DIR/erased_unit_choice_equal.c"
test "$(grep -Fc 'return true;' "$TMP_DIR/erased_unit_choice_equal.c")" -eq 1
grep -Fq 'return false;' "$TMP_DIR/erased_unit_choice_equal.c"
grep -Fq \
  'return (bool)((op1.left == op2.left) && (op1.right == op2.right));' \
  "$SPEC_INCLUDE/evmsail/spec/support.h"
grep -Fq 'static inline struct sample_choice InputChoice' "$SPEC_INCLUDE/evmsail/spec/support.h"
grep -Fq 'static inline enum fatal_reason UNDEFINED(fatal_reason)(void)' "$SPEC_INCLUDE/evmsail/spec/support.h"
if grep -Eq 'UNDEFINED\([^)]*\)\(unit [A-Za-z_][A-Za-z0-9_]*\)' "$SPEC_INCLUDE/evmsail/spec/support.h"; then
  echo 'optimized extraction retained a unit argument on an undefined type helper' >&2
  exit 1
fi
if grep -Fq 'typedef uint64_t unit;' "$SPEC_INCLUDE/evmsail/spec/base.h"; then
  echo 'optimized module header duplicated the shared fixed ABI prelude' >&2
  exit 1
fi
if grep -Eq 'typedef .*wide_word;' "$SPEC_INCLUDE/evmsail/spec/base.h"; then
  echo 'optimized extraction leaked a semantic Sail alias into the concrete C ABI' >&2
  exit 1
fi
grep -Fq 'u256 wide_identity(u256 value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'u256 as_u256(u256 value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'struct tuple_u256_u256 {' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Eq 'struct tuple_u256_u256 wide_pair_identity\(u256 arg_0_[[:alnum:]_]+, u256 arg_1_[[:alnum:]_]+\);' \
  "$SPEC_INCLUDE/evmsail/spec/base.h"
if grep -REq 'proof_(identity|branch).*bounds' "$SPEC_INCLUDE/evmsail/spec" "$SPEC_SOURCE"; then
  echo 'optimized extraction leaked proof-bound hashes into represented specialization symbols' >&2
  exit 1
fi
test "$(grep -Ec '^uint8_t proof_identity\(' "$SPEC_SOURCE/base.c")" -eq 1
test "$(grep -Ec '^uint8_t proof_branch_uint8_t_to_uint8_t' "$SPEC_SOURCE/base.c")" -eq 2
grep -Fq 'proof_branch_uint8_t_to_uint8_t(' "$SPEC_SOURCE/base.c"
grep -Fq 'proof_branch_uint8_t_to_uint8_t_variant_2(' "$SPEC_SOURCE/base.c"
if grep -Eq 'if \((true|false)\)' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction retained a constant JIB branch' >&2
  exit 1
fi
if grep -Fq 'lt_int_result' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction retained an unread pure predicate temporary' >&2
  exit 1
fi
grep -Eq 'wide_pair_identity\(u256 arg_0_[[:alnum:]_]+, u256 arg_1_[[:alnum:]_]+\)' \
  "$SPEC_SOURCE/base.c"
awk '
  /^u256 wide_identity\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/wide_identity.c"
grep -Fq 'return value;' "$TMP_DIR/wide_identity.c"
if grep -Eq 'tmp_|end_function_' "$TMP_DIR/wide_identity.c"; then
  echo 'optimized extraction retained result-copy or dead-label scaffolding in an identity function' >&2
  exit 1
fi
awk '
  /^u256 widen_byte\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/widen_byte.c"
grep -Fq 'return u256_of_fbits(value);' "$TMP_DIR/widen_byte.c"
if grep -Eq 'result_|tmp_|u256 [A-Za-z0-9_]+ =' "$TMP_DIR/widen_byte.c"; then
  echo 'optimized extraction retained an immediate converted return temporary' >&2
  exit 1
fi
awk '
  /^u256 conditional_wide_return\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/conditional_wide_return.c"
grep -Eq 'return .* \? .* : .*;' "$TMP_DIR/conditional_wide_return.c"
if grep -Eq 'result_|tmp_|u256 [A-Za-z0-9_]+ =' "$TMP_DIR/conditional_wide_return.c"; then
  echo 'optimized extraction retained a scalar initialized only to be returned' >&2
  exit 1
fi
awk '
  /^uint8_t narrow_then_decrement\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/narrow_then_decrement.c"
grep -Eq 'uint8_t [A-Za-z0-9_]+ = \(uint8_t\).*distance.*UINT16_C\(1\).*;' \
  "$TMP_DIR/narrow_then_decrement.c"
if grep -Eq '^[[:space:]]+uint8_t [A-Za-z0-9_]+;$' "$TMP_DIR/narrow_then_decrement.c"; then
  echo 'optimized extraction retained an adjacent scalar declaration and assignment' >&2
  exit 1
fi
sed -n \
  '/^uint32_t widen_three_byte(/,/^}/p' \
  "$SPEC_SOURCE/base.c" > "$TMP_DIR/widen_three_byte.c"
grep -Fq 'return value;' "$TMP_DIR/widen_three_byte.c"
if grep -Eq '\(uint32_t\).*value' "$TMP_DIR/widen_three_byte.c"; then
  echo 'optimized extraction cast between semantic integer types with the same C carrier' >&2
  exit 1
fi
awk '
  /^uint8_t narrow_wide_byte\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/narrow_wide_byte.c"
# The optimized model defaults to unchecked narrowing, so the proved
# wide-to-native projection keeps its direct low-limb form.
grep -Fq '(uint8_t)u256_to_u64_unchecked(' "$TMP_DIR/narrow_wide_byte.c"
if grep -Eq '= u256_to_u64(_unchecked)?\(' "$TMP_DIR/narrow_wide_byte.c"; then
  echo 'optimized extraction retained an implicit wide-to-native integer narrowing' >&2
  exit 1
fi
awk '
  /^uint8_t narrow_word_remainder\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/narrow_word_remainder.c"
grep -Fq '% UINT32_C(9)' "$TMP_DIR/narrow_word_remainder.c"
if grep -Fq 'sail_native_conversion_failure' "$TMP_DIR/narrow_word_remainder.c"; then
  echo 'optimized extraction retained an impossible checked-conversion failure path' >&2
  exit 1
fi
awk '
  /^bool one_bit_is_set\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/one_bit_is_set.c"
grep -Fq 'UINT64_C(0x1)' "$TMP_DIR/one_bit_is_set.c"
if grep -Eq '0[bB][01]+' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction emitted a C23 binary integer literal' >&2
  exit 1
fi
awk '
  /^bool unsigned_le_signed\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/unsigned_le_signed.c"
grep -Fq '(int64_t)left <= (int64_t)right' "$TMP_DIR/unsigned_le_signed.c"
awk '
  /^bool signed_lt_unsigned\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/signed_lt_unsigned.c"
grep -Fq '(int64_t)left < (int64_t)right' "$TMP_DIR/signed_lt_unsigned.c"
awk '
  /^bool unsigned_eq_signed\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/unsigned_eq_signed.c"
grep -Fq '(int64_t)left == (int64_t)right' "$TMP_DIR/unsigned_eq_signed.c"
awk '
  /^bool guarded_blob_gas_add\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/guarded_blob_gas_add.c"
grep -Fq '(int64_t)transaction <= ((int64_t)(int32_t)' "$TMP_DIR/guarded_blob_gas_add.c"
if "$CC" -std=c11 -Wsign-compare -Werror -fsyntax-only \
    -I"$SPEC_INCLUDE" "$SPEC_SOURCE/base.c" >/dev/null 2>&1; then
  :
else
  echo 'optimized extraction retained a mixed-sign comparison diagnostic' >&2
  exit 1
fi
awk '
  /^u256 nested_wide_identity\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/nested_wide_identity.c"
grep -Fq '= wide_identity(value);' "$TMP_DIR/nested_wide_identity.c"
grep -Eq 'return (as_)?u256(_u256_to_u256)?\(' "$TMP_DIR/nested_wide_identity.c"
if grep -Eq '^[[:space:]]+u256 [[:alnum:]_]+;$|^[[:space:]]+\{$' "$TMP_DIR/nested_wide_identity.c"; then
  echo 'optimized extraction retained split declaration/call assignment or nested copy scope' >&2
  exit 1
fi
awk '
  /^uint8_t sample_choice_value\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/sample_choice_value.c"
grep -Fq 'switch (value.kind)' "$TMP_DIR/sample_choice_value.c"
grep -Fq 'case Kind_InputChoice:' "$TMP_DIR/sample_choice_value.c"
test "$(grep -Fc 'return value.variants.' "$TMP_DIR/sample_choice_value.c")" -eq 2
if grep -Eq 'goto |finish_match_|case_|tmp_' "$TMP_DIR/sample_choice_value.c"; then
  echo 'optimized extraction retained a flattened two-arm match result diamond' >&2
  exit 1
fi
awk '
  /^uint8_t \* empty_direct_jumpdest\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/empty_direct_jumpdest.c"
grep -Fq 'return EMPTY_DIRECT_JUMP_TABLE;' "$TMP_DIR/empty_direct_jumpdest.c"
if grep -Eq '__direct\)|__direct\(' "$SPEC_SOURCE/base.c"; then
  echo 'adapter-free byte pointer emitted a synthetic offset adapter call' >&2
  exit 1
fi
grep -Eq 'uint8_t \* *allocated_jumpdest\(uint8_t off\);' "$SPEC_INCLUDE/evmsail/spec/host_contracts.h"
grep -Fq 'test_jumpdest_alloc(off)' "$SPEC_SOURCE/host_contracts.c"
grep -Fq '= (value.bytes +' "$SPEC_SOURCE/base.c"
grep -Fq 'return (int16_t)(left.bytes - right.bytes);' "$SPEC_SOURCE/base.c"
if grep -Fq 'CONVERT_OF(mach_uint, byte_pointer_test_bytes_at)' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction converted a byte pointer back to its semantic integer offset' >&2
  exit 1
fi
if grep -REq 'struct pair[[:space:]]*\{' "$SPEC_INCLUDE/evmsail/spec"; then
  echo 'optimized extraction redefined an externally owned struct' >&2
  exit 1
fi
if grep -REq 'struct byte_slice[[:space:]]*\{' "$SPEC_INCLUDE/evmsail/spec"; then
  echo 'optimized extraction redefined the externally owned byte-pointer struct' >&2
  exit 1
fi
if grep -REq 'struct byte_slice_small[[:space:]]*\{' "$SPEC_INCLUDE/evmsail/spec"; then
  echo 'optimized extraction redefined the second externally owned byte-pointer struct' >&2
  exit 1
fi
grep -Fq 'uint8_t data[4]' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t catch_byte(uint8_t value);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint32_t host_mix_exact(uint32_t /* arg_0 */, uint8_t /* arg_1 */);' \
  "$SPEC_INCLUDE/evmsail/spec/host_contracts.h"
grep -Fq 'void host_reset_exact(void);' "$SPEC_INCLUDE/evmsail/spec/host_contracts.h"
awk '
  /^uint32_t reset_then_mix\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/reset_then_mix.c"
grep -Fq 'host_reset_exact();' "$TMP_DIR/reset_then_mix.c"
grep -Fq 'return host_mix_exact(value, tag);' "$TMP_DIR/reset_then_mix.c"
if grep -Eq '\bUNIT\b|\bunit\b|tmp_|end_function_' "$TMP_DIR/reset_then_mix.c"; then
  echo 'optimized extraction retained unit ABI or result scaffolding around a unit extern' >&2
  exit 1
fi
awk '
  /^uint32_t guarded_host_mix\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/guarded_host_mix.c"
grep -Fq 'if (off < len)' "$TMP_DIR/guarded_host_mix.c"
grep -Fq 'return host_mix_exact(value, tag);' "$TMP_DIR/guarded_host_mix.c"
grep -Fq 'return UINT32_C(0);' "$TMP_DIR/guarded_host_mix.c"
if grep -Eq 'result_|tmp_|end_function_' "$TMP_DIR/guarded_host_mix.c"; then
  echo 'optimized extraction retained join-result scaffolding in a conditional return' >&2
  exit 1
fi
awk '
  /^uint32_t guarded_host_slice\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/guarded_host_slice.c"
grep -Fq 'if (off < segment.len)' "$TMP_DIR/guarded_host_slice.c"
grep -Fq 'return host_mix_exact(value, tag);' "$TMP_DIR/guarded_host_slice.c"
grep -Fq 'return UINT32_C(0);' "$TMP_DIR/guarded_host_slice.c"
if grep -Eq 'result_|tmp_|end_function_' "$TMP_DIR/guarded_host_slice.c"; then
  echo 'optimized extraction retained predicate or block scaffolding in a field-guarded return' >&2
  exit 1
fi
awk '
  /^uint32_t guarded_wide_offset\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/guarded_wide_offset.c"
grep -Eq 'if \(u256_lt_u64\(off, UINT[0-9]+_C\(256\)\)\)' "$TMP_DIR/guarded_wide_offset.c"
# The guarded projection reaches the host call directly, either through the
# source-named temporary or as the inlined proved low-limb projection.
grep -Eq 'return host_mix_exact\(value, (tag|\(uint8_t\)u256_to_u64(_unchecked)?\(off\))\);' \
  "$TMP_DIR/guarded_wide_offset.c"

awk '
  /^uint8_t masked_high_nibble\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { exit }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/masked_high_nibble.c"
grep -Fq 'UINT64_C(0xF) &' "$TMP_DIR/masked_high_nibble.c"
if grep -Fq 'sail_native_conversion_failure' "$TMP_DIR/masked_high_nibble.c"; then
  echo "bounded bit-mask conversion retained an impossible range check" >&2
  exit 1
fi
grep -Fq 'return UINT32_C(0);' "$TMP_DIR/guarded_wide_offset.c"
if grep -Eq 'result_|end_function_' "$TMP_DIR/guarded_wide_offset.c"; then
  echo 'optimized extraction retained a join result around a branch-local conversion' >&2
  exit 1
fi
if grep -Eq '^[[:space:]]{4}\{$' "$TMP_DIR/guarded_wide_offset.c"; then
  echo 'optimized extraction retained a redundant singleton block inside a conditional arm' >&2
  exit 1
fi
awk '
  /^bool widened_host_call\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/widened_host_call.c"
grep -Fq 'return host_wide_pair_exact((uint32_t)small, (uint32_t)medium);' \
  "$TMP_DIR/widened_host_call.c"
if grep -Eq 'result_|tmp_|end_function_' "$TMP_DIR/widened_host_call.c"; then
  echo 'optimized extraction retained assignment-conversion temporaries around a call' >&2
  exit 1
fi
grep -Fq 'extern uint32_t public_counter;' "$SPEC_INCLUDE/evmsail/spec/machine.h"
grep -Fq 'uint32_t public_counter' "$SPEC_SOURCE/machine.c"
grep -Fq 'void reset_counter(void);' "$SPEC_INCLUDE/evmsail/spec/machine.h"
awk '
  /^bool conditional_word\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/machine.c" > "$TMP_DIR/conditional_word.c"
grep -Eq 'uint32_t [A-Za-z0-9_]+ = flag \? left : right;' "$TMP_DIR/conditional_word.c"
if grep -Eq '} else \{|^[[:space:]]+uint32_t [A-Za-z0-9_]+;$' "$TMP_DIR/conditional_word.c"; then
  echo 'optimized extraction did not recover a pure conditional value initializer' >&2
  exit 1
fi
awk '
  /^bool conditional_bool\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/machine.c" > "$TMP_DIR/conditional_bool.c"
grep -Fq 'return (bool)(flag || fallback);' "$TMP_DIR/conditional_bool.c"
if grep -Fq '?' "$TMP_DIR/conditional_bool.c"; then
  echo 'optimized extraction retained a ternary for a simple boolean selection' >&2
  exit 1
fi
awk '
  /^bool conditional_bool_false\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/machine.c" > "$TMP_DIR/conditional_bool_false.c"
grep -Fq 'return (bool)(flag && fallback);' "$TMP_DIR/conditional_bool_false.c"
if grep -Eq '\?|!\(flag\)|!\(fallback\)' "$TMP_DIR/conditional_bool_false.c"; then
  echo 'optimized extraction retained a ternary or redundant boolean parentheses for a false selection' >&2
  exit 1
fi
awk '
  /^void reset_counter\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/machine.c" > "$TMP_DIR/reset_counter.c"
grep -Fq 'public_counter = UINT32_C(0);' "$TMP_DIR/reset_counter.c"
if grep -Fq 'return;' "$TMP_DIR/reset_counter.c"; then
  echo 'optimized extraction retained a redundant terminal return in a void function' >&2
  exit 1
fi
awk '
  /^void reset_via_host\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/reset_via_host.c"
grep -Fq 'host_reset_exact();' "$TMP_DIR/reset_via_host.c"
if grep -Fq 'return;' "$TMP_DIR/reset_via_host.c"; then
  echo 'optimized extraction retained a redundant return after a terminal unit call' >&2
  exit 1
fi
awk '
  /^void guarded_reset\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/guarded_reset.c"
grep -Fq 'if (enabled)' "$TMP_DIR/guarded_reset.c"
grep -Fq 'host_reset_exact();' "$TMP_DIR/guarded_reset.c"
if grep -Eq 'goto |cleanup_|end_function_|} else {' "$TMP_DIR/guarded_reset.c"; then
  echo 'optimized extraction retained control-flow scaffolding around a conditional unit action' >&2
  exit 1
fi
awk '
  /^void reset_when_pair\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/host_contracts.c" > "$TMP_DIR/reset_when_pair.c"
grep -Fq 'if (host_wide_pair_result_' "$TMP_DIR/reset_when_pair.c"
grep -Fq 'host_reset_exact();' "$TMP_DIR/reset_when_pair.c"
if grep -Eq 'bool result_' "$TMP_DIR/reset_when_pair.c"; then
  echo 'optimized extraction retained single-use boolean guard temporaries across a host call' >&2
  exit 1
fi
awk '
  /^uint32_t preserve_counter_snapshot\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/machine.c" > "$TMP_DIR/preserve_counter_snapshot.c"
grep -Eq 'uint32_t [A-Za-z0-9_]+ = public_counter;' "$TMP_DIR/preserve_counter_snapshot.c"
grep -Fq 'reset_counter();' "$TMP_DIR/preserve_counter_snapshot.c"
if grep -Fq 'return public_counter;' "$TMP_DIR/preserve_counter_snapshot.c"; then
  echo 'optimized extraction moved a register snapshot across a mutating call' >&2
  exit 1
fi
awk '
  /^uint8_t save_pair_then_read\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/machine.c" > "$TMP_DIR/save_pair_then_read.c"
grep -Eq 'struct pair [A-Za-z0-9_]+ = make_public_pair\(value\);' \
  "$TMP_DIR/save_pair_then_read.c"
grep -Eq 'public_pair = [A-Za-z0-9_]+;' "$TMP_DIR/save_pair_then_read.c"
grep -Eq 'return [A-Za-z0-9_]+\.second;' "$TMP_DIR/save_pair_then_read.c"
sed -n \
  '/^bool initialized_comparison_return(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/initialized_comparison_return.c"
grep -Fq 'return (bool)(snapshot.first >= UINT8_C(1));' \
  "$TMP_DIR/initialized_comparison_return.c"
if grep -Eq 'bool [A-Za-z0-9_]+ = .*;' "$TMP_DIR/initialized_comparison_return.c"; then
  echo 'optimized extraction retained an initialized scalar used only by the immediate return' >&2
  exit 1
fi
sed -n \
  '/^bool specialized_comparison(void)/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/specialized_comparison.c"
grep -Fq 'return (bool)(snapshot.first >= UINT8_C(1));' \
  "$TMP_DIR/specialized_comparison.c"
if grep -Eq 'bool [A-Za-z0-9_]+ = .*;' "$TMP_DIR/specialized_comparison.c"; then
  echo 'optimized extraction retained a specialized scalar used only by the immediate return' >&2
  exit 1
fi
sed -n \
  '/^bool specialized_enum_comparison(/,/^}/p' \
  "$SPEC_SOURCE/machine.c" > "$TMP_DIR/specialized_enum_comparison.c"
grep -Fq 'return (bool)(execution_profile.protocol.fork >= TestAfter);' \
  "$TMP_DIR/specialized_enum_comparison.c"
if grep -Eq 'bool [A-Za-z0-9_]+ = .*;' "$TMP_DIR/specialized_enum_comparison.c"; then
  echo 'optimized extraction retained a specialized enum comparison temporary' >&2
  exit 1
fi
grep -Fq 'void evmsail_model_init(void);' "$SPEC_INCLUDE/evmsail/spec/entry.h"
grep -Fq 'void zmain(void);' "$SPEC_INCLUDE/evmsail/spec/entry.h"
if grep -Eq '\bunit (z?main)\(unit\)' "$SPEC_INCLUDE/evmsail/spec/entry.h"; then
  echo 'optimized extraction retained unit in the guest ABI' >&2
  exit 1
fi
grep -Fq '__builtin_trap()' "$SPEC_SOURCE/entry.c"
grep -Fq 'run_uint8_t_to_uint32_t(UINT8_C(1));' "$SPEC_SOURCE/entry.c"
if grep -Fq 'run_result' "$SPEC_SOURCE/entry.c"; then
  echo 'optimized extraction retained an unread effectful call result' >&2
  exit 1
fi
awk '
  /^uint32_t run\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/entry.c" > "$TMP_DIR/run.c"
if grep -Eq '^[[:space:]]*unit tmp_[[:alnum:]_]*;' "$TMP_DIR/run.c"; then
  echo 'optimized extraction retained an unread unit result temporary' >&2
  exit 1
fi
if grep -REq '\bUNIT\b|^[[:space:]]*unit [[:alnum:]_]+' "$SPEC_SOURCE/entry.c"; then
  echo 'optimized extraction retained a standalone unit value in generated entry code' >&2
  exit 1
fi
if grep -REq '\bz[[:digit:]]+zE[[:digit:]]+\b' "$SPEC_INCLUDE/evmsail" "$SPEC_SOURCE"; then
  echo 'no-mangle optimized extraction retained a z-encoded generated local' >&2
  exit 1
fi
if grep -Fq 'run requires a nonzero byte' "$SPEC_SOURCE/entry.c"; then
  echo 'strict optimized model retained a managed Sail assertion string' >&2
  exit 1
fi

if grep -REq 'sail_int|mpz_|sail_new|sail_free|CREATE\(|COPY\(|RECREATE\(|KILL\(' \
    "$SPEC_INCLUDE/evmsail" "$SPEC_SOURCE"; then
  echo 'strict optimized model contains a managed Sail representation or ownership helper' >&2
  exit 1
fi

# The fixed_index source type proves every access lies inside the 17-element
# POD array.  Preserve that proof through JIB and emit the C member access
# directly instead of routing through a generated vector helper.
awk '
  /^(uint16_t )?pick_(fixed|initialized|guarded)_id\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/proved_fixed_vector_accesses.c"
test "$(grep -Fc '.data[(size_t)index]' "$TMP_DIR/proved_fixed_vector_accesses.c")" -eq 3
if grep -Eq '(fast_)?(unsigned_)?vector_access_' "$TMP_DIR/proved_fixed_vector_accesses.c"; then
  echo 'proved fixed-vector access retained an out-of-line helper call' >&2
  exit 1
fi

# Module-specific helpers remain beside the code that selects them, while
# globally shared type support is emitted once in support.h and included by
# every generated translation unit.
grep -Fq 'internal_vector_init_vector_17_uint_16' "$SPEC_SOURCE/base.c"
grep -Fq 'internal_vector_update_vector_17_uint_16' "$SPEC_SOURCE/base.c"
grep -Fq 'internal_vector_init_vector_4_uint_8' "$SPEC_SOURCE/machine.c"
grep -Fq 'internal_vector_update_vector_4_uint_8' "$SPEC_SOURCE/machine.c"
grep -Fq 'EQUAL(vector_17_uint_16)' "$SPEC_INCLUDE/evmsail/spec/support.h"
for module in base host_contracts machine entry; do
  if test "$(grep -Fc '#include "evmsail/spec/support.h"' "$SPEC_SOURCE/$module.c")" -ne 1; then
    echo "module $module does not include the generated shared support header exactly once" >&2
    exit 1
  fi
  if grep -Fq 'EQUAL(vector_17_uint_16)' "$SPEC_SOURCE/$module.c"; then
    echo "module $module duplicated a helper owned by the generated shared support header" >&2
    exit 1
  fi
done

for source in "$SPEC_SOURCE"/*.c; do
  "$CC" ${CFLAGS:-} -std=c11 -Wall -Werror=implicit-function-declaration -Werror=unused-label \
    -Werror=uninitialized \
    -I "$SPEC_INCLUDE" -c "$source" -o "$TMP_DIR/$(basename "$source" .c).o"
done

"$CC" ${CFLAGS:-} -std=c11 -Wall -I "$SPEC_INCLUDE" \
  "$TEST_DIR/host_stub.c" "$TEST_DIR/harness.c" "$TMP_DIR"/*.o \
  -o "$TMP_DIR/optimized-model-test"
"$TMP_DIR/optimized-model-test"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/negative/ffi/optimized" \
    --c-preserve bad "$TEST_DIR/negative.sail_project" \
    >"$TMP_DIR/negative.stdout" 2>"$TMP_DIR/negative.stderr"; then
  echo 'strict optimized model unexpectedly accepted an unbounded integer' >&2
  exit 1
fi

grep -Eqi 'bounded|unbounded|fixed representation|optimized model' "$TMP_DIR/negative.stderr"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/missing-header/ffi/optimized" \
    --c-optimized-include-dir "$TMP_DIR/ffi/optimized/include" \
    --c-optimized-external-type pair=evmsail/host/missing.h \
    --c-preserve-type pair "$TEST_DIR/model.sail_project" \
    >"$TMP_DIR/missing-header.stdout" 2>"$TMP_DIR/missing-header.stderr"; then
  echo 'optimized extraction unexpectedly accepted a missing external type header' >&2
  exit 1
fi

grep -Fqi 'does not exist' "$TMP_DIR/missing-header.stderr"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/missing-type/ffi/optimized" \
    --c-optimized-include-dir "$TMP_DIR/ffi/optimized/include" \
    --c-optimized-external-type canonical_slice=evmsail/host/types.h \
    --c-optimized-external-type canonical_list=evmsail/host/types.h \
    --c-optimized-external-type missing_type=evmsail/host/types.h \
    "$TEST_DIR/model.sail_project" \
    >"$TMP_DIR/missing-type.stdout" 2>"$TMP_DIR/missing-type.stderr"; then
  echo 'optimized extraction unexpectedly accepted an unknown external type' >&2
  exit 1
fi

grep -Fqi 'does not name a concrete type' "$TMP_DIR/missing-type.stderr"

# Output stems follow Sail module names, not source basenames.  Both source
# basenames deliberately differ from their project module names.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail \
  --c-output-dir "$TMP_DIR/filename/ffi/optimized" \
  --c-preserve from_first_filename --c-preserve from_second_filename \
  "$TEST_DIR/filename.sail_project"

FILENAME_INCLUDE="$TMP_DIR/filename/ffi/optimized/include/evmsail"
FILENAME_SOURCE="$TMP_DIR/filename/ffi/optimized/src/spec"

for module in first_filename_output second_filename_output; do
  test -f "$FILENAME_INCLUDE/spec/$module.h"
  test -f "$FILENAME_SOURCE/$module.c"
  test "$(grep -Fc "#include \"evmsail/spec/$module.h\"" "$FILENAME_INCLUDE/spec.h")" -eq 1
done
test ! -e "$FILENAME_INCLUDE/spec/first_source.h"
test ! -e "$FILENAME_SOURCE/first_source.c"
test ! -e "$FILENAME_INCLUDE/spec/second_source.h"
test ! -e "$FILENAME_SOURCE/second_source.c"
grep -Fq 'from_first_filename' "$FILENAME_INCLUDE/spec/first_filename_output.h"
grep -Fq 'from_first_filename' "$FILENAME_SOURCE/first_filename_output.c"
grep -Fq 'from_second_filename' "$FILENAME_INCLUDE/spec/second_filename_output.h"
grep -Fq 'from_second_filename' "$FILENAME_SOURCE/second_filename_output.c"
if grep -Fq 'from_second_filename' "$FILENAME_INCLUDE/spec/first_filename_output.h" \
    || grep -Fq 'from_second_filename' "$FILENAME_SOURCE/first_filename_output.c" \
    || grep -Fq 'from_first_filename' "$FILENAME_INCLUDE/spec/second_filename_output.h" \
    || grep -Fq 'from_first_filename' "$FILENAME_SOURCE/second_filename_output.c"; then
  echo 'optimized extraction assigned a definition to the wrong project module' >&2
  exit 1
fi

# Source-tree output preserves the source layout without changing the
# project's semantic module structure. The manifest is the authoritative,
# ordered compilation input for nested generated translation units.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail \
  --c-output-dir "$TMP_DIR/source-tree/ffi/optimized" \
  --c-optimized-source-root "$TEST_DIR" \
  --c-preserve from_first_filename --c-preserve from_second_filename \
  "$TEST_DIR/source_tree.sail_project"

SOURCE_TREE_INCLUDE="$TMP_DIR/source-tree/ffi/optimized/include/evmsail"
SOURCE_TREE_SOURCE="$TMP_DIR/source-tree/ffi/optimized/src/spec"

for source in filename_first/first_source filename_second/second_source; do
  test -f "$SOURCE_TREE_INCLUDE/spec/$source.h"
  test -f "$SOURCE_TREE_SOURCE/$source.c"
  test "$(grep -Fc "#include \"evmsail/spec/$source.h\"" "$SOURCE_TREE_INCLUDE/spec.h")" -eq 1
done
test ! -e "$SOURCE_TREE_INCLUDE/spec/source_tree.h"
test ! -e "$SOURCE_TREE_SOURCE/source_tree.c"
grep -Fq '#include "evmsail/spec/filename_first/first_source.h"' \
  "$SOURCE_TREE_INCLUDE/spec/filename_second/second_source.h"
grep -Fq 'from_first_filename' "$SOURCE_TREE_SOURCE/filename_first/first_source.c"
grep -Fq 'from_second_filename' "$SOURCE_TREE_SOURCE/filename_second/second_source.c"
printf '%s\n' filename_first/first_source.c filename_second/second_source.c \
  > "$TMP_DIR/source-tree-expected.list"
cmp "$TMP_DIR/source-tree-expected.list" "$SOURCE_TREE_SOURCE/sources.list"

# Regeneration replaces the previous manifest-owned output set. This keeps a
# switch from module output to source-tree output from leaving an obsolete
# monolithic translation unit visible beside the new package.
touch "$SOURCE_TREE_SOURCE/obsolete.c" "$SOURCE_TREE_INCLUDE/spec/obsolete.h"
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail \
  --c-output-dir "$TMP_DIR/source-tree/ffi/optimized" \
  --c-optimized-source-root "$TEST_DIR" \
  --c-preserve from_first_filename --c-preserve from_second_filename \
  "$TEST_DIR/source_tree.sail_project"
test ! -e "$SOURCE_TREE_SOURCE/obsolete.c"
test ! -e "$SOURCE_TREE_INCLUDE/spec/obsolete.h"
cmp "$TMP_DIR/source-tree-expected.list" "$SOURCE_TREE_SOURCE/sources.list"

while IFS= read -r source; do
  object=$(printf '%s' "$source" | tr '/' '_')
  "$CC" ${CFLAGS:-} -std=c11 -Wall -I "$TMP_DIR/source-tree/ffi/optimized/include" \
    -c "$SOURCE_TREE_SOURCE/$source" -o "$TMP_DIR/$object.o"
done < "$SOURCE_TREE_SOURCE/sources.list"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/collision/ffi/optimized" \
    "$TEST_DIR/collision.sail_project" \
    >"$TMP_DIR/collision.stdout" 2>"$TMP_DIR/collision.stderr"; then
  echo 'optimized extraction unexpectedly accepted colliding module file stems' >&2
  exit 1
fi

grep -Fq 'FooBar' "$TMP_DIR/collision.stderr"
grep -Fq 'Foo_bar' "$TMP_DIR/collision.stderr"
grep -Fq "file stem 'foo_bar'" "$TMP_DIR/collision.stderr"
test ! -e "$TMP_DIR/collision/ffi/optimized/include/evmsail/spec.h"
test ! -e "$TMP_DIR/collision/ffi/optimized/include/evmsail/spec/foo_bar.h"
test ! -e "$TMP_DIR/collision/ffi/optimized/src/spec/foo_bar.c"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/state-passing-discard/ffi/optimized" \
    --c-preserve-type state_passing_status \
    --c-preserve update_state --c-preserve discard_updated_state \
    "$TEST_DIR/state_passing_discard.sail_project" \
    >"$TMP_DIR/state-passing-discard.stdout" 2>"$TMP_DIR/state-passing-discard.stderr"; then
  echo 'optimized extraction unexpectedly accepted a discarded state result' >&2
  exit 1
fi

grep -Fq 'call to optimized state-passing function update_state discards returned state field 0' \
  "$TMP_DIR/state-passing-discard.stderr"

if ! "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/state-passing-invalid/ffi/optimized" \
    --c-preserve-type invalid_state_status \
    --c-preserve invalid_state_order --c-preserve state_last_product \
    "$TEST_DIR/state_passing_invalid.sail_project" \
    >"$TMP_DIR/state-passing-invalid.stdout" 2>"$TMP_DIR/state-passing-invalid.stderr"; then
  echo 'optimized extraction rejected an ordinary non-mirroring tuple result' >&2
  exit 1
fi

grep -Eq 'struct tuple_bool_uint_8_invalid_state_status invalid_state_order\(uint8_t state_word, bool state_flag\);' \
  "$TMP_DIR/state-passing-invalid/ffi/optimized/include/evmsail/spec/state_passing_invalid.h"
grep -Fq 'struct tuple_bool_uint_8 state_last_product(uint8_t state_word);' \
  "$TMP_DIR/state-passing-invalid/ffi/optimized/include/evmsail/spec/state_passing_invalid.h"
