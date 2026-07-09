$include <prelude.sail>

val call_foo : unit -> unit

function call_foo() = foo()

$[c: "c_ext"]
val external_foo : unit -> unit

function external_foo() = ()

enum LocalChoice = ChoiceAlpha | ChoiceBeta

enum OtherChoice = ChoiceOther

struct LocalRecord = {
  record_field : int,
  other_field : bool,
}

struct OtherRecord = {
  record_other : int,
}

struct WrapperRecord = {
  inner_record : LocalRecord,
  indexed_records : vector(2, dec, LocalRecord),
}

val make_local_record : unit -> LocalRecord

val make_wrapper_record : unit -> WrapperRecord

val make_local_records : unit -> vector(2, dec, LocalRecord)

union LocalUnion = {
  UnionAlpha : int,
  UnionBeta : bool,
}

union OtherUnion = {
  UnionOther : int,
}

val use_params : int -> int -> int

function use_params(param_alpha : int, param_beta : int) -> int = {
  param_alpha
}

val use_pattern_binders : unit -> int

function use_pattern_binders() -> int = {
  let (pattern_alpha, pattern_beta) = (1, 2);
  pattern_alpha + pattern_beta
}

val use_struct_pattern_binders : LocalRecord -> int

function use_struct_pattern_binders(r : LocalRecord) -> int = {
  let struct { record_field = struct_pattern_value, other_field = _ } : LocalRecord = r;
  let record_probe = struct_pattern_value;
  let other_probe = record_probe;
  other_probe + struct_pattern_value
}

val use_var_binder : unit -> int

function use_var_binder() -> int = {
  var mutable_alpha : int = 1;
  mutable_alpha
}

val use_match_binder : LocalUnion -> int

function use_match_binder(u : LocalUnion) -> int = {
  match u {
    UnionAlpha(match_payload) => {
      match_payload
    },
    UnionAlpha(guard_payload) if guard_payload > 0 => guard_payload,
    _ => 0,
  }
}

val use_as_match_binder : LocalUnion -> int

function use_as_match_binder(u : LocalUnion) -> int = {
  match u {
    UnionAlpha(_) as alias_payload => {
      alias_payload
    },
    _ => 0,
  }
}

val use_list_cons_match_binder : list(int) -> int

function use_list_cons_match_binder(xs : list(int)) -> int = {
  match xs {
    list_head_payload :: list_tail_payload => {
      let list_tail_probe = list_tail_payload;
      list_head_payload + list_tail_probe
    },
    [||] => 0,
  }
}

val use_inline_match_binder : LocalUnion -> int

function use_inline_match_binder(u : LocalUnion) -> int = {
  let inline_result : int = match u { UnionAlpha(inline_payload) if inline_payload > 0 => inline_payload, _ => 0 };
  inline_result
}

val use_multiline_match_binder : LocalUnion -> int

function use_multiline_match_binder(u : LocalUnion) -> int = {
  let multiline_result : int =
    match u {
      UnionAlpha(
        multiline_payload
      )
        if multiline_payload > 0
        => {
          let nested_payload_result : int = multiline_payload + 1;
          nested_payload_result
        },
      UnionBeta(_) => 0,
    };
  multiline_result
}

val use_loop_binder : unit -> int

function use_loop_binder() -> int = {
  var loop_acc = 0;
  foreach (loop_index from 0 to 3) {
    loop_acc = loop_acc + loop_index
  };
  loop_acc
}

val use_multiline_loop_binder : unit -> int

function use_multiline_loop_binder() -> int = {
  var multiline_loop_acc = 0;
  foreach (multiline_loop_index
    from 0
    to 3
    by 1
    in inc) {
    multiline_loop_acc = multiline_loop_acc + multiline_loop_index
  };
  multiline_loop_acc
}

val use_unbraced_loop_binder : unit -> int

function use_unbraced_loop_binder() -> int = {
  var unbraced_loop_acc = 0;
  foreach (unbraced_loop_index from 0 to 3)
    unbraced_loop_acc = unbraced_loop_acc + unbraced_loop_index;
  unbraced_loop_acc
}

union MappingUnion = {
  MappingI : int,
  MappingJ : int,
  MappingK : int,
}

val mapping_binder : MappingUnion <-> int

mapping mapping_binder : MappingUnion <-> int = {
  MappingI(mapping_payload) <-> mapping_payload,
  MappingJ(mapping_guard_payload) if mapping_guard_payload > 0 <-> mapping_guard_payload,
  MappingK(mapping_no_leak_payload) <-> mapping_no_leak_payload,
}

function mapping_after_binder() = 0

val clause_mapping_binder : MappingUnion <-> int

scattered mapping clause_mapping_binder

mapping clause clause_mapping_binder = MappingI(clause_payload) <-> clause_payload

function clause_after_mapping() = 0

val use_function_pattern_binders : LocalUnion -> int

function use_function_pattern_binders(UnionAlpha(function_clause_payload)) -> int = {
  function_clause_payload
}

val use_tuple_function_pattern_binders : ((int, int)) -> int

function use_tuple_function_pattern_binders((fn_tuple_left, fn_tuple_right)) -> int = {
  fn_tuple_left + fn_tuple_right
}

val use_subrange_pattern_binder : bits(20) -> int

function use_subrange_pattern_binder subrange_payload[19] @ subrange_payload[9..0] @ subrange_payload[10] @ subrange_payload[18..11] = {
  unsigned(subrange_payload)
}

val scattered_pattern : LocalUnion -> int

scattered function scattered_pattern

function clause scattered_pattern(UnionAlpha(scattered_payload)) = {
  scattered_payload
}

end scattered_pattern

function function_clause_after_pattern() = 0

function use_choice() = ChoiceAlpha

function use_union() = UnionAlpha(1)

function use_expected_choice() -> LocalChoice = ChoiceAlpha

function use_expected_union() -> LocalUnion = UnionAlpha(1)

function use_expected_let() -> LocalChoice = {
  let selected_choice : LocalChoice = ChoiceAlpha;
  selected_choice
}

function use_fields(r : LocalRecord) -> int = r.record_field

function use_local_fields(r : LocalRecord) -> int = {
  let local_record : LocalRecord = r;
  local_record.record_field
}

function use_nested_fields(w : WrapperRecord) -> int = w.inner_record.record_field

function use_local_nested_fields(w : WrapperRecord) -> int = {
  let local_wrapper : WrapperRecord = w;
  local_wrapper.inner_record.record_field
}

function use_call_receiver_fields() -> int = make_local_record().record_field

function use_call_receiver_nested_fields() -> int = make_wrapper_record().inner_record.record_field

function use_indexed_local_fields(r : LocalRecord) -> int = {
  let local_records : vector(2, dec, LocalRecord) = [|r, r|];
  local_records[0].record_field
}

function use_indexed_nested_fields(w : WrapperRecord) -> int = w.indexed_records[0].record_field

function use_indexed_call_receiver_fields() -> int = make_local_records()[0].record_field

function use_parenthesized_field(r : LocalRecord) -> int = (r).record_field

function use_parenthesized_nested_field(w : WrapperRecord) -> int = (w.inner_record).record_field

function use_parenthesized_call_receiver_fields() -> int = (make_local_record()).record_field

function use_parenthesized_indexed_receiver_fields(r : LocalRecord) -> int = {
  let local_records : vector(2, dec, LocalRecord) = [|r, r|];
  (local_records[0]).record_field
}

function use_parenthesized_outer_index_receiver_fields(r : LocalRecord) -> int = {
  let local_records : vector(2, dec, LocalRecord) = [|r, r|];
  (local_records)[0].record_field
}

function use_conditional_field(flag : bool, left : LocalRecord, right : LocalRecord) -> int =
  (if flag then left else right).record_field

function use_conditional_nested_field(flag : bool, w : WrapperRecord, right : LocalRecord) -> int =
  (if flag then w.inner_record else right).record_field

function use_conditional_call_receiver_fields(flag : bool, right : LocalRecord) -> int =
  (if flag then make_local_record() else right).record_field

function use_conditional_indexed_receiver_fields(flag : bool, r : LocalRecord, right : LocalRecord) -> int = {
  let local_records : vector(2, dec, LocalRecord) = [|r, r|];
  (if flag then local_records[0] else right).record_field
}
