register public_counter : word
register public_pair : pair
register startup_public_pair : startup_pair = struct { first = 0, second = 0 }

type test_fork = range(0, 1)

let TestBefore : int(0) = 0
let TestAfter : int(1) = 1

struct test_protocol = {
  fork : test_fork,
}

struct test_execution_profile = {
  protocol : test_protocol,
}

register public_execution_profile : test_execution_profile

function reset_counter() -> unit = public_counter = 0

function preserve_counter_snapshot(value : word) -> word = {
  if value != 0 then public_counter = value;
  let snapshot = public_counter;
  reset_counter();
  snapshot
}

function make_public_pair(value : byte) -> pair =
  struct { first = value, second = value }

function initialize_public_pair(value : byte) -> unit =
  public_pair = struct { first = value, second = value }

function startup_pair_first() -> byte = startup_public_pair.first

val terminal_proven_narrow_sum : forall 'start 'size,
  0 <= 'start & 'start < 2 ^ 256 & 0 <= 'size & 'size < 2 ^ 256.
  (int('start), int('size)) -> word_endpoint
function terminal_proven_narrow_sum(start, size) = {
  if size == 0 then 0
  else if start <= 4294967295 then {
    let (bounded_start as 'bounded_start) :
      {'bounded_start, 'bounded_start == 'start & 0 <= 'bounded_start & 'bounded_start <= 4294967295.
       int('bounded_start)} = start;
    if size <= 4294967295 - bounded_start then {
      let (bounded_size as 'bounded_size) :
        {'bounded_size,
         'bounded_size == 'size & 0 < 'bounded_size & 'bounded_size <= 4294967295 - 'bounded_start.
         int('bounded_size)} = size;
      let endpoint : word_endpoint = bounded_start + bounded_size;
      endpoint
    } else 4294967296
  } else 4294967296
}

function pair_field_value(value : byte) -> byte = value

function call_result_in_struct(value : byte) -> pair =
  struct { first = pair_field_value(value), second = value }

function consume_field_value(value : byte) -> byte = value

function call_result_as_argument(value : byte) -> byte =
  consume_field_value(pair_field_value(value))

function consume_second_field_value(first : byte, second : byte) -> range(0, 510) = first + second

function call_result_as_later_argument(value : byte) -> range(0, 510) =
  consume_second_field_value(value, pair_field_value(value))

function consume_wide_field_value(value : range(0, 256)) -> range(0, 256) = value

function call_result_through_expression(value : byte) -> range(0, 256) =
  consume_wide_field_value(pair_field_value(value) + 1)

function pure_extern_result_through_expression(value : byte) -> range(0, 256) =
  consume_wide_field_value(host_pure_byte_exact(value) + 1)

function pure_call_after_register_write(value : byte) -> byte = {
  let selected = pair_field_value(value);
  public_counter = 0;
  selected
}

function save_pair_then_read(value : byte) -> byte = {
  let next = make_public_pair(value);
  public_pair = next;
  next.second
}

function initialized_comparison_return() -> bool = {
  let snapshot = public_pair;
  let active = snapshot.first >= 1;
  active
}

val specialized_comparison : forall 'n, 0 <= 'n & 'n <= 256. int('n) -> bool
function specialized_comparison(n) = {
  let snapshot = public_pair;
  let base = n <= 4;
  let final = (n == 256) & (snapshot.first >= 1);
  base | final
}

function call_specialized_comparison() -> bool = specialized_comparison(256)

val specialized_enum_comparison : forall 'n, 0 <= 'n & 'n <= 256. int('n) -> bool
function specialized_enum_comparison(n) = {
  let execution_profile = public_execution_profile;
  let base0 = n <= 2;
  let base1 = n <= 3;
  let base2 = n <= 4;
  let final = (n == 256) & (execution_profile.protocol.fork >= TestAfter);
  base0 | base1 | base2 | final
}

function call_specialized_enum_comparison() -> bool = specialized_enum_comparison(256)

function conditional_word(flag : bool, left : word, right : word) -> bool = {
  let selected : word = if flag then left else right;
  selected == public_counter
}

function widened_branch_join(flag : bool, left : byte, right : byte) -> word = {
  let selected : word = if flag then left else right;
  public_counter = selected;
  selected
}

function conditional_bool(flag : bool, fallback : bool) -> bool = {
  let selected = if flag then true else fallback;
  public_counter = 0;
  selected
}

function conditional_bool_false(flag : bool, fallback : bool) -> bool = {
  let selected = if flag then fallback else false;
  public_counter = 0;
  selected
}

function nested_pair_join(flag : bool, valid : bool, left : byte, right : byte) -> byte = {
  let selected : pair =
    if flag then {
      if valid then make_public_pair(left) else fatal_error(TestFatal)
    } else make_public_pair(right);
  consume_field_value(selected.first)
}

enum terminal_choice = {
  TerminalOne,
  TerminalTwo,
  TerminalThree,
  TerminalFour,
}

enum state_passing_outcome = {
  StateContinue,
  StateFailed,
}

type state_passing_zero = range(0, 0)
let STATE_PASSING_ZERO : state_passing_zero = 0

$[c_inline]
val state_passing_guard : (byte, word, bool) -> (word, state_passing_outcome)

function state_passing_guard(read_only, state, fail) =
  if fail then (STATE_PASSING_ZERO, StateFailed) else (state, StateContinue)

function forward_state_passing_guard(read_only : byte, state : word, fail : bool) -> (word, state_passing_outcome) = {
  let (state_after, status_after) = state_passing_guard(read_only, state, fail);
  (state_after, status_after)
}

function call_state_passing_guard(read_only : byte, state : word, fail : bool) -> (word, state_passing_outcome) = {
  let (state_after, status_after) = forward_state_passing_guard(read_only, state, fail);
  (state_after, status_after)
}

function state_passing_guard_failed(read_only : byte, state : word, fail : bool) -> bool = {
  let (state_after, status_after) = state_passing_guard(read_only, state, fail);
  if state_after == STATE_PASSING_ZERO then {
    match status_after {
      StateFailed => true,
      _ => false
    }
  } else false
}

function reused_boolean_guard(value : byte) -> bool = {
  let is_nonzero = value != 0;
  if is_nonzero then public_counter = 0;
  is_nonzero
}

function one_use_guard_before_local_write(value : byte) -> byte = {
  var current : byte = value;
  let is_nonzero = current != 0;
  if is_nonzero then public_counter = 0;
  current = tmod_nat(current + 1, 256);
  current
}

function one_use_guard_in_composed_condition(value : byte, fallback : bool) -> byte = {
  let is_nonzero = value != 0;
  if is_nonzero | fallback then public_counter = 0;
  value
}

function one_use_guard_in_reversed_composed_condition(value : byte, fallback : bool) -> byte = {
  let is_nonzero = value != 0;
  if fallback | is_nonzero then public_counter = 0;
  value
}

function terminal_enum_match(choice : terminal_choice) -> byte =
  match choice {
    TerminalOne => 1,
    TerminalTwo => 2,
    TerminalThree => 3,
    TerminalFour => 4,
  }

function terminal_enum_grouped(choice : terminal_choice) -> byte =
  match choice {
    TerminalOne => 1,
    TerminalTwo => 1,
    TerminalThree => 2,
    TerminalFour => 2,
  }

function terminal_enum_match_or_fatal(choice : terminal_choice) -> byte =
  match choice {
    TerminalOne => 1,
    TerminalTwo => 2,
    _ => {
      if public_counter != 0 then public_counter = 0;
      fatal_error(TestFatal)
    },
  }

function fatal_guard_result_is_unread(flag : bool) -> byte = {
  if flag then {
    fatal_error(TestFatal)
  };
  7
}

function widened_result_or_fatal(value : byte, valid : bool) -> word =
  if valid then value else fatal_error(TestFatal)

function terminal_signed_byte_or_fatal(value : bits(8), outer : bool, valid : bool) -> signed_byte =
  if outer then {
    if valid then signed(value) else fatal_error(TestFatal)
  } else fatal_error(TestFatal)

function terminal_signed_halfword_or_fatal(value : bits(16), outer : bool, valid : bool) -> signed_halfword =
  if outer then {
    if valid then signed(value) else fatal_error(TestFatal)
  } else fatal_error(TestFatal)

function terminal_signed_word_or_fatal(value : bits(32), outer : bool, valid : bool) -> signed_word =
  if outer then {
    if valid then signed(value) else fatal_error(TestFatal)
  } else fatal_error(TestFatal)

function terminal_signed_doubleword_or_fatal(value : bits(64), outer : bool, valid : bool) -> signed_doubleword =
  if outer then {
    if valid then signed(value) else fatal_error(TestFatal)
  } else fatal_error(TestFatal)

function throwing_signed_byte(value : bits(8), should_throw : bool) -> signed_byte = {
  if should_throw then throw(E_byte(1));
  signed(value)
}

function recover_throwing_signed_byte(value : bits(8), should_throw : bool) -> signed_byte =
  try throwing_signed_byte(value, should_throw) catch {
    E_byte(_) => -1,
  }

function terminal_unit_empty() -> unit = reset_counter()

function terminal_unit_other_empty() -> unit = public_counter = 1

function terminal_unit_byte(value : byte) -> unit = public_counter = value

function terminal_unit_variant_match(choice : erased_unit_choice) -> unit =
  match choice {
    EmptyChoice() => terminal_unit_empty(),
    OtherEmptyChoice() => terminal_unit_other_empty(),
    ByteChoice(value) => terminal_unit_byte(value),
  }

function terminal_variant_after_write(fail : bool) -> erased_unit_choice = {
  if fail then {
    let selected = EmptyChoice();
    public_counter = 0;
    selected
  } else {
    let selected = OtherEmptyChoice();
    public_counter = 1;
    selected
  }
}

function terminal_assertion(flag : bool) -> byte =
  if not_bool(flag) then {
    assert(false, "terminal assertion");
    0
  } else 1

function terminal_fixed_bytes_match(bytes : four_bytes) -> byte =
  match bytes {
    _ if eq_anything(bytes, TEST_FIXED_BYTES_ZERO) => 0,
    _ if eq_anything(bytes, TEST_FIXED_BYTES_ONE) => 1,
    _ => 2,
  }

function fixed_bytes_differ(left : four_bytes, right : four_bytes) -> bool =
  not_bool(eq_anything(left, right))

function machine_pick_zero(index : four_index) -> byte = {
  let bytes : four_bytes = vector_init(4, 0);
  bytes[index]
}

function step(value : byte) -> word = {
  public_counter = host_mix(public_counter, value);
  public_counter
}
