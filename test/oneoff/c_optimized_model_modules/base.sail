default Order dec

$include <prelude.sail>

type byte = range(0, 255)
type halfword = range(0, 65535)
type byte_offset = range(0, 254)
type three_byte = range(0, 16777215)
type word = range(0, 4294967295)
type signed_word = range(-2147483648, 2147483647)
type blob_count = range(0, 12)
type blob_gas = range(0, 1572864)
$[c_repr u256]
type wide_word = range(0, 2 ^ 256 - 1)
type fixed_index = range(0, 16)
type four_index = range(0, 3)
type maybe_fixed_index = range(0, 17)
type fixed_id = range(0, 256)
type jump_table_index = range(0, 255)

val eq_anything = pure { c: "eq_anything" } : forall ('a : Type). ('a, 'a) -> bool

$[c_repr byte_pointer]
type direct_jump_table_index = range(0, 255)

let EMPTY_DIRECT_JUMP_TABLE : direct_jump_table_index = 0

let TEST_GAS : int(21000) = 21000
let TEST_GAS_ALIAS : int(21000) = TEST_GAS

struct pair = {
  first : byte,
  second : byte,
}

let RUNTIME_PAIR : pair = struct { first = 1, second = 2 }

function runtime_pair() -> pair = RUNTIME_PAIR

struct byte_slice = {
  bytes : byte,
  len : byte,
}

struct byte_slice_small = {
  bytes : byte_offset,
  len : byte,
}

$[c_repr {representation = external, name = TestBytes}]
struct canonical_slice = {
  bytes : byte,
  len : byte,
}

function canonical_slice_len(value : canonical_slice) -> byte = value.len

$[c_repr {representation = external, name = TestList}]
struct canonical_list = {
  values : list(byte),
  count : byte,
}

function canonical_list_count(value : canonical_list) -> byte = value.count

function canonical_list_identity(value : canonical_list) -> canonical_list = value

function canonical_list_count_after_identity(value : canonical_list) -> byte = {
  let remaining = canonical_list_identity(value);
  remaining.count
}

struct analyzed_code = {
  bytes : byte_offset,
  len : byte,
  jumpdests : jump_table_index,
}

$[c_repr {representation = fixed_bytes, name = bytes4}]
type four_bytes = vector(4, inc, byte)
$[c_repr {representation = fixed_bytes, name = test_bytes20}]
type twenty_bytes = vector(20, inc, byte)
$[c_repr {representation = fixed_bytes_u64_lanes, name = lane_bytes5}]
type lane_five_bytes = vector(5, inc, byte)
type fixed_ids = vector(17, fixed_id)

let TEST_FIXED_BYTES_ZERO : four_bytes = vector_init(4, 0)
$[c_static_eval "word_to_fixed_bytes"]
val test_word_to_four : bits(32) -> four_bytes
function test_word_to_four(value) = [
  unsigned(value[31 .. 24]),
  unsigned(value[23 .. 16]),
  unsigned(value[15 .. 8]),
  unsigned(value[7 .. 0]),
]
let TEST_FIXED_BYTES_ONE : four_bytes = test_word_to_four(0x00000001)
let TEST_LANE_BYTES : lane_five_bytes = [1, 35, 69, 103, 137]
let TEST_DISCOUNT : fixed_ids = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 256]

struct fixed_ids_box = {
  ids : fixed_ids,
}

struct equality_pair = {
  left : byte,
  right : byte,
}

union exception = {
  E_byte : byte,
}

union sample_choice = {
  InputChoice : byte,
  MemoryChoice : byte,
}

union erased_unit_choice = {
  EmptyChoice : unit,
  OtherEmptyChoice : unit,
  ByteChoice : byte,
}

enum tuple_choice = { TupleOne, TupleTwo, TupleThree }

function add_byte(left : byte, right : byte) -> range(0, 510) = left + right

function added_is_nonzero(left : byte, right : byte) -> bool = {
  let sum = add_byte(left, right);
  sum != 0
}

function boolean_cleanup(flag : bool) -> byte =
  if not_bool(not_bool(flag)) == true then 1 else 0

function positive_branch(flag : bool) -> byte =
  if not_bool(flag) then 0 else 1

function early_wide_guard(per_unit : halfword, units : wide_word) -> bool = {
  if (per_unit == 0) | (units == 0) then {
    return true
  };
  let remaining : word = 100;
  if units <= remaining then true else false
}

function widened_tuple_match(choice : tuple_choice) -> (halfword, halfword) =
  match choice {
    TupleOne => (1, 2),
    TupleTwo => (3, 4),
    TupleThree => (5, 6),
  }

function repeated_branch(first : bool, second : bool) -> byte =
  if first then 1 else if second then 1 else 2

function repeated_call_branch(first : bool, second : bool, value : byte) -> range(0, 510) =
  if first then add_byte(value, 1) else if second then add_byte(value, 1) else value

function boolean_value_join(first : bool, second : bool) -> bool = first & second

function boolean_comparison_join(left : byte, right : byte, flag : bool) -> bool =
  (left == right) | flag

function discard_internal_parameter(_proof : byte, value : byte) -> byte = value

function call_discard_internal_parameter(value : byte) -> byte =
  discard_internal_parameter(7, value)

function pure_parameter_value(value : byte) -> byte = value

function discard_computed_parameter(_computed : byte, value : byte) -> byte = value

function call_discard_computed_parameter(value : byte) -> byte = {
  let computed = pure_parameter_value(value);
  discard_computed_parameter(computed, value)
}

function preserve_unused_parameter(unused : byte) -> byte = 1

function require_flag(flag : bool) -> unit = assert(flag, "flag required")

function widen_optional_byte(value : option(byte)) -> option(halfword) =
  match value {
    None() => None(),
    Some(value) => Some(value),
  }

function test_gas() -> int(21000) = TEST_GAS

function test_gas_alias() -> int(21000) = TEST_GAS_ALIAS

function test_fixed_bytes_zero() -> four_bytes = TEST_FIXED_BYTES_ZERO

function test_fixed_bytes_one() -> four_bytes = TEST_FIXED_BYTES_ONE

function test_lane_bytes() -> lane_five_bytes = TEST_LANE_BYTES

function twenty_bytes_equal(left : twenty_bytes, right : twenty_bytes) -> bool =
  eq_anything(left, right)

function decrement_byte(value : byte) -> byte = {
  var result : byte = value;
  if result > 0 then result = 0;
  result
}

function increment_to(limit : byte) -> byte = {
  var current : byte = 0;
  while current < limit do {
    current = tmod_nat(current + 1, 256)
  };
  current
}

function count_four() -> byte = {
  var count : byte = 0;
  foreach (_index from 0 to 3) {
    count = tmod_nat(count + 1, 256)
  };
  count
}

function below_limit(current : byte, limit : byte) -> bool = current < limit

function increment_to_via_call(limit : byte) -> byte = {
  var current : byte = 0;
  while below_limit(current, limit) do {
    current = tmod_nat(current + 1, 256)
  };
  current
}

function wide_identity(value : wide_word) -> wide_word = value

function aggregate_early_return(flag : bool, value : wide_word) -> wide_word = {
  let result = wide_identity(value);
  if flag then return wide_identity(result);
  result
}

function widen_byte(value : byte) -> wide_word = value

val conditional_wide_return : forall 'left 'right,
  0 <= 'left & 'left < 2 ^ 256 & 0 <= 'right & 'right < 2 ^ 256.
  (int('left), int('right)) -> wide_word
function conditional_wide_return(left, right) =
  if right <= left then {
    left - right
  } else {
    let maximum : int(2 ^ 256 - 1) = 2 ^ 256 - 1;
    (maximum - (right - left)) + 1
  }

function narrow_then_decrement(distance : range(1, 256)) -> byte = {
  let index : byte = distance - 1;
  decrement_byte(index)
}

function widen_three_byte(value : three_byte) -> word = value

function narrow_wide_byte(value : wide_word) -> byte = {
  let bounded : byte = tmod_nat(value, 256);
  bounded
}

function narrow_word_remainder(value : word) -> byte = {
  let bounded : byte = tmod_nat(value, 9);
  bounded
}

function masked_high_nibble(value : bits(8)) -> byte = {
  let shifted : bits(8) = xor_vec(value, 0x8f);
  let nibble : range(0, 15) = unsigned(shifted[7 .. 4]);
  nibble
}

function one_bit_is_set(value : bits(1)) -> bool = value == 0b1

function unsigned_le_signed(left : word, right : signed_word) -> bool =
  left <= right

function signed_lt_unsigned(left : signed_word, right : word) -> bool =
  left < right

function unsigned_eq_signed(left : word, right : signed_word) -> bool =
  left == right

function guarded_blob_gas_add(
  maximum_count : blob_count,
  accumulated : blob_gas,
  transaction : word,
) -> bool = {
  let maximum = 131072 * maximum_count;
  (accumulated <= maximum) & (transaction <= maximum - accumulated)
}

function u256(value : wide_word) -> wide_word = value

function nested_wide_identity(value : wide_word) -> wide_word = u256(wide_identity(value))

function wide_pair_identity(value : (wide_word, wide_word)) -> (wide_word, wide_word) = value

function four_bytes_identity(value : four_bytes) -> four_bytes = value

val proof_identity : forall 'n, 0 <= 'n & 'n <= 255. int('n) -> int('n)
function proof_identity(value) = value

function identity_one(value : int(1)) -> int(1) = proof_identity(value)

function identity_two(value : int(2)) -> int(2) = proof_identity(value)

val proof_branch : forall 'n, 0 <= 'n & 'n <= 255. int('n) -> byte
function proof_branch(value) = if value < 4 then 1 else 2

let RUNTIME_LABEL_TEST : byte = proof_branch(5)

function runtime_label_test() -> byte = RUNTIME_LABEL_TEST

function branch_one(value : int(1)) -> byte = proof_branch(value)

function branch_five(value : int(5)) -> byte = proof_branch(value)

function pair_sum(value : pair) -> range(0, 510) = value.first + value.second

function sample_choice_value(value : sample_choice) -> byte = match value {
  InputChoice(value) => value,
  MemoryChoice(value) => value,
}

function byte_slice_at(off : byte, len : byte) -> byte_slice =
  struct { bytes = off, len = len }

function byte_slice_small_at(off : byte_offset, len : byte) -> byte_slice_small =
  struct { bytes = off, len = len }

function byte_slice_same_start(left : byte_slice, right : byte_slice) -> bool =
  left.bytes == right.bytes

function byte_slice_next(value : byte_slice_small) -> byte_slice = {
  let off = value.bytes;
  struct { bytes = off + 1, len = value.len }
}

function byte_slice_advance(value : byte_slice_small) -> byte_slice =
  struct { bytes = value.bytes + 1, len = value.len }

function byte_slice_distance(left : byte_slice, right : byte_slice) -> range(-255, 255) =
  left.bytes - right.bytes

val jumpdest_from_offset : byte_offset -> jump_table_index
function jumpdest_from_offset(off) = off

val empty_jumpdest : unit -> jump_table_index
function empty_jumpdest() = 0

val empty_direct_jumpdest : unit -> direct_jump_table_index
function empty_direct_jumpdest() = EMPTY_DIRECT_JUMP_TABLE

val analyzed_code_at : (byte_offset, byte, jump_table_index) -> analyzed_code
function analyzed_code_at(bytes, len, jumpdests) =
  struct { bytes = bytes, len = len, jumpdests = jumpdests }

function analyzed_code_copy(code : analyzed_code) -> analyzed_code =
  struct { bytes = code.bytes, len = code.len, jumpdests = code.jumpdests }

function pick_fixed_id(index : fixed_index) -> fixed_id = {
  let ids : fixed_ids = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 256];
  ids[index]
}

function pick_test_discount(index : fixed_index) -> fixed_id = TEST_DISCOUNT[index]

function pick_initialized_id(index : fixed_index) -> fixed_id = {
  let ids : fixed_ids = vector_init(17, 256);
  ids[index]
}

function pick_guarded_id(index : maybe_fixed_index) -> fixed_id =
  if index < 17 then {
    let ids : fixed_ids = vector_init(17, 256);
    ids[index]
  } else 0

function catch_byte(value : byte) -> byte =
  try throw(E_byte(value)) catch {
    E_byte(caught) => caught,
  }
