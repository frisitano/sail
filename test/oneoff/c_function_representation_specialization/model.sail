default Order dec

$include <prelude.sail>
$include <arith.sail>
$include <smt.sail>

type word = range(0, 115792089237316195423570985008687907853269984665640564039457584007913129639935)
type word_bit_count = range(0, 255)
type full_u64 = range(0, 18446744073709551615)
type wide_length = range(0, 340282366920938463463374607431768211455)
type wide_product = range(0, 2135987035920910082279229616932235919179133537347964862093771623156579161741164519270975247745025)
type wide_sum = range(0, 231584178474632390847141970017375815706539969331281128078915168015826259279870)
type byte = range(0, 255)
type smaller_tiny = range(0, 7)
type tiny = range(0, 8)
type tiny_sum = range(0, 16)
type tiny_product = range(0, 64)
type medium = range(0, 200)
type wider_than_byte = range(0, 300)
type signed_state_gas = range(-18446744073709551615, 18446744073726328831)
type word_modulus : Int = 2 ^ 256
type wide_modulus : Int = 2 ^ 128
type byte_modulus : Int = 2 ^ 8

union exception = {
  Ezero : unit,
}

function U256(value : range(0, 115792089237316195423570985008687907853269984665640564039457584007913129639935)) -> word = value

let REWARD = unsigned(0x1bc16d674ec80000)

val leaf_add : forall 'right,
  0 <= 'right & 'right <= 115792089237316195423570985008687907853269984665640564039457584007913129639935.
  (word, atom('right)) -> word

function leaf_add(left, right) = U256(tmod_nat(left + right, sizeof(word_modulus)))

val middle_add : forall 'right,
  0 <= 'right & 'right <= 115792089237316195423570985008687907853269984665640564039457584007913129639935.
  (word, atom('right)) -> word

function middle_add(left, right) = leaf_add(left, right)

val top_add : forall 'right,
  0 <= 'right & 'right <= 115792089237316195423570985008687907853269984665640564039457584007913129639935.
  (word, atom('right)) -> word

function top_add(left, right) = middle_add(left, right)

val add_reward : word -> word

function add_reward(balance) = top_add(balance, REWARD)

function add_full(left : word, right : word) -> word = leaf_add(left, right)

function exact_add_full(left : word, right : word) -> wide_sum = left + right

function non_power_of_two_addmod(left : word, right : word) -> word =
  U256(tmod_nat(left + right, sizeof(word_modulus) - 1))

function wrapping_sub_full(left : word, right : word) -> word =
  U256(emod_positive(left - right, sizeof(word_modulus)))

function wrapping_sub_u64(left : word, right : full_u64) -> word =
  U256(emod_positive(left - right, sizeof(word_modulus)))

function wrapping_sub_u8(left : byte, right : byte) -> byte =
  emod_positive(left - right, sizeof(byte_modulus))

function non_power_of_two_submod(left : word, right : full_u64) -> word =
  U256(emod_positive(left - right, sizeof(word_modulus) - 1))

function truncating_submod(left : word, right : full_u64) -> int =
  tmod_int(left - right, sizeof(word_modulus))

val ordered_truncating_submod : forall 'left 'right,
  0 <= 'right & 'right <= 'left & 'left < 2 ^ 256.
  (atom('left), atom('right)) -> word

function ordered_truncating_submod(left, right) =
  U256(tmod_nat(left - right, sizeof(word_modulus)))

val ordered_non_power_of_two_submod : forall 'left 'right,
  0 <= 'right & 'right <= 'left & 'left < 2 ^ 256.
  (atom('left), atom('right)) -> word

function ordered_non_power_of_two_submod(left, right) =
  U256(tmod_nat(left - right, sizeof(word_modulus) - 1))

function wrapping_truncating_sub_ordered(left : word, right : word) -> word =
  if right <= left then ordered_truncating_submod(left, right) else 0

function wrapping_add_u128(left : wide_length, right : full_u64) -> wide_length =
  tmod_nat(left + right, sizeof(wide_modulus))

function wrapping_mul_u128_result(left : wide_length, right : full_u64) -> wide_length =
  tmod_nat(left * right, sizeof(wide_modulus))

val leaf_mul : forall 'right,
  0 <= 'right & 'right <= 115792089237316195423570985008687907853269984665640564039457584007913129639935.
  (word, atom('right)) -> word

function leaf_mul(left, right) = U256(tmod_nat(left * right, sizeof(word_modulus)))

val leaf_mul_reverse : forall 'right,
  0 <= 'right & 'right <= 115792089237316195423570985008687907853269984665640564039457584007913129639935.
  (word, atom('right)) -> word

function leaf_mul_reverse(left, right) = U256(tmod_nat(right * left, sizeof(word_modulus)))

function wrapping_mul_u64(left : word, right : full_u64) -> word =
  leaf_mul(left, right)

function wrapping_mul_u64_reverse(left : word, right : full_u64) -> word =
  leaf_mul_reverse(left, right)

function wrapping_mul_u128(left : word, right : wide_length) -> word =
  leaf_mul(left, right)

function wrapping_mul_u128_reverse(left : word, right : wide_length) -> word =
  leaf_mul_reverse(left, right)

function wrapping_mul_full(left : word, right : word) -> word =
  leaf_mul(left, right)

function exact_mul_u64(left : word, right : full_u64) -> wide_product =
  left * right

function non_power_of_two_mulmod(left : word, right : full_u64) -> word =
  U256(tmod_nat(left * right, sizeof(word_modulus) - 1))

function shared_product_mulmod(left : word, right : full_u64) -> word = {
  let product : wide_product = left * right;
  let wrapped = U256(tmod_nat(product, sizeof(word_modulus)));
  if product == 0 then 0 else wrapped
}

function interleaved_mulmod(left : word, right : full_u64) -> word = {
  let product = left * right;
  print("semantic web interleave");
  U256(tmod_nat(product, sizeof(word_modulus)))
}

val alu_addmod : forall 'left 'right 'modulus,
  0 <= 'left & 'left < 2 ^ 256 &
  0 <= 'right & 'right < 2 ^ 256 &
  0 <= 'modulus & 'modulus < 2 ^ 256.
  (atom('left), atom('right), atom('modulus)) -> word

function alu_addmod(left, right, modulus) =
  if modulus == 0 then 0 else U256(tmod_nat(left + right, modulus))

val alu_mulmod : forall 'left 'right 'modulus,
  0 <= 'left & 'left < 2 ^ 256 &
  0 <= 'right & 'right < 2 ^ 256 &
  0 <= 'modulus & 'modulus < 2 ^ 256.
  (atom('left), atom('right), atom('modulus)) -> word

function alu_mulmod(left, right, modulus) =
  if modulus == 0 then 0 else U256(tmod_nat(left * right, modulus))

function full_addmod(left : word, right : word, modulus : word) -> word =
  alu_addmod(left, right, modulus)

function full_mulmod(left : word, right : word, modulus : word) -> word =
  alu_mulmod(left, right, modulus)

function consume_bit_count(amount : word_bit_count) -> word_bit_count = amount

function narrow_after_guard(amount : word) -> word_bit_count =
  if amount < 256 then consume_bit_count(amount) else 0

val words_for_bytes : forall 'byte_len, 0 <= 'byte_len.
  atom('byte_len) -> atom(div('byte_len + 31, 32))

function words_for_bytes(byte_len) = tdiv_nat(byte_len + 31, 32)

function word_words_for_bytes(byte_len : word) -> word = words_for_bytes(byte_len)

function native_words_for_bytes(byte_len : word_bit_count) -> word_bit_count =
  words_for_bytes(byte_len)

function full_u64_words_for_bytes(byte_len : full_u64) -> full_u64 =
  words_for_bytes(byte_len)

val dependent_add : forall 'left 'right, 0 <= 'left & 0 <= 'right.
  (atom('left), atom('right)) -> atom('left + 'right)

function dependent_add(left, right) = left + right

function unbounded_dependent_add(left : full_u64, right : full_u64) -> nat =
  dependent_add(left, right)

val dependent_tiny_add : forall 'left 'right,
  0 <= 'left & 'left <= 8 & 0 <= 'right & 'right <= 8.
  (atom('left), atom('right)) -> atom('left + 'right)

function dependent_tiny_add(left, right) = left + right

function bounded_dependent_tiny_add(left : tiny, right : tiny) -> tiny_sum =
  dependent_tiny_add(left, right)

val dependent_tiny_sub : forall 'left 'right,
  0 <= 'right & 'right <= 'left & 'left <= 8.
  (atom('left), atom('right)) -> atom('left - 'right)

function dependent_tiny_sub(left, right) = left - right

function bounded_dependent_tiny_sub(left : tiny, right : tiny) -> tiny =
  if right <= left then dependent_tiny_sub(left, right) else 0

val dependent_tiny_mul : forall 'left 'right,
  0 <= 'left & 'left <= 8 & 0 <= 'right & 'right <= 8.
  (atom('left), atom('right)) -> atom('left * 'right)

function dependent_tiny_mul(left, right) = left * right

function bounded_dependent_tiny_mul(left : tiny, right : tiny) -> tiny_product =
  dependent_tiny_mul(left, right)

val caller_sensitive_square_le : forall 'value,
  0 <= 'value & 'value <= 200.
  atom('value) -> bool

function caller_sensitive_square_le(value) = value * value <= 64

function smaller_tiny_square_le(value : smaller_tiny) -> bool =
  caller_sensitive_square_le(value)

function tiny_square_le(value : tiny) -> bool =
  caller_sensitive_square_le(value)

function medium_square_le(value : medium) -> bool =
  caller_sensitive_square_le(value)

val forward_caller_sensitive_square_le : forall 'value,
  0 <= 'value & 'value <= 200.
  atom('value) -> bool

function forward_caller_sensitive_square_le(value) =
  caller_sensitive_square_le(value)

function tiny_forwarded_square_le(value : tiny) -> bool =
  forward_caller_sensitive_square_le(value)

function medium_forwarded_square_le(value : medium) -> bool =
  forward_caller_sensitive_square_le(value)

val caller_bounded_wrapping_mul : forall 'left 'right,
  0 <= 'left & 0 <= 'right.
  (atom('left), atom('right)) -> byte

function caller_bounded_wrapping_mul(left, right) =
  tmod_nat(left * right, sizeof(byte_modulus))

function tiny_caller_bounded_wrapping_mul(left : tiny, right : tiny) -> byte =
  caller_bounded_wrapping_mul(left, right)

function wide_caller_bounded_wrapping_mul(left : wider_than_byte, right : wider_than_byte) -> byte =
  caller_bounded_wrapping_mul(left, right)

val dependent_mul : forall 'left 'right, 0 <= 'left & 0 <= 'right.
  (atom('left), atom('right)) -> atom('left * 'right)

function dependent_mul(left, right) = left * right

function unbounded_dependent_mul(left : full_u64, right : full_u64) -> nat =
  dependent_mul(left, right)

function guarded_u64_tiny_square(value : full_u64) -> tiny_product =
  if value <= 8 then dependent_mul(value, value) else 0

function else_guarded_u64_tiny_square(value : full_u64) -> tiny_product =
  if value > 8 then 0 else dependent_mul(value, value)

function is_tiny_u64(value : full_u64) -> bool =
  value <= 8

function forwarded_is_tiny_u64(value : full_u64) -> bool =
  is_tiny_u64(value)

val predicate_sensitive_square_le : forall 'value, 0 <= 'value.
  atom('value) -> bool

function predicate_sensitive_square_le(value) =
  value * value <= 64

function helper_guarded_u64_tiny_square(value : full_u64) -> bool =
  if forwarded_is_tiny_u64(value) then predicate_sensitive_square_le(value) else false

function is_not_tiny_u64(value : full_u64) -> bool =
  not_bool(is_tiny_u64(value))

function negated_helper_guarded_square(value : full_u64) -> bool =
  if is_not_tiny_u64(value) then false else predicate_sensitive_square_le(value)

function recursive_is_tiny_u64(value : full_u64) -> bool =
  if value == 0 then true else recursive_is_tiny_u64(value - 1)
termination_measure recursive_is_tiny_u64(value) = value

function recursive_predicate_guarded_square(value : full_u64) -> bool =
  if recursive_is_tiny_u64(value) then predicate_sensitive_square_le(value) else false

function unsound_mixed_predicate(value : full_u64) -> bool =
  if value == 0 then value <= 8 else true

function unsound_predicate_guarded_square(value : full_u64) -> bool =
  if unsound_mixed_predicate(value) then predicate_sensitive_square_le(value) else false

function comparison_observable_path(value : full_u64) -> full_u64 =
  value

val comparison_unreachable_specialization : forall 'value, 0 <= 'value.
  atom('value) -> atom('value)

function comparison_unreachable_specialization(value) =
  value

function comparison_fold_true(value : tiny) -> full_u64 =
  if value <= 8 then value else comparison_unreachable_specialization(value)

function comparison_fold_false(value : tiny) -> full_u64 =
  if value > 8 then comparison_unreachable_specialization(value) else value

function comparison_fold_forwarded(value : full_u64) -> full_u64 =
  if forwarded_is_tiny_u64(value) then
    if value > 8 then comparison_observable_path(value) else value
  else 0

function comparison_fold_unknown(value : full_u64) -> full_u64 =
  if value > 8 then comparison_observable_path(value) else value

function comparison_fold_after_mutation(value : full_u64, replacement : full_u64) -> full_u64 = {
  var current : full_u64 = value;
  let was_tiny = current <= 8;
  current = replacement;
  if was_tiny then
    if current > 8 then comparison_observable_path(current) else current
  else current
}

function invalidated_u64_square(value : full_u64, replacement : full_u64) -> nat = {
  var current : full_u64 = value;
  let fits_in_tiny = current <= 8;
  current = replacement;
  if fits_in_tiny then dependent_mul(current, current) else 0
}

struct IntegerBox('value : Int), 0 <= 'value = {
  value : atom('value),
}

type BoundedIntegerBox = {
  'value,
  0 <= 'value & 'value < 256.
  IntegerBox('value)
}

val integer_box_value : forall 'value, 0 <= 'value.
  IntegerBox('value) -> atom('value)

function integer_box_value(box) = box.value

function bounded_integer_box_value(box : BoundedIntegerBox) -> word_bit_count =
  integer_box_value(box)

function mutable_unbounded_accumulator(value : nat) -> nat = {
  var total : nat = 0;
  total = total + value;
  total
}

function bounded_guarded_loop(value : word_bit_count) -> int = {
  var current : int = value;
  while current < 8 do {
    current = current + 1
  };
  current
}

function unbounded_guarded_loop(value : nat, steps : word_bit_count) -> nat = {
  var current : nat = value;
  var remaining : int = steps;
  while remaining > 0 do {
    current = current + 1;
    remaining = remaining - 1
  };
  current
}

function signed_state_gas_lifecycle(entry : full_u64, remaining : full_u64, spilled : word_bit_count) -> signed_state_gas =
  entry - remaining + spilled

val throw_if_zero : forall 'value, 0 <= 'value. atom('value) -> atom('value)

function throw_if_zero(value) =
  if value == 0 then throw(Ezero()) else value

function bounded_throw_if_zero(value : full_u64) -> full_u64 =
  throw_if_zero(value)

function bounded_guarded_ediv(numerator : full_u64, denominator : byte) -> full_u64 = {
  if denominator == 0 then throw(Ezero());
  ediv_int(numerator, denominator)
}

val recursive_once : forall 'value, 0 <= 'value.
  (atom('value), bool) -> unit

function recursive_once(value, continue) =
  if continue then recursive_once(value, false) else ()
termination_measure recursive_once(value, continue) = if continue then 1 else 0

function bounded_recursive_once(value : full_u64) -> unit =
  recursive_once(value, true)

val recursive_countdown : forall 'value, 0 <= 'value.
  atom('value) -> unit

function recursive_countdown(value) =
  if value == 0 then () else recursive_countdown(value - 1)
termination_measure recursive_countdown(value) = value

function bounded_recursive_countdown(value : full_u64) -> unit =
  recursive_countdown(value)

struct NativeSlice = {
  len : full_u64,
}

struct SemanticIntegerBox = {
  value : nat,
}

val generic_local_length : forall 'value, 0 <= 'value.
  atom('value) -> atom('value)

function generic_local_length(value) = value

function aggregate_local_length(value : NativeSlice) -> full_u64 = {
  let len = value.len;
  generic_local_length(len)
}

function aggregate_constructor_fact(value : word_bit_count) -> nat = {
  let box : SemanticIntegerBox = struct { value = value };
  let recovered = box.value;
  generic_local_length(recovered)
}

function invalidated_aggregate_constructor_fact(value : word_bit_count, replacement : nat) -> nat = {
  var box : SemanticIntegerBox = struct { value = value };
  box.value = replacement;
  let recovered = box.value;
  generic_local_length(recovered)
}

function bounded_callee_result(value : full_u64) -> nat =
  if value < 8 then value else 8

function recursive_bounded_callee(value : full_u64) -> nat =
  if value == 0 then 7
  else if value < 8 then recursive_bounded_callee(value - 1)
  else 7

function consume_bounded_callee_result(value : full_u64) -> bool = {
  let bounded = bounded_callee_result(value);
  bounded * bounded <= 64
}

function consume_recursive_bounded_callee(value : full_u64) -> bool = {
  let bounded = recursive_bounded_callee(value);
  bounded * bounded <= 64
}

function unbounded_callee_result(value : nat) -> nat = value

function consume_unbounded_callee_result(value : nat) -> bool = {
  let unbounded = unbounded_callee_result(value);
  unbounded * unbounded <= 64
}

val generic_encoded_length : forall 'value, 0 <= 'value.
  atom('value) -> range(1, 'value + 33)

function generic_encoded_length(value) = value + 1

function aggregate_encoded_length(value : NativeSlice) -> wide_length = {
  let len = value.len;
  generic_encoded_length(len)
}

val guarded_comparison : forall 'value, 0 <= 'value.
  atom('value) -> bool

function guarded_comparison(value) = value < 2 ^ 256

function bounded_guarded_comparison(value : wide_length) -> bool =
  guarded_comparison(value)

function main() -> unit = ()
