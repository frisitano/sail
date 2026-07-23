default Order dec

$include <prelude.sail>
$include <arith.sail>

type word = range(0, 115792089237316195423570985008687907853269984665640564039457584007913129639935)
type word_bit_count = range(0, 255)
type full_u64 = range(0, 18446744073709551615)
type wide_length = range(0, 340282366920938463463374607431768211455)
type signed_state_gas = range(-18446744073709551615, 18446744073726328831)
type word_modulus : Int = 2 ^ 256

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

function signed_state_gas_lifecycle(entry : full_u64, remaining : full_u64, spilled : word_bit_count) -> signed_state_gas =
  entry - remaining + spilled

val throw_if_zero : forall 'value, 0 <= 'value. atom('value) -> atom('value)

function throw_if_zero(value) =
  if value == 0 then throw(Ezero()) else value

function bounded_throw_if_zero(value : full_u64) -> full_u64 =
  throw_if_zero(value)

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

val generic_local_length : forall 'value, 0 <= 'value.
  atom('value) -> atom('value)

function generic_local_length(value) = value

function aggregate_local_length(value : NativeSlice) -> full_u64 = {
  let len = value.len;
  generic_local_length(len)
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
