default Order dec

$include <prelude.sail>
$include <exception_basic.sail>

struct Pair = {
  left : int,
  right : bits(8)
}

union MaybeByte = {
  NoByte : unit,
  SomeByte : bits(8)
}

union BoundedValue('n : Int) = {
  Bounded : {'value, 0 <= 'value & 'value <= 'n. int('value)}
}

enum Direction = North | South | East

val direction_number : Direction -> int
function direction_number(direction) = num_of_Direction(direction)

val direction_from_number : range(0, 2) -> Direction
function direction_from_number(value) = Direction_of_num(value)

$[no_enum_number_conversions]
enum Traffic = Stop | Ready | Go

type u16_range = range(0, 2 ^ 16 - 1)
type u32_range = range(0, 2 ^ 32 - 1)
type u64_range = range(0, 2 ^ 64 - 1)
type u256_range = range(0, 2 ^ 256 - 1)
type quotient_range = range(0, div(31, 4))
type natural = nat

val sum_int : (int, int) -> int
function sum_int(x, y) = x + y

val local_shadows_function : int -> int
function local_shadows_function(x) = {
  let shadowed_name : int = x;
  shadowed_name
}

val identity_range_name : int -> int
function identity_range_name(range) = range

val shadowed_name : int -> int
function shadowed_name(x) = x + 1

val undefined_user_value : int -> int
function undefined_user_value(value) = value + 1

val keep_nat : nat -> nat
function keep_nat(x) = x

val keep_natural : natural -> natural
function keep_natural(x) = x

val keep_u8 : range(0, 255) -> range(0, 255)
function keep_u8(x) = x

val keep_u16 : u16_range -> u16_range
function keep_u16(x) = x

val keep_u32 : u32_range -> u32_range
function keep_u32(x) = x

val keep_u64 : u64_range -> u64_range
function keep_u64(x) = x

val keep_u256 : u256_range -> u256_range
function keep_u256(x) = x

val keep_small_range : range(3, 10) -> range(3, 10)
function keep_small_range(x) = x

val keep_quotient_range : quotient_range -> quotient_range
function keep_quotient_range(x) = x

val sum_bits : (bits(8), bits(8)) -> bits(8)
function sum_bits(x, y) = x + y

val polymorphic_first : forall 'n. (bits('n), bits('n)) -> bits('n)
function polymorphic_first(x, y) = x

val polymorphic_zeros : forall 'n, 'n >= 0. implicit('n) -> bits('n)
function polymorphic_zeros(n) = sail_zeros(n)

val dependent_bounded_identity : forall 'value, 0 <= 'value. int('value) -> {
  'result,
  0 <= 'result & 'result <= 'value.
  int('result)
}
function dependent_bounded_identity(value) = value

val concat_bits : (bits(4), bits(4)) -> bits(8)
function concat_bits(x, y) = x @ y

val low_nibble : bits(8) -> bits(4)
function low_nibble(x) = x[3 .. 0]

val signed_byte : bits(8) -> int
function signed_byte(x) = signed(x)

val add_integer_to_byte : (bits(8), int) -> bits(8)
function add_integer_to_byte(x, amount) = add_bits_int(x, amount)

val high_nibble : bits(8) -> bits(4)
function high_nibble(x) = truncateLSB(x, 4)

val byte_leading_zeros : bits(8) -> range(0, 8)
function byte_leading_zeros(x) = count_leading_zeros(x)

val byte_trailing_zeros : bits(8) -> range(0, 8)
function byte_trailing_zeros(x) = count_trailing_zeros(x)

val shift_left : (bits(8), int) -> bits(8)
function shift_left(x, amount) = sail_shiftleft(x, amount)

val shift_right : (bits(8), int) -> bits(8)
function shift_right(x, amount) = sail_shiftright(x, amount)

val shift_right_arithmetic : (bits(8), int) -> bits(8)
function shift_right_arithmetic(x, amount) = sail_arith_shiftright(x, amount)

val choose : (bool, int, int) -> int
function choose(condition, when_true, when_false) =
  if condition then when_true else when_false

val triangular : nat -> nat
function triangular(n) = {
  var result : nat = 0;
  foreach (i from 0 to n) {
    result = result + i;
  };
  result
}

val vector_pick : vector(4, dec, bits(8)) -> bits(8)
function vector_pick(items) = items[2]

val vector_fill : bits(8) -> vector(4, dec, bits(8))
function vector_fill(value) = vector_init(4, value)

val swap_pair : Pair -> Pair
function swap_pair(pair) = struct { left = signed(pair.right), right = 0x00 }

val update_pair : (Pair, int, bits(8)) -> Pair
function update_pair(pair, left, right) =
  { pair with left = left, right = right }

val pair_pattern_score : Pair -> int
function pair_pattern_score(pair) = match pair {
  struct { left, right = 0x00 } => left,
  struct { left, right } => left + signed(right)
}

val record_update_score : unit -> int
function record_update_score() = {
  let pair : Pair = struct { left = 4, right = 0xff };
  let updated = update_pair(pair, 9, 0x01);
  pair_pattern_score(updated)
}

val unwrap_or_zero : MaybeByte -> bits(8)
function unwrap_or_zero(value) = match value {
  SomeByte(byte) => byte,
  NoByte(()) => 0x00
}

val option_or_zero : option(int) -> int
function option_or_zero(value) = match value {
  Some(item) => item,
  None() => 0
}

val optional_positive : int -> option(int)
function optional_positive(value) =
  if value > 0 then Some(value) else None()

val traffic_score : Traffic -> int
function traffic_score(value) = match value {
  Stop => 0,
  Ready => 1,
  Go => 2
}

val guarded_score : int -> int
function guarded_score(value) = match value {
  item if item > 10 => item + 1,
  _ => 0
}

val head_or : (list(int), int) -> int
function head_or(items, fallback) = match items {
  head :: _ => head,
  [||] => fallback
}

val count_while : nat -> nat
function count_while(limit) = {
  var current : nat = 0;
  while current < limit do {
    current = current + 1;
  };
  current
}

val count_until : nat -> nat
function count_until(limit) = {
  var current : nat = 0;
  repeat {
    current = current + 1;
  } until current >= limit;
  current
}

val first_at_least : (nat, nat) -> nat
function first_at_least(limit, threshold) = {
  foreach (i from 0 to limit) {
    if i >= threshold then return i;
  };
  limit
}

val require_nonnegative : int -> int
function require_nonnegative(value) = {
  assert(value >= 0, "value must be non-negative");
  value
}

val catches_exception : unit -> bool
function catches_exception() =
  try throw(Exception()) catch {
    Exception(()) => true
  }

let COUNTER_BASE : int = 0
let COUNTER_INITIAL : int = COUNTER_BASE

register COUNTER : int = COUNTER_INITIAL

val bump_counter : int -> int
function bump_counter(amount) = {
  COUNTER = COUNTER + amount;
  COUNTER
}

val discard_bump_result : int -> int
function discard_bump_result(amount) = {
  let _ = bump_counter(amount);
  COUNTER
}

val host_value = pure "python_missing_host_value" : unit -> int

val c_host_value = pure { c: "c_host_value" } : unit -> int

val host_pair = pure "python_missing_host_pair" : unit -> Pair

val call_host : unit -> int
function call_host() = host_value()

val call_c_host : unit -> int
function call_c_host() = c_host_value()

val call_host_pair : unit -> Pair
function call_host_pair() = host_pair()

val call_undefined : unit -> int
function call_undefined() = undefined_int()
