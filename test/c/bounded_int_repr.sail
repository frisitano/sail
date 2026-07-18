default Order dec

$include <prelude.sail>

$option -c_include includes/bounded_int_repr.h

newtype gas = Gas : range(0, 18446744073709551615)

newtype bounded_i64 = Bounded_i64 : range(-9223372036854775808, 9223372036854775807)

newtype small_u64 = Small_u64 : range(0, 100)

newtype sum_u64 = Sum_u64 : range(0, 200)

newtype small_i64 = Small_i64 : range(-100, 100)

newtype sum_i64 = Sum_i64 : range(-200, 200)

struct bounded_box = {
  gas_value : gas,
  signed_value : bounded_i64
}

type protocol_quantity = range(0, 18446744073709551615)

type precompile_id = range(1, 256)

struct blob_schedule = {
  target : protocol_quantity,
  max : protocol_quantity,
  update_fraction : protocol_quantity
}

val literal_blob_schedule : unit -> blob_schedule

function literal_blob_schedule() = struct {
  target = 14,
  max = 21,
  update_fraction = 11684671
}

val literal_precompile_ids : unit -> vector(4, dec, precompile_id)

function literal_precompile_ids() = [1, 2, 3, 4]

val c_gas_identity = pure {c: "gas_identity"} : gas -> gas

function c_gas_identity(value) = value

val c_bounded_i64_identity = pure {c: "bounded_i64_identity"} : bounded_i64 -> bounded_i64

function c_bounded_i64_identity(value) = value

val add_small_u64 : (small_u64, small_u64) -> sum_u64

function add_small_u64(Small_u64(lhs), Small_u64(rhs)) = Sum_u64(lhs + rhs)

val add_small_i64 : (small_i64, small_i64) -> sum_i64

function add_small_i64(Small_i64(lhs), Small_i64(rhs)) = Sum_i64(lhs + rhs)

val gas_to_int : gas -> int

/* This is an explicit boundary back to Sail's arbitrary-precision int. */
function gas_to_int(Gas(value)) = value

val unwrap_i64 : bounded_i64 -> int

function unwrap_i64(Bounded_i64(value)) = value

val unwrap_sum_u64 : sum_u64 -> int

function unwrap_sum_u64(Sum_u64(value)) = value

val unwrap_sum_i64 : sum_i64 -> int

function unwrap_sum_i64(Sum_i64(value)) = value

val charge_gas : (gas, gas) -> gas

/* These operations stay entirely in the native uint64_t representation. */
function charge_gas(Gas(remaining), Gas(cost)) =
  if cost <= remaining then Gas(remaining - cost) else Gas(0)

val gas_less : (gas, gas) -> bool

function gas_less(Gas(lhs), Gas(rhs)) = lhs < rhs

val print_gas_direct : gas -> unit

/* Printing also crosses into sail_int because print_int accepts int. */
function print_gas_direct(Gas(value)) = print_int("gas direct = ", value)

val mixed_add : (gas, bounded_i64) -> int

function mixed_add(Gas(lhs), Bounded_i64(rhs)) = lhs + rhs

val mixed_greater : (gas, bounded_i64) -> bool

function mixed_greater(Gas(lhs), Bounded_i64(rhs)) = lhs > rhs

function main() -> unit = {
  let schedule = literal_blob_schedule();
  let precompile_ids = literal_precompile_ids();
  assert(schedule.target == 14);
  assert(precompile_ids[0] == 1);
  let box : bounded_box = struct {
    gas_value = c_gas_identity(Gas(18446744073709551615)),
    signed_value = c_bounded_i64_identity(Bounded_i64(-9223372036854775808))
  };
  print_int("gas min = ", gas_to_int(Gas(0)));
  print_int("gas max = ", gas_to_int(box.gas_value));
  print_gas_direct(box.gas_value);
  print_int("gas charged = ", gas_to_int(charge_gas(box.gas_value, Gas(1))));
  print_int("i64 min = ", unwrap_i64(box.signed_value));
  print_int("i64 max = ", unwrap_i64(Bounded_i64(9223372036854775807)));
  print_int("u64 sum = ", unwrap_sum_u64(add_small_u64(Small_u64(99), Small_u64(100))));
  print_int("i64 sum = ", unwrap_sum_i64(add_small_i64(Small_i64(-100), Small_i64(75))));
  print_int("mixed sum = ", mixed_add(Gas(18446744073709551615), Bounded_i64(-1)));
  if gas_less(Gas(0), Gas(18446744073709551615)) then
    print_endline("gas order = true")
  else
    print_endline("gas order = false");
  if mixed_greater(Gas(18446744073709551615), Bounded_i64(9223372036854775807)) then
    print_endline("mixed order = true")
  else
    print_endline("mixed order = false")
}
