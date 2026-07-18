default Order dec

$include <prelude.sail>

$[c_repr uint64]
newtype gas = Gas : nat

type quartet = vector(4, dec, bits(8))

type bounded_index = range(0, 31)

union represented_operation = {
  Represented_index : bounded_index,
  Represented_gas : gas
}

struct gas_box = {
  value : gas
}

struct index_box = {
  index : bounded_index
}

val increment : gas -> gas

function increment(Gas(value)) = Gas(value + 1)

val add : (gas, gas) -> gas

function add(Gas(left), Gas(right)) = Gas(left + right)

val subtract : (gas, gas) -> gas

function subtract(Gas(left), Gas(right)) =
  if right <= left then Gas(left - right) else Gas(0)

val multiply : (gas, gas) -> gas

function multiply(Gas(left), Gas(right)) = Gas(left * right)

val divide : (gas, gas) -> gas

function divide(Gas(left), Gas(right)) =
  if right == 0 then {
    Gas(0)
  } else {
    let quotient = tdiv_int(left, right);
    assert(0 <= quotient);
    Gas(quotient)
  }

val remainder : (gas, gas) -> gas

function remainder(Gas(left), Gas(right)) =
  if right == 0 then Gas(0) else Gas(tmod_int(left, right))

val less_than : (gas, gas) -> bool

function less_than(Gas(left), Gas(right)) = left < right

val equal_to : (gas, gas) -> bool

function equal_to(Gas(left), Gas(right)) = left == right

val reverse_index : bounded_index -> bounded_index

function reverse_index(index) = 31 - index

val operation_is_zero : represented_operation -> bool

function operation_is_zero(operation) = match operation {
  Represented_index(index) => index == 0,
  Represented_gas(Gas(value)) => value == 0
}

val boxed_index_is_zero : index_box -> bool

function boxed_index_is_zero(box) = box.index == 0

val boxed_index_differs : (index_box, bounded_index) -> bool

function boxed_index_differs(box, expected) = box.index != expected

val low_byte : gas -> bits(8)

function low_byte(Gas(value)) = get_slice_int(8, value, 0)

val to_limb : gas -> bits(64)

function to_limb(Gas(value)) = get_slice_int(64, value, 0)

val vector_read : (quartet, gas) -> bits(8)

function vector_read(values, Gas(index)) =
  if index <= 3 then values[index] else 0x00

val vector_write : (quartet, gas, bits(8)) -> quartet

function vector_write(values, Gas(index), elem) =
  if index <= 3 then [values with index = elem] else values

val pack_gas : nat -> gas

function pack_gas(value) = Gas(value)

val unpack_gas : gas -> nat

function unpack_gas(Gas(value)) = value

function main() -> unit = {
  let values : quartet = [0x00, 0x01, 0x02, 0x03];
  let updated = vector_write(values, pack_gas(2), 0x7f);
  assert(vector_read(updated, pack_gas(2)) == 0x7f);
  let box : gas_box = struct { value = increment(pack_gas(0)) };
  print_int("zero = ", unpack_gas(pack_gas(0)));
  print_int("incremented = ", unpack_gas(box.value));
  print_int("added = ", unpack_gas(add(pack_gas(2), pack_gas(3))));
  print_int("subtracted = ", unpack_gas(subtract(pack_gas(5), pack_gas(2))));
  print_int("multiplied = ", unpack_gas(multiply(pack_gas(3), pack_gas(4))));
  print_int("divided = ", unpack_gas(divide(pack_gas(12), pack_gas(3))));
  print_int("remainder = ", unpack_gas(remainder(pack_gas(13), pack_gas(5))));
  assert(less_than(pack_gas(2), pack_gas(3)));
  assert(equal_to(pack_gas(4), pack_gas(4)));
  assert(reverse_index(7) == 24);
  assert(operation_is_zero(Represented_index(0)));
  assert(operation_is_zero(Represented_gas(pack_gas(0))));
  assert(boxed_index_is_zero(struct { index = 0 }));
  assert(boxed_index_differs(struct { index = 1 }, 0));
  assert(low_byte(pack_gas(4779)) == 0xab);
  assert(to_limb(pack_gas(4660)) == 0x0000000000001234);
  print_int("max = ", unpack_gas(pack_gas(18446744073709551615)))
}
