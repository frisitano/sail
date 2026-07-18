default Order dec

$include <prelude.sail>

$[c_repr int64]
newtype refund = Refund : int

struct refund_box = {
  value : refund
}

val add : (refund, refund) -> refund

function add(Refund(left), Refund(right)) = Refund(left + right)

val subtract : (refund, refund) -> refund

function subtract(Refund(left), Refund(right)) = Refund(left - right)

val less_than : (refund, refund) -> bool

function less_than(Refund(left), Refund(right)) = left < right

val equal_to : (refund, refund) -> bool

function equal_to(Refund(left), Refund(right)) = left == right

val pack_refund : int -> refund

function pack_refund(value) = Refund(value)

val unpack_refund : refund -> int

function unpack_refund(Refund(value)) = value

function main() -> unit = {
  let box : refund_box = struct { value = add(pack_refund(-3), pack_refund(5)) };
  print_int("sum = ", unpack_refund(box.value));
  print_int("difference = ", unpack_refund(subtract(pack_refund(-3), pack_refund(5))));
  assert(less_than(pack_refund(-3), pack_refund(5)));
  assert(equal_to(pack_refund(-4), pack_refund(-4)));
  print_int("min = ", unpack_refund(pack_refund(-9223372036854775808)));
  print_int("max = ", unpack_refund(pack_refund(9223372036854775807)))
}
