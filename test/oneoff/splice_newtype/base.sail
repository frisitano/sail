default Order dec

$include <prelude.sail>

newtype gas = Gas : nat

struct gas_box = {
  value : gas
}

val pack_gas : nat -> gas

function pack_gas(value) = Gas(value)

val unpack_gas : gas -> nat

function unpack_gas(Gas(value)) = value

function main() -> unit = {
  let box : gas_box = struct { value = pack_gas(42) };
  print_int("gas = ", unpack_gas(box.value))
}
