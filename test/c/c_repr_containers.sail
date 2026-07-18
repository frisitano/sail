default Order dec

$include <prelude.sail>

$[c_repr uint64]
newtype gas = Gas : nat

type protocol_quantity = range(0, 18446744073709551615)

struct gas_box = {
  direct : gas,
  optional : option(gas),
  checked : option(protocol_quantity)
}

val pack_gas : nat -> gas

function pack_gas(value) = Gas(value)

val optional_gas : gas -> option(gas)

function optional_gas(value) = Some(value)

val checked_protocol_quantity : nat -> option(protocol_quantity)

function checked_protocol_quantity(value) =
  if value <= 18446744073709551615 then Some(value) else None()

function main() -> unit = {
  let value = pack_gas(1);
  let box : gas_box = struct {
    direct = value,
    optional = optional_gas(value),
    checked = checked_protocol_quantity(1),
  };
  match box.checked {
    Some(amount) => print_int("gas = ", amount),
    None() => (),
  }
}
