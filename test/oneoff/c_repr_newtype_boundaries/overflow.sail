default Order dec

$include <prelude.sail>

$[c_repr uint64]
newtype gas = Gas : int

val unpack_gas : gas -> int

function unpack_gas(Gas(value)) = value

function main() -> unit =
  print_int("unreachable = ", unpack_gas(Gas(18446744073709551616)))
