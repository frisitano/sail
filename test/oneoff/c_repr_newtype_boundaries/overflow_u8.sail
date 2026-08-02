default Order dec

$include <prelude.sail>

$[c_repr uint8]
newtype octet = Octet : int

val unpack_octet : octet -> int

function unpack_octet(Octet(value)) = value

function main() -> unit =
  print_int("unreachable = ", unpack_octet(Octet(256)))
