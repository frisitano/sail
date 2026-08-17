default Order dec

$include <prelude.sail>

$[c_repr uint8]
newtype octet = Octet : int

struct octet_box = {
  value : octet,
}

val unpack_octet : octet -> int
function unpack_octet(Octet(value)) = value

function main() -> unit = {
  let box : octet_box = struct { value = Octet(-1) };
  print_int("unreachable = ", unpack_octet(box.value))
}
