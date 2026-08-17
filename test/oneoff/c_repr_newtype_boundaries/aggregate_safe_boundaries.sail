default Order dec

$include <prelude.sail>

$[c_repr uint8]
newtype octet = Octet : int

$[c_repr int8]
newtype signed_octet = SignedOctet : int

$[c_repr uint16]
newtype unsigned_halfword = UnsignedHalfword : int

$[c_repr int16]
newtype signed_halfword = SignedHalfword : int

struct boundary_box = {
  low : signed_octet,
  high : signed_octet,
  zero : octet,
  max : octet,
  widened_unsigned : unsigned_halfword,
  widened_signed : signed_halfword,
}

val unpack_octet : octet -> int
function unpack_octet(Octet(value)) = value

val unpack_signed_octet : signed_octet -> int
function unpack_signed_octet(SignedOctet(value)) = value

val unpack_unsigned_halfword : unsigned_halfword -> int
function unpack_unsigned_halfword(UnsignedHalfword(value)) = value

val unpack_signed_halfword : signed_halfword -> int
function unpack_signed_halfword(SignedHalfword(value)) = value

function main() -> unit = {
  let box : boundary_box = struct {
    low = SignedOctet(-128),
    high = SignedOctet(127),
    zero = Octet(0),
    max = Octet(255),
    widened_unsigned = UnsignedHalfword(unpack_octet(Octet(255))),
    widened_signed = SignedHalfword(unpack_signed_octet(SignedOctet(-128))),
  };
  let values : (signed_octet, octet) = (box.low, box.max);
  let (low, max) = values;
  assert(unpack_signed_octet(low) == -128, "signed lower boundary changed");
  assert(unpack_octet(max) == 255, "unsigned upper boundary changed");
  assert(unpack_unsigned_halfword(box.widened_unsigned) == 255, "unsigned widening changed");
  assert(unpack_signed_halfword(box.widened_signed) == -128, "signed widening changed")
}
