default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

type byte = bits(8)

$[c_repr u256]
newtype u256 = U256 : bits(256)

$[c_repr fixed_bytes]
newtype address = Address : vector(20, dec, byte)

$[c_repr fixed_bytes]
newtype b160 = B160 : vector(20, dec, byte)

$[c_repr fixed_bytes]
newtype b256 = B256 : vector(32, dec, byte)

/* Fixed-byte lowering is structural rather than a closed B160/B256 list.
   This extra width guards the extensible B<N> container path. */
$[c_repr fixed_bytes]
newtype b384 = B384 : vector(48, dec, byte)

/* The representation annotation is independent of the source vector order. */
$[c_repr fixed_bytes]
newtype bytes20_inc = Bytes20Inc : vector(20, inc, byte)

/* The standard runtime primitive returns the low 256 bits at this result width. */
val u256_mul_bits = pure {
  _: "mult_vec"
} : (bits(256), bits(256)) -> bits(256)

val u256_add : (u256, u256) -> u256

function u256_add(U256(left), U256(right)) = U256(left + right)

val u256_sub : (u256, u256) -> u256

function u256_sub(U256(left), U256(right)) = U256(sub_bits(left, right))

val u256_mul : (u256, u256) -> u256

function u256_mul(U256(left), U256(right)) = U256(u256_mul_bits(left, right))

val u256_and : (u256, u256) -> u256

function u256_and(U256(left), U256(right)) = U256(left & right)

val u256_or : (u256, u256) -> u256

function u256_or(U256(left), U256(right)) = U256(left | right)

val u256_xor : (u256, u256) -> u256

function u256_xor(U256(left), U256(right)) = U256(xor_vec(left, right))

val u256_not : u256 -> u256

function u256_not(U256(value)) = U256(not_vec(value))

val u256_equal : (u256, u256) -> bool

function u256_equal(U256(left), U256(right)) = left == right

val u256_bit : (u256, range(0, 255)) -> bit

function u256_bit(U256(value), index) = value[index]

val u256_shift_left : (u256, range(0, 512)) -> u256

function u256_shift_left(U256(value), amount) = U256(sail_shiftleft(value, amount))

val u256_shift_right : (u256, range(0, 512)) -> u256

function u256_shift_right(U256(value), amount) = U256(sail_shiftright(value, amount))

val u256_arith_shift_right : (u256, range(0, 512)) -> u256

function u256_arith_shift_right(U256(value), amount) = U256(sail_arith_shiftright(value, amount))

val u256_from_byte : byte -> u256

function u256_from_byte(value) = U256(sail_zero_extend(value, 256))

val u256_from_lbits : bits(160) -> u256

function u256_from_lbits(value) = U256(sail_zero_extend(value, 256))

val u256_low_byte : u256 -> byte

function u256_low_byte(U256(value)) = value[7 .. 0]

val u256_middle_word : u256 -> bits(64)

function u256_middle_word(U256(value)) = value[127 .. 64]

/* A deliberately generic result exercises the compatibility path.  The
   native-only oneoff extraction does not preserve this function, while the
   mixed extraction does, so the backend must retain these helpers only when
   the final program genuinely crosses back to Sail's mathematical integer. */
val u256_to_nat : u256 -> nat

function u256_to_nat(U256(value)) = unsigned(value)

/* Fixed bitvectors should not detour through lbits/sail_int for the scalar
   operations used heavily by SSZ and RLP decoders. */
val limb_unsigned : bits(64) -> range(0, 18446744073709551615)

function limb_unsigned(value) = unsigned(value)

val limb_signed : bits(64) -> range(-9223372036854775808, 9223372036854775807)

function limb_signed(value) = signed(value)

val limb_shift_left : (bits(64), range(0, 128)) -> bits(64)

function limb_shift_left(value, amount) = sail_shiftleft(value, amount)

val limb_shift_right : (bits(64), range(0, 128)) -> bits(64)

function limb_shift_right(value, amount) = sail_shiftright(value, amount)

val byte_arith_shift_right : (bits(8), range(0, 16)) -> bits(8)

function byte_arith_shift_right(value, amount) = sail_arith_shiftright(value, amount)

val address_equal : (address, address) -> bool

function address_equal(Address(left), Address(right)) = left == right

/* A mixed represented/generic comparison must cross back to the generic
   vector ABI instead of selecting the fixed-bytes equality helper. */
val address_equal_vector : (address, vector(20, dec, byte)) -> bool

function address_equal_vector(Address(left), right) = left == right

val address_byte : (address, range(0, 19)) -> byte

function address_byte(Address(value), index) = value[index]

val address_update : (address, range(0, 19), byte) -> address

function address_update(Address(value), index, elem) = Address([value with index = elem])

val address_from_vector : vector(20, dec, byte) -> address

function address_from_vector(value) = Address(value)

val address_to_vector : address -> vector(20, dec, byte)

function address_to_vector(Address(value)) = value

val b160_equal : (b160, b160) -> bool

function b160_equal(B160(left), B160(right)) = left == right

val b256_equal : (b256, b256) -> bool

function b256_equal(B256(left), B256(right)) = left == right

/* Constructing an arbitrary fixed-byte container must stay entirely in its
   POD representation.  This is the path used by zero/fill constructors in
   optimized EVM code, and it applies uniformly to every B<N> width. */
val b256_fill : byte -> b256

function b256_fill(elem) = B256(vector_init(32, elem))

val b384_equal : (b384, b384) -> bool

function b384_equal(B384(left), B384(right)) = left == right

val b384_byte : (b384, range(0, 47)) -> byte

function b384_byte(B384(value), index) = value[index]

val b384_update : (b384, range(0, 47), byte) -> b384

function b384_update(B384(value), index, elem) = B384([value with index = elem])

val keep_bytes20_inc : bytes20_inc -> bytes20_inc

function keep_bytes20_inc(value) = value

val bytes20_inc_byte : (bytes20_inc, range(0, 19)) -> byte

function bytes20_inc_byte(Bytes20Inc(value), index) = value[index]

val bytes20_inc_update : (bytes20_inc, range(0, 19), byte) -> bytes20_inc

function bytes20_inc_update(Bytes20Inc(value), index, elem) = Bytes20Inc([value with index = elem])

val main : unit -> unit

function main(_) = ()
