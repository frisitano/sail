default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

type byte = bits(8)

type word = range(0, 2 ^ 256 - 1)

$[c_repr u256]
newtype u256 = U256 : bits(256)

$[c_repr {representation = fixed_bytes, name = bytes20}]
newtype address = Address : vector(20, dec, byte)

/* The EVM model uses a transparent alias rather than a nominal wrapper. */
$[c_repr {representation = fixed_bytes, name = bytes20}]
type address_alias = vector(20, dec, byte)

$[c_repr {representation = fixed_bytes, name = bytes20}]
newtype b160 = B160 : vector(20, dec, byte)

$[c_repr {representation = fixed_bytes, name = bytes32}]
newtype b256 = B256 : vector(32, dec, byte)

/* Fixed-byte lowering is structural rather than a closed B160/B256 list.
   This extra width guards the extensible B<N> container path. */
$[c_repr {representation = fixed_bytes, name = bytes48}]
newtype b384 = B384 : vector(48, dec, byte)

/* The representation annotation is independent of the source vector order. */
$[c_repr {representation = fixed_bytes, name = bytes20}]
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

/* Constant-width instances of the standard byte-vector conversions must keep
   their native endpoint representations after polymorphic specialization. */
val b256_to_u256 : b256 -> u256

function b256_to_u256(B256(bytes)) = U256(from_bytes_le(32, bytes))

val u256_to_b256 : u256 -> b256

function u256_to_b256(U256(value)) = B256(to_bytes_le(32, value))

val address_to_u256 : address -> u256

function address_to_u256(Address(bytes)) = U256(sail_zero_extend(from_bytes_le(20, bytes), 256))

val u256_to_address : u256 -> address

function u256_to_address(U256(value)) = Address(to_bytes_le(20, value[159 .. 0]))

/* The EVM word is a transparent range rather than a bits newtype.  These are
   the address boundary shapes used by evm-sail: from_bytes_le is embedded in
   the word range, while to_bytes_le consumes a proven low-160-bit slice. */
val address_to_word : address -> word

function address_to_word(Address(bytes)) = unsigned(from_bytes_le(20, bytes))

val word_to_address : word -> address

function word_to_address(value) = Address(to_bytes_le(20, get_slice_int(160, value, 0)))

val address_alias_low_byte : address_alias -> byte

function address_alias_low_byte(value) = value[0]

/* Exercise an ordinary fixed-vector result directly at a represented alias
   boundary.  No source conversion is needed: both values have the same Sail
   type, while the specialized C call must retain the fixed-byte ABI. */
val word_address_alias_low_byte : word -> byte

function word_address_alias_low_byte(value) =
  address_alias_low_byte(to_bytes_le(20, get_slice_int(160, value, 0)))

val word_low_byte : word -> byte

function word_low_byte(value) = get_slice_int(8, value, 0)

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

/* These tighter semantic bounds discharge the C shift-count obligation.  The
   generated operations therefore need neither the >= 64 branch nor the safe
   shift helper retained by the wider-range controls above. */
val limb_shift_left_in_range : (bits(64), range(0, 63)) -> bits(64)

function limb_shift_left_in_range(value, amount) = sail_shiftleft(value, amount)

val limb_shift_right_in_range : (bits(64), range(0, 63)) -> bits(64)

function limb_shift_right_in_range(value, amount) = sail_shiftright(value, amount)

/* Equal-width zero extension is a value-preserving semantic conversion and
   should disappear before C emission. */
val byte_widen_identity : bits(8) -> bits(8)

function byte_widen_identity(value) = sail_zero_extend(value, 8)

/* Signed-value preservation and low-bit truncation are separate semantic
   obligations even though all of these values use the same C carrier. */
val byte_sign_identity : bits(8) -> bits(8)

function byte_sign_identity(value) = sail_sign_extend(value, 8)

val byte_truncate_identity : bits(8) -> bits(8)

function byte_truncate_identity(value) = truncate(value, 8)

/* Both extension kinds preserve the original low bits.  The final truncation
   can therefore return the original byte, including through multiple
   immutable conversion bindings. */
val byte_unsigned_extend_truncate_roundtrip : bits(8) -> bits(8)

function byte_unsigned_extend_truncate_roundtrip(value) =
  truncate(sail_zero_extend(sail_zero_extend(value, 16), 32), 8)

val byte_sign_extend_truncate_roundtrip : bits(8) -> bits(8)

function byte_sign_extend_truncate_roundtrip(value) =
  truncate(sail_sign_extend(sail_sign_extend(value, 16), 32), 8)

/* Controls: genuine narrowing must keep its low-bit mask, while a wider sign
   extension must retain sign propagation.  Truncating an extended byte to a
   different width is not a round trip and must preserve both operations. */
val word_truncate_byte : bits(16) -> bits(8)

function word_truncate_byte(value) = truncate(value, 8)

val byte_sign_widen : bits(8) -> bits(16)

function byte_sign_widen(value) = sail_sign_extend(value, 16)

val byte_unsigned_extend_truncate_seven : bits(8) -> bits(7)

function byte_unsigned_extend_truncate_seven(value) =
  truncate(sail_zero_extend(value, 16), 7)

val byte_sign_extend_truncate_nine : bits(8) -> bits(9)

function byte_sign_extend_truncate_nine(value) =
  truncate(sail_sign_extend(value, 16), 9)

val byte_arith_shift_right : (bits(8), range(0, 16)) -> bits(8)

function byte_arith_shift_right(value, amount) = sail_arith_shiftright(value, amount)

/* Result-bound certificates from masks, slices, concatenation and fixed bit
   insertion must survive a same-ABI function boundary.  The generic helper is
   valid for arbitrary 64-bit operands, but these callers demand narrower body
   specializations from their actual value web. */
val multiply_bit_words : (bits(64), bits(64)) -> range(0, 340282366920938463426481119284349108225)

function multiply_bit_words(left, right) = unsigned(left) * unsigned(right)

val multiply_masked_bytes : bits(64) -> range(0, 340282366920938463426481119284349108225)

function multiply_masked_bytes(value) = {
  let mask : bits(64) = 0x00000000000000FF;
  multiply_bit_words(value & mask, sail_shiftright(value, 8) & mask)
}

/* A non-contiguous mask is not a low-bit slice certificate.  It must remain
   an ordinary shift-and-mask web even though its shift count is defined. */
val shift_noncontiguous_mask : bits(64) -> bits(64)

function shift_noncontiguous_mask(value) =
  sail_shiftright(value, 8) & 0x00000000000000F5

val multiply_sliced_bytes : bits(64) -> range(0, 340282366920938463426481119284349108225)

function multiply_sliced_bytes(value) =
  multiply_bit_words(sail_zero_extend(value[7 .. 0], 64), sail_zero_extend(value[15 .. 8], 64))

val multiply_concatenated_bytes : bits(64) -> range(0, 340282366920938463426481119284349108225)

function multiply_concatenated_bytes(value) = {
  let joined : bits(16) = append(value[7 .. 0], value[15 .. 8]);
  multiply_bit_words(sail_zero_extend(joined, 64), sail_zero_extend(joined, 64))
}

/* The fixed-bitvector web fusion must not merge slices from distinct semantic
   sources, even when their widths and constant offsets otherwise line up. */
val concatenate_distinct_sources : (bits(64), bits(64)) -> bits(16)

function concatenate_distinct_sources(left, right) =
  append(left[7 .. 0], right[15 .. 8])

val multiply_inserted_byte : bits(8) -> range(0, 340282366920938463426481119284349108225)

function multiply_inserted_byte(value) = {
  let inserted : bits(64) = set_slice_bits(64, 8, sail_zeros(64), 8, value);
  multiply_bit_words(inserted, inserted)
}

/* A bounded dynamic position is just as safe as a literal insertion point.
   The optimized backend should use the same native mask/shift operation. */
val insert_byte_at : (bits(64), range(0, 56), bits(8)) -> bits(64)

function insert_byte_at(base, start, value) =
  set_slice_bits(64, 8, base, start, value)

/* This position range does not prove that the inserted byte remains inside
   the carrier, so it must retain the generic checked Sail implementation. */
val insert_byte_at_unproven : (bits(64), range(0, 57), bits(8)) -> bits(64)

function insert_byte_at_unproven(base, start, value) =
  set_slice_bits(64, 8, base, start, value)

val address_equal : (address, address) -> bool

function address_equal(Address(left), Address(right)) = left == right

/* An equal-width generic vector can share the represented fixed-byte ABI in
   the specialized build; the ordinary backend retains Sail's vector ABI. */
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
