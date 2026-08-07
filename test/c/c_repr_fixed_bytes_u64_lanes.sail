default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

type byte = bits(8)

$[c_repr u256]
newtype u256 = U256 : bits(256)

/* These aliases deliberately match evm-sail's transparent, increasing-order
   address and digest types. The optimized representation is selected
   structurally after Sail erases the alias name. */
$[c_repr {representation = fixed_bytes_u64_lanes, name = bytes20}]
type lane_address = vector(20, inc, byte)

$[c_repr {representation = fixed_bytes_u64_lanes, name = bytes32}]
type lane_b256 = vector(32, inc, byte)

val lane_address_equal : (lane_address, lane_address) -> bool

function lane_address_equal(left, right) = left == right

val lane_address_byte : (lane_address, range(0, 19)) -> byte

function lane_address_byte(value, index) = value[index]

val lane_address_update : (lane_address, range(0, 19), byte) -> lane_address

function lane_address_update(value, index, elem) = [value with index = elem]

val lane_b256_equal : (lane_b256, lane_b256) -> bool

function lane_b256_equal(left, right) = left == right

val lane_b256_fill : byte -> lane_b256

function lane_b256_fill(elem) = vector_init(32, elem)

val lane_b256_to_u256 : lane_b256 -> u256

function lane_b256_to_u256(bytes) = U256(from_bytes_le(32, bytes))

val u256_to_lane_b256 : u256 -> lane_b256

function u256_to_lane_b256(U256(value)) = to_bytes_le(32, value)

val main : unit -> unit

function main(_) = ()
