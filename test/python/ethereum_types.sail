default Order dec

$include <prelude.sail>

type byte = bits(8)
type address = vector(20, dec, byte)
type hash = vector(32, dec, byte)
type word = range(0, (2 ^ 256) - 1)
type word_below_max = range(0, (2 ^ 256) - 2)

val U256 : forall 'value, 0 <= 'value & 'value < 2 ^ 256. int('value) -> word
function U256(value) = value

function keep_address(value : address) -> address = value
function keep_hash(value : hash) -> hash = value
function update_hash(value : hash, index : range(0, 31), byte : byte) -> hash =
  [value with index = byte]
function keep_word(value : word) -> word = value
function increment_word(value : word_below_max) -> word = value + 1
