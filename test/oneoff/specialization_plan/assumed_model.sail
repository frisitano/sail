default Order dec

$include <prelude.sail>

type word = range(0, 115792089237316195423570985008687907853269984665640564039457584007913129639935)

$[c_repr uint64]
newtype compact_word = CompactWord : int

val generic_compact_word : forall 'value, 0 <= 'value.
  atom('value) -> compact_word

function generic_compact_word(value) = CompactWord(value)

function compact_word_boundary(value : word) -> compact_word =
  generic_compact_word(value)

function main() -> unit = ()
