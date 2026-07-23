default Order dec

$include <prelude.sail>
$include <arith.sail>

type word = range(0, 115792089237316195423570985008687907853269984665640564039457584007913129639935)

val U256 : forall 'value,
  0 <= 'value & 'value < 115792089237316195423570985008687907853269984665640564039457584007913129639936.
  atom('value) -> word

function U256(value) = value

let WORD_ALL_ONES : word =
  U256(unsigned(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))

function main() -> unit = ()
