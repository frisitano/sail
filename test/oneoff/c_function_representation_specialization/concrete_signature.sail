default Order dec

$include <prelude.sail>
$include <arith.sail>

type word = range(0, 115792089237316195423570985008687907853269984665640564039457584007913129639935)
type full_u64 = range(0, 18446744073709551615)

val concrete_add : (word, word) -> word
function concrete_add(left, right) =
  if right == 0 then left else left

let NARROW_VALUE : full_u64 = 2000000000000000000

function rejected_concrete_specialization(left : word) -> word =
  concrete_add(left, NARROW_VALUE)

function main() -> unit = ()
