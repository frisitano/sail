default Order dec

$include <prelude.sail>

type bounded_word = range(0, 2 ^ 256 - 1)
type bounded_word_modulus : Int = 2 ^ 256

function consume_bounded_word(value : bounded_word) -> unit = ()

val pass_remainder_to_consumer : forall 'left 'right,
  0 <= 'left & 'left < 2 ^ 256 & 0 <= 'right & 'right < 2 ^ 256.
  (int('left), int('right)) -> unit
function pass_remainder_to_consumer(left, right) = {
  let reduced = tmod_nat(left + right, sizeof(bounded_word_modulus));
  consume_bounded_word(reduced)
}

function main() -> unit = ()
