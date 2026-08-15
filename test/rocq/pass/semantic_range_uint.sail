default Order dec

$include <prelude.sail>

type bounded_word = range(0, 2 ^ 256 - 1)

val make_bounded_word : forall 'value, 0 <= 'value & 'value < 2 ^ 256.
  int('value) -> bounded_word
function make_bounded_word(value) = value

function word_from_bits(value : bits(256)) -> bounded_word = {
  let natural_value = unsigned(value);
  make_bounded_word(natural_value)
}

function main() -> unit = ()
