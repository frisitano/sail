default Order dec

$include <prelude.sail>

type bounded_word = range(0, 2 ^ 256 - 1)

function consume_bounded_word(value : bounded_word) -> unit = ()

function main() -> unit = ()
