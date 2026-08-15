default Order dec

$include <prelude.sail>

type bounded_byte = range(0, 255)

function bounded_byte_from_bits(value : bits(8)) -> bounded_byte = unsigned(value)

function consume_bounded_byte(value : bounded_byte) -> unit = ()

function pass_result_to_consumer(value : bits(8)) -> unit = {
  let bounded_value = bounded_byte_from_bits(value);
  consume_bounded_byte(bounded_value)
}

function main() -> unit = ()
