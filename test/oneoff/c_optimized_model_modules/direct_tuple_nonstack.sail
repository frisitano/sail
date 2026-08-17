default Order dec

$include <prelude.sail>

type byte = range(0, 255)

function nonstack_first(value : byte) -> (list(byte), byte) =
  ([|1, 2|], value)

function nonstack_first_value(value : byte) -> byte = {
  let (items, result) = nonstack_first(value);
  match items {
    [|1, 2|] => result,
    _ => 0,
  }
}
