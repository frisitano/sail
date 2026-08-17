default Order dec

$include <prelude.sail>

type byte = range(0, 255)
type incrementable_byte = range(0, 254)

enum operation = { Keep, Advance }

function advance(state : incrementable_byte) -> (byte, byte) =
  (state + 1, state)

function choose_pair(
  operation : operation,
  state : incrementable_byte,
) -> (byte, byte, bool) = {
  let state_value : byte = state;
  let zero : byte = 0;
  let pair : (byte, byte) =
    match operation {
      Keep => (state_value, zero),
      Advance => advance(state),
    };
  let (state_after, value) = pair;
  (state_after, value, state_after == value)
}
