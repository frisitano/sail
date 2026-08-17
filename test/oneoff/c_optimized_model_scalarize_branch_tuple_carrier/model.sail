default Order dec

$include <prelude.sail>

type byte = range(0, 255)
type incrementable_byte = range(0, 254)

enum operation = { Keep, Advance }

struct payload = { value : byte }

function advance(state : incrementable_byte) -> (byte, byte) =
  (state + 1, state)

function advance_managed(state : incrementable_byte) -> (payload, byte) =
  (struct { value = state }, state + 1)

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

function choose_managed(operation : operation, state : incrementable_byte) -> byte = {
  let state_value : byte = state;
  let pair : (payload, byte) =
    match operation {
      Keep => (struct { value = state_value }, state_value),
      Advance => advance_managed(state),
    };
  let (item, state_after) = pair;
  if item.value == state_value then state_after else 0
}
