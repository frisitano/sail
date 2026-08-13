default Order dec

$include <prelude.sail>

type state_word = range(0, 255)

enum state_passing_status = { StatePassingContinue, StatePassingFailed }

function update_state(state : state_word, fail : bool) -> (state_word, state_passing_status) =
  if fail then (0, StatePassingFailed) else (state, StatePassingContinue)

function discard_updated_state(state : state_word, fail : bool) -> state_passing_status = {
  let (_, status) = update_state(state, fail);
  status
}
