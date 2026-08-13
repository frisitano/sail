default Order dec

$include <prelude.sail>

type invalid_state_word = range(0, 255)

enum invalid_state_status = { InvalidStateContinue, InvalidStateFailed }

function invalid_state_order(
  state_word : invalid_state_word,
  state_flag : bool,
) -> (bool, invalid_state_word, invalid_state_status) =
  (state_flag, state_word, InvalidStateContinue)

function state_last_product(state_word : invalid_state_word) -> (bool, invalid_state_word) =
  (true, state_word)
