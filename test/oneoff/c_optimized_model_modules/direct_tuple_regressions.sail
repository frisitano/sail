default Order dec

$include <prelude.sail>

type byte = range(0, 255)
enum step_status = { StepContinue, StepFailed }

union exception = {
  TupleFailure : byte,
}

function inner_pair(selector : bool) -> (byte, byte) =
  if selector then (11, 22) else (33, 44)

function repeated_pair(selector : bool) -> (byte, byte, byte) = {
  let (first, second) = inner_pair(selector);
  (first, second, first)
}

function repeated_pair_value(selector : bool) -> byte = {
  let (first, second, repeated) = repeated_pair(selector);
  if first == repeated then second else 0
}

function reordered_pair(selector : bool) -> (byte, byte) = {
  let (first, second) = inner_pair(selector);
  (second, first)
}

function reordered_pair_value(selector : bool) -> byte = {
  let (second, first) = reordered_pair(selector);
  if selector then {
    if (first == 11) & (second == 22) then first else 0
  } else if (first == 33) & (second == 44) then first else 0
}

function unit_tail(value : byte) -> (byte, unit) = (value, ())

function unit_tail_value(value : byte) -> byte = {
  let (result, _) = unit_tail(value);
  result
}

function two_state_step(
  left : byte,
  right : byte,
  fail : bool,
) -> (byte, byte, step_status) =
  if fail then (left, right, StepFailed) else (11, 22, StepContinue)

function aliased_inout_value(value : byte) -> byte = {
  let (left, right, status) = two_state_step(value, value, false);
  match status {
    StepContinue => if (left == 11) & (right == 22) then value else 0,
    StepFailed => 0,
  }
}

function throwing_inner_pair(selector : bool, should_throw : bool) -> (byte, byte) = {
  if should_throw then throw(TupleFailure(77));
  inner_pair(selector)
}

function throwing_repeated_pair(selector : bool, should_throw : bool) -> (byte, byte, byte) = {
  let (first, second) = throwing_inner_pair(selector, should_throw);
  (first, second, first)
}

function recovered_throwing_pair(selector : bool, should_throw : bool) -> byte =
  try {
    let (first, second, repeated) = throwing_repeated_pair(selector, should_throw);
    if first == repeated then second else 0
  } catch {
    TupleFailure(value) => value,
  }
