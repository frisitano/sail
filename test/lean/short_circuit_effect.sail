default Order dec

$include <prelude.sail>

register EFFECT_COUNT : nat

function effectful_false() -> bool = {
  EFFECT_COUNT = EFFECT_COUNT + 1;
  false
}

function effectful_true() -> bool = {
  EFFECT_COUNT = EFFECT_COUNT + 1;
  true
}

function short_circuit_and(left : bool) -> bool =
  left & effectful_false()

function short_circuit_or(left : bool) -> bool =
  left | effectful_true()

function short_circuit_and_nested(left : bool) -> bool =
  left & not_bool(effectful_true())

function short_circuit_or_nested(left : bool) -> bool =
  left | not_bool(effectful_false())
