default Order dec

$include <prelude.sail>
$include <arith.sail>

type tiny = range(0, 8)
type medium = range(0, 200)

val budgeted_square : forall 'value, 0 <= 'value. atom('value) -> bool

function budgeted_square(value) = value * value <= 64

function tiny_budgeted_square(value : tiny) -> bool =
  budgeted_square(value)

function medium_budgeted_square(value : medium) -> bool =
  budgeted_square(value)
