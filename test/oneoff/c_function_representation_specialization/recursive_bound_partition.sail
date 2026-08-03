default Order dec

$include <prelude.sail>
$include <arith.sail>

val descending_to_zero : forall 'value, 0 <= 'value <= 8.
  atom('value) -> unit

function descending_to_zero(value) =
  if value == 0 then () else descending_to_zero(value - 1)
termination_measure descending_to_zero(value) = value

function positive_countdown(value : range(1, 8)) -> unit =
  descending_to_zero(value)

val ascending_to_eight : forall 'value, 0 <= 'value <= 8.
  atom('value) -> unit

function ascending_to_eight(value) =
  if value == 8 then () else ascending_to_eight(value + 1)
termination_measure ascending_to_eight(value) = 8 - value

function low_countup(value : range(0, 1)) -> unit =
  ascending_to_eight(value)

function main() -> unit = ()
