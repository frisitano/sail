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

val widening_countup : forall 'value, 0 <= 'value <= 511.
  atom('value) -> unit

function widening_countup(value) =
  if value == 511 then () else widening_countup(value + 1)
termination_measure widening_countup(value) = 511 - value

function low_widening_countup(value : range(0, 255)) -> unit =
  widening_countup(value)

function main() -> unit = ()
