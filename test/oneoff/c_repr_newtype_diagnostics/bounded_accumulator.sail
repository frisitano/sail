default Order dec

$include <prelude.sail>

type accumulator_bound : Int = 3670902070668200771385
type accumulator = range(-accumulator_bound, accumulator_bound)

register total : accumulator = 0

val keep : forall 'delta,
  -accumulator_bound <= 'delta & 'delta <= accumulator_bound.
  atom('delta) -> unit
function keep(delta) = {
  let next = total + delta;
  if (-sizeof(accumulator_bound) <= next) & (next <= sizeof(accumulator_bound)) then {
    total = next
  }
}

val main : unit -> unit
function main() = {
  keep(total);
  keep(100 - 3000)
}
