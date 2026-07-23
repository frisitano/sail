default Order dec

$include <prelude.sail>

type accumulator = int

register total : accumulator = 0

val keep : accumulator -> unit
function keep(delta) = total = total + delta
