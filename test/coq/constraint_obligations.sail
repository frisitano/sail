default Order dec
$include <prelude.sail>

val clamped : forall 'n, 0 <= 'n & 'n < 256. int('n) -> int
function clamped(n) = n + 1

val caller : unit -> int
function caller() = clamped(7)
