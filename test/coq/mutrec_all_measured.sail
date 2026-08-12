default Order dec
$include <prelude.sail>
val f : int -> int
val g : int -> int
function f(n) = if n <= 0 then 0 else g(n - 1)
function g(n) = if n <= 0 then 0 else f(n - 1)
termination_measure f(n) = n
termination_measure g(n) = n
