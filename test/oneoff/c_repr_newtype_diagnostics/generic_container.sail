default Order dec

$include <prelude.sail>
$include <arith.sail>

type bounded = range(0, 255)

function keep(value : bounded) -> bounded = value

function main() -> unit = ()
