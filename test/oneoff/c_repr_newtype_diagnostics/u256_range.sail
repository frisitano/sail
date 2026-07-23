default Order dec

$include <prelude.sail>

$[c_repr u256]
newtype bounded_u256 = BoundedU256 : range(0, 2 ^ 256 - 1)

val keep : bounded_u256 -> bounded_u256
function keep(value) = value

function main() -> unit = ()
