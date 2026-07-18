default Order dec

$include <prelude.sail>

$[c_repr u256]
newtype almost_u256 = AlmostU256 : bits(255)
