default Order dec

$include <prelude.sail>

$[c_repr uint64]
val not_a_newtype : int -> int

function not_a_newtype(value) = value
