default Order dec

$include <prelude.sail>

type word16 = bits(16)

$[c_repr fixed_bytes]
newtype words = Words : vector(20, dec, word16)
