default Order dec

$include <prelude.sail>

type byte = bits(8)

$[c_repr fixed_bytes]
newtype empty_bytes = EmptyBytes : vector(0, dec, byte)
