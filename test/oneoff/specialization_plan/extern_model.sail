default Order dec

$include <prelude.sail>

type byte_count = range(0, 255)

val foreign_identity = pure { c: "foreign_identity" } :
  forall 'value, 0 <= 'value. atom('value) -> atom('value)

val generic_foreign_bridge :
  forall 'value, 0 <= 'value. atom('value) -> atom('value)

function generic_foreign_bridge(value) = foreign_identity(value)

function bounded_foreign_bridge(value : byte_count) -> byte_count =
  generic_foreign_bridge(value)

function main() -> unit = ()
