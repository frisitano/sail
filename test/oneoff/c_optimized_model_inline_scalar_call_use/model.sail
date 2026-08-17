default Order dec

$include <prelude.sail>

type byte = range(0, 255)
type incrementable_byte = range(0, 254)

function next_byte(value : incrementable_byte) -> byte =
  value + 1

function call_in_return_comparison(value : incrementable_byte) -> bool =
  next_byte(value) == 2

function call_in_eager_guard(value : incrementable_byte) -> byte =
  if next_byte(value) == 2 then 3 else 4

val external_byte = pure { c: "external_byte" } : byte -> byte

function external_call_in_return(value : byte) -> bool =
  external_byte(value) == 2

function call_in_short_circuit(value : incrementable_byte, enabled : bool) -> bool =
  enabled & next_byte(value) == 2
