default Order dec

$include <prelude.sail>

type byte = range(0, 255)

function added_is_nonzero(left : byte, right : byte) -> bool =
  left + right != 0

function called_boolean_guard(left : byte, right : byte) -> byte =
  if added_is_nonzero(left, right) then 1 else 0

val external_predicate = pure { c: "external_predicate" } : byte -> bool

function external_boolean_guard(value : byte) -> byte =
  if external_predicate(value) then 1 else 0
