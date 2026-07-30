default Order dec

$include <prelude.sail>

val split_twice : int -> int
$include "lib/helpers.sail"

type SplitValueAlias = SplitValue

function split_twice(value) = split_increment(split_increment(value))

val split_value_score : SplitValueAlias -> int
function split_value_score(value) = value.value

val split_bump : int -> int
function split_bump(amount) = {
  SPLIT_COUNTER = SPLIT_COUNTER + amount;
  SPLIT_COUNTER
}

val split_initial : unit -> int
function split_initial() = SPLIT_INITIAL

val main : unit -> unit
function main() = ()
