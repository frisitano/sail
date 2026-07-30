struct SplitValue = {
  value : int
}

let SPLIT_INITIAL : int = 1

register SPLIT_COUNTER : int = SPLIT_INITIAL

val split_increment : int -> int
function split_increment(value) = value + 1

val choose_named : bool -> int
function choose_named(condition) = {
  let selected = if condition then 1 else 2;
  selected
}

val split_counter_reset : unit -> unit
function split_counter_reset() = {
  SPLIT_COUNTER = SPLIT_INITIAL
}

val split_cycle : int -> int
function split_cycle(value) = split_twice(value) - 2
