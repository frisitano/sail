default Order dec

$include <prelude.sail>

val compiler_type_target : unit -> unit

function compiler_type_target() = ()

val use_compiler_type : unit -> unit

function use_compiler_type() = compiler_type_target()

val use_compiler_local : unit -> int

function use_compiler_local() = {
  let local_value : int = 42;
  local_value
}

val use_second_local : unit -> int

function use_second_local() = {
  let local_value : int = 7;
  local_value
}
