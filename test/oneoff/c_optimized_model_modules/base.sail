default Order dec

$include <prelude.sail>

type byte = range(0, 255)
type word = range(0, 4294967295)
type fixed_index = range(0, 16)
type maybe_fixed_index = range(0, 17)
type fixed_id = range(0, 256)

struct pair = {
  first : byte,
  second : byte,
}

type four_bytes = vector(4, byte)
type fixed_ids = vector(17, fixed_id)

union exception = {
  E_byte : byte,
}

function add_byte(left : byte, right : byte) -> range(0, 510) = left + right

function pick_fixed_id(index : fixed_index) -> fixed_id = {
  let ids : fixed_ids = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 256];
  ids[index]
}

function pick_initialized_id(index : fixed_index) -> fixed_id = {
  let ids : fixed_ids = vector_init(17, 256);
  ids[index]
}

function pick_guarded_id(index : maybe_fixed_index) -> fixed_id =
  if index < 17 then {
    let ids : fixed_ids = vector_init(17, 256);
    ids[index]
  } else 0

function catch_byte(value : byte) -> byte =
  try throw(E_byte(value)) catch {
    E_byte(caught) => caught,
  }
