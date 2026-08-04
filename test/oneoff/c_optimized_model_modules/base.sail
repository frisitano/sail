default Order dec

$include <prelude.sail>

type byte = range(0, 255)
type byte_offset = range(0, 254)
type word = range(0, 4294967295)
type fixed_index = range(0, 16)
type four_index = range(0, 3)
type maybe_fixed_index = range(0, 17)
type fixed_id = range(0, 256)
type jump_table_index = range(0, 255)

$[c_repr byte_pointer]
type direct_jump_table_index = range(0, 255)

let EMPTY_DIRECT_JUMP_TABLE : direct_jump_table_index = 0

struct pair = {
  first : byte,
  second : byte,
}

struct byte_slice = {
  bytes : byte,
  len : byte,
}

struct byte_slice_small = {
  bytes : byte_offset,
  len : byte,
}

struct analyzed_code = {
  bytes : byte_offset,
  len : byte,
  jumpdests : jump_table_index,
}

type four_bytes = vector(4, byte)
type fixed_ids = vector(17, fixed_id)

struct fixed_ids_box = {
  ids : fixed_ids,
}

union exception = {
  E_byte : byte,
}

function add_byte(left : byte, right : byte) -> range(0, 510) = left + right

function pair_sum(value : pair) -> range(0, 510) = value.first + value.second

function byte_slice_at(off : byte, len : byte) -> byte_slice =
  struct { bytes = off, len = len }

function byte_slice_small_at(off : byte_offset, len : byte) -> byte_slice_small =
  struct { bytes = off, len = len }

function byte_slice_same_start(left : byte_slice, right : byte_slice) -> bool =
  left.bytes == right.bytes

function byte_slice_next(value : byte_slice_small) -> byte_slice = {
  let off = value.bytes;
  struct { bytes = off + 1, len = value.len }
}

function byte_slice_advance(value : byte_slice_small) -> byte_slice =
  struct { bytes = value.bytes + 1, len = value.len }

function byte_slice_distance(left : byte_slice, right : byte_slice) -> range(-255, 255) =
  left.bytes - right.bytes

val jumpdest_from_offset : byte_offset -> jump_table_index
function jumpdest_from_offset(off) = off

val empty_jumpdest : unit -> jump_table_index
function empty_jumpdest() = 0

val empty_direct_jumpdest : unit -> direct_jump_table_index
function empty_direct_jumpdest() = 0

val analyzed_code_at : (byte_offset, byte, jump_table_index) -> analyzed_code
function analyzed_code_at(bytes, len, jumpdests) =
  struct { bytes = bytes, len = len, jumpdests = jumpdests }

function analyzed_code_copy(code : analyzed_code) -> analyzed_code =
  struct { bytes = code.bytes, len = code.len, jumpdests = code.jumpdests }

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
