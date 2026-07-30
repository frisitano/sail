default Order dec

$include <prelude.sail>

type existential_int = { 'n. int('n) }

struct IntBox = {
  item : existential_int,
}

val existential_int : forall 'n. int('n) -> existential_int
function existential_int(value) = value

let ONE : existential_int = existential_int(1)

let ONE_BOX : IntBox = struct {
  item = ONE,
}

let ZERO : int(0) = 0

let ZERO_BOX : IntBox = struct {
  item = ZERO,
}

struct SliceFields('off : Int, 'len : Int) = {
  off : int('off),
  len : int('len),
}

type slice = { 'off 'len. SliceFields('off, 'len) }

struct SliceBox = {
  item : slice,
}

val slice_fields : forall 'off 'len. (int('off), int('len)) -> SliceFields('off, 'len)
function slice_fields(off, len) = struct {
  off = off,
  len = len,
}

val make_slice : forall 'off 'len. SliceFields('off, 'len) -> slice
function make_slice(fields) = fields

let EMPTY_SLICE : slice = make_slice(slice_fields(0, 0))

let EMPTY_SLICE_BOX : SliceBox = struct {
  item = EMPTY_SLICE,
}

val touch_slice : forall 'off 'len. SliceFields('off, 'len) -> unit
function touch_slice(_) = ()

let EMPTY_SLICE_TOUCHED : unit = touch_slice(EMPTY_SLICE)
