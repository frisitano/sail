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

struct Holder = {
  value : byte
}

type wide_byte = range(0, 511)

struct WideHolder = {
  value : wide_byte
}

struct Pair = {
  left : byte,
  right : byte
}

val consume_byte = pure { c: "consume_byte" } : byte -> unit
val consume_pair = pure { c: "consume_pair" } : Pair -> unit

function field_snapshot_into_call(holder : Holder) -> unit =
  consume_byte(holder.value)

function converted_field_into_external_call(holder : WideHolder) -> byte = {
  let value = holder.value;
  if value <= 255 then external_byte(value) else 0
}

function updated_record_into_call(pair : Pair, value : byte) -> unit =
  consume_pair({ pair with right = value })

function updated_record_into_return(pair : Pair, value : byte) -> Pair =
  { pair with right = value }

function count_four() -> byte = {
  var count : byte = 0;
  foreach (index from 0 to 3) {
    count = tmod_nat(count + 1, 256)
  };
  count
}

function decode_flag(cursor : incrementable_byte) -> (byte, bool) =
  (cursor + 1, cursor == 0)

function finish_flag(state : byte, flag : bool) -> (byte, bits(16)) =
  (state, if flag then 0x0001 else 0x0000)

function forward_flag(cursor : incrementable_byte, state : byte) -> (byte, byte, bits(16)) = {
  let (next, flag) = decode_flag(cursor);
  let (state_after, encoded) = finish_flag(state, flag);
  (next, state_after, encoded)
}
