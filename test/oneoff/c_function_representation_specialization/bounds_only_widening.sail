default Order dec

$include <prelude.sail>
$include <arith.sail>

type byte = range(0, 255)

function lowered_byte(value : byte) -> bits(8) =
  if value <= 8 then get_slice_int(8, value, 0) else get_slice_int(8, value, 0)

function from_wide(value : int) -> bits(8) =
  if 0 <= value & value <= 8 then lowered_byte(value) else 0x00

function main() -> unit = ()
