default Order dec

$include <prelude.sail>

type region_bound : Int = 16

type valid_range('off : Int, 'len : Int) -> Bool =
  0 <= 'off & 0 <= 'len & 'off + 'len <= region_bound

struct CheckedRangeFields('off : Int, 'len : Int),
  valid_range('off, 'len) = {
  off : int('off),
  len : int('len),
}

val checked_range_fields : forall 'off 'len, valid_range('off, 'len).
  (int('off), int('len)) -> CheckedRangeFields('off, 'len)
function checked_range_fields(off, len) = struct { off = off, len = len }

val pack_range : (int, int) -> option({
  'off 'len, valid_range('off, 'len). CheckedRangeFields('off, 'len)
})
function pack_range(off, len) =
  if 0 <= off & 0 <= len & off + len <= 16 then
    {
      let fields = checked_range_fields(off, len);
      Some(fields)
    }
  else
    None()

function main() -> unit = ()
