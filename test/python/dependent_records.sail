default Order dec

$include <prelude.sail>

type valid_cursor_maximum('maximum : Int) -> Bool =
  0 < 'maximum & 'maximum <= 16

struct BoundedCursor('maximum : Int), valid_cursor_maximum('maximum) = {
  count : range(0, 'maximum),
  position : range(0, 'maximum - 1)
}

val make_bounded_cursor : (range(0, 8), range(0, 7)) -> BoundedCursor(8)
function make_bounded_cursor(count, position) =
  struct { count = count, position = position }

val copy_bounded_cursor : forall 'maximum, valid_cursor_maximum('maximum).
  BoundedCursor('maximum) -> BoundedCursor('maximum)
function copy_bounded_cursor(cursor) =
  struct { count = cursor.count, position = cursor.position }

type conditional_limit('fork : Int, 'denominator : Int) = int(
  if 'fork < 11 then 0 else 256 * 'denominator
)

struct ConditionalProfile('fork : Int, 'denominator : Int) = {
  fork : int('fork),
  denominator : int('denominator),
  limit : conditional_limit('fork, 'denominator),
}

val make_conditional_profile :
  forall 'fork 'denominator.
  (int('fork), int('denominator)) ->
  ConditionalProfile('fork, 'denominator)
function make_conditional_profile(fork, denominator) =
  struct {
    fork = fork,
    denominator = denominator,
    limit = if fork < 11 then 0 else 256 * denominator,
  }

type ItemCount('maximum : Int) = range(0, 'maximum)

struct RenamedRecordQuantifier('maximum : Int) = {
  count : ItemCount('maximum),
}

val make_renamed_record_quantifier : forall 'limit.
  ItemCount('limit) -> RenamedRecordQuantifier('limit)
function make_renamed_record_quantifier(count) =
  struct { count = count }

val update_renamed_record_quantifier : forall 'limit.
  (RenamedRecordQuantifier('limit), ItemCount('limit)) -> RenamedRecordQuantifier('limit)
function update_renamed_record_quantifier(record, count) =
  { record with count = count }
