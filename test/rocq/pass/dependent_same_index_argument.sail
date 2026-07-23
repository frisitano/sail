default Order dec

$include <prelude.sail>

struct Cursor('maximum : Int), 0 < 'maximum = {
  count : range(0, 'maximum),
  position : range(0, 'maximum),
}

union exception = { OutOfRange : unit }

val cursor_position : forall ('maximum : Int), 0 < 'maximum.
  Cursor('maximum) -> range(0, 'maximum - 1)
function cursor_position(cursor) = {
  let count = cursor.count;
  let position = cursor.position;
  if position < count then position else throw(OutOfRange())
}

val cursor_empty : forall ('maximum : Int), 0 < 'maximum. Cursor('maximum) -> bool
function cursor_empty(cursor) = cursor.count <= cursor.position

val consume_position : int -> int
function consume_position(position) = position

val rebuild_then_read : forall ('maximum : Int), 0 < 'maximum.
  Cursor('maximum) -> option(int)
function rebuild_then_read(cursor) = {
  let next_cursor : Cursor('maximum) = struct {
    count = cursor.count,
    position = cursor.position,
  };
  if cursor_empty(next_cursor) then None()
  else Some(consume_position(cursor_position(next_cursor)))
}
