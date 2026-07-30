default Order dec

$include <prelude.sail>

union exception = {
  Bad : unit,
}

struct Box('n : Int) = {
  value : int('n),
}

type SomeBox = { 'n. Box('n) }

val make_box : int -> SomeBox
function make_box(x) = {
  if x < 0 then throw Bad();
  let (n as 'n) = x;
  let box : Box('n) = struct { value = n };
  box
}

val keep_box : forall 'n. Box('n) -> Box('n)
function keep_box(box) = {
  if box.value == box.value then box else throw Bad()
}

val make_and_keep_box : int -> SomeBox
function make_and_keep_box(x) =
  keep_box(make_box(x))
