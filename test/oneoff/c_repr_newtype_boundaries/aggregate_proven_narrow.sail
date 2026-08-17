default Order dec

$include <prelude.sail>

$[c_repr uint8]
newtype octet = Octet : int

struct wide_octet('value : Int), 0 <= 'value & 'value <= 65535 = {
  raw : int('value),
}

struct octet_box = {
  value : octet,
}

val unpack_octet : octet -> int
function unpack_octet(Octet(value)) = value

val unpack_box : octet_box -> int
function unpack_box(box) = unpack_octet(box.value)

val record_fold : forall 'value, 0 <= 'value & 'value <= 65535.
  wide_octet('value) -> octet
function record_fold(value) = {
  let raw : range(0, 65535) = value.raw;
  if raw <= 255 then {
    var converted : range(0, 255) = 0;
    converted = raw;
    let box : octet_box = struct { value = Octet(converted) };
    box.value
  } else Octet(0)
}

val converted_tuple_fold : forall 'value, 0 <= 'value & 'value <= 65535.
  wide_octet('value) -> octet
function converted_tuple_fold(value) = {
  let raw : range(0, 65535) = value.raw;
  if raw <= 255 then {
    let converted : range(0, 255) = raw;
    let pair : (octet, octet) = (Octet(0), Octet(converted));
    let (_, result) = pair;
    result
  } else Octet(0)
}

val terminal_sink : forall 'value, 0 <= 'value & 'value <= 65535.
  (wide_octet('value), bool) -> octet_box
function terminal_sink(value, select_value) = {
  let raw : range(0, 65535) = value.raw;
  if raw <= 255 then {
    let converted : range(0, 255) = raw;
    var box : octet_box = struct { value = Octet(0) };
    if select_value then box = struct { value = Octet(converted) }
    else box = struct { value = Octet(1) };
    box
  } else struct { value = Octet(0) }
}

val propagated_aggregate : forall 'value, 0 <= 'value & 'value <= 65535.
  wide_octet('value) -> int
function propagated_aggregate(value) = {
  let raw : range(0, 65535) = value.raw;
  if raw <= 255 then {
    let converted : range(0, 255) = raw;
    let narrowed = Octet(converted);
    let box : octet_box = struct { value = narrowed };
    unpack_box(box)
  } else 0
}

val initialized_local : forall 'value, 0 <= 'value & 'value <= 65535.
  wide_octet('value) -> int
function initialized_local(value) = {
  let raw : range(0, 65535) = value.raw;
  if raw <= 255 then {
    let converted : range(0, 255) = raw;
    let narrowed : octet = Octet(converted);
    unpack_octet(narrowed) + unpack_octet(narrowed)
  } else 0
}

function main() -> unit = ()
