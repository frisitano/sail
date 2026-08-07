val host_mix = impure {c: "host_mix_exact"} : (word, byte) -> word
val host_wide_pair = impure {c: "host_wide_pair_exact"} : (word, word) -> bool
val host_jumpdest_alloc = impure {c: "test_jumpdest_alloc"} : byte -> jump_table_index
val host_reset = impure {c: "host_reset_exact"} : unit -> unit

enum fatal_reason = { TestFatal }

val fatal_error = impure {c: "fatal_error"} :
  forall ('a : Type). fatal_reason -> 'a
function fatal_error(_reason) = exit(())

function always_fatal() -> unit = fatal_error(TestFatal)

function reset_via_host() -> unit = host_reset()

function guarded_reset(enabled : bool) -> unit =
  if enabled then host_reset() else ()

function reset_when_pair(left : word, right : word) -> unit =
  if not_bool(host_wide_pair(left, right)) then () else host_reset()

function reset_then_mix(value : word, tag : byte) -> word = {
  host_reset();
  host_mix(value, tag)
}

function guarded_host_mix(value : word, tag : byte, off : byte, len : byte) -> word =
  if off < len then host_mix(value, tag) else 0

function guarded_host_slice(value : word, tag : byte, segment : byte_slice, off : byte) -> word =
  if off < segment.len then host_mix(value, tag) else 0

function guarded_wide_offset(value : word, off : wide_word) -> word =
  if off < 256 then {
    let tag : byte = off;
    host_mix(value, tag)
  } else 0

function widened_host_call(small : byte, medium : halfword) -> bool =
  host_wide_pair(small, medium)

val allocated_jumpdest : byte -> jump_table_index
function allocated_jumpdest(off) = host_jumpdest_alloc(off)
