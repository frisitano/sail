function run(value : byte) -> word = {
  require_flag(value != 0);
  assert(value != 0, "run requires a nonzero byte");
  step(value)
}

function main() -> unit = {
  let _ = run(1);
  ()
}
