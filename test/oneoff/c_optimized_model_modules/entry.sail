function run(value : byte) -> word = {
  assert(value != 0, "run requires a nonzero byte");
  step(value)
}
