val host_mix = impure {c: "host_mix_exact"} : (word, byte) -> word
val host_jumpdest_alloc = impure {c: "test_jumpdest_alloc"} : byte -> jump_table_index

val allocated_jumpdest : byte -> jump_table_index
function allocated_jumpdest(off) = host_jumpdest_alloc(off)
