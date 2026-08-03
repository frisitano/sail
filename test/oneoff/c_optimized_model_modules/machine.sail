register public_counter : word

function machine_pick_zero(index : four_index) -> byte = {
  let bytes : four_bytes = vector_init(4, 0);
  bytes[index]
}

function step(value : byte) -> word = {
  public_counter = host_mix(public_counter, value);
  public_counter
}
