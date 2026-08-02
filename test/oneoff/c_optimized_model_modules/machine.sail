register public_counter : word

function step(value : byte) -> word = {
  public_counter = host_mix(public_counter, value);
  public_counter
}
