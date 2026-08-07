default Order dec

$include <prelude.sail>

val little_endian_u32 : (bits(8), bits(8), bits(8), bits(8)) -> bits(32)

function little_endian_u32(byte0, byte1, byte2, byte3) = {
  let b0 = sail_zero_extend(byte0, 32);
  let b1 = sail_zero_extend(byte1, 32);
  let b2 = sail_zero_extend(byte2, 32);
  let b3 = sail_zero_extend(byte3, 32);
  let shifted1 = sail_shiftleft(b1, 8);
  let shifted2 = sail_shiftleft(b2, 16);
  let shifted3 = sail_shiftleft(b3, 24);
  let high = or_vec(shifted2, shifted3);
  let nonzero = or_vec(shifted1, high);
  or_vec(b0, nonzero)
}

function main((): unit) -> unit = ()
