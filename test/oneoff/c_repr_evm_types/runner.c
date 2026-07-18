#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "model.h"

void model_init(void);
void model_fini(void);

#define CHECK(condition)                                                                    \
  do {                                                                                      \
    if (!(condition)) {                                                                     \
      fprintf(stderr, "check failed at %s:%d: %s\n", __FILE__, __LINE__, #condition);      \
      return 1;                                                                             \
    }                                                                                       \
  } while (0)

static bool u256_is(const sail_u256 value, const uint64_t limb0, const uint64_t limb1,
                    const uint64_t limb2, const uint64_t limb3) {
  return value.limbs[0] == limb0 && value.limbs[1] == limb1 && value.limbs[2] == limb2 &&
         value.limbs[3] == limb3;
}

int main(void) {
  _Static_assert(sizeof(sail_u256) == 32, "u256 must be four native 64-bit limbs");
  _Static_assert(sizeof(sail_fixed_bytes_20) == 20, "B160/address must be exactly 20 bytes");
  _Static_assert(sizeof(sail_fixed_bytes_32) == 32, "B256 must be exactly 32 bytes");
  _Static_assert(sizeof(sail_fixed_bytes_48) == 48, "B384 must be exactly 48 bytes");

  model_init();

  const sail_u256 zero = {{0, 0, 0, 0}};
  const sail_u256 one = {{1, 0, 0, 0}};
  const sail_u256 limb_carry = {{UINT64_MAX, 0, 0, 0}};
  const sail_u256 carried = zu256_add(limb_carry, one);
  CHECK(u256_is(carried, 0, 1, 0, 0));
  CHECK(u256_is(zu256_sub(carried, one), UINT64_MAX, 0, 0, 0));

  const sail_u256 one_limb_up = {{0, 1, 0, 0}};
  const sail_u256 three = {{3, 0, 0, 0}};
  CHECK(u256_is(zu256_mul(one_limb_up, three), 0, 3, 0, 0));

  const sail_u256 alternating = {{UINT64_C(0x0f0f0f0f0f0f0f0f), UINT64_MAX, 0, 0}};
  const sail_u256 low_mask = {{UINT64_C(0xff00ff00ff00ff00), 0, UINT64_MAX, 0}};
  CHECK(u256_is(zu256_and(alternating, low_mask), UINT64_C(0x0f000f000f000f00), 0, 0, 0));
  CHECK(u256_is(zu256_or(alternating, low_mask), UINT64_C(0xff0fff0fff0fff0f), UINT64_MAX,
                UINT64_MAX, 0));
  CHECK(u256_is(zu256_xor(alternating, low_mask), UINT64_C(0xf00ff00ff00ff00f), UINT64_MAX,
                UINT64_MAX, 0));
  CHECK(u256_is(zu256_not(zero), UINT64_MAX, UINT64_MAX, UINT64_MAX, UINT64_MAX));
  CHECK(zu256_equal(one, one));
  CHECK(!zu256_equal(one, zero));

  const sail_u256 shifted = zu256_shift_left(one, 65);
  CHECK(u256_is(shifted, 0, 2, 0, 0));
  CHECK(u256_is(zu256_shift_right(shifted, 65), 1, 0, 0, 0));
  CHECK(u256_is(zu256_shift_left(one, 256), 0, 0, 0, 0));
  CHECK(u256_is(zu256_shift_right(one, 256), 0, 0, 0, 0));

  const sail_u256 sign_bit = {{0, 0, 0, UINT64_C(0x8000000000000000)}};
  CHECK(zu256_bit(sign_bit, 255) == 1);
  CHECK(zu256_bit(sign_bit, 254) == 0);
  CHECK(u256_is(zu256_arith_shift_right(sign_bit, 255), UINT64_MAX, UINT64_MAX, UINT64_MAX,
                UINT64_MAX));

  CHECK(u256_is(zu256_from_byte(UINT64_C(0xab)), UINT64_C(0xab), 0, 0, 0));
  const sail_u256 sliced = {{UINT64_C(0x1234), UINT64_C(0x1122334455667788), 0, 0}};
  CHECK(zu256_low_byte(sliced) == UINT64_C(0x34));
  CHECK(zu256_middle_word(sliced) == UINT64_C(0x1122334455667788));
  CHECK(zlimb_unsigned(UINT64_MAX) == UINT64_MAX);
  CHECK(zlimb_signed(UINT64_MAX) == INT64_C(-1));
  CHECK(zlimb_shift_left(UINT64_C(1), UINT64_C(63)) == (UINT64_C(1) << 63));
  CHECK(zlimb_shift_left(UINT64_C(1), UINT64_C(64)) == UINT64_C(0));
  CHECK(zlimb_shift_right((UINT64_C(1) << 63), UINT64_C(63)) == UINT64_C(1));
  CHECK(zlimb_shift_right(UINT64_MAX, UINT64_C(64)) == UINT64_C(0));
  CHECK(zbyte_arith_shift_right(UINT64_C(0x80), UINT64_C(1)) == UINT64_C(0xc0));
  CHECK(zbyte_arith_shift_right(UINT64_C(0x80), UINT64_C(8)) == UINT64_C(0xff));
  CHECK(zbyte_arith_shift_right(UINT64_C(0x7f), UINT64_C(8)) == UINT64_C(0));

  sail_fixed_bytes_20 address = {{0}};
  address.bytes[0] = UINT8_C(0x11);
  address.bytes[19] = UINT8_C(0xaa);
  CHECK(zaddress_equal(address, address));
  CHECK(zaddress_byte(address, 0) == UINT64_C(0x11));
  CHECK(zaddress_byte(address, 19) == UINT64_C(0xaa));
  const sail_fixed_bytes_20 updated_address = zaddress_update(address, 19, UINT64_C(0xbb));
  CHECK(updated_address.bytes[19] == UINT8_C(0xbb));
  CHECK(address.bytes[19] == UINT8_C(0xaa));
  CHECK(zb160_equal(address, address));

  sail_fixed_bytes_32 hash = {{0}};
  hash.bytes[31] = UINT8_C(0xcc);
  CHECK(zb256_equal(hash, hash));

  sail_fixed_bytes_48 b384 = {{0}};
  b384.bytes[47] = UINT8_C(0xee);
  CHECK(zb384_equal(b384, b384));
  CHECK(zb384_byte(b384, 47) == UINT64_C(0xee));
  const sail_fixed_bytes_48 updated_b384 = zb384_update(b384, 47, UINT64_C(0x44));
  CHECK(updated_b384.bytes[47] == UINT8_C(0x44));
  CHECK(b384.bytes[47] == UINT8_C(0xee));

  CHECK(zbytes20_inc_byte(address, 19) == UINT64_C(0xaa));
  const sail_fixed_bytes_20 updated_inc = zbytes20_inc_update(address, 0, UINT64_C(0xdd));
  CHECK(updated_inc.bytes[0] == UINT8_C(0xdd));
  CHECK(address.bytes[0] == UINT8_C(0x11));
  CHECK(zaddress_equal(zkeep_bytes20_inc(address), address));

  model_fini();
  return 0;
}
