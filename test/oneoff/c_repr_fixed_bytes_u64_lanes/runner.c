#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "model.h"

void model_init(void);
void model_fini(void);

#define CHECK(condition)                                                                           \
  do {                                                                                             \
    if (!(condition)) {                                                                            \
      fprintf(stderr, "check failed at %s:%d: %s\n", __FILE__, __LINE__, #condition);              \
      return 1;                                                                                    \
    }                                                                                              \
  } while (0)

static bool u256_is(const u256 value, const uint64_t limb0, const uint64_t limb1,
                    const uint64_t limb2, const uint64_t limb3)
{
  return value.limbs[0] == limb0 && value.limbs[1] == limb1 && value.limbs[2] == limb2 &&
         value.limbs[3] == limb3;
}

int main(void)
{
  _Static_assert(sizeof(bytes20) == 24, "lane-backed address must use three native lanes");
  _Static_assert(sizeof(bytes32) == 32, "lane-backed B256 must use four native lanes");

  model_init();

  const bytes20 address = {{UINT64_C(0x11), 0, UINT64_C(0xaa000000)}};
  CHECK(zlane_address_byte(address, 0) == UINT64_C(0x11));
  CHECK(zlane_address_byte(address, 19) == UINT64_C(0xaa));
  CHECK(zlane_address_equal(address, address));
  const bytes20 updated_address = zlane_address_update(address, 19, UINT64_C(0xbb));
  CHECK(zlane_address_byte(updated_address, 19) == UINT64_C(0xbb));
  CHECK(zlane_address_byte(address, 19) == UINT64_C(0xaa));
  CHECK(!zlane_address_equal(address, updated_address));

  const bytes32 hash = {{UINT64_C(0x22), 0, 0, UINT64_C(0xcc00000000000000)}};
  CHECK(zlane_b256_equal(hash, hash));
  CHECK(u256_is(zlane_b256_to_u256(hash), UINT64_C(0x22), 0, 0, UINT64_C(0xcc00000000000000)));
  const bytes32 roundtrip_hash = zu256_to_lane_b256(zlane_b256_to_u256(hash));
  CHECK(zlane_b256_equal(roundtrip_hash, hash));
  const bytes32 filled_hash = zlane_b256_fill(UINT64_C(0x5a));
  CHECK(filled_hash.lanes[0] == UINT64_C(0x5a5a5a5a5a5a5a5a));
  CHECK(filled_hash.lanes[3] == UINT64_C(0x5a5a5a5a5a5a5a5a));

  model_fini();
  return 0;
}
