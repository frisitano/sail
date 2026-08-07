#include <stdint.h>

#include "model.h"

int main(void)
{
  return zlittle_endian_u32(UINT64_C(0x78), UINT64_C(0x56), UINT64_C(0x34), UINT64_C(0x12))
                 == UINT64_C(0x12345678)
           ? 0
           : 1;
}
