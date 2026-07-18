#ifndef SAIL_TEST_C_REPR_NEWTYPE_H
#define SAIL_TEST_C_REPR_NEWTYPE_H

#include <stdint.h>

static inline uint64_t c_repr_newtype_increment(uint64_t value)
{
  return value + UINT64_C(1);
}

#endif
