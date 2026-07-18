#ifndef SAIL_TEST_BOUNDED_INT_REPR_H
#define SAIL_TEST_BOUNDED_INT_REPR_H

#include <stdint.h>

static inline uint64_t gas_identity(uint64_t value)
{
  return value;
}

static inline int64_t bounded_i64_identity(int64_t value)
{
  return value;
}

#endif
