#ifndef C_REPR_NAT_NEWTYPE_H
#define C_REPR_NAT_NEWTYPE_H

#include <stdint.h>

static inline uint64_t c_repr_nat_newtype_increment(uint64_t value)
{
  return value + UINT64_C(1);
}

#endif
