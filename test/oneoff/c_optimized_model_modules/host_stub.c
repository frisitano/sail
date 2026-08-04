#include "evmsail/spec.h"

static uint8_t test_bytes[256];
static uint8_t test_jumpdests[256];

uint8_t *test_bytes_at(uint64_t off)
{
  return test_bytes + off;
}

uint8_t *test_jumpdests_at(uint64_t off)
{
  if (off == 0) return NULL;
  return test_jumpdests + off;
}

uint8_t *test_jumpdest_alloc(uint8_t off)
{
  return test_jumpdests_at(off);
}

uint32_t host_mix_exact(uint32_t word, uint8_t byte)
{
  return word + byte;
}
