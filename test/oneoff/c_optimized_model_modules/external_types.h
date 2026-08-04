#pragma once

#include <stdint.h>

uint8_t *test_bytes_at(uint64_t off);
uint8_t *test_jumpdests_at(uint64_t off);

struct pair {
  uint8_t first;
  uint8_t second;
};

struct byte_slice {
  uint8_t *bytes;
  uint8_t len;
};

struct byte_slice_small {
  uint8_t *bytes;
  uint8_t len;
};
