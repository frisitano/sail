#pragma once

#include <stdint.h>

const uint8_t *test_bytes_at(uint64_t off);
uint8_t *test_jumpdests_at(uint64_t off);

struct pair {
  uint8_t first;
  uint8_t second;
};

struct byte_slice {
  const uint8_t *bytes;
  uint8_t len;
};

struct byte_slice_small {
  const uint8_t *bytes;
  uint8_t len;
};

typedef struct TestBytes {
  const uint8_t *bytes;
  uint8_t len;
} TestBytes;

typedef struct TestList {
  uint8_t count;
} TestList;
