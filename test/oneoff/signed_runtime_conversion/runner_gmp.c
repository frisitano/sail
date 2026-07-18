#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "sail.h"

#define CHECK(condition)                                                               \
  do {                                                                                 \
    if (!(condition)) {                                                                \
      fprintf(stderr, "check failed at %s:%d: %s\n", __FILE__, __LINE__, #condition); \
      return 1;                                                                        \
    }                                                                                  \
  } while (0)

int main(int argc, char **argv) {
  sail_int value;
  mpz_init(value);

  if (argc == 2) {
    if (strcmp(argv[1], "high") == 0)
      mpz_set_str(value, "9223372036854775808", 10);
    else
      mpz_set_str(value, "-9223372036854775809", 10);
    (void)CONVERT_OF(mach_int, sail_int)(value);
    mpz_clear(value);
    return 0;
  }

  mpz_set_si(value, -42);
  CHECK(CREATE_OF(mach_int, sail_int)(value) == INT64_C(-42));
  CHECK(CONVERT_OF(mach_int, sail_int)(value) == INT64_C(-42));
  mpz_set_str(value, "-9223372036854775808", 10);
  CHECK(CREATE_OF(mach_int, sail_int)(value) == INT64_MIN);
  mpz_set_str(value, "9223372036854775807", 10);
  CHECK(CONVERT_OF(mach_int, sail_int)(value) == INT64_MAX);

  mpz_clear(value);
  return 0;
}
