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
  if (argc == 2) {
    const sail_int beyond = ((sail_int)INT64_MAX) + 1;
    const sail_int value = strcmp(argv[1], "high") == 0 ? beyond : -beyond - 1;
    (void)CONVERT_OF(mach_int, sail_int)(value);
    return 0;
  }

  CHECK(CREATE_OF(mach_int, sail_int)((sail_int)-42) == INT64_C(-42));
  CHECK(CONVERT_OF(mach_int, sail_int)((sail_int)-42) == INT64_C(-42));
  CHECK(CREATE_OF(mach_int, sail_int)((sail_int)INT64_MIN) == INT64_MIN);
  CHECK(CONVERT_OF(mach_int, sail_int)((sail_int)INT64_MAX) == INT64_MAX);
  return 0;
}
