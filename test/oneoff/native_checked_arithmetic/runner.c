#include "native_checked_arithmetic.c"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int safe_cases(void) {
  if (zchecked_u64_add(UINT64_C(2), UINT64_C(3)) != UINT64_C(5)) return 1;
  if (zchecked_u64_sub(UINT64_C(5), UINT64_C(3)) != UINT64_C(2)) return 2;
  if (zchecked_u64_mul(UINT64_C(6), UINT64_C(7)) != UINT64_C(42)) return 3;
  if (zchecked_u64_div(UINT64_C(13), UINT64_C(5)) != UINT64_C(2)) return 4;
  if (zchecked_u64_mod(UINT64_C(13), UINT64_C(5)) != UINT64_C(3)) return 5;
  if (zchecked_i64_add(INT64_C(-7), INT64_C(4)) != INT64_C(-3)) return 6;
  if (zchecked_i64_sub(INT64_C(-7), INT64_C(4)) != INT64_C(-11)) return 7;
  if (zchecked_i64_mul(INT64_C(-6), INT64_C(7)) != INT64_C(-42)) return 8;
  if (zchecked_i64_div(INT64_C(-13), INT64_C(5)) != INT64_C(-2)) return 9;
  if (zchecked_i64_mod(INT64_C(-13), INT64_C(5)) != INT64_C(-3)) return 10;
  return 0;
}

int main(int argc, char **argv) {
  if (argc == 1) return safe_cases();
  if (strcmp(argv[1], "uadd") == 0) (void)zchecked_u64_add(UINT64_MAX, UINT64_C(1));
  else if (strcmp(argv[1], "usub") == 0) (void)sail_checked_u64_sub(UINT64_C(0), UINT64_C(1));
  else if (strcmp(argv[1], "umul") == 0) (void)zchecked_u64_mul(UINT64_MAX, UINT64_C(2));
  else if (strcmp(argv[1], "udiv") == 0) (void)sail_checked_u64_div(UINT64_C(1), UINT64_C(0));
  else if (strcmp(argv[1], "umod") == 0) (void)sail_checked_u64_mod(UINT64_C(1), UINT64_C(0));
  else if (strcmp(argv[1], "iadd") == 0) (void)zchecked_i64_add(INT64_MAX, INT64_C(1));
  else if (strcmp(argv[1], "isub") == 0) (void)zchecked_i64_sub(INT64_MIN, INT64_C(1));
  else if (strcmp(argv[1], "imul") == 0) (void)zchecked_i64_mul(INT64_MIN, INT64_C(-1));
  else if (strcmp(argv[1], "idiv") == 0) (void)zchecked_i64_div(INT64_MIN, INT64_C(-1));
  else if (strcmp(argv[1], "imod") == 0) (void)zchecked_i64_mod(INT64_MIN, INT64_C(-1));
  else return 64;
  return 65;
}
