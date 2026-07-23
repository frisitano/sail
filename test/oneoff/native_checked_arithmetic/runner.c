#include "native_checked_arithmetic.c"

#include <stdint.h>
#include <stdio.h>

int main(void) {
  sail_int signed_difference;
  CREATE(sail_int)(&signed_difference);
  zsigned_u64_difference(&signed_difference, UINT64_C(0), UINT64_C(96390));
  if (mpz_cmp_si(signed_difference, -96390) != 0) {
    KILL(sail_int)(&signed_difference);
    return 11;
  }
  KILL(sail_int)(&signed_difference);
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
  if (zproven_u64_mul(UINT64_C(6), UINT64_C(7)) != UINT64_C(42)) return 12;
  const __int128 wide = ((__int128)UINT64_MAX) + 14;
  if (zproven_i128_add(wide, -wide) != 0) return 13;
  if (zproven_i128_sub(wide, wide) != 0) return 14;
  if (zproven_i128_mul((__int128)6, -(__int128)7) != -(__int128)42) return 15;
  const __int128 wide_divisor = ((__int128)UINT64_MAX) + 6;
  const sail_u128 wide_value = {{UINT64_C(13), UINT64_C(1)}};
  const sail_u128 wide_divisor_value = {{UINT64_C(5), UINT64_C(1)}};
  if (zproven_i128_div(wide_value, wide_divisor_value) != wide / wide_divisor) return 16;
  if (zproven_i128_mod(wide_value, wide_divisor_value) != wide % wide_divisor) return 17;
  if (!zmixed_i128_u64_lte(-(__int128)1, UINT64_MAX)) return 18;
  if (zmixed_i128_u64_lte(((__int128)UINT64_MAX) + 1, UINT64_MAX)) return 19;
  if (zmixed_u64_i128_lte(UINT64_C(0), -(__int128)1)) return 20;
  if (!zmixed_u64_i128_lte(UINT64_MAX, ((__int128)UINT64_MAX) + 1)) return 21;
  return 0;
}
