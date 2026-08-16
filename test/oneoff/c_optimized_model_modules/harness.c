#include "evmsail/spec.h"

const uint8_t *test_bytes_at(uint64_t);
uint8_t *test_jumpdests_at(uint64_t);

static bool check_composed_guard(bool reversed, uint8_t value, bool fallback,
                                 bool expected_write) {
  public_counter = UINT8_C(9);
  uint8_t returned =
      reversed ? one_use_guard_in_reversed_composed_condition(value, fallback)
               : one_use_guard_in_composed_condition(value, fallback);
  return returned == value &&
         public_counter == (expected_write ? UINT8_C(0) : UINT8_C(9));
}

int main(void) {
  struct pair value = {.first = 3, .second = 4};
  struct byte_slice first = byte_slice_at(3, 2);
  struct byte_slice second = byte_slice_next(byte_slice_small_at(6, 2));
  struct analyzed_code code =
      analyzed_code_copy(analyzed_code_at(4, 9, jumpdest_from_offset(12)));
  TestList list = {.count = 3};
  evmsail_model_init();
  public_counter = 40;
  return run(2) == 42 && catch_byte(7) == 7 && machine_pick_zero(3) == 0 &&
                 pair_sum(value) == 7 && preserve_counter_snapshot(9) == 9 &&
                 public_counter == 0 && first.bytes == test_bytes_at(3) &&
                 second.bytes == test_bytes_at(7) &&
                 byte_slice_same_start(first, byte_slice_at(3, 9)) &&
                 byte_slice_distance(second, first) == 4 &&
                 code.bytes == test_bytes_at(4) && code.len == 9 &&
                 code.jumpdests == test_jumpdests_at(12) &&
                 empty_jumpdest() == NULL && empty_direct_jumpdest() == NULL &&
                 allocated_jumpdest(5) == test_jumpdests_at(5) &&
                 canonical_list_count_after_identity(list) == 3 &&
                 check_composed_guard(false, UINT8_C(0), false, false) &&
                 check_composed_guard(false, UINT8_C(0), true, true) &&
                 check_composed_guard(false, UINT8_C(1), false, true) &&
                 check_composed_guard(false, UINT8_C(1), true, true) &&
                 check_composed_guard(true, UINT8_C(0), false, false) &&
                 check_composed_guard(true, UINT8_C(0), true, true) &&
                 check_composed_guard(true, UINT8_C(1), false, true) &&
                 check_composed_guard(true, UINT8_C(1), true, true) &&
                 terminal_signed_byte_or_fatal(UINT64_C(0), true, true) ==
                     INT8_C(0) &&
                 terminal_signed_byte_or_fatal(UINT64_C(0x7f), true, true) ==
                     INT8_C(127) &&
                 terminal_signed_byte_or_fatal(UINT64_C(0xff), true, true) ==
                     INT8_C(-1) &&
                 terminal_signed_halfword_or_fatal(UINT64_C(0), true, true) ==
                     INT16_C(0) &&
                 terminal_signed_halfword_or_fatal(UINT64_C(0x7fff), true,
                                                   true) == INT16_C(32767) &&
                 terminal_signed_halfword_or_fatal(UINT64_C(0x8000), true,
                                                   true) == INT16_C(-32768) &&
                 terminal_signed_word_or_fatal(UINT64_C(0), true, true) ==
                     INT32_C(0) &&
                 terminal_signed_word_or_fatal(UINT64_C(0x7fffffff), true,
                                               true) == INT32_C(2147483647) &&
                 terminal_signed_word_or_fatal(UINT64_C(0xffffffff), true,
                                               true) == INT32_C(-1) &&
                 terminal_signed_doubleword_or_fatal(UINT64_C(0), true, true) ==
                     INT64_C(0) &&
                 terminal_signed_doubleword_or_fatal(
                     UINT64_C(0x7fffffffffffffff), true, true) == INT64_MAX &&
                 terminal_signed_doubleword_or_fatal(UINT64_MAX, true, true) ==
                     INT64_C(-1) &&
                 recover_throwing_signed_byte(UINT64_C(0x80), false) ==
                     INT8_C(-128) &&
                 recover_throwing_signed_byte(UINT64_C(0x7f), true) ==
                     INT8_C(-1)
             ? 0
             : 1;
}
