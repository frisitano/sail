#include "evmsail/spec.h"

uint8_t *test_bytes_at(uint64_t);
uint8_t *test_jumpdests_at(uint64_t);

int main(void)
{
  struct pair value = { .first = 3, .second = 4 };
  struct byte_slice first = byte_slice_at(3, 2);
  struct byte_slice second = byte_slice_next(byte_slice_small_at(6, 2));
  struct analyzed_code code = analyzed_code_copy(analyzed_code_at(4, 9, jumpdest_from_offset(12)));
  evmsail_model_init();
  public_counter = 40;
  return run(2) == 42 && catch_byte(7) == 7 && machine_pick_zero(3) == 0 && pair_sum(value) == 7
             && first.bytes == test_bytes_at(3) && second.bytes == test_bytes_at(7)
             && byte_slice_same_start(first, byte_slice_at(3, 9))
             && byte_slice_distance(second, first) == 4
             && code.bytes == test_bytes_at(4) && code.len == 9
             && code.jumpdests == test_jumpdests_at(12)
             && empty_jumpdest(UNIT) == NULL && EMPTY_DIRECT_JUMP_TABLE == NULL
             && empty_direct_jumpdest(UNIT) == NULL
             && allocated_jumpdest(5) == test_jumpdests_at(5)
         ? 0
         : 1;
}
