#include "evmsail/spec.h"

int main(void) {
  evmsail_model_init();
  return repeated_pair_value(true) == UINT8_C(22) &&
                 repeated_pair_value(false) == UINT8_C(44) &&
                 reordered_pair_value(true) == UINT8_C(11) &&
                 reordered_pair_value(false) == UINT8_C(33) &&
                 unit_tail_value(UINT8_C(55)) == UINT8_C(55) &&
                 aliased_inout_value(UINT8_C(88)) == UINT8_C(88) &&
                 recovered_throwing_pair(true, false) == UINT8_C(22) &&
                 recovered_throwing_pair(false, true) == UINT8_C(77)
             ? 0
             : 1;
}
