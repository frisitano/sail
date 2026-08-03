#include "evmsail/spec.h"

int main(void)
{
  struct pair value = { .first = 3, .second = 4 };
  evmsail_model_init();
  public_counter = 40;
  return run(2) == 42 && catch_byte(7) == 7 && machine_pick_zero(3) == 0 && pair_sum(value) == 7 ? 0 : 1;
}
