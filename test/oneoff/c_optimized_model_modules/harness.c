#include "evmsail/spec.h"

int main(void)
{
  evmsail_model_init();
  public_counter = 40;
  return run(2) == 42 && catch_byte(7) == 7 ? 0 : 1;
}
