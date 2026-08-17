#include "aggregate_proven_narrow.h"
#include "sail.h"

#include <string.h>

void model_init(void);
void model_fini(void);

int main(int argc, char **argv) {
  struct zwide_octet value = {.zraw = UINT16_C(255)};
  bool result_is_expected = true;

  if (argc != 2)
    return 64;
  model_init();
  if (strcmp(argv[1], "record") == 0) {
    result_is_expected = zrecord_fold(value) == UINT8_C(255);
  } else if (strcmp(argv[1], "tuple") == 0) {
    result_is_expected = zconverted_tuple_fold(value) == UINT8_C(255);
  } else if (strcmp(argv[1], "terminal") == 0) {
    result_is_expected = zterminal_sink(value, true).zvalue == UINT8_C(255);
  } else if (strcmp(argv[1], "propagation") == 0) {
    sail_int result;
    CREATE(sail_int)(&result);
    zpropagated_aggregate(&result, value);
    result_is_expected = mpz_cmp_ui(result, 255) == 0;
    KILL(sail_int)(&result);
  } else if (strcmp(argv[1], "initialization") == 0) {
    sail_int result;
    CREATE(sail_int)(&result);
    zinitializzed_local(&result, value);
    result_is_expected = mpz_cmp_ui(result, 510) == 0;
    KILL(sail_int)(&result);
  } else {
    return 64;
  }

  model_fini();
  return result_is_expected ? 0 : 1;
}
