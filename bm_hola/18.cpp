#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, a, b, j, flag);

  INIT_a(unknown);
  INIT_b(unknown);
  INIT_flag(unknown);

  j = 0;
  for (b = 0; b < 100; ++b) {
    PRINT_VARS();
    if (flag != 0) j = j + 1;
  }
  PRINT_VARS();

  if (flag != 0) assert(j == 100);
}
