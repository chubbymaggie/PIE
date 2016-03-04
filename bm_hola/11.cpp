#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, i, j, x);

  INIT_i(unknown);

  j = 0;
  x = 100;

  for (i = 0; i < x; i++) {
    PRINT_VARS();
    j = j + 2;
  }
  PRINT_VARS();

  assert(j == 2 * x);
}
