#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, x, m);

  INIT_m(unknown);
  x = 100;

  while (x > 0) {
    PRINT_VARS();
    m = unknown();
    x = x - 1;
  }
  PRINT_VARS();

  assert(x == 0);
  return 0;
}
