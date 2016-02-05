#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(2, x, m);
  INIT_m(unknown);

  x = 0;
  while (x < 100) {
    PRINT_VARS();
    m = unknown();
    x = x + 1;
  }
  PRINT_VARS();

  assert(x == 100);
  return 0;
}
