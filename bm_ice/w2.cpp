#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, n, x, input, flag);

  INIT_n(unknown);
  assume(n > 0);

  INIT_input(unknown1);

  x = 0;
  flag = 1;

  while (flag != 0) {
    PRINT_VARS();
    if (input != 0) {
      x = x + 1;
      if (x >= n)
        flag = 0;
      else
        flag = 1;
    }
    input = unknown1();
  }
  PRINT_VARS();

  assert(x == n);
}
