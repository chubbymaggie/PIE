#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, x, y, i, j);

  INIT_i(unknownu);
  INIT_j(unknownu);
  assume(i >= 0 && j >= 0);

  x = i;
  y = j;

  while (x != 0) {
    PRINT_VARS();
    x--;
    y--;
  }
  PRINT_VARS();

  if (i == j) assert(y == 0);
}
