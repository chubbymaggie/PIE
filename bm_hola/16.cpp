#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(4, i, j, x, y);

  INIT_i(unknownu);
  INIT_j(unknownu);

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
