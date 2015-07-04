#include "bm_oopsla.h"

int main() {
  int i, j, x, y;
  INITIALIZE(4, i, j, x, y);

  x = i;
  y = j;

  while(x != 0) {
    PRINT_VARS();
    x--;
    y--;
  }
  PRINT_VARS();

  if(i == j) assert(y == 0);
  return 0;
}
