#include "bm_oopsla.h"

int main() {
  int i, j, x, y, l = 0;
  INITIALIZE(5, i, j, l, x, y);

  i = unknown();
  j = unknown();
  assume(i >= l);
  x = i; y = j;

  while(x != l) {
    PRINT_VARS();
    x--;
    y--;
  }
  PRINT_VARS();

  if(i == j) assert(y == l);
  return 0;
}

