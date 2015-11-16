#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(5, i, j, l, x, y);

  l = 0;
  INIT_i(unknown);
  assume(i >= l);
  INIT_j(unknown);
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

