#include "bm_oopsla.h"

int main() {
  int i, j, x, y, l = 0;
  INITIALIZE(5, i, j, l, x, y);

  x = i; y = j;

  while(x != l) {
    x--;
    y--;
  }

  if(i == j) assert(y == l);
  return 0;
}
