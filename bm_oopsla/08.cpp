#include "bm_oopsla.h"

int main() {
  int n, i = 0, j = 0;
  INITIALIZE("(%d, %d, %d)\n", n, i, j);

  assume(n >= 0);

  while(i < n) {
    PRINT_VARS();
    i++;
    j++;
  }
  PRINT_VARS();

  assert(j == n);
  return 0;
}
