#include "bm_oopsla.h"

int main() {
  int n, i = 0, j = 0;
  INITIALIZE(3, i, j, n);

  while(i < 3) {
    PRINT_VARS();
    i++;
    j++;
  }
  PRINT_VARS();

  assert(j == 3);
  return 0;
}
