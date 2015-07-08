#include "bm_oopsla.h"

int main() {
  int n, i = 0, j = 0;
  INITIALIZE(3, i, j, n);

  n = unknown();
  assume(n > 0);

  while(i < n) {
    PRINT_VARS();
    if(i % 2 == 1) j++;
    i++;
  }
  PRINT_VARS();

  if(n % 2 == 0) assert(i == 2 * j);
  return 0;
}
