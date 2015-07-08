#include "bm_oopsla.h"

int main() {
  int n, x = 0;
  INITIALIZE(2, n, x);

  n = unknown();

  while(x < n) {
    PRINT_VARS();
    x++;
  }
  PRINT_VARS();

  if(n > 0) assert(x == n);
  return 0;
}
