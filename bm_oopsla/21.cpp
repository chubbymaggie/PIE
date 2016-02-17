#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, i, j, k, n);
  
  INIT_n(unknown);
  k = 1;
  i = 1;
  j = 0;
  PRINT_BAR(1);
  while(i < n) {
    PRINT_VARS();
    j = 0;
    PRINT_BAR(2);
    while(j < i) {
      PRINT_VARS();
      k += (i - j);
      j++;
    }
    PRINT_VARS();
    i++;
    PRINT_BAR(1);
  }
  PRINT_VARS();
  assert(k >= n);
  return 0;
}

