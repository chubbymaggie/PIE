#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, i, j, k, n);
  
  INIT_n(unknown);
  k = 1;
  i = 1;
  j = 0;
  while(i < n) {
    PRINT_BAR(1);
    PRINT_VARS(1);
    j = 0;
    PRINT_BAR(2);
    while(j < i) {
      PRINT_VARS(2);
      k += (i - j);
      j++;
    }
    PRINT_VARS(2);
    i++;
  }
  PRINT_BAR(1);
  PRINT_VARS(1);
  assert(k >= n);
  return 0;
}

