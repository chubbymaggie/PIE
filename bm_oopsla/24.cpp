#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, i, j, k, n);

  INIT_n(unknown);
  assume(n > 0);
  INIT_k(unknown);
  assume(k > n);
  j = 0;

  while(j < n) {
    PRINT_VARS();
    j++;
    k--;
  }
  PRINT_VARS();

  assert(k >= 0);
  return 0;
}
