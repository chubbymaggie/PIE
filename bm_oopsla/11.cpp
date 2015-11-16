#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, j, k, l, n);

  INIT_n(unknown);
  assume(n > 0);
  j = n; k = n; l = 0;

  while(j > l) {
    PRINT_VARS();
    j--;
    k--;
  }
  PRINT_VARS();

  assert(k >= l);
  return 0;
}
