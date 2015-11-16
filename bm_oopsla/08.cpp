#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(3, n, i, j);

  INIT_n(unknown);
  assume(n >= 0);
  i = 0; j = 0;

  while(i < n) {
    PRINT_VARS();
    i++;
    j++;
  }
  PRINT_VARS();

  assert(j == n);
  return 0;
}
