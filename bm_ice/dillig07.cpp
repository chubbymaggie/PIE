#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, i, j, n);

  i = 0;
  j = 0;

  INIT_n(unknown1);
  assume(n >= 0);

  while (i < n) {
    PRINT_VARS();
    i++;
    j++;
  }
  PRINT_VARS();

  assert(j < n + 1);
}
