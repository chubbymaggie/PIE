#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(3, i, j, n);

  INIT_n(unknown);
  i = 0; j = 0;

  while(i < 3) {
    PRINT_VARS();
    i++;
    j++;
  }
  PRINT_VARS();

  assert(j == 3);
  return 0;
}
