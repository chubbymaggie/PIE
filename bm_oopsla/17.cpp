#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(2, n, x);

  INIT_n(unknown);
  x = 0;

  while(x < n) {
    PRINT_VARS();
    x++;
  }
  PRINT_VARS();

  if(n > 0) assert(x == n);
  return 0;
}
