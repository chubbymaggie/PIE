#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(3, m, n, x);

  x = 0;
  m = 0;
  INIT_n(unknown);

  while (x < n) {
    PRINT_VARS();
    if (unknown1()) {
      m = x;
    }
    x = x + 1;
  }
  PRINT_VARS();

  if (n > 0) assert(0 <= m && m < n);
}
