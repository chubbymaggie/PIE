#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(3, m, n, x);

  INIT_n(unknown);
  m = 0; x = 0;

  while(x < n) {
    PRINT_VARS();
    if(unknown1()) {
      m = x;
    }
    x = x+1;
  }
  PRINT_VARS();

  if(n > 0) {
    assert(0 <= m);
    assert(m < n);
  }
  return 0;
}
