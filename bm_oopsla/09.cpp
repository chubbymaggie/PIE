#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, i, n, x, y);

  INIT_n(unknown);
  i = 0; x = 0; y = 0;

  while(i < n) {
    PRINT_VARS();
    i++;
    x++;
    if(i % 2 == 0) y++;
  }
  PRINT_VARS();

  if(i % 2 == 0) assert(x == 2 * y);
  return 0;
}
