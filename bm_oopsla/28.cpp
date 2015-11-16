#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(4, k, x, y, z);

  x = 0; y = 0; z = 0; k = 0;

  while(unknown1()) {
    PRINT_VARS();
    if(k % 3 == 0) x++;
    y++;
    z++;
    k = x+y+z;
  }
  PRINT_VARS();

  assert(x == y);
  assert(y == z);
  return 0;
}
