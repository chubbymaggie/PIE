#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(6, i, j, w, x, y, z);

  i = 1; j = 0; z = i - j; x = 0; y = 0; w = 0;

  while(unknown2()) {
    PRINT_VARS();
    z += x + y + w;
    y++;
    if(z % 2 == 1)
      x++;
    w += 2;
  }
  PRINT_VARS();

  assert(x == y);
  return 0;
}
