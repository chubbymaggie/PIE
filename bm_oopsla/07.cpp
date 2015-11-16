#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(5, flag, i, j, x, y);

  INIT_flag(unknown4);
  x = 0; y = 0; j = 0; i = 0;

  while(unknown1()) {
    PRINT_VARS();
    x++;
    y++;
    i+=x;
    j+=y;

    if(flag != 0)  j += 1;
  }
  PRINT_VARS();

  assert(j >= i);
  return 0;
}
