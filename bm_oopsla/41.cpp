#include "bm_oopsla.h"

int main(int argc, char* argv[]) {
  RECORD(6, flag, i, j, k, a, b);

  INIT_flag(unknown4);
  j = 1;
  if (flag != 0) {
    i = 0;
  }
  else {
    i = 1;
  }

  while(unknown1()) {
    PRINT_VARS();
    i += 2;
    if(i % 2 == 0) {
      j += 2;
    }
    else j++;
  }
  PRINT_VARS();
  a = 0;
  b = 0;
  PRINT_BAR();
  while(unknown2()) {
    PRINT_VARS();
    a++;
    b += (j - i);
  }
  PRINT_VARS();
  if (flag != 0)
    assert(a == b);
  return 0;
}

