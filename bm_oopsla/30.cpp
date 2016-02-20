#include "bm_oopsla.h"

int main(int argc, char* argv[]) {

  RECORD(4, x, y, i, j);
  x = 0;
  y = 0;
  i = 0;
  j = 0;

  while (unknown4()) {
    PRINT_VARS();
    PRINT_BAR(1);
    while (unknown4()) {
      PRINT_VARS();
      if(x == y)
        i++;
      else
        j++;
    }
    PRINT_VARS();
    PRINT_BAR(2);
    if (i >= j) {
      x++;
      y++;
    }
    else
      y++;
  }
  PRINT_VARS();
  PRINT_BAR(1);

  assert(i >= j);
  return 0;
}
