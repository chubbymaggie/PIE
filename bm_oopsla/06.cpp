#include "bm_oopsla.h"

int main() {
  int w = 1, z = 0, x = 0, y = 0;
  INITIALIZE("(%d, %d, %d, %d)\n", w, x, y, z);

  while(unknown2()){
    PRINT_VARS();
    if(w % 2 == 1) {x++; w++;};
    if(z % 2 == 0) {y++; z++;};
  }
  PRINT_VARS();

  assert(x <= 1);
  return 0;
}
