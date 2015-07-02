#include "bm_oopsla.h"

int main() {
  int n, i = 0, j = 1;
  INITIALIZE("(%d, %d)", i, j, n);

  while(i < n){
    PRINT_VARS();
    if(j % 2 == 1) i++;
    if(i % 2 == 1) j++;
  }
  PRINT_VARS();

  assert(j >= i);
  return 0;
}
