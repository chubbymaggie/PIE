#include "bm_oopsla.h"

int main() {
  int n, i = 0, j = 1;
  INITIALIZE(3, i, j, n);

  n = unknown();

  while(i < n){
    PRINT_VARS();
    if(j % 2 == 1) i++;
    if(i % 2 == 1) j++;
  }
  PRINT_VARS();

  assert(j >= i);
  return 0;
}
