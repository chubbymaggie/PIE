#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  int n, k, i, j;

  k = 0;
  i = 0;

  while(i < n)
  {
        i = i + 1;
        k = k + 1;
  }
  j = n;
  while(j > 0)
  {
  	__VERIFIER_assert(k > 0);
	j = j - 1;
   	k = k - 1;
  }
}
