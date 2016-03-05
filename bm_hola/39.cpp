#include "bm_oopsla.h"

int main(int argc, char * argv[]) {
  RECORD(10,
         MAXPATHLEN,
         buf_off,
         pattern_off,
         bound_off,
         glob3_pathbuf_off,
         glob3_pathend_off,
         glob3_pathlim_off,
         glob3_pattern_off,
         glob3_dc,
         flag);

  INIT_MAXPATHLEN(unknownu);
  assume(MAXPATHLEN > 0);

  INIT_glob3_dc(unknown);

  buf_off = 0;
  pattern_off = 0;

  bound_off = 0 + (MAXPATHLEN + 1) - 1;

  glob3_pathbuf_off = buf_off;
  glob3_pathend_off = buf_off;
  glob3_pathlim_off = bound_off;
  glob3_pattern_off = pattern_off;

  glob3_dc = 0;

  if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off)
    flag = 0;
  else
    flag = 1;
  while (flag != 0) {
    PRINT_VARS();

    //      A[glob3_dc] = 1;
    glob3_dc++;
    /* OK */
    assert(0 <= glob3_dc);
    assert(glob3_dc < MAXPATHLEN + 1);

    if (unknown())
      flag = 0;
    else if (glob3_pathend_off + glob3_dc >= glob3_pathlim_off)
      flag = 0;
    else
      flag = 1;
  }
  PRINT_VARS();
}
