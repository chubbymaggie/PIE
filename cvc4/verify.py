#!/usr/bin/python

import subprocess
import sys

from mcf2smtlib import string_from_cvc4_model, smtlib2_string_from_file

if __name__ == '__main__':
    smtdata = (smtlib2_string_from_file("define-fun goal () Bool",
                                        sys.argv[1], sys.argv[3] if len(sys.argv) > 3 else "1",
                                        sys.argv[2], sys.argv[4] if len(sys.argv) > 4 else "1")
               + "\n(assert (not goal))")

    cvc4_in = ('\n'.join([
                 '(set-option :produce-models true)',
                 '(set-option :strings-fmf true)',
                 '(set-logic ALL_SUPPORTED)'])
               + smtdata
               + '\n(check-sat)\n')
    cvc4 = subprocess.Popen(['cvc4', '--rewrite-divk', '--lang', 'smt'],
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=sys.stderr)
    cvc4.stdin.write(cvc4_in)
    cvc4_res = cvc4.stdout.readline().strip()

    if cvc4_res == 'unsat':
        print("UNSAT")
    elif cvc4_res == 'sat' or 'valid':
        print(string_from_cvc4_model(cvc4))
    else:
        print("ERROR")
