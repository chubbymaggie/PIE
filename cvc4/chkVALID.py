#!/usr/bin/python

import subprocess
import sys

from mcf2smtlib import z3str_to_cvc4, string_from_cvc4_model, smtlib2_string_from_file

if __name__ == '__main__':
    smtdata = z3str_to_cvc4((smtlib2_string_from_file("define-fun goal () Bool", sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "1")
               + "\n(assert (not goal))"))

    cvc4_in = ('\n'.join([
                 '(set-option :produce-models true)',
                 '(set-option :strings-fmf true)',
                 '(set-logic QF_S)'])
               + smtdata
               + '\n(check-sat)\n')
    cvc4 = subprocess.Popen(['cvc4', '--lang', 'smt', '--rewrite-divk', '--strings-exp'],
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=sys.stderr)
    cvc4.stdin.write(cvc4_in)
    cvc4_res = cvc4.stdout.readline().strip()

    if cvc4_res == 'unsat':
        print("VALID")
    elif cvc4_res == 'sat' or cvc4_res == "valid":
        print(string_from_cvc4_model(cvc4))
    else:
        print("ERROR")
