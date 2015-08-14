#!/usr/bin/python

import sys

import z3

from mcf2smtlib import string_from_z3_model, smtlib2_string_from_file

if __name__ == '__main__':
    solver = z3.Solver()
    solver.add(z3.parse_smt2_string(smtlib2_string_from_file(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "1")
                                    + "(assert goal)"))
    if solver.check() == z3.unsat:
        print("UNSAT")
    else:
        print(string_from_z3_model(solver.model()))
