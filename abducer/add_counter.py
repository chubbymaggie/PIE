#!/usr/bin/python

import os
import sys

def fix(string):
    if string[0] == '(' and string[-1] == ')':
        return '-' + string[3:-1]
    elif string[0] == '"' and string[-1] == '"':
        return string[1:-1]
    return string

if __name__ == "__main__":
    [EXE, TST, HDR, RES] = sys.argv[1:]

    with open(HDR) as f:
        header = f.readline()
    with open(RES) as f:
        data = f.readlines()[1:]

    header = header.split('\t')
    data = {line.split(' : ')[0].strip():line.split(' : ')[1].strip() for line in data if line.strip() != ''}

    model = {var.strip():fix(data[var.strip()]) if var.strip() in data else '-' for var in header}
    sys.stderr.write("    [+] Root state for counter-examples : %s\n" % str(model))

    model = ' '.join([model[var.strip()] for var in header])

    # TODO: Pick a reasonable amount / accept command line arg for timeout
    os.system("timeout 1s %s %s >> %s" % (EXE, model, TST))
