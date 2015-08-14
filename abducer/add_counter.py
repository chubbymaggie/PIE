#!/usr/bin/python

import sys

from random import randint

def fix(string):
    if string[0] == '(' and string[-1] == ')':
        return '-' + string[3:-1]
    return string

if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        header = f.readline()
    with open(sys.argv[2]) as f:
        data = f.readlines()[1:]

    header = header.split('\t')
    data = {line.split(' : ')[0].strip():line.split(' : ')[1].strip() for line in data}

    model = {var.strip():fix(data[var.strip()]) if var.strip() in data else str(randint(-16,16)) for var in header}
    sys.stderr.write("    [+] Counter example added ... %s\n" % str(model))

    model = [data[var.strip()] if var.strip() in data else str(randint(-16,16)) for var in header]
    with open(sys.argv[1], 'a') as f:
        f.write('\n%s' % '\t'.join(model))
