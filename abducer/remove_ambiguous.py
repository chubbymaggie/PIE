#!/usr/bin/python

import os
import sys

def has_state(d, s, h):
    d = zip(h, (v.strip() for v in d.split('\t')))
    if all(v in d for v in s):
        sys.stderr.write('\n    [-] Removed ambiguous state: %s\n' % d)
        return True

file = 'ambiguous'
if __name__ == "__main__":
    if os.path.isfile(file):
        with open(file, 'r') as f:
            state = [v.strip() for v in f.readline()[1:-1].split(',')]
        os.remove(file)

        with open(sys.argv[1], 'r') as f:
            vars = [x.strip() for (x,y,z) in (l[3:-3].partition(' =+=> ') for l in f.readlines() if ' =+=> ' in l)]
        state = zip(vars, state)

        # assuming final_tests is sym-linked to loopId tests file
        with open('final_tests', 'r') as f:
            header = f.readline()
            data = f.readlines()

        hlist = [h.strip() for h in header.split('\t')]
        datax = (d for d in data if len(d.strip()) > 0 and not has_state(d, state, hlist))

        with open('final_tests', 'w') as f:
            f.write(header)
            f.write(''.join(datax))
