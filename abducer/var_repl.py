#!/usr/bin/python

import re
import sys

def fix(string):
    if string[0] == '(' and string[-1] == ')':
        return '-' + string[3:-1]
    return string

if __name__ == '__main__':
    inp = sys.stdin.read()

    # MCF to C++/OCaml
    if sys.argv[1].startswith('rev'):
        with open(sys.argv[2]) as f:
            xvars = dict((z.strip(),x.strip()) for (x,y,z) in (l[3:-3].partition(' =+=> ') for l in f.readlines() if ' =+=> ' in l))
        inp = inp.replace('&', '&&').replace('|', '||')
    # C++/OCaml to MCF
    else:
        with open(sys.argv[len(sys.argv) - 1]) as f:
            xvars = dict((x.strip(),z.strip()) for (x,y,z) in (l[3:-3].partition(' =+=> ') for l in f.readlines() if ' =+=> ' in l))
        inp = inp.replace('&&', '&').replace('||', '|')

    for (k,v) in xvars.items():
        inp = re.sub(r"\b%s\b" % v, k, inp)

    # MCF to C++/OCaml with Values
    if sys.argv[1] == 'revVals':
        inp = inp.split('\n')[1:]
        inp = inp if inp[-1] != '' else inp[:-1]
    #    if len(sys.argv) > 3:
    #        #FIXME: Unused now, was for missingTest calls
    #        temp = ['0'] * int(sys.argv[3])
    #        for (k,v) in ((l.split(' : ')[0][1:-1], l.split(' : ')[1]) for l in sorted((l for l in inp if l.split(' : ')[0][1:-1].isdigit()), key=lambda l: int(l.split(' : ')[0][1:-1]))):
    #            temp[int(k)] = v
    #        inp = '\n'.join(temp)
    #    else:
        inp = '\n'.join(fix(l.split(' : ')[1]) for l in sorted((l for l in inp if l.split(' : ')[0][1:-1].isdigit()),
                                                               key=lambda l: int(l.split(' : ')[0][1:-1])))

    print inp
