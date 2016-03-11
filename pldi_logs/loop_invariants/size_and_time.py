#!/usr/bin/python

import re, sys

from imp import load_source
mcf2ml = load_source('mcf2ml', '../../abducer/mcf2smtlib.py')

def pprintAST(ast, indent, initial=True):
    if type(ast) == str:
        print '%s%s' % ((' ' * indent) if initial else ' ', ast)
    elif len(ast) == 1:
        pprintAST(ast[0], indent, initial)
    else:
        sys.stdout.write('%s%s' % ((' ' * indent) if initial else ' ', ast[0]))
        if all(type(a) == str for a in ast[1:]):
            print ' %s' % ' '.join(ast[1:])
        else:
            pprintAST(ast[1], indent+len(ast[0])+1, False)
            [pprintAST(a, indent+len(ast[0])+1) for a in ast[2:]]

def sizeOfAST(ast):
    if type(ast) == str:
        return 1
    elif len(ast) == 1:
        return sizeOfAST(ast[0])
    else:
        return 1 + sum(sizeOfAST(a) for a in ast[1:])

def analyzeAST(ast):
    sys.stdout.write('AST:')
    pprintAST(ast, 5, False)
    print 'SIZE: %d' % sizeOfAST(ast)


if __name__ == "__main__":
    invariant_matcher = re.compile("^(Loop\ \#\d+:) (.*)\n$")
    time_matcher = re.compile("^real\t(\d+)m(\d+\.\d+)s\n$")

    for line in open(sys.argv[1]).readlines():
        res = invariant_matcher.search(line)
        if res is not None:
            invariant = res.group(2).replace(' & true', '')
            print '%s == %s' % (res.group(1), invariant)
            analyzeAST(mcf2ml.pred.parseString(invariant, parseAll=True).asList())
        else:
            res = time_matcher.search(line)
            if res is not None:
                print 'TIME: %ss\n' % (int(res.group(1)) * 60 + int(round(float(res.group(2)))))
