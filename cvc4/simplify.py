#!/usr/bin/python

import subprocess
import sys

from mcf2smtlib import smtlib2_string_from_file

lets = dict()

def joinit(iterable, delimiter):
    it = iter(iterable)
    yield next(it)
    for x in it:
        yield delimiter
        yield x

def flatString(l):
    return (l if type(l) is str else "(%s)" % (' '.join(flatString(x) for x in l)))

def let_action(s,l,t):
    lets[t[0]] = flatString(t[1])
    return [t[2]]

from pyparsing import alphas, alphanums, Combine, delimitedList, Forward, Group, Literal, \
                      Keyword, nums, oneOf, Optional, ParserElement, Suppress, White, Word

ParserElement.enablePackrat()

LPAR, RPAR = map(Suppress, '()')
const = Literal('true') | Literal('false')

AOps = oneOf('INTS_MODULUS_TOTAL * / + -').setParseAction(lambda s,l,t: ['%'] if t[0] == 'INTS_MODULUS_TOTAL' else t)
BOps = ( Keyword('and').setParseAction(lambda s,l,t: ['&'])
       | Keyword('not').setParseAction(lambda s,l,t: ['!'])
       | Keyword('or').setParseAction(lambda s,l,t: ['|']))
ROps = oneOf('< > <= >= =')

val = Combine(Optional('-') + Word(nums))
var = Word(alphas+'_:$', alphanums+'_:$')

term = val | var

let = Forward()
pred = Forward()
stmt = Forward()
expr = Forward()

expr << ( term
        | (LPAR + AOps + Group(delimitedList(expr, delim=White(' '))) + RPAR).setParseAction(lambda s,l,t: [list(joinit(t[1], t[0]))] if not(t[0] == '-' and len(t[1]) == 1) else [['0 -', t[1][0]]])
        | (LPAR + expr + RPAR))

stmt << ( const
        | term
        | (LPAR + ROps + expr + expr + RPAR).setParseAction(lambda s,l,t: [[t[1], t[0], t[2]]])
        | (LPAR + stmt + RPAR) )

pred << ( (LPAR + BOps + Group(delimitedList(pred, White(' '))) + RPAR).setParseAction(lambda s,l,t: [list(joinit(t[1], t[0]))] if t[0] != '!' else [['!', t[1][0]]])
        | stmt )

let << ( pred
       | (LPAR + Suppress('let') + LPAR + LPAR + term + (expr | pred) + RPAR + RPAR + let + RPAR).setParseAction(let_action))

if __name__ == '__main__':
    smtdata = smtlib2_string_from_file("simplify", sys.argv[1], "1" if len(sys.argv) > 2 and sys.argv[2] == "0" else "0")

    cvc4_in = ('\n'.join([
                 '(set-option :produce-models true)',
                 '(set-option :strings-fmf true)',
                 '(set-logic ALL_SUPPORTED)'])
               + smtdata + '\n')
    cvc4 = subprocess.Popen(['cvc4', '--lang', 'smt', '--rewrite-divk'],
                            stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE,
                            stderr=sys.stderr)
    cvc4.stdin.write(cvc4_in)
    cvc4_res = cvc4.stdout.readline().strip()

    mcf = flatString(let.parseString(cvc4_res, parseAll = True).asList())
    while('_let_' in mcf):
        for var in lets:
            mcf = mcf.replace(var, lets[var])
    print(mcf)
