#!/usr/bin/python

import sys

import z3

from mcf2smtlib import smtlib2_string_from_file

def joinit(iterable, delimiter):
    it = iter(iterable)
    yield next(it)
    for x in it:
        yield delimiter
        yield x

def flatString(l):
    return (l if type(l) is str else "(%s)" % (' '.join(flatString(x) for x in l)))

from pyparsing import alphas, alphanums, Combine, delimitedList, Forward, Group, Literal, \
                      Keyword, nums, oneOf, opAssoc, operatorPrecedence, Optional, \
                      ParserElement, Suppress, Word

ParserElement.enablePackrat()

LPAR, RPAR = map(Suppress, '()')
const = ( Literal('True').setParseAction(lambda s,l,t: ['true'])
        | Literal('False').setParseAction(lambda s,l,t: ['false']))

aop0 = oneOf('%')
aop1 = oneOf('* /')
aop2 = oneOf('+ -')

BOps = ( Keyword('And').setParseAction(lambda s,l,t: ['&'])
       | Keyword('Not').setParseAction(lambda s,l,t: ['!'])
       | Keyword('Or').setParseAction(lambda s,l,t: ['|']))

rop = oneOf('< > <= >= == !=').setParseAction(lambda s,l,t: ['=' if t[0] == '==' else t[0]])

val = Combine(Optional('-') + Word(nums))
var = Word(alphas+'_:$', alphanums+'_:$')

term = val | var

expr = operatorPrecedence(term, [
                            (aop0, 2, opAssoc.LEFT, ),
                            (aop1, 2, opAssoc.LEFT, ),
                            (aop2, 2, opAssoc.LEFT, )
                         ])

pred = Forward()
stmt = Forward()

stmt << ( const
        | Group(expr + rop + expr)
        | (LPAR + stmt + RPAR) )
pred << ( (BOps + LPAR + Group(delimitedList(pred)) + RPAR).setParseAction(lambda s,l,t: [joinit(t[1], t[0])] if t[0] != '!' else [['!', t[1][0]]])
        | stmt )

if __name__ == '__main__':
    goal = z3.Goal()
    goal.add(z3.parse_smt2_string(smtlib2_string_from_file(sys.argv[1], "1" if len(sys.argv) > 2 and sys.argv[2] == "0" else "0")))
    print(flatString(pred.parseString(str(z3.simplify(goal.as_expr())), parseAll = True).asList()[0]))
