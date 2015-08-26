#!/usr/bin/python

import cgi
import sys

def infix2prefix(l):
    return (l[0] if len(l) < 3 else [l[-2], infix2prefix(l[:-2]), l[-1]])

from pyparsing import alphas, alphanums, Combine, Forward, Literal, nums, \
                      oneOf, opAssoc, operatorPrecedence,  Optional, \
                      ParseException, ParserElement, QuotedString, Suppress, Word

ParserElement.enablePackrat()

LPAR, RPAR, COMMA = map(Suppress, '(),')
const = oneOf('true false')

aop0 = oneOf('* /')
aop1 = oneOf('+ -')
aop2 = oneOf('%')

bop = oneOf('& |')
NOT = Literal('!')

rop = oneOf('< > <= >= = !=')

GET, CAT, HAS, IND, LEN, REP, SUB, EQL = map(Literal, '#get #cat #has #ind #len #rep #sub #eql'.split())

var = Word(alphas+'_:$', alphanums+'_:$')
ival = Combine(Optional('-') + Word(nums))
ivar = (ival + var).setParseAction(lambda s,l,t: ['*', t[0], t[1]])

term = ivar | ival | var | QuotedString(quoteChar='"', unquoteResults=False)

stmt = Forward()
expr = Forward()
sexpr = Forward()

sexpr << ( (GET + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1], t[2]]])
         | (CAT + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1], t[2]]])
         | (IND + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1], t[2]]])
         | (LEN + LPAR + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1]]])
         | (REP + LPAR + expr + COMMA + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1], t[2], t[3]]])
         | (SUB + LPAR + expr + COMMA + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1], t[2], t[3]]])
         | term
         | (LPAR + sexpr + RPAR))

expr << ( operatorPrecedence(sexpr, [
                                     (aop0, 2, opAssoc.LEFT, lambda s,l,t: [infix2prefix(t[0])]),
                                     (aop1, 2, opAssoc.LEFT, lambda s,l,t: [infix2prefix(t[0])]),
                                     (aop2, 2, opAssoc.LEFT, lambda s,l,t: [infix2prefix(t[0])])
                                    ])
        | (LPAR + expr + RPAR))

stmt << ( const
        | (HAS + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1], t[2]]])
        | (EQL + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[t[0][1:], t[1], t[2]]])
        | (expr + rop + expr).setParseAction(lambda s,l,t: [[t[1], t[0], t[2]]])
        | (LPAR + stmt + RPAR))

pred = operatorPrecedence(stmt, [
                            (NOT, 1, opAssoc.RIGHT, lambda s,l,t: [['!', t[0][1]]]),
                            (bop, 2, opAssoc.LEFT, lambda s,l,t: [infix2prefix(t[0])] )
                         ])

def toXML(l, i=0):
    if type(l) is str:
            return "%s<expr>%s</expr>" % (' ' * i, cgi.escape(l))
    if len(l) == 1:
            return toXML(l[0], i)
    return "%s<expr>\n%s\n%s</expr>" % (' ' * i, '\n'.join(toXML(c, i+2) for c in l), ' ' * i)

if __name__ == "__main__":
    headless = sys.argv[2] if len(sys.argv) > 2  else "1"
    with open(sys.argv[1]) as f:
       mcf = f.readlines()
    mcf = mcf[0].strip() if headless != "0" else mcf[2].strip()

    try:
        print(toXML(pred.parseString(mcf, parseAll=True).asList()))
    except ParseException:
        try:
            print(toXML(stmt.parseString(mcf, parseAll=True).asList()))
        except ParseException:
            print(toXML(expr.parseString(mcf, parseAll=True).asList()))
