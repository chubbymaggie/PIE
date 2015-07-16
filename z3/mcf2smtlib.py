#!/usr/bin/python

import sys

uvars = {'true', 'false'}

def addVar(s,l,t):
    if t[0] not in uvars:
        uvars.add(t[0])
    return t

def flatString(l):
    return (l if type(l) is str else "(%s)" % (' '.join(flatString(x) for x in l)))

def infix2postfix(l):
    return (l[0] if len(l) < 3 else [l[-2], infix2postfix(l[:-2]), l[-1]])

###

from pyparsing import alphas, alphanums, Combine, Forward, Literal, nums, oneOf, opAssoc, \
                      operatorPrecedence, Optional, ParserElement, Suppress, Word

ParserElement.enablePackrat()

LPAR, RPAR = map(Suppress, '()')
const = oneOf('true false')

aop0 = oneOf('* /')
aop1 = oneOf('+ -')
aop2 = oneOf('%').setParseAction(lambda s,l,t: ['mod'])

bop = oneOf('& |').setParseAction(lambda s,l,t: ['and'] if t[0] == '&' else ['or'])
NOT = Literal('!')

rop = oneOf('< > <= >= = !=').setParseAction(lambda s,l,t: 'distinct' if t[0] == '!=' else t[0])

val = Combine(Optional('-') + Word(nums))
var = Word(alphas+'_:$', alphanums+'_:$').setParseAction(addVar)

term = val | var

expr = operatorPrecedence(term, [
                            (aop0, 2, opAssoc.LEFT, lambda s,l,t: [infix2postfix(t[0])]),
                            (aop1, 2, opAssoc.LEFT, lambda s,l,t: [infix2postfix(t[0])]),
                            (aop2, 2, opAssoc.LEFT, lambda s,l,t: [infix2postfix(t[0])])
                         ])

stmt = Forward()

stmt << ( const
        | ((expr + rop + expr).setParseAction(lambda s,l,t: [[t[1], t[0], t[2]]]))
        | (LPAR + stmt + RPAR))

pred = operatorPrecedence(stmt, [
                            (NOT, 1, opAssoc.RIGHT, lambda s,l,t: [['not', t[0][1]]]),
                            (bop, 2, opAssoc.LEFT, lambda s,l,t: [infix2postfix(t[0])] )
                         ])

###

def string_from_z3_model(mod):
    model = {var: 0 for var in uvars}
    for var in mod:
        model[str(var)] = mod[var]
    return '-\n' + '\n'.join('%s : %s' % (var, model[var]) for var in model)

def smtlib2_string_from_file(filename, headless):
    global uvars

    uvars = {'true', 'false'}
    with open(filename) as f:
       mcf = f.readlines()
    mcf = mcf[0].strip() if headless != "0" else mcf[2].strip()

    smtstr = flatString(pred.parseString(mcf, parseAll = True).asList()[0])
    uvars.discard('true')
    uvars.discard('false')

    smtstr = '%s (assert %s)' % (
        ' '.join('(declare-const %s Int)' % var for var in uvars),
        smtstr)
    return smtstr

if __name__ == "__main__":
    print(smtlib2_string_from_file(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "1"))
