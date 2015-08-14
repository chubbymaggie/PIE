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

val = Combine(Optional('-') + Word(nums)).setParseAction(lambda s,l,t: ['(- %s)' % t[0][1:]] if t[0][0] == '-' else t)
var = Word(alphas+'_:$', alphanums+'_:$').setParseAction(addVar)

term = val | var

stmt = Forward()
expr = Forward()

expr << ( operatorPrecedence(term, [
                                     (aop0, 2, opAssoc.LEFT, lambda s,l,t: [infix2postfix(t[0])]),
                                     (aop1, 2, opAssoc.LEFT, lambda s,l,t: [infix2postfix(t[0])]),
                                     (aop2, 2, opAssoc.LEFT, lambda s,l,t: [infix2postfix(t[0])])
                                   ])
        | (LPAR + expr + RPAR))

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


def string_from_cvc4_model(cvc4_proc):
    cvc4_proc.stdin.write('(get-value (%s))\n' % (' '.join(uvars)))
    model = cvc4_proc.stdout.readline().strip()[2:-2].split(') (')
    model = {pair.partition(' ')[0]:pair.partition(' ')[2] for pair in model}
    return '-\n' + '\n'.join('%s : %s' % (var, model[var]) for var in model)

def smtlib2_string_from_file(action, filename, headless, implicant=None, implicantHeadless=None):
    global uvars

    uvars = {'true', 'false'}
    with open(filename) as f:
       mcf = f.readlines()
    mcf = mcf[0].strip() if headless != "0" else mcf[2].strip()

    if implicant is not None:
        with open(implicant) as f:
            imcf = f.readlines()
        imcf = imcf[0].strip() if implicantHeadless != "0" else imcf[2].strip()
        mcf = '((! (%s)) | (%s))' % (mcf, imcf)

    smtstr = flatString(pred.parseString(mcf, parseAll = True).asList()[0])
    uvars.discard('true')
    uvars.discard('false')

    smtstr = '%s\n(%s %s)' % (
        '\n'.join('(declare-const %s Int)' % var for var in uvars),
        action,
        smtstr)
    return smtstr

if __name__ == "__main__":
    print(smtlib2_string_from_file('assert', sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "1"))
