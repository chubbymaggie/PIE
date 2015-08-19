#!/usr/bin/python3

import itertools
import os
import random
import sys

from subprocess import check_output

cnt = 0
uvars = []
uniq_vars = {}
uniq_consts = set([0])

def addConst(s,l,t):
    uniq_consts.add(int(t[0]))
    return t[0]

def addVar(s,l,t):
    global cnt
    if t[0] in ['true', 'false']:
        return t
    if not t[0] in uniq_vars:
        uniq_vars[t[0]] = "x%dg" % cnt
        cnt = cnt+1
    return uniq_vars[t[0]]

def flatString(l):
    return (l if type(l) is str else "(%s)" % (' '.join(flatString(x) for x in l)))

###

from pyparsing import alphas, alphanums, Combine, Literal, nums, oneOf, opAssoc, \
                      operatorPrecedence, Optional, ParserElement, Suppress, Word

ParserElement.enablePackrat()

LPAR, RPAR = map(Suppress, '()')

aop0 = oneOf('* /')
aop1 = oneOf('+ -')
aop2 = oneOf('%').setParseAction(lambda s,l,t: ['mod'])
bop = oneOf('& |').setParseAction(lambda s,l,t: [t[0]+t[0]])
NOT = Literal('!')
rop = oneOf('< > <= >= = !=')
const = oneOf('true false')

var = Word(alphas+'_:$', alphanums+'_:$').setParseAction(addVar)
ival = Combine(Optional('-') + Word(nums)).setParseAction(addConst)
ivar = (ival + var).setParseAction(lambda s,l,t: ['%s*%s' % tuple(t)])

term = ivar | ival | var

expr = operatorPrecedence(term, [
                            (aop0, 2, opAssoc.LEFT, ),
                            (aop1, 2, opAssoc.LEFT, ),
                            (aop2, 2, opAssoc.LEFT, lambda s,l,t: [[[t[0][0], 'mod', t[0][2]], '+', t[0][2]], 'mod', t[0][2]])
                         ])

stmt = const | (expr + rop + expr)

pred = operatorPrecedence(stmt, [
                            (NOT, 1, opAssoc.RIGHT, lambda s,l,t: ['not', t[0][1:]]),
                            (bop, 2, opAssoc.LEFT, )
                         ])

###

def pairwise(iterable):
    a, b = itertools.tee(iterable)
    next(b, None)
    return list(zip(a, b))

def gen_rnd(p):
    if type(p) is int:
        return p
    elif type(p) is tuple and len(p) == 2:
        if p[0] == float('-inf'):
            return random.randint(p[1]-99999, p[1]-1)
        elif p[1] == float('inf'):
            return random.randint(p[0]+1, p[0]+99999)
        elif p[1] != float('-inf') and p[0] != float('inf'):
            return random.randint(*(p if p[0]+1 > p[1]-1 else (p[0]+1, p[1]-1)))

def sample_rnd_product(iterable):
    return (str(gen_rnd(random.choice(iterable))) for _ in uniq_vars)

MAX_SPACE = 3.2 * (10**4)
PENALTY = 32

def genTests():
    if os.path.isfile('final_tests'):
        with open('final_tests') as f:
            models = f.readlines()
        header = {uniq_vars[name.strip()] : idx for idx, name in enumerate(models[0].split('\t')) if name.strip() in uniq_vars}
        models = ([val.strip() for val in vals.split('\t')] for vals in models[1:] if len(vals.strip()) > 0)
        return ((vals[header[v]] for v in uvars) for vals in models)

    space = pairwise(uniq_consts) + uniq_consts + ([(float('-inf'), uniq_consts[0]), (uniq_consts[-1], float('inf'))] * 3)

    if len(uniq_vars) * (len(space) ** len(uniq_vars)) > MAX_SPACE:
        space = space + (uniq_consts * 2)
        return (sample_rnd_product(space) for t in range(int(MAX_SPACE/(PENALTY * len(uniq_vars)))))
    else:
        return ((str(gen_rnd(i)) for i in t) for t in itertools.product(space, repeat=len(uniq_vars)))

if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        smt = (f.readlines()[2]).strip()
    print('(* SMT --- %s --- END *)' % smt)

    ml = flatString(pred.parseString(smt, parseAll = True).asList())
    uvars = sorted(uniq_vars.values())
    uniq_consts = sorted(list(uniq_consts))

    out = check_output(['./chkSAT', sys.argv[1], '0']).decode().split("\n")
    if out[0] == 'UNSAT':
        sys.exit(1)
    model = dict((kv[0].strip(), kv[1].strip()) for kv in (line.partition(':')[0::2] for line in out[1:]))

    print('\n(*** Variable mapping ***)')
    for kv in sorted(uniq_vars.items(), key=lambda kv: int(kv[1][1:-1])):
        print('(*  %s =+=> %s  *)' % kv)
    print("\nopen Batteries")
    print("open Escher_types")
    print("open SpecInfer")
    print("\nlet f = fun (%s) -> %s" % (','.join(uvars), ml))
    print("\nlet def_features = (*PYF:x|T(%s)*)" % ','.join(v +':I' for v in uvars))
    print("\nlet my_features = []")
    print("\nlet post_cond = ((fun x r -> match r with Bad _ -> false | Ok z -> z), \"true\")")
    print("\nlet tests = [")
    print("    (%s);" % (', '.join(model[v] for v in uniq_vars)))
    print(';\n'.join(("    (%s)" % (', '.join(t))) for t in genTests()))
    print("]\n\nlet typo = [ %s ]" % (' ; '.join(['TInt'] * len(uniq_vars))))
    print("\nlet trans = fun (%s) -> [ %s ]" % (','.join(uvars), ' ; '.join('of_int ' + v for v in uvars)))
    print("\nlet test_trans = fun (l) -> List.(%s)" % ','.join('nth l %d' % i for i in range(len(uvars))))
    print("\n\n\nlet () = print_cnf stdout (pacLearnSpecNSATVerify f tests (def_features @ my_features) post_cond (typo, trans) [%s] test_trans \"%s\")" % ('; '.join(str(i) for i in uniq_consts), sys.argv[1]))
