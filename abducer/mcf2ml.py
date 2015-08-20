#!/usr/bin/python3

import os
import sys

from subprocess import check_output

cnt = 0
uvars = []
uniq_vars = {}
string_vars = set()
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

def chkString(token):
    if type(token) is str:
        if token not in string_vars:
            string_vars.add(token)
    return token

def chkStringSibling(s,l,t):
    if (type(t[0]) is not str) and (type(t[2]) is not str):
        return t

    if type(t[2]) is str:
        if type(t[0]) is not str or ((t[0][0] == '"') == (t[2][0] == '"')):
            return t
        elif t[0][0] == '"':
            chkString(t[2])
        elif t[2][0] == '"':
            chkString(t[0])
    else:
        if len(t[2]) == 1:
            return chkStringSibling(s,l,[t[0], t[1], t[2][0]])

        if t[2][0] in ['Char.escaped','snd','String.sub'] or t[2][1] == '^':
            chkString(t[0])

    return t

###

from pyparsing import alphas, alphanums, Combine, Forward, Literal, nums, \
                      oneOf, opAssoc, operatorPrecedence, Optional, \
                      ParserElement, QuotedString, Suppress, Word

ParserElement.enablePackrat()

LPAR, RPAR, COMMA = map(Suppress, '(),')
const = oneOf('true false')

aop0 = oneOf('* /')
aop1 = oneOf('+ -')
aop2 = oneOf('%').setParseAction(lambda s,l,t: ['mod'])

bop = oneOf('& |').setParseAction(lambda s,l,t: [t[0]+t[0]])
NOT = Literal('!')

rop = oneOf('< > <= >= = !=')

GET, CAT, HAS, IND, LEN, REP, SUB = map(Literal, '#get #cat #has #ind #len #rep #sub'.split())

var = Word(alphas+'_:$', alphanums+'_:$').setParseAction(addVar)
ival = Combine(Optional('-') + Word(nums)).setParseAction(addConst)
ivar = (ival + var).setParseAction(lambda s,l,t: [t[0], '*', t[1]])

term = ivar | ival | var | QuotedString(quoteChar='"', unquoteResults=False)

stmt = Forward()
expr = Forward()
sexpr = Forward()

sexpr << ( (GET + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [['Char.escaped', ['String.get', chkString(t[1]), t[2]]]])
         | (CAT + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [[chkString(t[1]), '^', chkString(t[2])]])
         | (IND + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [['index_of', chkString(t[1]), chkString(t[2])]])
         | (LEN + LPAR + expr + RPAR).setParseAction(lambda s,l,t: [['String.length', chkString(t[1])]])
         | (REP + LPAR + expr + COMMA + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [['snd', ['BatString.replace', chkString(t[1]), chkString(t[2]), chkString(t[3])]]])
         | (SUB + LPAR + expr + COMMA + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [['String.sub', chkString(t[1]),  t[2], t[3]]])
         | term
         | (LPAR + expr + RPAR))

expr << operatorPrecedence(sexpr, [
                             (aop0, 2, opAssoc.LEFT, ),
                             (aop1, 2, opAssoc.LEFT, ),
                             (aop2, 2, opAssoc.LEFT, lambda s,l,t: [[[t[0][0], 'mod', t[0][2]], '+', t[0][2]], 'mod', t[0][2]])
                          ])

stmt << ( const
        | (HAS + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [['BatString.exists', chkString(t[1]), chkString(t[2])]])
        | (expr + rop + expr).setParseAction(chkStringSibling)
        | (LPAR + stmt + RPAR))

pred = operatorPrecedence(stmt, [
                            (NOT, 1, opAssoc.RIGHT, lambda s,l,t: ['not', t[0][1:]]),
                            (bop, 2, opAssoc.LEFT, )
                         ])

###

def genTests():
    if os.path.isfile('final_tests'):
        with open('final_tests') as f:
            models = f.readlines()
        header = {uniq_vars[name.strip()] : idx for idx, name in enumerate(models[0].split('\t')) if name.strip() in uniq_vars}
        models = ([val.strip() for val in vals.split('\t')] for vals in models[1:] if len(vals.strip()) > 0)
        return '[\n%s\n]' % (';\n'.join(("    (%s)" % (', '.join(('"%s"' if v in string_vars else '%s') % vals[header[v]] for v in uvars))) for vals in models))
    else:
        return '(f_tests ())'

if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        smt = (f.readlines()[2]).strip()
    print('(* SMT --- %s --- END *)' % smt)

    ml = flatString(pred.parseString(smt, parseAll = True).asList())
    uvars = sorted(uniq_vars.values())
    uniq_consts = sorted(list(uniq_consts))

    with open('/dev/null', 'w') as err:
        out = check_output(['./chkSAT', sys.argv[1], '0'], stderr=err).decode().split("\n")
    if out[0] == 'UNSAT' or out[0] == '~UNKNOWN~':
        sys.exit(1)
    model = dict((uniq_vars[kv[0].strip()], kv[1].strip()) for kv in (line.partition(':')[0::2] for line in filter(None, out[1:])))

    print('\n(*** Variable mapping ***)')
    for kv in sorted(uniq_vars.items(), key=lambda kv: int(kv[1][1:-1])):
        print('(*  %s =+=> %s  *)' % kv)
    print("\nopen Batteries")
    print("open QCheck.Arbitrary")
    print("\nopen Escher_types")
    print("open SpecInfer")
    print("open TestGen")
    print("\nlet index_of = fun s0 s1 -> try (BatString.find s0 s1) with Not_found -> (-1)")
    print("\n\nlet n_arg_gen %s = (fun rand -> (%s))" % (' '.join('g%d' % i for i in range(len(uvars))), ', '.join('g%d rand' % i for i in range(len(uvars)))))
    print("\n\nlet f = fun (%s) -> %s" % (','.join(uvars), ml))
    print("\nlet f_tests () = generate ~n:8192 (n_arg_gen %s)" % (' '.join(('string' if v in string_vars else 'sint') for v in uvars)))
    print("\nlet def_features = (*PYF:x|T(%s)*)" % ','.join(v + (':S' if v in string_vars else ':I') for v in uvars))
    print("\nlet my_features = []")
    print("\nlet post_cond = ((fun x r -> match r with Bad _ -> false | Ok z -> z), \"true\")")
    print("\nlet tests = (%s) :: %s" % (', '.join(model[v] for v in uvars), genTests()))
    print("\n\nlet typo = [ %s ]" % (' ; '.join(('TString' if v in string_vars else 'TInt') for v in uvars)))
    print("\nlet trans = fun (%s) -> [ %s ]" % (','.join(uvars), ' ; '.join(('of_string ' if v in string_vars else 'of_int ') + v for v in uvars)))
    print("\nlet test_trans = fun (l) -> List.(%s)" % ' , '.join(('(%s (nth l %d))' % (('from_string' if v in string_vars else 'from_int'), i)) for (i,v) in enumerate(uvars)))
    print("\n\n\nlet () = print_cnf stdout (pacLearnSpecNSATVerify f tests (def_features @ my_features) post_cond (typo, trans) [%s] test_trans \"%s\")" % ('; '.join(str(i) for i in uniq_consts), sys.argv[1]))
