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
    try:
        uniq_consts.add(int(t[0]))
    except:
        uniq_consts.add(t[0])

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

###

from pyparsing import alphas, alphanums, Combine, Forward, Group, Literal, \
                      nums, oneOf, opAssoc, operatorPrecedence, Optional, \
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

GET, CAT, HAS, IND, LEN, REP, SUB, EQL = map(Literal, '#get #cat #has #ind #len #rep #sub #eql'.split())

var = Word(alphas+'_:$', alphanums+'_:$').setParseAction(addVar)
ival = Combine(Optional('-') + Word(nums)).setParseAction(addConst)
ivar = (ival + var).setParseAction(lambda s,l,t: [t[0], '*', t[1]])

term = ivar | ival | var | QuotedString(quoteChar='"', unquoteResults=False).setParseAction(addConst)

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
        | (EQL + LPAR + expr + COMMA + expr + RPAR).setParseAction(lambda s,l,t: [['(=)', chkString(t[1]), chkString(t[2])]])
        | Group(expr + rop + expr)
        | (LPAR + stmt + RPAR))

pred = operatorPrecedence(stmt, [
                            (NOT, 1, opAssoc.RIGHT, lambda s,l,t: ['not', t[0][1:]]),
                            (bop, 2, opAssoc.LEFT, )
                         ])

###

RAND_TEST_COUNT = 8192
NO_DEF_FEATURES = True
INITIAL_CHK_SAT = False
ESCHER_MODE = True

def genTests():
    if os.path.isfile('final_tests'):
        with open('final_tests') as f:
            models = f.readlines()
        header = {uniq_vars[name.strip()] : idx for idx, name in enumerate(models[0].split('\t')) if name.strip() in uniq_vars}
        models = ([val.strip() for val in vals.split('\t')] for vals in models[1:] if len(vals.strip()) > 0)
        return '[\n%s\n]' % (';\n'.join(("    (%s)" % (', '.join(('"%s"' if v in string_vars else '%s') % vals[header[v]] for v in uvars))) for vals in models))
    else:
        return '(f_tests ())'

# argv[1] = filename
# argv[2] = record filename
# argv[3] = Escher mode?
# argv[4] = conflict group size

if __name__ == "__main__":
    ESCHER_MODE = True if len(sys.argv) > 3 and sys.argv[3] == 'escher' else False

    with open(sys.argv[1]) as f:
        smt = (f.readlines()[2]).strip()
    print('(* SMT --- %s --- END *)' % smt)

    ml = flatString(pred.parseString(smt, parseAll = True).asList())
    uvars = sorted(uniq_vars.values())
    uniq_consts = list(uniq_consts)

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
    print("open Pie")
    print("open TestGen")
    print("\n\nlet index_of = fun s0 s1 -> try (BatString.find s0 s1) with Not_found -> (-1)")
    print("\n\nlet n_arg_gen %s = (fun rand -> (%s))" % (' '.join('g%d' % i for i in range(len(uvars))), ', '.join('g%d rand' % i for i in range(len(uvars)))))
    print("\n\nlet n_arg_dumper %s (%s) = \"(\" ^ %s ^ \")\"" % (' '.join('d%d' % i for i in range(len(uvars))), ', '.join('v%d' % i for i in range(len(uvars))), ' ^ ", " ^ '.join('(d%d v%d)' % (i, i) for i in range(len(uvars)))))
    print("\n\nlet f = fun (%s) -> %s" % (','.join(uvars), ml))
    print("\nlet f_tests () = generate ~n:%d (n_arg_gen %s)" % (RAND_TEST_COUNT, ' '.join(('string' if v in string_vars else 'sint') for v in uvars)))
    print("\nlet f_dumper = n_arg_dumper %s" % (' '.join(('string_dumper' if v in string_vars else 'int_dumper') for v in uvars)))
    print("\nlet consts = [%s]" % ('; '.join("VString %s" % c if type(c) is str else "VInt %d" % c for c in uniq_consts)))
    if NO_DEF_FEATURES:
        print("\nlet def_features = []")
    else:
        print("\nlet def_features = (*PYF:x|T(%s)*)" % ','.join(v + (':S' if v in string_vars else ':I') for v in uvars))
    print("\nlet my_features = []")
    print("\nlet post_cond = ((fun x r -> match r with Bad _ -> false | Ok z -> z), \"true\")")
    if INITIAL_CHK_SAT:
        print("\nlet tests = (%s) :: %s" % (', '.join(model[v] for v in uvars), genTests()))
    else:
        print("\nlet tests = %s" % genTests())
    print("\n\nlet typo = [ %s ]" % (' ; '.join(('TString' if v in string_vars else 'TInt') for v in uvars)))
    print("\nlet trans = fun (%s) -> [ %s ]" % (','.join(uvars), ' ; '.join(('of_string ' if v in string_vars else 'of_int ') + v for v in uvars)))
    print("\nlet test_trans = fun (l) -> List.(%s)" % ' , '.join(('(%s (nth l %d))' % (('from_string' if v in string_vars else 'from_int'), i)) for (i,v) in enumerate(uvars)))
    if ESCHER_MODE:
        print("\n\n\nlet () = output_string stdout (snd (escherSynthAndVerify ~dump:(\"%s\", f_dumper) ~record:\"%s\" ~consts:consts f tests post_cond (typo, trans) test_trans \"%s\"))" % (sys.argv[1], sys.argv[2], sys.argv[1]))
    else:
        print("\n\n\nlet () = max_conflict_set_size := %s ; print_cnf stdout (pacLearnSpecAndVerify ~dump:(\"%s\", f_dumper) ~record:\"%s\" ~consts:consts f tests (def_features @ my_features) post_cond (typo, trans) test_trans \"%s\")" % ("1000000000" if sys.argv[4] == "all" else sys.argv[4], sys.argv[1], sys.argv[2], sys.argv[1]))
