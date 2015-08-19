#!/usr/bin/python

import multiprocessing as mp
import subprocess
import sys

from mcf2smtlib import smtlib2_string_from_file, string_from_cvc4_model, \
                       string_from_z3str_model, substitute_model, z3str_to_cvc4
from time import sleep

epsilon = 0.03
timeout = 8.00

sema = mp.Semaphore(2)

def runZ3Str2(smtdata, queue):
    with sema:
        z3str_in = smtdata + '\n(check-sat)\n'
        with open('/tmp/z3str.in', 'w') as f:
            f.write(z3str_in)

        z3str_out = subprocess.check_output(['/data/Repos/Z3-str/Z3-str.py', '-f', '/tmp/z3str.in']).split('\n')
        z3str_res = z3str_out[1][3:].lower()

        if z3str_res == 'unsat':
            res = 'UNSAT'
        else:
            res = string_from_z3str_model(z3str_out)

        queue.put(['z3str', res])

def runCVC4(smtdata, queue):
    with sema:
        cvc4_in = ('\n'.join([
                    '(set-option :produce-models true)',
                    '(set-option :strings-fmf true)',
                    '(set-logic QF_S)'])
                + smtdata
                + '\n(check-sat)\n')
        cvc4 = subprocess.Popen(['cvc4', '--lang', 'smt', '--rewrite-divk', '--strings-exp'],
                                stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE,
                                stderr=sys.stderr)
        cvc4.stdin.write(cvc4_in)
        cvc4_res = cvc4.stdout.readline().strip()

        res = 'ERROR'
        if cvc4_res == 'unsat':
            res = 'UNSAT'
        elif cvc4_res == 'sat' or cvc4_res == 'valid':
            res = string_from_cvc4_model(cvc4)

        if res == 'ERROR':
            sleep(timeout)
        queue.put(['cvc4', res])

if __name__ == '__main__':
    q = mp.Queue()
    vals = dict()

    smtdata = (smtlib2_string_from_file('define-fun goal () Bool',
                                       sys.argv[1], sys.argv[3] if len(sys.argv) > 3 else "1",
                                       sys.argv[2], sys.argv[4] if len(sys.argv) > 4 else "1")
               + "\n(assert (not goal))")

    jobs = [('str', mp.Process(target=runZ3Str2, args=(smtdata, q))),
            ('cvc4', mp.Process(target=runCVC4, args=(z3str_to_cvc4(smtdata), q)))]
    [j.start() for (p, j) in jobs]
    sleep(epsilon)

    sema_status = sema.acquire(timeout=timeout)
    [subprocess.call(['killall', p]) for (p, j) in jobs if j.is_alive()]
    [j.terminate() for (p, j) in jobs if j.is_alive()]

    # If we have a timeout, abort
    if not sema_status:
        print("~UNKNOWN~")
        sys.exit(1)

    assert(not q.empty())
    while not q.empty():
        item = q.get(False)
        vals[item[0]] = item[1]

    # If we have an answer from CVC4 or we have an UNSAT, trust it
    if 'cvc4' in vals:
        print(vals['cvc4'])
        sys.exit(0)
    elif vals['z3str'] == 'UNSAT':
        print(vals['z3str'])
        sys.exit(0)

    # Only remaining case is Z3Str reporting a model which we need to verify
    smtdata = z3str_to_cvc4(smtdata).strip().split('\n')[-1]
    smtdata = substitute_model(smtdata, vals['z3str']) + '\n(check-sat)'

    sema.release()
    runCVC4(smtdata, q)
    item = q.get()
    if item[1] != 'UNSAT' and item[1] != 'ERROR':
        print(vals['z3str'])
        sys.exit(0)
    else:
        print('~UNKNOWN~')
        sys.exit(1)
