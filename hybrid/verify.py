#!/usr/bin/python

import multiprocessing as mp
import subprocess
import sys

from time import sleep
from Queue import Empty

from mcf2smtlib import vars_from_smtlib, smtlib2_string_from_file, substitute_model, \
     run_CVC4_internal, run_Z3_internal, run_Z3Str2_internal, z3str_to_cvc4, \
     epsilon, timeout, devnull, increment_record

def runZ3(sema, smtdata, queue):
    with sema:
        res = run_Z3_internal(smtdata)
        if res == 'ERROR':
            sleep(timeout)
        elif res[:3]== 'SAT':
            vsmtdata = substitute_model(smtdata, res)
            vres = run_Z3_internal(vsmtdata, False)
            res = 'ERROR' if vres != 'SAT' else res

        queue.put(['z3', res])
        sleep(epsilon)

def runZ3Str2(sema, smtdata, queue):
    with sema:
        res = run_Z3Str2_internal(smtdata)
        if res == 'ERROR':
            sleep(timeout)
        elif res[:3] == 'SAT':
            vsmtdata = substitute_model(smtdata, res)
            vres = run_Z3Str2_internal(vsmtdata, False)
            res = 'ERROR' if vres != 'SAT' else res

        queue.put(['z3str', res])
        sleep(epsilon)

def runCVC4(sema, smtdata, queue):
    with sema:
        res = run_CVC4_internal(smtdata)
        if res == 'ERROR':
            sleep(timeout)
        elif res[:3] == 'SAT':
            vsmtdata = substitute_model(smtdata, res)
            vres = run_CVC4_internal(vsmtdata, False)
            res = 'ERROR' if vres != 'SAT' else res

        queue.put(['cvc4', res])
        sleep(epsilon)

def unknownAction(smtdata):
    sys.stderr.write('''[!] None of the solvers could verify the following SMTLib2 query:
                     ----------------------------------------------------------------------------------------------------
                     %s
                     ----------------------------------------------------------------------------------------------------
                     ''' % smtdata)

    satness = -1
    while satness != 0 and satness != 1:
        sys.stderr.write('[?] Please enter [0] if the query is SAT; or [1] if it is UNSAT --> ')
        satness = int(raw_input())

    if satness == 1:
        return 'UNSAT'
    else:
        sys.stderr.write('[>] Please provide a model (quote the string values) :\n')
        all_vars = vars_from_smtlib(smtdata)
        vals = all_vars
        for var in all_vars.items():
            sys.stderr.write('  [+] Value of %s (%s) :: ' % var)
            vals[var[0]] = raw_input()
            return 'SAT @ MANUAL\n%s' % '\n'.join('%s : %s' % v for v in vals.items())

if __name__ == '__main__':
    error = True
    acquired = 0

    vals = dict()
    q = mp.Queue()

    smtdata = (smtlib2_string_from_file('define-fun goal () Bool',
                                        sys.argv[1], sys.argv[3] if len(sys.argv) > 3 else "1",
                                        sys.argv[2], sys.argv[4] if len(sys.argv) > 4 else "1")
               + "\n(assert (not goal))")

    sema = mp.BoundedSemaphore(3)
    jobs = [('str', mp.Process(target=runZ3Str2, args=(sema, smtdata, q))),
            ('z3', mp.Process(target=runZ3, args=(sema, smtdata, q))),
            ('cvc4', mp.Process(target=runCVC4, args=(sema, z3str_to_cvc4(smtdata), q)))]
    [j.start() for (p, j) in jobs]
    sleep(epsilon)

    final_result = ''
    try:
        # If we still have error, and have other verifiers running
        while error and acquired < len(jobs):
            acquired += 1
            sema_status = sema.acquire(timeout=timeout)
            if not sema_status:
                raise Exception

            while True:
                try:
                    item = q.get(False)
                    if item[1] != 'ERROR':
                        error = False
                        vals[item[0]] = item[1]
                except Empty:
                    break

        # If we finally have no non-error answers or we have both SAT and UNSAT
        if error or ('UNSAT' in vals.values() and True in (v[:4] == 'SAT' for v in vals.values())):
            raise Exception

        final_result = vals.popitem()[1]
        if len(sys.argv) > 5:
            increment_record(sys.argv[5], final_result.split()[0].lower())

    except Exception:
        final_result = unknownAction(smtdata)
        if len(sys.argv) > 5:
            increment_record(sys.argv[5], 'unk')

    finally:
        # Stop the running verifiers
        [subprocess.call(['killall', p], stdout=devnull, stderr=devnull) for (p, j) in jobs if j.is_alive()]
        [j.terminate() for (p, j) in jobs if j.is_alive()]

        print(final_result)
