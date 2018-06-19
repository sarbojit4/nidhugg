#!/usr/bin/python3

# Copyright (C) 2018 Magnus Lång and Tuan Phong Ngo
# Based on source code of Carl Leonardsson
# Run swsc on all C tests.

import datetime
import subprocess
import sys
import tempfile
import os
import time
import argparse
import multiprocessing

curDir = os.getcwd()
LITMUSDIR = curDir + '/C-tests'
OUTPUTTFILE = curDir + '/swsc.results.txt'
LISTFILE = curDir + '/nidhugg.results.txt'
# FIX ME
SWSCBIN = 'swscc'

class bcolors:
    FAIL = '\033[91m'
    OKGREEN = '\033[92m'
    WARNING = '\033[93m'
    ENDC = '\033[0m'


def get_expected(fname):
    f = open(fname,'r')
    l = []

    for ln in f:
        ln = ln.strip()
        if len(ln) and not(ln[0] == '#'):
            segments = ln.split()
            assert(segments[1] == 'Allow' or segments[1] == 'Forbid')
            l.append({'tstname' : segments[0],
                      'expect allow' : (segments[1] == 'Allow'),
                      'expected trace count' : int(segments[3])})
    f.close()

    return l


def res_to_string(tst, res):
    s = tst['tstname']
    
    if not('allow' in res):
        s = s + bcolors.FAIL + ' FAILURE: ' + bcolors.ENDC
        if 'failure' in tst:
            s = s + tst['failure']
        else:
            s = s + '(unknown)'
        return s

    if res['allow'] != tst['expect allow']:
        s = s + bcolors.FAIL + ' FAILURE: unexpected result ' + ('Allow' if tst['nidhugg allow'] else 'Forbid') + bcolors.ENDC
        return s
    else:
        s = s + ' ' + ('Allow' if res['allow'] else 'Forbid')

    if tst['expected trace count'] != res['tracecount']:
    	s = s + bcolors.FAIL + ' FAILURE: not same trace as ' + str(tst['expected trace count']) + bcolors.ENDC

    s = s + bcolors.OKGREEN + ' OK ' + bcolors.ENDC + ' : ' + str(res['tracecount'])

    return s

    
def runallswsc(jobs):
    logfile = open(OUTPUTTFILE, 'w')
    logfile.write('# Results of running swsc to all C tests.\n')
    version = subprocess.check_output([SWSCBIN, '--version'], stderr = subprocess.STDOUT).decode()
    logfile.write('# ' + version)
    logfile.write('# swsc --wsc TEST.c \n')
    logfile.write('# The tests where executed using test-swsc.py.\n')
    logfile.write('# Date: ' + datetime.datetime.now().strftime('%y%m%d-%H:%M')+'\n')
    logfile.write('\n')
    
    totaltracecount = 0
    tests = get_expected(LISTFILE)
    initial_count = len(tests)
    t0 = time.time()

    q = multiprocessing.Queue()
    workers = []
    work = dict()

    def give_work(w, p):
        if len(tests) > 0:
            tst = tests.pop()
            n = initial_count - len(tests)
            p.send((n,tst))
            work[n] = (tst,w,p)
        else:
            p.send('die')
            w.join()

    for _ in range(min(len(tests), jobs)):
        (o, i) = multiprocessing.Pipe(False)
        p = multiprocessing.Process(target=slave, args=(q, o))
        p.start()
        workers.append((p, i))
        give_work(p, i)

    while len(work) > 0:
        (done_n, res) = q.get()
        (tst,w,p) = work.pop(done_n)
        totaltracecount += res['tracecount']
        print('{0:4}: '.format(done_n), end = '')
        print(res_to_string(tst, res))
        logfile.write(res_to_string(tst, res)  + '\n')
        give_work(w, p)

    runtime = time.time() - t0
    logfile.write('# Total number of traces: ' + str(totaltracecount) + '\n')
    logfile.write('# Total running time: {0:.2f} s\n'.format(runtime))
    logfile.close()

def slave(q, p):
    while True:
        cmd = p.recv()
        if cmd == 'die': break
        (n,tst) = cmd
        res = run_test(tst)
        q.put((n, res))

def run_test(tst):
    res = dict()
    try:
        out = subprocess.check_output([SWSCBIN, '--wsc',
                                       LITMUSDIR + '/' + tst['tstname'] + '.c'],
                                      stderr = subprocess.STDOUT).decode()
        parts_0 = out.split("\n")
        error_info = parts_0[-6]
        trace_info = parts_0[-7]
        res['tracecount'] = int(trace_info.split(":")[1].split()[0])
        if out.find('No errors were detected') >= 0:
            res['allow'] = False
        else:
            res['allow'] = True
    except subprocess.CalledProcessError:
        res['failure'] = SWSCBIN
        res['tracecount'] = -1
    return res

def runoneswsc(filename):
    found = False

    for tst in get_expected(LISTFILE):
        if tst['tstname'] != filename:
            continue
        else:
            found = True
            res = run_test(tst)
            print(res_to_string(tst, res))
            break

    if found == False:
        print('Test case was not found!')

####################################################

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('-j', dest='jobs', metavar='N', type=int, default=1,
                        help='Numer or parallel jobs')
    modes = parser.add_subparsers(metavar='mode',dest='mode')
    all_parser = modes.add_parser('all', help='Run all tests')
    one_parser = modes.add_parser('one', help='Run single test')
    one_parser.add_argument('test', help='testname(without_dot_c)');
    args = parser.parse_args()
    if (args.mode == "all"):
        runallswsc(args.jobs)
        sys.exit(0)
    elif (args.mode == "one"):
        runoneswsc(args.test)
        sys.exit(0)
    else:
        parser.print_help()
