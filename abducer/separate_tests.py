#!/usr/bin/python

import os
import sys

if __name__ == "__main__":
    with open(sys.argv[1], 'r') as f:
        content = []
        loopid = '1'
        header = f.readline()
        varcount = len(header.split())
        for line in f.readlines():
            if (line.startswith('---')):
                loopid = line[3:-4]
                if (len(content) > 0):
                    tests_name = sys.argv[1] + '_' + loopid
                    if (not os.path.isfile(tests_name)):
                        with open(tests_name, 'w') as tf:
                            tf.write(header)
                    with open(tests_name, 'a') as tf:
                        tf.write(''.join(content))
                    with open('loopids', 'a') as lf:
                        lf.write(loopid + '\n')
                    content = []
            else:
                if len(line.split()) == varcount:
                    content.append(line)
                # else ignore bad (partial) line
        if (len(content) > 0):
            tests_name = sys.argv[1] + '_' + loopid
            if (not os.path.isfile(tests_name)):
                with open(tests_name, 'w') as tf:
                    tf.write(header)
            with open(tests_name, 'a') as tf:
                tf.write(''.join(content))
            with open('loopids', 'a') as lf:
                lf.write(loopid + '\n')
