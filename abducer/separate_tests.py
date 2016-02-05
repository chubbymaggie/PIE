#!/usr/bin/python

import os
import sys

if __name__ == "__main__":
    
    with open(sys.argv[1], 'r') as f:
        header = f.readline()
        counter = 1
        content = ''
        for line in f.readlines():
            if (line.startswith('---')):
                tests_name = sys.argv[1] + '_' + str(counter)
                if (not os.path.isfile(tests_name)):
                    with open(tests_name, 'w') as tf:
                        tf.write(header)
                with open(tests_name, 'a') as tf:
                    tf.write(content)
                counter = counter + 1
                content = ''
            else:
                content = content + line
        if (len(content) > 0):
            tests_name = sys.argv[1] + '_' + str(counter)
            if (not os.path.isfile(tests_name)):
                with open(tests_name, 'w') as tf:
                    tf.write(header)
            with open(tests_name, 'a') as tf:
                tf.write(content)
