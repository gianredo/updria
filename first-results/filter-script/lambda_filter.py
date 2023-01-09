import readline
from string import Template
from unicodedata import name
import sys
import os

def do_filter(iterable):
    result = "?"
    time = 0
    num_used_preds = 0    
    memout = False
    for line in iterable:
        line = line.strip()
        if line == 'safe':
            result = 'safe'
        elif line == 'unsafe':
            result = 'unsafe'
        elif line.startswith('verification time'):
            try:
                _, time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('num used predicates'):
            try:
                _, num_used_preds = line.split(':', 1)
            except ValueError: pass
    t = Template('$result, $time, $num_used_preds \n')
    return t.substitute(locals())

if __name__ == '__main__':

    directory = os.fsencode(sys.argv[1])    
    for file in os.listdir(directory):
        filename = os.fsdecode(file)
        if filename.endswith(".stdout"): 
            f = open(sys.argv[1] + '/' + filename)
            print(filename + ', ' + do_filter(f.readlines()))
        else:
            continue
