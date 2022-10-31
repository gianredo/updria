'''
UPDR + IA PROTOTYPE
'''
from _vmtparser import *
from _updria import *
import sys


def parse(opts):
    if opts.infile is not None:
        with open(opts.infile) as f:
            data = f.read()
    else:
        data = sys.stdin.read()    
    return parse_vmt(opts, data)   


def main():
    opts = getopts()
    ts = parse(opts)
    # ts is a ParamTransitionSystem
    res = updria(opts, ts)


if __name__ == '__main__':
    main()