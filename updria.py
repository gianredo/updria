'''
UPDR + IA PROTOTYPE
'''
from _vmtparser import *
from _mcmtparser import *
from _updria import *
import sys



def parse(opts):
    if opts.infile is not None:
        with open(opts.infile) as f:
            data = f.read()
    else:
        data = sys.stdin.read()  
    
    if opts.input_language == 'mcmt':
        parser = MCMTParser()
        return parser.parse(data)
    else:
        return parse_vmt(opts, data)   


def main():
    opts = getopts()
    ts = parse(opts)
        
    # ts is a ParamTransitionSystem
    with Timer('verification_time'):
        res = updria(opts, ts)
    from _updria import _stats
    print('Stats:')
    print(str(_stats))

if __name__ == '__main__':
    main()