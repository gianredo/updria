'''
UPDR + IA PROTOTYPE
'''
from _vmtparser import *
from _mcmtparser import *
from _updria import *
import sys


def translate_int_index(opts, env, ts):
    '''
    function to translate ts from mcmt
    '''
    index_tp = msat_get_simple_type(env, "index")
    toint_decl = msat_declare_function(
        env, "index2int", msat_get_function_type(env, [index_tp], INT))
    def toint(t):
        return msat_make_uf(env, toint_decl, [t])

    vmap = {}
    cache = {}    

    def translate_indices(formula):
        def visit(e, t, pre):
            if t in cache:
                return MSAT_VISIT_SKIP
            if not pre:
                if msat_term_is_variable(e, t):
                    v = msat_make_variable(env, "i_%d" % id_(t), index_tp)
                    vmap[t] = v
                    tt = toint(v)
                elif msat_term_is_forall(e, t):
                    tt = msat_make_forall(e, vmap[arg(t, 0)], cache[arg(t, 1)])
                elif msat_term_is_exists(e, t):
                    tt = msat_make_exists(e, vmap[arg(t, 0)], cache[arg(t, 1)])
                else:
                    tt = term(t, [cache[a] for a in args(t)])
                cache[t] = tt
            return MSAT_VISIT_PROCESS
        msat_visit_term(env, formula, visit)
        return cache[formula]

    new_init = translate_indices(ts.init)
    new_rules = []
    for r in ts.trans_rules:
        new_rules.append(translate_indices(r))

    new_axioms = []
    for r in ts.axioms:
        new_axioms.append(translate_indices(r))

    new_prop = translate_indices(ts.prop)

    a, b = QVar('a', index_tp), QVar('b', index_tp)
    inj_axiom = Forall(a, Forall(b, Iff(Eq(a, b), Eq(toint(a), toint(b)))))
    new_axioms.append(inj_axiom)

    return ParametricTransitionSystem([msat_type_repr(index_tp)], ts.statevars, new_axioms, new_init, new_rules, ts.frozenvars, new_prop)

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
    if opts.input_language == 'mcmt':
        ts = translate_int_index(opts, env, ts)
    # ts is a ParamTransitionSystem
    with Timer('verification_time'):
        res = updria(opts, ts)
    from _updria import _stats
    print('Stats:')
    print(str(_stats))

if __name__ == '__main__':
    main()