#!/usr/bin/env python3
# UPDRIA PROTOTYPE 
from typing import Dict, NamedTuple
from xml.dom import NotSupportedErr
from mathsat import *
import sys
import itertools
import functools
from collections import namedtuple
import argparse
from z3 import *

#-----------------------------------------------------------------------------
# user-configurable options
#-----------------------------------------------------------------------------

class Options:
    def __init__(self):
        self.vmt_property = 0      
        

    def __str__(self):
        return "\n".join(sorted([
            "vmt_property = %s" % self.vmt_property,
            ]))
# end of class Options

def getopts():
    p = argparse.ArgumentParser()
    def add_flag(n):
        dest = n.replace('-', '_')
        p.add_argument('--%s' % n, action='store_true', dest=dest)
        p.add_argument('--no-%s' % n, action='store_false', dest=dest)
    p.add_argument('--vmt-property', type=int, default=0)
    p.add_argument('infile', nargs='?')
    opts = Options()
    p.parse_args(namespace=opts)
    return opts

#-----------------------------------------------------------------------------
# convenience functions (PySMT style)
#-----------------------------------------------------------------------------
env = msat_create_env({'printer.defines_prefix' : 'd!',
                       'allow_bool_function_args' : 'true'})

BOOL = msat_get_bool_type(env)
INT = msat_get_integer_type(env)
REAL = msat_get_rational_type(env)

def TRUE(): return msat_make_true(env)
def FALSE(): return msat_make_false(env)
def And(*args):
    return functools.reduce(lambda a, b: msat_make_and(env, a, b), args, TRUE())
def Or(*args):
    return functools.reduce(lambda a, b: msat_make_or(env, a, b), args, FALSE())
def Int(v): return msat_make_number(env, str(v))
def Not(t): return msat_make_not(env, t)
def Implies(a, b): return msat_make_or(env, msat_make_not(env, a), b)
def Iff(a, b): return msat_make_iff(env, a, b)
def GE(a, b): return msat_make_leq(env, b, a)
def GT(a, b): return msat_make_not(env, msat_make_leq(env, a, b))
def LE(a, b): return GE(b, a)
def LT(a, b): return GT(b, a)
def Plus(a, b): return msat_make_plus(env, a, b)
def Times(a, b): return msat_make_times(env, a, b)
def Minus(a, b): return Plus(a, Times(Int(-1), b))
def Eq(a, b): return msat_make_eq(env, a, b)
def Ite(c, t, e):
    if msat_is_bool_type(env, msat_term_get_type(t)):
        return And(Implies(c, t), Implies(Not(c), e))
    else:
        return msat_make_term_ite(env, c, t, e)
def Exists(v, f): return msat_make_exists(env, v, f)
def Forall(v, f): return msat_make_forall(env, v, f)
def Alldiff(vlist): return And(*(Not(Eq(v1, v2)) for v1, v2 in pair(vlist)))

def id_(t): return msat_term_id(t)
def name(t): return msat_decl_get_name(msat_term_get_decl(t))
def smt2(t): return msat_to_smtlib2_term(env, t)
def args(t): return (msat_term_get_arg(t, i) for i in range(msat_term_arity(t)))
def arg(t, i): return msat_term_get_arg(t, i)
def arity(t): return msat_term_arity(t)
def type_(t): return msat_term_get_type(t)
def term(t, children):
    return msat_make_term(env, msat_term_get_decl(t), children)

_tpmap = {
    msat_type_repr(BOOL): BOOL,
    msat_type_repr(INT): INT,
    msat_type_repr(REAL): REAL,
    }
def mksort(name):
    return _tpmap.get(name, msat_get_simple_type(env, name))

def substitute(t, tosubst, values):
    return msat_apply_substitution(env, t, tosubst, values)

def pair(vlist):
    for i, a in enumerate(vlist):
        for j in range(i+1, len(vlist)):
            b = vlist[j]
            yield (a, b)

FORALL, EXISTS = 0, 1
def split_quantifier(t):
    qvars = []
    if msat_term_is_exists(env, t):
        kind = EXISTS
        test = msat_term_is_exists
    else:
        kind = FORALL
        test = msat_term_is_forall
    while test(env, t):
        qvars.append(arg(t, 0))
        t = arg(t, 1)
    return kind, qvars, t

# p_var are used for the ground instances
p_var_cache = {}
all_p_vars = set()

def nextvar(v):
    return Var(name(v) + ".next", type_(v))


def p_var(idx, sort):
    assert not MSAT_ERROR_TYPE(sort)
    res = p_var_cache.get(sort)
    if not res:
        p = Var("P{%s}{%d}" % (msat_type_repr(sort), idx), sort)
        all_p_vars.add(p)
        p_var_cache[sort] = [p]        
    elif res and len(res) <= idx:
        p = Var("P{%s}{%d}" % (msat_type_repr(sort), idx), sort)
        all_p_vars.add(p)
        p_var_cache[sort].append(p)
    else:
        p = res[idx]
    return p


def is_prophecy(v):
    return v in all_p_vars
           
_param_map = {}
_params = set()
_param_read_funs = set()

def Param(name, idxtplist, elemtp):
    res = _param_map.get(name)
    if res is None:
        elemname = "[%s]" % msat_type_repr(elemtp)
        idxname = []
        for idxtp in idxtplist:
            idxname.append("[%s]" % msat_type_repr(idxtp)) 
        ptype = msat_get_simple_type(env, elemname)
        ftp = msat_get_function_type(env, [ptype] + idxtplist, elemtp)
        read_fun = msat_declare_function(
            env, "Param%s%s" % (str(idxname), elemname), ftp)
        _param_read_funs.add(msat_decl_id(read_fun))
                
        d = msat_declare_function(env, name, ptype)
        p = msat_make_constant(env, d)
        
        res = (p, read_fun)
        _param_map[name] = res
        _params.add(p)
    return res[0]


def ParamVal(param, idxlist):
    d = msat_term_get_decl(param)
    name = msat_decl_get_name(d)
    read_fun = _param_map[name][1]
    return msat_make_uf(env, read_fun, [param] + idxlist)

def is_param(v): return v in _params
def is_param_val(t):
    return msat_term_is_uf(env, t) \
           and msat_decl_id(msat_term_get_decl(t)) in _param_read_funs

def Var(name, tp):
    d = msat_declare_function(env, name, tp)
    return msat_make_constant(env, d)

_qvars = {}
def QVar(name, sort):
    res = _qvars.get(name)
    if not res:
        res = msat_make_variable(env, name, sort)
        _qvars[name] = res
    return res


def is_qvar(t): return msat_term_is_variable(env, t)


def get_free_vars(formula):
    free_vars = list()

    def get_vars(e: msat_env, term : msat_term, pre : bool):
        nonlocal free_vars 
        if pre:
            if msat_term_is_variable(e, term):
                if term not in set(free_vars):
                    free_vars.append(term)   

        if not pre:        
            if msat_term_is_forall(e, term) or msat_term_is_exists(e, term):
                for var in free_vars:
                    if name(var) == name(msat_term_get_arg(term, 0)):
                        free_vars.remove(var)                                     

        return MSAT_VISIT_PROCESS     
    
    msat_visit_term(env, formula, get_vars)
    return free_vars
#-----------------------------------------------------------------------------
# utility functions and statistics
#-----------------------------------------------------------------------------

_print = print
def print(*args, **kwds):
    _print(*args, **kwds)
    sys.stdout.flush()

def banner(msg):
    print('=' * 80)
    print(msg)
    print('=' * 80)
#-----------------------------------------------------------------------------
# Problem definition
#-----------------------------------------------------------------------------
TransitionSystem = namedtuple('TransitionSystem',
                              ['statevars', 'init',
                               'trans', 'trans_guard', 'prop'])

ParametricTransitionSystem = namedtuple(
    'ParametricTransitionSystem',
    ['sorts', 'statevars', 'axioms', 'init', 'trans_rules', 'frozenvars',
     'prop'])

SAFE, UNSAFE, UNKNOWN = 0, 1, 2
VerificationResult = namedtuple('VerificationResult', ['status', 'witness'])

#-----------------------------------------------------------------------------
# updria  verification functions
#-----------------------------------------------------------------------------

Cti = namedtuple('Cti', ['diagram', 'universe_dict', 'frame_number'])
## Global parameters of UPDRIA

#frame sequence is a list of list of diagrams
frame_sequence = []

#cti_queue is a list of cti
cti_queue = [] 

#frame_coutner is the length of frame_sequence
frame_coutner = 0

def find_initial_predicates(opts, sorts, init_formula, prop):

    predicates = set()

    def find_predicates(env, t, pre): 
        nonlocal predicates
        if not pre:
            if msat_term_is_atom(env, t) and not msat_term_is_quantifier(env, t):
                if msat_term_is_equal(env, t) and msat_type_repr(type_(arg(t, 0))) in sorts:
                    #equality among index variables
                    pass

                #if predicates among indexes, skip
                #maybe consider using this with an option
                elif msat_term_is_uf(env, t):
                    d = msat_term_get_decl(d)
                    index_sort_flag = True
                    for i in range(msat_decl_get_arity(d)):
                        if msat_type_repr(msat_decl_get_arg_type(d, i)) not in sorts:
                            index_sort_flag = False

                    if not index_sort_flag:
                        predicates.add(t)

                else:
                    predicates.add(t)

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, init_formula, find_predicates)
    msat_visit_term(env, prop, find_predicates)

    return sorted(predicates, key=msat_term_id)


def get_abstract_predicates(predicates):
    new_preds = {p : FALSE() for p in predicates}
    abstract_vars = set()
    for p in predicates:
        vars = get_free_vars(p)
        if vars:
            #define a fresh boolean symbol
            #the ariety is the number of free vars in p
            tp = msat_get_function_type(env, [type_(x) for x in vars], BOOL)
            f = msat_declare_function(env, 'x_%s' % (smt2(p)), tp)
            abstract_vars.add(f)
            new_preds[p] = msat_make_uf(env, f, vars)
        else:  
            f = Var('x_%s' % (smt2(p)), BOOL)
            abstract_vars.add(msat_term_get_decl(f))
            new_preds[p] = f
            
    
    return new_preds, sorted(abstract_vars, key=msat_decl_id)


def remove_duplicates(abstract_predicates):
    '''
    rewrite the free variables in the predicate to remove duplicates as p(i1) and p(i2)
    '''
    norm_predicates_dict = dict()

    for p in abstract_predicates:
        freevars = get_free_vars(p)
        if freevars:
            for i, x in enumerate(freevars):
                norm_p  = msat_apply_substitution(env, p, [x], [QVar('%s_%d' % (msat_type_repr(type_(x)), i), type_(x))])
                if norm_p not in norm_predicates_dict:
                    norm_predicates_dict[norm_p] = msat_apply_substitution(env, abstract_predicates[p], \
                        [x], [QVar('%s_%d' % (msat_type_repr(type_(x)), i), type_(x))])
        else:
            norm_predicates_dict[p] = abstract_predicates[p]
    
    return norm_predicates_dict


def get_h_formula(abstract_predicates):
    h = And(*[ Iff(p, abstract_predicates[p]) for p in abstract_predicates])
    for var in get_free_vars(h):
        h = Forall(var, h)
    return h


def convert_type(env, tp):
    '''
    takes a msat type 
    return z3 type

    VERY SIMPLIFIED VERSION
    '''
    if msat_is_integer_type(env, tp):
        return z3.IntSort()
    elif msat_is_bool_type(env, tp):
        return z3.BoolSort()
    elif msat_is_rational_type(env, tp):
        return z3.RealSort()
    else:
        return z3.DeclareSort(msat_type_repr(tp))


def convert_predicate(env, p):
    '''
    convert an atomic predicate from mathsat to z3    
    '''
    # #FAILED
    # from pysmt.solvers.msat import MSatConverter
    # from pysmt.solvers.z3 import Z3Converter 
    # from pysmt.shortcuts import get_env

    # env_wrap = lambda: env
    # msatconv = MSatConverter(get_env(), env_wrap)
    # #print(p)
    # pysmt_pred = msatconv.back(p)
    # #print(pysmt_pred)
    # #z3conv = Z3Converter(get_env())
    # #z3_pred = z3conv.convert(pysmt_pred)
    # #print(z3_pred)
    
    # #very simplified version 

    import z3
    z3_atom = True
    cache = {}

    def create_z3_predicate(env, term, pre):
        nonlocal z3_atom 
        if not pre:
            # if msat_term_is_number(env, term):
            #     z3_term = str(term)
            #     cache[term] = z3_term
            #     return MSAT_VISIT_PROCESS

            if msat_term_is_variable(env, term):
                z3_term = z3.Var(msat_term_id(term), convert_type(env, type_(term)))
                cache[term] = z3_term
                return MSAT_VISIT_PROCESS

            if msat_term_is_constant(env, term):
                if msat_term_is_boolean_constant(env, term):
                    z3_atom = z3.Bool(msat_term_repr(term))         
                    return MSAT_VISIT_ABORT
                else:
                    z3_term = z3.Const(str(term), convert_type(env, type_(term)))
                    cache[term] = z3_term
                    return MSAT_VISIT_PROCESS

            elif msat_term_is_uf(env, term):
                d = msat_term_get_decl(term)
                ar = msat_decl_get_arity(d)
                assert ar > 0
                rettp = msat_decl_get_return_type(d)
                
                if not msat_is_bool_type(env, rettp):
                    # term is f(t1, ... tn)
                    z3_fun = z3.Function(name(term), \
                        [convert_type(env, type_(arg(term, i))) for i in range(ar)] \
                             + [convert_type(env, msat_decl_get_return_type(d))])
                    z3_term = z3_fun([cache[arg(term, i)] for i in range(ar)])
                    cache[term] = z3_term
                    return MSAT_VISIT_PROCESS
                else:
                    # this is a predicate
                    
                    # HACK: REPLACEING '|' with '\|'
                    # To obtain the same name as mathsat predicate 

                    z3_fun = z3.Function(name(term).replace('|', '\|'), \
                        [convert_type(env, type_(arg(term, i))) for i in range(ar)] \
                             + [convert_type(env, msat_decl_get_return_type(d))])
                    z3_atom = z3_fun([cache[arg(term, i)] for i in range(ar)])
                    return MSAT_VISIT_ABORT
            else:
                raise NotSupportedErr('not supported translation for %s' %(smt2(term)))

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, p, create_z3_predicate)

    return z3_atom
    

def extract_diagram(predicates, model, sort_names):
    '''
    takes a z3 model and return a msat formula
    which is the diagram of the model
    '''
    # for every sort, take the universe of that sort in the model
    universes = {s : [] for s in sort_names}
    for sort in sort_names:
        if model.get_universe(convert_type(env, mksort(sort))):
            universes[sort] = model.get_universe(convert_type(env, mksort(sort)))

    # create one msat variable for each element in universe
    # this will be existentially quantified in the diagrm
    ex_vars_dict = { s : [QVar(str(x), mksort(s)) \
        for x in universes[s]] for s in sort_names }
    #impose that they are all different 
    diff_constraint = {s : Alldiff(ex_vars_dict[s]) for s in sort_names}

    # TODO!!
    # for all constant symbol c of index sort (pass as an argument)
    # for all var in universe v of index sort
    # if c = v is true in the z3 model
    # compute c = v; otherwise c != v

    # compute the values of each predicate
    predicates_constraint = TRUE()
    for p in predicates:
        #replace free vars with consant variables
        renaming_dict = {a : Var(smt2(a), type_(a)) for a in get_free_vars(p)}
        p = substitute(p, list(renaming_dict), list(renaming_dict.values()))
        z3_predicate = convert_predicate(env, p)
        z3_vars = [z3.Const(smt2(a), convert_type(env, type_(a))) for a in renaming_dict.values()]
        ar = arity(p)
        if ar == 0:
            #arity 0 so the predicate is a boolean constant
            try:
                if model.eval(z3_predicate):
                    predicates_constraint = And(predicates_constraint, p)
                else:
                    predicates_constraint = And(predicates_constraint, Not(p))
            except z3.z3types.Z3Exception as Err:
                #the exception is to catch if we evalue predicate not in the model
                #not sure this is the proper way
                pass
        else: 
            assert ar > 0
            #compute all possible substitution 
            for vars in itertools.product(*[universes[msat_type_repr(type_(arg(p, i)))] for i in range(ar)]):
                # print('substitution')
                # print(vars)        
                       
                #z3 ground predicate 
                ground = z3.substitute(z3_predicate, *zip(z3_vars, vars))
                # print('after substitution')
                # print(ground)

                msat_ground = substitute(p, list(renaming_dict.values()), [QVar(str(x), mksort(str(x.sort()))) for x in vars])
                #print(msat_ground)
                
                #again exception
                try:
                    if model.eval(ground):
                        predicates_constraint = And(predicates_constraint, msat_ground)
                    else:
                        predicates_constraint = And(predicates_constraint, Not(msat_ground))

                except z3.z3types.Z3Exception as Err:
                    pass

    #make the diagram                
    diagram = And(And(*[diff_constraint[s] for s in diff_constraint], predicates_constraint))
    # compute existential clousure
    for s in sort_names:
        for v in ex_vars_dict[s]:
            diagram = Exists(v, diagram)
     
    return diagram, universes


def get_next_abstract_formula(formula, abs_vars):
    cache = {}
    
    #save i1...in
    def build_cache(env, t, pre):
        nonlocal cache
        d = msat_term_get_decl(t)
        if not pre:
            if msat_decl_repr(d) in [msat_decl_repr(f) for f in abs_vars]:
                ar = arity(t)
                cache[t] = [arg(t, i) for i in range(ar)]

        return MSAT_VISIT_PROCESS 
    
    #make the substitution
    def substitute_next_predicates(env, t, pre):
        nonlocal cache, formula
        d = msat_term_get_decl(t)
        if not pre:
            if msat_decl_repr(d) in [msat_decl_repr(f) for f in abs_vars]:
                ar = arity(t)
                if ar > 0:
                    tp = msat_get_function_type(env, [msat_decl_get_arg_type(d, i) for i in range(ar)],\
                        msat_decl_get_return_type(d))
                    next_t = msat_declare_function(env, msat_decl_get_name(d)+'.next', tp)
                    formula = substitute(formula, [t], [msat_make_uf(env, next_t, cache[t])])
                else:
                    formula = substitute(formula, [t], [nextvar(t)])

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, formula, build_cache)
    msat_visit_term(env, formula, substitute_next_predicates)  
    return formula


def get_abs_relative_inductive_check(paramts, abs_vars, frame, diagram, \
    predicates_dict, H_formula, abs_init, initial_constr : Bool = False):    
    
    #we need H_formula for next variables
    #we substitute every (p i1 ... in) with (p.next i1 ... in)
    H_formula_next = get_next_abstract_formula(H_formula, abs_vars)   
    H_formula_next = substitute(H_formula_next, [s[0] for s in paramts.statevars], [s[1] for s in paramts.statevars])       

    next_abs_init = get_next_abstract_formula(abs_init, abs_vars) 

    def barvar(v):
        return Var(name(v) + ".bar", type_(v))

    #we need a dublicate (bar version) of the state vars
    bar_statevars = [ (barvar(a), barvar(b)) for a, b in paramts.statevars]
    predicates_bar_c = [substitute(p, [c[0] for c in paramts.statevars], [bc[0] for bc in bar_statevars]) \
         for p in predicates_dict]

    predicates_next = [substitute(p, [c[0] for c in paramts.statevars], [c[1] for c in paramts.statevars]) \
         for p in predicates_dict]
    
    predicates_bar_n = [substitute(p, [c[0] for c in paramts.statevars], [bc[1] for bc in bar_statevars]) \
         for p in predicates_dict]

    EQ_formula_1 = And(*[Iff(p[0], p[1]) for p in zip(predicates_dict, predicates_bar_c)])
    for var in get_free_vars(EQ_formula_1):
        EQ_formula_1 = Forall(var, EQ_formula_1)
    
    EQ_formula_2 = And(*[Iff(p[0], p[1]) for p in zip(predicates_next, predicates_bar_n)])
    for var in get_free_vars(EQ_formula_2):
        EQ_formula_2 = Forall(var, EQ_formula_2)

    # abstract transition formula
    t_bar = [substitute(t, [c[0] for c in paramts.statevars], [c[0] for c in bar_statevars]) for t in paramts.trans_rules]
    t_bar = [substitute(t, [c[1] for c in paramts.statevars], [c[1] for c in bar_statevars]) for t in t_bar]
    t_bar = Or(*t_bar)

    #next diagram
    next_diagram = get_next_abstract_formula(diagram, abs_vars)

    # print(next_diagram)
    # print(H_formula_next)
    # print(And(*frame))
    # print(diagram)
    # print(t_bar)
    # print(next_diagram)
    # print(EQ_formula_1)
    # print(EQ_formula_2)

    formula = And(And(*frame), t_bar, H_formula, H_formula_next, Not(diagram), EQ_formula_1, EQ_formula_2)
    if initial_constr: 
        formula = Or(formula, next_abs_init)
    formula = And(formula, next_diagram)
    return formula


def get_id(x):
    return Z3_get_ast_id(x.ctx_ref(), x.as_ast())


def minimize_core_aux2(s, core):
    mus = []
    ids = {}
    while core != []:
        c = core[0]
        new_core = mus + core[1:]
        is_sat = s.check(new_core)
        if is_sat == sat:
            mus = mus + [c]
            ids[get_id(c)] = True
            core = core[1:]
        else:
            core = s.unsat_core()
            core = [c for c in core if get_id(c) not in ids]
    return mus


def minimize_core(s):
    core = list(s.unsat_core())
#    print "minimize_core: core = {}".format(core)
    core = minimize_core_aux2(s, core)
#    print "minimize_core: core = {}".format(core)
    return core


def generalize_diagram(paramts, abs_vars, frame, diagram, predicates_dict, H_formula, hat_init):
    kind, qf, body = split_quantifier(diagram)
    assert kind == EXISTS
    def collect(e, tag, formula):
        to_process = [formula]
        seen = set()
        while to_process:
            cur = to_process[-1]
            to_process.pop()
            if cur in seen:
                continue
            seen.add(cur)
            if msat_decl_get_tag(e, msat_term_get_decl(cur)) == tag:
                n = msat_term_arity(cur)
                for i in range(n):
                    to_process.append(msat_term_get_arg(cur, n-1-i))
            else:
                yield cur

    fmlas = [a for a in collect(env, MSAT_TAG_AND, body)]
    alits = [Var("__c%s" % n, BOOL) for n,c in enumerate(fmlas)]
    z3_alits = [z3.Const("__c%s" % n, z3.BoolSort()) for n,c in enumerate(fmlas)]
    cc = [Or(Not(a),c) for a,c in zip(alits,fmlas)]
    n_diagram = And(*cc)
    for v in qf: 
        n_diagram = Exists(v, n_diagram)

    s2 = Solver()
    abs_rel_formula = get_abs_relative_inductive_check(paramts, abs_vars, frame, n_diagram,\
         predicates_dict, H_formula, hat_init, True)

    s2.from_string(msat_to_smtlib2_ext(env, abs_rel_formula, 'UFLIA', True))
    
    is_sat = s2.check(z3_alits)
    if is_sat == z3.sat:
        return None
    else:
        core = minimize_core(s2)
    
    s2.reset()
    core_ids = [get_id(a) for a in core]
    res = [c for a,c in zip(z3_alits,fmlas) if get_id(a) in core_ids]

    g_diagram = And(*res)
    qf = get_free_vars(g_diagram)
    for v in qf: 
        g_diagram = Exists(v, g_diagram)
    return g_diagram


def recblock(paramts, predicates_dict, abs_vars, cti : Cti, H_formula, hat_init) -> Bool :
    
    if cti.frame_number == 0:
        print('CEX! Violation of the initial formula')
        return False
   
    else:    
        #check if the cti is reachable from the last frame              
        
        print('trying to block cex at frame %d' %cti.frame_number)
        # print('trying to block diagram %s' %smt2(cti.diagram))
        abs_rel_formula = get_abs_relative_inductive_check(paramts, abs_vars, frame_sequence[cti.frame_number-1],\
             cti.diagram, predicates_dict, H_formula, hat_init)

        s = Solver()     
        s.from_string(msat_to_smtlib2_ext(env, abs_rel_formula, 'UFLIA', True))
        if s.check() == z3.unsat:      
            print('blocked')          
            cti_queue.remove(cti)        
            # generalize diagram with unsat cores
            print('generalizing diagram...')
            gen_diagram = generalize_diagram(paramts, abs_vars, frame_sequence[cti.frame_number-1],\
             cti.diagram, predicates_dict, H_formula, hat_init)
            # print(gen_diagram)
            # # add diagram to all frames from 1 to frame_number
            for i in range(1, cti.frame_number + 1):
                if Not(gen_diagram) not in set(frame_sequence[i]):
                    frame_sequence[i].append(Not(gen_diagram)) 
            s.reset()
            return True

        elif s.check() == z3.sat:
            model = s.model()
            n_diagram, universe_dict = extract_diagram(predicates_dict.values(), model, paramts.sorts)
            s.reset()
            print('failed...')
            cti_queue.append(Cti(n_diagram, universe_dict, cti.frame_number-1))
            return True

        else:
            assert str(s.check) == 'unknown'
            s.reset()
            raise NotImplementedError


def substitute_diagram(cti : Cti, predicates_dict, abs_vars):
    diagram = cti.diagram
    universe = cti.universe_dict
    kind, qvars, body = split_quantifier(diagram)
    assert kind == EXISTS
    
    cache = {}
    #save i1...in
    def build_cache(env, t, pre):
        nonlocal cache
        d = msat_term_get_decl(t)
        if not pre:
            if msat_decl_repr(d) in [msat_decl_repr(f) for f in abs_vars]:
                ar = arity(t)
                cache[t] = [arg(t, i) for i in range(ar)]

        return MSAT_VISIT_PROCESS 
    
    inverse_dict = {predicates_dict[a] : a for a in predicates_dict}

    #make the substitution
    def substitute_next_predicates(env, t, pre):
        nonlocal cache, body
        d = msat_term_get_decl(t)
        if not pre:
            if msat_decl_repr(d) in [msat_decl_repr(f) for f in abs_vars]:
                ar = arity(t)
                if ar > 0:
                    for c in predicates_dict:
                        sd = msat_term_get_decl(predicates_dict[c])
                        if d == sd:
                            to_sub = substitute(c, get_free_vars(c), cache[t])
                    
                    body = substitute(body, [t], [to_sub])
                else:
                    body = substitute(body, [t], [inverse_dict[t]])

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, body, build_cache)
    msat_visit_term(env, body, substitute_next_predicates)     
   
    for v in qvars:
        body = Exists(v, body)
    
    return body



def updria(opts, paramts : ParametricTransitionSystem):
    global frame_sequence, cti_queue, frame_counter

    predicates = find_initial_predicates(opts, paramts.sorts, paramts.init, paramts.prop) 
    abstract_predicates_dict, abs_vars = get_abstract_predicates(predicates)
    H_formula = get_h_formula(abstract_predicates_dict)
    #compute abstraction of initial formula and property
    hat_init = substitute(paramts.init, \
        list(abstract_predicates_dict), list(abstract_predicates_dict.values()))

    hat_prop = substitute(paramts.prop, \
        list(abstract_predicates_dict), list(abstract_predicates_dict.values()))

    abstract_predicates_dict = remove_duplicates(abstract_predicates_dict)
    # here we switch to z3. probabily using string is inefficent
    # we should use convertor (pystm?) from mathsat to z3
    # convertor is avaible only for predicates

    s = z3.Solver()
    s.from_string(msat_to_smtlib2_ext(env, And(hat_init, Not(hat_prop), H_formula), 'UFLIA', True))
    if s.check() == z3.sat:
         print('unsafe! cex in the initial formula')
         return VerificationResult(UNSAFE, s.model())
    else: 
        print('no initial cex! Entering main loop \n') 
    s.reset()

    # initialize frame sequence
    frame_counter = 1
    frame_sequence.append([hat_init])
    frame_sequence.append([])
    
    #main loop of updr
    while True:
        #there are no more cti's
        assert not cti_queue
        #compute intersection between last frame and bad
        last_frame_formula = And(*[And(*frame_sequence[-1]), H_formula, Not(hat_prop)])
        #pass it to z3
        s.from_string(msat_to_smtlib2_ext(env, last_frame_formula, 'UFLIA', True))
        print('Checking intersection between last frame and property...')

        while s.check() == z3.sat:
            # take a model, extract a diagram
            print('found a cti')
            model = s.model()
            print('extracting diagram...')
            diagram, universe_dict = extract_diagram(abstract_predicates_dict.values(), model, paramts.sorts)
            s.reset()
            # Aadd a cti in the cti_queue
            print('add cti')
            new_cti = Cti(diagram, universe_dict, frame_counter)
            cti_queue.append(new_cti)

            while cti_queue:
                curr =  cti_queue[-1]
                #recursevily block the cex
                if not recblock(paramts, abstract_predicates_dict, abs_vars, curr, H_formula, hat_init):
                    # abstract coutnerexample
                        print('abstract cex')
                        cti_queue.reverse()
                        for i, c in enumerate(cti_queue):
                            banner('diagram at step %d' %(i))
                            concrete_d = substitute_diagram(c, abstract_predicates_dict, abs_vars)
                            print(str(concrete_d))

                        return VerificationResult(UNSAFE, cti_queue)
                    # refine predicates or exit with a concrete cex                    

            else:
                last_frame_formula = And(*[And(*frame_sequence[-1]), H_formula, Not(hat_prop)])
                s.reset()
                s.from_string(msat_to_smtlib2_ext(env, last_frame_formula, 'UFLIA', True))        
    
        frame_counter += 1
        print('Add new counter %d' %frame_counter)
        frame_sequence.append([])
        s.reset()
  
        # #propagation phase
        # maybe do this in a function..
        print('propagation phase...')
        for i in range(1, frame_counter):
            for d in frame_sequence[i]:
                if d not in frame_sequence[i+1]:
                    f = get_abs_relative_inductive_check(paramts, abs_vars, frame_sequence[i+1], \
                        Not(d), abstract_predicates_dict, H_formula, hat_init)
                    s1 = Solver()
                    s1.from_string(msat_to_smtlib2_ext(env, f, 'UFLIA', True))
                    if s1.check() == z3.unsat:
                        frame_sequence[i+1].append(d)
                    s.reset()
                
            if set(frame_sequence[i]) == set(frame_sequence[i+1]):
                print('Proved! Inductive invariant:')
                for x in frame_sequence[i+1]:
                    print(x)
                return VerificationResult(SAFE, frame_sequence[i])
