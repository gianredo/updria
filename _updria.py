#!/usr/bin/env python3
# UPDRIA PROTOTYPE
import argparse
import functools
import itertools
import random
import sys
from collections import namedtuple
from contextlib import contextmanager
from typing import *
from xml.dom import NotSupportedErr
import time

from mathsat import *
from z3 import *

#-----------------------------------------------------------------------------
# user-configurable options
#-----------------------------------------------------------------------------

class Options:
    def __init__(self):
        self.vmt_property = 0
        self.input_language = 'vmt'
        self.use_diagram_constraint = True
        self.abstract_index = False
        self.transition_num = False

    def __str__(self):
        return "\n".join(sorted([
            "vmt_property = %s" % self.vmt_property,
            "input_language = %s " % self.input_language,
            "use_diagram_constraint = %s " %self.use_diagram_constraint,
            "abstract_index = %s " %self.abstract_index,
            "transition_num = %s " %self.transition_num,
            ]))
# end of class Options

def getopts():
    p = argparse.ArgumentParser()
    def add_flag(n):
        dest = n.replace('-', '_')
        p.add_argument('--%s' % n, action='store_true', dest=dest)
        p.add_argument('--no-%s' % n, action='store_false', dest=dest)
    add_flag('use-diagram-constraint')
    p.add_argument('--vmt-property', type=int, default=0)
    p.add_argument('infile', nargs='?')
    p.add_argument('-l', '--input-language',
                   choices=['vmt', 'mcmt'])
    add_flag('abstract-index')
    add_flag('transition-num')
    opts = Options()
    p.parse_args(namespace=opts)
    return opts


#-----------------------------------------------------------------------------
# Statistics
#-----------------------------------------------------------------------------


class Statistics:
    def __init__(self):
        self.verification_time = 0.0
        self.z3_time = 0.0
        self.generalization_time = 0.0
        self.rec_block_time = 0.0
        self.propagate_time = 0.0
        self.refinement_time = 0.0
        self.minimizing_model_time = 0.0
        self.num_z3_calls = 0
        self.added_diagram = {0 : 1}
        self.greatest_diagram_len = {0 : 0}
        self.num_initial_preds = 0
        self.num_final_preds = 0
        self.num_ref_iterations = 0
        self.max_concrete_size = 0
        self.num_predicates_inductive = 0


    def __str__(self):
        out = [
         "verification time: %.3f" % self.verification_time,
         "z3 check time: %.3f" % self.z3_time,
         "generalization time: %.3f" %self.generalization_time,
         "recursive block time: %.3f" % self.rec_block_time,
         "propagation time: %.3f" % self.propagate_time,
         "refinement time: %.3f" % self.refinement_time,
         "minimization models time: %.3f" % self.minimizing_model_time,
         "num z3 calls: %d" % self.num_z3_calls,
         "number of added diagrams per frame: %s" % self.added_diagram,
         "greatest number of literals in a diagram per frame: %s" %self.greatest_diagram_len,
         "number of refinement steps: %d" % self.num_ref_iterations,
         "number of initial predicates: %d" % self.num_initial_preds,
         "number of final predicates: %d" % self.num_final_preds,
         "max concrete size: %s" % self.max_concrete_size,
         "number of predicates used in the inductive invariant: %d" % self.num_predicates_inductive
            ]
        return "\n".join(out)

_stats = Statistics()

@contextmanager
def Timer(which):
    start = time.time()
    yield
    end = time.time()
    t = end - start
    setattr(_stats, which, getattr(_stats, which) + t)

def measure(which, func, *args, **kwds):
    with Timer(which):
        return func(*args, **kwds)


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


def split_quantifier_map(t):

    qvar_map = {}

    def visit(env, t, pre):
        nonlocal qvar_map
        if pre:
            if msat_term_is_forall(env, t):
                v = msat_term_get_arg(t, 0)
                qvar_map[v] = FORALL
            elif msat_term_is_exists(env, t):
                v = msat_term_get_arg(t, 0)
                qvar_map[v] = EXISTS

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, t, visit)
    return qvar_map


def nextvar(v):
    return Var(name(v) + ".next", type_(v))

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
    found_vars = set()
    not_free_vars = set()

    def get_vars(e: msat_env, term : msat_term, pre : bool):
        nonlocal found_vars
        if not pre:
            if is_qvar(term):
                if term not in set(found_vars):
                    found_vars.add(term)

        return MSAT_VISIT_PROCESS


    def remove_quantified(e, t, pre):
        nonlocal not_free_vars, found_vars
        if not pre:
            if msat_term_is_forall(e, t) or msat_term_is_exists(e, t):
                for var in found_vars:
                    if name(var) == name(msat_term_get_arg(t, 0)):
                        not_free_vars.add(var)

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, formula, get_vars)
    msat_visit_term(env, formula, remove_quantified)
    return sorted(found_vars.difference(not_free_vars), key=msat_term_id)


def number_quantifiers(env : msat_env, formula : msat_term) -> int:
    num = 0
    ## count number of quanfitified variables in formula
    def count(env: msat_env, term : msat_term, pre):
        nonlocal num
        if pre:
            if msat_term_is_forall(env, term) or msat_term_is_exists(env, term):
                num += 1
        return MSAT_VISIT_PROCESS

    msat_visit_term(env, formula, count)
    return num


def renaming(env : msat_env, formula : msat_term, counter : int) -> msat_term:

    #perform necessary renaming to change all the names of quantified variables
    #recursive definition, probabily not the best

    # if formula is A * B,
    #return *(renaming(env, A, counter), renaming(env, B, counter + nq(A)))

    #if formula is neg(A)
    #return not(renaming(env, A, counter))

    #if formula is exists x. phi(x)
    #return exists fresh(x, counter). renaming(env, phi(x -> x,coutner), coutner + 1)

    #if formula is forall x. phi(x)
    #return forall fresh(x, counter). renaming(env, phi(x -> x,coutner), coutner + 1)

    # if formula is atomic
    #return formla
    if msat_term_is_and(env, formula):
        A = msat_term_get_arg(formula, 0)
        B = msat_term_get_arg(formula, 1)
        return msat_make_and(env, renaming(env, A, counter), renaming(env, B, counter + number_quantifiers(env, A)))

    if msat_term_is_or(env, formula):
        A = msat_term_get_arg(formula, 0)
        B = msat_term_get_arg(formula, 1)
        return msat_make_or(env, renaming(env, A, counter), renaming(env, B, counter + number_quantifiers(env, A)))

    if msat_term_is_not(env, formula):
        A = msat_term_get_arg(formula, 0)
        return msat_make_not(env, renaming(env, A, counter))

    if msat_term_is_forall(env, formula):
        var = msat_term_get_arg(formula, 0)
        new_var = QVar(msat_type_repr(type_(var))+'_'+str(counter), msat_term_get_type(var))
        body = msat_term_get_arg(formula, 1)
        new_body = msat_apply_substitution(env, body, [var], [new_var])
        return msat_make_forall(env, new_var, renaming(env, new_body, counter + 1))

    if msat_term_is_exists(env, formula):
        var = msat_term_get_arg(formula, 0)
        new_var = QVar(msat_type_repr(type_(var))+'_'+str(counter), msat_term_get_type(var))
        body = msat_term_get_arg(formula, 1)
        new_body = msat_apply_substitution(env, body, [var], [new_var])
        return msat_make_exists(env, new_var, renaming(env, new_body, counter + 1))

    else:
        return formula

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

Cti = namedtuple('Cti', ['diagram', 'universe_dict', 'frame_number', 'transition_num'])
## Global parameters of UPDRIA

#frame sequence is a list of list of diagrams
frame_sequence = []

#cti_queue is a list of cti
cti_queue = []

#frame_coutner is the length of frame_sequence
frame_coutner = 0


def get_index_signature(paramts : ParametricTransitionSystem):
    '''
    from the formulae defining the system, this function gets
    - the set of constants of index sorts
    - the set of functions among index vars (domain and codomain are all indexes)
    - predicates among index vars (boolean functions and domain all indexes)
    (these are not abstracted in the IA)
    '''

    all_formulae = [paramts.init, paramts.prop] + paramts.trans_rules + paramts.axioms
    all_constants = set()
    all_preds = set()
    all_functions = set()
    nextvars = set(t[1] for t in paramts.statevars).union(t[1] for t in paramts.frozenvars)
    def get_symbols(env, term, pre):
        nonlocal all_constants
        if msat_term_is_constant(env, term) and msat_type_repr(type_(term)) in paramts.sorts:
            if term not in nextvars:
                all_constants.add(term)   
        
        if msat_term_is_uf(env, term):
            d = msat_term_get_decl(term)
            if msat_decl_id(d) not in _param_read_funs:
                rettp = msat_decl_get_return_type(d)
                if msat_type_equals(rettp, BOOL):
                    all_preds.add(d)
                elif msat_type_repr(rettp) in paramts.sorts:
                    no_theory_flag = True
                    ar = msat_decl_get_arity(d)
                    for i in range(ar):
                        argtp = msat_decl_get_arg_type(d, i)
                        if msat_type_repr(argtp) not in paramts.sorts:
                            no_theory_flag = False
                            break
                    if no_theory_flag:
                        all_functions.add(d)
        return MSAT_VISIT_PROCESS  
    
    for formula in all_formulae:
        msat_visit_term(env, formula, get_symbols)   
    
    all_constants = sorted(all_constants, key=msat_term_id)
    # for x in all_constants:
    #     print(x)
    all_functions = sorted(all_functions, key=msat_decl_id)
    # for x in all_functions:
    #     print(msat_decl_get_name(x))
    all_preds = sorted(all_preds, key=msat_decl_id)
    # for x in all_preds:
    #     print(msat_decl_get_name(x))
    return all_constants, all_functions, all_preds


def find_initial_predicates(opts, sorts, formula):
    '''
    this function mines predicates from the initial formula and the proposition
    equalities of index sorts, predicates of index sorts are ignored
    also booleans

    '''
    predicates = set()

    def find_predicates(env, t, pre):
        nonlocal predicates
        if not pre:
            if msat_term_is_atom(env, t) and not msat_term_is_quantifier(env, t):
                #equalities among index terms
                if msat_term_is_equal(env, t) and msat_type_repr(type_(arg(t, 0))) in sorts:
                    pass

                elif msat_term_is_uf(env, t):
                    d = msat_term_get_decl(t)
                    if msat_decl_id(d) in _param_read_funs:
                        if  not opts.abstract_index:
                        #in this case t is of the form (param name index1 ... indexn)
                        #and param is a boolean (otherwise t would not be an atom), thus we can skip
                            pass
                        else:
                            predicates.add(t)               
                    
                    else:
                        # lets see if the predicate is all among index vars
                        theory_sort_flag = False
                        for i in range(msat_decl_get_arity(d)):
                            if msat_type_repr(msat_decl_get_arg_type(d, i)) not in sorts:
                                theory_sort_flag = True
                                
                        if theory_sort_flag or opts.abstract_index:
                            predicates.add(t)
                

                # boolean constants
                elif msat_term_is_constant(env, t):
                    pass
                
                else:
                    predicates.add(t)

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, formula, find_predicates)
    #sort the predicates with msat_term_id

    return sorted(predicates, key=msat_term_id)




def find_predicates(sorts, formula):
    '''
    this function mines predicates from the initial formula and the proposition
    equalities of index sorts, predicates of index sorts are ignored
    also booleans

    '''
    predicates = set()

    def find_predicates(env, t, pre):
        nonlocal predicates
        if not pre:
            if msat_term_is_atom(env, t) and not msat_term_is_quantifier(env, t):
                #equalities among index terms
                if msat_term_is_equal(env, t) and msat_type_repr(type_(arg(t, 0))) in sorts:
                    pass                
                # boolean constants
                elif msat_term_is_constant(env, t):
                    pass
                else:
                    predicates.add(t)

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, formula, find_predicates)
    #sort the predicates with msat_term_id

    return sorted(predicates, key=msat_term_id)



def remove_duplicates(predicates, varlist = None):
    '''
    we rewrite index variables in predicates with qvars named '<type>_<position>' where position
    is given by the msat_term_id ordering
    '''
    norm_predicates = set()
    norm_dict = {}
    for p in predicates:
        if varlist:
            freevars = []
            def get_concrete_vars(e: msat_env, term : msat_term, pre : bool):
                nonlocal freevars, varlist
                if not pre:
                    from _grounder import is_prophecy
                    if is_prophecy(term) and term in varlist[msat_type_repr(type_(term))]:
                        freevars.append(term)
                return MSAT_VISIT_PROCESS
            msat_visit_term(env, p, get_concrete_vars)
            freevars = sorted(freevars, key=msat_term_id)
        else:
            freevars = get_free_vars(p)
        if freevars:
            norm_p = p
            for i, x in enumerate(freevars):
                norm_p  = msat_apply_substitution(env, norm_p, [x], [QVar('%s_%d' % (msat_type_repr(type_(x)), i), type_(x))])
            if norm_p not in norm_predicates:
                norm_predicates.add(norm_p)
            norm_dict[p] = norm_p
        else:
            norm_predicates.add(p)

    norm_dict = dict(sorted(norm_dict.items(), key= lambda x : msat_term_id(x[1])))

    return sorted(norm_predicates, key=msat_term_id), norm_dict


def get_abstract_predicates(predicates, varlist = None):
    '''
    this function takes a set of predicates
    first, it normalize them (remove_duplicates)
    then, defines new set of boolean predicates x_{unique_id}
    it returns:
        - a dictionary {old_predicate : new_predicate}
        - the set of abstract_variables (x_{unique_id} as boolean function declaration)
        - a dictionary for normalized predicates  which will be used for the substitution
    '''
    predicates, norm_dict = remove_duplicates(predicates, varlist)
    new_preds = {p : FALSE() for p in predicates}
    abstract_vars = set()
    for p in predicates:
        vars = get_free_vars(p)
        if vars:
            #define a fresh boolean symbol
            #the ariety is the number of free vars in p
            tp = msat_get_function_type(env, [type_(x) for x in vars], BOOL)
            f = msat_declare_function(env, 'x_%d' % (msat_term_id(p)), tp)
            abstract_vars.add(f)
            new_preds[p] = msat_make_uf(env, f, vars)
            #print(msat_last_error_message(env))
        else:
            f = Var('x_%s' % (msat_term_id(p)), BOOL)
            abstract_vars.add(msat_term_get_decl(f))
            new_preds[p] = f

    new_preds = dict(sorted(new_preds.items(), key= lambda x : msat_term_id(x[1])))
    return new_preds, sorted(abstract_vars, key=msat_decl_id), norm_dict


def substitute_index_predicates(formula, abstract_predicates_dict, norm_dict):
    '''
    we substitute the predicates in the initial formula and in the property
    first, we substitute predicates without idx variables
    then, we look at the norm_dictionary to discover the original variables
    and do the substitution with a proper renaming
    (not sure if it is the best way!!!)
    '''
    hat_formula = formula
    for p in abstract_predicates_dict:
        idx_vars = get_free_vars(p)
        if not idx_vars:
            hat_formula = substitute(hat_formula, [p], [abstract_predicates_dict[p]])
        else:
            for old_p in norm_dict:
                for p in abstract_predicates_dict:
                    if norm_dict[old_p] == p:
                        #look for a unifier i.e. a substitution sigma such that
                        # p [sigma] = old_p
                        idx_vars = get_free_vars(p)
                        for subs in itertools.product(get_free_vars(old_p), repeat=len(idx_vars)):
                            if all([msat_type_equals(type_(x), type_(y)) for x, y in zip(idx_vars, subs)]):
                                if substitute(p, idx_vars, subs) == old_p:
                                    hat_formula = substitute(hat_formula, [old_p], \
                                    [substitute(abstract_predicates_dict[p], idx_vars, subs)])
                                    #print(msat_last_error_message(env))
                                    break

    return hat_formula


def get_h_formula(abstract_predicates):
    '''
    h formula to connect abstract predicates with old ones
    '''
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

            if is_qvar(term):
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
                    # To obtain the same name as the mathsat predicate
                    z3_fun = z3.Function(name(term).replace('|', '\|'), \
                        [convert_type(env, type_(arg(term, i))) for i in range(ar)] \
                             + [convert_type(env, msat_decl_get_return_type(d))])
                    z3_atom = z3_fun([cache[arg(term, i)] for i in range(ar)])
                    return MSAT_VISIT_ABORT
            
            elif msat_term_is_equal(env, term):
                z3_atom = cache[arg(term, 0)] == cache[arg(term, 1)]
            
            else:
                raise NotSupportedErr('not supported translation for %s' %(smt2(term)))

        return MSAT_VISIT_PROCESS

    msat_visit_term(env, p, create_z3_predicate)

    return z3_atom


def extract_diagram(opts, statevars, index_signature, abs_predicates, model, sort_names):
    '''
    takes a z3 model and return a msat formula
    which is the diagram of the model
    in this function I use an hack for z3 evaluation which is not great:
    if m is a z3 model and t is a term/predicates, to see whether the model evaluate t to something, 
    I test if str(m.eval(t)) == t - if the latter is true, t is not evaluated

    another possibilty is add the flag model_completion = True, which evaluate everything to some 
    default value. however, this would produce unnecessary large formulas!

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

    #get the index signature
    index_constants, index_functions, index_predicates = index_signature

    # start with constants
    eq_constraint = []
    # for each constant in the signature, for each v in the universe, 
    #  add c = v if it is true in the model, or c != v otherwise
    for c in index_constants:
        s = msat_type_repr(type_(c))
        z3_c = z3.Const(str(c), convert_type(env, type_(c)))
        for v in universes[s]:
            #check if the constant is in the model
            # hack... idk
            if str(model.eval(z3_c)) != str(z3_c):
                if bool(model.eval(z3_c == v)):
                    eq_constraint.append(Eq(c, QVar(str(v), mksort(s))))
                else:
                    eq_constraint.append(Not(Eq(c, QVar(str(v), mksort(s)))))

    eq_constraint = And(*eq_constraint)

    # compute the values of each predicate. 
    # we have both predicates in the index signature (original predicates)
    # and indexed predicates of the abstraction

    predicates_constraint = TRUE()
    # let's start with index predicates in the abstraction
    for p in abs_predicates:
        #replace free vars with constant variables (just needed to convert in z3 predicates)
        renaming_dict = {a : Var(smt2(a), type_(a)) for a in get_free_vars(p)}
        p = substitute(p, list(renaming_dict), list(renaming_dict.values()))
        z3_predicate = convert_predicate(env, p)
        z3_vars = [z3.Const(smt2(a), convert_type(env, type_(a))) for a in renaming_dict.values()]
        ar = arity(p)
        if ar == 0:
            #arity 0 so the predicate is a boolean constant
            try:
                if bool(model.eval(z3_predicate)):
                    predicates_constraint = And(predicates_constraint, p)
                else:
                    predicates_constraint = And(predicates_constraint, Not(p))
            except z3types.Z3Exception as Err:
                #the exception is to catch if we evalue predicate not in the model
                #not sure this is the proper way
                pass
        else:
            assert ar > 0
            #compute all possible substitution
            for vars in itertools.product(*[universes[msat_type_repr(type_(arg(p, i)))] for i in range(ar)]):
                ground = z3.substitute(z3_predicate, *zip(z3_vars, vars))
                msat_ground = substitute(p, list(renaming_dict.values()), [QVar(str(x), mksort(str(x.sort()))) for x in vars])
                try:
                    if bool(model.eval(ground)):
                        predicates_constraint = And(predicates_constraint, msat_ground)
                    else:
                        predicates_constraint = And(predicates_constraint, Not(msat_ground))

                except z3types.Z3Exception as Err:
                    pass
    
    #index predicates in the signature
    if not opts.abstract_index:
        for p in index_predicates:
            ar = msat_decl_get_arity(p)       
            assert ar > 0
            for vars in itertools.product(*[universes[msat_type_repr(msat_decl_get_arg_type(p, i))] for i in range(ar)]):    
                msat_vars = [Var(str(x), mksort(str(x.sort()))) for x in vars]
                msat_ground = msat_make_uf(env, p, msat_vars)
                ground = convert_predicate(env, msat_ground)
                z3_vars = [z3.Const(smt2(a), convert_type(env, type_(a))) for a in msat_vars]
                ground = z3.substitute(ground, *zip(z3_vars, vars))
                msat_ground = msat_make_uf(env, p, [QVar(str(x), mksort(str(x.sort()))) for x in vars])
                try:
                    if bool(model.eval(ground)):
                        predicates_constraint = And(predicates_constraint, msat_ground)
                    else:
                        predicates_constraint = And(predicates_constraint, Not(msat_ground))

                except z3types.Z3Exception as Err:
                    pass


        # should add constrains of the form f(i) = j for all possible permutation of i, j
        for x in index_functions:
            ar = msat_decl_get_arity(x)
            for vars in itertools.product(*[universes[msat_type_repr(msat_decl_get_arg_type(x, i))] \
                for i in range(ar)]):
                msat_vars = [Var(str(x), mksort(str(x.sort()))) for x in vars]
                rettp = msat_decl_get_return_type(x)
                for v in universes[msat_type_repr(rettp)]:
                    msat_ground = Eq(msat_make_uf(env, x, msat_vars), Var(str(v), mksort(str(v.sort()))))
                    ground = convert_predicate(env, msat_ground)
                    z3_vars = [z3.Const(smt2(a), convert_type(env, type_(a))) for a in msat_vars]
                    ground = z3.substitute(ground, *zip(z3_vars, vars))
                    msat_ground = Eq(msat_make_uf(env, x, [QVar(str(x), mksort(str(x.sort()))) \
                        for x in vars]), Var(str(v), mksort(str(v.sort()))))
                    try:
                        # terrible hack 
                        if str(model.eval(ground)) != str(ground):
                            if model.eval(ground):
                                predicates_constraint = And(predicates_constraint, msat_ground)
                            else:
                                predicates_constraint = And(predicates_constraint, Not(msat_ground))
                        else:
                            pass

                    except z3types.Z3Exception as Err:
                        pass

    statevars_constraint = TRUE()

    if not opts.abstract_index:
        #we compute differently the values of statevars of boolean element type
        #i.e. boolean constants in the signature or boolean functions
        for a, _ in statevars:
            if is_param(a) and msat_type_repr(type_(a)) == '[Bool]':
                
                
                if opts.input_language == 'mcmt':
                    index_tp = msat_get_simple_type(env, "index")
                    toint_decl = msat_declare_function(
                        env, "index2int", msat_get_function_type(env, [index_tp], INT))
                    def toint(t):
                        return msat_make_uf(env, toint_decl, [t])

                    z3_const = z3.Const('%s' %str(a), convert_type(env, type_(a)))
                    try:
                        # if the constant has an evaluation in the model, then we compute the constraint
                        # ugly way of comparing but idk
                        if str(model.eval(z3_const)) != str(z3_const):
                            d = _param_map[str(a)][1] 
                            ar = msat_decl_get_arity(d)
                            for vars in itertools.product(*[universes['index'] for i in range(1, ar)]):
                                msat_vars = [Var(str(x), mksort(str(x.sort()))) for x in vars]
                                msat_ground = ParamVal(a, [toint(x) for x in msat_vars])
                                ground = convert_predicate(env, msat_ground)
                                z3_vars = [z3.Const(smt2(a), convert_type(env, type_(a))) for a in msat_vars]
                                ground = z3.substitute(ground, *zip(z3_vars, vars))
                                msat_ground = ParamVal(a, [toint(QVar(str(x), mksort(str(x.sort())))) for x in vars])
                                if bool(model.eval(ground)):
                                    statevars_constraint = And(statevars_constraint, msat_ground)
                                else:
                                    statevars_constraint = And(statevars_constraint, Not(msat_ground))
                    except z3types.Z3Exception as Err:
                        pass 

                
                else:  
                    #boolean functions
                    #check if the evaluation is in the model
                    #check the evaluation of the 'name' of the function
                    z3_const = z3.Const('%s' %str(a), convert_type(env, type_(a)))
                    try:
                        # if the constant has an evaluation in the model, then we compute the constraint
                        # ugly way of comparing but idk
                        if str(model.eval(z3_const)) != str(z3_const):
                            d = _param_map[str(a)][1] 
                            ar = msat_decl_get_arity(d)
                            for vars in itertools.product(*[universes[msat_type_repr(msat_decl_get_arg_type(d, i))] for i in range(1, ar)]):
                                msat_vars = [Var(str(x), mksort(str(x.sort()))) for x in vars]
                                msat_ground = ParamVal(a, msat_vars)
                                ground = convert_predicate(env, msat_ground)
                                z3_vars = [z3.Const(smt2(a), convert_type(env, type_(a))) for a in msat_vars]
                                ground = z3.substitute(ground, *zip(z3_vars, vars))
                                msat_ground = ParamVal(a, [QVar(str(x), mksort(str(x.sort()))) for x in vars])
                                if bool(model.eval(ground)):
                                    statevars_constraint = And(statevars_constraint, msat_ground)
                                else:
                                    statevars_constraint = And(statevars_constraint, Not(msat_ground))
                    except z3types.Z3Exception as Err:
                        pass

            #statevars with index type 
            elif is_param(a) and msat_type_repr(msat_decl_get_return_type(_param_map[name(a)][1])) in sort_names:
                        d = _param_map[str(a)][1] 
                        ar = msat_decl_get_arity(d)
                        for vars in itertools.product(*[universes[msat_type_repr(msat_decl_get_arg_type(d, i))] for i in range(1, ar)]):
                            msat_vars = [Var(str(x), mksort(str(x.sort()))) for x in vars]
                            msat_qvars = [QVar(str(x), mksort(str(x.sort()))) for x in vars]
                            rettp = msat_decl_get_return_type(d)
                            for v in universes[msat_type_repr(rettp)]:
                                msat_ground = Eq(ParamVal(a, msat_vars), Var(str(v), mksort(str(v.sort()))))
                                ground = convert_predicate(env, msat_ground)
                                z3_vars = [z3.Const(smt2(a), convert_type(env, type_(a))) for a in msat_vars]
                                ground = z3.substitute(ground, *zip(z3_vars, vars))
                                msat_ground = Eq(ParamVal(a, msat_qvars), Var(str(v), mksort(str(v.sort()))))
                                try:
                                    # terrible hack 
                                    if str(model.eval(ground)) != str(ground):
                                        if model.eval(ground):
                                            predicates_constraint = And(predicates_constraint, msat_ground)
                                        else:
                                            predicates_constraint = And(predicates_constraint, Not(msat_ground))
                                    else:
                                        pass

                                except z3types.Z3Exception as Err:
                                    pass

    for a, _ in statevars:
    # variable can be a boolean constant (not a function)        
        if msat_type_equals(type_(a), BOOL):
            z3_predicate = convert_predicate(env, a)
            try:
                if bool(model.eval(z3_predicate)):
                    statevars_constraint = And(statevars_constraint, a)
                else:
                    statevars_constraint = And(statevars_constraint, Not(a))

            except z3types.Z3Exception as Err:
                pass


    #make the diagram
    diagram = And(eq_constraint, And(*[diff_constraint[s] for s in diff_constraint], \
        predicates_constraint, statevars_constraint))
    # compute existential clousure
    for s in sort_names:
        for v in ex_vars_dict[s]:
            diagram = Exists(v, diagram)
    
    return diagram, universes


def get_next_abstract_formula(formula, abs_vars):
    '''
    function to make substitution 
    from a formula using (x i1 ... in) to (x.next i1 ... in)
    
    '''
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


def get_abs_relative_inductive_check(opts, paramts, abs_vars, frame, diagram, \
    predicates_dict, H_formula, abs_init, initial_constr = False):

    '''
    this function gets the relative inductivness check with IA
    initial constraint is used for generalization of diagrams 
    
    '''

    #we need H_formula for next variables
    #we substitute every (p i1 ... in) with (p.next i1 ... in)
    H_formula_next = get_next_abstract_formula(H_formula, abs_vars)
    H_formula_next = substitute(H_formula_next, [s[0] for s in paramts.statevars], [s[1] for s in paramts.statevars])

    # same for initial formula of next (used in the generalization)
    next_abs_init = get_next_abstract_formula(abs_init, abs_vars)
    next_abs_init = substitute(next_abs_init, [s[0] for s in paramts.statevars], [s[1] for s in paramts.statevars])

    def barvar(v):
        return Var(name(v) + ".bar", type_(v))

    #we need a dublicate (bar version) of the non boolean state vars
    non_bool_vars = [x for x in paramts.statevars if (msat_type_repr(type_(x[0])) != '[Bool]' \
        and not msat_type_equals(type_(x[0]), BOOL) and msat_type_repr(type_(x[0])) not in paramts.sorts) ]
    bar_statevars = [ (barvar(a), barvar(b)) for a, b in non_bool_vars]
    
    predicates_bar_c = [substitute(p, [c[0] for c in non_bool_vars], [bc[0] for bc in bar_statevars]) \
         for p in predicates_dict]

    predicates_next = [substitute(p, [c[0] for c in non_bool_vars], [c[1] for c in non_bool_vars]) \
         for p in predicates_dict]

    predicates_bar_n = [substitute(p, [c[0] for c in non_bool_vars], [bc[1] for bc in bar_statevars]) \
         for p in predicates_dict]

    EQ_formula_1 = And(*[Iff(p[0], p[1]) for p in zip(predicates_dict, predicates_bar_c)])
    for var in get_free_vars(EQ_formula_1):
        EQ_formula_1 = Forall(var, EQ_formula_1)

    EQ_formula_2 = And(*[Iff(p[0], p[1]) for p in zip(predicates_next, predicates_bar_n)])
    for var in get_free_vars(EQ_formula_2):
        EQ_formula_2 = Forall(var, EQ_formula_2)

    # abstract transition formula
    t_bar = [substitute(t, [c[0] for c in non_bool_vars], [c[0] for c in bar_statevars]) for t in paramts.trans_rules]
    t_bar = [substitute(t, [c[1] for c in non_bool_vars], [c[1] for c in bar_statevars]) for t in t_bar]
    
    abs_trans = FALSE()
    if opts.transition_num:
        rule_var = Var("rule", INT)
        for i, rule in enumerate(t_bar):
            abs_trans = Or(abs_trans, And(rule, Eq(rule_var, Int(i))))

        f = And(GE(rule_var, Int(0)), LE(rule_var, Int(len(paramts.trans_rules))))
        paramts.axioms.append(f)
    else:
        abs_trans = Or(*t_bar)

    #next diagram
    next_diagram = get_next_abstract_formula(diagram, abs_vars)
    next_diagram = substitute(next_diagram, [c[0] for c in paramts.statevars], [c[1] for c in paramts.statevars])
    # print(next_diagram)
    # print(H_formula_next)
    # print(And(*frame))
    # print(diagram)
    # print(abs_trans)
    # print(next_diagram)
    # print(EQ_formula_1)
    # print(EQ_formula_2)
    axioms = And(*paramts.axioms)
    axioms = substitute(axioms, [c[0] for c in non_bool_vars], [c[0] for c in bar_statevars])        

    formula = And(And(*frame), Not(diagram), axioms, abs_trans, H_formula, H_formula_next, EQ_formula_1, EQ_formula_2)
    if initial_constr:
        formula = Or(formula, next_abs_init)

    formula = And(formula, next_diagram)
    return formula


def get_size_constraint(sort, size):
    vars = [z3.Const('%s_%d' %(sort, i), DeclareSort(sort)) for i in range(size)]
    qvar = z3.Const('VAR_%s' %sort, DeclareSort(sort))
    formula = z3.ForAll([qvar], z3.Or(*[qvar == v for v in vars]))
    return formula


def minimize_model(solver, sorts):
    for s in sorts:
        for size in itertools.count(1):
            f = get_size_constraint(s, size)
            solver.push()
            solver.add(f)
            res = solver.check()
            if res == z3.sat:
                print('minimal model of size %d for sort %s' %(size, s))
                break
            else:
                solver.pop()



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
            core = sorted(core, key=get_id)
            # order core in some method
            core = [c for c in core if get_id(c) not in ids]
    return mus


def minimize_core(s):
    core = s.unsat_core()
    core = sorted(core, key=get_id)

    # order core in some method
    core = minimize_core_aux2(s, core)
    core = sorted(core, key=get_id)
    # order here

#    print "minimize_core: core = {}".format(core)
    return core


def generalize_diagram(opts, paramts, abs_vars, frame, diagram, predicates_dict, H_formula, hat_init):
    '''
    this function generalize the diagram
    returns a set of literals with possibly existentially quantified variables
    '''
    kind, qf, body = split_quantifier(diagram)
    if kind:
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

    fmlas = sorted([a for a in collect(env, MSAT_TAG_AND, body)], key=msat_term_id)
    alits = [Var("__c%s" % n, BOOL) for n,c in enumerate(fmlas)]
    z3_alits = [z3.Const("__c%s" % n, z3.BoolSort()) for n,c in enumerate(fmlas)]
    cc = [Or(Not(a),c) for a,c in zip(alits,fmlas)]

    idx = frame_sequence.index(frame)
    try:
        _stats.greatest_diagram_len[idx] = max(_stats.greatest_diagram_len[idx], len(cc))
    except KeyError as err:
        _stats.greatest_diagram_len[idx] = len(cc)

    n_diagram = And(*cc)
    for v in qf:
        n_diagram = Exists(v, n_diagram)

    s2 = Solver()
    abs_rel_formula = get_abs_relative_inductive_check(opts, paramts, abs_vars, frame, n_diagram,\
         predicates_dict, H_formula, hat_init, True)

    s2.from_string(msat_to_smtlib2_ext(env, abs_rel_formula, 'ALL', True))
    is_sat = s2.check(z3_alits)
    try:
        assert is_sat == z3.unsat
    except AssertionError as Err:
        print('error in unsat core')
        raise Err

    core = minimize_core(s2)

    s2.reset()
    core_ids = [get_id(a) for a in core]
    res = sorted([c for a,c in zip(z3_alits,fmlas) if get_id(a) in core_ids], key=msat_term_id)

    g_diagram = And(*res)
    qf = get_free_vars(g_diagram)
    for v in qf:
        g_diagram = Exists(v, g_diagram)

    g_diagram = renaming(env, g_diagram, 0)

    # def ok(g_diagram, diagram):
    #     s2 = z3.Solver()
    #     f1 = Implies(Not(g_diagram), Not(diagram))
    #     f2 = Implies(hat_init, Not(g_diagram))
    #     print(f2)
    #     s2.from_string(msat_to_smtlib2_ext(env, Not(f1), 'ALL', True))
    #     if s2.check() == z3.sat:
    #         print('not a generalization')
    #         return False
    #     s2.reset()
    #     s2.from_string(msat_to_smtlib2_ext(env, Not(f2), 'ALL', True))
    #     if s2.check() == z3.sat:
    #         print('falsified initial')
    #         return False
    #     s2.reset()
    #     return True
    # assert ok(g_diagram, diagram)

    # s2.reset()
    # abs_rel_formula = get_abs_relative_inductive_check(paramts, abs_vars, frame, g_diagram,\
    #      predicates_dict, e, hat_init, True)
    # s2.from_string(msat_to_smtlib2_ext(env, abs_rel_formula, 'UFLIA', True))
    # is_sat = s2.check(z3_alits)
    # assert is_sat == z3.unsat


    return g_diagram


def recblock(opts, paramts, index_constants, predicates_dict, abs_vars, cti : Cti, H_formula, hat_init):
    if cti.frame_number == 0:
        print('CEX! Violation of the initial formula')
        return False

    else:
        #check if the cti is reachable from the last frame
        print('trying to block cex at frame %d' %cti.frame_number)

        # print('trying to block diagram %s' %(substitute_diagram(cti.diagram, predicates_dict, abs_vars)))
        abs_rel_formula = get_abs_relative_inductive_check(opts, paramts, abs_vars,\
             frame_sequence[cti.frame_number-1],\
             cti.diagram, predicates_dict, H_formula, hat_init)

        s = Solver()
        s.from_string(msat_to_smtlib2_ext(env, abs_rel_formula, 'ALL', True))

        if opts.transition_num:
            l = len(paramts.trans_rules)
            for i in range(l):
                s.push()
                s.add(z3.Const('rule', IntSort()) == i)
                _stats.num_z3_calls +=1
                res = measure('z3_time', s.check)
                if res == z3.unsat:
                    s.pop()
                    continue
                elif res == z3.sat:
                    with Timer('minimizing_model_time'):
                        minimize_model(s, paramts.sorts)
                    model = s.model()
                    #print(model)
                    n_diagram, universe_dict = extract_diagram(opts, paramts.statevars, index_constants, \
                        predicates_dict.values(), model, paramts.sorts)
                    s.reset()
                    print('failed...')
                    cti_queue.append(Cti(n_diagram, universe_dict, cti.frame_number-1, i))
                    return True

            try:
                _stats.added_diagram[frame_counter] += 1
            except KeyError as err:
                _stats.added_diagram[frame_counter] = 1
            print('blocked')
            cti_queue.remove(cti)
            # generalize diagram with unsat cores
            print('generalizing diagram...')
            gen_diagram = measure('generalization_time', generalize_diagram, opts, paramts, abs_vars, \
                frame_sequence[cti.frame_number-1], cti.diagram, predicates_dict, H_formula, hat_init)
            # add diagram to all frames from 1 to frame_number
            for i in range(1, cti.frame_number+1):
                if Not(gen_diagram) not in set(frame_sequence[i]):
                    frame_sequence[i].append(Not(gen_diagram))
            s.reset()

            return True 



        else:    
            _stats.num_z3_calls +=1
            res = measure('z3_time', s.check)
            if res == z3.unsat:
                try:
                    _stats.added_diagram[frame_counter] += 1
                except KeyError as err:
                    _stats.added_diagram[frame_counter] = 1
                print('blocked')
                cti_queue.remove(cti)
                # generalize diagram with unsat cores
                print('generalizing diagram...')
                gen_diagram = measure('generalization_time', generalize_diagram, opts, paramts, abs_vars, \
                    frame_sequence[cti.frame_number-1], cti.diagram, predicates_dict, H_formula, hat_init)
                # add diagram to all frames from 1 to frame_number
                for i in range(1, cti.frame_number + 1):
                    if Not(gen_diagram) not in set(frame_sequence[i]):
                        frame_sequence[i].append(Not(gen_diagram))
                s.reset()
                return True

            elif res == z3.sat:
                with Timer('minimizing_model_time'):
                    minimize_model(s, paramts.sorts)
                model = s.model()
                #print(model)
                n_diagram, universe_dict = extract_diagram(opts, paramts.statevars, index_constants, \
                    predicates_dict.values(), model, paramts.sorts)
                s.reset()
                print('failed...')
                cti_queue.append(Cti(n_diagram, universe_dict, cti.frame_number-1, None))
                return True

            else:
                assert str(s.check()) == 'unknown'
                s.reset()
                raise NotImplementedError


def substitute_diagram(diagram, predicates_dict, abs_vars):

    kind, qvars, body = split_quantifier(diagram)
    #assert kind == EXISTS

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


def print_cex(cex):
    '''
    this function should print out the counterexample
    in a finite instance of the appropriate sorts

    '''
    pass


def updria(opts, paramts : ParametricTransitionSystem):
    global frame_sequence, cti_queue, frame_counter
    z3.set_param('smt.random_seed', 42)
    predicates = find_initial_predicates(opts, paramts.sorts, paramts.init)
    predicates += find_initial_predicates(opts, paramts.sorts, paramts.prop)
    abstract_predicates_dict, abs_vars, norm_dict  = get_abstract_predicates(predicates)
    _stats.num_initial_preds = len([x for x in abstract_predicates_dict])
    print('There are %d initial predicates' %_stats.num_initial_preds)

    # for x in abstract_predicates_dict:
    #     print(x)
    #     print(abstract_predicates_dict[x])

    #compute abstraction of initial formula and property
    hat_init = substitute_index_predicates(paramts.init, abstract_predicates_dict, norm_dict)
    hat_prop = substitute_index_predicates(paramts.prop, abstract_predicates_dict, norm_dict)
    # print(hat_init)
    # print(hat_prop)
    H_formula = get_h_formula(abstract_predicates_dict)
    #print(H_formula)

    index_signature = get_index_signature(paramts)
    # here we switch to z3. probabily using string is inefficent
    # we should use convertor (pystm?) from mathsat to z3
    # convertor is avaible only for predicates
    _stats.num_z3_calls += 1
    s = z3.Solver()
    s.from_string(msat_to_smtlib2_ext(env, And(hat_init, Not(hat_prop), H_formula), 'ALL', True))
    res = measure("z3_time", s.check)
    if res == z3.sat:
         print('unsafe! cex in the initial formula')
         return VerificationResult(UNSAFE, s.model())
    else:
        print('no initial cex! Entering main loop')
    s.reset()
    # initialize frame sequence
    frame_counter = 1
    #print(hat_prop)
    frame_sequence.append([hat_init])
    frame_sequence.append([])

  

    #main loop of updr
    while True:
        #there are no more cti's
        assert not cti_queue
        #compute intersection between last frame and bad
        last_frame_formula = And(*[And(*frame_sequence[-1]), H_formula, Not(hat_prop), And(*paramts.axioms)])
        #pass it to z3
        _stats.num_z3_calls += 1
        s = z3.Solver()
        s.from_string(msat_to_smtlib2_ext(env, last_frame_formula, 'ALL', True))
        print('Checking intersection between last frame and property...')
        res = measure('z3_time', s.check)
        while res == z3.sat:
            # take a model, extract a diagram
            print('found a cti')
            with Timer('minimizing_model_time'):
                minimize_model(s, paramts.sorts)
            model = s.model()
            #print(model)
            print('extracting diagram...')
            diagram, universe_dict = extract_diagram(opts, paramts.statevars, index_signature, \
                abstract_predicates_dict.values(), model, paramts.sorts)
            #print(diagram)
            s.reset()
            # Aadd a cti in the cti_queue
            print('add cti')
            new_cti = Cti(diagram, universe_dict, frame_counter, None)
            cti_queue.append(new_cti)

            while cti_queue:
                curr =  cti_queue[-1]
                #recursevily block the cex
                recblockres = measure('rec_block_time', recblock, opts, paramts, index_signature, abstract_predicates_dict,\
                     abs_vars, curr, H_formula, hat_init)
                if not recblockres:
                    # abstract coutnerexample
                        print('abstract cex')
                        cti_queue.reverse()
                        # for i, c in enumerate(cti_queue):
                        #     banner('diagram at step %d' %(i))
                        #     concrete_d = substitute_diagram(c.diagram, abstract_predicates_dict,\
                        #  abs_vars)
                        #     print(str(concrete_d))
                        s.reset()

                        import _grounder
                        spurious, cex, new_preds, concrete_varlist = measure('refinement_time', \
                            _grounder.concretize_cti_queue ,opts, cti_queue, paramts, \
                                abstract_predicates_dict, abs_vars)
                        if not spurious:
                            print('Concrete conterexample is found!')
                            return VerificationResult(UNSAFE, cex)
                        else:
                            _stats.num_ref_iterations += 1
                            print('starting refinemnt # %d' %_stats.num_ref_iterations)
                            new_preds_dict, n_abs_vars, _ = \
                                    get_abstract_predicates(new_preds, concrete_varlist)

                            # if set(new_preds_dict.values()) <= set(abstract_predicates_dict.values()):
                            #     print('no new predicates found!')
                            #     # fail
                            #     return VerificationResult(UNKNOWN, cti_queue)
                            abstract_predicates_dict.update(new_preds_dict)
                            abs_vars += n_abs_vars
                            H_formula = get_h_formula(abstract_predicates_dict)
                            cti_queue = []
                            # restart the loop with updated set of predicates

            # blocked cex, recompute last formula to see wheter there are more models
            last_frame_formula = And(*[And(*frame_sequence[-1]), H_formula, Not(hat_prop), And(*paramts.axioms)])
            s = Solver()
            _stats.num_z3_calls += 1
            s.from_string(msat_to_smtlib2_ext(env, last_frame_formula, 'ALL', True))
            res = measure('z3_time', s.check)

        frame_counter += 1
        print('Add new counter %d' %frame_counter)
        frame_sequence.append([])
        s.reset()

        # #propagation phase
        # maybe do this in a function..
        with Timer('propagate_time'):
            print('propagation phase...')
            for i in range(1, frame_counter):
                for d in frame_sequence[i]:
                    if d not in set(frame_sequence[i+1]):
                        f = get_abs_relative_inductive_check(opts, paramts, abs_vars, frame_sequence[i+1], \
                            Not(d), abstract_predicates_dict, H_formula, hat_init)
                        _stats.num_z3_calls += 1
                        s1 = Solver()
                        s1.from_string(msat_to_smtlib2_ext(env, f, 'ALL', True))
                        res = measure('z3_time', s1.check)
                        if res == z3.unsat:
                            frame_sequence[i+1].append(d)
                        # else:
                        #      print(substitute_diagram(d, abstract_predicates_dict, abs_vars))
                        s1.reset()

                if set(frame_sequence[i]) == set(frame_sequence[i+1]):
                    print('Proved! Inductive invariant:')
                    for x in frame_sequence[i]:
                        print(substitute_diagram(x, abstract_predicates_dict, abs_vars))

                    #let's count the predicates in the invariant
                    actual_predicates = set()
                    for f in frame_sequence[i]:
                        predicates = find_predicates(paramts.sorts, f)
                        norm_predicates, _ = remove_duplicates(predicates)
                        actual_predicates = actual_predicates.union(norm_predicates)
                    _stats.num_predicates_inductive = len(actual_predicates)

                    #count the number of total index predicates
                    _stats.num_final_preds = len(abstract_predicates_dict)
                    return VerificationResult(SAFE, frame_sequence[i])
