from _updria import *
from mathsat import *
from _updria import *
try:
    import ic3ia
    _has_ic3ia = True
except ImportError:
    _has_ic3ia = False

# p_var are used for the ground instances
p_var_cache = {}
all_p_vars = set()


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


def expand_quantifier(formula, varlist):
    qvar = arg(formula, 0)
    sort = msat_type_repr(type_(qvar))
    is_exists = msat_term_is_exists(env, formula)
    formula = arg(formula, 1)
    res = TRUE() if not is_exists else FALSE()
    to_subst = [qvar]
    values = [None]
    for v in varlist[sort]:
        values[0] = v
        t = substitute(formula, to_subst, values)
        if is_exists:
            res = Or(res, t)
        else:
            res = And(res, t)
    return res


def expand_quantifiers(formula, varlist):
    cache = {}
    propvars = set()
    def visit(e, t, pre):
        if not pre:
            targs = [cache[a] for a in args(t)]
            tt = term(t, targs)
            if msat_term_is_quantifier(e, tt):
                tt = expand_quantifier(tt, varlist)
            cache[t] = tt
        return MSAT_VISIT_PROCESS
    # from normalizer._normalizer import miniscoping
    # formula = miniscoping(env, formula)
    msat_visit_term(env, formula, visit)
    res = cache[formula]
    return res

               
def instantiate_u_vars(formula, vardict):
    kind, tosubst, body = split_quantifier(formula)
    if kind != FORALL:
        return formula

    varlist = []
    for s in vardict:
        varlist = vardict[s]
        tosubst_s = [x for x in tosubst if msat_type_repr(type_(x)) == s]
        assert len(varlist) >= len(tosubst_s)

        if len(varlist) > len(tosubst_s):
            varlist = varlist[:len(tosubst_s)]
            
        body = substitute(body, tosubst_s, varlist)
            
    return body


def cardinality_axioms(paramts, conc_size, only_cur=False):
    from _updria import _param_map, _param_read_funs, _params
    
    all_formulae = [paramts.init, paramts.prop] + ([] if only_cur else paramts.trans_rules + paramts.axioms)
    all_constants = set()
    all_functions = set()
    nextvars = set(t[1] for t in paramts.statevars)
    def get_symbols(env, term, pre):
        nonlocal all_constants, all_functions
        if msat_term_is_constant(env, term):
            if not only_cur or term not in nextvars:
                all_constants.add(term)   
        if msat_term_is_uf(env, term):
            all_functions.add(msat_term_get_decl(term))                
        return MSAT_VISIT_PROCESS  

    for formula in all_formulae:
        msat_visit_term(env, formula, get_symbols)   

    axioms = []

    for a in all_constants:
        if _param_map.get(name(a)):
            pass
        else:
            if msat_type_repr(type_(a)) in paramts.sorts and not msat_type_equals(type_(a), INT):
                j = QVar('j%s' %msat_type_repr(type_(a)), type_(a))
                axioms.append(Exists(j, Eq(j, a)))

    for f in all_functions:
        rettp = msat_decl_get_return_type(f)        
        if msat_decl_id(f) in _param_read_funs and msat_type_repr(rettp) in paramts.sorts \
            and not msat_type_equals(rettp, INT):
            arity = msat_decl_get_arity(f)
            tps = [msat_decl_get_arg_type(f, i) for i in range(1, arity)] 
            vars = [QVar('i%d%s' %(i, msat_type_repr(x)), x) for (i, x) in enumerate(tps)]
            ret = QVar('j%s' %(msat_type_repr(rettp)), rettp)

            for pname in _params:
                if only_cur and pname in nextvars:
                    continue
                tpparam = msat_term_get_type(pname)
                tp = msat_decl_get_arg_type(f, 0)
                if msat_type_equals(tp, tpparam):  
                    ax = Exists(ret, Eq(msat_make_uf(env, f, [pname] + vars), ret))
                    for var in vars:
                        ax = Forall(var, ax)

                    axioms.append(ax)

        elif msat_type_repr(rettp) in paramts.sorts and not msat_type_equals(rettp, INT):
            arity = msat_decl_get_arity(f)
            tps = [msat_decl_get_arg_type(f, i) for i in range(arity)] 
            vars = [QVar('i%d%s' %(i, msat_type_repr(x)), x) for (i, x) in enumerate(tps)]
            ret = QVar('j%s' %(msat_type_repr(rettp)), rettp)
            ax = Exists(ret, Eq(msat_make_uf(env, f, vars), ret))
            for var in vars:
                ax = Forall(var, ax)
            axioms.append(ax)
  

    return axioms


#functions for increasing cardinality
def get_succ(l : list):
    n = len(l)
    for i in range(n):
        b = l[:]
        b[i] += 1
        yield b


def get_next(root : list):
    global queue, visited

    for i in get_succ(root):
        if i not in queue:
            queue.append(i)
    if root not in visited:
        yield root
    #visit
    else:
        #min_l = lambda x : [i for i in x if sum(i) == sum(min(x))]
        def find_min(l):
            curr_min = -1
            idx = -1
            for i in l:
                m = max(i)
                if m < curr_min or curr_min == -1:
                    curr_min = m
                    idx = l.index(i)

            return l[idx]        

        queue.sort()
        new = find_min(queue)
        queue.remove(new)
        yield from get_next(new)


def increase_size(conc_size):

    curr_size = [conc_size[s] for s in conc_size]
    new_size = next(get_next(curr_size))
    return {s : new_size[i] for i,s in enumerate(conc_size)}


#functions for grounding


def get_concretization(opts, paramts, conc_size, lemmas):

    varlist = {s : [p_var(i, mksort(s)) for i in range(conc_size[s])]
               for s in paramts.sorts}

    init = expand_quantifiers(paramts.init, varlist)
    card_ax = cardinality_axioms(paramts, conc_size, True)
   
    for a in paramts.axioms + card_ax:
        axiom = expand_quantifiers(a, varlist)
        init = And(init, axiom)

    trans = FALSE()

    rule_var = Var("rule", INT)
    for i, rule in enumerate(paramts.trans_rules):
        t_rule = expand_quantifiers(rule, varlist)
        # if opts.show_witness and opts.cex_track_rules:
        #     t_rule = And(t_rule, Eq(rule_var, Int(i)))    
        trans = Or(trans, t_rule)


    card_ax = cardinality_axioms(paramts, conc_size, False)
    tosubst = [c for (c, _) in paramts.statevars]
    values = [n for (_, n) in paramts.statevars]
    for a in paramts.axioms + card_ax:
        axiom = expand_quantifiers(a, varlist)
        #next_axiom = msat_apply_substitution(env, axiom, tosubst, values)
        trans = And(trans, axiom)

    for (c, n) in paramts.frozenvars:
        trans = And(trans, Eq(c, n))
   
    prop = expand_quantifiers(paramts.prop, varlist)   
    
    for lemma in lemmas:
        prop = And(prop, instantiate_u_vars(lemma, varlist))

    statevars = paramts.statevars[:]
    for s in paramts.sorts:
        for p in varlist[s]:
            n = nextvar(p)
            statevars.append((p, n))
            trans = And(trans, Eq(p, n))

    for s in paramts.sorts:
        d = Alldiff(varlist[s])
        init = And(init, d)
        #trans = And(trans, d)

    return TransitionSystem(statevars, init, trans, TRUE(), prop)


def get_concrete_bmc_formula(opts, cti_queue, paramts, sizes): 
    '''
    takes the cti queue and a paramts
    return the bmc as list [step0, ..., stepn]
    '''

    ts = get_concretization(opts, paramts, sizes, [])
    concrete_vars = [a[0] for a in ts.statevars]
    varlist = {s : [p_var(i, mksort(s)) for i in range(sizes[s])]
               for s in paramts.sorts}
    vars_at_time = []

    for step, diagram in enumerate(cti_queue):
        if step == 0: 
            curr_vars = [Var(name(v) + ".step_%s" %step, type_(v)) for (v, _) in ts.statevars] 
            vars_at_time.append(curr_vars)
            init_step = ts.init
            if opts.use_diagram_constraint:
                init_step = And(init_step, expand_quantifiers(diagram, varlist))
            init_step = substitute(init_step, concrete_vars, curr_vars)
            unrolling = [init_step]
        else:
            trans = substitute(ts.trans, concrete_vars, curr_vars)
            next_vars = [Var(name(v) + ".step_%s" %step, type_(v)) for (v, _) in ts.statevars] 
            vars_at_time.append(next_vars)
            trans = substitute(trans, [a[1] for a in ts.statevars], next_vars)
            if opts.use_diagram_constraint:
                diagram = expand_quantifiers(diagram, varlist)
                diagram = substitute(diagram, concrete_vars, next_vars)
                trans = And(trans, diagram)
            elif len(unrolling) == len(cti_queue)-1:
                trans = And(trans, Not(substitute(ts.prop, [a[0] for a in ts.statevars], next_vars)))   
            curr_vars = next_vars  
            unrolling.append(trans)
    
    assert len(unrolling) == len(cti_queue)
    return unrolling, vars_at_time, concrete_vars, varlist


def check_if_new_predicates(new_predicates, old_predicates_dict, varlist):
    new_predicates, _ = remove_duplicates(new_predicates, varlist)
    # print('new')
    # for x in set(new_predicates):
    #     print(x)
    # print('old')
    # for x in set(old_predicates_dict):
    #     print(x)
    if set(new_predicates) <= set(old_predicates_dict):
        print('no new predicates found! increasing size...')
        # fail
        return False
    else:
        return True


queue = []
visited = []
def concretize_cti_queue(opts, cti_queue, paramts, predicates_dict, abs_vars):
    '''
    this function returns a triple 
        - a boolean flag (true if a real cti is found)
        - the real cti or None
        - a set of predicates or None
    ''' 
    global queue, visited
    from _updria import _stats
    sizes = {s : 1 for s in paramts.sorts} 
    # take the max among cti's
    for c in cti_queue:
        for s in paramts.sorts:
            n = len(c.universe_dict[s])
            if  n > sizes[s]:
                sizes[s] = n 
    _stats.max_concrete_size = sizes
    queue.append([sizes[s] for s in sizes])
    #visited list of size already done


    import _updria
    concrete_cti = [_updria.substitute_diagram(c.diagram, predicates_dict, abs_vars) for c in cti_queue]
    
    while True:

        bmc_list_formula, vars_at_time, concrete_vars, varlist = get_concrete_bmc_formula(opts, concrete_cti,\
             paramts, sizes)    
        groups = []
        wenv = msat_create_shared_env({'interpolation' : 'true'}, env)
        
        for idx, f in enumerate(bmc_list_formula):
            groups.append(msat_create_itp_group(wenv))
            msat_set_itp_group(wenv, groups[idx])
            msat_assert_formula(wenv, f)

        msat_last_error_message(wenv)
        res = msat_solve(wenv)
        if res == MSAT_SAT:
            print('true counterexample!')
            ##actually concrete counterexamples
            witness = []
            ## compute witness
            return False, witness, None, varlist
        elif res == MSAT_UNSAT:
            print('cex blocked in size %s' %str(sizes))
            visited.append([sizes[s] for s in sizes])
            ## sprurious counterexample
            ## compute interpolants
            print('extracting interpolants...')
            all_preds = []
            for i in range(1, len(bmc_list_formula)):
                itp = msat_get_interpolant(wenv, groups[:i])
                itp = substitute(itp, vars_at_time[i-1], concrete_vars)
                from _updria import find_initial_predicates
                predicates = find_initial_predicates(paramts.sorts, itp, TRUE())
                # for x in predicates:
                #     print(x)
                # normalize predicates
                # if all predicates are already discovered... restar with greater size
                
                all_preds += predicates
            if check_if_new_predicates(all_preds, predicates_dict, varlist):
                return True, None, all_preds, varlist
            else:
                _stats.max_concrete_size = sizes
                sizes = increase_size(sizes)

        else: 
            raise AssertionError('Ground BMC are expected to be either sat or unsat')
