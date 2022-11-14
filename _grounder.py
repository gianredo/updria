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
    from _updria import _param_map, _param_read_funs
    
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

        #this is true if existentials in transitions are assumed different
        #which is true for mcmt, now broken
        if False:
            for (e_rule, is_degenerate) in instantiate_ex_vars(rule, varlist):
                assert not is_degenerate
                t_rule = expand_quantifiers(e_rule, varlist)
                if opts.show_witness and opts.cex_track_rules:
                    t_rule = And(t_rule, Eq(rule_var, Int(i)))    
                trans = Or(trans, t_rule)
        else:
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
   
    is_forall = True
    def visit(env, t, pre):
        nonlocal is_forall
        if pre and msat_term_is_exists(env, t):
            is_forall = False
            return MSAT_VISIT_ABORT
        return MSAT_VISIT_PROCESS

    msat_visit_term(env, paramts.prop, visit)

    # if is_forall:
    #     # sound for symmetries, crucial for good lemmas
    #     def collect(e, tag, formula):
    #         to_process = [formula]
    #         seen = set()
    #         while to_process:
    #             cur = to_process[-1]
    #             to_process.pop()
    #             if cur in seen:
    #                 continue
    #             seen.add(cur)
    #             if msat_decl_get_tag(e, msat_term_get_decl(cur)) == tag:
    #                 n = msat_term_arity(cur)
    #                 for i in range(n):
    #                     to_process.append(msat_term_get_arg(cur, n-1-i))
    #             else:
    #                 yield cur    
        
    #     prop = TRUE()
    #     for conj in collect(env, MSAT_TAG_AND, paramts.prop):
    #         prop = And(prop, instantiate_u_vars(conj, varlist))

    # if opts.input_language == 'mcmt':
    #     prop = instantiate_u_vars(paramts.prop, varlist)

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


def model_check(opts, ts, symset=None):
    var2uf = {}
    ufsubst = []
    ufvalues = []
    def remove_uf(ts):
        uf2var = {}
        curvars = set(p[0] for p in ts.statevars)
        nextvars = { p[1] : p[0] for p in ts.statevars }
        sv = {}
        ok = True
        
        def visit(e, t, pre):
            nonlocal ok
            if not pre:
                if t in uf2var:
                    return MSAT_VISIT_SKIP
                if is_param_val(t):
                    c = Var("X{%d}" % id_(t), type_(t))
                    var2uf[c] = t
                    ufsubst.append(c)
                    ufvalues.append(t)
                    a = arg(t, 0)
                    i = arg(t, 1)
                    if a in curvars and i in curvars:
                        sv.setdefault((a, i), [None, None])[0] = c
                    elif a in nextvars and i in curvars:
                        sv.setdefault((nextvars[a], i), [None, None])[1] = c
                    uf2var[t] = c
                elif msat_term_is_uf(e, t) and \
                         any(is_param(c) for c in args(t)):
                    ok = False
                    return MSAT_VISIT_ABORT
                else:
                    targs = [uf2var[a] for a in args(t)]
                    tt = term(t, targs)
                    uf2var[t] = tt
            return MSAT_VISIT_PROCESS

        def get(t):
            msat_visit_term(env, t, visit)
            if ok:
                return uf2var[t]
            else:
                return t

        newinit = get(ts.init)
        newtrans = get(ts.trans)
        newprop = get(ts.prop)
        newtransguard = get(ts.trans_guard)
        
        statevars = []
        for (c, n) in ts.statevars:
            if not is_param(c):
                statevars.append((c, n))

        for idx in sorted(sv, key=lambda t :
                          (id_(t[0]), id_(t[1]))):
            c, n = sv[idx]
            if not (c and n):
                ok = False
                break
            statevars.append((c, n))

        if not ok:
            var2uf.clear()
            return ts
        else:
            ret = TransitionSystem(statevars, newinit, newtrans,
                                   newtransguard, newprop)
            return ret

    if opts.remove_uf:
        ts = remove_uf(ts)
    
    ic3 = msat_create_ic3(env)
    if msat_ic3_setopt(ic3, "ic3core.reduce_inv", "true") != 0:
        msat_ic3_setopt(ic3, "ic3core.reduce_inv", "2")
    msat_ic3_setopt(ic3, "ic3ia.add_initial_reset", "true")
    if opts.euf_low_priority:
        msat_ic3_setopt(ic3, "mathsat-itp.theory.euf.low_priority", "true")
    msat_ic3_set_verbosity(ic3, 1)

    for (c, n) in ts.statevars:
        err = msat_ic3_add_state_var(ic3, c, n)
        assert not err, msat_ic3_last_error_message(ic3)

    err = msat_ic3_set_init(ic3, ts.init)
    assert not err, msat_ic3_last_error_message(ic3)

    err = msat_ic3_set_trans(ic3, And(ts.trans, ts.trans_guard))
    assert not err, msat_ic3_last_error_message(ic3)

    prop_idx = msat_ic3_add_invar_property(ic3, ts.prop)
    assert prop_idx == 0, msat_ic3_last_error_message(ic3)

    use_ic3ia = _has_ic3ia and opts.ic3ia

    vmt = msat_ic3_to_smtlib2(ic3)
    # with open('/tmp/out.vmt', 'w') as out:
    #     out.write(vmt)

    if use_ic3ia:
        ic3ia_opts = [
            '-v', '1',
            '-inv-reduce', '1'
            '-inc-ref', '1',
            '-lazy-init-preds', '1',
            '-abs-bool-vars', '1',
            ]
        vmt = msat_ic3_to_smtlib2(ic3)
        if opts.use_symmetries and symset:
            terms, annots = msat_annotated_list_from_smtlib2(env, vmt)
            for v in symset:
                terms.append(v)
                annots.append("symmetry-group")
                annots.append("1")
            vmt = msat_annotated_list_to_smtlib2(env, terms, annots)
            ic3ia_opts += ['-use-symmetries', '1']
        ## with open('/tmp/out.vmt', 'w') as out:
        ##     out.write(vmt)
            ##     exit(1)

        prover = ic3ia.ic3ia_create(vmt,  ic3ia_opts)
        safe = ic3ia.ic3ia_prove(prover)
        wit = ic3ia.ic3ia_witness(prover)
        ic3ia.ic3ia_destroy(prover)

        res = msat_annotated_list_from_smtlib2(env, wit)
        assert res, msat_last_error_message(env)
        terms, annots = res
        witness = []

        err = MSAT_MAKE_ERROR_TERM()

        if safe:
            status = 0
            clauses = []
            for i, t in enumerate(terms):
                k = annots[2*i]
                v = annots[2*i+1]
                if k == 'clause':
                    j = int(v)
                    while len(clauses) <= j:
                        clauses.append([])
                    clauses[j].append(t)
            for cls in clauses:
                witness += cls
                witness.append(err)
            witness.append(err)
        else:
            status = 1
            steps = []
            for i, t in enumerate(terms):
                k = annots[2*i]
                v = annots[2*i+1]
                if k == 'step':
                    j = int(v)
                    while len(steps) <= j:
                        steps.append([])
                    steps[j].append(t)
            for step in steps:
                witness += step
                witness.append(err)
            witness.append(err)
    


    else:       
        err = msat_ic3_init(ic3, MSAT_IC3_IA)
        assert not err, msat_ic3_last_error_message(ic3)

        status = msat_ic3_prove(ic3, prop_idx)
        assert status in (0, 1), msat_ic3_last_error_message(ic3)

        witness = msat_ic3_witness(ic3)
        assert witness, msat_ic3_last_error_message(ic3)

    if opts.remove_uf and var2uf:
        for i, t in enumerate(witness):
            if not MSAT_ERROR_TERM(t):
                tt = var2uf.get(t)
                if tt is None:
                    tt = substitute(t, ufsubst, ufvalues)
                    var2uf[t] = tt
                witness[i] = tt

    ret = VerificationResult(SAFE if status == 0 else UNSAFE, witness)    
    msat_destroy_ic3(ic3)
    
    return ret


def extract_lemmas(paramts, result, lemmas):
    new_lemmas = []
    seen_lemmas = set()
    cls = FALSE()
    num_qvars = {s : 0 for s in paramts.sorts}
    for t in result.witness[:-1]:
        if MSAT_ERROR_TERM(t):
            l, n = lemma(cls, paramts.sorts)
            if l not in seen_lemmas:
                seen_lemmas.add(l)
                new_lemmas.append(l)
                num_qvars = {s : max(num_qvars[s], n[s]) for s in paramts.sorts}
            cls = FALSE()
        else:
            cls = Or(cls, t)

    return new_lemmas, num_qvars


def extract_cex(witness, conc_size):
    cex = []
    step = []
    tosubst = []
    values = []
    for i, t in enumerate(witness[:-1]):
        if MSAT_ERROR_TERM(t):
            cex.append([substitute(s, tosubst, values) for s in step])
            step = []
            tosubst = []
            values = []
        else:
            if msat_term_is_equal(env, t):
                v, n = arg(t, 0), arg(t, 1)
                if not is_prophecy(v):
                    v, n = n, v
                if is_prophecy(v):
                    tosubst.append(v)
                    values.append(n)
                    continue
            step.append(t)
    return cex


def get_concrete_bmc_formula(opts, cti_queue, paramts, sizes): 
    '''
    takes the cti queue and a paramts
    return the bmc as list [step0, ..., stepn]
    '''

    ts = get_concretization(opts, paramts, sizes, [])
    varlist = {s : [p_var(i, mksort(s)) for i in range(sizes[s])]
               for s in paramts.sorts}


    for step, diagram in enumerate(cti_queue):
        if step == 0: 
            curr_vars = [Var(name(v) + ".step_%s" %step, type_(v)) for (v, _) in ts.statevars] 
            init_step = And(ts.init, expand_quantifiers(diagram, varlist))
            init_step = substitute(init_step, [a[0] for a in ts.statevars], curr_vars)
            unrolling = [init_step]
        else:
            trans = substitute(ts.trans, [a[0] for a in ts.statevars], curr_vars)
            next_vars = [Var(name(v) + ".step_%s" %step, type_(v)) for (v, _) in ts.statevars] 
            trans = substitute(trans, [a[1] for a in ts.statevars], next_vars)
            diagram = expand_quantifiers(diagram, varlist)
            diagram = substitute(diagram, [a[0] for a in ts.statevars], next_vars)
            curr_vars = next_vars
            unrolling.append(And(trans, diagram))
    
    assert len(unrolling) == len(cti_queue)
    return unrolling


def concretize_cti_queue(opts, cti_queue, paramts, predicates_dict, abs_vars):
    '''
    this function returns a triple 
        - a boolean flag (true if a real cti is found)
        - the real cti or None
        - a set of predicates or None
    ''' 

    sizes = {s : 1 for s in paramts.sorts} 
    # take the max among cti's
    for c in cti_queue:
        for s in paramts.sorts:
            n = len(c.universe_dict[s])
            if  n > sizes[s]:
                sizes[s] = n

    import _updria
    concrete_cti = [_updria.substitute_diagram(c.diagram, predicates_dict, abs_vars) for c in cti_queue]
    
    bmc_list_formula = get_concrete_bmc_formula(opts, concrete_cti, paramts, sizes)    
    groups = []
    wenv = msat_create_shared_env({'interpolation' : 'true'}, env)
    
    for idx, f in enumerate(bmc_list_formula):
        groups.append(msat_create_itp_group(wenv))
        msat_set_itp_group(wenv, groups[idx])
        msat_assert_formula(wenv, f)

    res = msat_solve(wenv)
    if res == MSAT_SAT:
        print('true counterexample!')
        ##actually concrete counterexamples
        witness = []
        ## compute witness
        return -1 
    elif res == MSAT_UNSAT:
        print('cex blocked in size %s' %str(sizes))
        ## sprurious counterexample
        ## compute interpolants
        print('extracting interpolants...')
        for i in range(len(bmc_list_formula)):
            itp = msat_get_interpolant(wenv, groups[:i])
            print(itp)
        new_preds_dict = []
        return -1
        return False, None, new_preds_dict
    
    else: 
        raise AssertionError('Ground BMC are expected to be either sat or unsat')
