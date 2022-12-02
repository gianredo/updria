from optparse import Option
from _updria import *


def parse_vmt(opts, data): 
        
    #some hacks for strange ic3po format...
    data = data.replace('.action_ext:', '')
    data = data.replace('V__fml:', '')
    data = data.replace('V__new_loc:0', 'new')
    data = data.replace('V__new_fml:', '')
    data = data.replace('V__loc:', '')
    data = data.replace('ext:', '')
    data = data.replace('__fml:', '') 
                   
    wenv = msat_create_env({'allow_bool_function_args': 'true'})
    res = msat_annotated_list_from_smtlib2(wenv, data)
    assert res is not None, msat_last_error_message(wenv)
    terms, annots = res
    sv = []
    init = msat_make_true(wenv)
    trans = []
    axioms = []
    definitions = []
    prop = None
    frozen = []
    sorts = set()

    def unquote(s):
        if s.startswith('|') and s.endswith('|'):
            return s[1:-1]
        return s

    for i, t in enumerate(terms):
        key = annots[2*i]
        val = annots[2*i+1]
        if key == 'init':
            assert val == 'true'
            init = msat_make_and(wenv, init, t)
        elif key == 'action':
            trans.append(t)
        elif key == 'axiom':
            axioms.append(t)
        # also keyword defintion: this are used by ic3po for ghost variables.
        elif key == 'definition':
            raise NotImplementedError
            #definitions.append(t)
        elif key == 'invar-property':
            idx = int(val)
            if idx == opts.vmt_property:
                prop = t
        elif key == 'global' and val == 'true':
            decl = msat_term_get_decl(t)
            ar = msat_decl_get_arity(decl)
            if ar == 0:
                frozen.append(t)
        # next is differencte since current is defined as (c <list args>)
        # but d is equal
        elif key == 'next':
            c = t
            decl = msat_term_get_decl(t)
            ar = msat_decl_get_arity(decl)
            value = type_(t)
            if ar == 0:
                c = msat_term_get_decl(c)
                n = msat_declare_function(wenv, unquote(val), value)
                sv.append((c, n))
            else:
                argslist = []
                # fun <args> value
                # array arg1 (array arg2 (... (array argn value)))
                for i in range(ar):
                    idx = msat_term_get_arg(t, i)
                    idxtp = type_(idx)
                    argslist.append(idxtp)
                    tp = msat_get_function_type(wenv, argslist, value)

                c = msat_declare_function(wenv, name(c), tp)
                n = msat_declare_function(wenv, unquote(val), tp)
                sv.append((c, n))

        elif key == 'sort':
            pass
        else:
            print(key)

    assert prop is not None, "Property %d not found!" % opts.vmt_property

    cache = {}
    tagmap = {
        MSAT_TAG_AND: msat_make_and,
        MSAT_TAG_OR: msat_make_or,
        MSAT_TAG_NOT: msat_make_not,
        MSAT_TAG_IFF: msat_make_iff,
        MSAT_TAG_PLUS: msat_make_plus,
        MSAT_TAG_TIMES: msat_make_times,
        MSAT_TAG_DIVIDE: msat_make_divide,
        MSAT_TAG_FLOOR: msat_make_floor,
        MSAT_TAG_LEQ: msat_make_leq,
        MSAT_TAG_EQ: msat_make_eq,
        MSAT_TAG_ITE: msat_make_term_ite,
        MSAT_TAG_FORALL: msat_make_forall,
        MSAT_TAG_EXISTS: msat_make_exists,
        }

    def get_tp(e, tp):
        if msat_is_bool_type(e, tp):
            return BOOL
        elif msat_is_integer_type(e, tp):
            return INT
        elif msat_is_rational_type(e, tp):
            return REAL
        else:
            key = msat_type_repr(tp)
            return msat_get_simple_type(env, key)

    next_qvar = 1
    write_qvar = None

    def get_param(e: msat_env, decl : msat_decl):
        n = msat_decl_get_arity(decl)
        if n == 0:
            name = msat_decl_get_name(decl)
            value = msat_decl_get_return_type(decl)
            return Var(name, get_tp(e, value))
        else:
            idxlist = []
            for i in range(n):
                idxlist.append(msat_decl_get_arg_type(decl, i))
            name = msat_decl_get_name(decl)
            value = msat_decl_get_return_type(decl)
            
            return Param(name, [get_tp(e, i) for i in idxlist], get_tp(e, value))

    def visit(e, t, pre):
        nonlocal next_qvar, write_qvar
        if not pre:
            tp = msat_term_get_type(t)
            if msat_term_is_constant(e, t):                
                decl = msat_term_get_decl(t)
                name = msat_decl_get_name(decl)
                assert arity(t) == 0
                tt = Var(name, get_tp(e, tp))
            elif msat_term_is_variable(e, t):
                tt = QVar("_i%d%s" % (next_qvar, msat_type_repr(tp)),
                          get_tp(e, tp))
                next_qvar += 1
            elif not msat_term_arity(t):
                tt = msat_make_copy_from(env, t, e)
            elif msat_term_is_uf(e, t):               
                args = [cache[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]
                assert all(a is not None for a in args)
                d = msat_term_get_decl(t)
                
                if d in [x for (x, _) in sv] + [x for (_, x) in sv]:
                    tt = ParamVal(get_param(e, d), args)
                else:
                    name = msat_decl_get_name(d)
                    ptps = [get_tp(e, msat_decl_get_arg_type(d, i))
                        for i in range(msat_decl_get_arity(d))]
                    rtp = get_tp(e, msat_decl_get_return_type(d))               
                    ftp = msat_get_function_type(env, ptps, rtp)
                    dd = msat_declare_function(env, name, ftp)
                    tt = msat_make_uf(env, dd, args)
            else:
                
                args = [cache[msat_term_get_arg(t, i)]
                        for i in range(msat_term_arity(t))]
                assert all(a is not None for a in args)
                tag = msat_decl_get_tag(e, msat_term_get_decl(t))
                
                try:
                    f = tagmap[tag]
                    tt = f(env, *args)
                except KeyError:
                    raise

            cache[t] = tt
        return MSAT_VISIT_PROCESS

    def get_vars(t, vset):
        res = []

        def visit(e, t, pre):
            if pre and t in vset:
                res.append(t)
            return MSAT_VISIT_PROCESS
        msat_visit_term(env, t, visit)
        return sorted(res, key=id_)

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

    def get(t):
        nonlocal next_qvar, write_qvar
        next_qvar = 1
        write_qvar = None
        msat_visit_term(wenv, t, visit)
        res = cache[t]
        kind, ev, ebody = split_quantifier(res)
        if kind == EXISTS:
            kind, qv, body = split_quantifier(ebody)
        else:
            qv, body = ev, ebody
            ev = []
        if write_qvar is not None:
            qv.append(write_qvar)
        if not qv:
            return res

        # qvset = set(qv)
        # mv = 0
        # res = TRUE()
        # old_qv = qv[:]
        # for c in collect(env, MSAT_TAG_AND, body):
        #     uv = get_vars(c, qvset)
        #     if uv:
        #         to_sub = []
        #         for v in uv:
        #             tp = msat_term_get_type(v)
        #             for w in qv:
        #                 tpw = msat_term_get_type(w)
        #                 if msat_type_equals(tp, tpw):
        #                     to_sub.append(w)
        #                     qv.remove(w)
        #                     break
        #         qv = old_qv
        #         c = substitute(c, uv, to_sub)
        #     res = And(res, c)
        # for v in reversed(old_qv):
        #     res = Forall(v, res)
        # for v in reversed(ev):
        #     res = Exists(v, res)
        return res

    statevars = [(get_param(wenv, c), get_param(wenv, n)) for (c, n) in sv]

    init = get(init)
    for defs in definitions:
        edef = get(defs)
        if not get_vars(edef, [y for (_, y) in statevars]):
            init = And(init, edef)

    new_axs = []
    for ax in axioms:
        for conj in collect(wenv, MSAT_TAG_AND, ax):
            new_axs.append(conj)
    axioms = [get(ax) for ax in new_axs]
    #definitions = [get(defs) for defs in definitions]
    prop = get(prop)


    frozenvars = []
    for f in frozen:
        f = get(f)
        n = Var(".{%s}.next" % name(f), type_(f))
        statevars.append((f, n))
        frozenvars.append((f, n))

    # extract rules
    # inertia means that variables that do not explicitly change are left unchanged
    # so we add an universal axiom for that
    def add_inertia(rule : msat_term):
        for (c, n) in set(statevars).difference(set(frozenvars)):
            if n not in get_vars(rule, [y for (_, y) in statevars]):
                for (cc, nn) in sv:
                    if msat_decl_get_name(nn) == name(n):
                        arity = msat_decl_get_arity(nn)
                        break
                if arity == 0:
                    inertia = Eq(c, n)

                else:
                    qvars = []
                    for i in range(arity):
                        tp = msat_decl_get_arg_type(nn, i)
                        qvars.append(QVar('i%s%s' %(i, msat_type_repr(tp)), get_tp(env, tp)))
                    inertia = Eq(ParamVal(c, qvars), ParamVal(n, qvars))
                    for i in qvars:
                        inertia = Forall(i, inertia)

                rule = And(rule, inertia)
        
        
        return rule


    trans_rules = [add_inertia(get(rule)) for rule in trans]
    #trans_rules = [get(rule) for rule in trans]

    # this is for ghost variables in ic3po
    # for rule in trans:
    #     for defs in definitions:
    #         rule = msat_make_and(wenv, rule, defs)    
            

    def get_sorts(env, all_formulae):
        sorts = set()
        
        def find_qf(e, t, pre):
            if pre and (msat_term_is_exists(e, t) or msat_term_is_forall(e, t)):
                var = msat_term_get_arg(t, 0)
                tp = msat_term_get_type(var)
                sorts.add(msat_type_repr(tp))
            return MSAT_VISIT_PROCESS

        for formula in all_formulae:
            msat_visit_term(env, formula, find_qf)

        return sorts

    all_formulae = axioms + [init] + trans_rules + [prop]
    sorts = get_sorts(env, all_formulae)

    return ParametricTransitionSystem(sorted(sorts),
                                      statevars, axioms, init,
                                      trans_rules, frozenvars, prop)

