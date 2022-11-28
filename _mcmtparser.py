"""
Learning Abstractions from Bounded Analysis
An algorithm for the verification of parametric systems using quantifier-free
SMT-based model checking techniques

Authors:
Alberto Griggio <griggio@fbk.eu>
Gianluca Redondi <gredondi@fbk.eu>
"""

import sys, copy
import ply.lex as lex
import ply.yacc as yacc
from _updria import *


class MCMTLexer(object):
    tokens = (
        'SYMBOL',
        'NUMERAL',
        'SMT',
        'LOCAL',
        'GLOBAL',
        'INITIAL',
        'VAR',
        'CNJ',
        'UNSAFE',
        'TRANSITION',
        'GUARD',
        'UGUARD',
        'NUMCASES',
        'CASE',
        'VAL',
        'SYSTEM_AXIOM',
        )

    literals = "()![]:"
    t_ignore = ' \t'

    reserved = dict([(':' + t.lower(), t) for t in tokens[2:]])

    def __init__(self):
        self.lexer = None
        self.index_arrays = []
        self.index_arrays_extra = {}

    def t_newline(self, t):
        r'\n+'
        t.lexer.lineno += len(t.value)

    def t_comment(self, t):
        r':\b(comment|key_search|inv_search_max_index_var|inv_search_start|dynamic_predicate_abstraction|inv_search_max_num_invariants|inv_search_max_num_cand_invariants|no_backward_simplification|index|display_accelerated_transitions|determine_bounds|eevar|variable_redundancy_test|max_transitions_number)\b.*\n'
        if t.value.startswith(':comment'):
            bits = t.value.split()
            if len(bits) > 2:
                if bits[1] == 'index_arrays':
                    self.index_arrays += bits[2:]
                elif bits[1] == 'index_arrays_extra':
                    var = bits[2]
                    extra = [int(b) for b in bits[3:]]
                    self.index_arrays_extra[var] = extra
        t.lexer.lineno += 1

    def t_KEYWORD(self, t):
        r':[a-z_]+'
        t.type = self.reserved.get(t.value, 'SYMBOL')
        return t

    def t_SYMBOL(self, t):
        r'[a-zA-Z0-9._+\-*=%/?!$_~&^<>@]+'
        t.type = 'SYMBOL'
        try:
            int(t.value)
            t.type = 'NUMERAL'
        except ValueError:
            pass
        return t

    def t_error(self, t):
        raise Exception("ERROR")

    def build(self):
        self.lexer = lex.lex(object=self, lextab="exprlextab")

    def input(self, text):
        self.lexer.input(text)

    def token(self):
        return self.lexer.token()

# end of class MCMTLexer


class MCMTParser(object):
    def __init__(self, debug=False):
        self.lex = MCMTLexer()
        self.lex.build()
        self.tokens = self.lex.tokens
        kwds = {
            'write_tables' : False,
            'errorlog' : yacc.NullLogger(),
            'debug' : False,
            }
        if debug:
            kwds['debug'] = True
            del kwds['errorlog']

        self.var_bindings = {
            "true" : TRUE(),
            "false" : FALSE(),
            }
        self.extra_state = []
        self.next = {}
        self.scopes = []
        self.type_bindings = {
            'nat' : INT,
            'int' : INT,
            'bool' : BOOL,
            'real' : REAL
            }

        self.sig = []
        self.init = TRUE()
        self.rules = []
        self.inv = TRUE()
        self.trans_local = None
        self.trans_univ = []
        self.axioms = []
        self.frozen = []

        self.predmap = {
            '=' : Eq,
            '>' : GT,
            '<' : LT,
            '>=' : GE,
            '<=' : LE,
            }
        self.funmap = {
            '+' : Plus,
            '-' : Minus,
            '*' : Times,
            }
        self.in_lguard = False
            
        self.parser = yacc.yacc(module=self, tabmodule="exprtab", **kwds)

    def p_start(self, p):
        "start : system"
        p[0] = p[1]

    def p_system(self, p):
        "system : directives declarations rules"
        if self.frozen is not None:
            self.sig += self.frozen
        self.sig += self.extra_state
        if self.lex.index_arrays:
            i = QVar("i", INT)
            j = QVar("j", INT)
            svmap = { name(v) : v for v, _ in self.sig }
            other = []
            for n in self.lex.index_arrays:
                v = svmap[n]
                if not is_param(v):
                    other.append(v)
            for n in self.lex.index_arrays:
                v = svmap[n]
                extra = self.lex.index_arrays_extra.get(n)
                if is_param(v):
                    val = ParamVal(v, [j])
                    dom = Or(Eq(val, i), *[Eq(val, o) for o in other])
                    if extra:
                        dom = And(GE(j, Int(0)),
                                  Or(dom, *[Eq(val, Int(k)) for k in extra]))
                    self.axioms.append(Forall(j, Exists(i, dom)))
                else:
                    val = v
                    dom = Or(Eq(val, i), *[Eq(val, o) for o in other])
                    if extra:
                        dom = Or(dom, *[Eq(val, Int(k)) for k in extra])
                    self.axioms.append(Exists(i, dom))
                #print('AXIOM: %s' % smt2(self.axioms[-1]))
        
        p[0] = ParametricTransitionSystem([msat_type_repr(INT)],
                                          self.sig, self.axioms,
                                          self.init, self.rules, self.frozen,
                                          self.inv)

    def p_empty(self, p):
        "empty : "
        pass

    def p_directives(self, p):
        """directives : directives directive
                      | empty"""
        pass

    def p_directive(self, p):
        """directive : SMT '(' SYMBOL SYMBOL '(' SYMBOL NUMERAL NUMERAL ')' ')'
                     | SMT '(' SYMBOL SYMBOL ':' SYMBOL ')'
        """
        if len(p) == 8:
            if p[3] != 'define':
                raise Exception("unhandled :smt command: %s" % p[3])
            if not p[6].startswith(':'):
                raise Exception("unhandled :smt command: %s" % p[3])
            tp = self.type_bindings[p[6][1:]]
            name = p[4]
            c = Var(name, tp)
            n = Var(name + ".next", tp)
            self.var_bindings[name] = c
            if self.frozen is None:
                self.frozen = []
            self.frozen.append((c, n))
            self.next[name] = n
        else:
            if p[3] != 'define-type':
                raise Exception("unhandled :smt command: %s" % p[3])
            tp = p[4]
            if p[6] != 'subrange':
                raise Exception("unhandled type definition: %s" % p[6])
            self.type_bindings[tp] = INT

    def p_declarations(self, p):
        """declarations : declarations declaration
                        | empty"""
        pass

    def p_declaration(self, p):
        """declaration : local_decl
                       | global_decl"""
        pass

    def p_local_decl(self, p):
        "local_decl : LOCAL SYMBOL type"
        name = p[2]
        tp = p[3]
        c = Param(name, [INT], tp)
        n = Param(name + ".next", [INT], tp)
        self.var_bindings[name] = c
        self.sig.append((c, n))
        self.next[name] = n

    def p_global_decl(self, p):
        "global_decl : GLOBAL SYMBOL type"
        name = p[2]
        tp = p[3]
        c = Var(name, tp)
        n = Var(name + ".next", tp)
        self.var_bindings[name] = c
        self.sig.append((c, n))
        self.next[name] = n

    def p_type(self, p):
        "type : SYMBOL"
        tp = p[1]
        p[0] = self.type_bindings[tp]

    def p_rules(self, p):
        """rules : rules rule
                 | empty"""
        pass

    def p_rule(self, p):
        """rule : initial
                | unsafe
                | transition
                | system_axiom"""
        for v in self.scopes[-1]:
            del self.var_bindings[v]
        self.scopes.pop()

    def p_initial(self, p):
        "initial : initialscope vars cnj"
        self.init = p[3]
        for v in reversed(p[2]):
            self.init = Forall(v, self.init)

    def p_initialscope(self, p):
        "initialscope : INITIAL"
        self.scopes.append([])

    def p_vars(self, p):
        """vars : vars var
                | empty"""
        if len(p) == 2:
            p[0] = []
        else:
            p[0] = p[1]
            p[0].append(p[2])

    def p_var(self, p):
        "var : VAR SYMBOL"
        name = p[2]
        self.scopes[-1].append(name)
        v = QVar(name, INT)
        self.var_bindings[name] = v
        p[0] = v

    def p_cnj(self, p):
        "cnj : CNJ formulalist"
        p[0] = And(*p[2])

    def p_formulalist(self, p):
        """formulalist : formulalist formula
                       | formula
        """
        if len(p) == 2:
            p[0] = [p[1]]
        else:
            p[0] = p[1]
            p[0].append(p[2])

    ## def p_formula(self, p):
    ##     """formula : lit
    ##                | '(' SYMBOL formulalist ')'"""
    ##     if len(p) == 2:
    ##         p[0] = p[1]
    ##     else:
    ##         if p[3] not in ('and', 'or'):
    ##             raise Exception("unknown connective: %s" % p[3])
    ##         if p[3] == 'and':
    ##             p[0] = And(*p[4])
    ##         else:
    ##             p[0] = Or(*p[4])
    def p_formula(self, p):
        "formula : term"
        p[0] = p[1]

    def p_litlist(self, p):
        """litlist : litlist lit
                   | empty"""
        if len(p) == 3:
            p[0] = p[1]
            p[0].append(p[2])
        else:
            p[0] = []

    def p_lit(self, p):
        """lit : atom
               | notlit"""
        p[0] = p[1]

    def p_atom(self, p):
        "atom : term"
        s = p[1]
        p[0] = s

    def p_notlit(self, p):
        "notlit : '(' SYMBOL lit ')'"
        if p[2] == "not":
            p[0] = Not(p[3])
        else:
            raise Exception("unknown literal operation: %s" % p[2])

    def p_term(self, p):
        """term : symbol_term
                | number_term
                | array_term
                | '(' SYMBOL formulalist ')'"""
        n = len(p)
        if n == 2:
            p[0] = p[1]
        else:
            f = p[2]
            if f == 'and':
                p[0] = And(*p[3])
            elif f == 'or':
                p[0] = Or(*p[3])
            elif f == '=>':
                p[0] = Implies(*p[3])
            elif len(p[3]) == 1:
                if f == 'not':
                    p[0] = Not(p[3][0])
                elif f == "+":
                    p[0] = p[3][0]
                elif f == "-":
                    p[0] = Times(Int(-1), p[3][0])
                else:
                    raise Exception("unhandled function: %s" % f)
            elif len(p[3]) == 2:
                func = self.predmap.get(f, self.funmap.get(f))
                if not func:
                    raise Exception("unhandled function: %s" % f)
                else:
                    p[0] = func(p[3][0], p[3][1])
            else:
                raise Exception("unhandled function: %s" % f)

    def p_symbol_term(self, p):
        "symbol_term : SYMBOL"
        s = p[1]
        p[0] = self.var_bindings[s]

    def p_number_term(self, p):
        "number_term : NUMERAL"
        p[0] = Int(int(p[1]))

    def p_array_term(self, p):
        """array_term : symbol_term '[' symbol_term ']'
                      | symbol_term '[' number_term ']'"""
        if is_param(p[1]):
            if not is_qvar(p[3]) and not self.in_lguard:
                raise Exception("Invalid array index: %s" % smt2(p[3]))
            p[0] = ParamVal(p[1], [p[3]])
        else: # "global" arrays
            p[0] = p[1]

    def p_unsafe(self, p):
        "unsafe : unsafescope vars cnj"
        self.inv = Implies(Alldiff(p[2]), Not(p[3]))
        for v in reversed(p[2]):
            self.inv = Forall(v, self.inv)

    def p_unsafescope(self, p):
        "unsafescope : UNSAFE"
        self.scopes.append([])

    def p_transition(self, p):
        "transition : transitionscope vars transguards transupdates"
        exvars = []
        exqvars = []
        uvar = None
        j = QVar("j", INT)
        for i, v in enumerate(p[2]):
            if v != j:
                exvars.append(v)
                exqvars.append(QVar("i%d" % i, INT))
            else:
                uvar = v
        if uvar is None:
            raise Exception("transition without quantified var")
        local_guard, universal_guard = p[3]
        local_update, universal_update = p[4]
        kind, qv, local_guard = split_quantifier(local_guard)
        if kind == EXISTS:
            n = len(exvars)
            exvars += qv
            exqvars += [QVar("i%d" % (i+n), INT) for i in range(len(qv))]
        else:
            assert not qv
        kind, qv1, universal_guard = split_quantifier(universal_guard)
        assert kind == FORALL or not qv1
        kind, qv2, universal_update = split_quantifier(universal_update)
        assert kind == FORALL or not qv2
        uvars = sorted(set(qv1 + qv2), key=msat_term_id)
        rule = And(local_guard, local_update, universal_guard, universal_update)
        rule = substitute(rule, exvars, exqvars)
        for q in reversed(uvars):
            rule = Forall(q, rule)
        for q in reversed(exqvars):
            rule = Exists(q, rule)
        self.rules.append(rule)
        #print('ADDED RULE %d:\n%s\n' % (len(self.rules), self.rules[-1]))

    def p_transitionscope(self, p):
        "transitionscope : TRANSITION"
        self.scopes.append([])

    def p_transguards(self, p):
        "transguards : lguard uguards"
        if p[2]:
            ug = Or(*p[2])
            x = self.var_bindings.get('x')
            j = self.var_bindings['j']
            if x is not None:
                ug = Or(Eq(x, j), ug)
            uguards = [Forall(j, ug)]
        else:
            uguards = []
        ug = And(*uguards)

        idxmap = {}
        def flatten_e_index(lit):
            n = []
            def visit(e, t, pre):
                if not pre and is_param_val(t):
                    idx = arg(t, 1)
                    if not is_qvar(idx):
                        n.append(idx)
                return MSAT_VISIT_PROCESS
            msat_visit_term(env, lit, visit)
            if n:
                qv = []
                for i, idx in enumerate(n):
                    v = idxmap.get(idx)
                    if not v:
                        v = QVar("e%d" % i, INT)
                        idxmap[idx] = v
                    qv.append(v)
                lit = substitute(lit, n, qv)
                pre = And(*[Eq(i, v) for (i, v) in zip(qv, n)])
                return And(pre, lit)
            else:
                return lit
            
        lg = And(*[flatten_e_index(lit) for lit in p[1]])
        if idxmap:
            for v in sorted(idxmap.values(), key=id_, reverse=True):
                lg = Exists(v, lg)
        if ug != TRUE():
            j = QVar("j", INT)
            ug = Forall(j, ug)
        p[0] = lg, ug

    def p_lguard(self, p):
        "lguard : lguard_scope litlist"
        if not p[2]:
            p[0] = []
        else:
            p[0] = p[2]
        self.in_lguard = False

    def p_lguard_scope(self, p):
        "lguard_scope : GUARD"
        self.in_lguard = True

    def p_uguards(self, p):
        """uguards : uguards uguard
                   | empty"""
        if len(p) == 2:
            p[0] = []
        else:
            p[0] = p[1]
            p[0].append(p[2])

    def p_uguard(self, p):
        "uguard : UGUARD litlist"
        g = And(*p[2])
        p[0] = g

    def p_transupdates(self, p):
        "transupdates : numcases cases"
        trans_univ = TRUE()
        for d in self.trans_univ:
            for g in sorted(d, key=msat_term_id):
                u = d[g]
                trans_univ = And(trans_univ, Implies(g, u))
        if trans_univ != TRUE():
            j = QVar("j", INT)
            trans_univ = Forall(j, trans_univ)
        p[0] = self.trans_local, trans_univ

    def p_numcases(self, p):
        "numcases : NUMCASES NUMERAL"
        self.trans_local = None
        self.trans_univ = []

    def p_cases(self, p):
        """cases : cases case
                 | case"""
        if len(p) == 2:
            g, ul = p[1]
            assert len(ul) == len(self.sig)
            j = self.var_bindings['j']
            x = self.var_bindings.get('x')
            if x is not None:
                f = TRUE()
                for i, u in enumerate(ul):
                    u = substitute(u, [j], [x])
                    v = self.sig[i][1]
                    if is_param(v):
                        v = ParamVal(v, [x])
                    f = And(f, Eq(v, u))
                self.trans_local = f
            else:
                self.trans_local = TRUE()                
                self.trans_univ = [{} for u in ul]
                for i, u in enumerate(ul):
                    v = self.sig[i][1]
                    if is_param(v):
                        v = ParamVal(v, [j])
                    self.trans_univ[i][g] = Eq(v, u)
        else:
            assert self.trans_local is not None
            g, ul = p[2]
            j = self.var_bindings['j']
            y = self.var_bindings.get('y')
            first_univ = not self.trans_univ
            if not self.trans_univ:
                self.trans_univ = [{} for u in ul]
            if y is not None and first_univ and g == Eq(y, j):
                # local transition on y
                f = TRUE()
                for i, u in enumerate(ul):
                    u = substitute(u, [j], [y])
                    v = self.sig[i][1]
                    if is_param(v):
                        v = ParamVal(v, [y])
                    f = And(f, Eq(v, u))
                self.trans_local = And(self.trans_local, f)
            else:
                if 'x' in self.var_bindings:
                    g = And(g, Not(Eq(j, self.var_bindings['x'])))
                assert len(ul) == len(self.sig)
                for i, u in enumerate(ul):
                    v = self.sig[i][1]
                    if is_param(v):
                        v = ParamVal(v, [j])
                    self.trans_univ[i][g] = Eq(v, u)

    def p_case(self, p):
        "case : casecond casevals"
        p[0] = p[1], p[2]

    def p_casecond(self, p):
        "casecond : CASE litlist"
        if not p[2]:
            p[0] = TRUE()
        else:
            p[0] = And(*p[2])

    def p_casevals(self, p):
        """casevals : casevals caseval
                    | empty"""
        if len(p) == 2:
            p[0] = []
        else:
            p[0] = p[1]
            p[0].append(p[2])

    def p_caseval(self, p):
        "caseval : VAL term"
        p[0] = p[2]

    def p_system_axiom(self, p):
        "system_axiom : system_axiom_scope vars cnj"
        ax = p[3]
        for v in reversed(p[2]):
            ax = Forall(v, ax)
        self.axioms.append(ax)

    def p_system_axiom_scope(self, p):
        "system_axiom_scope : SYSTEM_AXIOM"
        self.scopes.append([])

    def p_error(self, p):
        # get formatted representation of stack
        parser = self.parser
        stack_state_str = ' '.join([symbol.type for symbol in
                                    parser.symstack][1:])

        raise Exception('Syntax error in input (line: {})! '
                        'Parser State:{} {} . {}'
                        .format(p.lineno,
                                parser.state,
                                stack_state_str,
                                p))

    def parse(self, data):
        return self.parser.parse(input=data, lexer=self.lex)

# end of class MCMTParser


