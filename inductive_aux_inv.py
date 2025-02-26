from itertools import combinations
from queue import Queue

from solver import *


def obligation_in_list(o, o_list):
    for o_ in o_list:
        if o.vals.issubset(o_.vals):
            o_.cur = simplify(o.cur)
            o_.vals = o.vals
            return True
        elif o_.vals.issubset(o.vals):
            return True
        # if o_vals == o__vals:
        #     return True
    return False


def generalize_list(exprs: list[BoolRef]):
    if len(exprs) == 0:
        return True
    if len(exprs) == 1:
        return exprs[0]
    whole = Or(*exprs)
    generalized = []
    subsets = []
    visited = set()
    for expr in exprs:
        cur = get_vals(expr)
        flag = False
        for s in subsets:
            if s.issubset(cur):
                flag = True
                break
        if flag:
            continue
        for length in range(1, len(cur)):
            subset = combinations(cur, length)
            for s in subset:
                e_list = frozenset(var == val for (var, val) in s)
                if e_list in visited:
                    continue
                visited.add(e_list)
                gen_inv = And(*e_list)
                solver = Solver()
                solver.add(gen_inv)
                solver.add(And(gen_inv, Not(whole)))
                if solver.check() == unsat:
                    print(f'generalized: {gen_inv}')
                    generalized.append(gen_inv)
                    subsets.append(frozenset(s))
                    flag = True
                    break
            if flag:
                break
        if not flag:
            generalized.append(expr)
            subsets.append(cur)
    return generalized


def generalize(s, model):
    all_vars = [decl() for decl in model.decls()]
    all_vars = list(filter(lambda variable: '\'' not in str(variable), all_vars))

    essential_vars = []
    for var in all_vars:
        new_solver = Solver()
        new_solver.add(s.assertions())
        new_solver.add(var == model[var])
        if new_solver.check() == sat:
            new_solver = Solver()
            new_solver.add(s.assertions())
            new_solver.add(var != model[var])
            if new_solver.check() == unsat:
                essential_vars.append(var)
    return And([var == model[var] for var in essential_vars])


def generate_obligation(rule, inv_pair):
    (cond, cmds, others) = rule
    (inv, inv_prime) = inv_pair
    r = And(cond, cmds, others)

    def collect_literals(expr, literals):
        if expr.num_args() == 0:
            if expr.decl().kind() == Z3_OP_UNINTERPRETED:
                literals.add(expr)
        else:
            for child in expr.children():
                collect_literals(child, literals)

    lit = set()
    rule_lit = set()
    collect_literals(Or(inv.cur, inv_prime, cond, cmds), lit)
    collect_literals(r, rule_lit)

    redundant_lit = list(rule_lit - lit)

    if redundant_lit:
        r = Exists(redundant_lit, r)

    return simplify(And(r, inv_prime, Not(inv.cur)))


class InductiveAuxSolver(ProtSolver):
    def __init__(self, literals, primes, init, trans, post, post_prime, debug):
        super().__init__(literals, primes, init, trans, post, post_prime, debug)

    def enforce_obligation(self):
        queue = Queue()
        for p in self.property:
            queue.put((State(p[0], self.literals), p[1]))
            print(f'queue.put: {p[0]}')
        while not queue.empty():
            inv_pair = queue.get()
            for rule in self.trans:
                o = generate_obligation(rule, inv_pair)
                s = Solver()
                s.add(o)
                if s.check() == sat:
                    model = s.model()
                    g = generalize(s, model)
                    obligation = State(simplify(g), self.aux_invs)
                    if not obligation_in_list(obligation, self.aux_invs):
                        self.aux_invs.append(obligation)
                        next_state = substitute(obligation.cur, self.primeMap)
                        queue.put((obligation, next_state))
                        print(f'queue.put: {obligation.cur}')

    def run(self):
        self.enforce_obligation()
        self.aux_invs = generalize_list([inv.cur for inv in self.aux_invs])
        invs = [Not(expr) for expr in self.aux_invs]
        print('Inductive Invariant:')
        print(f'{And(invs)}')
