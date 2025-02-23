from queue import Queue

from z3 import *


# a cube is a conjunction of literals associated with a given frame (t) in the trace
class Cube(object):
    # make a tcube object associated with frame t. If t is none, have it be frameless
    def __init__(self, model, lMap, t=None):
        self.frame_index = t
        # filter out primed variables when creating cube
        self.cubeLiterals = [lMap[str(literal)] == model[literal] for literal in model if '\'' not in str(literal)]

    # return the conjunction of all literals in this cube
    def cube(self):
        return And(*self.cubeLiterals)

    def __repr__(self):
        return str(self.frame_index) + ": " + str(sorted(self.cubeLiterals, key=str))

    def __str__(self):
        return f'{sorted(self.cubeLiterals, key=str)} of frame {self.frame_index}'


def get_vals(expr: BoolRef):
    vals = set()
    for rule_e in expr.children():
        if rule_e.decl().name() == '=':
            lhs, rhs = rule_e.children()
            if lhs.decl().kind() == Z3_OP_UNINTERPRETED:
                vals.add((lhs, rhs))
            elif rhs.decl().kind() == Z3_OP_UNINTERPRETED:
                vals.add((rhs, lhs))
        else:
            assert len(rule_e.children()) < 2
            if len(rule_e.children()) == 0:
                vals.add((rule_e, BoolVal(True)))
            else:
                v_list = rule_e.children()
                assert len(v_list) == 1
                vals.add((v_list[0], BoolVal(False)))
    return frozenset(vals)


class State:
    def __init__(self, cur: BoolRef, literals):
        self.cur = simplify(cur)
        self.literals = literals
        self.vals = get_vals(self.cur)

    def satisfies(self, cond):
        solver = Solver()
        solver.add(self.cur)
        solver.add(cond)
        return solver.check() == sat

    def apply(self, cmds, prime_map):
        cmds = simplify(cmds)
        last_state = self.vals
        next_state = set((p, var) for (var, p) in prime_map)
        substitution = list(next_state | last_state)
        new_eqs = []
        for rule_e in cmds.children():
            if rule_e.decl().name() == '=':
                lhs, rhs = rule_e.children()
                new_lhs = substitute(lhs, substitution)
                new_rhs = substitute(rhs, substitution)
                new_eq = (new_lhs == new_rhs)
                new_eqs.append(new_eq)
            else:
                assert len(rule_e.children()) < 2
                new_eqs.append(substitute(rule_e, next_state))
        self.cur = simplify(And(*new_eqs))
        self.vals = get_vals(self.cur)

    def __repr__(self):
        return str(self.cur)

    def __str__(self):
        return str(self.cur)

    def __eq__(self, other):
        return isinstance(other, State) and simplify(self.cur).eq(simplify(other.cur))

    def __hash__(self):
        return hash(self.vals)

    def hash(self):
        return hash(self.vals)


def obligation_in_list(o, o_list):
    for o_ in o_list:
        if eq(o, o_):
            return True
    return False


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
    collect_literals(Or(inv, inv_prime, cond, cmds), lit)
    collect_literals(r, rule_lit)

    redundant_lit = list(rule_lit - lit)

    if redundant_lit:
        r = Exists(redundant_lit, r)

    return simplify(And(r, Not(inv_prime), inv))


class ProtSolver(object):
    def __init__(self, literals, primes, init, trans, post, post_prime, debug):
        self.debug = debug
        self.init = init
        self.trans = [(simplify(cond), simplify(cmds), simplify(others)) for (cond, cmds, others) in trans]
        self.literals = literals
        prop = [simplify(p) for p in post]
        prop_prime = [simplify(p) for p in post_prime]
        self.aux_invs = []
        self.property = (list(zip(prop, prop_prime)))
        self.frames = []
        self.primeMap = [(from_, to_) for from_, to_ in zip(literals, primes)]
        self.lMap = {str(literal): literal for literal in literals} | {str(literal): literal for literal in primes}
        self.enforce_obligation()

    def enforce_obligation(self):
        queue = Queue()
        for p in self.property:
            queue.put(p)
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
                    obligation = simplify(Not(g))
                    if not obligation_in_list(obligation, self.aux_invs):
                        self.aux_invs.append(obligation)
                        next_state = substitute(obligation, self.primeMap)
                        queue.put((obligation, next_state))
                        print(f'queue.put: {obligation}')

    def run(self):
        pass
