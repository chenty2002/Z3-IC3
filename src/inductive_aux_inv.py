from itertools import combinations
from queue import Queue

from solver import *
from utils import z3_inv_to_murphi
from generalize_murphi import check_murphi, murphi_check_init


def obligation_in_list(o, o_list):
    s = Solver()
    cex_list = [o_[1] for o_ in o_list]
    s.add(And(o, Not(Or(*cex_list))))
    return s.check() == unsat


def generalize_list(cexs: list[tuple[str, BoolRef]]):
    if len(cexs) < 2:
        return cexs
    whole = Or(*[cex[1] for cex in cexs])
    generalized = []
    subsets = []
    visited = set()
    for expr in cexs:
        cur = get_vals(expr[1])
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
                solver.add(And(gen_inv, Not(whole)))
                if solver.check() == unsat:
                    print(f'generalized: {expr[0]} -> {gen_inv}')
                    generalized.append((expr[0], gen_inv))
                    subsets.append(frozenset(s))
                    flag = True
                    break
            if flag:
                break
        if not flag:
            generalized.append(expr)
            subsets.append(cur)
    return generalized


def make_equation_list(model, vars):
    equations = {}
    for var in vars:
        if not isinstance(var, DatatypeRef):
            equations[var] = var == model[var]
            continue
        assert var.sort().num_constructors() > 0
        if not str(var.sort().constructor(0)).startswith('mk_'):
            equations[var] = var == model[var]
            continue

        attr_num = var.sort().constructor(0).arity()
        for i in range(attr_num):
            attr = var.sort().accessor(0, i)
            equations[attr(var)] = simplify(attr(var) == attr(model[var]))
    return equations


# def generalize(s, model):
#     all_vars = [decl() for decl in model.decls()]
#     filtered_vars = list(filter(lambda variable: '\'' not in str(variable), all_vars))
#     attr_list = make_equation_list(model, filtered_vars)
#     return And(*list(attr_list.values()))
#
#     essential_vars = []
#     for var, equation in attr_list.items():
#         new_solver = Solver()
#         new_solver.add(s.assertions())
#         new_solver.add(Not(equation))
#         if new_solver.check() == unsat:
#             essential_vars.append(var)
#     return And(*[attr_list[var] for var in essential_vars])


visited = {}


def generalize(s, model, prot):
    all_vars = [decl() for decl in model.decls()]
    filtered_vars = list(filter(lambda variable: '\'' not in str(variable), all_vars))
    attr_list = make_equation_list(model, filtered_vars)
    eq_tuple = tuple(attr_list.values())
    len_eqs = len(eq_tuple)

    if len_eqs < 2:
        if eq_tuple in visited:
            assert visited[eq_tuple]
        else:
            visited[eq_tuple] = True
        return And(*eq_tuple)

    for length in range(1, len_eqs):
        subset = combinations(eq_tuple, length)
        for eqs in subset:
            if eqs in visited:
                if visited[eqs]:
                    return None
                continue
            if check_generalized_by_murphi(eqs, prot):
                visited[eqs] = True
                return And(*eqs)
            visited[eqs] = False
    visited[eq_tuple] = True
    return And(*eq_tuple)


def check_generalized_by_murphi(eqs, prot):
    murphi_str = prot + z3_inv_to_murphi(eqs)
    return check_murphi(murphi_str)


def collect_literals(expr, literals):
    # print(expr)
    # print(expr.sort())
    if not is_bool(expr):
        if expr.decl().kind() == Z3_OP_DT_ACCESSOR or expr.decl().kind() == Z3_OP_UNINTERPRETED:
            literals.add(expr)
    elif expr.num_args() == 0:
        if expr.decl().kind() == Z3_OP_UNINTERPRETED:
            literals.add(expr)
    else:
        for child in expr.children():
            collect_literals(child, literals)


def generate_obligation(rule, cex_pair, var2prime, prime2var):
    (rule_name, cond, cmds, others) = rule
    (cex_name, cex, cex_prime) = cex_pair
    inv = Not(cex)
    inv_prime = Not(cex_prime)
    r = And(cond, cmds)

    inv_literals = set()
    collect_literals(Or(inv, inv_prime), inv_literals)
    rule_literals = set()
    collect_literals(r, rule_literals)

    extra_literals = inv_literals - rule_literals
    others_literals = set()
    for var in extra_literals:
        if var in var2prime:
            if var2prime[var] not in rule_literals:
                others_literals.add(var2prime[var] == var)
        else:
            others_literals.add(var == prime2var[var])

    if extra_literals == inv_literals:
        return None
    return simplify(And(r, And(*others_literals), Not(inv_prime), inv))


class InductiveAuxSolver(ProtSolver):
    def __init__(self, literals, primes, init, trans, post, post_prime, full_vars, var_cons, prot, debug):
        super().__init__(literals, primes, init, trans, post, post_prime, full_vars, var_cons, prot, debug)
        self.aux_cex = []

    def get_constraints(self, expr):
        if len(self.var_cons) == 0:
            return True
        used_vars = set()
        collect_literals(expr, used_vars)
        if len(used_vars) == 0:
            return True
        constraints = []
        for var in used_vars:
            if var in self.var_cons:
                lower_bound = self.var_cons[var].start
                upper_bound = self.var_cons[var].stop
                constraints.append(And(var >= lower_bound, var <= upper_bound-1))
        return And(*constraints)

    def enforce_obligation(self):
        murphi_check_init()
        cex_queue = Queue()
        for p in self.property:
            cex_queue.put((p[0], Not(p[1]), Not(p[2])))
            # logging.debug(f'queue.put {p[0]}: {Not(p[1])}')
        while not cex_queue.empty():
            # cex_pair = (name, cex, cex')
            cex_pair = cex_queue.get()
            for rule in self.trans:
                o = generate_obligation(rule, cex_pair, self.full_var2prime, self.full_prime2var)
                if o is None:
                    continue
                # logging.debug(f'currently checking {cex_pair[0]}: {simplify(Not(cex_pair[1]))}')
                # logging.debug(f'for rule {rule[0]}: cond = {rule[1]}, cmds = {rule[2]}')
                # logging.debug(f'generating obligation: {o}')

                while True:
                    constraints = self.get_constraints(o)
                    o = And(o, constraints)
                    # logging.debug(f'constraints: {constraints}')
                    # logging.debug(f'obligation with constraints: {o}')
                    s = Solver()
                    s.add(o)
                    if self.aux_cex:
                        cexs = [Not(cex[1]) for cex in self.aux_cex]
                        s.add(And(*cexs))
                    if s.check() == unsat:
                        break
                    else:
                        model = s.model()
                        g = generalize(s, model, self.prot_str)
                        if g is None:
                            break
                        # logging.info(f'getting cex: {model}')
                        # logging.info(f'generalized: {g}')
                        obligation = simplify(g)
                        if not obligation_in_list(obligation, self.aux_cex):
                            cex_name = f'{rule[0]} - {cex_pair[0]}'
                            self.aux_cex.append((cex_name, obligation))
                            next_state = substitute(obligation, self.prime_tuples)
                            cex_queue.put((cex_name, obligation, next_state))
                            logging.debug(f'appending cex {cex_name}')
                            logging.debug(f'aux_cex: {self.aux_cex}')

    def run(self):
        self.enforce_obligation()
        # invs = '\n'.join([f'{name}: \n{Not(expr)}' for (name, expr) in self.aux_cex])
        # logging.info('Invariants before generalization:')
        # logging.info(f'{invs}')
        # self.aux_cex = generalize_list(self.aux_cex)
        invs = '\n'.join([f'{name}: \n{Not(expr)}' for (name, expr) in self.aux_cex])
        print('Inductive Invariant:')
        print(f'{invs}')
        logging.info('Inductive Invariant:')
        logging.info(f'{invs}')
