from z3 import *
from queue import Queue


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


class PDR(object):
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
        self.frames = list()
        self.frames.append(self.init)

        iteration = 1
        while True:
            if self.debug:
                print(f'\n\nIteration {iteration}')
                iteration += 1
            c = self.getBadCube()
            if c is not None:
                # print "Found bad cube:", c
                # we have a bad cube, which we will try to block 
                # if the cube is blocked from the previous frame 
                # we can block it from all previous frames
                if self.debug:
                    print(f"Found bad cube {c}, blocking")
                trace = self.block_cube_recursive(c)
                if trace is not None:
                    print("Found trace ending in bad state:")
                    for f in trace:
                        print(f)
                    return False
            else:  # found no bad cube, add a new state on to R after checking for induction
                # print "Checking for induction"
                inv = self.check_induction()
                if inv is not None:
                    simp = simplify(inv)
                    print("Found inductive invariant:")
                    set_option(max_depth=999999, max_lines=999999, max_args=999999)
                    print(simp)
                    return True
                print(f"Did not find invariant, adding frame {len(self.frames)}: True")
                self.frames.append(True)

    # Check all images in frames to see if one is inductive
    def check_induction(self):
        for frame in self.frames:
            s = Solver()
            s.add(self.trans)
            s.add(frame)
            s.add(Not(substitute(frame, self.primeMap)))
            if s.check() == unsat:
                return frame
        return None

    # loosely based on the recBlockCube method from the berkely paper, without some optimizations
    def block_cube_recursive(self, s0):
        bad_cube = [s0]
        while len(bad_cube) > 0:
            s = bad_cube[-1]
            if s.frame_index == 0:
                # If a bad cube was not blocked all the way down to R[0]
                # we have found a counterexample and may extract the stack trace
                return bad_cube

            # solve if cube s was blocked by the image of the frame before it
            z = self.solveRelative(s)

            if z is None:
                # Cube 's' was blocked by image of predecessor:
                # block cube in all previous frames
                bad_cube.pop()  # remove cube s from bad_cube
                # s_generalized = self.generalize(s)
                for i in range(1, s.frame_index + 1):
                    # if not self.isBlocked(s, i):
                    self.frames[i] = simplify(And(self.frames[i], Not(s.cube())))
                if self.debug:
                    print(f"Blocked cube {s} in all previous frames")
                    print("Frames:")
                    for i, f in enumerate(self.frames):
                        print(f"Frame {i}: {f}")
            else:
                # Cube 's' was not blocked by image of predecessor
                # it will stay on the stack, and z (the model which allowed transition to s) will be added on top
                bad_cube.append(z)
        return None

    # def generalize(self, cube):
    #     literals = cube.cubeLiterals
    #     cube_gen = Cube({}, {})
    #     cube_gen.frame_index = cube.frame_index
    #     cube_gen.cubeLiterals = cube.cubeLiterals
    #     for lit in literals:
    #         # 尝试移除当前字面量
    #         cube.cubeLiterals = cube_gen.cubeLiterals
    #         cube.cubeLiterals.remove(lit)
    #         c = And(*cube.cubeLiterals)
    #         cp = substitute(c, self.primeMap)
    #         s = Solver()
    #         s.add(self.frames[cube.frame_index - 1])
    #         s.add(self.trans)
    #         s.add(cp)
    #         if s.check() != unsat:
    #             # 如果新子句是归纳的，用它来更新当前子句
    #             cube_gen.cubeLiterals = cube.cubeLiterals
    #     return cube_gen
    # def generalize(self, cube):
    #     c = cube.cubeLiterals
    #     res = Cube({}, {})
    #     res.cubeLiterals = cube.cubeLiterals
    #     res.frame_index = cube.frame_index
    #     for i in c:
    #         res.cubeLiterals.remove(i)
    #         if not self.down(res):
    #             res.cubeLiterals.append(i)
    #     return res

    def down(self, cube):
        res = Cube({}, {})
        res.cubeLiterals = cube.cubeLiterals
        res.frame_index = cube.frame_index
        while True:
            s = Solver()
            s.add(self.init)
            s.add(res.cube())
            if s.check() == sat:
                return None
            s = self.solveRelative(res)
            if s is None:
                return res
            res = Or(res, s.cube())

    # for cube, check if cube is blocked by R[t-1] AND trans
    def solveRelative(self, cube):
        cubeprime = substitute(cube.cube(), self.primeMap)
        s = Solver()
        s.add(self.frames[cube.frame_index - 1])
        s.add(self.trans)
        s.add(cubeprime)
        if s.check() != unsat:  # cube was not blocked, return new tcube containing the model
            model = s.model()
            return Cube(model, self.lMap, cube.frame_index - 1)
        return None

    # Using the top item in the trace, find a model of a bad state
    # and return a tcube representing it
    # or none if all bad states are blocked
    def getBadCube(self):
        model = And(Not(self.property), self.frames[-1])
        s = Solver()
        s.add(model)
        if s.check() == sat:
            return Cube(s.model(), self.lMap, len(self.frames) - 1)
        else:
            return None
