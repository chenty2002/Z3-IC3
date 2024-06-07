from z3 import Solver, Not, sat, And, substitute, simplify


class BMC(object):
    def __init__(self, literals, primes, init, trans, post):
        self.init = init
        self.trans = trans
        self.literals = literals
        self.lMap = {str(l): l for l in self.literals}
        self.property = post
        self.frames = []
        self.primeMap = [(from_, to_) for from_, to_ in zip(literals, primes)]

    def run(self, k=20):
        state = self.init
        for step in range(k):
            s = Solver()
            s.add(state)
            s.add(Not(self.property))
            if s.check() == sat:
                print("Property violated at step", step)
                return False
            state = simplify(self.next_state(state))
            print("Property holds for", step + 1, "steps")
        return True

    def next_state(self, state):
        s = Solver()
        s.add(state)
        s.add(self.trans)
        if s.check() == sat:
            model = s.model()
            return And(*[lit == model.get_interp(pri) for lit, pri in self.primeMap])
        raise Exception('Trans Error')
