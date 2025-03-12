from solver import *


class DFS(ProtSolver):
    def __init__(self, literals, primes, init, trans, post, post_prime, full_vars, debug):
        super().__init__(literals, primes, init, trans, post, post_prime, full_vars, debug)
        self.reachable = []
        self.init_state = State(self.init, self.literals)
        self.visited = set()

    def traverse(self, cur):
        cur_hash = cur.hash()
        if cur_hash in self.visited:
            return
        self.visited.add(cur_hash)
        self.reachable.append(cur)
        if self.debug:
            print('----')
            print(f'popping state: {cur.cur}')
        for (cond, cmds, others) in self.trans:
            if cur.satisfies(cond):
                next_state = copy.deepcopy(cur)
                next_state.apply(simplify(And(cmds, others)), self.prime_tuples)
                if self.debug:
                    print(f'applying rule: {cond, cmds, others}')
                    print(f'new state: {next_state.cur}')
                self.traverse(next_state)

    def dfs(self):
        self.traverse(self.init_state)
        print(f'\n\n{len(self.reachable)} Reachable states:')
        for state in self.reachable:
            print(state.cur)

    def run(self):
        pass
