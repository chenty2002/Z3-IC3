from solver import *


class BFS(ProtSolver):
    def __init__(self, literals, primes, init, trans, post, post_prime, debug):
        super().__init__(literals, primes, init, trans, post, post_prime, debug)
        self.reachable = []
        self.init_state = State(self.init, self.literals)
        self.visited = set()

    def bfs(self):
        state_queue = Queue()
        state_queue.put(self.init_state)
        self.visited.add(self.init_state.hash())
        self.reachable.append(self.init_state)
        while not state_queue.empty():
            cur_state = state_queue.get()
            if self.debug:
                print('----')
                print(f'popping state: {cur_state.cur}')
            for (cond, cmds, others) in self.trans:
                if cur_state.satisfies(cond):
                    next_state = copy.deepcopy(cur_state)
                    next_state.apply(simplify(And(cmds, others)), self.primeMap)
                    if self.debug:
                        print(f'applying rule: {cond, cmds, others}')
                        print(f'new state: {next_state.cur}')
                    if next_state.hash() not in self.visited:
                        state_queue.put(next_state)
                        self.visited.add(next_state.hash())
                        self.reachable.append(next_state)

        print(f'\n\n{len(self.reachable)} Reachable states:')
        for state in self.reachable:
            print(state.cur)

    def run(self):
        pass
