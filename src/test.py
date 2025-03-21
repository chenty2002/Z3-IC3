#!/usr/bin/python
from z3 import *

from bfs import BFS
from inductive_aux_inv import InductiveAuxSolver
from pdr import PDR
from dfs import DFS
from bmc import BMC
from murphi import MurphiProtocol, to_murphi
from murphiparser import parse_file


# SAFE
# This test is a simple program that rotates the variables of three booleans
# The post condition is that at least one of them must be true
# which is inductive because one is initialized to true and never negated, only swapped
def Swapper():
    x = Bool('x')
    y = Bool('y')
    z = Bool('z')
    xp = Bool('x\'')
    yp = Bool('y\'')
    zp = Bool('z\'')

    variables = [x, y, z]
    primes = [xp, yp, zp]

    init = And(x, Not(y), Not(z))
    trans = And(xp == y, zp == x, yp == z)
    post = Or(x, y, z)
    return variables, primes, init, trans, post


# UNSAFE
# A boolean bit vector is initialized with size 8
# to TTTTTTTT. One bit can be flipped per frame. 
# The post condition is that at least one bool is True
# which can be violated in 8 frames
def OneAtATime():
    size = 4
    variables = [Bool(str(i)) for i in range(size)]
    primes = [Bool(str(i) + '\'') for i in variables]

    def exclusive(i):
        return And(*[primes[j] == variables[j] for j in range(size) if j != i] + [Not(primes[i] == variables[i])])

    init = And(*[variables[i] for i in range(size - 1)] + [(variables[-1])])
    trans = Or(*[exclusive(i) for i in range(size)])
    post = Or(*variables)

    return variables, primes, init, trans, post


# SAFE
# Similar to OneAtATime
# A boolean bit vector is initialized with size 8
# to TTTTTTTT. One bit can be flipped per frame but 
# now the two neighbors to it's left must also flip for a total of three.
# The post condition is that at least one bool is True
# which cannot be violated with a bit vector of size 8 and three bits flipped per frame
def ThreeAtATimeEven():
    size = 8
    variables = [Bool(str(i)) for i in range(size)]
    primes = [Bool(str(i) + '\'') for i in variables]

    def triple(i):
        return And(*[primes[j] == variables[j] for j in range(size) if (j != i and j != i - 1 and j != i - 2)] +
                    [Not(primes[i] == variables[i]), Not(primes[i - 1] == variables[i - 1]),
                     Not(primes[i - 2] == variables[i - 2])])

    init = And(*[variables[i] for i in range(size - 1)] + [(variables[-1])])
    trans = Or(*[triple(i) for i in range(size)])
    post = Or(*variables)

    return variables, primes, init, trans, post


# UNSAFE
# Three at a time but with an odd length bit vector
# The post condition can now be violated flipping three bits at a time
def ThreeAtATimeOdd():
    size = 9
    variables = [Bool(str(i)) for i in range(size)]
    primes = [Bool(str(i) + '\'') for i in variables]

    def triple(i):
        return And(*[primes[j] == variables[j] for j in range(size) if (j != i and j != i - 1 and j != i - 2)] +
                    [Not(primes[i] == variables[i]), Not(primes[i - 1] == variables[i - 1]),
                     Not(primes[i - 2] == variables[i - 2])])

    init = And(*[variables[i] for i in range(size - 1)] + [(variables[-1])])
    trans = Or(*[triple(i) for i in range(size)])
    post = Or(*variables)

    return variables, primes, init, trans, post


### More involved examples: ###

# UNSAFE
# Initialize a boolean bitfield to [TTTTTTTTTF]
# Each iteration, each boolean takes the AND of the two bits to its left
# (rolling over at the left back to the right)
# (Frame 1 will look like [FFTTTTTTTT])
# The post condition is simply that at least one boolean be true,
# which can take quite a while to fail depending on the width of the bitfield
#
# This one can take quite a while to run
def BooleanShifter():
    len = 10
    variables = [Bool(str(i)) for i in range(len)]
    primes = [Bool(str(i) + '\'') for i in variables]

    # initialize to something like [T T T T T T T T F]
    init = And(*[variables[i] for i in range(len - 1)] + [Not(variables[-1])])
    trans = And(*[primes[i] == And(variables[i - 1], variables[i - 2]) for i in range(len)])
    post = Or(*variables)

    return variables, primes, init, trans, post


# UNSAFE
# Initialize a boolean bitfield [AAAAA BBBBB]
# Each iteration, add the value of BBBBB to AAAAA
# incrementing it
# In this example, BBBBB is 00001 and the post condition is that
# AAAAA is not 11111, which is unsafe after 16 frames
def BooleanIncrementer():
    len = 8
    variables = [Bool(str(i)) for i in range(len)]
    primes = [Bool(str(i) + '\'') for i in variables]
    init = And(*[Not(variables[i]) for i in range(len - 1)] + [variables[-1]])

    def carryout(pos):
        if pos == len // 2:
            return False
        else:
            return Or(And(Xor(variables[pos], variables[pos + len // 2]), carryout(pos + 1)),
                      And(variables[pos], variables[pos + len // 2]))

    trans = And(
        *[primes[i] == Xor(Xor(variables[i], variables[i + len // 2]), carryout(i + 1)) for i in range(len // 2)] +
         [primes[i + len // 2] == variables[i + len // 2] for i in range(len // 2)])
    post = Not(And(*[variables[i] for i in range(len // 2)]))
    return variables, primes, init, trans, post


# SAFE
# Add overflow protection to the previous boolean incrementer
# When the incrementer becomes full, it will not add anymore to it
# There is an overflow bit that gets set if there is any carryover from the MSB
# so the post condition is Not(overflow)
def IncrementerOverflow():
    size = 8
    overflow = Bool('Overflow')
    variables = [Bool(str(i)) for i in range(size)] + [overflow]
    primes = [Bool(str(i) + '\'') for i in variables]
    overflowprime = primes[-1]
    init = And(*[Not(variables[i]) for i in range(size - 1)] + [variables[size - 1], Not(overflow)])

    def carryout(pos):
        if pos == size / 2:
            return False
        else:
            return Or(And(Xor(variables[pos], variables[pos + size // 2]), carryout(pos + 1)),
                      And(variables[pos], variables[pos + size // 2]))

    trans = If(And(*[variables[i] for i in range(size // 2)]),
               And(*[variables[i] == primes[i] for i in range(len(variables))]),
               And(*[primes[i] == Xor(Xor(variables[i], variables[i + size // 2]), carryout(i + 1)) for i in
                     range(size // 2)] +
                    [primes[i + size // 2] == variables[i + size // 2] for i in range(size // 2)] +
                    [overflowprime == carryout(0)])
               )
    post = Not(overflow)
    return variables, primes, init, trans, post


# SAFE
# Using the same boolean incrementer from before
# In this example, BBB is 010 and the post condition is that
# AAA is even, which is safe
def EvenIncrementer():
    len = 6
    variables = [Bool(str(i)) for i in range(len)]
    primes = [Bool(str(i) + '\'') for i in variables]
    init = And(*[Not(variables[i]) for i in range(len - 2)] + [variables[-2], Not(variables[-1])])

    def carryout(pos):
        if pos == len // 2:
            return False
        else:
            return Or(And(Xor(variables[pos], variables[pos + len // 2]), carryout(pos + 1)),
                      And(variables[pos], variables[pos + len // 2]))

    trans = And(
        *[primes[i] == Xor(Xor(variables[i], variables[i + len // 2]), carryout(i + 1)) for i in range(len // 2)] \
         + [primes[i + len // 2] == variables[i + len // 2] for i in range(len // 2)])
    post = Not(variables[len // 2 - 1])
    return variables, primes, init, trans, post


def Mutual():
    n = 2
    states, (T, I, C, E) = EnumSort('State', ['T', 'I', 'C', 'E'])
    procs = Consts(' '.join(['a' + str(i) for i in range(n)]), states)
    procs_ = Consts(' '.join(['a' + str(i) + '\'' for i in range(n)]), states)
    x = Bool('x')
    x_ = Bool('x\'')

    variables = [x] + procs
    primes = [x_] + procs_
    init = And(x, *[proc == I for proc in procs])

    def exclusive(i):
        return And(*[procs_[j] == procs[j] for j in range(n) if j != i])

    # try: a[i] = I -> a[i]' = T
    try_rules = [And(p == I, p_ == T, x_ == x, exclusive(i)) for i, (p, p_) in enumerate(zip(procs, procs_))]

    # crit: (a[i] = T and x = true) -> a[i]' = C and x' = false
    crit_rules = [And(p == T, x, p_ == C, Not(x_), exclusive(i)) for i, (p, p_) in enumerate(zip(procs, procs_))]

    # exit: a[i] = C -> a[i]' = E
    exit_rules = [And(p == C, p_ == E, x_ == x, exclusive(i)) for i, (p, p_) in enumerate(zip(procs, procs_))]

    # idle: a[i] = E -> a[i]' = I and x' = true
    idle_rules = [And(p == E, p_ == I, x_, exclusive(i)) for i, (p, p_) in enumerate(zip(procs, procs_))]

    trans = Or(*(try_rules + crit_rules + exit_rules + idle_rules))

    post = Or(*[And(procs[i] == C, *[Not(procs[j] == C) for j in range(n) if j != i]) for i in range(n)],
              And(*[Not(procs[i] == C) for i in range(n)]))

    return variables, primes, init, trans, post


tests = {'Swapper': Swapper, 'BooleanShifter': BooleanShifter, 'BooleanIncrementer': BooleanIncrementer,
         'IncrementerOverflow': IncrementerOverflow,
         'EvenIncrementer': EvenIncrementer, 'OneAtATime': OneAtATime, 'ThreeAtATimeEven': ThreeAtATimeEven,
         'ThreeAtATimeOdd': ThreeAtATimeOdd,
         'Mutual': Mutual}


def listTests():
    for name in tests:
        print(name)


if __name__ == "__main__":
    import argparse
    import time

    parser = argparse.ArgumentParser(description="Run tests examples on the PDR algorithm")
    parser.add_argument('-ls', action='store_true')
    parser.add_argument('testname', type=str, help='The name of the test/murphi filename to run', default=None, nargs='?')
    args = parser.parse_args()
    if args.ls:
        listTests()
    elif args.testname is not None:
        name = args.testname
        print("=========== Running test", name, "===========")
        if name in tests:
            solver = PDR(*tests[name](), debug=True)
            solver.run()
        else:
            lex_tree = parse_file(name)
            assert isinstance(lex_tree, MurphiProtocol)
            pre_processing = lex_tree.to_z3(name)

            # solver = PDR(*pre_processing, debug=False)
            # t = time.time()
            # solver.run()
            # print(time.time() - t)

            solver = InductiveAuxSolver(*pre_processing, prot=to_murphi(lex_tree), debug=False)
            t = time.time()
            solver.run()
            print(time.time() - t)
            # solver = DFS(*lex_tree.to_z3(name), debug=False)
            # t = time.time()
            # solver.dfs()
            # print(time.time() - t)
            # solver = BFS(*lex_tree.to_z3(name), debug=False)
            # t = time.time()
            # solver.bfs()
            # print(time.time() - t)
    else:
        name = 'Mutual'
        print("=========== Running test", name, "===========")
        solver = PDR(*tests[name]())
        solver.run()
