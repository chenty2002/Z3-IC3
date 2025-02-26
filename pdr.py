from solver import *


class PDR(ProtSolver):
    def __init__(self, literals, primes, init, trans, post, post_prime, debug):
        super().__init__(literals, primes, init, trans, post, post_prime, debug)
        self.property = simplify(And(*post))
        trans_list = []
        for (cond, cmds, others) in trans:
            trans_list.append(And(cond, cmds, others))
        self.trans = simplify(Or(*trans_list))

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
