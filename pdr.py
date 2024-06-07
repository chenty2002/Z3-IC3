#!/usr/bin/python

# Implementation of the PDR algorithm by Peter Den Hartog. Apr 28, 2016

from z3 import Solver, substitute, simplify, And, Not, sat, unsat


# a cube is a conjunction of literals associated with a given frame (t) in the trace
class Cube(object):
    # make a tcube object associated with frame t. If t is none, have it be frameless
    def __init__(self, model, lMap, t=None):
        self.frame_index = t
        # filter out primed variables when creating cube
        self.cubeLiterals = [lMap[str(l)] == model[l] for l in model if '\'' not in str(l)]

    # return the conjunction of all literals in this cube
    def cube(self):
        return And(*self.cubeLiterals)

    def __repr__(self):
        return str(self.frame_index) + ": " + str(sorted(self.cubeLiterals, key=str))


class PDR(object):
    def __init__(self, literals, primes, init, trans, post):
        self.init = init
        self.trans = trans
        self.literals = literals
        self.lMap = {str(l): l for l in self.literals}
        self.property = post
        self.frames = []
        self.primeMap = [(from_, to_) for from_, to_ in zip(literals, primes)]

    def run(self):
        self.frames = list()
        self.frames.append(self.init)

        while True:
            c = self.getBadCube()
            if c is not None:
                # print "Found bad cube:", c
                # we have a bad cube, which we will try to block 
                # if the cube is blocked from the previous frame 
                # we can block it from all previous frames
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
                    print("Found inductive invariant:", simplify(inv))
                    return True
                print("Did not find invariant, adding frame", len(self.frames))
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
                for i in range(1, s.frame_index + 1):
                    # if not self.isBlocked(s, i):
                    self.frames[i] = simplify(And(self.frames[i], Not(s.cube())))
            else:
                # Cube 's' was not blocked by image of predecessor
                # it will stay on the stack, and z (the model which allowed transition to s) will be added on top
                bad_cube.append(z)
        return None

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