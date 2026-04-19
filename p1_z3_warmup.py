"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    # Add constraints
    s.add(x + 2 * y == z, z > 10, x > 0, y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # Add the *negation* of the formula and check UNSAT
    s.add(x > 5, x <= 3)

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    # Add the three constraints
    s.add(f(f(x)) == x, f(f(f(x))) == x, f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")

    # Add Z3 derivation steps below (see STEP 2 above).

    print("Step 1: show that f(f(x)) = x implies f(f(f(x))) = f(x)")
    s1 = Solver()
    s1.add(f(f(x)) == x, f(f(f(x))) != f(x))
    if s1.check() == unsat:
        print("Step 1 of derivation is correct.")

    print("Step 2: show that f(f(f(x))) = f(x) and f(f(f(x))) = x implies f(x) = x")
    s1 = Solver()
    s1.add(f(f(f(x))) == f(x), f(f(f(x))) == x, f(x) != x)
    if s1.check() == unsat:
        print("Step 2 of derivation is correct.")

    print("Step 3: show that f(x) = x and f(x) ≠ x is UNSAT")
    s1 = Solver()
    s1.add(f(x) == x, f(x) != x)
    if s1.check() == unsat:
        print("Step 3 of derivation proves the claim is unsatisfiable.")

    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT
    s1 = Solver()
    # Negate axiom 1 and check UNSAT
    s1.add(i == j, Select(Store(a, i, v), j) != v)
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS
    s2 = Solver()
    # Negate axiom 2 and check UNSAT
    s2.add(i != j, Select(Store(a, i, v), j) != Select(a, j))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")
    print()

    # Response to EXPLAIN prompt:
    # The reason these two axioms are fully sufficient to characterize the
    # behavior of Select and Store is that the axioms, which consider the
    # premises i == j and i != j respectively, account for the entire premise
    # space. There is no possible initial condition that cannot be
    # represented by one of these axioms. (We ignore the fact that axioms
    # don't tell us what to do in the case that we have a Select with no
    # Store inside; we can assume this is defined elsewhere.) Another way of
    # thinking about this is, supposed we have a Select() statement with a
    # bunch of Selects and Stores inside of its parameters. By induction, we
    # can simplify the internal Selects into a single value or expression.
    # Then, we know for sure that either axiom 1 or axiom 2 applies. Either
    # way, the number of Store calls goes down by 1. Inductively, we can
    # always apply an axiom and simply the expression until we get to a
    # specific value (the most recent stored at that index) or a single
    # Select call (querying the initial value at that index).


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
