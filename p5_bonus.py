"""
CS292C Homework 2 — Problem 5 (Bonus): Verified Skill Composition (10 points)
===============================================================================
Verify that two sequentially composed agent skills maintain a filesystem
invariant, then show how a composition bug breaks the invariant.
"""

from z3 import *


# ============================================================================
# Filesystem Model
#
# We model the filesystem as a Z3 array: Array(Int, Int)
#   - Index = file path ID (integer)
#   - Value = content hash (integer)
#
# Two paths are special:
#   INPUT_FILE = 0   (the file Skill A reads)
#   OUTPUT_FILE = 1  (the file Skill B writes to)
# ============================================================================

INPUT_FILE = 0
OUTPUT_FILE = 1


# ============================================================================
# Part (a): Verify correct composition — 4 pts
#
# Skill A: Reads INPUT_FILE, extracts URLs. Does NOT modify any file.
#   Pre:  true
#   Post: fs_after_A = fs_before_A  (filesystem unchanged)
#
# Skill B: Fetches URLs and writes results to OUTPUT_FILE. Does NOT modify
#          any file other than OUTPUT_FILE.
#   Pre:  true
#   Post: Select(fs_after_B, OUTPUT_FILE) = result_content
#         ∧ ∀p. p ≠ OUTPUT_FILE → Select(fs_after_B, p) = Select(fs_before_B, p)
#
# Composed postcondition:
#   Select(fs_final, INPUT_FILE) = Select(fs_initial, INPUT_FILE)  [input preserved]
#   ∧ Select(fs_final, OUTPUT_FILE) = result_content               [output written]
#   ∧ ∀p. p ≠ OUTPUT_FILE → Select(fs_final, p) = Select(fs_initial, p)
#                                                                  [nothing else changed]
#
# Encode this as a Z3 validity check and verify it.
# ============================================================================

def verify_correct_composition():
    print("=== Part (a): Correct Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    # Skill A postcondition: filesystem unchanged
    skill_A_post = fs_after_A == fs_initial

    # Skill B postcondition: only OUTPUT_FILE changes
    skill_B_post = And(
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Composed postcondition to verify
    composed_post = And(
        # Input file preserved
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        # Output written
        Select(fs_final, OUTPUT_FILE) == result_content,
        # Nothing else changed
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Check that (skill_A_post ∧ skill_B_post) → composed_post is valid.
    # That is, check that the negation is UNSAT.
    s = Solver()
    s.add(skill_A_post)
    s.add(skill_B_post)
    s.add(Not(composed_post))

    # uncomment and check
    result = s.check()

    print("  Implement verification")
    assert(result == unsat)
    print("The result was UNSAT.")
    print("This means that the post conditions of each skill implies the composed postcondition.")
    print()


# ============================================================================
# Part (b): Buggy composition — 3 pts
#
# Bug: Skill B accidentally writes to INPUT_FILE instead of OUTPUT_FILE.
#
# Buggy Skill B postcondition:
#   Select(fs_final, INPUT_FILE) = result_content     ← overwrites input!
#   ∧ ∀p. p ≠ INPUT_FILE → Select(fs_final, p) = Select(fs_after_A, p)
#
# The composed postcondition should FAIL because the input file is modified.
#
# Encode this and show the counterexample.
# ============================================================================

def verify_buggy_composition():
    print("=== Part (b): Buggy Composition ===")

    fs_initial = Array('fs_initial', IntSort(), IntSort())
    fs_after_A = Array('fs_after_A', IntSort(), IntSort())
    fs_final   = Array('fs_final', IntSort(), IntSort())
    result_content = Int('result_content')
    p = Int('p')

    skill_A_post = fs_after_A == fs_initial

    # BUGGY Skill B: writes to INPUT_FILE instead of OUTPUT_FILE
    buggy_B_post = And(
        Select(fs_final, INPUT_FILE) == result_content,  # ← BUG
        ForAll([p], Implies(p != INPUT_FILE,
                            Select(fs_final, p) == Select(fs_after_A, p)))
    )

    # Same composed postcondition as before
    composed_post = And(
        Select(fs_final, INPUT_FILE) == Select(fs_initial, INPUT_FILE),
        Select(fs_final, OUTPUT_FILE) == result_content,
        ForAll([p], Implies(p != OUTPUT_FILE,
                            Select(fs_final, p) == Select(fs_initial, p)))
    )

    # Check that the composed postcondition FAILS.
    # Print the counterexample showing how the input file gets corrupted.
    s = Solver()
    s.add(skill_A_post)
    s.add(buggy_B_post)
    s.add(Not(composed_post))

    result = s.check()

    print("  Implement buggy verification")
    assert(result == sat)
    print("The result was SAT.")
    print("This means that the post conditions of each skill does not imply the composed postcondition.")
    print(s.model())
    print()


# ============================================================================
# Part (c): Real-world connection — 3 pts
#
# [EXPLAIN] in a comment below (3–4 sentences):
# How does this kind of composition bug manifest in actual agent workflows?
# Give a concrete example from your experience with coding agents (Claude Code,
# Cursor, Copilot, etc.) or from what you learned in class. What would a runtime monitor need to check to
# prevent this class of bugs?

# Write your explanation here as a comment.

# Response to EXPLAIN prompt:
# Imagine if we were using skills in a codebase, where one skill scans for security
# vulnerabilities (maybe leaked private URLs) while the second skill constructs a
# report file based on the findings of the first skill. Usually, such skills will
# have an explicit filename that is desired for the report, but perhaps it does not
# specify what should be done if a file with that name already exists. If so, there
# is a chance that the skill overwrites a file without realizing that anything
# undesirable has happened, but from a global perspective, our desired postcondition
# has been violated. To mitigate this, a runtime monitor would need to be invoked
# at every file_write and ensure that the path being written to is in that
# particular skill's declared set of permitted paths, which in this example would be
# that any code file is not overwritten by the report generating skill.
# ============================================================================


# ============================================================================
if __name__ == "__main__":
    verify_correct_composition()
    verify_buggy_composition()
