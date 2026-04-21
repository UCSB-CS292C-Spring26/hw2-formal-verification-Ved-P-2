"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1–R5.

    Implement this. You need to think about:
    1. How to express "viewers may ONLY do X" (everything else is denied).
    2. How R4 overrides R3 for admins.
    3. Whether you need a closed-world assumption (if not explicitly
       allowed, it's denied).
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = [
        ForAll([u, t, r], Implies( # default deny
            Or(role(u) < ADMIN, role(u) > VIEWER),
            Not(allowed(u, t, r))
        )),
        ForAll([u, t, r], Implies( # R1
            role(u) == VIEWER,
            allowed(u, t, r) == And(t == FILE_READ, Not(is_sensitive(r)))
        )),
        ForAll([u, t, r], Implies( # R2
            role(u) == DEVELOPER,
            allowed(u, t, r) == Or(
                t == FILE_READ,
                And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r)))
            )
        )),
        ForAll([u, t, r], Implies( # R3
            role(u) == ADMIN,
            allowed(u, t, r) == Not(Or(
                And(t == SHELL_EXEC, is_sensitive(r)), # R4
                And(t == NETWORK_FETCH, Not(in_sandbox(r)))  # R5
            ))
        ))
    ]

    # Encode R1–R5
    # Hint: Start with a default-deny rule, then add exceptions.

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.

    Implement each query.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    query(
        "Can a developer write to a sensitive file they don't own, in the sandbox?",
        policy,
        And(
            role(u) == DEVELOPER,
            allowed(u, FILE_WRITE, r),
            is_sensitive(r),
            owner(r) != u,
            in_sandbox(r)
        )
    )
    # Q1 is SAT. R2 allows a developer to access a sandboxed file regardless of ownership or sensitivity.

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    query(
        "Can an admin network_fetch a resource outside the sandbox?",
        policy,
        And(
            role(u) == ADMIN,
            allowed(u, NETWORK_FETCH, r),
            Not(in_sandbox(r))
        )
    )
    # Q2 is UNSAT. R5 prevents a network fetch on an unsandboxed resource, regardless of admin privileges.

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    query(
        "Is there ANY role that can shell_exec on a sensitive resource?",
        policy,
        And(
            allowed(u, SHELL_EXEC, r),
            is_sensitive(r)
        )
    )
    # Q3 is UNSAT. R4 prevents a shell exec on a sensitive resource, regardless of the user.

    # Q4: [EXPLAIN] in a comment Remove R4 — what dangerous action becomes possible?
    # Create a modified policy without R4, demonstrate the new capability.

    t = Int('t')
    modified_policy = policy.copy()
    modified_policy[3] = ForAll([u, t, r], Implies( # R3
        role(u) == ADMIN,
        allowed(u, t, r) == Not(
            And(t == NETWORK_FETCH, Not(in_sandbox(r)))  # R5
        )
    ))

    query(
        "Remove R4 — what dangerous action becomes possible?",
        modified_policy,
        And(
            allowed(u, SHELL_EXEC, r),
            is_sensitive(r)
        )
    )

    # Response to EXPLAIN prompt:
    # After R4 is removed as requested in Q4, admins can perform
    # a shell exec on a sensitive resource. This is dangerous,
    # because admins can now execute shells on files that may
    # contain sensitive data such as passwords, private keys, etc.
    # A malicious or negligent admin can hypothetically leak these
    # to the external world or use these credentials to perform
    # actions that should not be allowed.


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """
    1. Add rule R6 to the policy.
    2. Model a 2-step trace:
       - Step 1: developer calls shell_exec on resource r1
         (r1 is non-sensitive and in sandbox — allowed by R6)
         Side-effect: this command changes resource r2 from sensitive to
         non-sensitive (e.g., modifying an access-control config)
       - Step 2: developer calls shell_exec on resource r2
         (r2 is NOW non-sensitive — was it allowed before? is it allowed now?)
    3. The twist: r2's sensitivity changes BETWEEN steps. Encode this by
       using two copies of is_sensitive (before and after).
    4. Check if the developer can effectively access a previously-sensitive resource.
    5. [EXPLAIN] in a comment: Propose and implement a fix.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    # Your encoding here.
    # Hint: Use is_sensitive_before and is_sensitive_after as two separate
    # functions, or use a time-indexed model.

    def make_policy_version(sensitive):
        u = Const('u', User)
        r = Const('r', Resource)
        t = Int('t')

        constraints = [
            ForAll([u, t, r], Implies( # default deny
                Or(role(u) < ADMIN, role(u) > VIEWER),
                Not(allowed(u, t, r))
            )),
            ForAll([u, t, r], Implies( # R1
                role(u) == VIEWER,
                allowed(u, t, r) == And(t == FILE_READ, Not(sensitive(r)))
            )),
            ForAll([u, t, r], Implies( # R2
                role(u) == DEVELOPER,
                allowed(u, t, r) == Or(
                    t == FILE_READ,
                    And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
                    And(t == SHELL_EXEC, Not(sensitive(r)), in_sandbox(r))
                )
            )),
            ForAll([u, t, r], Implies( # R3
                role(u) == ADMIN,
                allowed(u, t, r) == Not(Or(
                    And(t == SHELL_EXEC, sensitive(r)), # R4
                    And(t == NETWORK_FETCH, Not(in_sandbox(r)))  # R5
                ))
            ))
        ]

        return constraints

    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after = Function('is_sensitive_after', Resource, BoolSort())

    policy_before = make_policy_version(is_sensitive_before)
    policy_after = make_policy_version(is_sensitive_after)

    print("  Implement escalation analysis")

    u = Const('u', User)
    r1 = Const('r1', Resource)
    r2 = Const('r2', Resource)

    query(
        "Can r1 be shell_execed such that r2 will no longer be sensitive?",
        policy_before,
        And(
            role(u) == DEVELOPER,
            in_sandbox(r1),
            Not(is_sensitive_before(r1)),
            is_sensitive_before(r2),
            Not(is_sensitive_after(r1)),
            allowed(u, SHELL_EXEC, r1) == Not(is_sensitive_after(r2)), # if r1 can be execed, then r2's sensitivity changes
            Not(is_sensitive_after(r2)) # we want r2 to no longer be sensitive
        )
    )

    query(
        "Now that r2 is not sensitive, can it be shell_execed?",
        policy_after,
        And(
            role(u) == DEVELOPER,
            in_sandbox(r1),
            Not(is_sensitive_before(r1)),
            is_sensitive_before(r2),
            Not(is_sensitive_after(r1)),
            Not(is_sensitive_after(r2)), # r2 is no longer sensitive
            allowed(u, SHELL_EXEC, r2)
        )
    )

    print()

    print("  Implement escalation fix")

    # Response to EXPLAIN prompt:
    # The constraint I want to add is thatevelopers should not be able
    # to perform any action that changes the sensitivity for all files.
    # This can be represented by a universal statement ensuring that
    # the sensitivity before and after are the same for all r.

    r_all = Const('r_all', Resource)

    fix = query(
        "With a new constraint, can r1 be shell_execed?",
        policy_before,
        And(
            role(u) == DEVELOPER,
            in_sandbox(r1),
            Not(is_sensitive_before(r1)),
            is_sensitive_before(r2),
            Not(is_sensitive_after(r1)),
            allowed(u, SHELL_EXEC, r1) == Not(is_sensitive_after(r2)), # if r1 can be execed, then r2's sensitivity changes
            allowed(u, SHELL_EXEC, r1), # we want to see if r1 can be execed
            Implies(role(u) == DEVELOPER, ForAll([r_all], is_sensitive_before(r_all) == is_sensitive_after(r_all))) # New constraint!
        )
    )

    if fix == unsat:
        print("ESCALATION BLOCKED")

    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
