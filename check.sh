#!/usr/bin/env bash
# HW2 Submission Validator
# Run: bash check.sh

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

errors=0
warnings=0

pass_msg() { echo -e "  ${GREEN}✓${NC} $1"; }
warn_msg() { echo -e "  ${YELLOW}⚠${NC} $1"; warnings=$((warnings + 1)); }
fail_msg() { echo -e "  ${RED}✗${NC} $1"; errors=$((errors + 1)); }

echo ""
echo "═══════════════════════════════════════════"
echo "  CS292C HW2 Submission Checker"
echo "═══════════════════════════════════════════"
echo ""

# Check Z3 is installed
echo "Dependencies"
if python3 -c "from z3 import *" 2>/dev/null; then
    pass_msg "z3-solver is installed"
else
    fail_msg "z3-solver not found — run: pip install z3-solver"
fi
echo ""

# Check Python files exist and have been modified
echo "Code Files"
for f in p1_z3_warmup.py p2_vcgen.py p3_agent_policy.py p4_tool_chain.py p5_bonus.py; do
    if [ -f "$f" ]; then
        todo_count=$(grep -c "# TODO" "$f" 2>/dev/null || echo "0")
        if [ "$todo_count" -gt 0 ]; then
            warn_msg "$f has $todo_count remaining TODOs"
        else
            pass_msg "$f — no remaining TODOs"
        fi
    else
        fail_msg "$f not found"
    fi
done
echo ""

# Check that [EXPLAIN] prompts have been answered
# Look for lines with [EXPLAIN] that are followed by actual content (not just the prompt)
echo "Explanations"
total_explains=0
answered_explains=0
for f in p1_z3_warmup.py p2_vcgen.py p3_agent_policy.py p4_tool_chain.py p5_bonus.py; do
    if [ -f "$f" ]; then
        count=$(grep -c "\[EXPLAIN\]" "$f" 2>/dev/null || echo "0")
        total_explains=$((total_explains + count))
    fi
done
echo "  Found $total_explains [EXPLAIN] prompts across all files."
echo "  Make sure each has a substantive answer in a nearby comment."
echo ""

# Try running each file
echo "Execution Check"
for f in p1_z3_warmup.py p2_vcgen.py p3_agent_policy.py p4_tool_chain.py p5_bonus.py; do
    if [ -f "$f" ]; then
        if python3 "$f" > /dev/null 2>&1; then
            pass_msg "$f runs without errors"
        else
            warn_msg "$f has runtime errors (check your implementation)"
        fi
    fi
done
echo ""

# Summary
echo "═══════════════════════════════════════════"
if [ "$errors" -eq 0 ] && [ "$warnings" -eq 0 ]; then
    echo -e "  ${GREEN}All checks passed!${NC} Ready to submit."
elif [ "$errors" -eq 0 ]; then
    echo -e "  ${YELLOW}$warnings warning(s)${NC}, 0 errors. Review warnings above."
else
    echo -e "  ${RED}$errors error(s)${NC}, $warnings warning(s). Fix errors before submitting."
fi
echo "═══════════════════════════════════════════"
echo ""

exit $errors
