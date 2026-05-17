#!/usr/bin/env bash
# check_no_admitted.sh
# Enforces the no-Admitted discipline.
# Exits with code 1 if any forbidden proof terms are found.

set -e

COQDIR="coq"
ERRORS=0

echo "=== Checking for Admitted proofs ==="
if grep -rn "Admitted\b" "$COQDIR/"; then
  echo "ERROR: Found 'Admitted' in Coq files."
  ERRORS=$((ERRORS + 1))
fi

if grep -rn "\badmit\b" "$COQDIR/"; then
  echo "ERROR: Found 'admit' tactic in Coq files."
  ERRORS=$((ERRORS + 1))
fi

if grep -rn "\bConjecture\b" "$COQDIR/"; then
  echo "WARNING: Found 'Conjecture' in Coq files (see ASSUMPTIONS.md for justification)."
fi

echo ""
echo "=== Checking for Axioms and Parameters ==="
echo "(These are permitted only for abstract interfaces; see ASSUMPTIONS.md)"
grep -rn "\bAxiom\b\|\bParameter\b" "$COQDIR/" || true

echo ""
if [ $ERRORS -eq 0 ]; then
  echo "PASS: No forbidden admitted proofs found."
  exit 0
else
  echo "FAIL: $ERRORS error(s) found. See above."
  exit 1
fi
