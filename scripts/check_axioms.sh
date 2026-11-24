#!/usr/bin/env bash
# Check: there is no `axiom` declaration, and every theorem in scripts/AxiomCheck.lean uses only
# propext, Classical.choice, Quot.sound (no sorryAx).
set -euo pipefail
cd "$(dirname "$0")/.."

if grep -nE '^[[:space:]]*axiom[[:space:]]' ./*.lean; then
  echo "ERROR: a new axiom declaration was found." >&2
  exit 1
fi

lake env lean scripts/AxiomCheck.lean > axioms.txt 2>&1 || { cat axioms.txt; exit 1; }
cat axioms.txt

expected=$(grep -c '^#print axioms' scripts/AxiomCheck.lean)
found=$(tr '\n' ' ' < axioms.txt | grep -o 'depends on axioms: \[[^]]*\]' | wc -l | tr -d ' ')
if [ "$found" != "$expected" ]; then
  echo "ERROR: expected $expected axiom lines, got $found." >&2
  exit 1
fi

bad=$(tr '\n' ' ' < axioms.txt | grep -o 'depends on axioms: \[[^]]*\]' \
  | sed -e 's/depends on axioms: \[//' -e 's/\]//' | tr ',' '\n' | tr -d ' ' \
  | grep -vxE 'propext|Classical\.choice|Quot\.sound' || true)
if [ -n "$bad" ]; then
  echo "ERROR: non-standard axioms: $bad" >&2
  exit 1
fi
echo "OK: $found theorems, using only propext, Classical.choice, Quot.sound."
