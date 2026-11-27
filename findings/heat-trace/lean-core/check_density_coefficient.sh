#!/bin/sh
# Checks lean/CorrelationsToGeometryDensityCoefficient.lean against the COMPILED module of
# CorrelationsToGeometryDensityResponseSum under ../.tools/leanbuild. Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
for M in CorrelationsToGeometryDensityResponseSum; do
  if [ "$T/leanbuild/$M.olean" -ot $M.lean ]; then
    echo "compiled $M is older than its source: rebuild it first" >&2; exit 1
  fi
done
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryDensityCoefficient.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryDensityCoefficient.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryDensityCoefficient.lean: accepted"
