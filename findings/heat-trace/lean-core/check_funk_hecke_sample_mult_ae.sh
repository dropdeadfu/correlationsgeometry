#!/bin/sh
# Checks lean/CorrelationsToGeometryFunkHeckeSampleMultAE.lean against the COMPILED module of
# CorrelationsToGeometryFunkHeckeSampleMultProb under ../.tools/leanbuild. Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryFunkHeckeSampleMultProb.olean" -ot CorrelationsToGeometryFunkHeckeSampleMultProb.lean ]; then
  echo "compiled CorrelationsToGeometryFunkHeckeSampleMultProb is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryFunkHeckeSampleMultAE.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryFunkHeckeSampleMultAE.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryFunkHeckeSampleMultAE.lean: accepted"
