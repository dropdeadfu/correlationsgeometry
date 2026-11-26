#!/bin/sh
# Checks lean/CorrelationsToGeometryFlatNPointClose.lean against the COMPILED module of
# CorrelationsToGeometryFlatNPointFinal under ../.tools/leanbuild. Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryFlatNPointFinal.olean" -ot CorrelationsToGeometryFlatNPointFinal.lean ]; then
  echo "compiled CorrelationsToGeometryFlatNPointFinal is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryFlatNPointClose.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryFlatNPointClose.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryFlatNPointClose.lean: accepted"
