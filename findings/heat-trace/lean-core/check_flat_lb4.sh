#!/bin/sh
# Checks lean/CorrelationsToGeometryFlatLB4.lean against the COMPILED module of
# CorrelationsToGeometryFlatLB3 under ../.tools/leanbuild. Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryFlatLB3.olean" -ot CorrelationsToGeometryFlatLB3.lean ]; then
  echo "compiled CorrelationsToGeometryFlatLB3 is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryFlatLB4.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryFlatLB4.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryFlatLB4.lean: accepted"
