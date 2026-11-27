#!/bin/sh
# Checks lean/CorrelationsToGeometrySqrtSeries.lean (Mathlib only). Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometrySqrtSeries.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometrySqrtSeries.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometrySqrtSeries.lean: accepted"
