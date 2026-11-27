#!/bin/sh
# Checks lean/CorrelationsToGeometryFunkHeckeSample.lean against the COMPILED module of
# CorrelationsToGeometryFunkHecke under ../.tools/leanbuild. Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryFunkHecke.olean" -ot CorrelationsToGeometryFunkHecke.lean ]; then
  echo "compiled CorrelationsToGeometryFunkHecke is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryFunkHeckeSample.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryFunkHeckeSample.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryFunkHeckeSample.lean: accepted"
