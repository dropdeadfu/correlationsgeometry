#!/bin/sh
# Checks lean/CorrelationsToGeometryFunkHeckeSphereLB.lean against the COMPILED module of
# CorrelationsToGeometryFunkHeckeLink (and through it the seventh file) under ../.tools/leanbuild. Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryFunkHeckeLink.olean" -ot CorrelationsToGeometryFunkHeckeLink.lean ]; then
  echo "compiled CorrelationsToGeometryFunkHeckeLink is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryFunkHeckeSphereLB.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryFunkHeckeSphereLB.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryFunkHeckeSphereLB.lean: accepted"
