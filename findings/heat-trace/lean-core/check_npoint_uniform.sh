#!/bin/sh
# Checks lean/CorrelationsToGeometryNPointUniform.lean against the COMPILED nineteenth file (CorrelationsToGeometryNPointLip). Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
for f in CorrelationsToGeometryManifold CorrelationsToGeometryNPoint CorrelationsToGeometryVolume CorrelationsToGeometryNPointGeom CorrelationsToGeometryNPointSharp CorrelationsToGeometryNPointLip; do
  if [ "$T/leanbuild/$f.olean" -ot "$f.lean" ]; then
    echo "compiled $f is older than its source: rebuild it first" >&2; exit 1
  fi
done
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryNPointUniform.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryNPointUniform.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryNPointUniform.lean: accepted"
