#!/bin/sh
# Checks lean/CorrelationsToGeometryVolume.lean against the COMPILED ninth file. Run from lean/.
# Needs ../.tools/leanbuild/CorrelationsToGeometryManifold.olean built from the current source
# (`lean --root=. -o ../.tools/leanbuild/CorrelationsToGeometryManifold.olean CorrelationsToGeometryManifold.lean`).
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryManifold.olean" -ot "CorrelationsToGeometryManifold.lean" ]; then
  echo "compiled CorrelationsToGeometryManifold is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryVolume.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryVolume.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryVolume.lean: accepted"
