#!/bin/sh
# Checks lean/CorrelationsToGeometryNPoint.lean against the COMPILED ninth and eleventh files. Run from lean/.
# Needs ../.tools/leanbuild/CorrelationsToGeometryManifold.olean and ...Real3b.olean (and its imports),
# each built from the current source with `lean --root=. -o ...`. The script refuses if one is older than its source.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
for f in CorrelationsToGeometryManifold CorrelationsToGeometryReal CorrelationsToGeometryReal2 CorrelationsToGeometryReal3 CorrelationsToGeometryReal3b; do
  if [ "$T/leanbuild/$f.olean" -ot "$f.lean" ]; then
    echo "compiled $f is older than its source: rebuild it first" >&2; exit 1
  fi
done
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" LEAN_NUM_THREADS=2 lean --root=. CorrelationsToGeometryNPoint.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryNPoint.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryNPoint.lean: accepted"
