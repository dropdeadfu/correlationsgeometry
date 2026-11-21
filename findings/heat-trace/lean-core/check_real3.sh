#!/bin/sh
# Checks lean/CorrelationsToGeometryReal3.lean against the COMPILED third file. Run from the lean/ directory.
# Needs ../.tools/leanbuild/CorrelationsToGeometryReal2.olean built from the current CorrelationsToGeometryReal2.lean:
#   ./check_real2.sh   (checks the third file), then
#   LEAN_PATH=... lean --root=. -o ../.tools/leanbuild/CorrelationsToGeometryReal2.olean CorrelationsToGeometryReal2.lean
# The script refuses to run if a compiled module is older than its source.
# Lean may return 0 although it printed errors, so acceptance is judged by the output.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
for f in CorrelationsToGeometryReal CorrelationsToGeometryReal2; do
  if [ "$T/leanbuild/$f.olean" -ot "$f.lean" ]; then
    echo "compiled $f is older than its source: rebuild it first" >&2; exit 1
  fi
done
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" lean --root=. CorrelationsToGeometryReal3.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryReal3.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryReal3.lean: accepted"
