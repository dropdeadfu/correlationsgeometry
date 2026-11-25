#!/bin/sh
# Checks lean/CorrelationsToGeometryReal4.lean against the COMPILED seventh file. Run from the lean/ directory.
# Needs ../.tools/leanbuild/CorrelationsToGeometryReal3.olean built from the current CorrelationsToGeometryReal3.lean:
#   ./check_real3.sh   (checks the seventh file), then
#   LEAN_PATH=... lean --root=. -o ../.tools/leanbuild/CorrelationsToGeometryReal3.olean CorrelationsToGeometryReal3.lean
# The script refuses to run if a compiled module is older than its source.
# Lean may return 0 although it printed errors, so acceptance is judged by the output.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
for f in CorrelationsToGeometryReal CorrelationsToGeometryReal2 CorrelationsToGeometryReal3 CorrelationsToGeometryReal3b; do
  if [ "$T/leanbuild/$f.olean" -ot "$f.lean" ]; then
    echo "compiled $f is older than its source: rebuild it first" >&2; exit 1
  fi
done
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild" lean --root=. CorrelationsToGeometryReal4.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryReal4.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryReal4.lean: accepted"
