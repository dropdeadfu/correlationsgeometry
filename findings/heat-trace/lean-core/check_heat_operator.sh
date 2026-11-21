#!/bin/sh
# Checks lean/CorrelationsToGeometryHeatOperator.lean. Run from the lean/ directory.
# It compiles the two ported files under ports/alpoge-rh/ (by Levent Alpöge, see the README there)
# to ../.tools/leanbuild/alpoge/ and then checks the file against them and against the COMPILED
# second file (../.tools/leanbuild/CorrelationsToGeometryReal.olean, see check_real2.sh).
# Lean may return 0 although it printed errors, so acceptance is judged by the output.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryReal.olean" -ot CorrelationsToGeometryReal.lean ]; then
  echo "compiled second file is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
O="$T/leanbuild/alpoge"; M=GroundTheory/AutomorphicForms
mkdir -p "$O/$M"
LOG=$(mktemp)
for f in HilbertSchmidt TraceClass; do
  (cd ports/alpoge-rh && LEAN_PATH="$LP:$O" lean --root=. -o "$O/$M/$f.olean" "$M/$f.lean") > "$LOG" 2>&1 || true
  cat "$LOG"
  if grep -q 'error' "$LOG"; then echo "$f.lean (port): NOT accepted" >&2; exit 1; fi
done
LEAN_PATH="$LP:$T/leanbuild:$O" lean --root=. CorrelationsToGeometryHeatOperator.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryHeatOperator.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryHeatOperator.lean: accepted"
