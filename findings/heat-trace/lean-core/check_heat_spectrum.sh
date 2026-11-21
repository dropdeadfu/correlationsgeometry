#!/bin/sh
# Checks lean/CorrelationsToGeometryHeatSpectrum.lean. Run from the lean/ directory, AFTER
# ./check_heat_operator.sh (which compiles the two ported files by Levent Alpöge to
# ../.tools/leanbuild/alpoge/). It compiles the fourth and the fifth file to modules under
# ../.tools/leanbuild/bridge/ and then checks the sixth file against them.
# Lean may return 0 although it printed errors, so acceptance is judged by the output.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryReal.olean" -ot CorrelationsToGeometryReal.lean ]; then
  echo "compiled second file is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
O="$T/leanbuild/alpoge"; B="$T/leanbuild/bridge"
mkdir -p "$B"
LOG=$(mktemp)
LEAN_PATH="$LP" lean --root=. -o "$B/CorrelationsToGeometrySpectrum.olean" CorrelationsToGeometrySpectrum.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometrySpectrum.lean: NOT accepted" >&2; exit 1; fi
LEAN_PATH="$LP:$T/leanbuild:$O" lean --root=. -o "$B/CorrelationsToGeometryHeatOperator.olean" CorrelationsToGeometryHeatOperator.lean > "$LOG" 2>&1 || true
grep -v 'warning\|^Note\|^$\|^consider\|^  ' "$LOG" || true
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryHeatOperator.lean: NOT accepted" >&2; exit 1; fi
LEAN_PATH="$LP:$T/leanbuild:$O:$B" lean --root=. CorrelationsToGeometryHeatSpectrum.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryHeatSpectrum.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryHeatSpectrum.lean: accepted"
