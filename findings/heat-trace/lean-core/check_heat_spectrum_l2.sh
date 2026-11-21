#!/bin/sh
# Checks lean/CorrelationsToGeometryHeatSpectrumL2.lean. Run from the lean/ directory, AFTER
# ./check_heat_operator.sh and ./check_heat_spectrum.sh (which compile the ported files by
# Levent Alpöge to ../.tools/leanbuild/alpoge/ and the fourth and fifth file to
# ../.tools/leanbuild/bridge/). It compiles the sixth file to a module under bridge/ and then
# checks this file. Lean may return 0 although it printed errors: acceptance is judged by the output.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
O="$T/leanbuild/alpoge"; B="$T/leanbuild/bridge"
for f in CorrelationsToGeometrySpectrum CorrelationsToGeometryHeatOperator; do
  if [ ! -f "$B/$f.olean" ] || [ "$B/$f.olean" -ot "$f.lean" ]; then
    echo "module $f under bridge/ is missing or older than its source: run ./check_heat_spectrum.sh first" >&2; exit 1
  fi
done
LOG=$(mktemp)
LEAN_PATH="$LP:$T/leanbuild:$O:$B" lean --root=. -o "$B/CorrelationsToGeometryHeatSpectrum.olean" CorrelationsToGeometryHeatSpectrum.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryHeatSpectrum.lean: NOT accepted" >&2; exit 1; fi
LEAN_PATH="$LP:$T/leanbuild:$O:$B" lean --root=. CorrelationsToGeometryHeatSpectrumL2.lean > "$LOG" 2>&1 || true
cat "$LOG"
if grep -q 'error' "$LOG"; then echo "CorrelationsToGeometryHeatSpectrumL2.lean: NOT accepted" >&2; exit 1; fi
rm -f "$LOG"
echo "CorrelationsToGeometryHeatSpectrumL2.lean: accepted"
