#!/bin/sh
# Checks lean/CorrelationsToGeometrySpectrum.lean (imports only Mathlib, tag v4.29.0). Run from lean/.
# Needs Lean 4.29.0 under ../.tools/lean-4.29.0-linux and the Mathlib checkout with its complete cache
# under ../.tools/mathlib4 (the file starts with `import Mathlib`).
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LEAN_PATH="$LP" lean --root=. CorrelationsToGeometrySpectrum.lean > "$T/scratch/spectrum_check.out" 2>&1 || true
if grep -q "error" "$T/scratch/spectrum_check.out"; then cat "$T/scratch/spectrum_check.out"; echo "NOT accepted"; exit 1; fi
echo "CorrelationsToGeometrySpectrum.lean: accepted"
