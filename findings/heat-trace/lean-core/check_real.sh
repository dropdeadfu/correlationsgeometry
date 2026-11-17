#!/bin/sh
# Checks lean/CorrelationsToGeometryReal.lean (uses Mathlib). Run from the lean/ directory.
# Needs: Lean 4.29.0 under ../.tools/lean-4.29.0-linux and a Mathlib checkout at tag v4.29.0 under
# ../.tools/mathlib4 with the cache for the imported Mathlib modules unpacked
# (cd ../.tools/mathlib4 && lake exe cache get Mathlib.Analysis.Matrix.Spectrum Mathlib.Analysis.Normed.Algebra.MatrixExponential Mathlib.Analysis.SpecialFunctions.Exponential Mathlib.Topology.Algebra.InfiniteSum.Real Mathlib.Analysis.SpecificLimits.Basic).
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
mkdir -p "$T/leanbuild"
lean --root=. -o "$T/leanbuild/CorrelationsToGeometry.olean" CorrelationsToGeometry.lean
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LEAN_PATH="$LP:$T/leanbuild" lean --root=. CorrelationsToGeometryReal.lean
echo "CorrelationsToGeometryReal.lean: accepted"
