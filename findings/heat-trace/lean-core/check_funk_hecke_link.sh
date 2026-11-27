#!/bin/sh
# Checks lean/CorrelationsToGeometryFunkHeckeLink.lean against the COMPILED modules of the seventh file
# (CorrelationsToGeometryReal3) and of CorrelationsToGeometryFunkHecke under ../.tools/leanbuild. Run from lean/.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LEAN_PATH="$LP:$T/leanbuild" lean --root=. CorrelationsToGeometryFunkHeckeLink.lean > "$T/scratch/fhlink_check.out" 2>&1 || true
if grep -q "error" "$T/scratch/fhlink_check.out"; then cat "$T/scratch/fhlink_check.out"; echo "NOT accepted"; exit 1; fi
echo "CorrelationsToGeometryFunkHeckeLink.lean: accepted"
