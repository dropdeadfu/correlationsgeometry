#!/bin/sh
# Checks lean/CorrelationsToGeometryReal2.lean against the COMPILED second file. Run from the lean/ directory.
# Needs ../.tools/leanbuild/CorrelationsToGeometryReal.olean built from the current CorrelationsToGeometryReal.lean:
#   ./check_real.sh   (checks the second file), then
#   LEAN_PATH=... lean --root=. -o ../.tools/leanbuild/CorrelationsToGeometryReal.olean CorrelationsToGeometryReal.lean
# The script refuses to run if that compiled module is older than the source of the second file.
set -e
T=$(cd ../.tools && pwd)
PATH="$T/lean-4.29.0-linux/bin:$PATH"; export PATH
if [ "$T/leanbuild/CorrelationsToGeometryReal.olean" -ot CorrelationsToGeometryReal.lean ]; then
  echo "compiled second file is older than its source: rebuild it first" >&2; exit 1
fi
LP=$(cd "$T/mathlib4" && lake env printenv LEAN_PATH)
LEAN_PATH="$LP:$T/leanbuild" lean --root=. CorrelationsToGeometryReal2.lean
echo "CorrelationsToGeometryReal2.lean: accepted"
