# Reference copies of Lean files from openai/math

This folder holds 2,672 Lean files copied, **unchanged**, from the public repository
<https://github.com/openai/math>, commit `4eaee87548250b2682affda7d05d947c05554bae`
(2026-10-29), directory `lean/OAI/`. The folder layout and module names are the upstream ones.

## Credit and licence

The files are the work of **OpenAI**. The upstream repository describes its contents as
"mathematical manuscripts and supporting proof artifacts produced by an unnamed internal OpenAI
model". All credit for these files belongs to OpenAI and that repository; nothing in them was
written by this project.

They are licensed under the **Apache License, Version 2.0**. The licence text is in `LICENSE` next
to this file; it is the upstream `LICENSE` file (identical at the repository root and under
`lean/`). The upstream files carry no copyright header, and the upstream repository has no
`NOTICE` file, so there is no further notice to reproduce. No file here was modified.

To cite a result, use the upstream repository: its `CONTENTS.md` maps each manuscript to its
directory under `preprints/`, which holds the manuscript's own BibTeX block.

## Why these files

A reading pass over the Lean files of `openai/math` looked for statements that the paper
"From Correlations to Geometry" could reuse instead of proving again (lattice Gaussian sums and
Poisson summation for flat tori, lattice point counts, concentration inequalities, eigenvalue and
operator-norm bounds, trace and entropy of quantum states, real Riemannian geometry, elementary
Gaussian bounds). The method, its limits and the full list are in
`findings/heat-trace/second-session/openai-math-review/`.

- **253 files** hold at least one of the 398 statements that the pass rated "general and squarely
  on a need" (`shortlist_score3.md` there gives each statement with its wording).
- **2,419 further files** are here only because those 253 import them, directly or indirectly.
  Together the 2,672 files are closed under `import OAI.…`: every such import of a file in this
  folder is in this folder. Apart from that they import Mathlib.

`FILES.tsv` lists every file with the Git blob hash it has upstream, its size, its line count and
the number of rated statements in it (0 = present only as an import).

## What this folder is not

- **Not built here.** The folder is not a Lake library and nothing in `CorrelationsGeometry/`
  imports it. Upstream targets Lean `v4.34.1` (its `lean/lean-toolchain`); this project is on
  another version. Whether a given file compiles here has not been tested.
- **Not checked beyond reading.** The 253 files were scanned as text for `sorry`, `admit`, `axiom`,
  `native_decide` and own `macro`/`elab`/`syntax` declarations (none found); the 2,419 import-only
  files were not scanned. A handful of statements were read at the source; see the README in the
  findings folder for exactly which.
- **Not the files this project builds.** `vendor/openai-math/` holds 26 files of the same upstream
  commit that *are* built (`lake build OAI`), two of them with small changes for this project's
  Lean version. All 26 are also present here, in their unchanged upstream form.

A file that a proof in this repository comes to import should be moved (or copied) into a built
library with its imports, and tested, at that point.

## Checking the copy

`.gitattributes` switches off line-ending conversion for this folder, so a checkout has exactly
the upstream bytes. For any file, `git hash-object <file>` must print the hash in column 2 of
`FILES.tsv`, which is the blob hash of `lean/<path>` at the upstream commit
(`git ls-tree 4eaee87548250b2682affda7d05d947c05554bae lean/<path>` in a clone of upstream).

## Where the rated statements are

Projects (folders two levels below `OAI/`) with the most rated statements:

| Project | Rated statements | Subject of the rated statements |
|---|---|---|
| `Combinatorics/Progressions` | 31 | Gaussian sums over an arbitrary lattice, Poisson summation, dual lattice, fundamental domains |
| `MathematicalPhysics/CriticalSK` | 18 | eigenvalue bounds for symmetric matrices, min-max, sub-Gaussian tails |
| `MathematicalPhysics/PEPSMove` | 18 | partial trace, matrix entropy, strong subadditivity, monotonicity of relative entropy |
| `Geometry/HeilbronnTriangle` | 16 | covolume, successive minima, lattice points in boxes |
| `Analysis/BiholderTransport` | 13 | ordered eigenvalues, spectral continuity, Riemannian geodesics |
| `MathematicalPhysics/PEPSSubvolume` | 12 | the same entropy toolbox, regularised |
| `InformationTheory/AmplitudeDamping` | 11 | entropy of density matrices: concavity, continuity, tensor products |
| `Analysis/QuantumTrace` | 10 | trace and entropy of positive operators on a Hilbert space |

Note on size: the nine rated files of `Combinatorics/Progressions` alone bring in about 540 files,
because that project's files import one another in long chains.
