# Files copied from the Lean archive of Levent Alpöge

This folder holds Lean files written by **Levent Alpöge**. They are copied, unchanged, from the Lean 4
archive that he published on 2026-11-20 together with his note
<https://alpo.ge/remark.pdf>. All credit for these files belongs to him.

- **Source:** `https://alpo.ge/lean.tar.gz.part01` … `part14`, joined to `lean.tar.gz`
  (239,275,554 bytes).
- **sha256 of the joined archive:** `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`
- **Location in the archive:** below `lean/src/`; the folder layout and module names here are the
  archive's.
- **Upstream toolchain:** Lean `v4.33.1`, Mathlib revision
  `0df444a360eaa60ab8c11dca51a86af692955474` (from the archive's `lean-toolchain` and `lakefile.toml`).

## Licence

**The archive contains no licence file, and its files carry no licence or copyright header.** These
files are therefore not covered by this repository's licence, and no right to reuse them is granted
here. They are included, with credit to their author, because proofs in this repository are meant to
build on them (as of this commit no proof imports them yet; see "Which files"); the decision to include them was taken by the repository owner and the paper's author. The author of
the files has not been asked. **They will be removed on his request.** If the archive is given a
licence, this section will be replaced by its terms.

## Which files

Only files that a proof in this repository imports or is planned to import, together with the archive
files they import. **State now: candidates. No proof in this repository imports these files yet.**
A file that turns out not to be needed is removed again.

| File (path below `lean/src/` in the archive) | Lines | sha256 | Why here |
|---|---|---|---|
| `GroundTheory/AutomorphicForms/HilbertSchmidt.lean` | 248 | `2a23f04fb8fdf12591e7988541e9bdcfeaa80639332e9d416f9b5c90f38d537c` | listed |
| `GroundTheory/AutomorphicForms/TraceClass.lean` | 449 | `48b8330a87e1134a3a058e5b20ea3240d93130c3627383fda5b555e6a87895f5` | listed |
| `GroundTheory/AutomorphicForms/TraceNormComp.lean` | 61 | `7b4e198636be553d5d1fc17bfdced1a44e18e3c0c44ea7c2bc2f33158c829f1b` | listed |

"listed" = chosen for the planned use below; "imported" = needed by a listed file. The three
files import only Mathlib and each other. The `.gitattributes` next to this file switches off
line-ending conversion, so a checkout has exactly the bytes of the archive and the hashes above can be
checked with `sha256sum`.

## What is in the files

Hilbert–Schmidt and trace-class operators on a Hilbert space (namespace `GroundTheory.Automorphic`):

| Lean name | Meaning |
|---|---|
| `hsNormSq T`, `hsNormSq_eq_tsum` | squared Hilbert–Schmidt norm `∑ ‖T bᵢ‖²`, the same for every Hilbert basis |
| `IsHilbertSchmidt T`, `hsNorm T`, `norm_le_hsNorm` | Hilbert–Schmidt operators; operator norm ≤ Hilbert–Schmidt norm |
| `traceNorm T`, `IsTraceClass T` | trace norm (through `CFC.abs`) and trace-class operators |
| `isTraceClass_comp` | the composition of two Hilbert–Schmidt operators is trace class |
| `trace T`, `IsTraceClass.hasSum_trace` | the trace, equal to `∑ ⟪bᵢ, T bᵢ⟫` for every Hilbert basis |
| `trace_comp_comm` | `trace (C ∘ T) = trace (T ∘ C)` for trace-class `T` |
| `traceNorm_comp_le` | trace norm of `A ∘ B` ≤ `hsNorm A * hsNorm B` |

Planned use: the trace of the heat semigroup on the flat torus as an operator statement, through
the eigenbasis (`findings/heat-trace/`).

## Build status

The files are **not part of any build target of this repository yet**. Measured with the files as
published:

| Toolchain | Result |
|---|---|
| Lean `v4.33.1` with the archive's Mathlib (upstream) | not built here; a public report by a third party says all modules of the archive compile |
| Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2` (root project) | `HilbertSchmidt.lean` compiles unchanged; `TraceClass.lean` stops with one error (line 28); `TraceNormComp.lean` imports it and was not reached |
| Lean `v4.29.0`, Mathlib `v4.29.0` (`findings/heat-trace/lean-core`) | not yet measured |

## Changes made to the files

None. All files are byte-for-byte identical to the archive.

A port to another Lean version is never made by editing a file in this folder. It is added as a
separate file that names, in its first lines, the original it comes from and every change.
