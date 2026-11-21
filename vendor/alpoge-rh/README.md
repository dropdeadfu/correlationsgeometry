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
here. They are included, with credit to their author, because a proof in this repository builds on
them (see "Where they are used"); the decision to include them was taken by the repository owner and
the paper's author. The author of
the files has not been asked. **They will be removed on his request.** If the archive is given a
licence, this section will be replaced by its terms.

## Which files

Only files that a proof in this repository imports, together with the archive files they import.
A file that turns out not to be needed is removed again.

| File (path below `lean/src/` in the archive) | Lines | sha256 | Why here |
|---|---|---|---|
| `GroundTheory/AutomorphicForms/HilbertSchmidt.lean` | 248 | `2a23f04fb8fdf12591e7988541e9bdcfeaa80639332e9d416f9b5c90f38d537c` | listed |
| `GroundTheory/AutomorphicForms/TraceClass.lean` | 449 | `48b8330a87e1134a3a058e5b20ea3240d93130c3627383fda5b555e6a87895f5` | listed |

"listed" = imported by the proof named below; "imported" = needed by a listed file. The two
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

## Where they are used

`findings/heat-trace/lean-core/CorrelationsToGeometryHeatOperator.lean` (namespace `HeatTraceOperator`,
Lean `v4.29.0`) imports both files, in the ported form described below, and uses `IsHilbertSchmidt`,
`isHilbertSchmidt_iff`, `IsTraceClass`, `isTraceClass_comp`, `trace` and `IsTraceClass.hasSum_trace`.
It proves that the operator on `L²((ℝ/ℤ)^d)` that is diagonal in the Fourier basis with entries
`exp(-4π² t |n|²)` is trace class for `t > 0`, with trace `∑ₙ exp(-4π² t |n|²)`.

## Build status

The files in this folder are not built themselves; the proof above is checked with
`findings/heat-trace/lean-core/check_heat_operator.sh` against the ports. Measured with the files as
published:

| Toolchain | Result |
|---|---|
| Lean `v4.33.1` with the archive's Mathlib (upstream) | not built here; a public report by a third party says all modules of the archive compile |
| Lean `v4.36.0-rc2`, Mathlib `v4.36.0-rc2` (root project) | `HilbertSchmidt.lean` compiles unchanged; `TraceClass.lean` stops with one error (line 28) |
| Lean `v4.29.0`, Mathlib `v4.29.0` (`findings/heat-trace/lean-core`) | measured on the paper side's build, files as published: `HilbertSchmidt.lean` 2 errors (both "No goals to be solved", lines 203 and 224: a trailing `simp` after `convert`); `TraceClass.lean` 5 errors (instance search for `NonnegSpectrumClass ℝ (H →L[ℂ] H)` runs out of time, lines 47, 50, 53/54, 122), built against a port of the first file |

So no toolchain of this repository builds both files unchanged; the proof above builds on ports.

## Ports

Ports to Lean `v4.29.0` / Mathlib `v4.29.0` are separate files under
`findings/heat-trace/lean-core/ports/alpoge-rh/GroundTheory/AutomorphicForms/`, with a README in
`findings/heat-trace/lean-core/ports/alpoge-rh/`. Each names its original and every change in its
first lines. Compared here with `git diff` against the originals in this folder: apart from that header
comment, the ports differ from the originals only in the lines listed.

| Port | sha256 of the port (as stored in Git) | Changes against the original |
|---|---|---|
| `HilbertSchmidt.lean` | `588392ed930bc1ea0e258c63397db27b4ef390c1ddf57a08787afbcc2638951f` | two tactic calls removed inside proofs: the trailing `; simp` in `IsHilbertSchmidt.hasSum_norm_sq` and one `simp` line in `hasSum_inner_comp_comm` |
| `TraceClass.lean` | `4a5009759fe4096771e85716d070cb513a2d59bcc225fe22dbf6a3379bf00ac2` | a local instance `NonnegSpectrumClass ℝ (H →L[ℂ] H) := inferInstance` with a raised instance-search limit, added before `section Abs`; `set_option backward.isDefEq.respectTransparency false in` before `theorem exists_polar`; in the proof of `exists_polar`, six occurrences of `orthogonalProjectionOnto` renamed to `orthogonalProjection` |

No statement of a theorem or definition is changed by a port.

## Removed again

`GroundTheory/AutomorphicForms/TraceNormComp.lean` (61 lines) was part of the first version of this
folder as a candidate. The planned proof does not import it, so it was removed; it remains in the
history of this repository.

## Changes made to the files

None. All files are byte-for-byte identical to the archive.

A port to another Lean version is never made by editing a file in this folder. It is added as a
separate file that names, in its first lines, the original it comes from and every change.
