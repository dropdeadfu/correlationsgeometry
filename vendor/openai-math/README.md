# Files copied from openai/math

This folder holds 26 Lean files copied from the public repository
<https://github.com/openai/math>, commit `4eaee87548250b2682affda7d05d947c05554bae`,
directory `lean/OAI/`. They are licensed under the Apache License 2.0; the licence text is in
`LICENSE` next to this file. The upstream files carry no copyright header and the upstream
repository has no `NOTICE` file.

They are here as a starting point for the quantum half of Proposition 4.2 of the paper (see
`PLAN.md` in the project root). Nothing in `CorrelationsGeometry/` imports them yet.

## What is in the files

A bosonic Fock space for `n` modes, quantum states on it, von Neumann entropy, thermal states, a
partial trace, the beam-splitter unitary, and the proof of the entropy photon-number inequality.
The declarations this project plans to use:

| Lean name (namespace `OAI.EntropyPhotonNumber` unless noted) | Meaning |
|---|---|
| `Fock n` | `ℓ²(ℕⁿ, ℂ)`, the Fock space of `n` modes |
| `State n` | positive operator on `Fock n` with trace one |
| `entropy ρ` | `−Tr ρ log ρ` |
| `entropy_nonneg` | `0 ≤ entropy ρ` |
| `g t` | `(t + 1) log (t + 1) − t log t` |
| `thermalState n r` | thermal state with mean occupation `r` in every mode |
| `thermalState_entropy` | `entropy (thermalState n r) = n · g r` |
| `diagonalState_entropy` | entropy of a state diagonal in the number basis |
| `OAI.TensorLp.partialTrace` | partial trace over the second factor of `ℓ²(A × B)` |
| `beamUnitary η` | beam-splitter unitary on two copies of `Fock n` |
| `beamOutput η ρA ρB` | state of one output port after mixing `ρA` and `ρB` |
| `entropy_photon_number_inequality` | the main theorem of the upstream development |

The paper's single-mode entropy `f(ν)` is `g (ν − 1/2)`.

## Which files

The 20 files of `OAI/InformationTheory/PhotonNumber/` and the 6 files they import, directly or
indirectly:

```
OAI/Analysis/DiagonalForms.lean
OAI/Analysis/Herglotz.lean
OAI/Analysis/QuantumTrace/Basic.lean
OAI/Analysis/TensorLp.lean
OAI/MathematicalPhysics/Fock/Beam.lean
OAI/MathematicalPhysics/Fock/Operators.lean
```

All 26 depend only on Mathlib. The folder layout and module names are the upstream ones.

## Changes made to the files

Upstream targets Lean 4.34.1; this project uses Lean 4.36.0-rc2 with Mathlib `v4.36.0-rc2`.
24 of the 26 files are byte-for-byte identical to upstream (checked against the Git blob hashes of
the commit above). Two files were changed, and each carries a notice in its first lines:

| File | Change |
|---|---|
| `OAI/InformationTheory/PhotonNumber/Entropy.lean` | In `number_tail_mass_le`, the two arguments of `Summable.tsum_subtype_le` that upstream left as `_ _` are written out. In `entropy_tail_le_modulus`, two `· rfl` lines are removed because `convert` no longer produces those goals. |
| `OAI/InformationTheory/PhotonNumber/Functions.lean` | In `bParameter_nonneg`, one `show` line is added before `apply Function.invFunOn_mem`. |

Each changed place is marked with a comment containing `compatibility patch`. No statement of any
definition or theorem was changed.

`Audit.lean` in this folder is not from upstream. It was written for this project.

## Building and checking

The files are a separate library, `OAI`, which is not part of the default build.

```
lake build OAI
lake env lean vendor/openai-math/Audit.lean
```

The first command compiles the 26 files. The second prints the statements listed above and the
axioms behind `thermalState_entropy`, `entropy_nonneg` and `entropy_photon_number_inequality`.

The library is compiled with the upstream option `autoImplicit = false` only. The options of the
`CorrelationsGeometry` library (Mathlib linters, `maxSynthPendingDepth = 3`) are not applied to it;
see `lakefile.toml`.

## Caveats

* The upstream README says the repository was produced by an OpenAI model, that formalised results
  "may have issues", and that three results were withdrawn. Lean has checked the proofs in these 26
  files, so the theorems follow from the definitions. Whether the definitions say what one wants
  (for example that `State` and `entropy` are the right notions) is for the reader to judge.
* The annihilation and creation operators in `OAI/MathematicalPhysics/Fock/Operators.lean` are
  bounded, regularised versions (`sandwich`, `lowering`, `raising`), not the unbounded operators.
  Position and momentum operators are not defined.
* There are no Gaussian states, no squeezing, no covariance matrices and no mutual information.
