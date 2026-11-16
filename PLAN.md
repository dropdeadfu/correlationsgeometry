# Plan: the quantum half of Proposition 4.2

Status: not started. Written 2026-11-16. Nothing below has been formalised unless it says "done".
The Lean signatures in this file are sketches and have not been compiled.

## Goal

Proposition 4.2 of the paper says that for two bosonic modes in a Gaussian state with
`⟨φ²⟩ = x0`, `⟨π²⟩ = p0`, `⟨φ_A φ_B⟩ = x`, `⟨π_A π_B⟩ = p` and no `φπ` correlations,

    I(A : B) = ε² [f'(ν)/(4ν³) + 1/(4ν²(ν² − 1/4))] − (f'(ν)/ν) x p + O(|(x, p)|⁴).

The proof has two halves.

| Half | Content | State |
|---|---|---|
| Analytic | `2 f(ν) − f(ν₊) − f(ν₋)` has the expansion above | **done**: `two_mode_expansion` in `CorrelationsGeometry/TwoModeExpansion.lean` |
| Quantum | `I(A : B) = 2 f(ν) − f(ν₊) − f(ν₋)` for the Gaussian state | this plan |

The hand-over point between the halves is the definition `twoModeMI x0 p0 x p`. The target of this
plan is one theorem of the form

```lean
theorem mutualInformation_gaussianPair (x0 p0 x p : ℝ) (h : …) :
    mutualInformation (gaussianPair x0 p0 x p h) = twoModeMI x0 p0 x p
```

Once it exists, `two_mode_expansion` applies unchanged and Proposition 4.2 has no unproven input.

## What is already available

In this project:

* `entropyFn`, `twoModeMI`, `two_mode_expansion`, `twoModeMI_neg` (the analytic half).

In `vendor/openai-math` (26 files copied from openai/math, see the README there):

* `Fock n`, `State n`, `entropy`, `entropy_nonneg`;
* `thermalState n r` with `thermalState_entropy : entropy = n · g r` and `thermalState_energy`;
* `diagonalState_entropy`, the entropy of any state that is diagonal in the number basis;
* `OAI.TensorLp.partialTrace`, a partial trace for a family of vectors on `ℓ²(A × B)`;
* `beamUnitary η`, the beam-splitter unitary, and `beamOutput η ρA ρB`, one output port;
* `thermal_beamOutput`: mixing thermal states `a` and `b` gives the thermal state `η a + (1 − η) b`.

The paper's `f(ν)` equals `g (ν − 1/2)`.

Missing everywhere (in these files and in Mathlib): position and momentum operators, covariance
matrices of a state, Gaussian states, squeezing unitaries, characteristic functions, marginals of
a `State`, mutual information, and invariance of `entropy` under a unitary.

## Work packages

Effort figures are rough guesses for focused work and could be off by a factor of two.

### WP1. Symplectic eigenvalues of the covariance matrix

Pure matrix algebra, no quantum mechanics and no dependence on the copied files.

* Write the 4×4 covariance matrix `σ` of the pair in the order `(φ_A, φ_B, π_A, π_B)`. It is
  block diagonal with blocks `X = [[x0, x], [x, x0]]` and `P = [[p0, p], [p, p0]]`.
* Prove that `X P` has eigenvalues `(x0 + x)(p0 + p)` and `(x0 − x)(p0 − p)`, so the symplectic
  eigenvalues are `ν±`, and that each one-mode block has symplectic eigenvalue `ν`.
* Better: give the symplectic matrix `S` (a rotation by 45° followed by two rescalings) with
  `S σ Sᵀ = diag(ν₊, ν₋, ν₊, ν₋)` and prove `S` is symplectic.

Result: `twoModeMI` is, by a checked theorem, "`f` summed over the symplectic eigenvalues of the
marginals minus that of the pair". The remaining input is then the single textbook statement that
the entropy of a Gaussian state is the sum of `f` over its symplectic eigenvalues.

Effort: 2 to 4 days. Risk: low.

### WP2. Thermal states in the paper's variables

* `entropyFn ν = g (ν − 1/2)` (one line) and `entropy (thermalState 1 (ν − 1/2)) = entropyFn ν`.
* A product of thermal states with a different occupation in each mode, and its entropy
  `∑ j, g (r j)`. `thermalState` has the same `r` in every mode, so this generalises
  `thermalState_entropy`; `diagonalState_entropy` reduces it to a sum over the number basis.

Result: the state `τ(ν₊ − 1/2) ⊗ τ(ν₋ − 1/2)` has entropy `f(ν₊) + f(ν₋)`.

Effort: about 1 week. Risk: low to medium (depends on how reusable the proof of
`thermalState_entropy` is).

### WP3. Entropy is invariant under unitaries

`entropy (U ρ U⁻¹) = entropy ρ` for a unitary `U` of `Fock n`. `entropy` is defined as the
number-basis diagonal sum of `cfc negMulLog ρ`, so this needs that the functional calculus commutes
with conjugation by `U` and that the diagonal sum of a positive operator does not depend on the
basis. The copied files have basis-independent trace lemmas for the specific constructions they
need (`TraceEnsemble.trace`) but no general statement.

Effort: 1 to 2 weeks. Risk: medium.

### WP4. Marginals and mutual information

* Identify `Fock (m + n)` with `ℓ²(ℕᵐ × ℕⁿ)` and define `marginalA : State (m + n) → State m`,
  `marginalB`, using `OAI.TensorLp.partialTrace`.
* Define `mutualInformation ρ = entropy (marginalA ρ) + entropy (marginalB ρ) − entropy ρ`.
* Marginals of a product state.

Effort: 1 to 2 weeks. Risk: medium. `partialTrace` takes a family of vectors, not an operator, so
a state first has to be written as such a family (the copied files do this for the beam splitter
in `Continuity.lean`, `mixedVector`).

### WP5. Second moments of a state

Define `⟨a_i† a_j⟩` and `⟨a_i a_j⟩` through number-basis matrix entries, under a finite-energy
hypothesis, and from them the quadrature correlations `⟨φ_i φ_j⟩`, `⟨π_i π_j⟩`, `⟨φ_i π_j⟩`. Compute
them for thermal states.

This is needed only to state that the constructed state has the correlations `x0, p0, x, p`. It is
not needed for the entropy computation itself.

Effort: 1 to 2 weeks. Risk: medium. The ladder operators in the copied files are bounded,
regularised versions, so the unbounded `a`, `a†` cannot be taken from there.

### WP6. Gaussian unitaries

* **6a. Beam splitter.** `beamUnitary (1/2)` exists. Needed: its action on the second moments
  (a rotation by 45°), and the second output port. The copied `BeamLadder` lemmas contain the
  intertwining relations in regularised form. Effort: 2 to 3 weeks.
* **6b. Squeezer.** The one-mode unitary that rescales `φ → e^s φ`, `π → e^{−s} π`. It exists
  neither in the copied files nor in Mathlib. Options:
  1. define it by its number-basis matrix entries and prove unitarity directly;
  2. realise Fock space as `L²(ℝ)` through Hermite functions, where squeezing is a dilation; this
     needs completeness of the Hermite functions, which Mathlib does not have.

  Effort: 1 to 2 months either way. Risk: high.
* **6c. Marginals of the squeezed, mixed state.** One has to show that tracing out one mode of
  `B (σ₊ ⊗ σ₋) B⁻¹` gives a squeezed thermal state with variances `(x0, p0)`. The standard tool is
  the characteristic function `χ_ρ(ξ) = Tr(ρ W(ξ))` with Weyl operators `W(ξ)`: a partial trace
  restricts `χ`, Gaussian unitaries act linearly on `ξ`, and `χ` determines `ρ`. None of this
  exists. The last fact (injectivity of the Fourier–Weyl transform) is the deepest.

  Effort: 2 to 4 months. Risk: high.

## Milestones

**M1. Symplectic spectrum** (WP1). Self-contained, useful on its own, no dependence on WP2–6.

**M2. Isotropic special case** (WP2, WP3, WP4, part of 6a). Take `x0 = p0 = ν` and `x = p`. Then
`ν± = ν ± x` and no squeezing is needed: the state is the 50:50 beam-splitter mix of two thermal
states with occupations `ν ± x − 1/2`. `thermal_beamOutput` already gives one marginal as the
thermal state with occupation `ν − 1/2`. The result would be a fully proven

    I(A : B) = 2 f(ν) − f(ν + x) − f(ν − x)

for an explicit state on Fock space, with leading term `x² / (ν² − 1/4)`.

This case is not the one the paper needs: for the free-field vacuum `x/x0 ≠ p/p0` in general. Its
value is that it exercises every definition (marginals, mutual information, unitary invariance,
thermal entropies) end to end before the expensive part starts.

Effort: 5 to 8 weeks in total.

**M3. General case, explicit state** (WP5, 6b, 6c). The target theorem for the state built as
beam splitter ∘ squeezers applied to two thermal states. Effort: a further 3 to 6 months.

**M4. Any Gaussian state** (optional). The same statement for every state whose characteristic
function is Gaussian with the given covariance. Follows from the characteristic-function machinery
of 6c with little extra work.

## Decisions to take before starting

1. **How far to go.** M1 costs days and turns the quantum input into one textbook sentence. M2
   costs weeks and proves a special case the paper does not use. M3 costs months. A reasonable
   stopping point is M1, with the entropy formula for Gaussian states kept as a stated input, the
   same way the manifold results are treated elsewhere in this project.
2. **Squeezer route** (only for M3): number-basis matrix entries or Hermite functions.
3. **Where the code lives.** Proposed: `CorrelationsGeometry/Gaussian/*.lean`, importing the
   copied `OAI` modules. From the first such import on, `lake build` also compiles the copied files
   it needs (a one-off cost; see `vendor/openai-math/README.md`).

## Out of scope

* Theorem 4.4 (the decay law). It needs the two-point functions of the free-field vacuum, which
  is quantum field theory and has no formal basis in Mathlib or in the copied files.
* Proposition 4.3 (several modes per node). Its upper bound uses analyticity of the entropy in the
  covariance matrix, uniformly on compact sets; this would build on M4.
* Uniformity of the remainder in (4.2) on compact sets of `(x0, p0)`, which Lemma E.3 (c) in
  Appendix E uses. `two_mode_expansion` gives constants for fixed `(x0, p0)` only. This is an
  extension of the analytic half and does not depend on this plan.
