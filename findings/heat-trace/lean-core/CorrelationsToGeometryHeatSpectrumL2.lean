/-
A further Lean file of the project (intended as
`lean/CorrelationsToGeometryHeatSpectrumL2.lean`; it follows the fifth and the sixth file): the point spectrum, the eigenspaces and the
spectrum of the diagonal heat operator of the flat torus as statements about OPERATORS on `L²`.

Own text of this project. It builds on the fifth and the sixth project file
(`CorrelationsToGeometryHeatOperator.lean`, `CorrelationsToGeometryHeatSpectrum.lean`), which import
two ported files of the Lean archive of Levent Alpöge (https://alpo.ge/remark.pdf; ports under
`lean/ports/alpoge-rh/`). No definition or theorem of that archive is used by name in THIS file; the
archive enters only through the imports of the two earlier files. All credit for the archive belongs
to its author.

WHAT IS PROVED.

Part 1 (any complex Hilbert space `H`, Hilbert basis `b`, bounded family `a`, `D = diagOp b a ha`):
* `inner_diagOp`: `⟪b i, D v⟫ = a i * ⟪b i, v⟫`.
* `diagOp_eigen_iff`: `D v = μ • v` iff all coefficients `⟪b i, v⟫` with `a i ≠ μ` vanish.
* `diagOp_eigenvalue_iff`: there is `v ≠ 0` with `D v = μ • v` iff `μ ∈ Set.range a`.
* `diagOp_eigenspace_eq_closure`: the eigenspace of `μ` is the closure of the span of the `b i` with
  `a i = μ`; `diagOp_eigenspace_eq_span`, `diagOp_finrank_eigenspace`: if only finitely many `i` have
  `a i = μ`, it is their span and its dimension is their number.
* `spectrum_diagOp`: `spectrum ℂ D = closure (Set.range a)` (spectrum in the Banach algebra of
  bounded operators `H →L[ℂ] H`).

Part 2 (`heatOp d t` on `L²((ℝ/ℤ)^d)`, `t > 0`; `heatEig t q = exp(-4π² t q)`;
`shell d q = {n ∈ ℤ^d : |n|² = q}` of the fourth file):
* `heatOp_eigenvalue_iff`: `μ` is an eigenvalue iff `μ = heatEig t q` for some `q` with non-empty
  shell.
* `heatOp_eigenspace`, `heatOp_finrank_eigenspace`: the eigenspace of `heatEig t q` is the span of
  the Fourier modes `b_n`, `n ∈ shell d q`; its dimension is `Nat.card (shell d q)`.
* `heatOp_finrank_eq_classical`: this dimension equals the dimension of the space of classical
  (`C²`, periodic) eigenfunctions `Δ f = -4π² q f` of the fourth file (`finrank_eigenspace` there).
* `heatOp_injective`: `0` is not an eigenvalue.
* `spectrum_heatOp`: for `d ≥ 1`, `spectrum ℂ (heatOp d t) = {0} ∪ {exp(-4π² t |n|²) : n ∈ ℤ^d}`.

Part 3 (the semigroup `t ↦ heatOp d t`, `t ≥ 0`):
* `heatOp_joint_eigen_iff`: for `f ≠ 0` and real `lam`: `heatOp d t f = exp(-t·lam) • f` for ALL
  `t ≥ 0` iff `lam = 4π² q` for an integer `q` and `f` lies in the span of the `b_n`, `n ∈ shell d q`.
  `heatOp_joint_eigen_iff_complex`: the same for complex `lam` (so there is no non-real joint
  eigenvalue). `heatOp_single_time_eigen_iff`: one time `t > 0` already suffices.
* `heatOp_generator_on_modes`: for a finite linear combination `f = ∑ c_n b_n` of Fourier modes,
  `(heatOp d t f - f)/t → ∑ c_n λ_n b_n` in `L²` as `t ↓ 0`, with `λ_n = lapEig d n = -4π²|n|²` the
  eigenvalue of the classical Laplacian on the periodic function `e_n` (sixth file,
  `heatOp_mode_laplacian`). `heatSg d t` is `heatOp d (max t 0)`, a total function of `t`.

WHAT IS NOT PROVED AND NOT CLAIMED.
* No unbounded self-adjoint Laplace operator on `L²` occurs as an object, here or in any other
  project file. "`{4π²|n|²}` with multiplicities is the spectrum of the generator" is formalised
  only in the form of Part 3: as a statement about the joint eigenvectors of the semigroup and about
  the derivative at `t = 0` on FINITE linear combinations of Fourier modes. The domain of the
  generator, its closedness or self-adjointness, and the limit `(heatOp d t f - f)/t` for general
  `f` in that domain are not formalised. Strong continuity of `t ↦ heatOp d t f` for all `f ∈ L²` is
  not proved here.
* `heatOp d t` is still BY DEFINITION the diagonal operator in Mathlib's Fourier basis
  `mFourierBasis`. That it is the integral operator with the periodised Gaussian kernel is not a
  statement of any project file.
* `heatOp_finrank_eq_classical` equates two DIMENSIONS (both equal the number of lattice points of
  the shell). It does not construct an isomorphism between the `L²` eigenspace and the space of
  classical eigenfunctions (mode by mode the identification is `fourierBasis_ae`, `desc_e` of the
  sixth file).
* The spectrum is the spectrum in the algebra of bounded operators; no statement about continuous
  versus residual spectrum is made beyond the description of the eigenvalues (`0` is in the spectrum
  for `d ≥ 1` and is not an eigenvalue).
No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib
import GroundTheory.AutomorphicForms.HilbertSchmidt
import GroundTheory.AutomorphicForms.TraceClass
import CorrelationsToGeometryReal
import CorrelationsToGeometryHeatOperator
import CorrelationsToGeometrySpectrum
import CorrelationsToGeometryHeatSpectrum

namespace HeatTraceOperator

open scoped ENNReal InnerProductSpace Topology
open Filter

noncomputable section

/-! ## Part 1: point spectrum, eigenspaces and spectrum of a diagonal operator -/

section DiagSpectrum

variable {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Coordinates of `D v`: `(b.repr (D v)) i = a i * (b.repr v) i`. -/
theorem repr_diagOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (v : H) (i : ι) : b.repr (diagOp b a ha v) i = a i * b.repr v i := by
  rw [diagOp_apply, LinearIsometryEquiv.apply_symm_apply, mulL2_apply]

/-- `⟪b i, D v⟫ = a i * ⟪b i, v⟫`. -/
theorem inner_diagOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (v : H) (i : ι) : ⟪b i, diagOp b a ha v⟫_ℂ = a i * ⟪b i, v⟫_ℂ := by
  rw [← b.repr_apply_apply, ← b.repr_apply_apply, repr_diagOp]

omit [CompleteSpace H] in
/-- A vector all of whose coefficients in a Hilbert basis vanish is zero. -/
theorem eq_zero_of_inner_basis (b : HilbertBasis ι ℂ H) (v : H) (h : ∀ i, ⟪b i, v⟫_ℂ = 0) :
    v = 0 := by
  apply b.repr.injective
  ext i
  rw [b.repr_apply_apply, h i, map_zero]
  rfl

/-- **(1a)** `D v = μ • v` iff all coefficients `⟪b i, v⟫` with `a i ≠ μ` vanish. -/
theorem diagOp_eigen_iff (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (μ : ℂ) (v : H) : diagOp b a ha v = μ • v ↔ ∀ i, a i ≠ μ → ⟪b i, v⟫_ℂ = 0 := by
  constructor
  · intro h i hi
    have h1 := inner_diagOp b a ha v i
    rw [h, inner_smul_right] at h1
    have h2 : (μ - a i) * ⟪b i, v⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3).symm hi
    · exact h3
  · intro h
    have h0 : diagOp b a ha v - μ • v = 0 := by
      refine eq_zero_of_inner_basis b _ fun i => ?_
      rw [inner_sub_right, inner_diagOp, inner_smul_right]
      by_cases hi : a i = μ
      · rw [hi, sub_self]
      · rw [h i hi, mul_zero, mul_zero, sub_self]
    exact sub_eq_zero.1 h0

/-- **(1a')** The eigenvalues of `D` are exactly the entries: there is `v ≠ 0` with `D v = μ • v`
    iff `μ = a i` for some `i`. -/
theorem diagOp_eigenvalue_iff (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (μ : ℂ) :
    (∃ v : H, v ≠ 0 ∧ diagOp b a ha v = μ • v) ↔ μ ∈ Set.range a := by
  constructor
  · rintro ⟨v, hv, h⟩
    by_contra hμ
    refine hv (eq_zero_of_inner_basis b v fun i => ?_)
    exact (diagOp_eigen_iff b a ha μ v).1 h i fun hi => hμ ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    refine ⟨b i, fun h0 => ?_, diagOp_basis b a ha i⟩
    have h1 := b.orthonormal.1 i
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

omit [CompleteSpace H] in
/-- The eigenspace of a bounded operator is closed. -/
theorem isClosed_eigenspace (A : H →L[ℂ] H) (μ : ℂ) :
    IsClosed (Module.End.eigenspace A.toLinearMap μ : Set H) := by
  have e : (Module.End.eigenspace A.toLinearMap μ : Set H) = {v | A v = μ • v} := by
    ext v
    exact Module.End.mem_eigenspace_iff
  rw [e]
  exact isClosed_eq A.continuous (continuous_const_smul μ)

/-- **(1b)** The eigenspace of `D` for `μ` is the closure of the span of the basis vectors `b i`
    with `a i = μ`. -/
theorem diagOp_eigenspace_eq_closure (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (μ : ℂ) :
    Module.End.eigenspace (diagOp b a ha).toLinearMap μ
      = (Submodule.span ℂ (b '' {i | a i = μ})).topologicalClosure := by
  apply le_antisymm
  · intro v hv
    have hv' : diagOp b a ha v = μ • v := Module.End.mem_eigenspace_iff.1 hv
    have hc := (diagOp_eigen_iff b a ha μ v).1 hv'
    have hs := b.hasSum_repr v
    refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hs
      (Eventually.of_forall fun s => ?_)
    refine Submodule.le_topologicalClosure _ (Submodule.sum_mem _ fun i _ => ?_)
    by_cases hi : a i = μ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [b.repr_apply_apply, hc i hi, zero_smul]
      exact Submodule.zero_mem _
  · refine Submodule.topologicalClosure_minimal _ ?_ (isClosed_eigenspace _ μ)
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : a i = μ := hi
    show b i ∈ Module.End.eigenspace (diagOp b a ha).toLinearMap μ
    rw [Module.End.mem_eigenspace_iff]
    show diagOp b a ha (b i) = μ • b i
    rw [diagOp_basis, hi']

/-- **(1b')** If only finitely many `i` have `a i = μ`, the eigenspace is their span. -/
theorem diagOp_eigenspace_eq_span (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (μ : ℂ) (hfin : {i | a i = μ}.Finite) :
    Module.End.eigenspace (diagOp b a ha).toLinearMap μ
      = Submodule.span ℂ (b '' {i | a i = μ}) := by
  rw [diagOp_eigenspace_eq_closure]
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (b '' {i | a i = μ})) :=
    FiniteDimensional.span_of_finite ℂ (hfin.image b)
  exact (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq

/-- **(1b'')** …and its dimension is the number of these `i`. -/
theorem diagOp_finrank_eigenspace (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (μ : ℂ) (hfin : {i | a i = μ}.Finite) :
    Module.finrank ℂ (Module.End.eigenspace (diagOp b a ha).toLinearMap μ)
      = Nat.card {i | a i = μ} := by
  haveI : Fintype {i | a i = μ} := hfin.fintype
  rw [diagOp_eigenspace_eq_span b a ha μ hfin, Set.image_eq_range, Nat.card_eq_fintype_card]
  exact finrank_span_eq_card (b.orthonormal.linearIndependent.comp _ Subtype.val_injective)

/-- `μ·1 - D` is the diagonal operator with entries `μ - a i`. -/
theorem algebraMap_sub_diagOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (μ : ℂ) (hb : ∃ C : ℝ, ∀ i, ‖μ - a i‖ ≤ C) :
    algebraMap ℂ (H →L[ℂ] H) μ - diagOp b a ha = diagOp b (fun i => μ - a i) hb := by
  refine eq_diagOp_of_basis b _ hb _ fun i => ?_
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.algebraMap_apply, diagOp_basis, sub_smul]

/-- **(1c) The spectrum of a diagonal operator** (in the Banach algebra of bounded operators) is the
    closure of the set of its entries. -/
theorem spectrum_diagOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) :
    spectrum ℂ (diagOp b a ha) = closure (Set.range a) := by
  obtain ⟨C, hC⟩ := id ha
  apply Set.Subset.antisymm
  · intro μ hμ
    by_contra hcl
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_compl_iff.2 isClosed_closure) μ hcl
    have hdist : ∀ i, ε ≤ ‖μ - a i‖ := fun i => by
      by_contra hlt
      have hmem : a i ∈ Metric.ball μ ε := by
        rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]
        exact not_le.1 hlt
      exact hball hmem (subset_closure ⟨i, rfl⟩)
    have hne : ∀ i, μ - a i ≠ 0 := fun i h0 => by
      have h1 := hdist i
      rw [h0, norm_zero] at h1
      exact absurd hε (not_lt.2 h1)
    have hb : ∃ C' : ℝ, ∀ i, ‖μ - a i‖ ≤ C' :=
      ⟨‖μ‖ + C, fun i => (norm_sub_le _ _).trans (add_le_add le_rfl (hC i))⟩
    have hinv : ∃ C' : ℝ, ∀ i, ‖(μ - a i)⁻¹‖ ≤ C' := ⟨ε⁻¹, fun i => by
      rw [norm_inv]
      exact inv_anti₀ hε (hdist i)⟩
    have h1 : ∃ C' : ℝ, ∀ i, ‖(μ - a i) * (μ - a i)⁻¹‖ ≤ C' :=
      ⟨1, fun i => by rw [mul_inv_cancel₀ (hne i), norm_one]⟩
    have h2 : ∃ C' : ℝ, ∀ i, ‖(μ - a i)⁻¹ * (μ - a i)‖ ≤ C' :=
      ⟨1, fun i => by rw [inv_mul_cancel₀ (hne i), norm_one]⟩
    have e1 : (diagOp b (fun i => μ - a i) hb) * (diagOp b (fun i => (μ - a i)⁻¹) hinv) = 1 := by
      show (diagOp b (fun i => μ - a i) hb).comp (diagOp b (fun i => (μ - a i)⁻¹) hinv) = 1
      rw [diagOp_comp b _ _ hb hinv h1]
      exact diagOp_one b _ h1 fun i => mul_inv_cancel₀ (hne i)
    have e2 : (diagOp b (fun i => (μ - a i)⁻¹) hinv) * (diagOp b (fun i => μ - a i) hb) = 1 := by
      show (diagOp b (fun i => (μ - a i)⁻¹) hinv).comp (diagOp b (fun i => μ - a i) hb) = 1
      rw [diagOp_comp b _ _ hinv hb h2]
      exact diagOp_one b _ h2 fun i => inv_mul_cancel₀ (hne i)
    have hunit : IsUnit (algebraMap ℂ (H →L[ℂ] H) μ - diagOp b a ha) := by
      rw [algebraMap_sub_diagOp b a ha μ hb]
      exact ⟨⟨_, _, e1, e2⟩, rfl⟩
    exact spectrum.notMem_iff.2 hunit hμ
  · refine closure_minimal ?_ (spectrum.isClosed _)
    rintro _ ⟨i, rfl⟩
    by_contra hnot
    obtain ⟨u, hu⟩ := spectrum.notMem_iff.1 hnot
    have h0 : (u : H →L[ℂ] H) (b i) = 0 := by
      rw [hu, ContinuousLinearMap.sub_apply, ContinuousLinearMap.algebraMap_apply, diagOp_basis,
        sub_self]
    have h1 : ((↑u⁻¹ : H →L[ℂ] H) * (u : H →L[ℂ] H)) (b i) = b i := by
      rw [Units.inv_mul, ContinuousLinearMap.one_apply]
    rw [ContinuousLinearMap.mul_apply, h0, map_zero] at h1
    have h2 := b.orthonormal.1 i
    rw [← h1, norm_zero] at h2
    exact zero_ne_one h2

/-- If the entries tend to `0` along the cofinite filter, the closure of the set of entries adds at
    most the point `0`. -/
theorem closure_range_subset_of_tendsto_zero (a : ι → ℂ) (h : Tendsto a cofinite (𝓝 0)) :
    closure (Set.range a) ⊆ insert 0 (Set.range a) := by
  intro μ hμ
  by_cases h0 : μ = 0
  · exact Or.inl h0
  · right
    have hpos : 0 < ‖μ‖ / 2 := by positivity
    have hev : ∀ᶠ i in cofinite, ‖a i‖ ≤ ‖μ‖ / 2 := by
      have := h.eventually (Metric.closedBall_mem_nhds (0 : ℂ) hpos)
      filter_upwards [this] with i hi
      rwa [dist_zero_right] at hi
    have hF : {i | ¬ ‖a i‖ ≤ ‖μ‖ / 2}.Finite := hev
    have hsub : Set.range a ⊆ a '' {i | ¬ ‖a i‖ ≤ ‖μ‖ / 2} ∪ Metric.closedBall 0 (‖μ‖ / 2) := by
      rintro _ ⟨i, rfl⟩
      by_cases hi : ‖a i‖ ≤ ‖μ‖ / 2
      · exact Or.inr (mem_closedBall_zero_iff.2 hi)
      · exact Or.inl ⟨i, hi, rfl⟩
    have hcl : IsClosed (a '' {i | ¬ ‖a i‖ ≤ ‖μ‖ / 2} ∪ Metric.closedBall (0 : ℂ) (‖μ‖ / 2)) :=
      (hF.image a).isClosed.union Metric.isClosed_closedBall
    rcases closure_minimal hsub hcl hμ with ⟨i, -, hi⟩ | hball
    · exact ⟨i, hi⟩
    · rw [mem_closedBall_zero_iff] at hball
      have hn : 0 < ‖μ‖ := norm_pos_iff.2 h0
      linarith

end DiagSpectrum

/-! ## Part 2: the diagonal heat operator of the flat torus -/

section HeatSpectrumL2

open MeasureTheory

variable (d : ℕ)

/-- The number `exp(-4π² t q)` as a complex number. -/
def heatEig (t : ℝ) (q : ℤ) : ℂ := ((Real.exp (-(4 * Real.pi ^ 2 * t) * (q : ℝ)) : ℝ) : ℂ)

/-- On the shell `|n|² = q` the entry of `heatOp d t` is `heatEig t q` (any `t`). -/
theorem heatCoeff_of_mem_shell (t : ℝ) {q : ℤ} {n : Fin d → ℤ}
    (hn : n ∈ CTG.TorusSpectrum.shell d q) : ((heatCoeff d t n : ℝ) : ℂ) = heatEig t q := by
  have h' : ∑ i, n i ^ 2 = q := hn
  have h1 : (∑ i, ((n i : ℤ) : ℝ) ^ 2) = (q : ℝ) := by exact_mod_cast h'
  unfold heatEig heatCoeff
  rw [h1]

/-- For `t ≠ 0` the entry equals `heatEig t q` exactly on the shell `|n|² = q`. -/
theorem heatCoeff_eq_heatEig_iff {t : ℝ} (ht : t ≠ 0) (q : ℤ) (n : Fin d → ℤ) :
    ((heatCoeff d t n : ℝ) : ℂ) = heatEig t q ↔ n ∈ CTG.TorusSpectrum.shell d q := by
  constructor
  · intro h
    unfold heatEig heatCoeff at h
    have h1 := Real.exp_injective (Complex.ofReal_injective h)
    have hne : -(4 * Real.pi ^ 2 * t) ≠ 0 :=
      neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)) ht)
    have h2 : (∑ i, ((n i : ℤ) : ℝ) ^ 2) = (q : ℝ) := mul_left_cancel₀ hne h1
    have h3 : ∑ i, n i ^ 2 = q := by exact_mod_cast h2
    exact h3
  · exact heatCoeff_of_mem_shell d t

theorem heatEig_set_eq {t : ℝ} (ht : t ≠ 0) (q : ℤ) :
    {n : Fin d → ℤ | ((heatCoeff d t n : ℝ) : ℂ) = heatEig t q} = CTG.TorusSpectrum.shell d q :=
  Set.ext fun n => heatCoeff_eq_heatEig_iff d ht q n

/-- Every entry is `heatEig t q` with `q = |n|²`. -/
theorem heatCoeff_eq_heatEig_self (t : ℝ) (n : Fin d → ℤ) :
    ((heatCoeff d t n : ℝ) : ℂ) = heatEig t (∑ i, n i ^ 2) :=
  heatCoeff_of_mem_shell d t (show n ∈ CTG.TorusSpectrum.shell d (∑ i, n i ^ 2) from rfl)

/-- `heatOp d t f = μ • f` iff the Fourier coefficients of `f` vanish off the level set of `μ`. -/
theorem heatOp_eigen_iff (t : ℝ) (ht : 0 ≤ t) (μ : ℂ) (f : L2Torus d) :
    heatOp d t ht f = μ • f
      ↔ ∀ n, ((heatCoeff d t n : ℝ) : ℂ) ≠ μ → ⟪fourierBasis d n, f⟫_ℂ = 0 :=
  diagOp_eigen_iff (fourierBasis d) _ _ μ f

/-- **(2a) The eigenvalues of `heatOp d t`, `t > 0`,** are exactly the numbers `exp(-4π² t q)` with
    `q` a sum of `d` integer squares. -/
theorem heatOp_eigenvalue_iff {t : ℝ} (ht : 0 < t) (μ : ℂ) :
    (∃ f : L2Torus d, f ≠ 0 ∧ heatOp d t ht.le f = μ • f)
      ↔ ∃ q : ℤ, (CTG.TorusSpectrum.shell d q).Nonempty ∧ μ = heatEig t q := by
  unfold heatOp
  rw [diagOp_eigenvalue_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨∑ i, n i ^ 2, ⟨n, rfl⟩, heatCoeff_eq_heatEig_self d t n⟩
  · rintro ⟨q, ⟨n, hn⟩, rfl⟩
    exact ⟨n, heatCoeff_of_mem_shell d t hn⟩

/-- **(2b) The eigenspace of `heatOp d t`, `t > 0`, for `exp(-4π² t q)`** is the span of the Fourier
    modes `b_n` with `|n|² = q`. -/
theorem heatOp_eigenspace {t : ℝ} (ht : 0 < t) (q : ℤ) :
    Module.End.eigenspace (heatOp d t ht.le).toLinearMap (heatEig t q)
      = Submodule.span ℂ (Set.range fun n : CTG.TorusSpectrum.shell d q =>
          fourierBasis d (n : Fin d → ℤ)) := by
  have hfin : {n : Fin d → ℤ | ((heatCoeff d t n : ℝ) : ℂ) = heatEig t q}.Finite := by
    rw [heatEig_set_eq d ht.ne' q]
    exact CTG.TorusSpectrum.shell_finite d q
  unfold heatOp
  rw [diagOp_eigenspace_eq_span (fourierBasis d) _ _ (heatEig t q) hfin, heatEig_set_eq d ht.ne' q,
    Set.image_eq_range]

/-- **(2b') Multiplicity:** the eigenspace of `heatOp d t`, `t > 0`, for `exp(-4π² t q)` has
    dimension the number of lattice points with `|n|² = q`. -/
theorem heatOp_finrank_eigenspace {t : ℝ} (ht : 0 < t) (q : ℤ) :
    Module.finrank ℂ (Module.End.eigenspace (heatOp d t ht.le).toLinearMap (heatEig t q))
      = Nat.card (CTG.TorusSpectrum.shell d q) := by
  have hfin : {n : Fin d → ℤ | ((heatCoeff d t n : ℝ) : ℂ) = heatEig t q}.Finite := by
    rw [heatEig_set_eq d ht.ne' q]
    exact CTG.TorusSpectrum.shell_finite d q
  unfold heatOp
  rw [diagOp_finrank_eigenspace (fourierBasis d) _ _ (heatEig t q) hfin, heatEig_set_eq d ht.ne' q]

/-- **(2b'') The multiplicities of the operator and of the classical Laplacian agree:** the
    eigenspace of `heatOp d t` in `L²` for `exp(-4π² t q)` has the same dimension as the space of
    classical (`C²`, periodic) solutions of `Δ f = -4π² q f` of the fourth project file. (An equality
    of dimensions; no isomorphism is constructed.) -/
theorem heatOp_finrank_eq_classical {t : ℝ} (ht : 0 < t) (q : ℤ) :
    Module.finrank ℂ (Module.End.eigenspace (heatOp d t ht.le).toLinearMap (heatEig t q))
      = Module.finrank ℂ
          (CTG.TorusSpectrum.eigenspace d (4 * (Real.pi : ℂ) ^ 2 * (q : ℂ))) := by
  rw [heatOp_finrank_eigenspace d ht q, CTG.TorusSpectrum.finrank_eigenspace]

/-- **(2c)** `heatOp d t` is injective (`0` is not an eigenvalue), for every `t ≥ 0`. -/
theorem heatOp_injective (t : ℝ) (ht : 0 ≤ t) : Function.Injective (heatOp d t ht) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h0 : heatOp d t ht f = (0 : ℂ) • f := by rw [hf, zero_smul]
  refine eq_zero_of_inner_basis (fourierBasis d) f fun n => ?_
  refine (heatOp_eigen_iff d t ht 0 f).1 h0 n ?_
  exact Complex.ofReal_ne_zero.2 (heatCoeff_pos d t n).ne'

/-- The entries of `heatOp d t`, `t > 0`, tend to `0` along the cofinite filter of `ℤ^d`. -/
theorem heatCoeff_tendsto_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : Fin d → ℤ => ((heatCoeff d t n : ℝ) : ℂ)) cofinite (𝓝 0) := by
  have h := (heatCoeff_summable d ht).tendsto_cofinite_zero
  have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
  simpa using h2

/-- **(2d) The spectrum of `heatOp d t`** for `t > 0`, `d ≥ 1`:
    `{0} ∪ {exp(-4π² t |n|²) : n ∈ ℤ^d}`. -/
theorem spectrum_heatOp (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    spectrum ℂ (heatOp d t ht.le)
      = insert 0 (Set.range fun n : Fin d → ℤ => ((heatCoeff d t n : ℝ) : ℂ)) := by
  unfold heatOp
  rw [spectrum_diagOp]
  apply Set.Subset.antisymm
  · exact closure_range_subset_of_tendsto_zero _ (heatCoeff_tendsto_zero d ht)
  · rintro μ (rfl | hμ)
    · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      haveI : Infinite (Fin (k + 1) → ℤ) := Pi.infinite_of_right
      exact mem_closure_of_tendsto (heatCoeff_tendsto_zero (k + 1) ht)
        (Eventually.of_forall fun n => Set.mem_range_self n)
    · exact subset_closure hμ

/-- The same with the eigenvalues written as `heatEig t q`. -/
theorem spectrum_heatOp_shells (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    spectrum ℂ (heatOp d t ht.le)
      = insert 0 {μ | ∃ q : ℤ, (CTG.TorusSpectrum.shell d q).Nonempty ∧ μ = heatEig t q} := by
  rw [spectrum_heatOp d hd ht]
  congr 1
  ext μ
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨∑ i, n i ^ 2, ⟨n, rfl⟩, heatCoeff_eq_heatEig_self d t n⟩
  · rintro ⟨q, ⟨n, hn⟩, rfl⟩
    exact ⟨n, heatCoeff_of_mem_shell d t hn⟩

/-! ## Part 3: the generator, as statements about the semigroup -/

/-- `heatEig t q = exp(-t · (4π² q))`. -/
theorem heatEig_eq (t : ℝ) (q : ℤ) :
    heatEig t q = ((Real.exp (-(t * (4 * Real.pi ^ 2 * (q : ℝ)))) : ℝ) : ℂ) := by
  unfold heatEig
  congr 2
  ring

/-- A vector in the span of the modes of the shell `q` is an eigenvector of every `heatOp d t`,
    `t ≥ 0`, with eigenvalue `heatEig t q`. -/
theorem heatOp_of_mem_span (t : ℝ) (ht : 0 ≤ t) (q : ℤ) {f : L2Torus d}
    (hf : f ∈ Submodule.span ℂ (Set.range fun n : CTG.TorusSpectrum.shell d q =>
          fourierBasis d (n : Fin d → ℤ))) :
    heatOp d t ht f = heatEig t q • f := by
  have hle : Submodule.span ℂ (Set.range fun n : CTG.TorusSpectrum.shell d q =>
      fourierBasis d (n : Fin d → ℤ))
      ≤ Module.End.eigenspace (heatOp d t ht).toLinearMap (heatEig t q) := by
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    show fourierBasis d (n : Fin d → ℤ)
      ∈ Module.End.eigenspace (heatOp d t ht).toLinearMap (heatEig t q)
    rw [Module.End.mem_eigenspace_iff]
    show heatOp d t ht (fourierBasis d (n : Fin d → ℤ)) = heatEig t q • fourierBasis d (n : Fin d → ℤ)
    rw [heatOp_basis, heatCoeff_of_mem_shell d t n.2]
  exact Module.End.mem_eigenspace_iff.1 (hle hf)

/-- **(3a) One time suffices.** For `f ≠ 0`, `t > 0` and real `lam`: `heatOp d t f = exp(-t·lam) • f`
    iff `lam = 4π² q` for an integer `q` and `f` is in the span of the modes with `|n|² = q`. -/
theorem heatOp_single_time_eigen_iff {t : ℝ} (ht : 0 < t) (lam : ℝ) {f : L2Torus d} (hf : f ≠ 0) :
    heatOp d t ht.le f = ((Real.exp (-(t * lam)) : ℝ) : ℂ) • f
      ↔ ∃ q : ℤ, lam = 4 * Real.pi ^ 2 * (q : ℝ) ∧
          f ∈ Submodule.span ℂ (Set.range fun n : CTG.TorusSpectrum.shell d q =>
            fourierBasis d (n : Fin d → ℤ)) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, ⟪fourierBasis d n, f⟫_ℂ ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hf (eq_zero_of_inner_basis (fourierBasis d) f hno)
    have h1 : ((heatCoeff d t n : ℝ) : ℂ) = ((Real.exp (-(t * lam)) : ℝ) : ℂ) := by
      by_contra hne
      exact hn ((heatOp_eigen_iff d t ht.le _ f).1 h n hne)
    have h2 := Real.exp_injective (Complex.ofReal_injective h1)
    have h3 : lam = 4 * Real.pi ^ 2 * ((∑ i, n i ^ 2 : ℤ) : ℝ) := by
      have h4 : t * lam = t * (4 * Real.pi ^ 2 * ∑ i, ((n i : ℤ) : ℝ) ^ 2) := by linarith
      have h5 := mul_left_cancel₀ ht.ne' h4
      rw [h5]
      push_cast
      rfl
    refine ⟨∑ i, n i ^ 2, h3, ?_⟩
    rw [← heatOp_eigenspace d ht, Module.End.mem_eigenspace_iff, heatEig_eq, ← h3]
    exact h
  · rintro ⟨q, rfl, hfq⟩
    rw [← heatEig_eq]
    exact heatOp_of_mem_span d t ht.le q hfq

/-- **(3b) The joint eigenvectors of the semigroup.** For `f ≠ 0` in `L²((ℝ/ℤ)^d)` and real `lam`:
    `heatOp d t f = exp(-t·lam) • f` for ALL `t ≥ 0` iff `lam = 4π² q` for an integer `q` and `f` is
    in the span of the Fourier modes with `|n|² = q`. In this sense the numbers `4π²|n|²`, with the
    shells as multiplicities, are the eigenvalues of (minus) the generator of the semigroup; the
    generator itself is not an object of this file. -/
theorem heatOp_joint_eigen_iff (lam : ℝ) {f : L2Torus d} (hf : f ≠ 0) :
    (∀ (t : ℝ) (ht : 0 ≤ t), heatOp d t ht f = ((Real.exp (-(t * lam)) : ℝ) : ℂ) • f)
      ↔ ∃ q : ℤ, lam = 4 * Real.pi ^ 2 * (q : ℝ) ∧
          f ∈ Submodule.span ℂ (Set.range fun n : CTG.TorusSpectrum.shell d q =>
            fourierBasis d (n : Fin d → ℤ)) := by
  constructor
  · intro h
    exact (heatOp_single_time_eigen_iff d one_pos lam hf).1 (h 1 zero_le_one)
  · rintro ⟨q, rfl, hfq⟩ t ht
    rw [← heatEig_eq]
    exact heatOp_of_mem_span d t ht q hfq

/-- **(3b') No non-real joint eigenvalue.** The same with a COMPLEX `lam`: `heatOp d t f =
    exp(-t·lam) • f` for all `t ≥ 0` (complex exponential) iff `lam = 4π² q` for an integer `q` and
    `f` is in the span of the Fourier modes with `|n|² = q`. -/
theorem heatOp_joint_eigen_iff_complex (lam : ℂ) {f : L2Torus d} (hf : f ≠ 0) :
    (∀ (t : ℝ) (ht : 0 ≤ t), heatOp d t ht f = Complex.exp (-((t : ℂ) * lam)) • f)
      ↔ ∃ q : ℤ, lam = ((4 * Real.pi ^ 2 * (q : ℝ) : ℝ) : ℂ) ∧
          f ∈ Submodule.span ℂ (Set.range fun n : CTG.TorusSpectrum.shell d q =>
            fourierBasis d (n : Fin d → ℤ)) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ : ∃ n, ⟪fourierBasis d n, f⟫_ℂ ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hf (eq_zero_of_inner_basis (fourierBasis d) f hno)
    -- for every `t ≥ 0`: `exp(-(4π² t)|n|²) = cexp(-t·lam)`
    have key : ∀ t : ℝ, 0 ≤ t →
        ((heatCoeff d t n : ℝ) : ℂ) = Complex.exp (-((t : ℂ) * lam)) := fun t ht => by
      by_contra hne
      exact hn ((heatOp_eigen_iff d t ht _ f).1 (h t ht) n hne)
    set Q : ℝ := 4 * Real.pi ^ 2 * ∑ i, ((n i : ℤ) : ℝ) ^ 2 with hQ
    have key' : ∀ t : ℝ, 0 ≤ t → Complex.exp ((t : ℂ) * ((Q : ℂ) - lam)) = 1 := fun t ht => by
      have h1 := key t ht
      have h2 : ((heatCoeff d t n : ℝ) : ℂ) = Complex.exp (-((t : ℂ) * (Q : ℂ))) := by
        unfold heatCoeff
        rw [Complex.ofReal_exp]
        congr 1
        rw [hQ]
        push_cast
        ring
      rw [h2] at h1
      have h3 : (t : ℂ) * ((Q : ℂ) - lam) = -((t : ℂ) * lam) - -((t : ℂ) * (Q : ℂ)) := by ring
      rw [h3, Complex.exp_sub, ← h1, div_self (Complex.exp_ne_zero _)]
    -- the function `t ↦ exp(t z)` is constant `1` on `[0, ∞)`, so `z = 0`
    set z : ℂ := (Q : ℂ) - lam with hz
    have hz0 : z = 0 := by
      have hd1 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * z)) (Complex.exp (((1 : ℝ) : ℂ) * z) * z) 1 := by
        have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z 1 := by
          have := (Complex.ofRealCLM.hasDerivAt (x := (1 : ℝ))).mul_const z
          simpa using this
        exact hlin.cexp
      have hconst : (fun s : ℝ => Complex.exp ((s : ℂ) * z)) =ᶠ[𝓝 1] fun _ => (1 : ℂ) := by
        filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with s hs
        exact key' s hs.le
      have hd2 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * z)) 0 1 :=
        (hasDerivAt_const (1 : ℝ) (1 : ℂ)).congr_of_eventuallyEq hconst
      have h4 := hd1.unique hd2
      rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd h5 (Complex.exp_ne_zero _)
      · exact h5
    have hlam : lam = (Q : ℂ) := (sub_eq_zero.1 hz0).symm
    have hQq : Q = 4 * Real.pi ^ 2 * ((∑ i, n i ^ 2 : ℤ) : ℝ) := by
      rw [hQ]
      push_cast
      rfl
    refine ⟨∑ i, n i ^ 2, by rw [hlam, hQq], ?_⟩
    have h1 := h 1 zero_le_one
    rw [← heatOp_eigenspace d one_pos, Module.End.mem_eigenspace_iff]
    show heatOp d 1 zero_le_one f = heatEig 1 (∑ i, n i ^ 2) • f
    rw [h1, ← key 1 zero_le_one, heatCoeff_eq_heatEig_self]
  · rintro ⟨q, rfl, hfq⟩ t ht
    rw [heatOp_of_mem_span d t ht q hfq, heatEig_eq, Complex.ofReal_exp]
    congr 2
    push_cast
    ring

/-- The semigroup as a total function of the real variable `t`: `heatSg d t = heatOp d (max t 0)`. -/
def heatSg (t : ℝ) : L2Torus d →L[ℂ] L2Torus d := heatOp d (max t 0) (le_max_right t 0)

theorem heatSg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : heatSg d t = heatOp d t ht :=
  heatOp_congr d (max_eq_left ht) _ _

/-- The difference quotient at `0` on one Fourier mode: `(heatOp d t b_n - b_n)/t → λ_n b_n` as
    `t ↓ 0`, `λ_n = lapEig d n = -4π²|n|²`. -/
theorem heatOp_generator_on_mode (n : Fin d → ℤ) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (heatSg d t (fourierBasis d n) - fourierBasis d n))
      (𝓝[>] 0) (𝓝 (((HeatSpectrumBridge.lapEig d n : ℝ) : ℂ) • fourierBasis d n)) := by
  set L : ℝ := HeatSpectrumBridge.lapEig d n with hL
  -- derivative of `t ↦ exp(t L)` at `0`
  have hd : HasDerivAt (fun t : ℝ => Real.exp (t * L)) L 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * L) L 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const L
    have h2 := h1.exp
    simpa using h2
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (Real.exp (t * L) - 1)) (𝓝[>] 0) (𝓝 L) := by
    have h := hd.tendsto_slope_zero_right
    simpa using h
  have hC : Tendsto (fun t : ℝ => ((t⁻¹ * (Real.exp (t * L) - 1) : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 ((L : ℝ) : ℂ)) := (Complex.continuous_ofReal.tendsto L).comp hslope
  have hsm := hC.smul_const (fourierBasis d n)
  refine hsm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
  rw [heatSg_of_nonneg d ht0, heatOp_basis, HeatSpectrumBridge.heatCoeff_eq_exp_lapEig]
  rw [← hL]
  have e : ((Real.exp (t * L) : ℝ) : ℂ) • fourierBasis d n - fourierBasis d n
      = (((Real.exp (t * L) - 1 : ℝ)) : ℂ) • fourierBasis d n := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  rw [e, smul_smul]
  congr 1
  push_cast
  ring

/-- **(3c) The generator on finite linear combinations of Fourier modes.** For
    `f = ∑_{n ∈ s} c_n b_n`: `(heatOp d t f - f)/t → ∑_{n ∈ s} c_n λ_n b_n` in `L²` as `t ↓ 0`, where
    `λ_n = lapEig d n = -4π²|n|²` is the eigenvalue of the classical Laplacian on the periodic
    function `e_n` whose class is `b_n` (`heatOp_mode_laplacian` of the sixth file). This is the
    action of the generator on trigonometric polynomials only; nothing is said about its domain. -/
theorem heatOp_generator_on_modes (s : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ •
        (heatSg d t (∑ n ∈ s, c n • fourierBasis d n) - ∑ n ∈ s, c n • fourierBasis d n))
      (𝓝[>] 0)
      (𝓝 (∑ n ∈ s, (c n * ((HeatSpectrumBridge.lapEig d n : ℝ) : ℂ)) • fourierBasis d n)) := by
  have h : ∀ n ∈ s, Tendsto (fun t : ℝ => c n • ((t : ℂ)⁻¹ •
        (heatSg d t (fourierBasis d n) - fourierBasis d n))) (𝓝[>] 0)
      (𝓝 ((c n * ((HeatSpectrumBridge.lapEig d n : ℝ) : ℂ)) • fourierBasis d n)) := fun n _ => by
    have := (heatOp_generator_on_mode d n).const_smul (c n)
    rwa [smul_smul] at this
  have hsum := tendsto_finset_sum s h
  refine hsum.congr fun t => ?_
  rw [map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_smul, ← smul_sub, smul_comm]

end HeatSpectrumL2

end

end HeatTraceOperator
