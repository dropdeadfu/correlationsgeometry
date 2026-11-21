/-
Sixth Lean file of the project; check with `cd lean && ./check_heat_spectrum.sh`.
Two bridges from the diagonal heat operator of the fifth project file
(`CorrelationsToGeometryHeatOperator.lean`, namespace `HeatTraceOperator`).

Own text of this project. It USES, with attribution, `IsTraceClass`, `trace` and (through the
fifth file) `isTraceClass_comp`, `IsTraceClass.hasSum_trace`, `IsHilbertSchmidt` from the two ported
files of the Lean archive of Levent Alpöge (https://alpo.ge/remark.pdf; ports under
`lean/ports/alpoge-rh/`). All credit for those definitions and theorems belongs to their author.

PART (a) (namespace `HeatTraceOperator`; needs only the imports of the fifth file).
With `H := heatOp d (σ/2)` (the diagonal operator in Mathlib's Fourier basis with entries
`exp(-2π² σ |n|²)`):
* `heatOp_zero`, `heatOp_pow`: `heatOp d 0 = 1`, `H^k = heatOp d (k·t)`.
* `torusM_eq_trace_heatOp`, `torusM_eq_trace_pow`, `heatMode_eq_trace_pow`: the numbers
  `m_k = torusM d σ k = heatMode d σ k = p_{kσ}(0)` of the second file are `trace (H^k)`, `k ≥ 1`.
* `poissonMean_hasSum_trace`: `poissonMean d σ τ = ∑_{j ≥ 1} w_j(τ) trace (H^j)`.
* `poissonOp`: the diagonal operator with entries `e^{-τ}(e^{τ a_n} - 1)`, `a_n = exp(-2π² σ |n|²)`;
  `poissonOp_isTraceClass`, `trace_poissonOp`: it is trace class with trace `poissonMean d σ τ`.
* `exp_heatOp_sub_eq_poissonOp`: `NormedSpace.exp (τ • (H - 1)) - e^{-τ} • 1 = poissonOp`
  (operator exponential of Mathlib in the Banach algebra of bounded operators), hence
  `trace_exp_heatOp`: `exp(τ(H - 1)) - e^{-τ}·1` is trace class with trace `poissonMean d σ τ`.

PART (b) (namespace `HeatSpectrumBridge`; needs in addition the fourth file
`CorrelationsToGeometrySpectrum.lean`).
* `heatOp_mode_laplacian`: for every `n ∈ ℤ^d`, with `λ_n = lapEig d n = -4π²|n|²`: the periodic
  function `e_n` on `ℝ^d` satisfies `Δ e_n = λ_n e_n` (Mathlib's Laplacian), `e_n = mFourier n ∘ proj`,
  the basis vector `b_n` of `mFourierBasis` is the `L²` class of `mFourier n`, and
  `heatOp d t b_n = exp(t λ_n) • b_n`.
* `heatOp_mode_ae`: `heatOp d t b_n` is represented by `y ↦ exp(t λ_n) · mFourier n y`.

WHAT IS NOT PROVED AND NOT CLAIMED.
* `heatOp d t` is still BY DEFINITION the diagonal operator in the Fourier basis. Part (b) says that
  on each Fourier mode it acts as `exp(t λ)` with `λ` the eigenvalue of the classical Laplacian on
  the periodic function whose class the mode is. It does NOT say that `heatOp d t = e^{tΔ}` for an
  unbounded self-adjoint Laplacian on `L²` (no such operator occurs in any project file), nor that
  `heatOp d t` is the integral operator with the periodised Gaussian kernel.
* That `exp(τ(S - 1))` for the SAMPLE graph (the matrix statements `heat_trace_G29` of the second
  file) converges to the operator of part (a) in any operator sense is not a statement here; part
  (a) only identifies the limiting NUMBERS `m_k` and `poissonMean` as traces of operators.
No `sorry`, no `axiom`, no `native_decide`.
-/
import Mathlib
import GroundTheory.AutomorphicForms.HilbertSchmidt
import GroundTheory.AutomorphicForms.TraceClass
import CorrelationsToGeometryReal
import CorrelationsToGeometryHeatOperator
import CorrelationsToGeometrySpectrum

/-! ## Part (a): the numbers `m_k` and `poissonMean` as traces of operators -/

namespace HeatTraceOperator

open scoped ENNReal InnerProductSpace
open GroundTheory.Automorphic

noncomputable section

section DiagonalMore

variable {ι : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The diagonal operator with all entries `1` is the identity. -/
theorem diagOp_one (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (h : ∀ i, a i = 1) : diagOp b a ha = 1 := by
  ext x
  rw [diagOp_apply, ContinuousLinearMap.one_apply]
  have e : mulL2 a ha (b.repr x) = b.repr x := by
    ext i
    rw [mulL2_apply, h i, one_mul]
  rw [e, LinearIsometryEquiv.symm_apply_apply]

/-- A bounded operator that has the Hilbert basis `b` as eigenvectors with eigenvalues `a` is the
    diagonal operator of `a`. -/
theorem eq_diagOp_of_basis (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (A : H →L[ℂ] H) (h : ∀ i, A (b i) = a i • b i) : A = diagOp b a ha := by
  refine ContinuousLinearMap.ext_on (s := Set.range b)
    (Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span) ?_
  rintro _ ⟨i, rfl⟩
  show A (b i) = diagOp b a ha (b i)
  rw [h, diagOp_basis]

/-- A diagonal operator with non-negative summable real entries is trace class (the entries are
    squares of a square-summable family; `isTraceClass_comp` of the archive through
    `isTraceClass_diagOp_mul`). -/
theorem isTraceClass_diagOp_of_nonneg (b : HilbertBasis ι ℂ H) (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    (hs : Summable c) (ha : ∃ C : ℝ, ∀ i, ‖((c i : ℝ) : ℂ)‖ ≤ C) :
    IsTraceClass (diagOp b (fun i => ((c i : ℝ) : ℂ)) ha) := by
  obtain ⟨C, hC⟩ := id ha
  have hsb : ∃ C' : ℝ, ∀ i, ‖((Real.sqrt (c i) : ℝ) : ℂ)‖ ≤ C' := ⟨Real.sqrt C, fun i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    have h := hC i
    rwa [Complex.norm_real, Real.norm_of_nonneg (hc0 i)] at h⟩
  have hss : ∀ i, ((Real.sqrt (c i) : ℝ) : ℂ) * ((Real.sqrt (c i) : ℝ) : ℂ) = ((c i : ℝ) : ℂ) :=
    fun i => by rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc0 i)]
  have hsq : ∑' i, ‖((Real.sqrt (c i) : ℝ) : ℂ)‖ₑ ^ 2 < ∞ := by
    have h : ∀ i, ‖((Real.sqrt (c i) : ℝ) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (c i) := fun i => by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hc0 i)]
    simp only [h]
    rw [← ENNReal.ofReal_tsum_of_nonneg hc0 hs]
    exact ENNReal.ofReal_lt_top
  have hbb : ∃ C' : ℝ, ∀ i,
      ‖((Real.sqrt (c i) : ℝ) : ℂ) * ((Real.sqrt (c i) : ℝ) : ℂ)‖ ≤ C' :=
    ⟨C, fun i => by rw [hss i]; exact hC i⟩
  have h := isTraceClass_diagOp_mul b (fun i => ((Real.sqrt (c i) : ℝ) : ℂ))
    (fun i => ((Real.sqrt (c i) : ℝ) : ℂ)) hsb hsb hbb hsq hsq
  have e := diagOp_congr b (funext hss) hbb ha
  rw [← e]
  exact h

/-- The trace of a diagonal operator with non-negative real entries of sum `S` is `S`. -/
theorem trace_diagOp_of_hasSum (b : HilbertBasis ι ℂ H) (c : ι → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    {S : ℝ} (hS : HasSum c S) (ha : ∃ C : ℝ, ∀ i, ‖((c i : ℝ) : ℂ)‖ ≤ C) :
    GroundTheory.Automorphic.trace (diagOp b (fun i => ((c i : ℝ) : ℂ)) ha) = ((S : ℝ) : ℂ) :=
  (hasSum_trace_diagOp b _ ha (isTraceClass_diagOp_of_nonneg b c hc0 hS.summable ha)).unique
    (Complex.hasSum_ofReal.2 hS)

/-- The operator exponential on an eigenvector: `A v = λ v` implies `exp(A) v = e^λ v`
    (`NormedSpace.exp` of Mathlib in the Banach algebra of bounded operators). -/
theorem exp_apply_eigen (A : H →L[ℂ] H) (v : H) (lam : ℂ) (h : A v = lam • v) :
    NormedSpace.exp A v = Complex.exp lam • v := by
  have h1 : ∀ k : ℕ, (A ^ k) v = lam ^ k • v := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, ContinuousLinearMap.one_apply, one_smul]
    | succ k ih =>
      rw [pow_succ A k, ContinuousLinearMap.mul_apply, h, map_smul, ih, smul_smul, pow_succ lam k,
        mul_comm]
  have h2 : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • A ^ k)) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have h3 : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • A ^ k) v) (NormedSpace.exp A v) := by
    have h := (ContinuousLinearMap.apply ℂ H v).hasSum h2
    simp only [ContinuousLinearMap.apply_apply] at h
    exact h
  have e : (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • A ^ k) v)
      = fun k : ℕ => ((k.factorial : ℂ)⁻¹ • lam ^ k) • v := funext fun k => by
    rw [ContinuousLinearMap.smul_apply, h1, smul_assoc]
  rw [e] at h3
  have h4 : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • lam ^ k) • v) (NormedSpace.exp lam • v) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) lam).smul_const v
  rw [Complex.exp_eq_exp_ℂ]
  exact h3.unique h4

end DiagonalMore

section HeatMore

open MeasureTheory CTG.Reals

variable (d : ℕ)

theorem heatCoeff_pow (t : ℝ) (n : Fin d → ℤ) (k : ℕ) :
    heatCoeff d t n ^ k = heatCoeff d ((k : ℝ) * t) n := by
  unfold heatCoeff
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The coefficients sum to the Fourier-series heat kernel of the second file at the origin. -/
theorem hasSum_heatCoeff {t : ℝ} (ht : 0 < t) :
    HasSum (heatCoeff d t) (heatTorus d (4 * Real.pi ^ 2 * t) 0) := by
  rw [heatTorus, cosSeries_zero]
  exact (heatCoeff_summable d ht).hasSum

/-- `T_0 = 1`. -/
theorem heatOp_zero : heatOp d 0 le_rfl = 1 :=
  diagOp_one (fourierBasis d) _ _ (fun n => by
    show ((heatCoeff d 0 n : ℝ) : ℂ) = 1
    simp [heatCoeff])

/-- **Powers:** `T_t ^ k = T_{k t}` (from the semigroup property `heatOp_comp`). -/
theorem heatOp_pow {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    heatOp d t ht ^ k = heatOp d ((k : ℝ) * t) (mul_nonneg (Nat.cast_nonneg k) ht) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact (heatOp_zero d).symm.trans (heatOp_congr d (by simp) _ _)
  | succ k ih =>
    rw [pow_succ, ih, ContinuousLinearMap.mul_def,
      heatOp_comp d (mul_nonneg (Nat.cast_nonneg k) ht) ht]
    exact heatOp_congr d (by push_cast; ring) _ _

/-- **`m_k` as the trace of an operator:** `torusM d σ k = p_{kσ}(0) = trace (T_{kσ/2})`. -/
theorem torusM_eq_trace_heatOp {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k) :
    ((TorusReduction.torusM d σ k : ℝ) : ℂ) =
      GroundTheory.Automorphic.trace (heatOp d ((k : ℝ) * (σ / 2))
        (mul_nonneg (Nat.cast_nonneg k) (half_pos hσ).le)) := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 (by omega)
  have ht : 0 < (k : ℝ) * (σ / 2) := mul_pos hk' (half_pos hσ)
  have e : 4 * Real.pi ^ 2 * ((k : ℝ) * (σ / 2)) = 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := by ring
  show ((heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 : ℝ) : ℂ) = _
  rw [trace_heatOp_eq_heatTorus d ht, e]

/-- **`m_k = trace (H^k)`** with `H = T_{σ/2}`, for `k ≥ 1`, `σ > 0`. -/
theorem torusM_eq_trace_pow {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k) :
    ((TorusReduction.torusM d σ k : ℝ) : ℂ) =
      GroundTheory.Automorphic.trace (heatOp d (σ / 2) (half_pos hσ).le ^ k) := by
  rw [heatOp_pow d (half_pos hσ).le k]
  exact torusM_eq_trace_heatOp d hσ hk

/-- The same for `heatMode` of the section on the trace (`TraceG29`), which is the same number. -/
theorem heatMode_eq_trace_pow {σ : ℝ} (hσ : 0 < σ) {k : ℕ} (hk : 1 ≤ k) :
    ((TraceG29.heatMode d σ k : ℝ) : ℂ) =
      GroundTheory.Automorphic.trace (heatOp d (σ / 2) (half_pos hσ).le ^ k) :=
  torusM_eq_trace_pow d hσ hk

/-- **`poissonMean` as a Poisson-weighted sum of traces of powers:**
    `∑_{j ≥ 1} w_j(τ) trace (H^j) = poissonMean d σ τ` (a rewriting of the definition). -/
theorem poissonMean_hasSum_trace {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasSum (fun j : ℕ => ((TraceG29.pw τ (j + 1) : ℝ) : ℂ) *
        GroundTheory.Automorphic.trace (heatOp d (σ / 2) (half_pos hσ).le ^ (j + 1)))
      ((TraceG29.poissonMean d σ τ : ℝ) : ℂ) := by
  have e : (fun j : ℕ => ((TraceG29.pw τ (j + 1) : ℝ) : ℂ) *
        GroundTheory.Automorphic.trace (heatOp d (σ / 2) (half_pos hσ).le ^ (j + 1)))
      = fun j : ℕ => ((TraceG29.pw τ (j + 1) * TraceG29.heatMode d σ (j + 1) : ℝ) : ℂ) :=
    funext fun j => by
      rw [Complex.ofReal_mul, heatMode_eq_trace_pow d hσ (Nat.succ_le_succ (Nat.zero_le j))]
  rw [e]
  exact Complex.hasSum_ofReal.2 (TraceG29.poissonMean_hasSum hσ d hτ)

/-! ### The operator `exp(τ(H - 1)) - e^{-τ}` -/

/-- `∑_{j ≥ 1} w_j(τ) x^j = e^{-τ} e^{τ x} - e^{-τ}`. -/
theorem pw_pow_shift_hasSum (τ x : ℝ) :
    HasSum (fun j : ℕ => TraceG29.pw τ (j + 1) * x ^ (j + 1))
      (Real.exp (-τ) * Real.exp (τ * x) - Real.exp (-τ)) := by
  have h : HasSum (fun j : ℕ => TraceG29.pw τ j * x ^ j) (Real.exp (-τ) * Real.exp (τ * x)) := by
    have h0 := (real_hasSum_exp (τ * x)).mul_left (Real.exp (-τ))
    have e : (fun j : ℕ => TraceG29.pw τ j * x ^ j)
        = fun j : ℕ => Real.exp (-τ) * ((τ * x) ^ j / (j.factorial : ℝ)) := funext fun j => by
      unfold TraceG29.pw
      rw [mul_pow]
      ring
    rw [e]
    exact h0
  have h1 := (hasSum_nat_add_iff' 1).2 h
  rw [Finset.sum_range_one, pow_zero, mul_one, TraceG29.pw_zero] at h1
  exact h1

/-- The entry `e^{-τ}(e^{τ a_n} - 1)`, `a_n = exp(-2π² σ |n|²)`, of the diagonal operator below. -/
def poissonCoeff (σ τ : ℝ) (n : Fin d → ℤ) : ℝ :=
  Real.exp (-τ) * Real.exp (τ * heatCoeff d (σ / 2) n) - Real.exp (-τ)

theorem poissonCoeff_nonneg (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (n : Fin d → ℤ) :
    0 ≤ poissonCoeff d σ τ n := by
  unfold poissonCoeff
  have h1 : 1 ≤ Real.exp (τ * heatCoeff d (σ / 2) n) :=
    Real.one_le_exp (mul_nonneg hτ (heatCoeff_pos d _ n).le)
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-τ)).le
  linarith

theorem poissonCoeff_le_one {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (n : Fin d → ℤ) :
    poissonCoeff d σ τ n ≤ 1 := by
  unfold poissonCoeff
  have hσ2 : 0 ≤ σ / 2 := by linarith
  have h1 : τ * heatCoeff d (σ / 2) n ≤ τ * 1 :=
    mul_le_mul_of_nonneg_left (heatCoeff_le_one d hσ2 n) hτ
  have h2 : Real.exp (-τ) * Real.exp (τ * heatCoeff d (σ / 2) n) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.2 (by linarith)
  linarith [Real.exp_pos (-τ)]

theorem poissonCoeff_bdd {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) :
    ∃ C : ℝ, ∀ n : Fin d → ℤ, ‖((poissonCoeff d σ τ n : ℝ) : ℂ)‖ ≤ C :=
  ⟨1, fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg (poissonCoeff_nonneg d σ hτ n)]
    exact poissonCoeff_le_one d hσ hτ n⟩

/-- The double family `w_{j+1}(τ) a_n^{j+1}`. -/
def poissonTerm (σ τ : ℝ) (j : ℕ) (n : Fin d → ℤ) : ℝ :=
  TraceG29.pw τ (j + 1) * heatCoeff d (σ / 2) n ^ (j + 1)

theorem poissonTerm_nonneg (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (j : ℕ) (n : Fin d → ℤ) :
    0 ≤ poissonTerm d σ τ j n :=
  mul_nonneg (TraceG29.pw_nonneg hτ (j + 1)) (pow_nonneg (heatCoeff_pos d _ n).le _)

/-- Sum over the modes for a fixed number of steps: `w_{j+1} m_{j+1}`. -/
theorem hasSum_poissonTerm_modes {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) (j : ℕ) :
    HasSum (fun n : Fin d → ℤ => poissonTerm d σ τ j n)
      (TraceG29.pw τ (j + 1) * TraceG29.heatMode d σ (j + 1)) := by
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.succ_pos j)
  have ht : 0 < ((j + 1 : ℕ) : ℝ) * (σ / 2) := mul_pos hj (half_pos hσ)
  have h := (hasSum_heatCoeff d ht).mul_left (TraceG29.pw τ (j + 1))
  have e : 4 * Real.pi ^ 2 * (((j + 1 : ℕ) : ℝ) * (σ / 2))
      = 2 * Real.pi ^ 2 * (((j + 1 : ℕ) : ℝ) * σ) := by ring
  rw [e] at h
  have e2 : (fun n : Fin d → ℤ => poissonTerm d σ τ j n)
      = fun n : Fin d → ℤ =>
        TraceG29.pw τ (j + 1) * heatCoeff d (((j + 1 : ℕ) : ℝ) * (σ / 2)) n :=
    funext fun n => by rw [poissonTerm, heatCoeff_pow]
  rw [e2]
  exact h

/-- Sum over the steps for a fixed mode: the entry `poissonCoeff`. -/
theorem hasSum_poissonTerm_steps (σ τ : ℝ) (n : Fin d → ℤ) :
    HasSum (fun j : ℕ => poissonTerm d σ τ j n) (poissonCoeff d σ τ n) :=
  pw_pow_shift_hasSum τ (heatCoeff d (σ / 2) n)

theorem summable_poissonTerm {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    Summable (Function.uncurry (poissonTerm d σ τ)) := by
  refine (summable_prod_of_nonneg (fun p => poissonTerm_nonneg d σ hτ p.1 p.2)).2
    ⟨fun j => (hasSum_poissonTerm_modes d hσ τ j).summable, ?_⟩
  show Summable (fun j : ℕ => ∑' n : Fin d → ℤ, poissonTerm d σ τ j n)
  have e : (fun j : ℕ => ∑' n : Fin d → ℤ, poissonTerm d σ τ j n)
      = fun j : ℕ => TraceG29.pw τ (j + 1) * TraceG29.heatMode d σ (j + 1) :=
    funext fun j => (hasSum_poissonTerm_modes d hσ τ j).tsum_eq
  rw [e]
  exact (TraceG29.poissonMean_hasSum hσ d hτ).summable

/-- **The entries `e^{-τ}(e^{τ a_n} - 1)` sum to `poissonMean d σ τ`** (exchange of the sum over
    the modes and the Poisson sum; all terms are non-negative). -/
theorem hasSum_poissonCoeff {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasSum (poissonCoeff d σ τ) (TraceG29.poissonMean d σ τ) := by
  have hs := summable_poissonTerm d hσ hτ
  have h3 : Summable (fun n : Fin d → ℤ => ∑' j : ℕ, poissonTerm d σ τ j n) := hs.prod_symm.prod
  have e : (fun n : Fin d → ℤ => ∑' j : ℕ, poissonTerm d σ τ j n) = poissonCoeff d σ τ :=
    funext fun n => (hasSum_poissonTerm_steps d σ τ n).tsum_eq
  rw [e] at h3
  have hval : ∑' n, poissonCoeff d σ τ n = TraceG29.poissonMean d σ τ :=
    calc ∑' n, poissonCoeff d σ τ n
        = ∑' (n : Fin d → ℤ) (j : ℕ), poissonTerm d σ τ j n :=
          tsum_congr fun n => (hasSum_poissonTerm_steps d σ τ n).tsum_eq.symm
      _ = ∑' (j : ℕ) (n : Fin d → ℤ), poissonTerm d σ τ j n := hs.tsum_comm
      _ = ∑' j : ℕ, TraceG29.pw τ (j + 1) * TraceG29.heatMode d σ (j + 1) :=
          tsum_congr fun j => (hasSum_poissonTerm_modes d hσ τ j).tsum_eq
      _ = TraceG29.poissonMean d σ τ := rfl
  rw [← hval]
  exact h3.hasSum

/-- **The diagonal operator with entries `e^{-τ}(e^{τ a_n} - 1)`** in the Fourier basis,
    `a_n = exp(-2π² σ |n|²)`. By `exp_heatOp_sub_eq_poissonOp` below it is
    `exp(τ(H - 1)) - e^{-τ}·1` with `H = heatOp d (σ/2)`. -/
def poissonOp {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) : L2Torus d →L[ℂ] L2Torus d :=
  diagOp (fourierBasis d) (fun n => ((poissonCoeff d σ τ n : ℝ) : ℂ)) (poissonCoeff_bdd d hσ hτ)

theorem poissonOp_basis {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (n : Fin d → ℤ) :
    poissonOp d hσ hτ (fourierBasis d n) = ((poissonCoeff d σ τ n : ℝ) : ℂ) • fourierBasis d n :=
  diagOp_basis (fourierBasis d) _ _ n

/-- `poissonOp` is trace class (`σ > 0`, `τ ≥ 0`). -/
theorem poissonOp_isTraceClass {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsTraceClass (poissonOp d hσ.le hτ) :=
  isTraceClass_diagOp_of_nonneg (fourierBasis d) (poissonCoeff d σ τ)
    (poissonCoeff_nonneg d σ hτ) (hasSum_poissonCoeff d hσ hτ).summable _

/-- **`trace (poissonOp) = poissonMean d σ τ`.** -/
theorem trace_poissonOp {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    GroundTheory.Automorphic.trace (poissonOp d hσ.le hτ)
      = ((TraceG29.poissonMean d σ τ : ℝ) : ℂ) :=
  trace_diagOp_of_hasSum (fourierBasis d) (poissonCoeff d σ τ) (poissonCoeff_nonneg d σ hτ)
    (hasSum_poissonCoeff d hσ hτ) _

/-- **The operator exponential:** with `H = heatOp d (σ/2)`,
    `exp(τ • (H - 1)) - e^{-τ} • 1 = poissonOp` (`NormedSpace.exp` of Mathlib in the Banach algebra
    of bounded operators on `L²((ℝ/ℤ)^d)`). -/
theorem exp_heatOp_sub_eq_poissonOp {σ τ : ℝ} (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) :
    NormedSpace.exp ((τ : ℂ) • (heatOp d (σ / 2) (div_nonneg hσ zero_le_two) - 1))
        - ((Real.exp (-τ) : ℝ) : ℂ) • (1 : L2Torus d →L[ℂ] L2Torus d)
      = poissonOp d hσ hτ := by
  refine eq_diagOp_of_basis (fourierBasis d) _ _ _ (fun n => ?_)
  have hA : ((τ : ℂ) • (heatOp d (σ / 2) (div_nonneg hσ zero_le_two) - 1)) (fourierBasis d n)
      = ((τ : ℂ) * (((heatCoeff d (σ / 2) n : ℝ) : ℂ) - 1)) • fourierBasis d n := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, heatOp_basis,
      ContinuousLinearMap.one_apply, mul_smul, sub_smul, one_smul]
  have hc : ((poissonCoeff d σ τ n : ℝ) : ℂ)
      = Complex.exp ((τ : ℂ) * (((heatCoeff d (σ / 2) n : ℝ) : ℂ) - 1))
        - ((Real.exp (-τ) : ℝ) : ℂ) := by
    unfold poissonCoeff
    rw [← Real.exp_add, Complex.ofReal_sub,
      Complex.ofReal_exp (-τ + τ * heatCoeff d (σ / 2) n)]
    congr 2
    push_cast
    ring
  show (NormedSpace.exp ((τ : ℂ) • (heatOp d (σ / 2) (div_nonneg hσ zero_le_two) - 1))
        - ((Real.exp (-τ) : ℝ) : ℂ) • (1 : L2Torus d →L[ℂ] L2Torus d)) (fourierBasis d n)
      = ((poissonCoeff d σ τ n : ℝ) : ℂ) • fourierBasis d n
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, exp_apply_eigen _ _ _ hA, hc, sub_smul]

/-- **Operator form of `poissonMean`:** for `σ > 0`, `τ ≥ 0` and `H = heatOp d (σ/2)` the operator
    `exp(τ(H - 1)) - e^{-τ}·1` is trace class and its trace is `poissonMean d σ τ`. -/
theorem trace_exp_heatOp {σ : ℝ} (hσ : 0 < σ) {τ : ℝ} (hτ : 0 ≤ τ) :
    IsTraceClass (NormedSpace.exp ((τ : ℂ) • (heatOp d (σ / 2) (div_nonneg hσ.le zero_le_two) - 1))
        - ((Real.exp (-τ) : ℝ) : ℂ) • (1 : L2Torus d →L[ℂ] L2Torus d)) ∧
    GroundTheory.Automorphic.trace
        (NormedSpace.exp ((τ : ℂ) • (heatOp d (σ / 2) (div_nonneg hσ.le zero_le_two) - 1))
        - ((Real.exp (-τ) : ℝ) : ℂ) • (1 : L2Torus d →L[ℂ] L2Torus d))
      = ((TraceG29.poissonMean d σ τ : ℝ) : ℂ) := by
  rw [exp_heatOp_sub_eq_poissonOp d hσ.le hτ]
  exact ⟨poissonOp_isTraceClass d hσ hτ, trace_poissonOp d hσ hτ⟩

end HeatMore

end

end HeatTraceOperator

/-! ## Part (b): the Fourier modes, the classical Laplacian and the diagonal heat operator -/

namespace HeatSpectrumBridge

open MeasureTheory HeatTraceOperator

noncomputable section

variable (d : ℕ)

/-- The eigenvalue `λ_n = -4π² |n|²` of the Laplacian on the character `e_n`. -/
def lapEig (n : Fin d → ℤ) : ℝ := -(4 * Real.pi ^ 2 * ∑ i, ((n i : ℤ) : ℝ) ^ 2)

/-- The entries of the diagonal heat operator are `exp(t λ_n)`. -/
theorem heatCoeff_eq_exp_lapEig (t : ℝ) (n : Fin d → ℤ) :
    heatCoeff d t n = Real.exp (t * lapEig d n) := by
  unfold heatCoeff lapEig
  congr 1
  ring

/-- `laplacian_e` of the fourth file with the real number `lapEig`. -/
theorem laplacian_e_lapEig (n : Fin d → ℤ) (x : CTG.TorusSpectrum.E d) :
    Laplacian.laplacian (CTG.TorusSpectrum.e d n) x
      = ((lapEig d n : ℝ) : ℂ) * CTG.TorusSpectrum.e d n x := by
  have h : ((lapEig d n : ℝ) : ℂ) = -(4 * (Real.pi : ℂ) ^ 2 * ∑ i, ((n i : ℤ) : ℂ) ^ 2) := by
    unfold lapEig
    push_cast
    ring
  rw [CTG.TorusSpectrum.laplacian_e, h]

/-- The periodic function `e_n` on `ℝ^d` descends to `mFourier n` on the torus. -/
theorem desc_e (n : Fin d → ℤ) :
    CTG.TorusSpectrum.desc d (CTG.TorusSpectrum.e d n) = fun y => UnitAddTorus.mFourier n y := by
  funext y
  obtain ⟨x, rfl⟩ := CTG.TorusSpectrum.proj_surjective d y
  rw [CTG.TorusSpectrum.desc_proj d (CTG.TorusSpectrum.e_periodic d n) x]
  rfl

/-- The basis vector `b_n` of the fifth file is the `L²` class of `mFourier n`
    (`coe_mFourierBasis`, `coeFn_mFourierLp` of Mathlib). -/
theorem fourierBasis_ae (n : Fin d → ℤ) :
    (fun y => (fourierBasis d n : L2Torus d) y)
      =ᵐ[Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))]
        fun y => UnitAddTorus.mFourier n y := by
  have h := UnitAddTorus.coeFn_mFourierLp (d := Fin d) 2 n
  have e : fourierBasis d n = UnitAddTorus.mFourierLp 2 n :=
    congrFun UnitAddTorus.coe_mFourierBasis n
  rw [e]
  exact h

/-- **Bridge between the diagonal heat operator and the classical Laplacian, mode by mode.**
    For every `n ∈ ℤ^d`, with `λ_n = lapEig d n = -4π²|n|²`:
    (1) the periodic function `e_n` on `ℝ^d` is an eigenfunction, `Δ e_n = λ_n e_n`;
    (2) `e_n` is the pull-back of `mFourier n` along `ℝ^d → (ℝ/ℤ)^d`;
    (3) the basis vector `b_n` is the `L²` class of `mFourier n`;
    (4) `heatOp d t b_n = exp(t λ_n) • b_n`.
    This is a statement about each mode; it does not identify `heatOp d t` with `e^{tΔ}` for an
    unbounded operator `Δ` on `L²`. -/
theorem heatOp_mode_laplacian (t : ℝ) (ht : 0 ≤ t) (n : Fin d → ℤ) :
    (∀ x : CTG.TorusSpectrum.E d, Laplacian.laplacian (CTG.TorusSpectrum.e d n) x
        = ((lapEig d n : ℝ) : ℂ) * CTG.TorusSpectrum.e d n x) ∧
    (∀ x : CTG.TorusSpectrum.E d,
        CTG.TorusSpectrum.e d n x = UnitAddTorus.mFourier n (CTG.TorusSpectrum.proj d x)) ∧
    ((fun y => (fourierBasis d n : L2Torus d) y)
      =ᵐ[Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))]
        fun y => UnitAddTorus.mFourier n y) ∧
    heatOp d t ht (fourierBasis d n)
      = ((Real.exp (t * lapEig d n) : ℝ) : ℂ) • fourierBasis d n := by
  refine ⟨laplacian_e_lapEig d n, fun x => rfl, fourierBasis_ae d n, ?_⟩
  rw [heatOp_basis, heatCoeff_eq_exp_lapEig]

/-- The class `heatOp d t b_n` is represented by the function `y ↦ exp(t λ_n) · mFourier n y`. -/
theorem heatOp_mode_ae (t : ℝ) (ht : 0 ≤ t) (n : Fin d → ℤ) :
    (fun y => (heatOp d t ht (fourierBasis d n) : L2Torus d) y)
      =ᵐ[Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))]
        fun y => ((Real.exp (t * lapEig d n) : ℝ) : ℂ) * UnitAddTorus.mFourier n y := by
  rw [heatOp_basis, heatCoeff_eq_exp_lapEig]
  filter_upwards [Lp.coeFn_smul (((Real.exp (t * lapEig d n) : ℝ) : ℂ)) (fourierBasis d n),
    fourierBasis_ae d n] with y h1 h2
  rw [h1, Pi.smul_apply, h2, smul_eq_mul]

end

end HeatSpectrumBridge
