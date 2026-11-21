/-
The heat trace of the flat torus as a statement about an OPERATOR.
Fifth Lean file of the project; check with `cd lean && ./check_heat_operator.sh`.

Own text of this project (not part of the archive of Levent Alpöge). It USES, with attribution,
definitions and theorems from two files of the Lean archive published with
https://alpo.ge/remark.pdf by Levent Alpöge (ported to Lean 4.29.0 / Mathlib v4.29.0, see the
headers of `GroundTheory/AutomorphicForms/HilbertSchmidt.lean` and `.../TraceClass.lean` in
`lean/ports/alpoge-rh/`): `IsHilbertSchmidt`, `isHilbertSchmidt_iff`, `IsTraceClass`, `isTraceClass_comp`,
`trace`, `IsTraceClass.hasSum_trace`. All credit for those belongs to their author.

WHAT IS PROVED. For a Hilbert basis `b` of a complex Hilbert space and a bounded family `a`,
`diagOp b a ha` is the bounded operator that is diagonal in `b` with entries `a`. On
`L²((ℝ/ℤ)^d)` (product Haar probability measure) with the Fourier basis `mFourierBasis` of Mathlib, `heatOp d t` is the
diagonal operator with entries `exp(-4π² t |n|²)`, `n ∈ ℤ^d`, `t ≥ 0`. Then: `heatOp d s ∘ heatOp d t
= heatOp d (s+t)`; for `t > 0` it is Hilbert–Schmidt and trace class, and its trace (in the sense
of the archive: the sum of the diagonal matrix entries in a Hilbert basis) is
`∑_n exp(-4π² t |n|²)`, which equals `heatTorus d (4π² t) 0` of the second project file.

WHAT IS NOT PROVED AND NOT CLAIMED. `heatOp d t` is BY DEFINITION the diagonal operator in the
Fourier basis. That it is the heat semigroup `e^{tΔ}` of the (unbounded) Laplace–Beltrami operator
of the flat torus, or that it is the integral operator with the periodised Gaussian kernel, is NOT
part of any statement here. No Laplace operator occurs in this file.
-/
import Mathlib
import GroundTheory.AutomorphicForms.HilbertSchmidt
import GroundTheory.AutomorphicForms.TraceClass
import CorrelationsToGeometryReal

namespace HeatTraceOperator

open scoped ENNReal InnerProductSpace
open GroundTheory.Automorphic

noncomputable section

/-! ### Diagonal operators in a Hilbert basis -/

section Diagonal

variable {ι : Type*}

/-- Multiplying a square-summable family by a bounded family gives a square-summable family. -/
theorem memℓp_mul {a : ι → ℂ} (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (f : lp (fun _ : ι => ℂ) 2) :
    Memℓp (fun i => a i * f i) 2 := by
  obtain ⟨C, hC⟩ := ha
  have h1 : Memℓp (fun i => (C : ℂ) * f i) 2 := (lp.memℓp f).const_mul _
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  refine memℓp_gen ?_
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) _) (fun i => ?_)
    ((memℓp_gen_iff hp).1 h1)
  refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le
  rw [norm_mul, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right ((hC i).trans (Real.le_norm_self C)) (norm_nonneg _)

/-- The multiplication operator on `ℓ²(ι, ℂ)` by a bounded family `a`. -/
def mulL2 (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun f => ⟨fun i => a i * f i, memℓp_mul ha f⟩
      map_add' := fun f g => by
        ext i
        show a i * (f + g) i = a i * f i + a i * g i
        rw [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        ext i
        show a i * (c • f) i = c * (a i * f i)
        rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm] }
    (by
      obtain ⟨C, hC⟩ := ha
      have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
      refine ⟨‖C‖, fun f => ?_⟩
      refine lp.norm_le_of_forall_sum_le hp (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun s => ?_)
      have h2 : ‖(C : ℂ) • f‖ = ‖C‖ * ‖f‖ := by rw [norm_smul, Complex.norm_real]
      rw [← h2]
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) (lp.sum_rpow_le_norm_rpow hp _ s)
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp.le
      show ‖a i * f i‖ ≤ ‖((C : ℂ) • f) i‖
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right ((hC i).trans (Real.le_norm_self C)) (norm_nonneg _))

theorem mulL2_apply (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (f : lp (fun _ : ι => ℂ) 2)
    (i : ι) : mulL2 a ha f i = a i * f i := rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The diagonal operator** of a bounded family `a` in a Hilbert basis `b`: conjugate the
    multiplication operator on `ℓ²` by the coordinate isometry `b.repr`. -/
def diagOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) : H →L[ℂ] H :=
  (b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((mulL2 a ha).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem diagOp_apply (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (x : H) : diagOp b a ha x = b.repr.symm (mulL2 a ha (b.repr x)) := rfl

theorem diagOp_congr (b : HilbertBasis ι ℂ H) {a a' : ι → ℂ} (h : a = a')
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (ha' : ∃ C : ℝ, ∀ i, ‖a' i‖ ≤ C) :
    diagOp b a ha = diagOp b a' ha' := by
  subst h; rfl

/-- The basis vectors are eigenvectors: `D (b i) = a i • b i`. -/
theorem diagOp_basis (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (i : ι) : diagOp b a ha (b i) = a i • b i := by
  classical
  rw [diagOp_apply, b.repr_self]
  have h : mulL2 a ha (lp.single 2 i (1 : ℂ)) = a i • lp.single 2 i (1 : ℂ) := by
    ext j
    rw [mulL2_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i
    · rw [hj]
    · rw [lp.single_apply_ne _ _ _ hj, mul_zero, mul_zero]
  rw [h, map_smul, b.repr_symm_single]

/-- The diagonal matrix entries: `⟪b i, D (b i)⟫ = a i`. -/
theorem inner_diagOp_basis (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (i : ι) : ⟪b i, diagOp b a ha (b i)⟫_ℂ = a i := by
  rw [diagOp_basis, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
  simp

/-- Diagonal operators in the same basis compose by multiplying the entries. -/
theorem diagOp_comp (b : HilbertBasis ι ℂ H) (a a' : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (ha' : ∃ C : ℝ, ∀ i, ‖a' i‖ ≤ C) (haa' : ∃ C : ℝ, ∀ i, ‖a i * a' i‖ ≤ C) :
    (diagOp b a ha).comp (diagOp b a' ha') = diagOp b (fun i => a i * a' i) haa' := by
  ext x
  rw [ContinuousLinearMap.comp_apply, diagOp_apply, diagOp_apply, diagOp_apply,
    LinearIsometryEquiv.apply_symm_apply]
  congr 1
  ext i
  rw [mulL2_apply, mulL2_apply, mulL2_apply, mul_assoc]

/-- A diagonal operator with square-summable entries is Hilbert–Schmidt (criterion
    `isHilbertSchmidt_iff` of the archive, in the basis `b`). -/
theorem isHilbertSchmidt_diagOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (hs : ∑' i, ‖a i‖ₑ ^ 2 < ∞) :
    IsHilbertSchmidt (diagOp b a ha) := by
  rw [isHilbertSchmidt_iff b]
  have h : ∀ i, ‖diagOp b a ha (b i)‖ₑ = ‖a i‖ₑ := fun i => by
    rw [diagOp_basis, enorm_smul, ← ofReal_norm (b i), b.orthonormal.1 i, ENNReal.ofReal_one,
      mul_one]
  simp only [h]
  exact hs

/-- A diagonal operator whose entries are products of two square-summable families is trace
    class (`isTraceClass_comp` of the archive). -/
theorem isTraceClass_diagOp_mul (b : HilbertBasis ι ℂ H) (c c' : ι → ℂ)
    (hc : ∃ C : ℝ, ∀ i, ‖c i‖ ≤ C) (hc' : ∃ C : ℝ, ∀ i, ‖c' i‖ ≤ C)
    (hcc' : ∃ C : ℝ, ∀ i, ‖c i * c' i‖ ≤ C)
    (hs : ∑' i, ‖c i‖ₑ ^ 2 < ∞) (hs' : ∑' i, ‖c' i‖ₑ ^ 2 < ∞) :
    IsTraceClass (diagOp b (fun i => c i * c' i) hcc') := by
  rw [← diagOp_comp b c c' hc hc']
  exact isTraceClass_comp (isHilbertSchmidt_diagOp b c hc hs) (isHilbertSchmidt_diagOp b c' hc' hs')

/-- The trace of a trace-class diagonal operator is the sum of its entries
    (`IsTraceClass.hasSum_trace` of the archive, in the basis `b`). -/
theorem hasSum_trace_diagOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (hT : IsTraceClass (diagOp b a ha)) :
    HasSum a (GroundTheory.Automorphic.trace (diagOp b a ha)) := by
  have h := hT.hasSum_trace b
  simp only [inner_diagOp_basis] at h
  exact h

end Diagonal

/-! ### The diagonal heat operator of the flat torus -/

section Heat

open MeasureTheory

variable (d : ℕ)

/-- The coefficient `exp(-4π² t |n|²)`, `n ∈ ℤ^d`. -/
def heatCoeff (t : ℝ) (n : Fin d → ℤ) : ℝ :=
  Real.exp (-(4 * Real.pi ^ 2 * t) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)

theorem heatCoeff_pos (t : ℝ) (n : Fin d → ℤ) : 0 < heatCoeff d t n := Real.exp_pos _

theorem heatCoeff_le_one {t : ℝ} (ht : 0 ≤ t) (n : Fin d → ℤ) : heatCoeff d t n ≤ 1 := by
  unfold heatCoeff
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (by positivity))
    (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem heatCoeff_add (s t : ℝ) (n : Fin d → ℤ) :
    heatCoeff d s n * heatCoeff d t n = heatCoeff d (s + t) n := by
  unfold heatCoeff
  rw [← Real.exp_add]
  congr 1
  ring

theorem heatCoeff_bdd {t : ℝ} (ht : 0 ≤ t) :
    ∃ C : ℝ, ∀ n : Fin d → ℤ, ‖((heatCoeff d t n : ℝ) : ℂ)‖ ≤ C :=
  ⟨1, fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg (heatCoeff_pos d t n).le]
    exact heatCoeff_le_one d ht n⟩

/-- Summability of the coefficients over `ℤ^d` for `t > 0` (from `gauss_summable` of the second
    project file). -/
theorem heatCoeff_summable {t : ℝ} (ht : 0 < t) : Summable (heatCoeff d t) :=
  CTG.Reals.gauss_summable (c := 4 * Real.pi ^ 2 * t) (by positivity) d

theorem enorm_sq_heatCoeff (t : ℝ) (n : Fin d → ℤ) :
    ‖((heatCoeff d t n : ℝ) : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (heatCoeff d (2 * t) n) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (heatCoeff_pos d t n).le,
    ← ENNReal.ofReal_pow (heatCoeff_pos d t n).le, sq, heatCoeff_add, two_mul]

theorem heatCoeff_sq_summable {t : ℝ} (ht : 0 < t) :
    ∑' n : Fin d → ℤ, ‖((heatCoeff d t n : ℝ) : ℂ)‖ₑ ^ 2 < ∞ := by
  simp only [enorm_sq_heatCoeff]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (heatCoeff_pos d (2 * t) n).le)
    (heatCoeff_summable d (by positivity))]
  exact ENNReal.ofReal_lt_top

/-- The Hilbert space `L²((ℝ/ℤ)^d)`, with respect to the product of the Haar probability measures
    of the circles (the measure that `Mathlib.Analysis.Fourier.AddCircleMulti` uses locally as
    `volume`; it is `flatTorusMeasure d` of the second project file). -/
abbrev L2Torus : Type :=
  Lp ℂ 2 (Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)))

/-- The Fourier basis of Mathlib (`UnitAddTorus.mFourierBasis`), indexed by `ℤ^d`. -/
def fourierBasis : HilbertBasis (Fin d → ℤ) ℂ (L2Torus d) := UnitAddTorus.mFourierBasis

/-- **The diagonal heat operator** `T_t` on `L²((ℝ/ℤ)^d)`: BY DEFINITION the bounded operator that
    is diagonal in the Fourier basis `mFourierBasis` with entries `exp(-4π² t |n|²)`. (That this is
    `e^{tΔ}` is not part of the definition and is not proved in this file.) -/
def heatOp (t : ℝ) (ht : 0 ≤ t) : L2Torus d →L[ℂ] L2Torus d :=
  diagOp (fourierBasis d) (fun n => ((heatCoeff d t n : ℝ) : ℂ)) (heatCoeff_bdd d ht)

theorem heatOp_congr {s t : ℝ} (h : s = t) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatOp d s hs = heatOp d t ht := by
  subst h; rfl

/-- The Fourier modes are eigenvectors of `T_t` with eigenvalues `exp(-4π² t |n|²)`. -/
theorem heatOp_basis (t : ℝ) (ht : 0 ≤ t) (n : Fin d → ℤ) :
    heatOp d t ht (fourierBasis d n) = ((heatCoeff d t n : ℝ) : ℂ) • fourierBasis d n :=
  diagOp_basis (fourierBasis d) _ _ n

/-- **(b) Semigroup property** of the diagonal operators: `T_s ∘ T_t = T_{s+t}`. -/
theorem heatOp_comp {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (heatOp d s hs).comp (heatOp d t ht) = heatOp d (s + t) (add_nonneg hs ht) := by
  unfold heatOp
  have hb : ∃ C : ℝ, ∀ n : Fin d → ℤ,
      ‖((heatCoeff d s n : ℝ) : ℂ) * ((heatCoeff d t n : ℝ) : ℂ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := heatCoeff_bdd d (add_nonneg hs ht)
    exact ⟨C, fun n => by rw [← Complex.ofReal_mul, heatCoeff_add]; exact hC n⟩
  rw [diagOp_comp (fourierBasis d) _ _ _ _ hb]
  exact diagOp_congr (fourierBasis d) (funext fun n => by rw [← Complex.ofReal_mul, heatCoeff_add]) _ _

/-- **(a)** For `t > 0` the operator `T_t` is Hilbert–Schmidt. -/
theorem heatOp_isHilbertSchmidt {t : ℝ} (ht : 0 < t) : IsHilbertSchmidt (heatOp d t ht.le) :=
  isHilbertSchmidt_diagOp (fourierBasis d) (fun n => ((heatCoeff d t n : ℝ) : ℂ))
    (heatCoeff_bdd d ht.le) (heatCoeff_sq_summable d ht)

/-- **(c)** For `t > 0` the operator `T_t = T_{t/2} ∘ T_{t/2}` is trace class. -/
theorem heatOp_isTraceClass {t : ℝ} (ht : 0 < t) : IsTraceClass (heatOp d t ht.le) := by
  have h2 : 0 < t / 2 := by positivity
  have e : heatOp d t ht.le = (heatOp d (t / 2) h2.le).comp (heatOp d (t / 2) h2.le) := by
    rw [heatOp_comp d h2.le h2.le]
    exact heatOp_congr d (add_halves t).symm _ _
  rw [e]
  exact isTraceClass_comp (heatOp_isHilbertSchmidt d h2) (heatOp_isHilbertSchmidt d h2)

/-- **(d)** The coefficients sum to the trace of `T_t`. -/
theorem hasSum_trace_heatOp {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : Fin d → ℤ => ((heatCoeff d t n : ℝ) : ℂ))
      (GroundTheory.Automorphic.trace (heatOp d t ht.le)) :=
  hasSum_trace_diagOp (fourierBasis d) (fun n => ((heatCoeff d t n : ℝ) : ℂ))
    (heatCoeff_bdd d ht.le) (heatOp_isTraceClass d ht)

/-- **(d) The heat trace as the trace of an operator:**
    `trace T_t = ∑_{n ∈ ℤ^d} exp(-4π² t |n|²)` for `t > 0`. -/
theorem trace_heatOp {t : ℝ} (ht : 0 < t) :
    GroundTheory.Automorphic.trace (heatOp d t ht.le) =
      ((∑' n : Fin d → ℤ, Real.exp (-(4 * Real.pi ^ 2 * t) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  exact (hasSum_trace_heatOp d ht).tsum_eq.symm

/-- **(e)** Connection with the second project file: `trace T_t = heatTorus d (4π² t) 0`, the
    Fourier-series heat kernel of the flat torus on the diagonal (in the convention of that file,
    `c = 2π² · variance`, this is the kernel of variance `2t` at `0`). -/
theorem trace_heatOp_eq_heatTorus {t : ℝ} (ht : 0 < t) :
    GroundTheory.Automorphic.trace (heatOp d t ht.le) =
      ((CTG.Reals.heatTorus d (4 * Real.pi ^ 2 * t) 0 : ℝ) : ℂ) := by
  rw [trace_heatOp d ht, CTG.Reals.heatTorus, CTG.Reals.cosSeries_zero]

end Heat

end

end HeatTraceOperator
