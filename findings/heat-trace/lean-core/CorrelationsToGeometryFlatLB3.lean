/-
Twenty-fifth file: fourth-order version of the flat core of `thm:LB`.  Imports `CorrelationsToGeometryFlatLB2`
(compiled module under `.tools/leanbuild`); namespace `CTG.FlatLB3`; check with `./check_flat_lb3.sh`.
For a radial kernel with Lebesgue measure (odd moments vanish, `radial_odd`) and `f` of class `C⁴` with fourth
derivative bounded by `M₄`: `avgOp_expansion4` (`|A_c f − f − (c²/2) m₂ Δf| ≤ M₄ c⁴ μ₄/(24 K₀)`), `flat_LB4`
(error `M₄ ξ² μ₄/(12 m₂ K₀)`).  Flat conformal time-dependent metric `g_τ = a(τ)² · Euclidean`:
`conformal_LB4`, `conformal_dq4` (two times, `ξ²/|η|`), `conformal_dq_uniform` (for `a` differentiable with
`|a'| ≤ L_a`: error `C ξ²` uniformly in `η`), `conformal_dq_min` (the minimum of both).
In this flat case with constant density the error is `ξ² min{C₁/|η|, C₂}`, smaller than the `min{ξ, ξ²/|η|}` stated
in the paper for the general case.
NOT formalised: general constant-coefficient metrics `G_τ`, a time-dependent test function, the identification with
the population operator of the N-point files, anything on curved manifolds or with a non-constant density.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatLB2

open MeasureTheory Set Laplacian InnerProductSpace
open CTG.FlatLB CTG.FlatLB2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatLB3

variable {n : ℕ}

/-! ### One-dimensional Taylor bound of order four -/

theorem taylor4 (φ d₁ d₂ d₃ d₄ : ℝ → ℝ) (h1 : ∀ t, HasDerivAt φ (d₁ t) t)
    (h2 : ∀ t, HasDerivAt d₁ (d₂ t) t) (h3 : ∀ t, HasDerivAt d₂ (d₃ t) t)
    (h4 : ∀ t, HasDerivAt d₃ (d₄ t) t) (B : ℝ) (hB : ∀ t ∈ Icc (0:ℝ) 1, |d₄ t| ≤ B) :
    |φ 1 - φ 0 - d₁ 0 - d₂ 0 / 2 - d₃ 0 / 6| ≤ B / 24 := by
  have s1 := step_bound (fun t => d₃ t - d₃ 0) d₄ (fun t => (h4 t).sub_const _) (by simp) B 0
    (fun t ht => by simpa using hB t ht)
  have s2 := step_bound (fun t => d₂ t - d₂ 0 - t * d₃ 0) (fun t => d₃ t - d₃ 0)
    (fun t => (((h3 t).sub_const (d₂ 0)).sub ((hasDerivAt_id t).mul_const (d₃ 0))).congr_deriv
      (by simp)) (by simp) (B / (0 + 1)) 1 (fun t ht => by
        have := s1 t ht; norm_num at this ⊢; linarith)
  have s3 := step_bound (fun t => d₁ t - d₁ 0 - t * d₂ 0 - t ^ 2 / 2 * d₃ 0)
    (fun t => d₂ t - d₂ 0 - t * d₃ 0)
    (fun t => by
      have h := (((h2 t).sub_const (d₁ 0)).sub ((hasDerivAt_id t).mul_const (d₂ 0))).sub
        (((hasDerivAt_pow 2 t).div_const 2).mul_const (d₃ 0))
      exact h.congr_deriv (by first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp))
    (by simp) (B / (0 + 1) / (1 + 1)) 2 (fun t ht => by
        have := s2 t ht; norm_num at this ⊢; linarith)
  have s4 := step_bound (fun t => φ t - φ 0 - t * d₁ 0 - t ^ 2 / 2 * d₂ 0 - t ^ 3 / 6 * d₃ 0)
    (fun t => d₁ t - d₁ 0 - t * d₂ 0 - t ^ 2 / 2 * d₃ 0)
    (fun t => by
      have h := ((((h1 t).sub_const (φ 0)).sub ((hasDerivAt_id t).mul_const (d₁ 0))).sub
        (((hasDerivAt_pow 2 t).div_const 2).mul_const (d₂ 0))).sub
        (((hasDerivAt_pow 3 t).div_const 6).mul_const (d₃ 0))
      exact h.congr_deriv (by first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp))
    (by simp) (B / (0 + 1) / (1 + 1) / (2 + 1)) 3 (fun t ht => by
        have := s3 t ht; norm_num at this ⊢; linarith)
  have := s4 1 ⟨zero_le_one, le_rfl⟩
  have e : φ 1 - φ 0 - 1 * d₁ 0 - 1 ^ 2 / 2 * d₂ 0 - 1 ^ 3 / 6 * d₃ 0
      = φ 1 - φ 0 - d₁ 0 - d₂ 0 / 2 - d₃ 0 / 6 := by ring
  simp only at this
  rw [e] at this
  refine this.trans (le_of_eq ?_)
  first | (norm_num; ring) | norm_num

/-! ### Directional iterated derivatives of a `C⁴` function -/

/-- `D k y v = D^k f(y)[v,…,v]`. -/
abbrev Dk (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) (y v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  iteratedFDeriv ℝ k f y (fun _ => v)

theorem line_iter {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) (k : ℕ) (hk : k < 4)
    (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Dk f k (x + s • v) v) (Dk f (k + 1) (x + t • v) v) t := by
  have hd : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast hk)
  have hl := line_deriv hd x v t
  have hc := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => EuclideanSpace ℝ (Fin n)) ℝ
    (fun _ => v)).hasFDerivAt.comp_hasDerivAt t hl
  refine hc.congr_deriv ?_
  rw [ContinuousMultilinearMap.apply_apply]
  first | rfl | exact (iteratedFDeriv_succ_apply_left (fun _ => v)).symm

theorem Dk_zero (f : EuclideanSpace ℝ (Fin n) → ℝ) (y v : EuclideanSpace ℝ (Fin n)) :
    Dk f 0 y v = f y := iteratedFDeriv_zero_apply _

theorem Dk_smul (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) (y v : EuclideanSpace ℝ (Fin n))
    (c : ℝ) : Dk f k y (c • v) = c ^ k * Dk f k y v := by
  show iteratedFDeriv ℝ k f y (fun _ => c • v) = _
  rw [show (fun _ : Fin k => c • v) = fun i => (fun _ => c) i • (fun _ => v) i from rfl,
    ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

theorem Dk_neg_odd (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) (hk : Odd k)
    (y v : EuclideanSpace ℝ (Fin n)) : Dk f k y (-v) = -Dk f k y v := by
  rw [show -v = (-1 : ℝ) • v by simp, Dk_smul, hk.neg_one_pow]; ring

theorem Dk_bound (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) (y v : EuclideanSpace ℝ (Fin n)) :
    |Dk f k y v| ≤ ‖iteratedFDeriv ℝ k f y‖ * ‖v‖ ^ k := by
  rw [← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ k f y).le_opNorm _).trans (le_of_eq ?_)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem Dk_cont (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    Continuous fun v => Dk f k y v :=
  (iteratedFDeriv ℝ k f y).cont.comp (continuous_pi fun _ => continuous_id)

/-- The Taylor remainder of order three at scale `c` in direction `z`. -/
def rem (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f (x + c • z) - f x - c * Dk f 1 x z - c ^ 2 / 2 * Dk f 2 x z - c ^ 3 / 6 * Dk f 3 x z

/-- Its derivative in the scale `c`. -/
def drem (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Dk f 1 (x + c • z) z - Dk f 1 x z - c * Dk f 2 x z - c ^ 2 / 2 * Dk f 3 x z

theorem rem_bound {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (x z : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    |rem f x c z| ≤ M₄ * ‖z‖ ^ 4 * |c| ^ 4 / 24 := by
  have h := taylor4 (fun s => Dk f 0 (x + s • (c • z)) (c • z))
    (fun s => Dk f 1 (x + s • (c • z)) (c • z)) (fun s => Dk f 2 (x + s • (c • z)) (c • z))
    (fun s => Dk f 3 (x + s • (c • z)) (c • z)) (fun s => Dk f 4 (x + s • (c • z)) (c • z))
    (line_iter hf 0 (by norm_num) x _) (line_iter hf 1 (by norm_num) x _)
    (line_iter hf 2 (by norm_num) x _) (line_iter hf 3 (by norm_num) x _)
    (M₄ * ‖c • z‖ ^ 4) (fun t _ => (Dk_bound f 4 _ _).trans
      (mul_le_mul_of_nonneg_right (hM _) (by positivity)))
  simp only [one_smul, zero_smul, add_zero, Dk_zero, Dk_smul, norm_smul, Real.norm_eq_abs] at h
  unfold rem
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq (by ring)))
  ring_nf

theorem drem_bound {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (x z : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    |drem f x c z| ≤ M₄ * ‖z‖ ^ 4 * |c| ^ 3 / 6 := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp [drem]
  have h := taylor3 (fun s => Dk f 1 (x + s • (c • z)) (c • z))
    (fun s => Dk f 2 (x + s • (c • z)) (c • z)) (fun s => Dk f 3 (x + s • (c • z)) (c • z))
    (fun s => Dk f 4 (x + s • (c • z)) (c • z))
    (line_iter hf 1 (by norm_num) x _) (line_iter hf 2 (by norm_num) x _)
    (line_iter hf 3 (by norm_num) x _)
    (M₄ * ‖c • z‖ ^ 4) (fun t _ => (Dk_bound f 4 _ _).trans
      (mul_le_mul_of_nonneg_right (hM _) (by positivity)))
  simp only [one_smul, zero_smul, add_zero, Dk_smul, norm_smul, Real.norm_eq_abs] at h
  have e : c ^ 1 * Dk f 1 (x + c • z) z - c ^ 1 * Dk f 1 x z - c ^ 2 * Dk f 2 x z
      - c ^ 3 * Dk f 3 x z / 2 = c * drem f x c z := by unfold drem; ring
  rw [e, abs_mul] at h
  have hc0 : 0 < |c| := abs_pos.2 hc
  have h' : |c| * |drem f x c z| ≤ |c| * (M₄ * ‖z‖ ^ 4 * |c| ^ 3 / 6) := by
    refine h.trans (le_of_eq ?_); ring
  exact le_of_mul_le_mul_left h' hc0

theorem rem_hasDerivAt {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f)
    (x z : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    HasDerivAt (fun c => rem f x c z) (drem f x c z) c := by
  have h0 := line_iter hf 0 (by norm_num) x z c
  simp only [Dk_zero] at h0
  have h := ((((h0.sub_const (f x)).sub ((hasDerivAt_id c).mul_const (Dk f 1 x z))).sub
    (((hasDerivAt_pow 2 c).div_const 2).mul_const (Dk f 2 x z))).sub
    (((hasDerivAt_pow 3 c).div_const 6).mul_const (Dk f 3 x z)))
  refine h.congr_deriv ?_
  unfold drem
  first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp

theorem rem_cont {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f)
    (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) : Continuous fun z => rem f x c z := by
  have hfc : Continuous f := hf.continuous
  unfold rem
  exact ((((hfc.comp (continuous_const.add (continuous_const.smul continuous_id))).sub
    continuous_const).sub (continuous_const.mul (Dk_cont f 1 x))).sub
    (continuous_const.mul (Dk_cont f 2 x))).sub (continuous_const.mul (Dk_cont f 3 x))

/-! ### Radial kernels: odd functions integrate to zero -/

theorem radial_odd (h : ℝ → ℝ) (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ∀ z, F (-z) = -F z) :
    ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * F z = 0 := by
  set e := LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n)) with he
  have hmp : MeasurePreserving e volume volume := LinearIsometryEquiv.measurePreserving e
  have hcomp := hmp.integral_comp e.toHomeomorph.measurableEmbedding
    (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖ * F z)
  have hneg : (fun z : EuclideanSpace ℝ (Fin n) => h ‖e z‖ * F (e z))
      = fun z => -(h ‖z‖ * F z) := by
    funext z; simp [he, hF]
  have h2 : ∫ z : EuclideanSpace ℝ (Fin n), h ‖e z‖ * F (e z)
      = ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * F z := hcomp
  rw [hneg, integral_neg] at h2
  linarith

theorem laplacian_sum (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ i, fderiv ℝ (fderiv ℝ f) x (eb i) (eb i) = Δ f x := by
  have hL := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)) x
  refine Eq.trans ?_ hL.symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

/-! ### (1) The exact second-order expansion with remainder `rem` and the bound of order `c⁴` -/

/-- HYPOTHESES on the radial kernel collected: `Kern` and integrability of `|z| k` and `|z|⁴ k`. -/
structure RadK (n : ℕ) (h : ℝ → ℝ) (K₀ m₂ μ₃ μ₄ : ℝ) : Prop where
  kern : Kern n volume (fun z => h ‖z‖) K₀ m₂ μ₃
  int1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ * h ‖z‖)
  int4 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 4 * h ‖z‖)
  mom4 : ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 4 * h ‖z‖ = μ₄

theorem expansion {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖ * rem f x c z)
    ∧ ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * f (x + c • z)
      = K₀ * f x + c ^ 2 / 2 * (m₂ * K₀ * Δ f x)
        + ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * rem f x c z := by
  have hK := hk.kern
  have hh0 : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ h ‖z‖ := hK.nonneg
  have hkm := hK.int0.aestronglyMeasurable
  -- the moment terms
  have I1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖ * Dk f 1 x z) :=
    (hk.int1.const_mul ‖iteratedFDeriv ℝ 1 f x‖).mono' (hkm.mul (Dk_cont f 1 x).aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 z)]
        have := Dk_bound f 1 x z
        rw [pow_one] at this
        nlinarith [abs_nonneg (Dk f 1 x z), hh0 z, norm_nonneg z])
  have I3 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖ * Dk f 3 x z) :=
    (hK.int3.const_mul ‖iteratedFDeriv ℝ 3 f x‖).mono' (hkm.mul (Dk_cont f 3 x).aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 z)]
        have := Dk_bound f 3 x z
        nlinarith [abs_nonneg (Dk f 3 x z), hh0 z, pow_nonneg (norm_nonneg z) 3])
  have hD2 : ∀ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * Dk f 2 x z
      = ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (eb j) (eb i) * (z i * z j * h ‖z‖) := fun z => by
    rw [show Dk f 2 x z = iteratedFDeriv ℝ 2 f x (fun _ => z) from rfl, ← hess_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨I2', E2⟩ := integral_second hK (fun i j => fderiv ℝ (fderiv ℝ f) x (eb j) (eb i))
  have I2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖ * Dk f 2 x z) :=
    I2'.congr (ae_of_all _ fun z => (hD2 z).symm)
  have E2' : ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * Dk f 2 x z = m₂ * K₀ * Δ f x := by
    rw [integral_congr_ae (ae_of_all _ hD2), E2, laplacian_sum]
  have E1 : ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * Dk f 1 x z = 0 :=
    radial_odd h _ fun z => Dk_neg_odd f 1 (by decide) x z
  have E3 : ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * Dk f 3 x z = 0 :=
    radial_odd h _ fun z => Dk_neg_odd f 3 (by decide) x z
  -- the remainder
  have IR : Integrable (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖ * rem f x c z) :=
    (hk.int4.const_mul (M₄ * |c| ^ 4 / 24)).mono'
      (hkm.mul (rem_cont hf x c).aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 z)]
        have := rem_bound hf hM x z c
        calc h ‖z‖ * |rem f x c z| ≤ h ‖z‖ * (M₄ * ‖z‖ ^ 4 * |c| ^ 4 / 24) :=
              mul_le_mul_of_nonneg_left this (hh0 z)
          _ = M₄ * |c| ^ 4 / 24 * (‖z‖ ^ 4 * h ‖z‖) := by ring)
  refine ⟨IR, ?_⟩
  have hpt : ∀ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * f (x + c • z)
      = (((h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z)) + c ^ 2 / 2 * (h ‖z‖ * Dk f 2 x z))
        + c ^ 3 / 6 * (h ‖z‖ * Dk f 3 x z)) + h ‖z‖ * rem f x c z := fun z => by
    unfold rem; ring
  rw [integral_congr_ae (ae_of_all _ hpt)]
  have J0 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖ * f x) := hK.int0.mul_const _
  have A1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z)) := J0.add (I1.const_mul c)
  have A2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z) + c ^ 2 / 2 * (h ‖z‖ * Dk f 2 x z)) :=
    A1.add (I2.const_mul _)
  have A3 : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z) + c ^ 2 / 2 * (h ‖z‖ * Dk f 2 x z)
        + c ^ 3 / 6 * (h ‖z‖ * Dk f 3 x z)) := A2.add (I3.const_mul _)
  rw [integral_add A3 IR, integral_add A2 (I3.const_mul _), integral_add A1 (I2.const_mul _),
    integral_add J0 (I1.const_mul c), integral_mul_const, integral_const_mul, integral_const_mul,
    integral_const_mul, E1, E2', E3, hK.mass]
  ring

/-- **(1) Order `c⁴`**: `|A_c f(x) − f(x) − (c²/2) m₂ Δf(x)| ≤ M₄ c⁴ μ₄/(24 K₀)`. -/
theorem avgOp_expansion4 {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    |avgOp volume (fun z => h ‖z‖) c f x - f x - c ^ 2 / 2 * m₂ * Δ f x|
      ≤ M₄ * c ^ 4 * μ₄ / (24 * K₀) := by
  obtain ⟨IR, E⟩ := expansion hk hf hM x c
  have hK₀ := hk.kern.mass_pos
  have hh0 : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ h ‖z‖ := hk.kern.nonneg
  have hR : |∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * rem f x c z| ≤ M₄ * c ^ 4 / 24 * μ₄ := by
    calc _ ≤ ∫ z : EuclideanSpace ℝ (Fin n), |h ‖z‖ * rem f x c z| := abs_integral_le_integral_abs
      _ ≤ ∫ z : EuclideanSpace ℝ (Fin n), M₄ * c ^ 4 / 24 * (‖z‖ ^ 4 * h ‖z‖) :=
          integral_mono IR.abs (hk.int4.const_mul _) (fun z => by
            rw [abs_mul, abs_of_nonneg (hh0 z)]
            have := rem_bound hf hM x z c
            rw [pow_abs] at this
            calc h ‖z‖ * |rem f x c z| ≤ h ‖z‖ * (M₄ * ‖z‖ ^ 4 * |c ^ 4| / 24) :=
                  mul_le_mul_of_nonneg_left this (hh0 z)
              _ = M₄ * c ^ 4 / 24 * (‖z‖ ^ 4 * h ‖z‖) := by
                  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ 4)]; ring)
      _ = M₄ * c ^ 4 / 24 * μ₄ := by rw [integral_const_mul, hk.mom4]
  unfold avgOp
  rw [E, hk.kern.mass]
  have e : (K₀ * f x + c ^ 2 / 2 * (m₂ * K₀ * Δ f x)
        + ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * rem f x c z) / K₀ - f x
      - c ^ 2 / 2 * m₂ * Δ f x = (∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * rem f x c z) / K₀ := by
    first | (field_simp; ring) | field_simp | ring
  rw [e, abs_div, abs_of_pos hK₀]
  calc _ ≤ M₄ * c ^ 4 / 24 * μ₄ / K₀ := div_le_div_of_nonneg_right hR hK₀.le
    _ = M₄ * c ^ 4 * μ₄ / (24 * K₀) := by first | (field_simp; ring) | field_simp | ring

/-- **(1') Normalised form**: `|(2/(m₂ ξ²))(f − A_ξ f) + Δf| ≤ M₄ ξ² μ₄/(12 m₂ K₀)`. -/
theorem flat_LB4 {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (ξ : ℝ) (hξ : 0 < ξ)
    (x : EuclideanSpace ℝ (Fin n)) :
    |2 / (m₂ * ξ ^ 2) * (f x - avgOp volume (fun z => h ‖z‖) ξ f x) + Δ f x|
      ≤ M₄ * ξ ^ 2 * μ₄ / (12 * m₂ * K₀) := by
  have hE := avgOp_expansion4 hk hf hM x ξ
  have hK₀ := hk.kern.mass_pos
  have hc : 0 < 2 / (m₂ * ξ ^ 2) := by positivity
  have e : 2 / (m₂ * ξ ^ 2) * (f x - avgOp volume (fun z => h ‖z‖) ξ f x) + Δ f x
      = -(2 / (m₂ * ξ ^ 2)) * (avgOp volume (fun z => h ‖z‖) ξ f x - f x
          - ξ ^ 2 / 2 * m₂ * Δ f x) := by
    first | (field_simp; ring) | field_simp | ring
  rw [e, abs_mul, abs_neg, abs_of_pos hc]
  calc _ ≤ 2 / (m₂ * ξ ^ 2) * (M₄ * ξ ^ 4 * μ₄ / (24 * K₀)) := mul_le_mul_of_nonneg_left hE hc.le
    _ = M₄ * ξ ^ 2 * μ₄ / (12 * m₂ * K₀) := by first | (field_simp; ring) | field_simp | ring

/-! ### Conformal metric `a²·euclidean`: the remainder form of `L^τ + Δ_{g_τ}` -/

/-- `L^τ_ξ f + Δ_{g_τ} f = −(2/(m₂ K₀ ξ²)) ∫ k(z) rem(ξ/a, z) dz` (exact). -/
theorem conformal_rem {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Lconf h m₂ a ξ f x + Δ f x / a ^ 2
      = -(2 / (m₂ * K₀ * ξ ^ 2)) * ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖ * rem f x (ξ / a) z := by
  obtain ⟨IR, E⟩ := expansion hk hf hM x (ξ / a)
  have hK₀ := hk.kern.mass_pos
  unfold Lconf
  rw [Pconf_eq h ha hξ, avgOp, E, hk.kern.mass]
  first | (field_simp; ring) | field_simp | ring

/-- **(1'') Conformal metric, order `ξ²`**: `|L^τ_ξ f + Δ_{g_τ} f| ≤ M₄ ξ² μ₄/(12 m₂ K₀ a₀⁴)`. -/
theorem conformal_LB4 {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) {a a₀ ξ : ℝ} (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (hξ : 0 < ξ) (x : EuclideanSpace ℝ (Fin n)) :
    |Lconf h m₂ a ξ f x + Δ f x / a ^ 2| ≤ M₄ * ξ ^ 2 * μ₄ / (12 * m₂ * K₀ * a₀ ^ 4) := by
  have ha0 : 0 < a := lt_of_lt_of_le ha₀ ha
  have hK₀ := hk.kern.mass_pos
  have hμ₄ : 0 ≤ μ₄ := by
    rw [← hk.mom4]; exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hL := flat_LB4 hk hm₂ hf hM (ξ / a) (div_pos hξ ha0) x
  have e : Lconf h m₂ a ξ f x + Δ f x / a ^ 2
      = (2 / (m₂ * (ξ / a) ^ 2) * (f x - avgOp volume (fun z => h ‖z‖) (ξ / a) f x)
          + Δ f x) / a ^ 2 := by
    unfold Lconf
    rw [Pconf_eq h ha0 hξ]
    first | (field_simp; ring) | field_simp | ring
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < a ^ 2)]
  calc _ ≤ M₄ * (ξ / a) ^ 2 * μ₄ / (12 * m₂ * K₀) / a ^ 2 :=
        div_le_div_of_nonneg_right hL (by positivity)
    _ = M₄ * ξ ^ 2 * μ₄ / (12 * m₂ * K₀ * a ^ 4) := by
        first | (field_simp; ring) | field_simp | ring
    _ ≤ M₄ * ξ ^ 2 * μ₄ / (12 * m₂ * K₀ * a₀ ^ 4) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : a₀ ^ 4 ≤ a ^ 4 := pow_le_pow_left₀ ha₀.le ha 4
        nlinarith [mul_pos (mul_pos (by norm_num : (0:ℝ) < 12) hm₂) hK₀]

/-- **Branch `ξ²/|η|`**. -/
theorem conformal_dq4 {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) {aa ab a₀ ξ η : ℝ}
    (ha₀ : 0 < a₀) (haa : a₀ ≤ aa) (hab : a₀ ≤ ab) (hξ : 0 < ξ) (x : EuclideanSpace ℝ (Fin n)) :
    |(Lconf h m₂ ab ξ f x - Lconf h m₂ aa ξ f x) / η + (Δ f x / ab ^ 2 - Δ f x / aa ^ 2) / η|
      ≤ 2 * (M₄ * ξ ^ 2 * μ₄ / (12 * m₂ * K₀ * a₀ ^ 4)) / |η| := by
  have hb := conformal_LB4 hk hm₂ hf hM hM₄ ha₀ hab hξ x
  have ha := conformal_LB4 hk hm₂ hf hM hM₄ ha₀ haa hξ x
  have e : (Lconf h m₂ ab ξ f x - Lconf h m₂ aa ξ f x) / η + (Δ f x / ab ^ 2 - Δ f x / aa ^ 2) / η
      = ((Lconf h m₂ ab ξ f x + Δ f x / ab ^ 2) - (Lconf h m₂ aa ξ f x + Δ f x / aa ^ 2)) / η := by
    ring
  rw [e, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc _ ≤ |Lconf h m₂ ab ξ f x + Δ f x / ab ^ 2| + |Lconf h m₂ aa ξ f x + Δ f x / aa ^ 2| :=
        abs_sub _ _
    _ ≤ _ := by linarith

/-! ### (2) The branch uniform in `η` -/

/-- Time-Lipschitz bound of the remainder along `c(τ) = ξ/a(τ)`, pointwise in `z`. -/
theorem rem_time_lip {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x z : EuclideanSpace ℝ (Fin n)) (τa τb : ℝ) :
    |rem f x (ξ / a τb) z - rem f x (ξ / a τa) z|
      ≤ M₄ * ‖z‖ ^ 4 * ξ ^ 4 * La / (6 * a₀ ^ 5) * |τb - τa| := by
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hc : ∀ τ, HasDerivAt (fun τ => ξ / a τ) (-(ξ * a' τ) / a τ ^ 2) τ := fun τ => by
    have := (hasDerivAt_const τ ξ).div (hda τ) (hpos τ).ne'
    refine this.congr_deriv ?_; ring
  have hD : ∀ τ, HasDerivAt (fun τ => rem f x (ξ / a τ) z)
      (drem f x (ξ / a τ) z * (-(ξ * a' τ) / a τ ^ 2)) τ := fun τ => by
    have := (rem_hasDerivAt hf x z (ξ / a τ)).comp τ (hc τ)
    exact this
  have hLa0 : 0 ≤ La := (abs_nonneg _).trans (hLa 0)
  have hbd : ∀ τ, ‖drem f x (ξ / a τ) z * (-(ξ * a' τ) / a τ ^ 2)‖
      ≤ M₄ * ‖z‖ ^ 4 * ξ ^ 4 * La / (6 * a₀ ^ 5) := fun τ => by
    have h1 := drem_bound hf hM x z (ξ / a τ)
    have hat := hpos τ
    have hca : |ξ / a τ| ≤ ξ / a₀ := by
      rw [abs_of_pos (div_pos hξ hat)]; exact div_le_div_of_nonneg_left hξ.le ha₀ (ha τ)
    have h2 : |-(ξ * a' τ) / a τ ^ 2| ≤ ξ * La / a₀ ^ 2 := by
      rw [abs_div, abs_neg, abs_mul, abs_of_pos hξ, abs_of_pos (by positivity : (0:ℝ) < a τ ^ 2)]
      calc ξ * |a' τ| / a τ ^ 2 ≤ ξ * La / a τ ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hLa τ) hξ.le) (by positivity)
        _ ≤ ξ * La / a₀ ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ ha₀.le (ha τ) 2)
    rw [Real.norm_eq_abs, abs_mul]
    have h3 : |drem f x (ξ / a τ) z| ≤ M₄ * ‖z‖ ^ 4 * (ξ / a₀) ^ 3 / 6 :=
      h1.trans (by
        have := pow_le_pow_left₀ (abs_nonneg _) hca 3
        have h0 : 0 ≤ M₄ * ‖z‖ ^ 4 := by positivity
        calc M₄ * ‖z‖ ^ 4 * |ξ / a τ| ^ 3 / 6 ≤ M₄ * ‖z‖ ^ 4 * (ξ / a₀) ^ 3 / 6 := by gcongr)
    calc |drem f x (ξ / a τ) z| * |-(ξ * a' τ) / a τ ^ 2|
        ≤ (M₄ * ‖z‖ ^ 4 * (ξ / a₀) ^ 3 / 6) * (ξ * La / a₀ ^ 2) :=
          mul_le_mul h3 h2 (abs_nonneg _) (by positivity)
      _ = M₄ * ‖z‖ ^ 4 * ξ ^ 4 * La / (6 * a₀ ^ 5) := by
          first | (field_simp; ring) | field_simp | ring
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun τ _ => (hD τ).hasDerivWithinAt) (fun τ _ => hbd τ) (mem_univ τa) (mem_univ τb)
  simpa [Real.norm_eq_abs] using this

/-- **(2) Branch uniform in `η`**: for a differentiable conformal factor `a(τ) ≥ a₀ > 0` with
`|a'| ≤ L_a` (HYPOTHESES), `|Δ_η(L^τ_ξ f) + Δ_η(Δ_{g_τ} f)| ≤ M₄ μ₄ L_a ξ²/(3 m₂ K₀ a₀⁵)`. -/
theorem conformal_dq_uniform {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : EuclideanSpace ℝ (Fin n)) (τa τb : ℝ)
    (hne : τb ≠ τa) :
    |(Lconf h m₂ (a τb) ξ f x - Lconf h m₂ (a τa) ξ f x) / (τb - τa)
        + (Δ f x / a τb ^ 2 - Δ f x / a τa ^ 2) / (τb - τa)|
      ≤ M₄ * μ₄ * La * ξ ^ 2 / (3 * m₂ * K₀ * a₀ ^ 5) := by
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hK₀ := hk.kern.mass_pos
  have hh0 : ∀ z : EuclideanSpace ℝ (Fin n), 0 ≤ h ‖z‖ := hk.kern.nonneg
  obtain ⟨Ib, -⟩ := expansion hk hf hM x (ξ / a τb)
  obtain ⟨Ia, -⟩ := expansion hk hf hM x (ξ / a τa)
  have rb := conformal_rem hk hm₂ hf hM (hpos τb) hξ x
  have ra := conformal_rem hk hm₂ hf hM (hpos τa) hξ x
  have hη : 0 < |τb - τa| := abs_pos.2 (sub_ne_zero.2 hne)
  have e : (Lconf h m₂ (a τb) ξ f x - Lconf h m₂ (a τa) ξ f x) / (τb - τa)
        + (Δ f x / a τb ^ 2 - Δ f x / a τa ^ 2) / (τb - τa)
      = ((Lconf h m₂ (a τb) ξ f x + Δ f x / a τb ^ 2)
          - (Lconf h m₂ (a τa) ξ f x + Δ f x / a τa ^ 2)) / (τb - τa) := by ring
  rw [e, rb, ra, ← mul_sub, ← integral_sub Ib Ia]
  have hI : |∫ z : EuclideanSpace ℝ (Fin n),
        (h ‖z‖ * rem f x (ξ / a τb) z - h ‖z‖ * rem f x (ξ / a τa) z)|
      ≤ M₄ * ξ ^ 4 * La / (6 * a₀ ^ 5) * |τb - τa| * μ₄ := by
    calc _ ≤ ∫ z : EuclideanSpace ℝ (Fin n),
          |h ‖z‖ * rem f x (ξ / a τb) z - h ‖z‖ * rem f x (ξ / a τa) z| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z : EuclideanSpace ℝ (Fin n),
          M₄ * ξ ^ 4 * La / (6 * a₀ ^ 5) * |τb - τa| * (‖z‖ ^ 4 * h ‖z‖) :=
          integral_mono (Ib.sub Ia).abs (hk.int4.const_mul _) (fun z => by
            rw [← mul_sub, abs_mul, abs_of_nonneg (hh0 z)]
            have := rem_time_lip hf hM hM₄ a a' hda ha₀ ha hLa hξ x z τa τb
            calc h ‖z‖ * |rem f x (ξ / a τb) z - rem f x (ξ / a τa) z|
                ≤ h ‖z‖ * (M₄ * ‖z‖ ^ 4 * ξ ^ 4 * La / (6 * a₀ ^ 5) * |τb - τa|) :=
                  mul_le_mul_of_nonneg_left this (hh0 z)
              _ = _ := by ring)
      _ = _ := by rw [integral_const_mul, hk.mom4]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 / (m₂ * K₀ * ξ ^ 2))]
  rw [div_le_iff₀ hη]
  calc 2 / (m₂ * K₀ * ξ ^ 2) * |∫ z : EuclideanSpace ℝ (Fin n),
        (h ‖z‖ * rem f x (ξ / a τb) z - h ‖z‖ * rem f x (ξ / a τa) z)|
      ≤ 2 / (m₂ * K₀ * ξ ^ 2) * (M₄ * ξ ^ 4 * La / (6 * a₀ ^ 5) * |τb - τa| * μ₄) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M₄ * μ₄ * La * ξ ^ 2 / (3 * m₂ * K₀ * a₀ ^ 5) * |τb - τa| := by
        first | (field_simp; ring) | field_simp | ring

/-- **The combined form**: `|Δ_η(L^τ f) + Δ_η(Δ_{g_τ} f)| ≤ ξ² · min{C₁/|η|, C₂}`. -/
theorem conformal_dq_min {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : EuclideanSpace ℝ (Fin n)) (τa τb : ℝ)
    (hne : τb ≠ τa) :
    |(Lconf h m₂ (a τb) ξ f x - Lconf h m₂ (a τa) ξ f x) / (τb - τa)
        + (Δ f x / a τb ^ 2 - Δ f x / a τa ^ 2) / (τb - τa)|
      ≤ ξ ^ 2 * min (M₄ * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4) / |τb - τa|)
          (M₄ * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)) := by
  have h1 := conformal_dq4 hk hm₂ hf hM hM₄ (η := τb - τa) ha₀ (ha τa) (ha τb) hξ x
  have h2 := conformal_dq_uniform hk hm₂ hf hM hM₄ a a' hda ha₀ ha hLa hξ x τa τb hne
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min (h1.trans (le_of_eq ?_)) (h2.trans (le_of_eq ?_))
  · first | (field_simp; ring) | field_simp | ring
  · first | (field_simp; ring) | field_simp | ring

end CTG.FlatLB3
