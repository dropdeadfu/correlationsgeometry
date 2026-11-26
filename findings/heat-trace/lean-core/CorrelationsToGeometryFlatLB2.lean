/-
Twenty-fourth file: continuation of the flat core of `thm:LB`.  Imports `CorrelationsToGeometryFlatLB` (compiled
module under `.tools/leanbuild`); namespace `CTG.FlatLB2`; check with `./check_flat_lb2.sh`.
(1) `ofC3`: a `C³` function with third derivative bounded by `M₃` satisfies the interface `Taylor3` with the same
constant, `lapl_ofC3`: its `lapl` is Mathlib's Laplacian, `flat_LB_C3`: the flat Laplace–Beltrami limit with
Mathlib's Laplacian.  (2) Flat CONFORMAL time-dependent metric `g_τ = a(τ)² · Euclidean`, constant density:
`conformal_LB` (uniform for `a(τ) ≥ a₀ > 0`) and `conformal_dq`: for two times
`|Δ_η(L^τ_ξ f) + Δ_η(Δ_{g_τ} f)| ≤ 2 M₃ ξ μ₃/(3 m₂ K₀ a₀³ |η|)`, i.e. the second inequality of `prop:dotLN-diff` at
population level in the flat conformal case, in the form `C ξ/|η|` (the paper has `min{ξ, ξ²/|η|}`).
NOT formalised: general positive definite `G_τ`, the order `ξ²/|η|` (fourth-order Taylor), the branch `ξ`
(derivatives in the time), the identification with the population operator of the N-point files, anything on
curved manifolds.  No `sorry`, no `axiom`, no `native_decide`.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatLB

open MeasureTheory Set Laplacian InnerProductSpace
open CTG.FlatLB

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace CTG.FlatLB2

variable {n : ℕ}

/-- The coordinate vectors. -/
abbrev eb (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1:ℝ)

theorem clm_decomp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] F) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, v i • L (eb i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply]

theorem line_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : EuclideanSpace ℝ (Fin n) → F} (hG : Differentiable ℝ G)
    (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => G (x + s • v)) (fderiv ℝ G (x + t • v) v) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  exact (hG (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline

section Gen

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem three_bound (f : E → ℝ) (M₃ : ℝ) (hM : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ M₃) (y v : E) :
    |iteratedFDeriv ℝ 3 f y (fun _ => v)| ≤ M₃ * ‖v‖ ^ 3 := by
  rw [← Real.norm_eq_abs]
  refine ((iteratedFDeriv ℝ 3 f y).le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right (hM y) (by positivity)

end Gen

section C3

variable (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 3 f)

include hf

theorem diff0 : Differentiable ℝ f :=
  hf.differentiable (by first | norm_num | simp | decide)

theorem cd1 : ContDiff ℝ 2 (fderiv ℝ f) :=
  hf.fderiv_right (by first | norm_num | simp | rfl | exact le_rfl | (exact le_of_eq rfl))

theorem diff1 : Differentiable ℝ (fderiv ℝ f) :=
  (cd1 f hf).differentiable (by first | norm_num | simp | decide)

theorem diffI2 : Differentiable ℝ (iteratedFDeriv ℝ 2 f) :=
  hf.differentiable_iteratedFDeriv (by first | norm_num | (exact_mod_cast (by norm_num : (2:ℕ) < 3)) | decide)

end C3

theorem hess_sum (f : EuclideanSpace ℝ (Fin n) → ℝ) (y v : EuclideanSpace ℝ (Fin n)) :
    ∑ i, ∑ j, v i * v j * fderiv ℝ (fderiv ℝ f) y (eb j) (eb i)
      = iteratedFDeriv ℝ 2 f y (fun _ => v) := by
  rw [iteratedFDeriv_two_apply]
  show _ = fderiv ℝ (fderiv ℝ f) y v v
  rw [clm_decomp (fderiv ℝ (fderiv ℝ f) y v) v, clm_decomp (fderiv ℝ (fderiv ℝ f) y) v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 1000000 in
/-- **(1) `C³` with bounded third derivative gives the HYPOTHESES of `Taylor3`** (same constant). -/
def ofC3 (f : EuclideanSpace ℝ (Fin n) → ℝ) (M₃ : ℝ) (hf : ContDiff ℝ 3 f)
    (hM : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ M₃) : Taylor3 n f M₃ where
  g := fun i y => fderiv ℝ f y (eb i)
  H := fun i j y => fderiv ℝ (fderiv ℝ f) y (eb j) (eb i)
  D3 := fun y v => iteratedFDeriv ℝ 3 f y (fun _ => v)
  cont := (diff0 f hf).continuous
  d1 := fun x v t => (line_deriv (diff0 f hf) x v t).congr_deriv (by
    rw [clm_decomp (fderiv ℝ f (x + t • v)) v]
    simp only [smul_eq_mul])
  d2 := fun x v t => by
    have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun s : ℝ => v i * fderiv ℝ f (x + s • v) (eb i))
          (v i * (fderiv ℝ (fderiv ℝ f) (x + t • v) v (eb i) + fderiv ℝ f (x + t • v) 0)) t :=
      fun i _ => ((line_deriv (diff1 f hf) x v t).clm_apply (hasDerivAt_const t (eb i))).const_mul
        (v i)
    refine (HasDerivAt.fun_sum h).congr_deriv ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zero, add_zero, clm_decomp (fderiv ℝ (fderiv ℝ f) (x + t • v)) v,
      ContinuousLinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  d3 := fun x v t => by
    have hfun : (fun s : ℝ => ∑ i, ∑ j, v i * v j * fderiv ℝ (fderiv ℝ f) (x + s • v) (eb j) (eb i))
        = fun s => iteratedFDeriv ℝ 2 f (x + s • v) (fun _ => v) :=
      funext fun s => hess_sum f _ v
    show HasDerivAt
      (fun s : ℝ => ∑ i, ∑ j, v i * v j * fderiv ℝ (fderiv ℝ f) (x + s • v) (eb j) (eb i))
      (iteratedFDeriv ℝ 3 f (x + t • v) (fun _ => v)) t
    rw [hfun]
    have hl := line_deriv (diffI2 f hf) x v t
    have hc := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ
      (fun _ => v)).hasFDerivAt.comp_hasDerivAt t hl
    refine hc.congr_deriv ?_
    rw [ContinuousMultilinearMap.apply_apply]
    first | rfl | exact (iteratedFDeriv_succ_apply_left (fun _ => v)).symm
  bd3 := fun y v => three_bound f M₃ hM y v

/-- `lapl` of the `C³` data is Mathlib's Laplacian. -/
theorem lapl_ofC3 (f : EuclideanSpace ℝ (Fin n) → ℝ) (M₃ : ℝ) (hf : ContDiff ℝ 3 f)
    (hM : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ M₃) (x : EuclideanSpace ℝ (Fin n)) :
    lapl (ofC3 f M₃ hf hM) x = Δ f x := by
  have hL := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin n) ℝ)) x
  refine Eq.trans ?_ hL.symm
  unfold lapl
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [ofC3, EuclideanSpace.basisFun_apply]

/-- **Flat `thm:LB` with Mathlib's Laplacian**, for `C³` functions with bounded third derivative. -/
theorem flat_LB_C3 {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {K₀ m₂ μ₃ : ℝ} (hk : Kern n μ k K₀ m₂ μ₃) (hm₂ : 0 < m₂)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (M₃ : ℝ) (hf : ContDiff ℝ 3 f)
    (hM : ∀ y, ‖iteratedFDeriv ℝ 3 f y‖ ≤ M₃) (ξ : ℝ) (hξ : 0 < ξ)
    (x : EuclideanSpace ℝ (Fin n)) :
    |2 / (m₂ * ξ ^ 2) * (f x - avgOp μ k ξ f x) + Δ f x| ≤ M₃ * ξ * μ₃ / (3 * m₂ * K₀) := by
  rw [← lapl_ofC3 f M₃ hf hM x]
  exact flat_LB hk hm₂ (ofC3 f M₃ hf hM) ξ hξ x

/-- Example: constant functions are `C³` with third derivative `0`, so `ofC3` applies with `M₃ = 0`. -/
theorem const_hyp (c : ℝ) :
    ContDiff ℝ 3 (fun _ : EuclideanSpace ℝ (Fin n) => c)
    ∧ ∀ y, ‖iteratedFDeriv ℝ 3 (fun _ : EuclideanSpace ℝ (Fin n) => c) y‖ ≤ 0 := by
  refine ⟨contDiff_const, fun y => ?_⟩
  rw [iteratedFDeriv_const_of_ne (by norm_num : (3:ℕ) ≠ 0)]
  simp

/-- The resulting `Taylor3` data for a constant function. -/
def constTaylor (c : ℝ) : Taylor3 n (fun _ => c) 0 :=
  ofC3 _ 0 (const_hyp c).1 (const_hyp c).2

/-! ### (2) Flat conformal time-dependent metric `g_τ = a(τ)² · euclidean` -/

/-- Population Markov operator of the kernel `h(d_τ(x,y)/ξ)` with `d_τ(x,y) = a|y − x|` and
constant density (Lebesgue): `∫ h(a|y|/ξ) f(x + y) dy / ∫ h(a|y|/ξ) dy`. -/
def Pconf (h : ℝ → ℝ) (a ξ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∫ y : EuclideanSpace ℝ (Fin n), h (a * ‖y‖ / ξ) * f (x + y))
    / ∫ y : EuclideanSpace ℝ (Fin n), h (a * ‖y‖ / ξ)

/-- **Linear substitution**: `Pconf h a ξ = A_{ξ/a}` for the radial kernel `h(|z|)`. -/
theorem Pconf_eq (h : ℝ → ℝ) {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Pconf h a ξ f x = avgOp volume (fun z => h ‖z‖) (ξ / a) f x := by
  have hc : 0 < ξ / a := div_pos hξ ha
  have hsc : ∀ z : EuclideanSpace ℝ (Fin n), a * ‖(ξ / a) • z‖ / ξ = ‖z‖ := fun z => by
    rw [norm_smul, Real.norm_of_nonneg hc.le]; field_simp
  have h1 := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun y : EuclideanSpace ℝ (Fin n) => h (a * ‖y‖ / ξ) * f (x + y)) (ξ / a)
  have h2 := Measure.integral_comp_smul (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun y : EuclideanSpace ℝ (Fin n) => h (a * ‖y‖ / ξ)) (ξ / a)
  simp only [hsc] at h1 h2
  set s := |((ξ / a) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹| with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact abs_ne_zero.2 (inv_ne_zero (pow_ne_zero _ hc.ne'))
  unfold avgOp Pconf
  rw [h1, h2, smul_eq_mul, smul_eq_mul, mul_div_mul_left _ _ hs0]

/-- The operator `L^τ_ξ f = (2/(m₂ ξ²))(f − P^τ f)` for the conformal metric with factor `a`. -/
def Lconf (h : ℝ → ℝ) (m₂ a ξ : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  2 / (m₂ * ξ ^ 2) * (f x - Pconf h a ξ f x)

/-- **(2) Flat `thm:LB` for the conformal metric `g = a²·euclidean`**: `Δ_g f = a⁻² Δf`, and
`|L^τ_ξ f(x) + Δ_g f(x)| ≤ M₃ ξ μ₃/(3 m₂ K₀ a₀³)` for `a ≥ a₀ > 0` (uniform in the time).
HYPOTHESES: `Kern` for the radial kernel `h(|z|)` under Lebesgue measure (e.g. from
`radial_kern`), `Taylor3` for `f` (e.g. from `ofC3`), `M₃ ≥ 0`. -/
theorem conformal_LB (h : ℝ → ℝ) {K₀ m₂ μ₃ : ℝ}
    (hk : Kern n volume (fun z => h ‖z‖) K₀ m₂ μ₃) (hm₂ : 0 < m₂)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M₃ : ℝ} (T : Taylor3 n f M₃) (hM₃ : 0 ≤ M₃)
    {a a₀ ξ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (hξ : 0 < ξ) (x : EuclideanSpace ℝ (Fin n)) :
    |Lconf h m₂ a ξ f x + lapl T x / a ^ 2| ≤ M₃ * ξ * μ₃ / (3 * m₂ * K₀ * a₀ ^ 3) := by
  have ha0 : 0 < a := lt_of_lt_of_le ha₀ ha
  have hK₀ := hk.mass_pos
  have hμ₃ : 0 ≤ μ₃ := by
    rw [← hk.mom3]; exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.nonneg z)
  have hL := flat_LB hk hm₂ T (ξ / a) (div_pos hξ ha0) x
  have e : Lconf h m₂ a ξ f x + lapl T x / a ^ 2
      = (2 / (m₂ * (ξ / a) ^ 2) * (f x - avgOp volume (fun z => h ‖z‖) (ξ / a) f x)
          + lapl T x) / a ^ 2 := by
    unfold Lconf
    rw [Pconf_eq h ha0 hξ]
    field_simp
  rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < a ^ 2)]
  calc _ ≤ M₃ * (ξ / a) * μ₃ / (3 * m₂ * K₀) / a ^ 2 :=
        div_le_div_of_nonneg_right hL (by positivity)
    _ = M₃ * ξ * μ₃ / (3 * m₂ * K₀ * a ^ 3) := by field_simp
    _ ≤ M₃ * ξ * μ₃ / (3 * m₂ * K₀ * a₀ ^ 3) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        have : a₀ ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ ha₀.le ha 3
        nlinarith [mul_pos (mul_pos (by norm_num : (0:ℝ) < 3) hm₂) hK₀]

/-- **Two times**: for conformal factors `a_a, a_b ≥ a₀ > 0` and `η ≠ 0`,
`|Δ_η(L^τ_ξ f)(x) + Δ_η(Δ_{g_τ} f)(x)| ≤ 2 M₃ ξ μ₃/(3 m₂ K₀ a₀³ |η|)`: the second inequality of
`prop:dotLN-diff` on population level in the flat conformal case, with the power `ξ/|η|`. -/
theorem conformal_dq (h : ℝ → ℝ) {K₀ m₂ μ₃ : ℝ}
    (hk : Kern n volume (fun z => h ‖z‖) K₀ m₂ μ₃) (hm₂ : 0 < m₂)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M₃ : ℝ} (T : Taylor3 n f M₃) (hM₃ : 0 ≤ M₃)
    {aa ab a₀ ξ η : ℝ} (ha₀ : 0 < a₀) (haa : a₀ ≤ aa) (hab : a₀ ≤ ab) (hξ : 0 < ξ) (hη : η ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    |(Lconf h m₂ ab ξ f x - Lconf h m₂ aa ξ f x) / η
        + (lapl T x / ab ^ 2 - lapl T x / aa ^ 2) / η|
      ≤ 2 * (M₃ * ξ * μ₃ / (3 * m₂ * K₀ * a₀ ^ 3)) / |η| := by
  have hb := conformal_LB h hk hm₂ T hM₃ ha₀ hab hξ x
  have ha := conformal_LB h hk hm₂ T hM₃ ha₀ haa hξ x
  have e : (Lconf h m₂ ab ξ f x - Lconf h m₂ aa ξ f x) / η
        + (lapl T x / ab ^ 2 - lapl T x / aa ^ 2) / η
      = ((Lconf h m₂ ab ξ f x + lapl T x / ab ^ 2)
          - (Lconf h m₂ aa ξ f x + lapl T x / aa ^ 2)) / η := by ring
  rw [e, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc _ ≤ |Lconf h m₂ ab ξ f x + lapl T x / ab ^ 2| + |Lconf h m₂ aa ξ f x + lapl T x / aa ^ 2| :=
        abs_sub _ _
    _ ≤ _ := by linarith

end CTG.FlatLB2
