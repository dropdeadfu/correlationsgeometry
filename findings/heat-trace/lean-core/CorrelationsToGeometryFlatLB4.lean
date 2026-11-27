/-
Twenty-sixth file: the flat core of `thm:LB` for a general constant metric.  Imports
`CorrelationsToGeometryFlatLB3` (compiled module under `.tools/leanbuild`); namespace `CTG.FlatLB4`; check with
`./check_flat_lb4.sh`.
Metric `g(v,v) = ‖S⁻¹v‖²` for a continuous linear automorphism `S` of `ℝⁿ` (so `G = (S Sᵀ)⁻¹`), constant density:
`PG_eq` (substitution), `metric_LB4`: `|(2/(m₂ξ²))(f − P_g f) + Δ_g f| ≤ M₄ ‖S‖⁴ ξ² μ₄/(12 m₂ K₀)` with
`Δ_g f = Σ_i D²f(S e_i, S e_i)`; two metrics: `metric_dq4` (`ξ²/|η|`); the family `g_τ = a(τ)² g₀`:
`metric_dq_min` (`ξ² min{C₁/|η|, C₂}`); a test function depending on the time with a fixed metric:
`metric_testfun`.
NOT formalised: the branch uniform in `η` for a general differentiable `S(τ)`; metric and test function both
depending on the time (a triangle inequality from the two statements, not written); the flat torus; anything on
curved manifolds or with a non-constant density.  No `sorry`, no `axiom`, no `native_decide`.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatLB3

open MeasureTheory Set Laplacian InnerProductSpace
open CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatLB4

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Linear substitution for Lebesgue measure: `∫ F(L w) dw = s ∫ F` with `s ≠ 0`. -/
theorem subst (L : E ≃L[ℝ] E) :
    ∃ s : ℝ, s ≠ 0 ∧ ∀ F : E → ℝ, ∫ w, F (L w) = s * ∫ y, F y := by
  have hdet : LinearMap.det (L.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 :=
    L.toLinearEquiv.isUnit_det'.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) hdet
  refine ⟨(ENNReal.ofReal |(LinearMap.det (L.toLinearEquiv : E →ₗ[ℝ] E))⁻¹|).toReal, ?_,
    fun F => ?_⟩
  · rw [ENNReal.toReal_ofReal (abs_nonneg _)]; exact abs_ne_zero.2 (inv_ne_zero hdet)
  · have h1 := integral_map_equiv (μ := (volume : Measure E)) L.toHomeomorph.toMeasurableEquiv F
    have h2 : Measure.map (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E)
        = Measure.map (L.toLinearEquiv : E →ₗ[ℝ] E) volume := rfl
    rw [h2, hmap, integral_smul_measure, smul_eq_mul] at h1
    exact h1.symm

/-- Population operator of the kernel `h(‖S⁻¹(y−x)‖/ξ)` with constant density. -/
def PG (h : ℝ → ℝ) (S : E ≃L[ℝ] E) (ξ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  (∫ y : E, h (‖S.symm y‖ / ξ) * f (x + y)) / ∫ y : E, h (‖S.symm y‖ / ξ)

/-- The pulled-back function `u ↦ f(x + S u)`. -/
def Fx (f : E → ℝ) (S : E ≃L[ℝ] E) (x : E) : E → ℝ := fun u => f (x + S u)

theorem PG_eq (h : ℝ → ℝ) (S : E ≃L[ℝ] E) {ξ : ℝ} (hξ : 0 < ξ) (f : E → ℝ) (x : E) :
    PG h S ξ f x = avgOp volume (fun z => h ‖z‖) ξ (Fx f S x) 0 := by
  obtain ⟨s, hs, hsub⟩ := subst S
  set t := |(ξ ^ Module.finrank ℝ E)⁻¹| with ht
  have ht0 : t ≠ 0 := abs_ne_zero.2 (inv_ne_zero (pow_ne_zero _ hξ.ne'))
  have hsc : ∀ u : E, ‖ξ • u‖ / ξ = ‖u‖ := fun u => by
    rw [norm_smul, Real.norm_of_nonneg hξ.le]; field_simp
  have eN : ∫ z : E, h ‖z‖ * f (x + S (0 + ξ • z))
      = t * (s * ∫ y : E, h (‖S.symm y‖ / ξ) * f (x + y)) := by
    have h1 := hsub (fun y => h (‖S.symm y‖ / ξ) * f (x + y))
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h1
    have h2 := Measure.integral_comp_smul (volume : Measure E)
      (fun w : E => h (‖w‖ / ξ) * f (x + S w)) ξ
    simp only [hsc, smul_eq_mul] at h2
    simp only [zero_add]
    rw [h2, h1]
  have eD : ∫ z : E, h ‖z‖ = t * (s * ∫ y : E, h (‖S.symm y‖ / ξ)) := by
    have h1 := hsub (fun y => h (‖S.symm y‖ / ξ))
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h1
    have h2 := Measure.integral_comp_smul (volume : Measure E) (fun w : E => h (‖w‖ / ξ)) ξ
    simp only [hsc, smul_eq_mul] at h2
    rw [h2, h1]
  unfold PG avgOp Fx
  show _ = (∫ z : E, h ‖z‖ * f (x + S (0 + ξ • z))) / ∫ z : E, h ‖z‖
  rw [eN, eD, ← mul_assoc, ← mul_assoc, mul_div_mul_left _ _ (mul_ne_zero ht0 hs)]

theorem Fx_contDiff {f : E → ℝ} (hf : ContDiff ℝ 4 f) (S : E ≃L[ℝ] E) (x : E) :
    ContDiff ℝ 4 (Fx f S x) :=
  hf.comp (contDiff_const.add S.contDiff)

theorem Fx_eq (f : E → ℝ) (S : E ≃L[ℝ] E) (x : E) :
    Fx f S x = (fun w => f (x + w)) ∘ (S : E →L[ℝ] E) := rfl

theorem Fx_bound {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (S : E ≃L[ℝ] E) (x : E) (y : E) :
    ‖iteratedFDeriv ℝ 4 (Fx f S x) y‖ ≤ M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 := by
  have hT : ContDiff ℝ 4 (fun w => f (x + w)) := hf.comp (contDiff_const.add contDiff_id)
  rw [Fx_eq, (S : E →L[ℝ] E).iteratedFDeriv_comp_right hT y le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, iteratedFDeriv_comp_add_left]
  exact mul_le_mul_of_nonneg_right (hM _) (by positivity)

/-- The Laplace–Beltrami operator of the constant metric `g(v,v) = ‖S⁻¹v‖²`:
`Δ_g f(x) = Σ_i D²f(x)[S e_i, S e_i] = Σ_{jk} (SSᵀ)_{jk} ∂_j∂_k f(x)`. -/
def lapG (S : E ≃L[ℝ] E) (f : E → ℝ) (x : E) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 f x (fun _ => S (eb i))

theorem lapl_Fx {f : E → ℝ} (hf : ContDiff ℝ 4 f) (S : E ≃L[ℝ] E) (x : E) :
    Δ (Fx f S x) 0 = lapG S f x := by
  have hT : ContDiff ℝ 4 (fun w => f (x + w)) := hf.comp (contDiff_const.add contDiff_id)
  have hL := congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis (Fx f S x)
    (EuclideanSpace.basisFun (Fin n) ℝ)) 0
  refine hL.trans ?_
  unfold lapG
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fx_eq, (S : E →L[ℝ] E).iteratedFDeriv_comp_right hT 0 (by norm_num),
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left]
  simp only [ContinuousLinearMap.map_zero, add_zero, map_zero]
  congr 1
  funext j
  fin_cases j <;> simp [EuclideanSpace.basisFun_apply]

/-- **(1) Flat `thm:LB` for the constant metric `g(v,v) = ‖S⁻¹v‖²`**. -/
theorem metric_LB4 {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (S : E ≃L[ℝ] E) (ξ : ℝ) (hξ : 0 < ξ) (x : E) :
    |2 / (m₂ * ξ ^ 2) * (f x - PG h S ξ f x) + lapG S f x|
      ≤ M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * ξ ^ 2 * μ₄ / (12 * m₂ * K₀) := by
  have h1 := flat_LB4 hk hm₂ (Fx_contDiff hf S x) (Fx_bound hf hM S x) ξ hξ 0
  rw [lapl_Fx hf S x, ← PG_eq h S hξ f x] at h1
  have e : Fx f S x 0 = f x := by simp [Fx]
  rw [e] at h1
  exact h1

/-- **(2a) Branch `ξ²/|η|` for any two constant metrics** with `‖S_a‖, ‖S_b‖ ≤ σ`. -/
theorem metric_dq4 {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (Sa Sb : E ≃L[ℝ] E) {σ : ℝ} (hSa : ‖(Sa : E →L[ℝ] E)‖ ≤ σ)
    (hSb : ‖(Sb : E →L[ℝ] E)‖ ≤ σ) (ξ η : ℝ) (hξ : 0 < ξ) (x : E) :
    |(2 / (m₂ * ξ ^ 2) * (f x - PG h Sb ξ f x) - 2 / (m₂ * ξ ^ 2) * (f x - PG h Sa ξ f x)) / η
        + (lapG Sb f x - lapG Sa f x) / η|
      ≤ 2 * (M₄ * σ ^ 4 * ξ ^ 2 * μ₄ / (12 * m₂ * K₀)) / |η| := by
  have hK₀ := hk.kern.mass_pos
  have hμ₄ : 0 ≤ μ₄ := by
    rw [← hk.mom4]; exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have mono : ∀ S : E ≃L[ℝ] E, ‖(S : E →L[ℝ] E)‖ ≤ σ →
      M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * ξ ^ 2 * μ₄ / (12 * m₂ * K₀)
        ≤ M₄ * σ ^ 4 * ξ ^ 2 * μ₄ / (12 * m₂ * K₀) := fun S hS => by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := pow_le_pow_left₀ (norm_nonneg _) hS 4
    have h0 : 0 ≤ ξ ^ 2 * μ₄ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hM₄]
  have hb := (metric_LB4 hk hm₂ hf hM Sb ξ hξ x).trans (mono Sb hSb)
  have ha := (metric_LB4 hk hm₂ hf hM Sa ξ hξ x).trans (mono Sa hSa)
  have e : (2 / (m₂ * ξ ^ 2) * (f x - PG h Sb ξ f x) - 2 / (m₂ * ξ ^ 2) * (f x - PG h Sa ξ f x))
        / η + (lapG Sb f x - lapG Sa f x) / η
      = ((2 / (m₂ * ξ ^ 2) * (f x - PG h Sb ξ f x) + lapG Sb f x)
          - (2 / (m₂ * ξ ^ 2) * (f x - PG h Sa ξ f x) + lapG Sa f x)) / η := by ring
  rw [e, abs_div]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg _)
  calc _ ≤ |2 / (m₂ * ξ ^ 2) * (f x - PG h Sb ξ f x) + lapG Sb f x|
        + |2 / (m₂ * ξ ^ 2) * (f x - PG h Sa ξ f x) + lapG Sa f x| := abs_sub _ _
    _ ≤ _ := by linarith

/-- `L^τ_ξ f` for the family `g_τ = a(τ)² g₀`, `g₀(v,v) = ‖S₀⁻¹ v‖²`: kernel
`h(a(τ)‖S₀⁻¹(y−x)‖/ξ) = h(‖S₀⁻¹(y−x)‖/(ξ/a))`. -/
def Lmet (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a ξ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  2 / (m₂ * ξ ^ 2) * (f x - PG h S (ξ / a) f x)

theorem Lmet_eq (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ)
    (f : E → ℝ) (x : E) : Lmet h m₂ S a ξ f x = Lconf h m₂ a ξ (Fx f S x) 0 := by
  unfold Lmet Lconf
  rw [Pconf_eq h ha hξ, PG_eq h S (div_pos hξ ha)]
  simp [Fx]

/-- **(2b) The full form for `g_τ = a(τ)² g₀`**: for a differentiable conformal factor
`a(τ) ≥ a₀ > 0` with `|a'| ≤ L_a` (HYPOTHESES) and `σ = ‖S₀‖`,
`|Δ_η(L^τ_ξ f) + Δ_η(Δ_{g_τ} f)| ≤ ξ² · min{M₄σ⁴μ₄/(6m₂K₀a₀⁴|η|), M₄σ⁴μ₄L_a/(3m₂K₀a₀⁵)}`
with `Δ_{g_τ} f = a(τ)⁻² Δ_{g₀} f`. -/
theorem metric_dq_min {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (S₀ : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : E) (τa τb : ℝ) (hne : τb ≠ τa) :
    |(Lmet h m₂ S₀ (a τb) ξ f x - Lmet h m₂ S₀ (a τa) ξ f x) / (τb - τa)
        + (lapG S₀ f x / a τb ^ 2 - lapG S₀ f x / a τa ^ 2) / (τb - τa)|
      ≤ ξ ^ 2 * min (M₄ * ‖(S₀ : E →L[ℝ] E)‖ ^ 4 * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4) / |τb - τa|)
          (M₄ * ‖(S₀ : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)) := by
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have h1 := conformal_dq_min hk hm₂ (Fx_contDiff hf S₀ x) (Fx_bound hf hM S₀ x)
    (by positivity) a a' hda ha₀ ha hLa hξ 0 τa τb hne
  rw [lapl_Fx hf S₀ x, ← Lmet_eq h m₂ S₀ (hpos τb) hξ, ← Lmet_eq h m₂ S₀ (hpos τa) hξ] at h1
  exact h1

/-! ### (3) Time-dependent test function for a fixed metric -/

/-- Integrability of `k(z) f(x + c z)` for `C⁴` functions (needed for linearity). -/
theorem int_T {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (x : E) (c : ℝ) : Integrable (fun z : E => h ‖z‖ * f (x + c • z)) := by
  have hK := hk.kern
  have hh0 : ∀ z : E, 0 ≤ h ‖z‖ := hK.nonneg
  have hkm := hK.int0.aestronglyMeasurable
  obtain ⟨IR, -⟩ := expansion hk hf hM x c
  have I1 : Integrable (fun z : E => h ‖z‖ * Dk f 1 x z) :=
    (hk.int1.const_mul ‖iteratedFDeriv ℝ 1 f x‖).mono'
      (hkm.mul (Dk_cont f 1 x).aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 z)]
        have := Dk_bound f 1 x z
        rw [pow_one] at this
        nlinarith [abs_nonneg (Dk f 1 x z), hh0 z, norm_nonneg z])
  have I3 : Integrable (fun z : E => h ‖z‖ * Dk f 3 x z) :=
    (hK.int3.const_mul ‖iteratedFDeriv ℝ 3 f x‖).mono'
      (hkm.mul (Dk_cont f 3 x).aestronglyMeasurable)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 z)]
        have := Dk_bound f 3 x z
        nlinarith [abs_nonneg (Dk f 3 x z), hh0 z, pow_nonneg (norm_nonneg z) 3])
  have hD2 : ∀ z : E, h ‖z‖ * Dk f 2 x z
      = ∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (eb j) (eb i) * (z i * z j * h ‖z‖) := fun z => by
    rw [show Dk f 2 x z = iteratedFDeriv ℝ 2 f x (fun _ => z) from rfl, ← hess_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  obtain ⟨I2', -⟩ := integral_second hK (fun i j => fderiv ℝ (fderiv ℝ f) x (eb j) (eb i))
  have I2 : Integrable (fun z : E => h ‖z‖ * Dk f 2 x z) :=
    I2'.congr (ae_of_all _ fun z => (hD2 z).symm)
  have J0 : Integrable (fun z : E => h ‖z‖ * f x) := hK.int0.mul_const _
  have A1 : Integrable (fun z : E => h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z)) :=
    J0.add (I1.const_mul c)
  have A2 : Integrable (fun z : E =>
      h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z) + c ^ 2 / 2 * (h ‖z‖ * Dk f 2 x z)) :=
    A1.add (I2.const_mul _)
  have A3 : Integrable (fun z : E =>
      h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z) + c ^ 2 / 2 * (h ‖z‖ * Dk f 2 x z)
        + c ^ 3 / 6 * (h ‖z‖ * Dk f 3 x z)) := A2.add (I3.const_mul _)
  refine (A3.add IR).congr (ae_of_all _ fun z => ?_)
  show h ‖z‖ * f x + c * (h ‖z‖ * Dk f 1 x z) + c ^ 2 / 2 * (h ‖z‖ * Dk f 2 x z)
      + c ^ 3 / 6 * (h ‖z‖ * Dk f 3 x z) + h ‖z‖ * rem f x c z = h ‖z‖ * f (x + c • z)
  unfold rem; ring

/-- **(3) Time-dependent test function**, fixed metric `S`: if `f_a, f_b` are `C⁴` with bounded
fourth derivatives and the difference quotient `F = (f_b − f_a)/η` has `‖D⁴F‖ ≤ M₄'`
(HYPOTHESES), then `|Δ_η(L_ξ f) + Δ_η(Δ_g f)| ≤ M₄' ‖S‖⁴ ξ² μ₄/(12 m₂ K₀)`. -/
theorem metric_testfun {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {fa fb : E → ℝ} (ha : ContDiff ℝ 4 fa) (hb : ContDiff ℝ 4 fb) {Ma Mb M' : ℝ}
    (hMa : ∀ y, ‖iteratedFDeriv ℝ 4 fa y‖ ≤ Ma) (hMb : ∀ y, ‖iteratedFDeriv ℝ 4 fb y‖ ≤ Mb)
    (η : ℝ) (hη : η ≠ 0)
    (hMF : ∀ y, ‖iteratedFDeriv ℝ 4 (fun y => (fb y - fa y) / η) y‖ ≤ M')
    (S : E ≃L[ℝ] E) (ξ : ℝ) (hξ : 0 < ξ) (x : E) :
    |(2 / (m₂ * ξ ^ 2) * (fb x - PG h S ξ fb x) - 2 / (m₂ * ξ ^ 2) * (fa x - PG h S ξ fa x)) / η
        + (lapG S fb x - lapG S fa x) / η|
      ≤ M' * ‖(S : E →L[ℝ] E)‖ ^ 4 * ξ ^ 2 * μ₄ / (12 * m₂ * K₀) := by
  set F : E → ℝ := fun y => (fb y - fa y) / η with hFdef
  have hF : ContDiff ℝ 4 F := (hb.sub ha).div_const η
  have key := metric_LB4 hk hm₂ hF hMF S ξ hξ x
  -- linearity of the population operator
  have hPG : PG h S ξ F x = (PG h S ξ fb x - PG h S ξ fa x) / η := by
    rw [PG_eq h S hξ, PG_eq h S hξ, PG_eq h S hξ]
    unfold avgOp Fx
    have ib := int_T hk (Fx_contDiff hb S x) (Fx_bound hb hMb S x) 0 ξ
    have ia := int_T hk (Fx_contDiff ha S x) (Fx_bound ha hMa S x) 0 ξ
    unfold Fx at ib ia
    have e : (fun z : E => h ‖z‖ * F (x + S (0 + ξ • z)))
        = fun z => (h ‖z‖ * fb (x + S (0 + ξ • z)) - h ‖z‖ * fa (x + S (0 + ξ • z))) / η := by
      funext z; rw [hFdef]; ring
    show (∫ z : E, h ‖z‖ * F (x + S (0 + ξ • z))) / ∫ z : E, h ‖z‖ = _
    rw [e, integral_div, integral_sub ib ia]
    ring
  -- linearity of `Δ_g`
  have hlap : lapG S F x = (lapG S fb x - lapG S fa x) / η := by
    have hFs : F = η⁻¹ • (fb - fa) := by
      funext y; simp [hFdef, div_eq_inv_mul]
    have hcd : ContDiffAt ℝ 2 (fb - fa) x := ((hb.sub ha).of_le (by norm_num)).contDiffAt
    have hb2 : ContDiff ℝ 2 fb := hb.of_le (by norm_num)
    have ha2 : ContDiff ℝ 2 fa := ha.of_le (by norm_num)
    unfold lapG
    rw [hFs, iteratedFDeriv_const_smul_apply hcd, iteratedFDeriv_sub_apply hb2.contDiffAt ha2.contDiffAt]
    simp only [ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
      smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    field_simp
  have e1 : (2 / (m₂ * ξ ^ 2) * (fb x - PG h S ξ fb x) - 2 / (m₂ * ξ ^ 2) * (fa x - PG h S ξ fa x))
        / η + (lapG S fb x - lapG S fa x) / η
      = 2 / (m₂ * ξ ^ 2) * (F x - PG h S ξ F x) + lapG S F x := by
    rw [hPG, hlap, hFdef]; ring
  rw [e1]; exact key

end CTG.FlatLB4
