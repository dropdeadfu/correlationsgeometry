/-
Thirtieth file: `prop:dotLN-diff` with BOTH inequalities in the RATE FORM on the flat torus.  Imports
`CorrelationsToGeometryFlatNPoint` (compiled module under `.tools/leanbuild`); namespace
`CTG.FlatNPointRate`; check with `./check_flat_npoint_rate.sh`.
Setting of the twenty-eighth file (uniform sample of the unit cube, periodised kernel of a profile with compact
support `[0,R]`, metrics `g_τ = a(τ)² g₀`, `f` of class `C⁴`, periodic).  `mass_eq` (kernel mass
`K₀ |det S| ξ'ⁿ`), `hBI_of`, `hMI_of` (the bounds on the time difference quotient of the kernel, from a Lipschitz
profile and `|a'| ≤ L_a`), `flat_npoint_rate`: if `92416 Λ¹⁴ · 3 log N ≤ N ξⁿ`, `ξ ≤ 1`, `N ≥ 2`, then outside an
event of probability at most `30/N²`, with `δ' = √(3 log N/(N ξⁿ))`, at every sample point
(i) `|Δ_η L_N f − Δ_η L_ξ f| ≤ (7320000 Λ²⁰/m₂) δ'/ξ` and
(ii) `|Δ_η L_N f + Δ_η(Δ_{g_τ} f)| ≤ (7320000 Λ²⁰/m₂) δ'/ξ + ξ² min{C₁/|η|, C₂}`.
HYPOTHESES that remain: profile Lipschitz with compact support, `a₀ ≤ a ≤ a₁`, `|a'| ≤ L_a`, `f` Lipschitz
(not derived from `C⁴` and periodicity), `‖S‖ (ξ/a₀) R < 1/2`.  NOT formalised: Gaussian profiles, measurability
of the exceptional set, uniformity over pairs of times; `Δ_{g_τ} f` is `lapG S f / a(τ)²` of the flat files, there
is no Laplace–Beltrami operator as an object; constants are crude and not evaluated.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatNPoint

open MeasureTheory ProbabilityTheory Set
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB3 CTG.FlatLB4 CTG.FlatNPoint

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointRate

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### (1) The mass of the flat kernel -/

/-- `|det S|`. -/
def dS (S : E ≃L[ℝ] E) : ℝ := |LinearMap.det (S.toLinearEquiv : E →ₗ[ℝ] E)|

theorem dS_pos (S : E ≃L[ℝ] E) : 0 < dS S :=
  abs_pos.2 S.toLinearEquiv.isUnit_det'.ne_zero

/-- Linear substitution with the explicit factor: `∫ F(S w) dw = |det S|⁻¹ ∫ F`. -/
theorem substE (L : E ≃L[ℝ] E) (F : E → ℝ) : ∫ w, F (L w) = (dS L)⁻¹ * ∫ y, F y := by
  have hdet : LinearMap.det (L.toLinearEquiv : E →ₗ[ℝ] E) ≠ 0 :=
    L.toLinearEquiv.isUnit_det'.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) hdet
  have h1 := integral_map_equiv (μ := (volume : Measure E)) L.toHomeomorph.toMeasurableEquiv F
  have h2 : Measure.map (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E)
      = Measure.map (L.toLinearEquiv : E →ₗ[ℝ] E) volume := rfl
  rw [h2, hmap, integral_smul_measure, smul_eq_mul, ENNReal.toReal_ofReal (abs_nonneg _)] at h1
  unfold dS; rw [← abs_inv]
  exact h1.symm

/-- **(1)** `p = ∫ h(‖S⁻¹v‖/ξ') dv = K₀ |det S| ξ'ⁿ`. -/
theorem mass_eq {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (S : E ≃L[ℝ] E)
    {ξ' : ℝ} (hξ : 0 < ξ') : ∫ v, kap h S ξ' v = K₀ * dS S * ξ' ^ n := by
  have hsc : ∀ u : E, ‖ξ' • u‖ / ξ' = ‖u‖ := fun u => by
    rw [norm_smul, Real.norm_of_nonneg hξ.le]; field_simp
  have h1 := substE S (fun y => h (‖S.symm y‖ / ξ'))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h1
  have h2 := Measure.integral_comp_smul (volume : Measure E) (fun w : E => h (‖w‖ / ξ')) ξ'
  simp only [hsc, smul_eq_mul, finrank_euclideanSpace_fin] at h2
  rw [h1, hk.kern.mass] at h2
  have hp : (0:ℝ) < ξ' ^ n := pow_pos hξ n
  rw [abs_of_pos (inv_pos.2 hp)] at h2
  have hd := dS_pos S
  show ∫ v, h (‖S.symm v‖ / ξ') = _
  field_simp at h2 ⊢
  linarith

theorem pmass_eq {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (S : E ≃L[ℝ] E)
    {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ) : pmass h S a ξ = K₀ * dS S * (ξ / a) ^ n :=
  mass_eq hk S (div_pos hξ ha)

/-- Two-sided bound `K₀|det S|ξⁿ/a₁ⁿ ≤ p ≤ K₀|det S|ξⁿ/a₀ⁿ` for `a₀ ≤ a ≤ a₁`. -/
theorem pmass_bounds {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (S : E ≃L[ℝ] E)
    {a a₀ a₁ ξ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (ha₁ : a ≤ a₁) (hξ : 0 < ξ) :
    K₀ * dS S / a₁ ^ n * ξ ^ n ≤ pmass h S a ξ ∧ pmass h S a ξ ≤ K₀ * dS S / a₀ ^ n * ξ ^ n := by
  have hapos : 0 < a := lt_of_lt_of_le ha₀ ha
  rw [pmass_eq hk S hapos hξ, div_pow]
  have hK := hk.kern.mass_pos.le
  have hd := (dS_pos S).le
  have hc : 0 ≤ K₀ * dS S * ξ ^ n := by positivity
  have e1 : K₀ * dS S / a₁ ^ n * ξ ^ n = K₀ * dS S * ξ ^ n * (1 / a₁ ^ n) := by ring
  have e2 : K₀ * dS S * (ξ ^ n / a ^ n) = K₀ * dS S * ξ ^ n * (1 / a ^ n) := by ring
  have e3 : K₀ * dS S / a₀ ^ n * ξ ^ n = K₀ * dS S * ξ ^ n * (1 / a₀ ^ n) := by ring
  rw [e1, e2, e3]
  constructor
  · exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (pow_pos hapos n)
      (pow_le_pow_left₀ hapos.le ha₁ n)) hc
  · exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (pow_pos ha₀ n)
      (pow_le_pow_left₀ ha₀.le ha n)) hc

/-! ### (2) The time difference quotient of the flat kernel -/

/-- HYPOTHESES on the profile beyond `Prof`: Lipschitz with constant `Lh`. -/
def LipProf (h : ℝ → ℝ) (Lh : ℝ) : Prop := ∀ s s', |h s - h s'| ≤ Lh * |s - s'|

theorem kap_eq (h : ℝ → ℝ) (S : E ≃L[ℝ] E) {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ) (v : E) :
    kap h S (ξ / a) v = h (‖S.symm v‖ / ξ * a) := by
  unfold kap; congr 1; field_simp

/-- Pointwise key estimate. -/
theorem dq_key {h : ℝ → ℝ} {A R Lh : ℝ} (hP : Prof h A R) (hR : 0 ≤ R) (hL : LipProf h Lh)
    (hLh : 0 ≤ Lh) {t aa ab a₀ La η : ℝ} (ht : 0 ≤ t) (ha₀ : 0 < a₀) (haa : a₀ ≤ aa)
    (hab : a₀ ≤ ab) (hLa : 0 ≤ La) (hη : η ≠ 0) (hd : |ab - aa| ≤ La * |η|) :
    |(h (t * ab) - h (t * aa)) / η| ≤ Lh * R * La / a₀ := by
  have hB0 : 0 ≤ Lh * R * La / a₀ := by positivity
  by_cases h1 : R ≤ t * ab ∧ R ≤ t * aa
  · rw [hP.supp _ h1.1, hP.supp _ h1.2]; simp [hB0]
  · have htR : t ≤ R / a₀ := by
      rw [le_div_iff₀ ha₀]
      rcases not_and_or.1 h1 with h2 | h2
      · push_neg at h2; nlinarith
      · push_neg at h2; nlinarith
    rw [abs_div, div_le_iff₀ (abs_pos.2 hη)]
    calc |h (t * ab) - h (t * aa)| ≤ Lh * |t * ab - t * aa| := hL _ _
      _ = Lh * (t * |ab - aa|) := by rw [← mul_sub, abs_mul, abs_of_nonneg ht]
      _ ≤ Lh * (R / a₀ * (La * |η|)) := by
          apply mul_le_mul_of_nonneg_left _ hLh
          exact mul_le_mul htR hd (abs_nonneg _) (by positivity)
      _ = Lh * R * La / a₀ * |η| := by ring

/-- The pointwise constant `BI = Lh R L_a / a₀`. -/
def BIc (Lh R La a₀ : ℝ) : ℝ := Lh * R * La / a₀

/-- `|a(τ_b) − a(τ_a)| ≤ L_a |τ_b − τ_a|`. -/
theorem a_lip (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {La : ℝ}
    (hLa : ∀ τ, |a' τ| ≤ La) (τa τb : ℝ) : |a τb - a τa| ≤ La * |τb - τa| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ) (f := a) (f' := a')
    (fun x _ => (hda x).hasDerivWithinAt) (fun x _ => by simpa using hLa x) convex_univ
    (mem_univ τa) (mem_univ τb)
  simpa [Real.norm_eq_abs] using this

/-- **(2a) `hBI` discharged.** -/
theorem hBI_of {h : ℝ → ℝ} {A R Lh : ℝ} (hP : Prof h A R) (hR : 0 ≤ R) (hL : LipProf h Lh)
    (hLh : 0 ≤ Lh) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ)
    {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ)
    (τa τb : ℝ) (hne : τb ≠ τa) (v : E) :
    |(kap h S (ξ / a τb) v - kap h S (ξ / a τa) v) / (τb - τa)| ≤ BIc Lh R La a₀ := by
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  rw [kap_eq h S (hpos τb) hξ, kap_eq h S (hpos τa) hξ]
  exact dq_key hP hR hL hLh (by positivity) ha₀ (ha τa) (ha τb) hLa0 (sub_ne_zero.2 hne)
    (a_lip a a' hda hLa τa τb)

/-- Volume of the open unit ball. -/
def volB (n : ℕ) : ℝ := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1)

/-- The `L¹` constant: `MI = |det S| · BI · (R/a₀)ⁿ · vol(B₁) · ξⁿ`. -/
def MIc (S : E ≃L[ℝ] E) (Lh R La a₀ : ℝ) : ℝ := dS S * BIc Lh R La a₀ * (R / a₀) ^ n * volB n

theorem volB_nonneg : 0 ≤ volB n := measureReal_nonneg

/-- **(2b) `hMI` discharged.** -/
theorem hMI_of {h : ℝ → ℝ} {A R Lh : ℝ} (hP : Prof h A R) (hR : 0 ≤ R) (hL : LipProf h Lh)
    (hLh : 0 ≤ Lh) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ)
    {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ)
    (τa τb : ℝ) (hne : τb ≠ τa) :
    ∫ v, |(kap h S (ξ / a τb) v - kap h S (ξ / a τa) v) / (τb - τa)|
      ≤ MIc S Lh R La a₀ * ξ ^ n := by
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  set G : E → ℝ := fun v => |(kap h S (ξ / a τb) v - kap h S (ξ / a τa) v) / (τb - τa)| with hG
  have hsub := substE S G
  have hd := dS_pos S
  have eG : ∫ v, G v = dS S * ∫ w, G (S w) := by rw [hsub]; field_simp
  set r := R / a₀ * ξ with hr
  have hr0 : 0 ≤ r := by positivity
  have hBI0 : 0 ≤ BIc Lh R La a₀ := by unfold BIc; positivity
  have hpt : ∀ w : E, G (S w) ≤ (Metric.closedBall (0:E) r).indicator (fun _ => BIc Lh R La a₀) w := by
    intro w
    by_cases hw : w ∈ Metric.closedBall (0:E) r
    · rw [indicator_of_mem hw]
      exact hBI_of hP hR hL hLh S a a' hda ha₀ ha hLa hξ τa τb hne (S w)
    · rw [indicator_of_notMem hw]
      have hw' : r < ‖w‖ := by simpa using hw
      have hz : ∀ τ, kap h S (ξ / a τ) (S w) = 0 := by
        intro τ
        rw [kap_eq h S (hpos τ) hξ, ContinuousLinearEquiv.symm_apply_apply]
        apply hP.supp
        have h1 : R / a₀ < ‖w‖ / ξ := by
          rw [lt_div_iff₀ hξ]; rw [hr] at hw'; linarith
        have h2 : R ≤ ‖w‖ / ξ * a₀ := by
          rw [div_lt_iff₀ ha₀] at h1; linarith
        calc R ≤ ‖w‖ / ξ * a₀ := h2
          _ ≤ ‖w‖ / ξ * a τ := mul_le_mul_of_nonneg_left (ha τ) (by positivity)
      simp only [hG, hz, sub_self, zero_div, abs_zero, le_refl]
  have hint : Integrable ((Metric.closedBall (0:E) r).indicator fun _ => BIc Lh R La a₀) :=
    (integrableOn_const (C := BIc Lh R La a₀) measure_closedBall_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have hmono : ∫ w, G (S w) ≤ ∫ w, (Metric.closedBall (0:E) r).indicator
      (fun _ => BIc Lh R La a₀) w :=
    integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _) hint (ae_of_all _ hpt)
  rw [integral_indicator_const _ Metric.isClosed_closedBall.measurableSet,
    Measure.addHaar_real_closedBall _ _ hr0, finrank_euclideanSpace_fin, smul_eq_mul] at hmono
  rw [eG]
  calc dS S * ∫ w, G (S w) ≤ dS S * (r ^ n * volB n * BIc Lh R La a₀) :=
        mul_le_mul_of_nonneg_left hmono hd.le
    _ = MIc S Lh R La a₀ * ξ ^ n := by
        unfold MIc volB; rw [hr, mul_pow]; ring

/-! ### (3) The rate form -/

/-- The constant `Λ` of the rate form. -/
def rLam (A K₀ Lh R La a₀ a₁ Lip : ℝ) (S : E ≃L[ℝ] E) : ℝ :=
  let P1 := K₀ * dS S / a₀ ^ n
  let P0 := K₀ * dS S / a₁ ^ n
  let BI := BIc Lh R La a₀
  let MI := MIc S Lh R La a₀
  let Lρ := Lip * (‖(S : E →L[ℝ] E)‖ * R / a₀)
  max 1 (max A (max BI (max P1 (max MI (max P0⁻¹ (max (A * Lρ) (max (BI * Lρ)
    (max (P1 * Lρ) (MI * Lρ)))))))))

theorem rLam_bounds (A K₀ Lh R La a₀ a₁ Lip : ℝ) (S : E ≃L[ℝ] E) :
    let Λ := rLam A K₀ Lh R La a₀ a₁ Lip S
    let Lρ := Lip * (‖(S : E →L[ℝ] E)‖ * R / a₀)
    1 ≤ Λ ∧ A ≤ Λ ∧ BIc Lh R La a₀ ≤ Λ ∧ K₀ * dS S / a₀ ^ n ≤ Λ ∧ MIc S Lh R La a₀ ≤ Λ
      ∧ (K₀ * dS S / a₁ ^ n)⁻¹ ≤ Λ ∧ A * Lρ ≤ Λ ∧ BIc Lh R La a₀ * Lρ ≤ Λ
      ∧ K₀ * dS S / a₀ ^ n * Lρ ≤ Λ ∧ MIc S Lh R La a₀ * Lρ ≤ Λ := by
  intro Λ Lρ
  have e : Λ = max 1 (max A (max (BIc Lh R La a₀) (max (K₀ * dS S / a₀ ^ n)
      (max (MIc S Lh R La a₀) (max (K₀ * dS S / a₁ ^ n)⁻¹ (max (A * Lρ)
      (max (BIc Lh R La a₀ * Lρ) (max (K₀ * dS S / a₀ ^ n * Lρ) (MIc S Lh R La a₀ * Lρ))))))))) :=
    rfl
  rw [e]
  refine ⟨le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_left _ _))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_left _ _))))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_right _ _))))))))

/-- The error of `err5g` scales with `ξ` when `ρ = ξ ρ₁`. -/
theorem err5g_flat (N : ℕ) {BK vK BI vI M MI c L Lip ξ ρ₁ : ℝ} (hξ : 0 ≤ ξ) (A : ℝ) :
    err5g N BK vK BI vI M MI c L (Lip * (ξ * ρ₁) * M) (A * (Lip * (ξ * ρ₁)))
        ((Lip * (ξ * ρ₁)) ^ 2 * (A * M)) (Lip * (ξ * ρ₁) * MI) (BI * (Lip * (ξ * ρ₁)))
        ((Lip * (ξ * ρ₁)) ^ 2 * (BI * MI)) 1
      = ξ * err5g N BK vK BI vI M MI c L (Lip * ρ₁ * M) (A * (Lip * ρ₁))
        ((Lip * ρ₁) ^ 2 * (A * M)) (Lip * ρ₁ * MI) (BI * (Lip * ρ₁))
        ((Lip * ρ₁) ^ 2 * (BI * MI)) 1 := by
  rw [← err5g_scale N hξ]
  rw [show Lip * (ξ * ρ₁) * M = ξ * (Lip * ρ₁ * M) by ring,
    show A * (Lip * (ξ * ρ₁)) = ξ * (A * (Lip * ρ₁)) by ring,
    show (Lip * (ξ * ρ₁)) ^ 2 * (A * M) = ξ ^ 2 * ((Lip * ρ₁) ^ 2 * (A * M)) by ring,
    show Lip * (ξ * ρ₁) * MI = ξ * (Lip * ρ₁ * MI) by ring,
    show BI * (Lip * (ξ * ρ₁)) = ξ * (BI * (Lip * ρ₁)) by ring,
    show (Lip * (ξ * ρ₁)) ^ 2 * (BI * MI) = ξ ^ 2 * ((Lip * ρ₁) ^ 2 * (BI * MI)) by ring]

theorem prob_30 (N : ℕ) (hN : 2 ≤ N) :
    15 * ((N : ℝ) * (2 * Real.exp (-(3 * Real.log N)))) = 30 / (N : ℝ) ^ 2 := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have e : Real.exp (-(3 * Real.log N)) = ((N : ℝ) ^ 3)⁻¹ := by
    have h3 : 3 * Real.log N = Real.log ((N : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
    rw [Real.exp_neg, h3, Real.exp_log (by positivity)]
  rw [e]; field_simp; ring

theorem three_log_ge_one (N : ℕ) (hN : 2 ≤ N) : 1 ≤ 3 * Real.log N := by
  have h2 : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have := Real.log_two_gt_d9
  linarith

set_option maxHeartbeats 1600000 in
/-- **`prop:dotLN-diff` in the flat periodic case, rate form.**  Setting of
`CTG.FlatNPoint.flat_npoint`, kernel radius `‖S‖ (ξ/a₀) R < 1/2`, `ξ ≤ 1`, `a₀ ≤ a ≤ a₁`,
profile Lipschitz with constant `Lh` (HYPOTHESIS), `N ≥ 2` and `92416 Λ¹⁴·3 log N ≤ N ξⁿ`.
With probability at least `1 − 30/N²`, for every `i < N`, with `δ' = √(3 log N/(N ξⁿ))`:
(i)  `|Δ_η L_N f(i) − Δ_η L_ξ f(X_i)| ≤ (7320000 Λ²⁰/m₂) δ'/ξ`;
(ii) `|Δ_η L_N f(i) + Δ_η(Δ_{g_τ} f)(X_i)| ≤ (7320000 Λ²⁰/m₂) δ'/ξ + ξ² min{C₁/|η|, C₂}`. -/
theorem flat_npoint_rate {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          - (Lmet h m₂ S (a τb) ξ f (X i ω) - Lmet h m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)))}
      ≤ 30 / (N : ℝ) ^ 2 := by
  obtain ⟨l1, lA, lBI, lP1, lMI, lP0, lALρ, lBILρ, lP1Lρ, lMILρ⟩ :=
    rLam_bounds A K₀ Lh R La a₀ a₁ Lip S
  -- notation
  set Λ := rLam A K₀ Lh R La a₀ a₁ Lip S with hΛ
  set L := 3 * Real.log N with hLdef
  set x := ξ ^ n with hx
  set δ := Real.sqrt (L / (N * x)) with hδdef
  set ρ₁ := ‖(S : E →L[ℝ] E)‖ * R / a₀ with hρ₁
  set P1 := K₀ * dS S / a₀ ^ n with hP1
  set P0 := K₀ * dS S / a₁ ^ n with hP0
  set BI := BIc Lh R La a₀ with hBI
  set MI := MIc S Lh R La a₀ with hMI
  set Lρ := Lip * ρ₁ with hLρ
  set pa := pmass h S (a τa) ξ with hpa
  set pb := pmass h S (a τb) ξ with hpb
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hL1 : 1 ≤ L := three_log_ge_one N hN
  have hx0 : 0 < x := pow_pos hξ n
  have hx1 : x ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hd := dS_pos S
  have hK := hk.kern.mass_pos
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hP10 : 0 < P1 := by positivity
  have hP00 : 0 < P0 := by positivity
  have hBI0 : 0 ≤ BI := by simp only [hBI, BIc]; positivity
  have hMI0 : 0 ≤ MI := by simp only [hMI, MIc]; have := volB_nonneg (n := n); positivity
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  have hLρ0 : 0 ≤ Lρ := mul_nonneg hLip0 hρ₁0
  have hA0 : 0 ≤ A := le_trans (hP.nonneg 0) (hP.le 0)
  have hΛ0 : 0 < Λ := by linarith
  -- masses
  obtain ⟨pa0, pa1⟩ := pmass_bounds hk S ha₀ (ha τa) (ha₁ τa) hξ
  obtain ⟨pb0, pb1⟩ := pmass_bounds hk S ha₀ (ha τb) (ha₁ τb) hξ
  have hMx : max pa pb ≤ P1 * x := max_le pa1 pb1
  have hMx0 : 0 ≤ max pa pb := le_trans (mul_nonneg hP00.le hx0.le) (le_trans pa0 (le_max_left _ _))
  have hmn : P0 * x ≤ min pa pb := le_min pa0 pb0
  have hc : 0 < min pa pb := lt_of_lt_of_le (mul_pos hP00 hx0) hmn
  have hci : (min pa pb)⁻¹ ≤ Λ * x⁻¹ := by
    calc (min pa pb)⁻¹ ≤ (P0 * x)⁻¹ := inv_anti₀ (by positivity) hmn
      _ = P0⁻¹ * x⁻¹ := mul_inv _ _
      _ ≤ Λ * x⁻¹ := mul_le_mul_of_nonneg_right lP0 (by positivity)
  -- smallness and Ctx
  have hNx : (N : ℝ) * x ≠ 0 := (mul_pos hN' hx0).ne'
  have hδ : δ ^ 2 * (N * x) = L := by
    rw [hδdef, Real.sq_sqrt (div_nonneg (by linarith) (mul_pos hN' hx0).le)]; field_simp
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hPp : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * x) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ 1 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((1 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hPp] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ l1
    nlinarith
  have C : Ctx N Λ x x⁻¹ δ L :=
    { hN := hN0, hΛ := l1, hx := hx0, hx1 := hx1, hxy := mul_inv_cancel₀ hx0.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL1 }
  -- constant bounds
  have hvK : A * max pa pb ≤ Λ ^ 2 * x := by
    calc A * max pa pb ≤ Λ * (P1 * x) := mul_le_mul lA hMx hMx0 hΛ0.le
      _ ≤ Λ * (Λ * x) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right lP1 hx0.le) hΛ0.le
      _ = Λ ^ 2 * x := by ring
  have hM' : max pa pb ≤ Λ * x := hMx.trans (mul_le_mul_of_nonneg_right lP1 hx0.le)
  have hMIx : MI * x ≤ Λ * x := mul_le_mul_of_nonneg_right lMI hx0.le
  have hvI : BI * (MI * x) ≤ Λ ^ 2 * x := by
    calc BI * (MI * x) ≤ Λ * (Λ * x) := mul_le_mul lBI hMIx (by positivity) hΛ0.le
      _ = Λ ^ 2 * x := by ring
  have hcD1 : (1:ℝ)⁻¹ ≤ Λ ^ 2 := by rw [inv_one]; nlinarith
  have hsmall := C.small'_le hA0 lA (mul_nonneg hA0 hMx0) hvK hMx0 hM' hc hci one_pos hcD1 hsm
  have hMF : Lρ * max pa pb ≤ Λ * x := by
    calc Lρ * max pa pb ≤ Lρ * (P1 * x) := mul_le_mul_of_nonneg_left hMx hLρ0
      _ = (P1 * Lρ) * x := by ring
      _ ≤ Λ * x := mul_le_mul_of_nonneg_right lP1Lρ hx0.le
  have hvF : Lρ ^ 2 * (A * max pa pb) ≤ Λ ^ 2 * x := by
    calc Lρ ^ 2 * (A * max pa pb) ≤ Lρ ^ 2 * (A * (P1 * x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMx hA0) (sq_nonneg _)
      _ = (A * Lρ) * (P1 * Lρ) * x := by ring
      _ ≤ Λ * Λ * x := mul_le_mul_of_nonneg_right
          (mul_le_mul lALρ lP1Lρ (by positivity) hΛ0.le) hx0.le
      _ = Λ ^ 2 * x := by ring
  have hMFi : Lρ * (MI * x) ≤ Λ * x := by
    calc Lρ * (MI * x) = (MI * Lρ) * x := by ring
      _ ≤ Λ * x := mul_le_mul_of_nonneg_right lMILρ hx0.le
  have hvFi : Lρ ^ 2 * (BI * (MI * x)) ≤ Λ ^ 2 * x := by
    calc Lρ ^ 2 * (BI * (MI * x)) = (BI * Lρ) * (MI * Lρ) * x := by ring
      _ ≤ Λ * Λ * x := mul_le_mul_of_nonneg_right
          (mul_le_mul lBILρ lMILρ (by positivity) hΛ0.le) hx0.le
      _ = Λ ^ 2 * x := by ring
  have hMIx0 : 0 ≤ MI * x := mul_nonneg hMI0 hx0.le
  have he := err5g_le C hA0 lA (mul_nonneg hA0 hMx0) hvK hBI0 lBI (mul_nonneg hBI0 hMIx0) hvI
    hMx0 hM' hMIx0 hMIx hc hci one_pos hcD1
    (mul_nonneg hA0 hLρ0) lALρ (mul_nonneg (sq_nonneg _) (mul_nonneg hA0 hMx0)) hvF
    (mul_nonneg hLρ0 hMx0) hMF
    (mul_nonneg hBI0 hLρ0) lBILρ (mul_nonneg (sq_nonneg _) (mul_nonneg hBI0 hMIx0)) hvFi
    (mul_nonneg hLρ0 hMIx0) hMFi
  -- the composite statement with ρ = ξ ρ₁
  have hρeq : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) = ξ * ρ₁ := by rw [hρ₁]; field_simp
  have H := flat_npoint X h_indep hX hlaw N hN0 hk hm₂ hP hR hf hM hM₄ hper hLip0 hLip S a a'
    hda ha₀ ha hLa hξ (le_of_eq hρeq) (by rw [← hρeq]; exact hρh) τa τb hne
    (hBI_of hP hR hLP hLh S a a' hda ha₀ ha hLa hξ τa τb hne)
    (hMI_of hP hR hLP hLh S a a' hda ha₀ ha hLa hξ τa τb hne) (by linarith)
    hsmall.1 hsmall.2
  rw [err5g_flat N hξ.le A] at H
  rw [← prob_30 N hN]
  refine le_trans (measureReal_mono ?_) H
  intro ω hω
  obtain ⟨i, hi, hfail⟩ := hω
  refine ⟨i, hi, fun hok => hfail ?_⟩
  -- the err5g bound implies the rate bound
  set e := err5g N A (A * max pa pb) BI (BI * (MI * x)) (max pa pb) (MI * x) (min pa pb) L
    (Lip * ρ₁ * max pa pb) (A * (Lip * ρ₁)) ((Lip * ρ₁) ^ 2 * (A * max pa pb))
    (Lip * ρ₁ * (MI * x)) (BI * (Lip * ρ₁)) ((Lip * ρ₁) ^ 2 * (BI * (MI * x))) 1 with he_def
  have hbound : 2 / (m₂ * ξ ^ 2) * (ξ * e)
      ≤ 7320000 * Λ ^ 20 / m₂ * δ / ξ := by
    have h1 : 2 / (m₂ * ξ ^ 2) * (ξ * e) = 2 / m₂ * e / ξ := by field_simp
    rw [h1]
    have h2 : 2 / m₂ * e ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    calc 2 / m₂ * e / ξ ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) / ξ :=
          div_le_div_of_nonneg_right h2 hξ.le
      _ = 7320000 * Λ ^ 20 / m₂ * δ / ξ := by ring
  exact ⟨hok.1.trans hbound, hok.2.trans (add_le_add hbound le_rfl)⟩

end CTG.FlatNPointRate

#print axioms CTG.FlatNPointRate.mass_eq
#print axioms CTG.FlatNPointRate.hBI_of
#print axioms CTG.FlatNPointRate.hMI_of
#print axioms CTG.FlatNPointRate.flat_npoint_rate
