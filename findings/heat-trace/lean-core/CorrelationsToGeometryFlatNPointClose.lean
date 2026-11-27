/-
Thirty-third file: further gaps of the flat N-point statement.  Imports
`CorrelationsToGeometryFlatNPointFinal` (compiled module under `.tools/leanbuild`); namespace
`CTG.FlatNPointClose`; check with `./check_flat_npoint_close.sh`.
(1) `Gs_hasDerivAt`, `Lmet_hasDerivAt`: `τ ↦ L^τ_ξ f(x)` is differentiable (dominated differentiation in the
scale parameter, derivative in `f`; needs `f ∈ C¹` with bounded derivative), and `dotL_flat_full`: for `f ∈ C⁴`,
periodic, and a differentiable conformal factor with `a ≥ a₀ > 0`, `|a'| ≤ L_a`, the derivative `DL` exists and
`|DL − 2 a'(τ) lapG S f x / a(τ)³| ≤ ξ² M₄ ‖S‖⁴ μ₄ L_a/(3 m₂ K₀ a₀⁵)`.  This is `prop:dotL` in the flat conformal
case with constant density, WITHOUT a differentiability hypothesis.
(2) Deterministic ingredients only for a statement on all pairs of times of a window: `sampAvg_close`,
`perK_time_lip`, `sampAvg_transfer`, `grid_compare`.  The window statement itself is NOT assembled.
NOT formalised: that window statement, Gaussian profiles.  This file is the state of an interrupted sub-task,
accepted by Lean as it stands.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatNPointFinal

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointClose

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### (1) Differentiability in time of the population operator -/

/-- `G(c) = ∫ k(z) f(x + S(c z)) dz`, `k(z) = h(‖z‖)`. -/
def Gs (h : ℝ → ℝ) (S : E ≃L[ℝ] E) (f : E → ℝ) (x : E) (c : ℝ) : ℝ :=
  ∫ z : E, h ‖z‖ * f (x + S (c • z))

/-- Its derivative `∫ k(z) Df(x + S(c z))[S z] dz`. -/
def Gs' (h : ℝ → ℝ) (S : E ≃L[ℝ] E) (f : E → ℝ) (x : E) (c : ℝ) : ℝ :=
  ∫ z : E, h ‖z‖ * fderiv ℝ f (x + S (c • z)) (S z)

theorem inner_deriv (S : E ≃L[ℝ] E) (x z : E) (c : ℝ) :
    HasDerivAt (fun c : ℝ => x + S (c • z)) (S z) c := by
  have e : (fun c : ℝ => x + S (c • z)) = fun c => x + c • S z := funext fun c => by
    rw [map_smul]
  rw [e]
  have := ((hasDerivAt_id c).smul_const (S z)).const_add x
  simpa using this

/-- **Dominated differentiation in the scale parameter.** -/
theorem Gs_hasDerivAt {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {M₁ : ℝ} (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁) (S : E ≃L[ℝ] E) (x : E)
    (c₀ : ℝ) : HasDerivAt (Gs h S f x) (Gs' h S f x c₀) c₀ := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfc : Continuous f := hf.continuous
  have hcd : Continuous fun y => fderiv ℝ f y := hf.continuous_fderiv (by norm_num)
  have hk0 : Integrable (fun z : E => h ‖z‖) := hk.kern.int0
  have hk1 : Integrable (fun z : E => ‖z‖ * h ‖z‖) := hk.int1
  have hnn : ∀ z : E, 0 ≤ h ‖z‖ := hk.kern.nonneg
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  set σ := ‖(S : E →L[ℝ] E)‖ with hσ
  have hSz : ∀ w : E, ‖S w‖ ≤ σ * ‖w‖ := fun w => (S : E →L[ℝ] E).le_opNorm w
  have hder : ∀ (z : E) (c : ℝ), HasDerivAt (fun c => h ‖z‖ * f (x + S (c • z)))
      (h ‖z‖ * fderiv ℝ f (x + S (c • z)) (S z)) c := by
    intro z c
    have := (hfd (x + S (c • z))).hasFDerivAt.comp_hasDerivAt c (inner_deriv S x z c)
    exact this.const_mul _
  have hinner : ∀ c : ℝ, Continuous fun z : E => x + S (c • z) := fun c =>
    continuous_const.add (S.continuous.comp (continuous_const.smul continuous_id))
  have hFm : ∀ c : ℝ, AEStronglyMeasurable (fun z : E => h ‖z‖ * f (x + S (c • z))) volume :=
    fun c => hk0.aestronglyMeasurable.mul ((hfc.comp (hinner c)).aestronglyMeasurable)
  have hint : Integrable (fun z : E => h ‖z‖ * f (x + S (c₀ • z))) := by
    have hb : Integrable (fun z : E => |f x| * h ‖z‖ + M₁ * σ * |c₀| * (‖z‖ * h ‖z‖)) :=
      (hk0.const_mul _).add (hk1.const_mul _)
    refine hb.mono' (hFm c₀) (ae_of_all _ fun z => ?_)
    have hl := lip_of_fderiv hfd hM₁ x (x + S (c₀ • z))
    rw [add_sub_cancel_left] at hl
    have h2 : ‖S (c₀ • z)‖ ≤ σ * (|c₀| * ‖z‖) := by
      have := hSz (c₀ • z); rwa [norm_smul, Real.norm_eq_abs] at this
    have h3 : |f (x + S (c₀ • z))| ≤ |f x| + M₁ * σ * |c₀| * ‖z‖ := by
      have := abs_sub_abs_le_abs_sub (f (x + S (c₀ • z))) (f x)
      have h4 : M₁ * ‖S (c₀ • z)‖ ≤ M₁ * (σ * (|c₀| * ‖z‖)) := mul_le_mul_of_nonneg_left h2 hM0
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn z)]
    calc h ‖z‖ * |f (x + S (c₀ • z))| ≤ h ‖z‖ * (|f x| + M₁ * σ * |c₀| * ‖z‖) :=
          mul_le_mul_of_nonneg_left h3 (hnn z)
      _ = |f x| * h ‖z‖ + M₁ * σ * |c₀| * (‖z‖ * h ‖z‖) := by ring
  have hF'm : AEStronglyMeasurable
      (fun z : E => h ‖z‖ * fderiv ℝ f (x + S (c₀ • z)) (S z)) volume :=
    hk0.aestronglyMeasurable.mul
      (((hcd.comp (hinner c₀)).clm_apply S.continuous).aestronglyMeasurable)
  have hbnd : ∀ᵐ z ∂(volume : Measure E), ∀ c ∈ (univ : Set ℝ),
      ‖h ‖z‖ * fderiv ℝ f (x + S (c • z)) (S z)‖ ≤ M₁ * σ * (‖z‖ * h ‖z‖) := by
    refine ae_of_all _ fun z c _ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn z)]
    have h1 : |fderiv ℝ f (x + S (c • z)) (S z)| ≤ M₁ * (σ * ‖z‖) := by
      have := (fderiv ℝ f (x + S (c • z))).le_opNorm (S z)
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul (hM₁ _) (hSz z) (norm_nonneg _) hM0)
    calc h ‖z‖ * |fderiv ℝ f (x + S (c • z)) (S z)| ≤ h ‖z‖ * (M₁ * (σ * ‖z‖)) :=
          mul_le_mul_of_nonneg_left h1 (hnn z)
      _ = M₁ * σ * (‖z‖ * h ‖z‖) := by ring
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure E))
    (x₀ := c₀) (s := univ) univ_mem (Eventually.of_forall hFm) hint hF'm hbnd
    (hk1.const_mul _) (ae_of_all _ fun z c _ => hder z c)
  exact this.2

theorem PG_scale {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (S : E ≃L[ℝ] E)
    {c : ℝ} (hc : 0 < c) (f : E → ℝ) (x : E) : PG h S c f x = Gs h S f x c / K₀ := by
  rw [PG_eq h S hc]
  unfold avgOp Fx Gs
  rw [hk.kern.mass]
  simp only [zero_add]

/-- **Differentiability of `τ ↦ L^τ_ξ f(x)`** with explicit derivative. -/
theorem Lmet_hasDerivAt {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) {f : E → ℝ}
    (hf : ContDiff ℝ 1 f) {M₁ : ℝ} (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) (hpos : ∀ τ, 0 < a τ) {ξ : ℝ}
    (hξ : 0 < ξ) (x : E) (τ : ℝ) :
    HasDerivAt (fun t => Lmet h m₂ S (a t) ξ f x)
      (2 / (m₂ * ξ ^ 2) * (-(Gs' h S f x (ξ / a τ) * ((0 * a τ - ξ * a' τ) / a τ ^ 2) / K₀))) τ := by
  have hc : HasDerivAt (fun t => ξ / a t) ((0 * a τ - ξ * a' τ) / a τ ^ 2) τ :=
    (hasDerivAt_const τ ξ).div (hda τ) (hpos τ).ne'
  have hG := (Gs_hasDerivAt hk hf hM₁ S x (ξ / a τ)).comp τ hc
  have hfun : (fun t => Lmet h m₂ S (a t) ξ f x)
      = fun t => 2 / (m₂ * ξ ^ 2) * (f x - (Gs h S f x ∘ fun t => ξ / a t) t / K₀) := by
    funext t
    unfold Lmet
    rw [PG_scale hk S (div_pos hξ (hpos t)) f x]
    rfl
  rw [hfun]
  exact ((hG.div_const K₀).const_sub (f x)).const_mul _

/-- **(1) `prop:dotL` in the flat case, without the differentiability hypothesis.**  For `f ∈ C⁴`,
`ℤⁿ`-periodic, and a differentiable conformal factor, `τ ↦ L^τ_ξ f(x)` is differentiable and its derivative
`DL` satisfies `|DL − 2a'(τ) Δ_{g₀} f(x)/a(τ)³| ≤ ξ² M₄‖S‖⁴μ₄L_a/(3m₂K₀a₀⁵)`. -/
theorem dotL_flat_full {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {f : E → ℝ} (hf : ContDiff ℝ 4 f) (hper : Per f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : E) (τ : ℝ) :
    ∃ DL, HasDerivAt (fun t => Lmet h m₂ S (a t) ξ f x) DL τ ∧
      |DL - 2 * a' τ * lapG S f x / a τ ^ 3|
        ≤ ξ ^ 2 * (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)) := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  obtain ⟨M₁, -, hM₁⟩ := fderiv_bound_of_per hf1 hper
  have hpos : ∀ t, 0 < a t := fun t => lt_of_lt_of_le ha₀ (ha t)
  have hD := Lmet_hasDerivAt (m₂ := m₂) hk hf1 hM₁ S a a' hda hpos hξ x τ
  exact ⟨_, hD, dotL_flat hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ x τ hD⟩

/-! ### (2) Deterministic ingredients of the window statement -/

/-- Averages of kernels that differ by at most `e` differ by at most `e`. -/
theorem sampAvg_close {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) {K₁ K₂ : E → E → ℝ}
    {e : ℝ} (hK : ∀ x z, |K₂ x z - K₁ x z| ≤ e) (j : ℕ) (ω : Ω) :
    |sampAvg X N K₂ j ω - sampAvg X N K₁ j ω| ≤ e := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  unfold sampAvg
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
  calc 1 / (N : ℝ) * |∑ k ∈ Finset.range N, (K₂ (X j ω) (X k ω) - K₁ (X j ω) (X k ω))|
      ≤ 1 / (N : ℝ) * ∑ k ∈ Finset.range N, e :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k _ => hK _ _)) (by positivity)
    _ = e := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

/-- The periodised kernel is Lipschitz in time with constant `BI = Lh R L_a/a₀`. -/
theorem perK_time_lip {h : ℝ → ℝ} {A R Lh : ℝ} (hP : Prof h A R) (hR : 0 ≤ R)
    (hL : LipProf h Lh) (hLh : 0 ≤ Lh) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (s t : ℝ) (x z : E) :
    |perK (kap h S (ξ / a t)) x z - perK (kap h S (ξ / a s)) x z|
      ≤ BIc Lh R La a₀ * |t - s| := by
  by_cases hts : t = s
  · subst hts; simp only [sub_self, abs_zero, mul_zero, le_refl]
  · have hb := hBI_of hP hR hL hLh S a a' hda ha₀ ha hLa hξ s t hts (fr (z - x))
    rw [abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hts))] at hb
    exact hb

/-- **Transfer of the lower bound of the sample normalisation** from a grid time `g` to every time
`τ` with `BI·|τ − g| ≤ c/4`: if the sample normalisation at `g` is `≥ c/2`, it is `≥ c/4` at `τ`. -/
theorem sampAvg_transfer {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N)
    {h : ℝ → ℝ} {A R Lh : ℝ} (hP : Prof h A R) (hR : 0 ≤ R)
    (hL : LipProf h Lh) (hLh : 0 ≤ Lh) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) {c g τ : ℝ}
    (hgr : BIc Lh R La a₀ * |τ - g| ≤ c / 4) (j : ℕ) (ω : Ω)
    (hg : c / 2 ≤ sampAvg X N (perK (kap h S (ξ / a g))) j ω) :
    c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a τ))) j ω := by
  have := sampAvg_close X hN (fun x z => perK_time_lip hP hR hL hLh S a a' hda ha₀ ha hLa hξ
    g τ x z) j ω
  have := (abs_le.1 this).1
  linarith

/-- **Comparison of difference quotients at a pair and at a nearby grid pair.**  If `F` is
`ℒ`-Lipschitz, `|τa − ga|, |τb − gb| ≤ δg`, `|τb − τa| ≥ η₀` and `4δg ≤ η₀`, then the two difference
quotients differ by at most `4ℒδg/η₀`. -/
theorem grid_compare {F : ℝ → ℝ} {ℒ η₀ δg τa τb ga gb : ℝ} (hℒ : 0 ≤ ℒ)
    (hF : ∀ s t, |F s - F t| ≤ ℒ * |s - t|) (hη₀ : 0 < η₀) (hδ : 0 ≤ δg) (h4 : 4 * δg ≤ η₀)
    (ha : |τa - ga| ≤ δg) (hb : |τb - gb| ≤ δg) (hη : η₀ ≤ |τb - τa|) :
    |(F τb - F τa) / (τb - τa) - (F gb - F ga) / (gb - ga)| ≤ 4 * ℒ * δg / η₀ := by
  set η := τb - τa
  set η' := gb - ga
  have hdiff : |η - η'| ≤ 2 * δg := by
    have : η - η' = (τb - gb) - (τa - ga) := by simp only [η, η']; ring
    rw [this]; exact (abs_sub _ _).trans (by linarith)
  have hη'0 : η₀ / 2 ≤ |η'| := by
    have := abs_sub_abs_le_abs_sub η η'
    linarith
  have hηpos : 0 < |η| := by linarith
  have hη'pos : 0 < |η'| := by linarith
  set D := F τb - F τa
  set D' := F gb - F ga
  have hDD : |D - D'| ≤ 2 * ℒ * δg := by
    have : D - D' = (F τb - F gb) - (F τa - F ga) := by simp only [D, D']; ring
    rw [this]
    have h1 := (hF τb gb).trans (mul_le_mul_of_nonneg_left hb hℒ)
    have h2 := (hF τa ga).trans (mul_le_mul_of_nonneg_left ha hℒ)
    exact (abs_sub _ _).trans (by linarith)
  have hD' : |D'| ≤ ℒ * |η'| := hF gb ga
  have hη0 : η ≠ 0 := abs_pos.1 hηpos
  have hη'0' : η' ≠ 0 := abs_pos.1 hη'pos
  have e : D / η - D' / η' = (D - D') / η + D' * (η' - η) / (η * η') := by
    field_simp; ring
  rw [e]
  have t1 : |(D - D') / η| ≤ 2 * ℒ * δg / η₀ := by
    rw [abs_div]
    calc |D - D'| / |η| ≤ 2 * ℒ * δg / |η| := div_le_div_of_nonneg_right hDD hηpos.le
      _ ≤ 2 * ℒ * δg / η₀ := div_le_div_of_nonneg_left (by positivity) hη₀ hη
  have t2 : |D' * (η' - η) / (η * η')| ≤ 2 * ℒ * δg / η₀ := by
    rw [abs_div, abs_mul, abs_mul]
    have hnum : |D'| * |η' - η| ≤ ℒ * |η'| * (2 * δg) :=
      mul_le_mul hD' (by rw [abs_sub_comm]; exact hdiff) (abs_nonneg _) (by positivity)
    calc |D'| * |η' - η| / (|η| * |η'|) ≤ ℒ * |η'| * (2 * δg) / (|η| * |η'|) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 2 * ℒ * δg / |η| := by field_simp
      _ ≤ 2 * ℒ * δg / η₀ := div_le_div_of_nonneg_left (by positivity) hη₀ hη
  calc |(D - D') / η + D' * (η' - η) / (η * η')|
      ≤ |(D - D') / η| + |D' * (η' - η) / (η * η')| := abs_add_le _ _
    _ ≤ 2 * ℒ * δg / η₀ + 2 * ℒ * δg / η₀ := add_le_add t1 t2
    _ = 4 * ℒ * δg / η₀ := by ring

end CTG.FlatNPointClose

#print axioms CTG.FlatNPointClose.Gs_hasDerivAt
#print axioms CTG.FlatNPointClose.Lmet_hasDerivAt
#print axioms CTG.FlatNPointClose.dotL_flat_full
#print axioms CTG.FlatNPointClose.sampAvg_transfer
#print axioms CTG.FlatNPointClose.grid_compare
