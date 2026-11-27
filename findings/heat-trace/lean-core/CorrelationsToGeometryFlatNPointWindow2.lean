/-
Forty-first file: the window statement of the flat N-point theorem without free parameters, and measurability.
Imports `CorrelationsToGeometryFlatNPointWindow` (compiled module under `.tools/leanbuild`); namespace
`CTG.FlatNPointWindow2`; check with `./check_flat_npoint_window2.sh`.
(1) `iter2_bound_of_per`, `lapG_bound`, `flat_npoint_window_M2`: the bound for `lapG S f` follows from a bound
`M₂` of the second derivative, which exists for periodic `C²` functions.
(2) `wStar` (explicit grid width), `flat_npoint_window_auto` (no free grid width), `flat_npoint_window_N2`:
with `L = 4 log N` and the single numerical condition `92416 Λ¹⁴ (4 log N) ≤ N ξⁿ`, the exceptional set of the
window statement has (outer) probability at most `32 D²/N²`, `D = Dwin` explicit and independent of `N`
(it contains negative powers of `ξ`).
(3) `exists_param_measurable`, `LN_cont`, `Lmet_cont`, `window_set_measurable`,
`flat_npoint_window_set_measurable`: the exceptional set of `flat_npoint_window` is measurable.
HYPOTHESIS of part (3): `0 < h 0` (the self term keeps the sample normalisation positive).
NOT formalised: pairs with `|τb − τa| < η₀`; Gaussian profiles (only the truncated one of the thirty-eighth
file); the constants are not evaluated.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 26/27 November 2026.
-/
import CorrelationsToGeometryFlatNPointWindow

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4 CTG.FlatNPoint
  CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointClose CTG.FlatNPointWindow

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointWindow2

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### (1) A bound for `lapG` -/

/-- A periodic `C²` function has a bounded second derivative. -/
theorem iter2_bound_of_per {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hper : Per f) :
    ∃ M₂, 0 ≤ M₂ ∧ ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂ := by
  have hc : Continuous fun y => iteratedFDeriv ℝ 2 f y :=
    hf.continuous_iteratedFDeriv (by norm_num)
  obtain ⟨C, hC⟩ := cube_compact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  set g := y - fr y
  have hg : g ∈ Lat (n := n) := sub_fr_mem y
  have hfun : (fun w => f (g + w)) = f := funext fun w => hper g hg w
  have e : iteratedFDeriv ℝ 2 f y = iteratedFDeriv ℝ 2 f (fr y) := by
    have := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) 2 g (fr y)
    rw [hfun] at this
    rw [this]; congr 1; simp [g]
  rw [e]
  exact (hC _ (fr_mem_cube y)).trans (le_max_left _ _)

/-- `G₂ = n ‖S‖² M₂`. -/
def Gtwo (S : E ≃L[ℝ] E) (M₂ : ℝ) : ℝ := (n : ℝ) * (‖(S : E →L[ℝ] E)‖ ^ 2 * M₂)

theorem Gtwo_nonneg (S : E ≃L[ℝ] E) {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : 0 ≤ Gtwo S M₂ := by
  unfold Gtwo; positivity

/-- **Explicit bound**: `|lapG S f x| ≤ n ‖S‖² M₂` if `‖D²f‖ ≤ M₂`. -/
theorem lapG_bound (S : E ≃L[ℝ] E) {f : E → ℝ} {M₂ : ℝ}
    (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂) (x : E) : |lapG S f x| ≤ Gtwo S M₂ := by
  have hM0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  unfold lapG Gtwo
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin n, |iteratedFDeriv ℝ 2 f x (fun _ => S (eb i))|
      ≤ ‖(S : E →L[ℝ] E)‖ ^ 2 * M₂ := by
    intro i
    have h1 := (iteratedFDeriv ℝ 2 f x).le_opNorm (fun _ => S (eb i))
    rw [← Real.norm_eq_abs]
    refine h1.trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hS : ‖S (eb i)‖ ≤ ‖(S : E →L[ℝ] E)‖ := by
      have h1 : ‖(S : E →L[ℝ] E) (eb i)‖ ≤ ‖(S : E →L[ℝ] E)‖ * ‖eb i‖ :=
        (S : E →L[ℝ] E).le_opNorm (eb i)
      have h2 : ‖eb (n := n) i‖ = 1 := by
        rw [EuclideanSpace.norm_single]; exact norm_one
      rw [h2, mul_one] at h1
      exact h1
    calc ‖iteratedFDeriv ℝ 2 f x‖ * ‖S (eb i)‖ ^ 2 ≤ M₂ * ‖(S : E →L[ℝ] E)‖ ^ 2 :=
        mul_le_mul (hM₂ x) (pow_le_pow_left₀ (norm_nonneg _) hS 2) (by positivity) hM0
      _ = ‖(S : E →L[ℝ] E)‖ ^ 2 * M₂ := by ring
  calc ∑ i, |iteratedFDeriv ℝ 2 f x (fun _ => S (eb i))|
      ≤ ∑ _i : Fin n, ‖(S : E →L[ℝ] E)‖ ^ 2 * M₂ := Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * (‖(S : E →L[ℝ] E)‖ ^ 2 * M₂) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- For a periodic `C²` function there is a bound `G₂ ≥ 0` of `|lapG S f|`. -/
theorem exists_lapG_bound (S : E ≃L[ℝ] E) {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hper : Per f) :
    ∃ G₂, 0 ≤ G₂ ∧ ∀ x, |lapG S f x| ≤ G₂ := by
  obtain ⟨M₂, hM0, hM₂⟩ := iter2_bound_of_per hf hper
  exact ⟨Gtwo S M₂, Gtwo_nonneg S hM0, lapG_bound S hM₂⟩

set_option maxHeartbeats 800000 in
/-- **`flat_npoint_window` with `G₂ = n‖S‖²M₂`** (no hypothesis on `lapG`; `M₂` bounds `‖D²f‖`). -/
theorem flat_npoint_window_M2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ M₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂)
    (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * L ≤ N * ξ ^ n)
    {p q w η₀ : ℝ} (hw : 0 < w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀)
    (hwc : BIc Lh R La a₀ * w ≤ K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
    (hwE : 4 * (LNlip m₂ ξ A (BIc Lh R La a₀) (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
              (K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
            + (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + Gtwo S M₂ * (2 * La / a₀ ^ 3))) * w
          ≤ rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ * η₀) :
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
            + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa))}
      ≤ ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) * (N * (2 * Real.exp (-L)))
        + ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) :=
  flat_npoint_window X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper hM₁ S
    (lapG_bound S hM₂) a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh hL1 hNL hw hη₀ h4 hwc hwE

/-! ### (2) The choice of the grid width -/

/-- The grid width `w* = min{η₀/4, c/(4(BI+1)), Er η₀/(4(Ls+1))}`. -/
def wStar (η₀ c BI Er Ls : ℝ) : ℝ :=
  min (η₀ / 4) (min (c / (4 * (BI + 1))) (Er * η₀ / (4 * (Ls + 1))))

theorem wStar_props {η₀ c BI Er Ls : ℝ} (hη₀ : 0 < η₀) (hc : 0 < c) (hBI : 0 ≤ BI)
    (hEr : 0 < Er) (hLs : 0 ≤ Ls) :
    0 < wStar η₀ c BI Er Ls ∧ 4 * wStar η₀ c BI Er Ls ≤ η₀
      ∧ BI * wStar η₀ c BI Er Ls ≤ c / 4 ∧ 4 * Ls * wStar η₀ c BI Er Ls ≤ Er * η₀ := by
  set w := wStar η₀ c BI Er Ls with hw
  have h1 : w ≤ η₀ / 4 := min_le_left _ _
  have h2 : w ≤ c / (4 * (BI + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : w ≤ Er * η₀ / (4 * (Ls + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hpos : 0 < w := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨hpos, by linarith, ?_, ?_⟩
  · have e : (BI + 1) * (c / (4 * (BI + 1))) = c / 4 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ BI + 1)]
  · have e : 4 * (Ls + 1) * (Er * η₀ / (4 * (Ls + 1))) = Er * η₀ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 4 * (Ls + 1))]

theorem inv_min_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 1 / min x y ≤ 1 / x + 1 / y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; have : 0 < 1 / y := by positivity
    linarith
  · rw [min_eq_right h]; have : 0 < 1 / x := by positivity
    linarith

theorem one_div_wStar_le {η₀ c BI Er Ls : ℝ} (hη₀ : 0 < η₀) (hc : 0 < c) (hBI : 0 ≤ BI)
    (hEr : 0 < Er) (hLs : 0 ≤ Ls) :
    1 / wStar η₀ c BI Er Ls ≤ 4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) / (Er * η₀) := by
  unfold wStar
  refine (inv_min_le (by positivity) (lt_min (by positivity) (by positivity))).trans ?_
  have h1 := inv_min_le (x := c / (4 * (BI + 1))) (y := Er * η₀ / (4 * (Ls + 1)))
    (by positivity) (by positivity)
  have e1 : 1 / (η₀ / 4) = 4 / η₀ := one_div_div _ _
  have e2 : 1 / (c / (4 * (BI + 1))) = 4 * (BI + 1) / c := one_div_div _ _
  have e3 : 1 / (Er * η₀ / (4 * (Ls + 1))) = 4 * (Ls + 1) / (Er * η₀) := one_div_div _ _
  rw [e2, e3] at h1
  rw [e1]
  linarith

/-- `⌊x/w⌋₊ + 1 ≤ 1 + max x 0 · (1/w)`. -/
theorem floor_succ_le {x w : ℝ} (hw : 0 < w) :
    ((⌊x / w⌋₊ : ℕ) : ℝ) + 1 ≤ 1 + max x 0 * (1 / w) := by
  have h1 : ((⌊x / w⌋₊ : ℕ) : ℝ) ≤ max x 0 / w := by
    calc ((⌊x / w⌋₊ : ℕ) : ℝ) ≤ ((⌊max x 0 / w⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast Nat.floor_mono (div_le_div_of_nonneg_right (le_max_left _ _) hw.le)
      _ ≤ max x 0 / w := Nat.floor_le (div_nonneg (le_max_right _ _) hw.le)
  have e : max x 0 / w = max x 0 * (1 / w) := by ring
  linarith

/-- The sum of the Lipschitz constants in the condition on the grid width. -/
def Lsum (m₂ ξ A Lh R La a₀ M₁ K₀ a₁ M₄ μ₄ M₂ : ℝ) (S : E ≃L[ℝ] E) : ℝ :=
  LNlip m₂ ξ A (BIc Lh R La a₀) (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
      (K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
    + (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + Gtwo S M₂ * (2 * La / a₀ ^ 3))

theorem rateE_pos {Λ m₂ L ξ : ℝ} {N : ℕ} (hΛ : 0 < Λ) (hm₂ : 0 < m₂) (hL : 0 < L)
    (hN : 0 < N) (hξ : 0 < ξ) : 0 < rateE n Λ m₂ L N ξ := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  unfold rateE
  have : 0 < Real.sqrt (L / (N * ξ ^ n)) := Real.sqrt_pos.2 (by positivity)
  positivity

theorem C2_nonneg {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {M₄ a₀ La : ℝ} (hM₄ : 0 ≤ M₄) (ha₀ : 0 < a₀) (hLa : 0 ≤ La) (S : E ≃L[ℝ] E) :
    0 ≤ Ctwo M₄ μ₄ m₂ K₀ a₀ La S := by
  have hK := hk.kern.mass_pos
  have hμ₄ : 0 ≤ μ₄ := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  unfold Ctwo; positivity

set_option maxHeartbeats 800000 in
/-- **The window statement without a free grid width.**  Hypotheses of `flat_npoint_window_M2`
without `w`, `h4`, `hwc`, `hwE`; the grid width is `w* = wStar η₀ c BI Er Ls` with
`c = K₀|det S|ξⁿ/a₁ⁿ`, `BI = BIc …`, `Er = rateE …`, `Ls = Lsum …`. -/
theorem flat_npoint_window_auto {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ M₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂)
    (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * L ≤ N * ξ ^ n)
    {p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    let w := wStar η₀ (K₀ * dS S / a₁ ^ n * ξ ^ n) (BIc Lh R La a₀)
      (rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ)
      (Lsum m₂ ξ A Lh R La a₀ M₁ K₀ a₁ M₄ μ₄ M₂ S)
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
            + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa))}
      ≤ ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) * (N * (2 * Real.exp (-L)))
        + ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
  intro w
  have hN0 : 0 < N := by omega
  have hd := dS_pos S
  have hK := hk.kern.mass_pos
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < K₀ * dS S / a₁ ^ n * ξ ^ n := by positivity
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hM20 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hA0 : 0 ≤ A := le_trans (hP.nonneg 0) (hP.le 0)
  have hBI0 : 0 ≤ BIc Lh R La a₀ := by unfold BIc; positivity
  have hG0 : 0 ≤ M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)) := by positivity
  have hΛ : 0 < rLam A K₀ Lh R La a₀ a₁ M₁ S :=
    lt_of_lt_of_le one_pos (rLam_bounds A K₀ Lh R La a₀ a₁ M₁ S).1
  have hEr := rateE_pos (n := n) hΛ hm₂ (by linarith : (0:ℝ) < L) hN0 hξ (m₂ := m₂)
  have hLs : 0 ≤ Lsum m₂ ξ A Lh R La a₀ M₁ K₀ a₁ M₄ μ₄ M₂ S := by
    unfold Lsum
    have := LNlip_nonneg (ξ := ξ) hm₂ hA0 hBI0 hG0 (by positivity : 0 < K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
    have := C2_nonneg hk hm₂ hM₄ ha₀ hLa0 S
    have := Gtwo_nonneg S hM20
    positivity
  obtain ⟨hw, h4, hwc, hwE⟩ := wStar_props hη₀ hc hBI0 hEr hLs
  exact flat_npoint_window_M2 X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper hM₁ hM₂
    S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh hL1 hNL hw hη₀ h4 hwc hwE

/-- The explicit constant of the `1/N²` form. -/
def Dwin (η₀ c BI Ls m₂ p q : ℝ) : ℝ :=
  1 + max (q - p) 0 * (4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) * m₂ / (7320000 * η₀))

theorem rateE_lower {Λ m₂ L ξ : ℝ} {N : ℕ} (hΛ : 1 ≤ Λ) (hm₂ : 0 < m₂) (hL : 1 ≤ L)
    (hN : 0 < N) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    1 / rateE n Λ m₂ L N ξ ≤ m₂ * Real.sqrt N / 7320000 := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < ξ ^ n := pow_pos hξ n
  have hx1 : ξ ^ n ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN'
  have hs1 : 1 / Real.sqrt N ≤ Real.sqrt (L / (N * ξ ^ n)) := by
    rw [← Real.sqrt_one, ← Real.sqrt_div' 1 hN'.le]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hN' (by positivity)]
    nlinarith
  have hΛ20 : 1 ≤ Λ ^ 20 := one_le_pow₀ hΛ
  have hlow : 7320000 / (m₂ * Real.sqrt N) ≤ rateE n Λ m₂ L N ξ := by
    unfold rateE
    have hξi : 1 ≤ 1 / ξ := by rw [le_div_iff₀ hξ]; linarith
    calc 7320000 / (m₂ * Real.sqrt N) = 7320000 * 1 / m₂ * (1 / Real.sqrt N) / 1 := by
          field_simp
      _ ≤ 7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n)) / ξ := by
          rw [div_eq_mul_one_div (7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n))) ξ,
            div_one]
          have h1 : 7320000 * 1 / m₂ ≤ 7320000 * Λ ^ 20 / m₂ := by
            apply div_le_div_of_nonneg_right _ hm₂.le; linarith
          have h2 : 7320000 * 1 / m₂ * (1 / Real.sqrt N)
              ≤ 7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n)) :=
            mul_le_mul h1 hs1 (by positivity) (by positivity)
          have h3 : 0 ≤ 7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n)) := by positivity
          nlinarith
  have hpos : 0 < 7320000 / (m₂ * Real.sqrt N) := by positivity
  calc 1 / rateE n Λ m₂ L N ξ ≤ 1 / (7320000 / (m₂ * Real.sqrt N)) :=
        one_div_le_one_div_of_le hpos hlow
    _ = m₂ * Real.sqrt N / 7320000 := by rw [one_div_div]

set_option maxHeartbeats 1600000 in
/-- **The window statement with probability `≤ 32 D²/N²`** (`L = 4 log N`, grid width `w*`).
`D = Dwin η₀ c BI Ls m₂ p q` does not depend on `N`. -/
theorem flat_npoint_window_N2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ M₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂)
    (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * (4 * Real.log N) ≤ N * ξ ^ n)
    {p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ (4 * Real.log N) N ξ
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ (4 * Real.log N) N ξ
            + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa))}
      ≤ 32 * Dwin η₀ (K₀ * dS S / a₁ ^ n * ξ ^ n) (BIc Lh R La a₀)
          (Lsum m₂ ξ A Lh R La a₀ M₁ K₀ a₁ M₄ μ₄ M₂ S) m₂ p q ^ 2 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlog2 := Real.log_two_gt_d9
  have hL1 : 1 ≤ 4 * Real.log N := by linarith
  have H := flat_npoint_window_auto X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper
    hM₁ hM₂ S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh hL1 hNL (p := p) (q := q) hη₀
  simp only at H
  -- constants
  have hd := dS_pos S
  have hK := hk.kern.mass_pos
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < K₀ * dS S / a₁ ^ n * ξ ^ n := by positivity
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hM20 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hA0 : 0 ≤ A := le_trans (hP.nonneg 0) (hP.le 0)
  have hBI0 : 0 ≤ BIc Lh R La a₀ := by unfold BIc; positivity
  have hG0 : 0 ≤ M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)) := by positivity
  have hΛ1 := (rLam_bounds A K₀ Lh R La a₀ a₁ M₁ S).1
  have hΛ : 0 < rLam A K₀ Lh R La a₀ a₁ M₁ S := lt_of_lt_of_le one_pos hΛ1
  set Er := rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ (4 * Real.log N) N ξ with hErd
  have hEr : 0 < Er := rateE_pos hΛ hm₂ (by linarith) hN0 hξ
  set Ls := Lsum m₂ ξ A Lh R La a₀ M₁ K₀ a₁ M₄ μ₄ M₂ S with hLsd
  have hLs : 0 ≤ Ls := by
    rw [hLsd]; unfold Lsum
    have := LNlip_nonneg (ξ := ξ) hm₂ hA0 hBI0 hG0 (by positivity : 0 < K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
    have := C2_nonneg hk hm₂ hM₄ ha₀ hLa0 S
    have := Gtwo_nonneg S hM20
    positivity
  set c := K₀ * dS S / a₁ ^ n * ξ ^ n with hcd
  set BI := BIc Lh R La a₀ with hBId
  set w := wStar η₀ c BI Er Ls with hwd
  have hw := (wStar_props hη₀ hc hBI0 hEr hLs).1
  set K1 : ℝ := ((⌊(q - p) / w⌋₊ : ℕ) : ℝ) + 1 with hK1
  set mx := max (q - p) 0 with hmx
  have hmx0 : 0 ≤ mx := le_max_right _ _
  set D := Dwin η₀ c BI Ls m₂ p q with hDd
  have hsN : 1 ≤ Real.sqrt N := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hK1D : K1 ≤ D * Real.sqrt N := by
    have h1 := floor_succ_le (x := q - p) hw
    have h2 := one_div_wStar_le hη₀ hc hBI0 hEr hLs
    have h3 := rateE_lower (n := n) hΛ1 hm₂ hL1 hN0 hξ hξ1 (m₂ := m₂)
    rw [← hErd] at h3
    have h4 : 4 * (Ls + 1) / (Er * η₀) ≤ 4 * (Ls + 1) * m₂ / (7320000 * η₀) * Real.sqrt N := by
      have e1 : 4 * (Ls + 1) / (Er * η₀) = 4 * (Ls + 1) / η₀ * (1 / Er) := by field_simp
      have e2 : 4 * (Ls + 1) * m₂ / (7320000 * η₀) * Real.sqrt N
          = 4 * (Ls + 1) / η₀ * (m₂ * Real.sqrt N / 7320000) := by field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have ha0 : 0 ≤ 4 / η₀ := by positivity
    have hb0 : 0 ≤ 4 * (BI + 1) / c := by positivity
    have hc0 : 0 ≤ 4 * (Ls + 1) * m₂ / (7320000 * η₀) := by positivity
    have h5 : 1 / w ≤ (4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) * m₂ / (7320000 * η₀))
        * Real.sqrt N := by
      have := h2.trans (add_le_add_right h4 _)
      nlinarith
    have h6 : mx * (1 / w) ≤ mx * ((4 / η₀ + 4 * (BI + 1) / c
        + 4 * (Ls + 1) * m₂ / (7320000 * η₀)) * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left h5 hmx0
    rw [hDd]; unfold Dwin
    have h7 : 0 ≤ mx * (4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) * m₂ / (7320000 * η₀)) := by
      positivity
    rw [← hmx]
    nlinarith
  have hK10 : 1 ≤ K1 := by
    rw [hK1]; have := Nat.cast_nonneg (α := ℝ) ⌊(q - p) / w⌋₊; linarith
  -- the exponential
  have hexp : (N : ℝ) * (2 * Real.exp (-(4 * Real.log N))) = 2 / (N : ℝ) ^ 3 := by
    rw [Real.exp_neg, show (4:ℝ) * Real.log N = ((4:ℕ):ℝ) * Real.log N by norm_num,
      Real.exp_nat_mul, Real.exp_log hN']
    field_simp
  rw [hexp] at H
  refine H.trans ?_
  have hK1sq : K1 ^ 2 ≤ D ^ 2 * N := by
    have hD0 : 0 ≤ D * Real.sqrt N := le_trans (by linarith) hK1D
    calc K1 ^ 2 ≤ (D * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (by linarith) hK1D 2
      _ = D ^ 2 * N := by rw [mul_pow, Real.sq_sqrt hN'.le]
  have hX0 : 0 ≤ 2 / (N : ℝ) ^ 3 := by positivity
  calc K1 * (2 / (N : ℝ) ^ 3) + K1 ^ 2 * (15 * (2 / (N : ℝ) ^ 3))
      ≤ 16 * K1 ^ 2 * (2 / (N : ℝ) ^ 3) := by
        have hk : K1 ≤ K1 ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right hk hX0
        nlinarith
    _ ≤ 16 * (D ^ 2 * N) * (2 / (N : ℝ) ^ 3) := by gcongr
    _ = 32 * D ^ 2 / (N : ℝ) ^ 2 := by field_simp; ring

/-! ### (3) Measurability of the exceptional set -/

/-- A set `{ω | ∃ t ∈ D, 0 < F t ω}` is measurable if `F t` is measurable for `t ∈ D` and `F · ω` is
continuous on `D` for every `ω` (countable dense subset of `D`). -/
theorem exists_param_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {D : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Ω → ℝ} (hm : ∀ t ∈ D, Measurable (F t))
    (hc : ∀ ω, ContinuousOn (fun t => F t ω) D) :
    MeasurableSet {ω | ∃ t ∈ D, 0 < F t ω} := by
  obtain ⟨C, hCc, hCd⟩ := TopologicalSpace.exists_countable_dense ↥D
  have e : {ω | ∃ t ∈ D, 0 < F t ω} = ⋃ t ∈ C, {ω | 0 < F (t : ℝ × ℝ) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨t, htD, hpos⟩
      have hcont : Continuous (D.restrict fun t => F t ω) :=
        continuousOn_iff_continuous_restrict.1 (hc ω)
      have hop : IsOpen {u : ↥D | 0 < D.restrict (fun t => F t ω) u} :=
        isOpen_lt continuous_const hcont
      obtain ⟨u, hu, huC⟩ := hCd.inter_open_nonempty _ hop ⟨⟨t, htD⟩, hpos⟩
      exact ⟨u, huC, hu⟩
    · rintro ⟨u, huC, hu⟩
      exact ⟨u, u.2, hu⟩
  rw [e]
  exact MeasurableSet.biUnion hCc fun t _ => measurableSet_lt measurable_const (hm t t.2)

theorem fr_zero : fr (0 : E) = 0 :=
  fr_of_mem 0 fun i => by simp only [PiLp.zero_apply, zero_add]; constructor <;> norm_num

/-- The self-term of the periodised kernel is `h 0`. -/
theorem perK_kap_self (h : ℝ → ℝ) (S : E ≃L[ℝ] E) (r : ℝ) (x : E) :
    perK (kap h S r) x x = h 0 := by
  unfold perK kap; rw [sub_self, fr_zero]; simp

theorem sampAvg_pos {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} {h : ℝ → ℝ} {A R : ℝ}
    (hP : Prof h A R) (h0 : 0 < h 0) (S : E ≃L[ℝ] E) (r : ℝ) (ω : Ω) {j : ℕ} (hj : j < N) :
    0 < sampAvg X N (perK (kap h S r)) j ω := by
  have hN' : (0:ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le j) hj)
  unfold sampAvg
  have hs : perK (kap h S r) (X j ω) (X j ω)
      ≤ ∑ k ∈ Finset.range N, perK (kap h S r) (X j ω) (X k ω) :=
    Finset.single_le_sum (f := fun k => perK (kap h S r) (X j ω) (X k ω))
      (fun k _ => hP.nonneg _) (Finset.mem_range.2 hj)
  rw [perK_kap_self] at hs
  exact mul_pos (by positivity) (lt_of_lt_of_le h0 hs)

theorem den_pos {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} {h : ℝ → ℝ} {A R : ℝ}
    (hP : Prof h A R) (h0 : 0 < h 0) (S : E ≃L[ℝ] E) (r : ℝ) (ω : Ω) {i : ℕ} (hi : i < N) :
    0 < sampW X N (perK (kap h S r)) (fun _ _ => 1) i ω := by
  have hN' : (0:ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i) hi)
  unfold sampW avgN
  have hterm : ∀ k ∈ Finset.range N, 0 ≤ perK (kap h S r) (X i ω) (X k ω) * 1
      * (1 / sampAvg X N (perK (kap h S r)) k ω) := fun k hk =>
    mul_nonneg (mul_nonneg (hP.nonneg _) zero_le_one)
      (one_div_pos.2 (sampAvg_pos X hP h0 S r ω (Finset.mem_range.1 hk))).le
  have hs := Finset.single_le_sum hterm (Finset.mem_range.2 hi)
  have hi0 : 0 < perK (kap h S r) (X i ω) (X i ω) * 1
      * (1 / sampAvg X N (perK (kap h S r)) i ω) := by
    rw [perK_kap_self, mul_one]; exact mul_pos h0 (one_div_pos.2 (sampAvg_pos X hP h0 S r ω hi))
  exact mul_pos (by positivity) (lt_of_lt_of_le hi0 hs)

theorem cont_of_lip {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s t, |F t - F s| ≤ C * |t - s|) : Continuous F :=
  (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hF y x).continuous

/-- `τ ↦ L_N(τ) f(i)` is continuous for every sample (HYPOTHESIS `0 < h 0`). -/
theorem LN_cont {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N)
    {h : ℝ → ℝ} {A R Lh : ℝ} (hP : Prof h A R) (hR : 0 ≤ R)
    (hL : LipProf h Lh) (hLh : 0 ≤ Lh) (h0 : 0 < h 0) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (f : E → ℝ) {i : ℕ} (hi : i < N) (ω : Ω) :
    Continuous fun τ => LN X N h m₂ S (a τ) ξ f i ω := by
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hBI : 0 ≤ BIc Lh R La a₀ := by unfold BIc; positivity
  have hK : ∀ x z : E, Continuous fun τ => perK (kap h S (ξ / a τ)) x z := fun x z =>
    cont_of_lip hBI fun s t => perK_time_lip hP hR hL hLh S a a' hda ha₀ ha hLa hξ s t x z
  have hA : ∀ j, Continuous fun τ => sampAvg X N (perK (kap h S (ξ / a τ))) j ω := fun j =>
    cont_of_lip hBI fun s t => sampAvg_close X hN
      (fun x z => perK_time_lip hP hR hL hLh S a a' hda ha₀ ha hLa hξ s t x z) j ω
  have hW : ∀ g : E → E → ℝ,
      Continuous fun τ => sampW X N (perK (kap h S (ξ / a τ))) g i ω := by
    intro g
    unfold sampW avgN
    refine continuous_const.mul (continuous_finset_sum _ fun j hj => ?_)
    exact ((hK _ _).mul continuous_const).mul (continuous_const.div (hA j)
      fun τ => (sampAvg_pos X hP h0 S _ ω (Finset.mem_range.1 hj)).ne')
  unfold LN
  exact continuous_const.mul ((hW _).div (hW _) fun τ => (den_pos X hP h0 S _ ω hi).ne')

/-- `τ ↦ L^τ_ξ f(x)` is continuous. -/
theorem Lmet_cont {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : E) :
    Continuous fun τ => Lmet h m₂ S (a τ) ξ f x := by
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hC := C2_nonneg hk hm₂ hM₄ ha₀ hLa0 S
  exact cont_of_lip (C := ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + |lapG S f x| * (2 * La / a₀ ^ 3))
    (by positivity) fun s t => Lmet_lip hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ x le_rfl s t

/-- The domain of pairs of times. -/
def Dpair (p q η₀ : ℝ) : Set (ℝ × ℝ) := {t | t.1 ∈ Icc p q ∧ t.2 ∈ Icc p q ∧ η₀ ≤ |t.2 - t.1|}

set_option maxHeartbeats 800000 in
/-- **Measurability of the exceptional set of `flat_npoint_window`** (for arbitrary constants
`Er`, `C₁`, `C₂`; with `Er = rateE …`, `C₁ = Cone …`, `C₂ = Ctwo …` it is literally the set of
`flat_npoint_window`).  HYPOTHESIS beyond the setting: `0 < h 0`. -/
theorem window_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : ℕ → Ω → E) (hX : ∀ j, Measurable (X j)) {N : ℕ} (hN : 0 < N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh) (h0 : 0 < h 0)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ)
    {p q η₀ Er C₁ C₂ : ℝ} (hη₀ : 0 < η₀) :
    MeasurableSet {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω| ≤ 2 * Er
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω| ≤ 2 * Er + 2 * popErr ξ C₁ C₂ (τb - τa))} := by
  have hne : ∀ t ∈ Dpair p q η₀, t.2 - t.1 ≠ 0 := fun t ht hz => by
    have h1 : η₀ ≤ |t.2 - t.1| := ht.2.2
    rw [hz, abs_zero] at h1; linarith
  have hac : Continuous a := continuous_iff_continuousAt.2 fun τ => (hda τ).continuousAt
  have hFI : ∀ i < N, ∀ ω, Continuous (FI X N h m₂ S a ξ f i ω) := fun i hi ω => by
    unfold FI
    exact (LN_cont X hN hP hR hLP hLh h0 m₂ S a a' hda ha₀ ha hLa hξ f hi ω).sub
      (Lmet_cont hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ _)
  have hFII : ∀ i < N, ∀ ω, Continuous (FII X N h m₂ S a ξ f i ω) := fun i hi ω => by
    unfold FII
    exact (LN_cont X hN hP hR hLP hLh h0 m₂ S a a' hda ha₀ ha hLa hξ f hi ω).add
      (continuous_const.div (hac.pow 2)
        fun τ => pow_ne_zero 2 (lt_of_lt_of_le ha₀ (ha τ)).ne')
  have hdiff : ContinuousOn (fun t : ℝ × ℝ => t.2 - t.1) (Dpair p q η₀) :=
    (continuous_snd.sub continuous_fst).continuousOn
  have e : {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω| ≤ 2 * Er
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω| ≤ 2 * Er + 2 * popErr ξ C₁ C₂ (τb - τa))}
      = ⋃ i, ⋃ (_ : i < N),
        ({ω | ∃ t ∈ Dpair p q η₀, 0 < |dqI X N h m₂ S a ξ f t.1 t.2 i ω| - 2 * Er}
        ∪ {ω | ∃ t ∈ Dpair p q η₀, 0 < |dqII X N h m₂ S a ξ f t.1 t.2 i ω|
            - (2 * Er + 2 * popErr ξ C₁ C₂ (t.2 - t.1))}) := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, mem_union, sub_pos]
    constructor
    · rintro ⟨τa, ha', τb, hb', hη, i, hi, hn⟩
      refine ⟨i, hi, ?_⟩
      rcases not_and_or.1 hn with h1 | h2
      · exact Or.inl ⟨(τa, τb), ⟨ha', hb', hη⟩, not_le.1 h1⟩
      · exact Or.inr ⟨(τa, τb), ⟨ha', hb', hη⟩, not_le.1 h2⟩
    · rintro ⟨i, hi, ⟨t, ⟨ha', hb', hη⟩, h1⟩ | ⟨t, ⟨ha', hb', hη⟩, h2⟩⟩
      · exact ⟨t.1, ha', t.2, hb', hη, i, hi, fun hc => absurd hc.1 (not_le.2 h1)⟩
      · exact ⟨t.1, ha', t.2, hb', hη, i, hi, fun hc => absurd hc.2 (not_le.2 h2)⟩
  rw [e]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi => MeasurableSet.union ?_ ?_
  · refine exists_param_measurable
      (F := fun t ω => |dqI X N h m₂ S a ξ f t.1 t.2 i ω| - 2 * Er) ?_ ?_
    · intro t _
      unfold dqI
      exact ((((LN_measurable X hX N hP.meas m₂ S _ ξ hf.continuous i).sub
        (LN_measurable X hX N hP.meas m₂ S _ ξ hf.continuous i)).div_const _).sub
        ((((Lmet_measurable hP.meas m₂ S _ ξ hf.continuous).comp (hX i)).sub
          ((Lmet_measurable hP.meas m₂ S _ ξ hf.continuous).comp (hX i))).div_const _)).abs.sub_const _
    · intro ω
      have ee : (fun t : ℝ × ℝ => |dqI X N h m₂ S a ξ f t.1 t.2 i ω| - 2 * Er)
          = fun t => |(FI X N h m₂ S a ξ f i ω t.2 - FI X N h m₂ S a ξ f i ω t.1)
              / (t.2 - t.1)| - 2 * Er := by
        funext t; rw [dqI_eq]
      rw [ee]
      exact ((((hFI i hi ω).comp continuous_snd).sub
        ((hFI i hi ω).comp continuous_fst)).continuousOn.div hdiff hne).abs.sub continuousOn_const
  · refine exists_param_measurable
      (F := fun t ω => |dqII X N h m₂ S a ξ f t.1 t.2 i ω|
        - (2 * Er + 2 * popErr ξ C₁ C₂ (t.2 - t.1))) ?_ ?_
    · intro t _
      unfold dqII
      have hL1 := ((LN_measurable X hX N hP.meas m₂ S (a t.2) ξ hf.continuous i).sub
        (LN_measurable X hX N hP.meas m₂ S (a t.1) ξ hf.continuous i)).div_const (t.2 - t.1)
      have hG := (lapG_measurable S hf).comp (hX i)
      have hL2 := ((hG.div_const (a t.2 ^ 2)).sub (hG.div_const (a t.1 ^ 2))).div_const (t.2 - t.1)
      exact (hL1.add hL2).abs.sub_const _
    · intro ω
      have ee : (fun t : ℝ × ℝ => |dqII X N h m₂ S a ξ f t.1 t.2 i ω|
            - (2 * Er + 2 * popErr ξ C₁ C₂ (t.2 - t.1)))
          = fun t => |(FII X N h m₂ S a ξ f i ω t.2 - FII X N h m₂ S a ξ f i ω t.1)
              / (t.2 - t.1)| - (2 * Er + 2 * (ξ ^ 2 * min (C₁ / |t.2 - t.1|) C₂)) := by
        funext t; rw [dqII_eq]; rfl
      rw [ee]
      refine ((((hFII i hi ω).comp continuous_snd).sub
        ((hFII i hi ω).comp continuous_fst)).continuousOn.div hdiff hne).abs.sub
        (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.mul
          (ContinuousOn.inf (continuousOn_const.div hdiff.abs
            fun t ht => abs_ne_zero.2 (hne t ht)) continuousOn_const))))

set_option maxHeartbeats 800000 in
/-- **The exceptional set of `flat_npoint_window`, literally, is measurable** (HYPOTHESIS `0 < h 0`). -/
theorem flat_npoint_window_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : ℕ → Ω → E) (hX : ∀ j, Measurable (X j)) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh) (h0 : 0 < h 0)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ)
    {L p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    MeasurableSet {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
            + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa))} :=
  window_set_measurable X hX (by omega) hk hm₂ hP hR hLP hLh h0 hf hM hM₄ S a a' hda ha₀ ha hLa
    hξ hη₀

end CTG.FlatNPointWindow2
