/-
Thirty-eighth file: the flat N-point statement for the Gaussian profile CUT OFF at a radius `R`.  Imports
`CorrelationsToGeometryFlatNPointFinal` (compiled module under `.tools/leanbuild`); namespace
`CTG.FlatNPointGauss`; check with `./check_flat_npoint_gauss.sh`.
Profile `gT R s = max(exp(−s²/2) − exp(−R²/2), 0)`: Lipschitz with constant 1, support `[0,R]`, differs from
`exp(−s²/2)` by at most `exp(−R²/2)`.  `radK_gT` (its moments satisfy the hypotheses of the flat files, with no
assumption), `flat_npoint_gauss_truncated`, `flat_npoint_gauss_truncated_final` (both inequalities of the flat
N-point statement for this profile; the moments `gK₀`, `gm₂`, `gμ₃`, `gμ₄` are named integrals),
`kap_gauss_sub` (pointwise distance of the kernels), `gK₀_tendsto` (`K₀(R) → (2π)^{n/2}`), `gm₂_tendsto`,
`gμ₃_tendsto`, `gμ₄_tendsto` (convergence to the Gaussian moments).
This is NOT the kernel of the paper: the profile is shifted and truncated, the periodisation is the single
nearest image, the radius condition `‖S‖ ξ R/a₀ < 1/2` couples `R` and `ξ`, and the constant `Λ` grows with `R`.
NOT formalised: the periodised Gaussian kernel as a lattice sum and its comparison with the truncated kernel
on the sample side and on the population side; that the limit of `gm₂` is 1.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatNPointFinal

open MeasureTheory ProbabilityTheory Set
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointGauss

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### (1) The cut-off Gaussian profile -/

/-- The Gaussian profile `exp(−s²/2)` of the paper. -/
def gauss (s : ℝ) : ℝ := Real.exp (-(s ^ 2) / 2)

/-- The Gaussian profile cut off at `R`: `max (exp(−s²/2) − exp(−R²/2)) 0`. -/
def gT (R s : ℝ) : ℝ := max (gauss s - gauss R) 0

theorem gauss_pos (s : ℝ) : 0 < gauss s := Real.exp_pos _

theorem gauss_le_one (s : ℝ) : gauss s ≤ 1 := by
  unfold gauss; rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg s]

theorem gauss_continuous : Continuous gauss := by
  unfold gauss; fun_prop

theorem gT_continuous (R : ℝ) : Continuous (gT R) := by
  unfold gT; exact (gauss_continuous.sub continuous_const).max continuous_const

theorem gT_nonneg (R s : ℝ) : 0 ≤ gT R s := le_max_right _ _

theorem gT_le_one (R s : ℝ) : gT R s ≤ 1 := by
  unfold gT
  exact max_le (by linarith [gauss_le_one s, gauss_pos R]) zero_le_one

theorem gauss_anti {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : gauss t ≤ gauss s := by
  unfold gauss; apply Real.exp_le_exp.2; nlinarith

theorem gauss_strictAnti {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) : gauss t < gauss s := by
  unfold gauss; apply Real.exp_lt_exp.2; nlinarith

theorem gT_supp {R : ℝ} (hR : 0 ≤ R) (s : ℝ) (hs : R ≤ s) : gT R s = 0 := by
  unfold gT; exact max_eq_right (by linarith [gauss_anti hR hs])

theorem gT_pos {R s : ℝ} (hs : 0 ≤ s) (hsR : s < R) : 0 < gT R s := by
  unfold gT; exact lt_max_of_lt_left (by linarith [gauss_strictAnti hs hsR])

/-- The cut-off changes the profile by at most `exp(−R²/2)`. -/
theorem gT_sub_gauss {R : ℝ} (s : ℝ) : |gauss s - gT R s| ≤ gauss R := by
  unfold gT
  rcases le_total (gauss s - gauss R) 0 with h | h
  · rw [max_eq_right h, sub_zero, abs_of_nonneg (gauss_pos s).le]; linarith
  · rw [max_eq_left h]; rw [show gauss s - (gauss s - gauss R) = gauss R by ring,
      abs_of_nonneg (gauss_pos R).le]

theorem gauss_hasDerivAt (s : ℝ) : HasDerivAt gauss (-s * gauss s) s := by
  unfold gauss
  have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2) / 2) (-s) s := by
    have := ((hasDerivAt_pow 2 s).neg).div_const 2
    convert this using 1; push_cast; ring
  convert h1.exp using 1; ring

theorem abs_mul_gauss_le (s : ℝ) : |-s * gauss s| ≤ 1 := by
  rw [abs_mul, abs_neg, abs_of_nonneg (gauss_pos s).le]
  have h1 : |s| ≤ Real.exp (s ^ 2 / 2) := by
    have := Real.add_one_le_exp (s ^ 2 / 2)
    have h2 : |s| ^ 2 = s ^ 2 := sq_abs s
    nlinarith [sq_nonneg (|s| - 1), abs_nonneg s]
  have e : gauss s * Real.exp (s ^ 2 / 2) = 1 := by
    unfold gauss; rw [← Real.exp_add]; simp [show -(s ^ 2) / 2 + s ^ 2 / 2 = 0 by ring]
  have := gauss_pos s
  nlinarith

theorem gauss_lip (s s' : ℝ) : |gauss s - gauss s'| ≤ 1 * |s - s'| := by
  have hL : LipschitzWith 1 gauss := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (gauss_hasDerivAt x).differentiableAt)
    intro x
    rw [(gauss_hasDerivAt x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
    simpa using abs_mul_gauss_le x
  have := hL.dist_le_mul s s'
  simpa [Real.dist_eq] using this

theorem gT_lip (R : ℝ) : LipProf (gT R) 1 := fun s s' => by
  unfold gT
  calc |max (gauss s - gauss R) 0 - max (gauss s' - gauss R) 0|
      ≤ |(gauss s - gauss R) - (gauss s' - gauss R)| := abs_max_sub_max_le_abs _ _ _
    _ = |gauss s - gauss s'| := by ring_nf
    _ ≤ 1 * |s - s'| := gauss_lip s s'

theorem gT_prof {R : ℝ} (hR : 0 ≤ R) : Prof (gT R) 1 R :=
  ⟨(gT_continuous R).measurable, gT_nonneg R, gT_le_one R, gT_supp hR⟩

/-! ### (2) Integrability and symmetries of the radial kernel `gT R ‖z‖` -/

theorem kern_integrable {R : ℝ} (hR : 0 ≤ R) {g : E → ℝ} (hg : Continuous g) :
    Integrable (fun z : E => g z * gT R ‖z‖) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact hg.mul ((gT_continuous R).comp continuous_norm)
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : E) R)
    intro z hz
    have : R ≤ ‖z‖ := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz; exact hz.le
    simp [gT_supp hR _ this]

/-- Integrals are invariant under linear isometries. -/
theorem integral_isom (L : E ≃ₗᵢ[ℝ] E) (F : E → ℝ) : ∫ z, F (L z) = ∫ z, F z :=
  L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding F

/-- Reflection in the `i`-th coordinate. -/
def flipL (i : Fin n) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun j => if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

theorem flipL_apply (i j : Fin n) (z : E) : flipL i z j = if j = i then -z j else z j := by
  unfold flipL
  rw [LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> simp

/-- Swap of the coordinates `i` and `j`. -/
def swapL (i j : Fin n) : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

theorem swapL_apply (i j k : Fin n) (z : E) : swapL i j z k = z (Equiv.swap i j k) := by
  unfold swapL
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Equiv.piCongrLeft'_apply]

/-! ### (3) The moments and `RadK` -/

/-- Mass `K₀ = ∫ gT R ‖z‖ dz`. -/
def gK₀ (n : ℕ) (R : ℝ) : ℝ := ∫ z : EuclideanSpace ℝ (Fin n), gT R ‖z‖

/-- Second moment `m₂ = (∫ ‖z‖² gT R ‖z‖ dz)/(n K₀)` (per coordinate, normalised by the mass). -/
def gm₂ (n : ℕ) (R : ℝ) : ℝ :=
  (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 * gT R ‖z‖) / (n * gK₀ n R)

/-- Third absolute moment. -/
def gμ₃ (n : ℕ) (R : ℝ) : ℝ := ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 3 * gT R ‖z‖

/-- Fourth absolute moment. -/
def gμ₄ (n : ℕ) (R : ℝ) : ℝ := ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 4 * gT R ‖z‖

theorem gK₀_pos {R : ℝ} (hR : 0 < R) : 0 < gK₀ n R := by
  unfold gK₀
  have hi : Integrable (fun z : E => gT R ‖z‖) := by
    simpa using kern_integrable (n := n) hR.le (g := fun _ => (1 : ℝ)) continuous_const
  rw [integral_pos_iff_support_of_nonneg (fun z => gT_nonneg R ‖z‖) hi]
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : E) hR) (measure_mono ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  exact (gT_pos (norm_nonneg z) hz).ne'

theorem second_pos {R : ℝ} (hR : 0 < R) (hn : 1 ≤ n) :
    0 < ∫ z : E, ‖z‖ ^ 2 * gT R ‖z‖ := by
  haveI : NeZero n := ⟨by omega⟩
  have hi := kern_integrable (n := n) hR.le (g := fun z => ‖z‖ ^ 2) (by fun_prop)
  rw [integral_pos_iff_support_of_nonneg (fun z => mul_nonneg (sq_nonneg _) (gT_nonneg R ‖z‖)) hi]
  have hb : 0 < volume (Metric.ball (0 : E) R \ {0}) := by
    rw [measure_diff_null (measure_singleton 0)]
    exact Metric.measure_ball_pos volume (0 : E) hR
  refine lt_of_lt_of_le hb (measure_mono ?_)
  intro z ⟨hz, hz0⟩
  rw [Metric.mem_ball, dist_zero_right] at hz
  have h1 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  exact (mul_pos (pow_pos h1 2) (gT_pos (norm_nonneg z) hz)).ne'

theorem gm₂_pos {R : ℝ} (hR : 0 < R) (hn : 1 ≤ n) : 0 < gm₂ n R := by
  unfold gm₂
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (second_pos hR hn) (mul_pos this (gK₀_pos hR))

theorem mom1_zero {R : ℝ} (hR : 0 ≤ R) (i : Fin n) : ∫ z : E, z i * gT R ‖z‖ = 0 := by
  have h := integral_isom (flipL i) (fun z : E => z i * gT R ‖z‖)
  simp only [flipL_apply, LinearIsometryEquiv.norm_map, ↓reduceIte, neg_mul, integral_neg] at h
  linarith

theorem mom2_off {R : ℝ} (hR : 0 ≤ R) {i j : Fin n} (hij : i ≠ j) :
    ∫ z : E, z i * z j * gT R ‖z‖ = 0 := by
  have h := integral_isom (flipL i) (fun z : E => z i * z j * gT R ‖z‖)
  simp only [flipL_apply, if_neg (Ne.symm hij), LinearIsometryEquiv.norm_map, ↓reduceIte,
    neg_mul, integral_neg] at h
  linarith

theorem mom2_swap {R : ℝ} (i j : Fin n) :
    ∫ z : E, z i * z i * gT R ‖z‖ = ∫ z : E, z j * z j * gT R ‖z‖ := by
  have h := integral_isom (swapL i j) (fun z : E => z i * z i * gT R ‖z‖)
  simp only [swapL_apply, Equiv.swap_apply_left, LinearIsometryEquiv.norm_map] at h
  exact h.symm

theorem mom2_diag {R : ℝ} (hR : 0 < R) (i : Fin n) :
    ∫ z : E, z i * z i * gT R ‖z‖ = gm₂ n R * gK₀ n R := by
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this.ne'
  have hK := (gK₀_pos (n := n) hR).ne'
  have hsum : ∫ z : E, ‖z‖ ^ 2 * gT R ‖z‖ = n * ∫ z : E, z i * z i * gT R ‖z‖ := by
    have e1 : (fun z : E => ‖z‖ ^ 2 * gT R ‖z‖)
        = fun z => ∑ j, z j * z j * gT R ‖z‖ := by
      funext z
      rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, integral_finset_sum _ fun j _ =>
      kern_integrable hR.le (g := fun z : E => z j * z j) (by fun_prop)]
    rw [Finset.sum_congr rfl fun j _ => mom2_swap (R := R) j i]
    simp
  unfold gm₂
  rw [hsum]; field_simp

theorem radK_gT {R : ℝ} (hR : 0 < R) :
    RadK n (gT R) (gK₀ n R) (gm₂ n R) (gμ₃ n R) (gμ₄ n R) where
  kern :=
    { nonneg := fun z => gT_nonneg R ‖z‖
      int0 := by simpa using kern_integrable (n := n) hR.le (g := fun _ => (1 : ℝ)) continuous_const
      int1 := fun i => kern_integrable hR.le (g := fun z : E => z i) (by fun_prop)
      int2 := fun i j => kern_integrable hR.le (g := fun z : E => z i * z j) (by fun_prop)
      int3 := kern_integrable hR.le (g := fun z : E => ‖z‖ ^ 3) (by fun_prop)
      mass := rfl
      mass_pos := gK₀_pos hR
      mom1 := fun i => mom1_zero hR.le i
      mom2 := fun i j => by
        split_ifs with h
        · subst h; exact mom2_diag hR i
        · exact mom2_off hR.le h
      mom3 := rfl }
  int1 := kern_integrable hR.le (g := fun z : E => ‖z‖) (by fun_prop)
  int4 := kern_integrable hR.le (g := fun z : E => ‖z‖ ^ 4) (by fun_prop)
  mom4 := rfl

/-! ### (4) The tail of the cut-off and the choice `R = c √(log N)` -/

/-- Pointwise difference of the two kernels: `|exp(−d²/(2ξ'²)) − κ_R| ≤ exp(−R²/2)`. -/
theorem kap_gauss_sub (R : ℝ) (S : E ≃L[ℝ] E) (ξ : ℝ) (v : E) :
    |kap gauss S ξ v - kap (gT R) S ξ v| ≤ gauss R := by
  unfold kap; exact gT_sub_gauss _

/-- With `R = c √(log N)` the cut-off error is `N^{-c²/2}`. -/
theorem gauss_sqrt_log {N : ℕ} (hN : 1 ≤ N) (c : ℝ) :
    gauss (c * Real.sqrt (Real.log N)) = (N : ℝ) ^ (-(c ^ 2) / 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  unfold gauss
  rw [Real.rpow_def_of_pos hN0, mul_pow, Real.sq_sqrt hl]
  congr 1; ring

/-! ### (5) The N-point theorem for the cut-off Gaussian kernel -/

set_option maxHeartbeats 1600000 in
/-- **`prop:dotLN-diff`, flat periodic case, rate form, for the Gaussian profile cut off at `R`.**
Kernel `perK (kap (gT R) S (ξ/a(τ)))`, i.e. `max(exp(−‖S⁻¹ fr(z−x)‖² a²/(2ξ²)) − exp(−R²/2), 0)`;
`A = 1`, `Lh = 1`, moments `gK₀`, `gm₂`, `gμ₃`, `gμ₄` (named integrals).  HYPOTHESES as in
`flat_npoint_rate` (with `R > 0`, `n ≥ 1`); probability `≥ 1 − 30/N²`. -/
theorem flat_npoint_gauss_truncated (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LN X N (gT R) (gm₂ n R) S (a τb) ξ f i ω - LN X N (gT R) (gm₂ n R) S (a τa) ξ f i ω)
            / (τb - τa)
          - (Lmet (gT R) (gm₂ n R) S (a τb) ξ f (X i ω)
              - Lmet (gT R) (gm₂ n R) S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LN X N (gT R) (gm₂ n R) S (a τb) ξ f i ω - LN X N (gT R) (gm₂ n R) S (a τa) ξ f i ω)
            / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * gm₂ n R * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * gm₂ n R * gK₀ n R * a₀ ^ 5)))}
      ≤ 30 / (N : ℝ) ^ 2 :=
  flat_npoint_rate X h_indep hX hlaw N hN (radK_gT hR) (gm₂_pos hR hn) (gT_prof hR.le) hR.le
    (gT_lip R) zero_le_one hf hM hM₄ hper hLip0 hLip S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh
    τa τb hne hNL

/-- The same with the Lipschitz constant of `f` from a derivative bound `M₁`
(`flat_npoint_final`); exceptional set `badRate`. -/
theorem flat_npoint_gauss_truncated_final (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ M₁ S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real (badRate X N (gT R) (gm₂ n R) S a ξ f τa τb (rLam 1 (gK₀ n R) 1 R La a₀ a₁ M₁ S) M₄
        (gμ₄ n R) (gK₀ n R) a₀ La)
      ≤ 30 / (N : ℝ) ^ 2 :=
  flat_npoint_final X h_indep hX hlaw N hN (radK_gT hR) (gm₂_pos hR hn) (gT_prof hR.le) hR.le
    (gT_lip R) zero_le_one hf hM hM₄ hper hM₁ S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh τa τb hne hNL


/-! ### (6) The moments converge to the Gaussian moments as `R → ∞` -/

theorem gT_le_gauss (R s : ℝ) : gT R s ≤ gauss s := by
  unfold gT; exact max_le (by linarith [gauss_pos R]) (gauss_pos s).le

theorem expB_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : E => Real.exp (-b * ‖z‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := (b : ℂ))
    (by simpa using hb) 0 0).norm
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  rw [show (-(b : ℂ) * (‖z‖ : ℂ) ^ 2) = ((-b * ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.ofReal_re]

theorem gauss_integral : ∫ z : E, gauss ‖z‖ = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
  have e : (fun z : E => gauss ‖z‖) = fun z => Real.exp (-(1 / 2 : ℝ) * ‖z‖ ^ 2) := by
    funext z; unfold gauss; congr 1; ring
  rw [e, GaussianFourier.integral_rexp_neg_mul_sq_norm (by norm_num : (0 : ℝ) < 1 / 2), finrank_euclideanSpace_fin]
  congr 1; ring

/-- `‖z‖^{2j} exp(−‖z‖²/2) ≤ 4^j j! exp(−‖z‖²/4)`. -/
theorem even_moment_le (j : ℕ) (z : E) :
    ‖z‖ ^ (2 * j) * gauss ‖z‖ ≤ 4 ^ j * j.factorial * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) := by
  set x := ‖z‖ ^ 2 / 4 with hx
  have hx0 : 0 ≤ x := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx0 j
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h2 : x ^ j ≤ j.factorial * Real.exp x := by
    rw [div_le_iff₀ hf] at h1; linarith
  have e1 : ‖z‖ ^ (2 * j) = 4 ^ j * x ^ j := by
    rw [hx, div_pow, pow_mul]; field_simp
  have e2 : gauss ‖z‖ = Real.exp x * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) * Real.exp (-x) * Real.exp (-x) := by
    unfold gauss; rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hx]; ring
  have e3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [e1, e2]
  have hE := Real.exp_pos (-(1 / 4 : ℝ) * ‖z‖ ^ 2)
  have hm := Real.exp_pos (-x)
  have h4 : (0 : ℝ) < 4 ^ j := by positivity
  calc 4 ^ j * x ^ j * (Real.exp x * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) * Real.exp (-x) * Real.exp (-x))
      = 4 ^ j * x ^ j * Real.exp (-x) * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) := by
        rw [show Real.exp x * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) * Real.exp (-x) * Real.exp (-x)
          = (Real.exp x * Real.exp (-x)) * Real.exp (-x) * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) by ring,
          e3]; ring
    _ ≤ 4 ^ j * (j.factorial * Real.exp x) * Real.exp (-x) * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) := by
        gcongr
    _ = 4 ^ j * j.factorial * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) := by
        rw [show 4 ^ j * (j.factorial * Real.exp x) * Real.exp (-x) * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2)
          = 4 ^ j * j.factorial * (Real.exp x * Real.exp (-x)) * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) by ring,
          e3, mul_one]

theorem even_moment_integrable (j : ℕ) :
    Integrable (fun z : E => ‖z‖ ^ (2 * j) * gauss ‖z‖) := by
  refine ((expB_integrable (n := n) (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    (4 ^ j * j.factorial)).mono'
    (((continuous_norm.pow _).mul (gauss_continuous.comp continuous_norm)).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (gauss_pos _).le)]
  exact even_moment_le j z

theorem gauss_tendsto_zero : Filter.Tendsto gauss Filter.atTop (nhds 0) := by
  unfold gauss
  apply Real.tendsto_exp_atBot.comp
  have : Filter.Tendsto (fun R : ℝ => R ^ 2 / 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num)).atTop_div_const (by norm_num)
  have := Filter.tendsto_neg_atTop_atBot.comp this
  refine this.congr fun R => ?_
  simp [Function.comp, neg_div]

/-- Dominated convergence for the moments of the cut-off profile. -/
theorem tendsto_moment {g : E → ℝ} (hg : Continuous g)
    (hgi : Integrable (fun z => g z * gauss ‖z‖)) :
    Filter.Tendsto (fun R => ∫ z, g z * gT R ‖z‖) Filter.atTop
      (nhds (∫ z, g z * gauss ‖z‖)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖g z * gauss ‖z‖‖)
  · exact Filter.Eventually.of_forall fun R =>
      (hg.mul ((gT_continuous R).comp continuous_norm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun R => ae_of_all _ fun z => ?_
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (gT_nonneg R _),
      Real.norm_of_nonneg (gauss_pos _).le]
    exact mul_le_mul_of_nonneg_left (gT_le_gauss R _) (norm_nonneg _)
  · exact hgi.norm
  · refine ae_of_all _ fun z => ?_
    apply Filter.Tendsto.const_mul
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun R => norm_nonneg _) (fun R => ?_) gauss_tendsto_zero
    rw [Real.norm_eq_abs, abs_sub_comm]; exact gT_sub_gauss _

/-- `K₀(R) ≤ (2π)^{n/2}` and `K₀(R) → (2π)^{n/2}`. -/
theorem gK₀_le (R : ℝ) (hR : 0 ≤ R) : gK₀ n R ≤ (2 * Real.pi) ^ ((n : ℝ) / 2) := by
  rw [← gauss_integral]; unfold gK₀
  refine integral_mono ?_ ?_ fun z => gT_le_gauss R _
  · simpa using kern_integrable (n := n) hR (g := fun _ => (1 : ℝ)) continuous_const
  · simpa using even_moment_integrable (n := n) 0

theorem gK₀_tendsto :
    Filter.Tendsto (fun R => gK₀ n R) Filter.atTop (nhds ((2 * Real.pi) ^ ((n : ℝ) / 2))) := by
  rw [← gauss_integral]
  have := tendsto_moment (n := n) (g := fun _ => (1 : ℝ)) continuous_const
    (by simpa using even_moment_integrable (n := n) 0)
  simpa [gK₀] using this

theorem second_tendsto :
    Filter.Tendsto (fun R => ∫ z : E, ‖z‖ ^ 2 * gT R ‖z‖) Filter.atTop
      (nhds (∫ z : E, ‖z‖ ^ 2 * gauss ‖z‖)) :=
  tendsto_moment (g := fun z : E => ‖z‖ ^ 2) (by fun_prop)
    (by simpa using even_moment_integrable (n := n) 1)

theorem gμ₄_tendsto :
    Filter.Tendsto (fun R => gμ₄ n R) Filter.atTop (nhds (∫ z : E, ‖z‖ ^ 4 * gauss ‖z‖)) :=
  tendsto_moment (g := fun z : E => ‖z‖ ^ 4) (by fun_prop)
    (by simpa using even_moment_integrable (n := n) 2)

theorem gμ₃_tendsto :
    Filter.Tendsto (fun R => gμ₃ n R) Filter.atTop (nhds (∫ z : E, ‖z‖ ^ 3 * gauss ‖z‖)) := by
  apply tendsto_moment (g := fun z : E => ‖z‖ ^ 3) (by fun_prop)
  refine ((even_moment_integrable (n := n) 0).add (even_moment_integrable (n := n) 2)).mono'
    (((continuous_norm.pow _).mul (gauss_continuous.comp continuous_norm)).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  have hg := (gauss_pos ‖z‖).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Pi.add_apply, mul_zero, pow_zero, one_mul, show 2 * 2 = 4 by rfl]
  have : ‖z‖ ^ 3 ≤ 1 + ‖z‖ ^ 4 := by
    rcases le_total ‖z‖ 1 with h | h
    · nlinarith [pow_le_one₀ (norm_nonneg z) h (n := 3), pow_nonneg (norm_nonneg z) 4]
    · nlinarith [pow_le_pow_right₀ h (show 3 ≤ 4 by norm_num), norm_nonneg z]
  nlinarith

/-- `m₂(R) → (∫ ‖z‖² e^{−‖z‖²/2})/(n (2π)^{n/2})` (that this limit equals `1` is NOT shown). -/
theorem gm₂_tendsto (hn : 1 ≤ n) :
    Filter.Tendsto (fun R => gm₂ n R) Filter.atTop
      (nhds ((∫ z : E, ‖z‖ ^ 2 * gauss ‖z‖) / (n * (2 * Real.pi) ^ ((n : ℝ) / 2)))) := by
  have hc : (n : ℝ) * (2 * Real.pi) ^ ((n : ℝ) / 2) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  exact second_tendsto.div (gK₀_tendsto.const_mul (n : ℝ)) hc

end CTG.FlatNPointGauss
