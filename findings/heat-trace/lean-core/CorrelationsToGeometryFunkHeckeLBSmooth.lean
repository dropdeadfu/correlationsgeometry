/-
Seventieth file (A183, written by a subagent of the author-side session, checked by that session; read by nobody else).
Theorem LB on `S²` for smooth functions, at the population level and for the EXTRINSICALLY defined Laplacian
`sphLapS`. Namespace `CTG.FunkHecke.LBSmooth`; imports the compiled module of the sixty-ninth file
(`CorrelationsToGeometryFunkHeckeGreen`). Check with `./check_funk_hecke_lb_smooth.sh` from `lean/`.

Main statements: `expansion` (pointwise f(x) = Σ_l Π_l f(x) if Σ_l ‖Π_l f‖ < ∞), `Pinf_expansion`, `Lxi_expansion`,
`lap_expansion`, `LB_sphere_smooth_series`, `LB_sphere_smooth` (|L_ξ f(x) + Δf(x)| ≤ 3·W·‖Δ⁴f‖₂·ξ² for 0 < ξ ≤ 1/20),
`LB_sphere_smooth_sup` (∃ C, ∀ ξ ∈ (0,1/20], ∀ x, |L_ξ f(x) + Δf(x)| ≤ C ξ²). Only assumption: the iterates
Δ^j f, j < 4, satisfy `SphC2` everywhere.
NOT shown: identification of `sphLapS` with the intrinsic Laplace–Beltrami operator; the value of W; versions with
fewer than four iterates; the order ξ⁴; sample (N-point) statements. No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeGreen

open MeasureTheory Set Metric Real Filter Topology
open scoped RealInnerProductSpace

namespace CTG.FunkHecke.LBSmooth

open CTG.FunkHecke (S2 E3 cdot Isotropic zonalOp sigma sigma0 gk Pinf sphS)
open CTG.FunkHecke.Proj (harmDeg IsHarm projDeg integrable_of_cont)
open CTG.FunkHecke.Parseval (projC projC_apply projC_mem projDeg_cont L2_tendsto)
open CTG.FunkHecke.SphereLB (Lxi)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2 cLB)

local instance : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

local instance : IsProbabilityMeasure sigma :=
  ⟨by rw [← ofReal_measureReal, CTG.FunkHecke.Proj.sigma_real_univ', ENNReal.ofReal_one]⟩

local instance : sigma.IsOpenPosMeasure := ⟨fun U hU hne => by
  have h0 : sigma0 U ≠ 0 := by
    unfold sigma0; exact MeasureTheory.Measure.IsOpenPosMeasure.open_pos U hU hne
  rw [CTG.FunkHecke.sigma, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (Real.toNNReal_pos.mpr (by positivity)).ne') h0⟩

/-! ## (a) Uniform expansion in degrees -/

theorem proj_le_norm (l : ℕ) (F : C(S2, ℝ)) (x : S2) : |projDeg l F x| ≤ ‖projC l F‖ := by
  have h := (projC l F).norm_coe_le_norm x
  rwa [Real.norm_eq_abs, projC_apply] at h

theorem sq_split (a b c : ℝ) : (a - c) ^ 2 ≤ 2 * (a - b) ^ 2 + 2 * (b - c) ^ 2 := by
  nlinarith [sq_nonneg (a - 2 * b + c)]

set_option maxHeartbeats 800000 in
/-- **(a) Expansion.** If the supremum norms of the projections are summable, the expansion in degrees
converges at every point to `F`. -/
theorem expansion (F : C(S2, ℝ)) (hs : Summable fun l => ‖projC l F‖) (x : S2) :
    HasSum (fun l => projDeg l F x) (F x) := by
  have hsx : ∀ y, Summable fun l => projDeg l F y := fun y =>
    Summable.of_norm_bounded hs fun l => by rw [Real.norm_eq_abs]; exact proj_le_norm l F y
  set h : S2 → ℝ := fun y => ∑' l, projDeg l F y with hdef
  have hcont : Continuous h :=
    continuous_tsum (fun l => projDeg_cont l F) hs fun l y => by
      rw [Real.norm_eq_abs]; exact proj_le_norm l F y
  -- tail bound
  set t : ℕ → ℝ := fun L => ∑' l, ‖projC (l + (L + 1)) F‖ with htdef
  have htail : ∀ L y, |(∑ l ∈ Finset.range (L + 1), projDeg l F y) - h y| ≤ t L := by
    intro L y
    have e := (hsx y).sum_add_tsum_nat_add (L + 1)
    have hs' : Summable fun l => ‖projC (l + (L + 1)) F‖ := (summable_nat_add_iff (f := fun l => ‖projC l F‖) (L + 1)).2 hs
    have hn : Summable fun l => ‖projDeg (l + (L + 1)) F y‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun l => by rw [Real.norm_eq_abs]; exact proj_le_norm _ F y) hs'
    have : (∑ l ∈ Finset.range (L + 1), projDeg l F y) - h y
        = -∑' l, projDeg (l + (L + 1)) F y := by
      rw [hdef]; simp only; rw [← e]; ring
    rw [this, abs_neg, ← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hn).trans ?_
    exact hn.tsum_le_tsum (fun l => by rw [Real.norm_eq_abs]; exact proj_le_norm _ F y) hs'
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have h1 := tendsto_sum_nat_add (fun l => ‖projC l F‖)
    exact h1.comp (tendsto_add_atTop_nat 1)
  -- integral of the square of the difference vanishes
  have hFh : Continuous fun y => (F y - h y) ^ 2 := (F.continuous.sub hcont).pow 2
  have hSc : ∀ L, Continuous fun y => ∑ l ∈ Finset.range (L + 1), projDeg l F y := fun L =>
    continuous_finset_sum _ fun l _ => projDeg_cont l F
  have hle : ∀ L, ∫ y, (F y - h y) ^ 2 ∂sigma
      ≤ 2 * ∫ y, (F y - ∑ l ∈ Finset.range (L + 1), projDeg l F y) ^ 2 ∂sigma + 2 * t L ^ 2 := by
    intro L
    have i1 : Integrable (fun y => (F y - ∑ l ∈ Finset.range (L + 1), projDeg l F y) ^ 2) sigma :=
      integrable_of_cont sigma ((F.continuous.sub (hSc L)).pow 2)
    calc ∫ y, (F y - h y) ^ 2 ∂sigma
        ≤ ∫ y, (2 * (F y - ∑ l ∈ Finset.range (L + 1), projDeg l F y) ^ 2 + 2 * t L ^ 2) ∂sigma := by
          refine integral_mono (integrable_of_cont sigma hFh)
            ((i1.const_mul 2).add (integrable_const _)) fun y => ?_
          refine (sq_split (F y) (∑ l ∈ Finset.range (L + 1), projDeg l F y) (h y)).trans ?_
          have ha := htail L y
          have : ((∑ l ∈ Finset.range (L + 1), projDeg l F y) - h y) ^ 2 ≤ t L ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
          linarith
      _ = 2 * ∫ y, (F y - ∑ l ∈ Finset.range (L + 1), projDeg l F y) ^ 2 ∂sigma + 2 * t L ^ 2 := by
          rw [integral_add (i1.const_mul 2) (integrable_const _), integral_const_mul, integral_const,
            CTG.FunkHecke.Proj.sigma_real_univ', one_smul]
  have hlim : Tendsto (fun L => 2 * ∫ y, (F y - ∑ l ∈ Finset.range (L + 1), projDeg l F y) ^ 2 ∂sigma
      + 2 * t L ^ 2) atTop (𝓝 0) := by
    have := ((L2_tendsto F).const_mul 2).add ((ht0.pow 2).const_mul 2)
    rw [show (2 : ℝ) * 0 + 2 * 0 ^ 2 = 0 by norm_num] at this
    exact this
  have hI0 : ∫ y, (F y - h y) ^ 2 ∂sigma ≤ 0 := ge_of_tendsto' hlim hle
  have heq : F x = h x := by
    by_contra hne
    have hpos : 0 < ∫ y, (F y - h y) ^ 2 ∂sigma :=
      integral_pos_of_integrable_nonneg_nonzero (x := x) hFh (integrable_of_cont sigma hFh)
        (fun y => sq_nonneg _) (pow_ne_zero 2 (sub_ne_zero.2 hne))
    linarith
  rw [heq]
  exact (hsx x).hasSum

/-! ## (b) The population operator on the expansion -/

theorem gk_pos (ξ t : ℝ) : 0 < gk ξ t := Real.exp_pos _

theorem Z_pos (ξ : ℝ) (x : S2) : 0 < zonalOp (gk ξ) (fun _ => 1) x := by
  unfold zonalOp
  have hc : Continuous fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫ * 1 :=
    ((CTG.FunkHecke.gk_continuous ξ).comp (continuous_const.inner continuous_subtype_val)).mul
      continuous_const
  exact integral_pos_of_integrable_nonneg_nonzero (x := x) hc (integrable_of_cont sigma hc)
    (fun y => by simp only [mul_one]; exact (gk_pos _ _).le) (by simp only [mul_one]; exact (gk_pos _ _).ne')

/-- `P_∞ f = s_l f` on a generator of degree `l` (needs `ξ ≠ 0`). -/
theorem Pinf_gen {ξ : ℝ} (hξ : ξ ≠ 0) {l : ℕ} {f : S2 → ℝ} (hf : IsHarm l f) (x : S2) :
    Pinf (gk ξ) f x = sphS ξ l * f x := by
  have hc : (2 : ℝ) / ξ ^ 2 ≠ 0 := by positivity
  obtain ⟨p, q, hpq, e | e⟩ := hf <;> subst e
  · have h := CTG.FunkHecke.SphereLB.Lxi_harmonic ξ p q hpq l x
    unfold Lxi at h
    have : (fun y : S2 => (cdot p q (y : E3) ^ l).re) x - Pinf (gk ξ) (fun y : S2 => (cdot p q (y : E3) ^ l).re) x
        = (1 - sphS ξ l) * (cdot p q (x : E3) ^ l).re := by
      refine mul_left_cancel₀ hc (h.trans ?_)
      ring
    simp only at this ⊢; linarith
  · have h := CTG.FunkHecke.SphereLinComb.Lxi_harmonic_im ξ p q hpq l x
    unfold Lxi at h
    have : (fun y : S2 => (cdot p q (y : E3) ^ l).im) x - Pinf (gk ξ) (fun y : S2 => (cdot p q (y : E3) ^ l).im) x
        = (1 - sphS ξ l) * (cdot p q (x : E3) ^ l).im := by
      refine mul_left_cancel₀ hc (h.trans ?_)
      ring
    simp only at this ⊢; linarith

/-- The eigen-relation of the zonal operator on the span of degree `l`. -/
theorem zonal_span {ξ : ℝ} (hξ : ξ ≠ 0) {l : ℕ} {G : C(S2, ℝ)} (hG : G ∈ harmDeg l) (x : S2) :
    zonalOp (gk ξ) G x = sphS ξ l * G x * zonalOp (gk ξ) (fun _ => 1) x := by
  have hw := CTG.FunkHecke.gk_continuous ξ
  induction hG using Submodule.span_induction with
  | mem G hG =>
      have h := Pinf_gen hξ (hG : IsHarm l ⇑G) x
      unfold Pinf at h
      rw [div_eq_iff (Z_pos ξ x).ne'] at h
      exact h
  | zero => rw [CTG.FunkHecke.Proj.zonalOp_zero]; simp
  | add F G _ _ hF hG =>
      rw [CTG.FunkHecke.Proj.zonalOp_add _ hw, hF, hG]
      simp only [ContinuousMap.coe_add, Pi.add_apply]; ring
  | smul c F _ hF =>
      rw [CTG.FunkHecke.Proj.zonalOp_smul, hF]
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- **(b) `P_∞` on the expansion.** -/
theorem Pinf_expansion {ξ : ℝ} (hξ : ξ ≠ 0) (F : C(S2, ℝ)) (hs : Summable fun l => ‖projC l F‖)
    (x : S2) : HasSum (fun l => sphS ξ l * projDeg l F x) (Pinf (gk ξ) F x) := by
  set Z := zonalOp (gk ξ) (fun _ => 1) x
  have hZ : 0 < Z := Z_pos ξ x
  have hk : Continuous fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫ :=
    (CTG.FunkHecke.gk_continuous ξ).comp (continuous_const.inner continuous_subtype_val)
  have hint : HasSum (fun l => ∫ y, gk ξ ⟪(x : E3), (y : E3)⟫ * projDeg l F y ∂sigma)
      (∫ y, gk ξ ⟪(x : E3), (y : E3)⟫ * F y ∂sigma) := by
    refine hasSum_integral_of_dominated_convergence (fun l _ => ‖projC l F‖)
      (fun l => (hk.mul (projDeg_cont l F)).aestronglyMeasurable) (fun l => ?_)
      (Eventually.of_forall fun _ => hs) (integrable_const _)
      (Eventually.of_forall fun y => (expansion F hs y).mul_left _)
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |gk ξ ⟪(x : E3), (y : E3)⟫| * |projDeg l F y| ≤ 1 * ‖projC l F‖ :=
          mul_le_mul (CTG.FunkHecke.abs_gk_le ξ _) (proj_le_norm l F y) (abs_nonneg _) zero_le_one
      _ = ‖projC l F‖ := one_mul _
  have e : ∀ l, ∫ y, gk ξ ⟪(x : E3), (y : E3)⟫ * projDeg l F y ∂sigma
      = sphS ξ l * projDeg l F x * Z := by
    intro l
    have := zonal_span hξ (projC_mem l F) x
    simpa only [zonalOp, projC_apply] using this
  simp only [e] at hint
  have h2 := hint.div_const Z
  have e2 : (fun l => sphS ξ l * projDeg l F x * Z / Z) = fun l => sphS ξ l * projDeg l F x := by
    funext l; field_simp
  rw [e2] at h2
  exact h2

/-- **(b') `L_ξ` on the expansion.** -/
theorem Lxi_expansion {ξ : ℝ} (hξ : ξ ≠ 0) (F : C(S2, ℝ)) (hs : Summable fun l => ‖projC l F‖)
    (x : S2) : HasSum (fun l => 2 / ξ ^ 2 * (1 - sphS ξ l) * projDeg l F x) (Lxi ξ F x) := by
  have h := ((expansion F hs x).sub (Pinf_expansion hξ F hs x)).mul_left (2 / ξ ^ 2)
  unfold Lxi
  convert h using 1
  funext l; ring

/-! ## (c) The Laplacian on the expansion -/

/-- **(c)** For `f` with `SphC2` everywhere and summable `λ_l ‖Π_l f‖`, `Δf = Σ −l(l+1) Π_l f`. -/
theorem lap_expansion {f : S2 → ℝ} (hf : ∀ x, SphC2 f x)
    (hs : Summable fun l : ℕ => ((l : ℝ) * (l + 1)) * ‖projC l ⟨f, CTG.FunkHecke.Green.sphC2_cont hf⟩‖)
    (x : S2) :
    HasSum (fun l : ℕ => -((l : ℝ) * (l + 1)) * projDeg l f x) (sphLapS f x) := by
  set F : C(S2, ℝ) := ⟨f, CTG.FunkHecke.Green.sphC2_cont hf⟩
  set G : C(S2, ℝ) := ⟨sphLapS f, CTG.FunkHecke.Green.sphLapS_cont hf⟩
  have hG : ∀ l, ‖projC l G‖ ≤ ((l : ℝ) * (l + 1)) * ‖projC l F‖ := by
    intro l
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun y => ?_
    rw [Real.norm_eq_abs, projC_apply]
    show |projDeg l (sphLapS f) y| ≤ _
    rw [CTG.FunkHecke.Green.proj_lap l hf y, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (proj_le_norm l F y) (by positivity)
  have hsG : Summable fun l => ‖projC l G‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hG hs
  have h := expansion G hsG x
  have e : (fun l => projDeg l G x) = fun l : ℕ => -((l : ℝ) * (l + 1)) * projDeg l f x := by
    funext l; exact CTG.FunkHecke.Green.proj_lap l hf x
  rw [e] at h
  exact h

/-! ## (d) Summability from decay and the final estimate -/

/-- `w_l = √(2l+1)/(l(l+1))` (`w_0 = 0`). -/
noncomputable def wseq (l : ℕ) : ℝ := Real.sqrt (2 * (l : ℝ) + 1) / ((l : ℝ) * (l + 1))

theorem wseq_nonneg (l : ℕ) : 0 ≤ wseq l := by unfold wseq; positivity

theorem wseq_le (l : ℕ) : wseq l ≤ 2 * (1 / (l : ℝ) ^ ((3 : ℝ) / 2)) := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp [wseq]
  · have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hl0 : (0 : ℝ) < l := by linarith
    have hr : (l : ℝ) ^ ((3 : ℝ) / 2) = l * Real.sqrt l := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hl0, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [hr]
    unfold wseq
    have hs : 0 < Real.sqrt l := Real.sqrt_pos.2 hl0
    rw [div_le_iff₀ (by positivity)]
    -- √(2l+1) ≤ 2 (l+1) / √l
    have key : Real.sqrt (2 * (l : ℝ) + 1) * Real.sqrt l ≤ 2 * ((l : ℝ) + 1) := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    rw [show 2 * (1 / ((l : ℝ) * Real.sqrt l)) * ((l : ℝ) * (l + 1))
        = 2 * ((l : ℝ) + 1) / Real.sqrt l by field_simp]
    rw [le_div_iff₀ hs]; exact key

theorem wseq_summable : Summable wseq :=
  Summable.of_nonneg_of_le wseq_nonneg wseq_le
    ((Real.summable_one_div_nat_rpow.2 (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2)

/-- The `L²` norm of `Δ⁴ f`. -/
noncomputable def N4 (f : S2 → ℝ) : ℝ := Real.sqrt (∫ y, (sphLapS^[4] f) y ^ 2 ∂sigma)

/-- Decay with `k = 4` in the form `λ^4 ‖Π_l f‖ ≤ √(2l+1) N4`. -/
theorem decay4 {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) (hcf : Continuous f) (l : ℕ) :
    ((l : ℝ) * (l + 1)) ^ 4 * ‖projC l ⟨f, hcf⟩‖ ≤ Real.sqrt (2 * (l : ℝ) + 1) * N4 f := by
  have hlam : (0 : ℝ) ≤ ((l : ℝ) * (l + 1)) ^ 4 := by positivity
  rcases eq_or_lt_of_le hlam with h0 | hpos
  · rw [← h0, zero_mul]; unfold N4; positivity
  · rw [← le_div_iff₀' hpos]
    refine (ContinuousMap.norm_le _ (by unfold N4; positivity)).2 fun y => ?_
    rw [Real.norm_eq_abs, projC_apply, le_div_iff₀' hpos]
    exact CTG.FunkHecke.Green.decay_sup_fin f hcf 4 hf l y

theorem lam_cube_bound {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) (hcf : Continuous f)
    (l : ℕ) : ((l : ℝ) * (l + 1)) ^ 3 * ‖projC l ⟨f, hcf⟩‖ ≤ N4 f * wseq l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp [wseq]
  · have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hlam : (2 : ℝ) ≤ (l : ℝ) * (l + 1) := by nlinarith
    have hd := decay4 hf hcf l
    unfold wseq
    rw [mul_div_assoc', le_div_iff₀ (by linarith)]
    calc ((l : ℝ) * (l + 1)) ^ 3 * ‖projC l ⟨f, hcf⟩‖ * ((l : ℝ) * (l + 1))
        = ((l : ℝ) * (l + 1)) ^ 4 * ‖projC l ⟨f, hcf⟩‖ := by ring
      _ ≤ _ := hd
      _ = N4 f * Real.sqrt (2 * (l : ℝ) + 1) := by ring

theorem lam_le_cube (l : ℕ) : (l : ℝ) * (l + 1) ≤ ((l : ℝ) * (l + 1)) ^ 3 := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · simp
  · have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hlam : (1 : ℝ) ≤ (l : ℝ) * (l + 1) := by nlinarith
    nlinarith [mul_le_mul hlam hlam zero_le_one (by linarith)]

theorem one_le_lam {l : ℕ} (hl : 0 < l) : (1 : ℝ) ≤ (l : ℝ) * (l + 1) := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  nlinarith

theorem summable_lam_norm {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    (hcf : Continuous f) : Summable fun l : ℕ => ((l : ℝ) * (l + 1)) * ‖projC l ⟨f, hcf⟩‖ :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (fun l => (mul_le_mul_of_nonneg_right (lam_le_cube l) (norm_nonneg _)).trans
      (lam_cube_bound hf hcf l))
    (wseq_summable.mul_left _)

theorem summable_norm {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    (hcf : Continuous f) : Summable fun l => ‖projC l ⟨f, hcf⟩‖ := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
    ((summable_nat_add_iff 1).2 (summable_lam_norm hf hcf))
  have h1 := one_le_lam (Nat.succ_pos l)
  push_cast at h1 ⊢
  exact le_mul_of_one_le_left (norm_nonneg _) h1

/-- `cLB(ξ,l) ≤ 3 ξ² λ³` for `0 < ξ ≤ 1/20`. -/
theorem cLB_le {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (l : ℕ) :
    cLB ξ l ≤ 3 * ξ ^ 2 * ((l : ℝ) * (l + 1)) ^ 3 := by
  unfold cLB
  set A : ℝ := (l : ℝ) * (l + 1)
  have hA : 0 ≤ A := by positivity
  have h13 : A ≤ A ^ 3 := lam_le_cube l
  have h23 : A ^ 2 ≤ A ^ 3 := by
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [A]
    · have := one_le_lam hl
      nlinarith [pow_nonneg hA 2]
  have hξ2 : ξ ^ 2 ≤ 1 / 400 := by nlinarith
  have hξ4 : ξ ^ 4 ≤ ξ ^ 2 := by nlinarith [sq_nonneg ξ, pow_two_nonneg ξ]
  have e1 : (ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * A ≤ ξ ^ 2 * A ^ 3 := by
    have : ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4 ≤ ξ ^ 2 := by nlinarith [sq_nonneg ξ]
    calc (ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * A ≤ ξ ^ 2 * A := mul_le_mul_of_nonneg_right this hA
      _ ≤ ξ ^ 2 * A ^ 3 := mul_le_mul_of_nonneg_left h13 (by positivity)
  have e2 : 51 / 200 * ξ ^ 2 * A ^ 2 ≤ ξ ^ 2 * A ^ 3 := by
    have := mul_le_mul_of_nonneg_left h23 (by positivity : (0 : ℝ) ≤ ξ ^ 2)
    nlinarith [pow_nonneg hA 2, sq_nonneg ξ]
  have e3 : 27 / 200 * ξ ^ 4 * A ^ 3 ≤ ξ ^ 2 * A ^ 3 := by
    have := mul_le_mul_of_nonneg_right hξ4 (pow_nonneg hA 3)
    nlinarith [pow_nonneg hA 3, pow_nonneg (sq_nonneg ξ) 2]
  linarith

/-- **`thm:LB` on `S²` for smooth `f`, series form.** For `f` whose iterates `Δ^j f`, `j < 4`, satisfy
`SphC2` everywhere, every `ξ ≠ 0` and `x ∈ S²`:
`HasSum (l ↦ ((2/ξ²)(1 − s_l) − l(l+1)) · Π_l f(x)) (L_ξ f(x) + Δ_{S²} f(x))`. -/
theorem LB_sphere_smooth_series {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    {ξ : ℝ} (hξ : ξ ≠ 0) (x : S2) :
    HasSum (fun l : ℕ => (2 / ξ ^ 2 * (1 - sphS ξ l) - (l : ℝ) * (l + 1)) * projDeg l f x)
      (Lxi ξ f x + sphLapS f x) := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  have hcf := CTG.FunkHecke.Green.sphC2_cont hf0
  have h1 := Lxi_expansion hξ ⟨f, hcf⟩ (summable_norm hf hcf) x
  have h2 := lap_expansion hf0 (summable_lam_norm hf hcf) x
  have h := h1.add h2
  convert h using 1
  funext l
  show _ = 2 / ξ ^ 2 * (1 - sphS ξ l) * projDeg l f x + -((l : ℝ) * (l + 1)) * projDeg l f x
  ring

/-- **`thm:LB` on `S²` for smooth `f`** (population level, extrinsic `Δ_{S²} = sphLapS`): for `f` whose iterates
`Δ^j f`, `j < 4`, satisfy `SphC2` everywhere, `0 < ξ ≤ 1/20` and every `x ∈ S²`:
`|L_ξ f(x) + Δ_{S²} f(x)| ≤ Σ_l cLB(ξ,l) |Π_l f(x)| ≤ 3 · W · ‖Δ⁴ f‖_{L²(σ)} · ξ²`, `W = Σ_l √(2l+1)/(l(l+1))`. -/
theorem LB_sphere_smooth {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (x : S2) :
    Summable (fun l => cLB ξ l * |projDeg l f x|) ∧
    |Lxi ξ f x + sphLapS f x| ≤ ∑' l, cLB ξ l * |projDeg l f x| ∧
    ∑' l, cLB ξ l * |projDeg l f x| ≤ 3 * (∑' l, wseq l) * N4 f * ξ ^ 2 := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  have hcf := CTG.FunkHecke.Green.sphC2_cont hf0
  have hb : ∀ l, cLB ξ l * |projDeg l f x| ≤ 3 * ξ ^ 2 * (N4 f * wseq l) := by
    intro l
    calc cLB ξ l * |projDeg l f x|
        ≤ 3 * ξ ^ 2 * ((l : ℝ) * (l + 1)) ^ 3 * ‖projC l ⟨f, hcf⟩‖ :=
          mul_le_mul (cLB_le hξ hξ1 l) (proj_le_norm l ⟨f, hcf⟩ x) (abs_nonneg _) (by positivity)
      _ = 3 * ξ ^ 2 * (((l : ℝ) * (l + 1)) ^ 3 * ‖projC l ⟨f, hcf⟩‖) := by ring
      _ ≤ 3 * ξ ^ 2 * (N4 f * wseq l) :=
          mul_le_mul_of_nonneg_left (lam_cube_bound hf hcf l) (by positivity)
  have hnn : ∀ l, 0 ≤ cLB ξ l * |projDeg l f x| := fun l =>
    mul_nonneg (CTG.FunkHecke.SphereLinComb.cLB_nonneg ξ l) (abs_nonneg _)
  have hW : Summable fun l => 3 * ξ ^ 2 * (N4 f * wseq l) := (wseq_summable.mul_left _).mul_left _
  have hsum : Summable fun l => cLB ξ l * |projDeg l f x| := Summable.of_nonneg_of_le hnn hb hW
  refine ⟨hsum, ?_, ?_⟩
  · have hS := LB_sphere_smooth_series hf hξ.ne' x
    have he : ∀ l, ‖(2 / ξ ^ 2 * (1 - sphS ξ l) - (l : ℝ) * (l + 1)) * projDeg l f x‖
        ≤ cLB ξ l * |projDeg l f x| := by
      intro l
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      unfold cLB; exact CTG.FunkHecke.SphereLB.eig_limit hξ hξ1 l
    have hn : Summable fun l : ℕ => ‖(2 / ξ ^ 2 * (1 - sphS ξ l) - (l : ℝ) * (l + 1)) * projDeg l f x‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) he hsum
    rw [← hS.tsum_eq, ← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum he hsum)
  · calc ∑' l, cLB ξ l * |projDeg l f x| ≤ ∑' l, 3 * ξ ^ 2 * (N4 f * wseq l) :=
          hsum.tsum_le_tsum hb hW
      _ = 3 * (∑' l, wseq l) * N4 f * ξ ^ 2 := by
          rw [tsum_mul_left, tsum_mul_left]; ring

/-- Supremum form: `sup_x |L_ξ f(x) + Δ_{S²} f(x)| ≤ C(f) ξ²` with `C(f) = 3 W ‖Δ⁴ f‖₂`, for `0 < ξ ≤ 1/20`. -/
theorem LB_sphere_smooth_sup {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 → ∀ x : S2,
      |Lxi ξ f x + sphLapS f x| ≤ C * ξ ^ 2 := by
  refine ⟨3 * (∑' l, wseq l) * N4 f, ?_, fun ξ hξ hξ1 x => ?_⟩
  · have : 0 ≤ ∑' l, wseq l := tsum_nonneg wseq_nonneg
    unfold N4; positivity
  · obtain ⟨-, h1, h2⟩ := LB_sphere_smooth hf hξ hξ1 x
    exact h1.trans h2

/-- **(a') The expansion for smooth `f`**: `f(x) = Σ_l Π_l f(x)` (uniformly; here pointwise). -/
theorem expansion_smooth {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) (x : S2) :
    HasSum (fun l => projDeg l f x) (f x) := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  have hcf := CTG.FunkHecke.Green.sphC2_cont hf0
  exact expansion ⟨f, hcf⟩ (summable_norm hf hcf) x

end CTG.FunkHecke.LBSmooth

#print axioms CTG.FunkHecke.LBSmooth.expansion
#print axioms CTG.FunkHecke.LBSmooth.LB_sphere_smooth_series
#print axioms CTG.FunkHecke.LBSmooth.LB_sphere_smooth
#print axioms CTG.FunkHecke.LBSmooth.LB_sphere_smooth_sup
