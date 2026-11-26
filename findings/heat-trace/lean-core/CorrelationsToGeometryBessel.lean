import Mathlib

/-!
# Modified Bessel functions `K₀`, `K₁` and the constant `c₀ = 1/2` (Mathlib only)

Thirteenth Lean file of the project "From Correlations to Geometry"; it imports only Mathlib (tag v4.29.0,
which contains no modified Bessel functions).  Check with `cd lean && ./check_bessel.sh`.

`K0 z = ∫_0^∞ exp(-z cosh t) dt` and `K1 z = ∫_0^∞ exp(-z cosh t) cosh t dt` are DEFINED by the standard
integral representations; that they are the classical functions is not a statement of this file.
Main results, for `z > 0`: positivity, `K0 < K1`, `K0' = -K1`, the identity
`z (K1 - K0) = ∫ exp(-z cosh t)/(cosh t + 1) dt`, hence `0 < z (K1/K0 - 1) ≤ 1/2`, the lower bound
`1/2 - 1/(8z)`, the limit `1/2` and `sSup {z (K1 z / K0 z - 1) | z ≥ 1/4} = 1/2`: the constant `c₀` of
Proposition "lapse-stab" (Appendix H of the paper) equals `1/2`.  Further `|log (K0 z'/K0 z)| ≤
(1 + 1/(2 zmin)) |z' - z|` and `e^{-z}/√z ≤ K0 z ≤ √(π/(2z)) e^{-z}` (lower bound for `z ≥ 1`, not sharp).
Namespace `CTG.BesselK.LapseStab` (added 26 November 2026): Proposition "lapse-stab" as a complete
deterministic statement (`lapse_stab`, `lapse_stab_additive`, `lapse_stab_general`), with the constants 16, 32,
96, 12 of the paper; the correlators are arbitrary positive reals.
Not formalised: Theorem "vargap", Theorem "lapse-est", `K_ν` for general `ν`.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/

/-!
# Modified Bessel functions K₀, K₁ via their integral representations (A120)

Mathlib v4.29 has no modified Bessel functions; we define
`K0 z = ∫_{t>0} exp(-z cosh t)` and `K1 z = ∫_{t>0} exp(-z cosh t) cosh t` for `z > 0`
(for `z ≤ 0` the integrals are not integrable and Lean's convention gives `0`).
-/

open Real MeasureTheory Set Filter Topology

namespace CTG.BesselK

/-- `K₀(z) = ∫_0^∞ exp(-z cosh t) dt`. -/
noncomputable def K0 (z : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), exp (-z * cosh t)

/-- `K₁(z) = ∫_0^∞ exp(-z cosh t) cosh t dt`. -/
noncomputable def K1 (z : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), exp (-z * cosh t) * cosh t

theorem one_add_sq_div_two_le_cosh (t : ℝ) : 1 + t ^ 2 / 2 ≤ cosh t := by
  have h2 : cosh t = 1 + 2 * sinh (t / 2) ^ 2 := by
    have := Real.cosh_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring, Real.cosh_sq] at this
    linarith
  have hs : (t / 2) ^ 2 ≤ sinh (t / 2) ^ 2 := by
    rcases le_total 0 t with ht | ht
    · have h0 : 0 ≤ t / 2 := by linarith
      have := Real.self_le_sinh_iff.mpr h0
      nlinarith
    · have h0 : 0 ≤ -(t / 2) := by linarith
      have := Real.self_le_sinh_iff.mpr h0
      rw [Real.sinh_neg] at this
      nlinarith
  rw [h2]; nlinarith

theorem exp_cosh_le {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    exp (-a * cosh t) ≤ exp (-a) * exp (-(a / 2) * t ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := one_add_sq_div_two_le_cosh t
  nlinarith

theorem gauss_integrableOn {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => exp (-a) * exp (-(a / 2) * t ^ 2)) (Ioi 0) := by
  have : IntegrableOn (fun t : ℝ => exp (-(a / 2) * t ^ 2)) (Ioi 0) :=
    integrableOn_Ioi_exp_neg_mul_sq_iff.mpr (by linarith)
  exact this.const_mul _

theorem integrableOn_K0 {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => exp (-z * cosh t)) (Ioi 0) := by
  refine (gauss_integrableOn hz).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => exp (-z * cosh t)).aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_cosh_le hz.le t

theorem mul_exp_neg_le {z : ℝ} (hz : 0 < z) (x : ℝ) :
    x * exp (-z * x) ≤ 2 / z * exp (-(z / 2) * x) := by
  have h1 : z * x / 2 ≤ exp (z * x / 2) := by
    have := Real.add_one_le_exp (z * x / 2); linarith
  have hE : 0 ≤ exp (-z * x) := (Real.exp_pos _).le
  have key : x * exp (-z * x) = 2 / z * ((z * x / 2) * exp (-z * x)) := by
    field_simp
  rw [key]
  have h3 : (z * x / 2) * exp (-z * x) ≤ exp (z * x / 2) * exp (-z * x) :=
    mul_le_mul_of_nonneg_right h1 hE
  rw [← Real.exp_add] at h3
  have h4 : z * x / 2 + -z * x = -(z / 2) * x := by ring
  rw [h4] at h3
  exact mul_le_mul_of_nonneg_left h3 (by positivity)

theorem integrableOn_K1 {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => exp (-z * cosh t) * cosh t) (Ioi 0) := by
  have hz2 : 0 < z / 2 := by linarith
  refine ((integrableOn_K0 hz2).const_mul (2 / z)).mono' ?_ ?_
  · exact (by fun_prop : Continuous fun t : ℝ => exp (-z * cosh t) * cosh t).aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    have hc : 0 ≤ cosh t := (Real.cosh_pos t).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hc), mul_comm]
    exact mul_exp_neg_le hz (cosh t)

theorem K0_pos {z : ℝ} (hz : 0 < z) : 0 < K0 z := by
  unfold K0
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun t => (Real.exp_pos _).le)) (integrableOn_K0 hz)]
  have : Function.support (fun t : ℝ => exp (-z * cosh t)) = univ := by
    ext t; simp [(Real.exp_pos _).ne']
  rw [this, univ_inter, Real.volume_Ioi]
  simp

/-- `K₁ - K₀ = ∫ exp(-z cosh t)(cosh t - 1) dt`. -/
theorem K1_sub_K0 {z : ℝ} (hz : 0 < z) :
    K1 z - K0 z = ∫ t in Ioi (0:ℝ), exp (-z * cosh t) * (cosh t - 1) := by
  unfold K1 K0
  rw [← integral_sub (integrableOn_K1 hz) (integrableOn_K0 hz)]
  congr 1; ext t; ring

theorem K0_lt_K1 {z : ℝ} (hz : 0 < z) : K0 z < K1 z := by
  have hint : IntegrableOn (fun t : ℝ => exp (-z * cosh t) * (cosh t - 1)) (Ioi 0) := by
    have := (integrableOn_K1 hz).sub (integrableOn_K0 hz)
    refine this.congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
  have hpos : 0 < ∫ t in Ioi (0:ℝ), exp (-z * cosh t) * (cosh t - 1) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
    · have : Function.support (fun t : ℝ => exp (-z * cosh t) * (cosh t - 1)) ∩ Ioi 0
          = Ioi 0 := by
        ext t
        simp only [mem_inter_iff, Function.mem_support, mem_Ioi]
        constructor
        · exact fun h => h.2
        · intro ht
          refine ⟨?_, ht⟩
          have : 1 < cosh t := Real.one_lt_cosh.mpr ht.ne'
          exact (mul_pos (Real.exp_pos _) (by linarith)).ne'
      rw [this, Real.volume_Ioi]; simp
    · refine Eventually.of_forall (fun t => ?_)
      exact mul_nonneg (Real.exp_pos _).le (by linarith [Real.one_le_cosh t])
  have := K1_sub_K0 hz
  linarith

theorem K1_pos {z : ℝ} (hz : 0 < z) : 0 < K1 z := (K0_pos hz).trans (K0_lt_K1 hz)

/-- `K₀' = -K₁` (differentiation under the integral sign). -/
theorem hasDerivAt_K0 {z : ℝ} (hz : 0 < z) : HasDerivAt K0 (-K1 z) z := by
  have hz2 : 0 < z / 2 := by linarith
  have hs : Metric.ball z (z / 2) ∈ 𝓝 z := Metric.ball_mem_nhds z hz2
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun x t => exp (-x * cosh t)) (F' := fun x t => -(exp (-x * cosh t) * cosh t))
    (bound := fun t => exp (-(z / 2) * cosh t) * cosh t) hs
    (Eventually.of_forall (fun x =>
      (by fun_prop : Continuous fun t : ℝ => exp (-x * cosh t)).aestronglyMeasurable))
    (integrableOn_K0 hz)
    ((by fun_prop : Continuous fun t : ℝ => -(exp (-z * cosh t) * cosh t)).aestronglyMeasurable)
    ?_ (integrableOn_K1 hz2) ?_
  · have h2 := key.2
    unfold K0 K1
    rw [integral_neg] at h2
    exact h2
  · refine Eventually.of_forall (fun t x hx => ?_)
    have hc : 0 ≤ cosh t := (Real.cosh_pos t).le
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hc)]
    have hx' : z / 2 ≤ x := by
      have := Metric.mem_ball.mp hx
      rw [Real.dist_eq] at this
      have := (abs_lt.mp this).1
      linarith
    apply mul_le_mul_of_nonneg_right _ hc
    apply Real.exp_le_exp.mpr
    nlinarith [Real.one_le_cosh t]
  · refine Eventually.of_forall (fun t x _ => ?_)
    have h := ((hasDerivAt_id x).neg.mul_const (cosh t)).exp
    convert h using 1
    simp

theorem K0_strictAntiOn : StrictAntiOn K0 (Ioi 0) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0)
    (f' := fun z => -K1 z)
  · intro x hx
    exact (hasDerivAt_K0 hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hasDerivAt_K0 hx).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact neg_lt_zero.mpr (K1_pos hx)

theorem alg1 (z E c s : ℝ) (hc : c + 1 ≠ 0) (hs : s ^ 2 = c ^ 2 - 1) :
    E / (c + 1) - z * (E * (c - 1)) = ((E * (-z * s) * s + E * c) * (c + 1) - E * s * s) / (c + 1) ^ 2 := by
  have key : ((E * (-z * s) * s + E * c) * (c + 1) - E * s * s) / (c + 1) ^ 2
      - (E / (c + 1) - z * (E * (c - 1))) = -(E * (1 + z * (c + 1)) * (s ^ 2 - (c ^ 2 - 1))) / (c + 1) ^ 2 := by
    field_simp; ring
  rw [hs, sub_self, mul_zero, neg_zero, zero_div] at key
  linarith

/-- Integration-by-parts identity: `z (K₁ - K₀) = ∫ exp(-z cosh t)/(cosh t + 1) dt`. -/
theorem key_identity {z : ℝ} (hz : 0 < z) :
    z * (K1 z - K0 z) = ∫ t in Ioi (0:ℝ), exp (-z * cosh t) / (cosh t + 1) := by
  set G : ℝ → ℝ := fun t => exp (-z * cosh t) * sinh t / (cosh t + 1) with hG
  set G' : ℝ → ℝ := fun t =>
    exp (-z * cosh t) / (cosh t + 1) - z * (exp (-z * cosh t) * (cosh t - 1)) with hG'
  have hint1 : IntegrableOn (fun t : ℝ => exp (-z * cosh t) / (cosh t + 1)) (Ioi 0) := by
    refine (integrableOn_K0 hz).mono' ?_ ?_
    · exact (by fun_prop (disch := intro t; positivity) :
        Continuous fun t : ℝ => exp (-z * cosh t) / (cosh t + 1)).aestronglyMeasurable
    · refine Eventually.of_forall (fun t => ?_)
      have hc : 1 ≤ cosh t + 1 := by linarith [Real.cosh_pos t]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (by linarith))]
      exact div_le_self (Real.exp_pos _).le hc
  have hint2 : IntegrableOn (fun t : ℝ => exp (-z * cosh t) * (cosh t - 1)) (Ioi 0) :=
    ((integrableOn_K1 hz).sub (integrableOn_K0 hz)).congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_Ioi
  have hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt G (G' t) t := by
    intro t _
    have hc1 : cosh t + 1 ≠ 0 := by linarith [Real.cosh_pos t]
    have he : HasDerivAt (fun t => exp (-z * cosh t)) (exp (-z * cosh t) * (-z * sinh t)) t :=
      ((Real.hasDerivAt_cosh t).const_mul (-z)).exp
    have h := (he.mul (Real.hasDerivAt_sinh t)).div ((Real.hasDerivAt_cosh t).add_const 1) hc1
    convert h using 1
    simp only [hG', Pi.mul_apply]
    exact alg1 z _ _ _ hc1 (Real.sinh_sq t)
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => -z * cosh t) atTop atBot := by
      have : Tendsto cosh atTop atTop := by
        refine tendsto_atTop_mono (fun t => ?_) tendsto_id
        simp only [id]
        have := one_add_sq_div_two_le_cosh t
        nlinarith [sq_nonneg (t - 1)]
      exact this.const_mul_atTop_of_neg (by linarith)
    have he : Tendsto (fun t : ℝ => exp (-z * cosh t)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht
      have : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr ht
      have : 0 < cosh t + 1 := by linarith [Real.cosh_pos t]
      positivity
    · filter_upwards with t
      have hc1 : 0 < cosh t + 1 := by linarith [Real.cosh_pos t]
      have hsc : sinh t ≤ cosh t + 1 := by linarith [Real.sinh_lt_cosh (x := t)]
      show exp (-z * cosh t) * sinh t / (cosh t + 1) ≤ exp (-z * cosh t)
      rw [mul_div_assoc]
      have : sinh t / (cosh t + 1) ≤ 1 := (div_le_one hc1).mpr hsc
      calc exp (-z * cosh t) * (sinh t / (cosh t + 1)) ≤ exp (-z * cosh t) * 1 :=
            mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
        _ = exp (-z * cosh t) := mul_one _
  have hG'int : IntegrableOn G' (Ioi 0) := hint1.sub (hint2.const_mul z)
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hG'int hlim
  have hG0 : G 0 = 0 := by simp [hG]
  rw [hG0, sub_zero] at hftc
  have hsplit : ∫ t in Ioi (0:ℝ), G' t =
      (∫ t in Ioi (0:ℝ), exp (-z * cosh t) / (cosh t + 1))
        - z * ∫ t in Ioi (0:ℝ), exp (-z * cosh t) * (cosh t - 1) := by
    rw [hG', integral_sub hint1 (hint2.const_mul z), integral_const_mul]
  rw [hsplit, ← K1_sub_K0 hz] at hftc
  linarith

theorem integrableOn_div {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => exp (-z * cosh t) / (cosh t + 1)) (Ioi 0) := by
  refine (integrableOn_K0 hz).mono' ?_ ?_
  · exact (by fun_prop (disch := intro t; positivity) :
      Continuous fun t : ℝ => exp (-z * cosh t) / (cosh t + 1)).aestronglyMeasurable
  · refine Eventually.of_forall (fun t => ?_)
    have hc : 1 ≤ cosh t + 1 := by linarith [Real.cosh_pos t]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le (by linarith))]
    exact div_le_self (Real.exp_pos _).le hc

/-- The ratio bound behind `c₀ ≤ 1/2`: `z (K₁ - K₀) ≤ K₀ / 2` for every `z > 0`. -/
theorem ratio_upper {z : ℝ} (hz : 0 < z) : z * (K1 z - K0 z) ≤ K0 z / 2 := by
  rw [key_identity hz, K0, ← integral_div]
  refine setIntegral_mono (integrableOn_div hz) ((integrableOn_K0 hz).div_const 2) (fun t => ?_)
  have hc : 2 ≤ cosh t + 1 := by linarith [Real.one_le_cosh t]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) hc

/-- Lower companion: `K₀/2 - (K₁ - K₀)/4 ≤ z (K₁ - K₀)`. -/
theorem ratio_lower {z : ℝ} (hz : 0 < z) : K0 z / 2 - (K1 z - K0 z) / 4 ≤ z * (K1 z - K0 z) := by
  have hint2 : IntegrableOn (fun t : ℝ => exp (-z * cosh t) * (cosh t - 1)) (Ioi 0) :=
    ((integrableOn_K1 hz).sub (integrableOn_K0 hz)).congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring)
      measurableSet_Ioi
  have hlhs : K0 z / 2 - (K1 z - K0 z) / 4 = ∫ t in Ioi (0:ℝ),
      (exp (-z * cosh t) / 2 - exp (-z * cosh t) * (cosh t - 1) / 4) := by
    rw [integral_sub ((integrableOn_K0 hz).div_const 2) (hint2.div_const 4), integral_div,
      integral_div, ← K1_sub_K0 hz, K0]
  rw [hlhs, key_identity hz]
  refine setIntegral_mono (((integrableOn_K0 hz).div_const 2).sub (hint2.div_const 4))
    (integrableOn_div hz) (fun t => ?_)
  have hc : 1 ≤ cosh t := Real.one_le_cosh t
  have hE : 0 < exp (-z * cosh t) := Real.exp_pos _
  have hc1 : 0 < cosh t + 1 := by linarith
  rw [div_sub_div _ _ (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0),
    div_le_div_iff₀ (by norm_num) hc1]
  nlinarith [sq_nonneg (cosh t - 1), mul_nonneg hE.le (sq_nonneg (cosh t - 1))]

/-- Upper half of the large-argument sandwich: `K₀(z) ≤ √(π/(2z)) e^{-z}`. -/
theorem K0_le {z : ℝ} (hz : 0 < z) : K0 z ≤ sqrt (π / (2 * z)) * exp (-z) := by
  have h1 : K0 z ≤ ∫ t in Ioi (0:ℝ), exp (-z) * exp (-(z / 2) * t ^ 2) :=
    setIntegral_mono (integrableOn_K0 hz) (gauss_integrableOn hz) (fun t => exp_cosh_le hz.le t)
  rw [integral_const_mul, integral_gaussian_Ioi] at h1
  have h2 : sqrt (π / (z / 2)) / 2 = sqrt (π / (2 * z)) := by
    have : π / (z / 2) = 4 * (π / (2 * z)) := by field_simp; ring
    rw [this, Real.sqrt_mul (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
    ring
  rw [h2] at h1
  linarith

/-- `0 < z (K₁/K₀ - 1) ≤ 1/2` for every `z > 0`; hence `c₀ ≤ 1/2`. -/
theorem c0_bound {z : ℝ} (hz : 0 < z) :
    0 < z * (K1 z / K0 z - 1) ∧ z * (K1 z / K0 z - 1) ≤ 1 / 2 := by
  have h0 := K0_pos hz
  have hr : z * (K1 z / K0 z - 1) = z * (K1 z - K0 z) / K0 z := by field_simp
  rw [hr]
  refine ⟨div_pos (mul_pos hz (by linarith [K0_lt_K1 hz])) h0, ?_⟩
  rw [div_le_iff₀ h0]
  linarith [ratio_upper hz]

/-- `z (K₁/K₀ - 1) ≥ 1/2 - 1/(8z)` for every `z > 0`. -/
theorem c0_lower {z : ℝ} (hz : 0 < z) : 1 / 2 - 1 / (8 * z) ≤ z * (K1 z / K0 z - 1) := by
  have h0 := K0_pos hz
  have hu := ratio_upper hz
  have hl := ratio_lower hz
  have hd : K1 z - K0 z ≤ K0 z / (2 * z) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hr : z * (K1 z / K0 z - 1) = z * (K1 z - K0 z) / K0 z := by field_simp
  rw [hr, le_div_iff₀ h0]
  have : (K1 z - K0 z) / 4 ≤ K0 z / (8 * z) := by
    rw [show K0 z / (8 * z) = (K0 z / (2 * z)) / 4 by field_simp; ring]
    linarith
  have h8 : (1 / 2 - 1 / (8 * z)) * K0 z = K0 z / 2 - K0 z / (8 * z) := by ring
  linarith

theorem c0_tendsto : Tendsto (fun z => z * (K1 z / K0 z - 1)) atTop (𝓝 (1 / 2)) := by
  have hlow : Tendsto (fun z : ℝ => 1 / 2 - 1 / (8 * z)) atTop (𝓝 (1 / 2)) := by
    have : Tendsto (fun z : ℝ => 1 / (8 * z)) atTop (𝓝 0) := by
      exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 8))
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with z hz using c0_lower hz
  · filter_upwards [eventually_gt_atTop 0] with z hz using (c0_bound hz).2

/-- The constant of `prop:lapse-stab`: `c₀ = sup_{z ≥ 1/4} z(K₁/K₀ - 1) = 1/2`. -/
theorem c0_eq : sSup ((fun z => z * (K1 z / K0 z - 1)) '' Ici (1 / 4)) = 1 / 2 := by
  apply IsLUB.csSup_eq _ ((nonempty_Ici).image _)
  constructor
  · rintro _ ⟨z, hz, rfl⟩
    exact (c0_bound (by have := mem_Ici.mp hz; linarith)).2
  · intro b hb
    refine le_of_tendsto c0_tendsto ?_
    filter_upwards [eventually_ge_atTop (1 / 4)] with z hz
    exact hb ⟨z, hz, rfl⟩

/-- How `c₀` enters `prop:lapse-stab`: for `z, z' ≥ z_min > 0`,
`|log(K₀(z')/K₀(z))| ≤ (1 + c₀/z_min) |z' - z|` with `c₀ = 1/2`. -/
theorem log_K0_lipschitz {zmin z z' : ℝ} (h0 : 0 < zmin) (hz : zmin ≤ z) (hz' : zmin ≤ z') :
    |log (K0 z' / K0 z)| ≤ (1 + (1 / 2) / zmin) * |z' - z| := by
  have hpos : ∀ x ∈ Ici zmin, 0 < x := fun x hx => lt_of_lt_of_le h0 hx
  have hd : ∀ x ∈ Ici zmin, HasDerivWithinAt (fun x => log (K0 x)) (-K1 x / K0 x) (Ici zmin) x :=
    fun x hx => ((hasDerivAt_K0 (hpos x hx)).log (K0_pos (hpos x hx)).ne').hasDerivWithinAt
  have hb : ∀ x ∈ Ici zmin, ‖-K1 x / K0 x‖ ≤ 1 + (1 / 2) / zmin := by
    intro x hx
    have hx0 := hpos x hx
    have hK0 := K0_pos hx0
    have hK1 := K1_pos hx0
    rw [Real.norm_eq_abs, neg_div, abs_neg, abs_of_pos (div_pos hK1 hK0)]
    have h1 : K1 x / K0 x - 1 ≤ (1 / 2) / x := by
      have := (c0_bound hx0).2
      rw [le_div_iff₀ hx0]; linarith
    have h2 : (1 / 2) / x ≤ (1 / 2) / zmin := div_le_div_of_nonneg_left (by norm_num) h0 hx
    linarith
  have := (convex_Ici zmin).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hz hz'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  rwa [Real.log_div (K0_pos (hpos z' hz')).ne' (K0_pos (hpos z hz)).ne']

/-- Lower half of an explicit sandwich: `K₀(z) ≥ e^{-z}/√z` for `z ≥ 1`
(constant `1` instead of the sharp `√(π/2) ≈ 1.2533`). -/
theorem K0_ge {z : ℝ} (hz : 1 ≤ z) : exp (-z) / sqrt z ≤ K0 z := by
  have hz0 : 0 < z := by linarith
  set b := sqrt z with hb
  have hb0 : 0 < b := Real.sqrt_pos.mpr hz0
  have hbb : b * b = z := Real.mul_self_sqrt hz0.le
  have hb1 : 1 ≤ b := by rw [hb]; exact Real.one_le_sqrt.mpr hz
  set G : ℝ → ℝ := fun t => -(exp (-z * cosh t) / (z * sinh t + b)) with hG
  set G' : ℝ → ℝ := fun t => exp (-z * cosh t) *
      (z * sinh t / (z * sinh t + b) + z * cosh t / (z * sinh t + b) ^ 2) with hG'
  have hden : ∀ t ∈ Ici (0:ℝ), 0 < z * sinh t + b := fun t ht => by
    have : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr ht
    positivity
  have hderiv : ∀ t ∈ Ici (0:ℝ), HasDerivAt G (G' t) t := by
    intro t ht
    have hd := (hden t ht).ne'
    have he : HasDerivAt (fun t => exp (-z * cosh t)) (exp (-z * cosh t) * (-z * sinh t)) t :=
      ((Real.hasDerivAt_cosh t).const_mul (-z)).exp
    have hq : HasDerivAt (fun t => z * sinh t + b) (z * cosh t) t :=
      ((Real.hasDerivAt_sinh t).const_mul z).add_const b
    have h := (he.div hq hd).neg
    convert h using 1
    simp only [hG']
    field_simp
    ring
  have hle : ∀ t ∈ Ioi (0:ℝ), G' t ≤ exp (-z * cosh t) := by
    intro t ht
    have hD := hden t (mem_Ici.mpr (le_of_lt (mem_Ioi.mp ht)))
    have hs : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr (le_of_lt (mem_Ioi.mp ht))
    have hcs : cosh t ≤ sinh t + 1 := by
      have h1 : cosh t - sinh t = exp (-t) := by
        rw [Real.cosh_eq, Real.sinh_eq]; ring
      have h2 : exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp ht])
      linarith
    have hfac : z * sinh t / (z * sinh t + b) + z * cosh t / (z * sinh t + b) ^ 2 ≤ 1 := by
      rw [div_add_div _ _ hD.ne' (pow_ne_zero 2 hD.ne'), div_le_one (by positivity)]
      have : z * cosh t ≤ b * (z * sinh t) + b * b := by
        rw [hbb]
        have : z * sinh t ≤ b * (z * sinh t) := by
          nlinarith [mul_nonneg hz0.le hs]
        nlinarith
      nlinarith [mul_nonneg hz0.le hs, hD]
    calc G' t ≤ exp (-z * cosh t) * 1 :=
          mul_le_mul_of_nonneg_left hfac (Real.exp_pos _).le
      _ = exp (-z * cosh t) := mul_one _
  have hnn : ∀ t ∈ Ioi (0:ℝ), 0 ≤ G' t := by
    intro t ht
    have hD := hden t (mem_Ici.mpr (le_of_lt (mem_Ioi.mp ht)))
    have hs : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr (le_of_lt (mem_Ioi.mp ht))
    have := Real.cosh_pos t
    simp only [hG']
    positivity
  have hG'meas : Measurable G' := by
    simp only [hG']; fun_prop
  have hint : IntegrableOn G' (Ioi 0) := by
    refine (integrableOn_K0 hz0).mono' hG'meas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn t ht)]
    exact hle t ht
  have hlim : Tendsto G atTop (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => -z * cosh t) atTop atBot := by
      have : Tendsto cosh atTop atTop := by
        refine tendsto_atTop_mono (fun t => ?_) tendsto_id
        simp only [id]
        have := one_add_sq_div_two_le_cosh t
        nlinarith [sq_nonneg (t - 1)]
      exact this.const_mul_atTop_of_neg (by linarith)
    have he : Tendsto (fun t : ℝ => exp (-z * cosh t) / b) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp hc).div_const b
    have he' : Tendsto (fun t : ℝ => -(exp (-z * cosh t) / b)) atTop (𝓝 0) := by
      simpa using he.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' he' tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 0] with t ht
      have hD := hden t ht
      have hs : 0 ≤ sinh t := Real.sinh_nonneg_iff.mpr ht
      show -(exp (-z * cosh t) / b) ≤ -(exp (-z * cosh t) / (z * sinh t + b))
      rw [neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hb0 (by nlinarith [mul_nonneg hz0.le hs])
    · filter_upwards [eventually_ge_atTop 0] with t ht
      have hD := hden t ht
      show -(exp (-z * cosh t) / (z * sinh t + b)) ≤ 0
      have : 0 ≤ exp (-z * cosh t) / (z * sinh t + b) := div_nonneg (Real.exp_pos _).le hD.le
      linarith
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim
  have hG0 : G 0 = -(exp (-z) / b) := by simp [hG]
  rw [hG0] at hftc
  have hmono : ∫ t in Ioi (0:ℝ), G' t ≤ K0 z :=
    setIntegral_mono_on hint (integrableOn_K0 hz0) measurableSet_Ioi hle
  linarith

end CTG.BesselK

/-!
# Proposition `prop:lapse-stab` as a complete deterministic statement (A122)

Stability of the lapse estimator `K̂ = 3(ρ-1)/(g₁g₃)` under errors of the distances, with
`K₀ = K0` of the block above and `c₀ = 1/2` (`c0_bound`, `c0_eq`).  Four nodes on a line with gaps
`g₁, g₂, g₃`; true distances `r_ab = g₁`, `r_bc = g₂`, `r_cd = g₃`, `r_ac = g₁+g₂`, `r_bd = g₂+g₃`,
`r_ad = g₁+g₂+g₃`; used distances `r̃` with `|r̃/r - 1| ≤ ε ≤ 1/4`; the cross-ratio
`ρ = ((Z_ad Z_bc)/(Z_ac Z_bd))²` with `Z_xy = x_xy / K₀(m̄ r_xy)` from positive correlators `x_xy`.

The arithmetic of the last step (`stab_rho`, `stab_term1`, `stab_term2`, `stab_final`,
`stab_from_log`) is a verbatim re-proof of the lemmas `TimeAppendix.stab_*` of the seventh Lean
file `lean/CorrelationsToGeometryReal3b.lean`, which cannot be imported here.
-/

namespace CTG.BesselK.LapseStab

/-! ### The arithmetic of the last step (re-proved from the seventh file) -/

theorem stab_rho (ρ x lam : ℝ) (hρ : 0 < ρ) (hx : |x| ≤ lam) (hl : lam ≤ 1) :
    |ρ * Real.exp x - ρ| ≤ 2 * ρ * lam := by
  have h1 : |Real.exp x - 1| ≤ 2 * |x| := Real.abs_exp_sub_one_le (le_trans hx hl)
  have e : ρ * Real.exp x - ρ = ρ * (Real.exp x - 1) := by ring
  rw [e, abs_mul, abs_of_pos hρ]
  have h2 : ρ * |Real.exp x - 1| ≤ ρ * (2 * |x|) := mul_le_mul_of_nonneg_left h1 hρ.le
  have h3 : ρ * (2 * |x|) ≤ ρ * (2 * lam) :=
    mul_le_mul_of_nonneg_left (by linarith) hρ.le
  linarith

theorem stab_term1 (D g th ell A : ℝ) (hell : 0 < ell) (hg : ell ^ 2 / 4 ≤ g)
    (hth : 1 / 4 ≤ 1 + th) (hA : 0 ≤ A) (hD : |D| ≤ A) :
    |3 * D / (g * (1 + th))| ≤ 48 * A / ell ^ 2 := by
  have hl2 : 0 < ell ^ 2 := by positivity
  have hg0 : 0 < g := by linarith
  have hth0 : 0 < 1 + th := by linarith
  have hden : ell ^ 2 / 16 ≤ g * (1 + th) := by nlinarith
  have hden0 : 0 < g * (1 + th) := mul_pos hg0 hth0
  rw [abs_div, abs_of_pos hden0, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  rw [div_le_div_iff₀ hden0 hl2]
  have h1 : 3 * |D| ≤ 3 * A := by linarith
  have h2 : 3 * |D| * ell ^ 2 ≤ 3 * A * ell ^ 2 := mul_le_mul_of_nonneg_right h1 hl2.le
  have h3 : 3 * A * ell ^ 2 ≤ 48 * A * (g * (1 + th)) := by nlinarith
  linarith

theorem stab_term2 (Kh th eps : ℝ) (heps : 0 ≤ eps) (hth : |th| ≤ 3 * eps)
    (hth' : 1 / 4 ≤ 1 + th) :
    |Kh * (1 / (1 + th) - 1)| ≤ 12 * eps * |Kh| := by
  have hth0 : 0 < 1 + th := by linarith
  have e : 1 / (1 + th) - 1 = -th / (1 + th) := by field_simp; ring
  rw [e, abs_mul, abs_div, abs_neg, abs_of_pos hth0]
  have h1 : |th| / (1 + th) ≤ 12 * eps := by
    rw [div_le_iff₀ hth0]; nlinarith [abs_nonneg th]
  have := mul_le_mul_of_nonneg_left h1 (abs_nonneg Kh)
  linarith

theorem stab_final (ρ ρt g th ell lam eps : ℝ) (hell : 0 < ell) (hρ : 0 < ρ) (hlam : 0 ≤ lam)
    (hg : ell ^ 2 / 4 ≤ g) (heps : 0 ≤ eps) (heps' : eps ≤ 1 / 4) (hth : |th| ≤ 3 * eps)
    (hρt : |ρt - ρ| ≤ 2 * ρ * lam) :
    |3 * (ρt - 1) / (g * (1 + th)) - 3 * (ρ - 1) / g|
      ≤ 96 * ρ * lam / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| := by
  have hth' : 1 / 4 ≤ 1 + th := by
    have := abs_le.mp hth; linarith [this.1]
  have hg0 : 0 < g := by nlinarith [sq_nonneg ell, pow_pos hell 2]
  have hth0 : 0 < 1 + th := by linarith
  have e : 3 * (ρt - 1) / (g * (1 + th)) - 3 * (ρ - 1) / g
      = 3 * (ρt - ρ) / (g * (1 + th)) + (3 * (ρ - 1) / g) * (1 / (1 + th) - 1) := by
    field_simp; ring
  rw [e]
  have hA : 0 ≤ 2 * ρ * lam := by positivity
  have t1 := stab_term1 (ρt - ρ) g th ell (2 * ρ * lam) hell hg hth' hA hρt
  have t2 := stab_term2 (3 * (ρ - 1) / g) th eps heps hth hth'
  have e2 : 48 * (2 * ρ * lam) / ell ^ 2 = 96 * ρ * lam / ell ^ 2 := by ring
  calc |3 * (ρt - ρ) / (g * (1 + th)) + (3 * (ρ - 1) / g) * (1 / (1 + th) - 1)|
      ≤ |3 * (ρt - ρ) / (g * (1 + th))| + |(3 * (ρ - 1) / g) * (1 / (1 + th) - 1)| :=
        abs_add_le _ _
    _ ≤ 48 * (2 * ρ * lam) / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| := add_le_add t1 t2
    _ = 96 * ρ * lam / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| := by rw [e2]

theorem stab_from_log (ρ x g th ell lam eps : ℝ) (hell : 0 < ell) (hρ : 0 < ρ)
    (hx : |x| ≤ lam) (hl : lam ≤ 1) (hg : ell ^ 2 / 4 ≤ g) (heps : 0 ≤ eps)
    (heps' : eps ≤ 1 / 4) (hth : |th| ≤ 3 * eps) :
    |3 * (ρ * Real.exp x - 1) / (g * (1 + th)) - 3 * (ρ - 1) / g|
      ≤ 96 * ρ * lam / ell ^ 2 + 12 * eps * |3 * (ρ - 1) / g| :=
  stab_final ρ (ρ * Real.exp x) g th ell lam eps hell hρ (le_trans (abs_nonneg x) hx) hg heps
    heps' hth (stab_rho ρ x lam hρ hx hl)

/-! ### The analytic step: `log K₀(z) + z` is `c₀`-Lipschitz in `log z` -/

/-- With `G(z) = log K₀(z) + z`: `|G(z') - G(z)| ≤ c₀ |log z' - log z|`, `c₀ = 1/2`, for ALL
`z, z' > 0` (no lower bound `z ≥ 1/4` needed, by `c0_bound`). -/
theorem G_log_lipschitz {z z' : ℝ} (hz : 0 < z) (hz' : 0 < z') :
    |(log (K0 z') + z') - (log (K0 z) + z)| ≤ (1 / 2) * |log z' - log z| := by
  set H : ℝ → ℝ := fun u => log (K0 (exp u)) + exp u with hH
  have hd : ∀ u, HasDerivAt H (-(exp u) * (K1 (exp u) / K0 (exp u) - 1)) u := by
    intro u
    have h0 := (K0_pos (exp_pos u)).ne'
    have he := Real.hasDerivAt_exp u
    have hK := (hasDerivAt_K0 (exp_pos u)).comp u he
    have hl := hK.log h0
    convert hl.add he using 1
    simp only [Function.comp]
    field_simp
    ring
  have hb : ∀ u, ‖-(exp u) * (K1 (exp u) / K0 (exp u) - 1)‖ ≤ 1 / 2 := by
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (exp_pos u)]
    have := c0_bound (exp_pos u)
    have hq : 1 < K1 (exp u) / K0 (exp u) :=
      (one_lt_div (K0_pos (exp_pos u))).mpr (K0_lt_K1 (exp_pos u))
    rw [abs_of_pos (by linarith)]
    exact this.2
  have := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hd u).hasDerivWithinAt) (fun u _ => hb u) (mem_univ (log z)) (mem_univ (log z'))
  simp only [hH, Real.exp_log hz, Real.exp_log hz', Real.norm_eq_abs] at this
  exact this

theorem abs_log_le_of_ratio {t ε : ℝ} (ht : 0 < t) (h : |t - 1| ≤ ε) (hε : ε ≤ 1 / 4) :
    |log t| ≤ 4 / 3 * ε := by
  have h1 := abs_le.mp h
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) h
  rw [abs_le]
  constructor
  · have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
    rw [Real.log_inv] at hl
    have : t⁻¹ - 1 ≤ 4 / 3 * ε := by
      rw [inv_eq_one_div, div_sub_one ht.ne', div_le_iff₀ ht]
      nlinarith
    linarith
  · have := Real.log_le_sub_one_of_pos ht
    linarith

/-- One pair: `r̃ > 0` and `|G(m̄ r̃) - G(m̄ r)| ≤ c₀ · (4/3) ε = (2/3) ε`. -/
theorem pair_bound {m r rt ε : ℝ} (hm : 0 < m) (hr : 0 < r) (h : |rt / r - 1| ≤ ε)
    (hε : ε ≤ 1 / 4) :
    0 < rt ∧ |(log (K0 (m * rt)) + m * rt) - (log (K0 (m * r)) + m * r)| ≤ 2 / 3 * ε := by
  have h1 := abs_le.mp h
  have hq : 0 < rt / r := by linarith
  have hrt : 0 < rt := by
    have : rt = r * (rt / r) := by field_simp
    rw [this]; positivity
  refine ⟨hrt, ?_⟩
  have hz : 0 < m * r := mul_pos hm hr
  have hz' : 0 < m * rt := mul_pos hm hrt
  have hG := G_log_lipschitz hz hz'
  have e : log (m * rt) - log (m * r) = log (rt / r) := by
    rw [← Real.log_div hz'.ne' hz.ne']
    congr 1; field_simp
  rw [e] at hG
  have hL := abs_log_le_of_ratio hq h hε
  linarith

/-! ### Definitions of the proposition -/

/-- Normalised correlator `Z = x / K₀(m̄ r)`. -/
noncomputable def normCorr (m x r : ℝ) : ℝ := x / K0 (m * r)

/-- Cross-ratio `ρ = ((Z_ad Z_bc)/(Z_ac Z_bd))²` built from four correlators and four distances. -/
noncomputable def crossRatio (m xad xbc xac xbd rad rbc rac rbd : ℝ) : ℝ :=
  (normCorr m xad rad * normCorr m xbc rbc / (normCorr m xac rac * normCorr m xbd rbd)) ^ 2

/-- `Δ̃ = r̃_ad + r̃_bc - r̃_ac - r̃_bd`. -/
def deltaT (rad rbc rac rbd : ℝ) : ℝ := rad + rbc - rac - rbd

theorem normCorr_eq {m x r : ℝ} (hm : 0 < m) (hx : 0 < x) (hr : 0 < r) :
    normCorr m x r = exp (log x - log (K0 (m * r))) := by
  rw [Real.exp_sub, Real.exp_log hx, Real.exp_log (K0_pos (mul_pos hm hr)), normCorr]

theorem crossRatio_eq {m xad xbc xac xbd rad rbc rac rbd : ℝ} (hm : 0 < m)
    (h1 : 0 < xad) (h2 : 0 < xbc) (h3 : 0 < xac) (h4 : 0 < xbd)
    (r1 : 0 < rad) (r2 : 0 < rbc) (r3 : 0 < rac) (r4 : 0 < rbd) :
    crossRatio m xad xbc xac xbd rad rbc rac rbd =
      exp (2 * ((log xad - log (K0 (m * rad))) + (log xbc - log (K0 (m * rbc)))
        - (log xac - log (K0 (m * rac))) - (log xbd - log (K0 (m * rbd))))) := by
  unfold crossRatio
  rw [normCorr_eq hm h1 r1, normCorr_eq hm h2 r2, normCorr_eq hm h3 r3, normCorr_eq hm h4 r4,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub, sq, ← Real.exp_add]
  congr 1; ring

theorem crossRatio_pos {m xad xbc xac xbd rad rbc rac rbd : ℝ} (hm : 0 < m)
    (h1 : 0 < xad) (h2 : 0 < xbc) (h3 : 0 < xac) (h4 : 0 < xbd)
    (r1 : 0 < rad) (r2 : 0 < rbc) (r3 : 0 < rac) (r4 : 0 < rbd) :
    0 < crossRatio m xad xbc xac xbd rad rbc rac rbd := by
  rw [crossRatio_eq hm h1 h2 h3 h4 r1 r2 r3 r4]; exact exp_pos _

/-! ### Step (2): the perturbation of the logarithm of the cross-ratio -/

/-- **Perturbation bound, sharp form.** True distances with `r_ad + r_bc - r_ac - r_bd = 0` (points
on a line), used distances with relative error `≤ ε ≤ 1/4`, the same positive correlators:
`|log ρ̃ - log ρ| ≤ (32/3) c₀ ε + 2 m̄ |Δ̃|` with `c₀ = 1/2`, i.e. `(16/3) ε + 2 m̄ |Δ̃|`. -/
theorem log_crossRatio_perturb_sharp {m ε xad xbc xac xbd rad rbc rac rbd
    rtad rtbc rtac rtbd : ℝ} (hm : 0 < m) (hε : ε ≤ 1 / 4)
    (h1 : 0 < xad) (h2 : 0 < xbc) (h3 : 0 < xac) (h4 : 0 < xbd)
    (r1 : 0 < rad) (r2 : 0 < rbc) (r3 : 0 < rac) (r4 : 0 < rbd)
    (hline : rad + rbc - rac - rbd = 0)
    (e1 : |rtad / rad - 1| ≤ ε) (e2 : |rtbc / rbc - 1| ≤ ε) (e3 : |rtac / rac - 1| ≤ ε)
    (e4 : |rtbd / rbd - 1| ≤ ε) :
    |log (crossRatio m xad xbc xac xbd rtad rtbc rtac rtbd)
        - log (crossRatio m xad xbc xac xbd rad rbc rac rbd)|
      ≤ 32 / 3 * (1 / 2) * ε + 2 * m * |deltaT rtad rtbc rtac rtbd| := by
  obtain ⟨t1, b1⟩ := pair_bound hm r1 e1 hε
  obtain ⟨t2, b2⟩ := pair_bound hm r2 e2 hε
  obtain ⟨t3, b3⟩ := pair_bound hm r3 e3 hε
  obtain ⟨t4, b4⟩ := pair_bound hm r4 e4 hε
  rw [crossRatio_eq hm h1 h2 h3 h4 t1 t2 t3 t4, crossRatio_eq hm h1 h2 h3 h4 r1 r2 r3 r4,
    Real.log_exp, Real.log_exp]
  set D := deltaT rtad rtbc rtac rtbd with hD
  have e : 2 * ((log xad - log (K0 (m * rtad))) + (log xbc - log (K0 (m * rtbc)))
        - (log xac - log (K0 (m * rtac))) - (log xbd - log (K0 (m * rtbd))))
      - 2 * ((log xad - log (K0 (m * rad))) + (log xbc - log (K0 (m * rbc)))
        - (log xac - log (K0 (m * rac))) - (log xbd - log (K0 (m * rbd))))
      = 2 * (-((log (K0 (m * rtad)) + m * rtad) - (log (K0 (m * rad)) + m * rad))
          - ((log (K0 (m * rtbc)) + m * rtbc) - (log (K0 (m * rbc)) + m * rbc))
          + ((log (K0 (m * rtac)) + m * rtac) - (log (K0 (m * rac)) + m * rac))
          + ((log (K0 (m * rtbd)) + m * rtbd) - (log (K0 (m * rbd)) + m * rbd)))
        + 2 * m * D := by
    rw [hD, deltaT]; linear_combination (-2 * m) * hline
  rw [e]
  have q1 := abs_le.mp b1
  have q2 := abs_le.mp b2
  have q3 := abs_le.mp b3
  have q4 := abs_le.mp b4
  have m1 : m * D ≤ m * |D| := mul_le_mul_of_nonneg_left (le_abs_self _) hm.le
  have m2 : -(m * |D|) ≤ m * D := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le D) hm.le; linarith
  rw [abs_le]; constructor <;> linarith

/-- **Perturbation bound in the form of the paper**: `λ = 16 c₀ ε + 2 m̄ |Δ̃|`, `c₀ = 1/2`. -/
theorem log_crossRatio_perturb {m ε xad xbc xac xbd rad rbc rac rbd
    rtad rtbc rtac rtbd : ℝ} (hm : 0 < m) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (h1 : 0 < xad) (h2 : 0 < xbc) (h3 : 0 < xac) (h4 : 0 < xbd)
    (r1 : 0 < rad) (r2 : 0 < rbc) (r3 : 0 < rac) (r4 : 0 < rbd)
    (hline : rad + rbc - rac - rbd = 0)
    (e1 : |rtad / rad - 1| ≤ ε) (e2 : |rtbc / rbc - 1| ≤ ε) (e3 : |rtac / rac - 1| ≤ ε)
    (e4 : |rtbd / rbd - 1| ≤ ε) :
    |log (crossRatio m xad xbc xac xbd rtad rtbc rtac rtbd)
        - log (crossRatio m xad xbc xac xbd rad rbc rac rbd)|
      ≤ 16 * (1 / 2) * ε + 2 * m * |deltaT rtad rtbc rtac rtbd| := by
  have := log_crossRatio_perturb_sharp hm hε h1 h2 h3 h4 r1 r2 r3 r4 hline e1 e2 e3 e4
  linarith

/-- `|Δ̃| ≤ 16 ℓ ε` for four nodes on a line with gaps `≤ 2ℓ`. -/
theorem deltaT_le {ℓ ε g1 g2 g3 rtad rtbc rtac rtbd : ℝ}
    (hg1 : 0 < g1) (hg2 : 0 < g2) (hg3 : 0 < g3)
    (u1 : g1 ≤ 2 * ℓ) (u2 : g2 ≤ 2 * ℓ) (u3 : g3 ≤ 2 * ℓ)
    (e1 : |rtad / (g1 + g2 + g3) - 1| ≤ ε) (e2 : |rtbc / g2 - 1| ≤ ε)
    (e3 : |rtac / (g1 + g2) - 1| ≤ ε) (e4 : |rtbd / (g2 + g3) - 1| ≤ ε) :
    |deltaT rtad rtbc rtac rtbd| ≤ 16 * ℓ * ε := by
  have abs_err : ∀ r rt : ℝ, 0 < r → |rt / r - 1| ≤ ε → |rt - r| ≤ ε * r := by
    intro r rt hr h
    have : rt - r = r * (rt / r - 1) := by field_simp
    rw [this, abs_mul, abs_of_pos hr]; nlinarith [abs_nonneg (rt / r - 1)]
  have a1 := abs_le.mp (abs_err _ _ (by positivity) e1)
  have a2 := abs_le.mp (abs_err _ _ hg2 e2)
  have a3 := abs_le.mp (abs_err _ _ (by positivity) e3)
  have a4 := abs_le.mp (abs_err _ _ (by positivity) e4)
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) e2
  have hb : ε * (2 * g1 + 4 * g2 + 2 * g3) ≤ 16 * ℓ * ε := by nlinarith
  rw [deltaT, abs_le]; constructor <;> nlinarith

/-- `Δ̃ = 0` for additive used distances. -/
theorem deltaT_additive {rtab rtbc rtcd : ℝ} :
    deltaT (rtab + rtbc + rtcd) rtbc (rtab + rtbc) (rtbc + rtcd) = 0 := by
  rw [deltaT]; ring

/-- `Δ̃ = 0` for used distances `r̃_xy = r_xy + c_x + c_y` (true distances on a line). -/
theorem deltaT_shift {g1 g2 g3 ca cb cc cd : ℝ} :
    deltaT (g1 + g2 + g3 + ca + cd) (g2 + cb + cc) (g1 + g2 + ca + cc) (g2 + g3 + cb + cd) = 0 := by
  rw [deltaT]; ring

/-! ### Step (3): Proposition `prop:lapse-stab` -/

/-- **Proposition `prop:lapse-stab`** (complete, deterministic; `K₀ = K0`, `c₀ = 1/2`).
Nodes on a line with gaps `g₁, g₂, g₃ ∈ [ℓ/2, 2ℓ]`; positive correlators; used distances with
relative errors `≤ ε ≤ 1/4`; `λ = 16 c₀ ε + 2 m̄ |Δ̃| ≤ 1`.  Then
`|K̃ - K̂| ≤ 96 ρ λ / ℓ² + 12 ε |K̂|` with `K̂ = 3(ρ-1)/(g₁g₃)`, `K̃ = 3(ρ̃-1)/(r̃_ab r̃_cd)`.
The hypothesis `m̄ ℓ ≥ 1` of the paper is not needed. -/
theorem lapse_stab {m ℓ ε g1 g2 g3 xad xbc xac xbd rtab rtbc rtcd rtac rtbd rtad : ℝ}
    (hm : 0 < m) (hℓ : 0 < ℓ)
    (l1 : ℓ / 2 ≤ g1) (l2 : ℓ / 2 ≤ g2) (l3 : ℓ / 2 ≤ g3)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (h1 : 0 < xad) (h2 : 0 < xbc) (h3 : 0 < xac) (h4 : 0 < xbd)
    (eab : |rtab / g1 - 1| ≤ ε) (ecd : |rtcd / g3 - 1| ≤ ε)
    (ead : |rtad / (g1 + g2 + g3) - 1| ≤ ε) (ebc : |rtbc / g2 - 1| ≤ ε)
    (eac : |rtac / (g1 + g2) - 1| ≤ ε) (ebd : |rtbd / (g2 + g3) - 1| ≤ ε)
    (hlam : 16 * (1 / 2) * ε + 2 * m * |deltaT rtad rtbc rtac rtbd| ≤ 1) :
    |3 * (crossRatio m xad xbc xac xbd rtad rtbc rtac rtbd - 1) / (rtab * rtcd)
        - 3 * (crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) - 1) / (g1 * g3)|
      ≤ 96 * crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3)
          * (16 * (1 / 2) * ε + 2 * m * |deltaT rtad rtbc rtac rtbd|) / ℓ ^ 2
        + 12 * ε * |3 * (crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) - 1)
            / (g1 * g3)| := by
  have hg1 : 0 < g1 := by linarith
  have hg2 : 0 < g2 := by linarith
  have hg3 : 0 < g3 := by linarith
  set ρ := crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) with hρdef
  set ρt := crossRatio m xad xbc xac xbd rtad rtbc rtac rtbd with hρtdef
  set lam := 16 * (1 / 2) * ε + 2 * m * |deltaT rtad rtbc rtac rtbd| with hlamdef
  have hρ : 0 < ρ := crossRatio_pos hm h1 h2 h3 h4 (by positivity) hg2 (by positivity)
    (by positivity)
  have hlog := log_crossRatio_perturb (rad := g1 + g2 + g3) (rbc := g2) (rac := g1 + g2)
    (rbd := g2 + g3) hm hε0 hε h1 h2 h3 h4 (by positivity) hg2 (by positivity) (by positivity)
    (by ring) ead ebc eac ebd
  obtain ⟨tad, -⟩ := pair_bound hm (by positivity : (0:ℝ) < g1 + g2 + g3) ead hε
  obtain ⟨tbc, -⟩ := pair_bound hm hg2 ebc hε
  obtain ⟨tac, -⟩ := pair_bound hm (by positivity : (0:ℝ) < g1 + g2) eac hε
  obtain ⟨tbd, -⟩ := pair_bound hm (by positivity : (0:ℝ) < g2 + g3) ebd hε
  have hρt : 0 < ρt := crossRatio_pos hm h1 h2 h3 h4 tad tbc tac tbd
  set x := log ρt - log ρ with hx
  have hρtx : ρt = ρ * exp x := by
    rw [hx, Real.exp_sub, Real.exp_log hρt, Real.exp_log hρ]; field_simp
  set th := (rtab / g1) * (rtcd / g3) - 1 with hth
  have hprod : rtab * rtcd = g1 * g3 * (1 + th) := by rw [hth]; field_simp; ring
  have hthb : |th| ≤ 3 * ε := by
    have a := abs_le.mp eab
    have b := abs_le.mp ecd
    have e : th = (rtab / g1 - 1) * (rtcd / g3 - 1) + (rtab / g1 - 1) + (rtcd / g3 - 1) := by
      rw [hth]; ring
    rw [e, abs_le]; constructor <;> nlinarith
  have hg : ℓ ^ 2 / 4 ≤ g1 * g3 := by nlinarith
  rw [hprod, hρtx]
  exact stab_from_log ρ x (g1 * g3) th ℓ lam ε hℓ hρ hlog hlam hg hε0 hε hthb

/-- Corollary: additive used distances, `λ = 16 c₀ ε` (`= 8 ε`). -/
theorem lapse_stab_additive {m ℓ ε g1 g2 g3 xad xbc xac xbd rtab rtbc rtcd : ℝ}
    (hm : 0 < m) (hℓ : 0 < ℓ)
    (l1 : ℓ / 2 ≤ g1) (l2 : ℓ / 2 ≤ g2) (l3 : ℓ / 2 ≤ g3)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8)
    (h1 : 0 < xad) (h2 : 0 < xbc) (h3 : 0 < xac) (h4 : 0 < xbd)
    (eab : |rtab / g1 - 1| ≤ ε) (ecd : |rtcd / g3 - 1| ≤ ε)
    (ead : |(rtab + rtbc + rtcd) / (g1 + g2 + g3) - 1| ≤ ε) (ebc : |rtbc / g2 - 1| ≤ ε)
    (eac : |(rtab + rtbc) / (g1 + g2) - 1| ≤ ε) (ebd : |(rtbc + rtcd) / (g2 + g3) - 1| ≤ ε) :
    |3 * (crossRatio m xad xbc xac xbd (rtab + rtbc + rtcd) rtbc (rtab + rtbc) (rtbc + rtcd) - 1)
          / (rtab * rtcd)
        - 3 * (crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) - 1) / (g1 * g3)|
      ≤ 96 * crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3)
          * (16 * (1 / 2) * ε) / ℓ ^ 2
        + 12 * ε * |3 * (crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) - 1)
            / (g1 * g3)| := by
  have h := lapse_stab hm hℓ l1 l2 l3 hε0 (by linarith) h1 h2 h3 h4 eab ecd ead ebc eac ebd
    (by rw [deltaT_additive]; simp; linarith)
  rw [deltaT_additive] at h
  simpa using h

/-- Corollary: general used distances, `λ ≤ 16 c₀ ε + 32 m̄ ℓ ε`. -/
theorem lapse_stab_general {m ℓ ε g1 g2 g3 xad xbc xac xbd rtab rtbc rtcd rtac rtbd rtad : ℝ}
    (hm : 0 < m) (hℓ : 0 < ℓ)
    (l1 : ℓ / 2 ≤ g1) (l2 : ℓ / 2 ≤ g2) (l3 : ℓ / 2 ≤ g3)
    (u1 : g1 ≤ 2 * ℓ) (u2 : g2 ≤ 2 * ℓ) (u3 : g3 ≤ 2 * ℓ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (h1 : 0 < xad) (h2 : 0 < xbc) (h3 : 0 < xac) (h4 : 0 < xbd)
    (eab : |rtab / g1 - 1| ≤ ε) (ecd : |rtcd / g3 - 1| ≤ ε)
    (ead : |rtad / (g1 + g2 + g3) - 1| ≤ ε) (ebc : |rtbc / g2 - 1| ≤ ε)
    (eac : |rtac / (g1 + g2) - 1| ≤ ε) (ebd : |rtbd / (g2 + g3) - 1| ≤ ε)
    (hlam : 16 * (1 / 2) * ε + 32 * m * ℓ * ε ≤ 1) :
    |3 * (crossRatio m xad xbc xac xbd rtad rtbc rtac rtbd - 1) / (rtab * rtcd)
        - 3 * (crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) - 1) / (g1 * g3)|
      ≤ 96 * crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3)
          * (16 * (1 / 2) * ε + 32 * m * ℓ * ε) / ℓ ^ 2
        + 12 * ε * |3 * (crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) - 1)
            / (g1 * g3)| := by
  have hg1 : 0 < g1 := by linarith
  have hg2 : 0 < g2 := by linarith
  have hg3 : 0 < g3 := by linarith
  have hD := deltaT_le hg1 hg2 hg3 u1 u2 u3 ead ebc eac ebd
  have hmD : 2 * m * |deltaT rtad rtbc rtac rtbd| ≤ 32 * m * ℓ * ε := by
    have := mul_le_mul_of_nonneg_left hD (by positivity : (0:ℝ) ≤ 2 * m); linarith
  have h := lapse_stab hm hℓ l1 l2 l3 hε0 hε h1 h2 h3 h4 eab ecd ead ebc eac ebd (by linarith)
  have hρ : 0 < crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3) :=
    crossRatio_pos hm h1 h2 h3 h4 (by positivity) hg2 (by positivity) (by positivity)
  have hmono : 96 * crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3)
        * (16 * (1 / 2) * ε + 2 * m * |deltaT rtad rtbc rtac rtbd|) / ℓ ^ 2
      ≤ 96 * crossRatio m xad xbc xac xbd (g1 + g2 + g3) g2 (g1 + g2) (g2 + g3)
        * (16 * (1 / 2) * ε + 32 * m * ℓ * ε) / ℓ ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

end CTG.BesselK.LapseStab
