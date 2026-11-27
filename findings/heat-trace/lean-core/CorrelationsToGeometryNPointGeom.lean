/-
From Correlations to Geometry -- fifteenth Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the twelfth file `CorrelationsToGeometryNPoint.lean` and the fourteenth
`CorrelationsToGeometryVolume.lean` and combines them: Steps 2 to 5 of the proof of Proposition "dotLN-diff"
(Appendix H of the paper) for independent sample points on a compact connected Riemannian manifold modelled on
`Fin n → ℝ`, with a time-dependent metric, WITHOUT the geometric hypotheses of the twelfth file.  The volume growth
of balls at the two times and the lower bound for the population normalisation are derived from one assumption on
the sampling law `m`:  `m₀ μ ≤ m ≤ m₁ μ` with `μ` the n-dimensional Hausdorff measure of the Riemannian distance
(that `μ` is the Riemannian volume up to a constant is NOT proven).  Two smallness conditions remain explicit
hypotheses; the constants `A_m, r₀, c_q, ξ₀` are existential (compactness); the error is `err5` of the twelfth
file, not the form `C δ'/ξ` of the paper; the test function is only bounded; Step 6 is not formalised.
Check with `cd lean && ./check_npoint_geom.sh` (against the COMPILED twelfth and fourteenth files).
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryNPoint
import CorrelationsToGeometryVolume

/-!
# Steps 2–5 of `prop:dotLN-diff` with the geometric hypotheses discharged (block A125)

Scratch file of the project "From Correlations to Geometry" (not part of `lean/`).

Combines the twelfth file (`CTG.NPoint.npoint_step2`, `CTG.NPoint.npoint_step5`) with the fourteenth
file (`CTG.ManifoldVolume.sampling_upper_growth_time`, `sampling_normalisation_lower`).  The upper
volume-growth HYPOTHESES at the two times and the lower bound of the population normalisations are
derived for a compact connected Riemannian manifold modelled on `Fin n → ℝ` (sup norm, no boundary),
a `TimeMetric` whose metric is continuous in the base point at the time `a`, and a sampling law `m`
with `m₀ μH[n] ≤ m ≤ m₁ μH[n]`, `μH[n]` the `n`-dimensional Hausdorff measure of the Riemannian
distance (NOT identified with the Riemannian volume).  The smallness conditions stay explicit.
No `sorry`, no `axiom`, no `native_decide`.
-/

open Set MeasureTheory ProbabilityTheory Bundle Manifold Filter Metric
open scoped Manifold ENNReal Topology NNReal
open CTG.ManifoldDistance CTG.NPoint CTG.ManifoldVolume

noncomputable section

namespace CTG.NPointGeom

universe u

variable {n : ℕ} {M : Type*} [EMetricSpace M] [ChartedSpace (Fin n → ℝ) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M]
  [IsContinuousRiemannianBundle (Fin n → ℝ) (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsRiemannianManifold 𝓘(ℝ, Fin n → ℝ) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [PreconnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Real form of the comparison of the distances at two times: `d_a ≤ e^{κ|b−a|} d_b`. -/
theorem dist_le_exp_dist {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (x y : M) : G.dist x y a ≤ Real.exp (G.κ * |b - a|) * G.dist x y b := by
  have h := G.riemannianEDist_le hb ha x y
  have hfb := G.riemannianEDist_ne_top ha hb hcont x y
  rw [abs_sub_comm] at h
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfb) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h2
  exact h2

/-- **(1) Upper growth at both times.**  With `A, r₁` from `sampling_upper_growth_time` at the time
`a`: `A_m = A e^{nκ|b−a|}`, `r₀ = r₁ e^{−κ|b−a|}` (the ball of `d_b` of radius `r` lies in the ball
of `d_a` of radius `e^{κ|b−a|} r`). -/
theorem growth_two_times {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (m : Measure M) (m₁ : ℝ) (hm₁ : 0 ≤ m₁) (hm : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ),
      (∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ n)) ∧
      (∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ n)) := by
  obtain ⟨A, hA, r₁, hr₁, h⟩ := sampling_upper_growth_time G ha hcont m m₁ hm₁ hm
  set E := Real.exp (G.κ * |b - a|) with hEdef
  have hE : 1 ≤ E := Real.one_le_exp (mul_nonneg G.κ_nonneg (abs_nonneg _))
  have hE0 : 0 < E := by linarith
  refine ⟨A * E ^ n, by positivity, r₁ / E, by positivity, fun x r hr hrr => ?_,
    fun x r hr hrr => ?_⟩
  · have hr1 : r ≤ r₁ := hrr.trans (div_le_self hr₁.le hE)
    refine (h x r hr hr1).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : 1 ≤ E ^ n := one_le_pow₀ hE
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hA (pow_pos hr n).le)
    linarith
  · have hEr : E * r ≤ r₁ := by rwa [le_div_iff₀ hE0, mul_comm] at hrr
    have hsub : {y | G.dist x y b < r} ⊆ {y | G.dist x y a < E * r} := by
      intro y hy
      have h3 := dist_le_exp_dist G ha hb hcont x y
      simp only [mem_setOf_eq] at hy ⊢
      calc G.dist x y a ≤ E * G.dist x y b := h3
        _ < E * r := mul_lt_mul_of_pos_left hy hE0
    refine (measure_mono hsub).trans ((h x (E * r) (by positivity) hEr).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
    ring

/-- Lower bound of the population normalisation at one time `τ`, from a comparison
`d_τ ≤ C · edist` and the lower integral bound of `sampling_normalisation_lower`. -/
theorem popNorm_lower_one {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a τ : ℝ}
    (ha : a ∈ s) (hτ : τ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (m : Measure M) [IsFiniteMeasure m] (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hle : ∀ x y : M, (letI := G.norms τ; Manifold.riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y)
      ≤ C * edist x y)
    (K : ℝ) (hK : C.toReal ≤ K) (hK0 : 0 < K) (m₀ a' r₀ : ℝ)
    (hlow : ∀ (h : ℝ → ℝ) (h₀ : ℝ), 0 ≤ h₀ →
      (∀ t, 0 ≤ t → t ≤ 1 → h₀ ≤ h t) → ∀ x : M, ∀ ξ, 0 < ξ → ξ ≤ r₀ →
        ENNReal.ofReal (h₀ * m₀ * a' * ξ ^ n)
          ≤ ∫⁻ y, ENNReal.ofReal (h ((edist x y).toReal / ξ)) ∂m)
    (h : ℝ → ℝ) (hhc : Continuous h) (A : ℝ) (hA : 0 ≤ A)
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (h₀ s₀ : ℝ) (hh₀ : 0 ≤ h₀) (hs₀ : 0 < s₀) (hlo : ∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t)
    (ξ : ℝ) (hξ : 0 < ξ) (hξr : s₀ * ξ / K ≤ r₀) (x : M) :
    h₀ * m₀ * a' * (s₀ * ξ / K) ^ n ≤ popNorm G h ξ τ m x := by
  set ξ' := s₀ * ξ / K with hξ'
  have hξ'0 : 0 < ξ' := by positivity
  set hb : ℝ → ℝ := fun t => if t ≤ 1 then h₀ else 0 with hbdef
  have H := hlow hb h₀ hh₀ (fun t _ ht => by simp [hbdef, ht]) x ξ' hξ'0 hξr
  have hmeas : Measurable fun y => kern G h ξ τ x y :=
    (kern_measurable G ha hτ hcont h hhc ξ).comp (measurable_const.prodMk measurable_id)
  have hint : Integrable (fun y => kern G h ξ τ x y) m :=
    bdd_integrable m _ hmeas A (kern_abs_le G h A ξ τ hξ hh hA x)
  have hpt : ∀ y, ENNReal.ofReal (hb ((edist x y).toReal / ξ'))
      ≤ ENNReal.ofReal (kern G h ξ τ x y) := by
    intro y
    by_cases hy : (edist x y).toReal / ξ' ≤ 1
    · simp only [hbdef, hy, if_true]
      apply ENNReal.ofReal_le_ofReal
      have hfin := CTG.ManifoldDistance.edist_ne_top_of_preconnected x y
      have hd : G.dist x y τ ≤ C.toReal * (edist x y).toReal := by
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top hC hfin) (hle x y)
        rw [ENNReal.toReal_mul] at this
        exact this
      have he : (edist x y).toReal ≤ ξ' := by rwa [div_le_one hξ'0] at hy
      have hd2 : G.dist x y τ ≤ s₀ * ξ := by
        calc G.dist x y τ ≤ C.toReal * (edist x y).toReal := hd
          _ ≤ K * ξ' := mul_le_mul hK he ENNReal.toReal_nonneg hK0.le
          _ = s₀ * ξ := by rw [hξ']; field_simp [hK0.ne']
      apply hlo
      · exact div_nonneg (G.dist_nonneg x y τ) hξ.le
      · rw [div_le_iff₀ hξ]; exact hd2
    · simp only [hbdef, hy, if_false, ENNReal.ofReal_zero]
      exact zero_le _
  have H2 := H.trans (lintegral_mono hpt)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => hh0 _)] at H2
  have hnn : 0 ≤ ∫ y, kern G h ξ τ x y ∂m := integral_nonneg fun y => hh0 _
  rw [ENNReal.ofReal_le_ofReal_iff hnn] at H2
  exact H2

/-- **(2) Lower bound of the population normalisations at both times.**  For every `s₀ > 0` there
are `c_q > 0`, `ξ₀ > 0` (depending on `G`, `a`, `b`, `m₀`, `s₀` and the manifold, NOT on the profile)
such that for every continuous profile `h ≥ 0` with `|h(t)| ≤ A e^{−t}` and `h ≥ h₀` on `[0, s₀]`, all
`0 < ξ ≤ ξ₀` and all `x`: `c_q h₀ ξⁿ ≤ q^a(x)` and `c_q h₀ ξⁿ ≤ q^b(x)` (Bochner integrals).
Explicitly `c_q = m₀ a' (s₀/K)ⁿ`, `ξ₀ = r₀ K/s₀`, with `a', r₀` from `hausdorff_ball_uniform` and
`K ≥ 1` a common bound for the constants of `TimeMetric.redist_le_edist` at the times `a`, `b`. -/
theorem popNorm_lower_two_times {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (m : Measure M) [IsFiniteMeasure m] (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hm : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ∀ (h : ℝ → ℝ) (A h₀ : ℝ), Continuous h → 0 ≤ A →
      (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ h t) → 0 ≤ h₀ →
      (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) → ∀ ξ, 0 < ξ → ξ ≤ ξ₀ → ∀ x : M,
        cq * h₀ * ξ ^ n ≤ popNorm G h ξ a m x ∧ cq * h₀ * ξ ^ n ≤ popNorm G h ξ b m x := by
  obtain ⟨a', ha', r₀, hr₀, hlow⟩ := sampling_normalisation_lower m m₀ hm₀.le hm
  obtain ⟨Ca, hCa, hlea⟩ := G.redist_le_edist ha ha hcont
  obtain ⟨Cb, hCb, hleb⟩ := G.redist_le_edist ha hb hcont
  set K := max (max Ca.toReal Cb.toReal) 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  have hKa : Ca.toReal ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKb : Cb.toReal ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨m₀ * a' * (s₀ / K) ^ n, by positivity, r₀ * K / s₀, by positivity,
    fun h A h₀ hhc hA hh hh0 hh₀ hlo ξ hξ hξ₀ x => ?_⟩
  have hξr : s₀ * ξ / K ≤ r₀ := by
    rw [div_le_iff₀ hK0]
    rw [le_div_iff₀ hs₀] at hξ₀
    linarith
  have e : m₀ * a' * (s₀ / K) ^ n * h₀ * ξ ^ n = h₀ * m₀ * a' * (s₀ * ξ / K) ^ n := by
    rw [div_pow, div_pow, mul_pow]; ring
  rw [e]
  exact ⟨popNorm_lower_one G ha ha hcont m Ca hCa hlea K hKa hK0 m₀ a' r₀ hlow h hhc A hA hh hh0
      h₀ s₀ hh₀ hs₀ hlo ξ hξ hξr x,
    popNorm_lower_one G ha hb hcont m Cb hCb hleb K hKb hK0 m₀ a' r₀ hlow h hhc A hA hh hh0
      h₀ s₀ hh₀ hs₀ hlo ξ hξ hξr x⟩

/-- **(3a) Step 2 of `prop:dotLN-diff` with the growth hypotheses discharged.**  On a compact
connected Riemannian manifold modelled on `Fin n → ℝ`, for a `TimeMetric` continuous in the base
point at time `a` and a probability law `m ≤ m₁ μH[n]`: there are `A_m ≥ 0`, `r₀ > 0` (depending only
on `G`, `a`, `b`, `m₁` and the manifold) such that for every sample, profile and `L > 0` the
conclusion of `npoint_step2` holds with `d = n`: probability `≤ 3N·2e^{−L}`. -/
theorem npoint_step2_geom {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (m₁ : ℝ) (hm₁ : 0 ≤ m₁)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ),
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 0 < N → ∀ ξ : ℝ, 0 < ξ →
      ∀ (h h' : ℝ → ℝ) (A : ℝ), 0 ≤ A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
      ∀ L : ℝ, 0 < L →
      μ.real {ω | ∃ i < N,
        dev N A (vKern n Am r₀ ξ A) L < |sampNorm G h ξ a X N i ω - popNorm G h ξ a m (X i ω)|
        ∨ dev N A (vKern n Am r₀ ξ A) L
            < |sampNorm G h ξ b X N i ω - popNorm G h ξ b m (X i ω)|
        ∨ dev N (2 * G.κ * A) (vInc G.κ n Am r₀ ξ A a b) L
            < |(sampNorm G h ξ b X N i ω - sampNorm G h ξ a X N i ω) / (b - a)
              - (popNorm G h ξ b m (X i ω) - popNorm G h ξ a m (X i ω)) / (b - a)|}
        ≤ 3 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨Am, hAm, r₀, hr₀, hga, hgb⟩ := growth_two_times G ha hb hcont m m₁ hm₁ hup
  refine ⟨Am, hAm, r₀, hr₀, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ h h' A hA hder hbd hh L hL
  exact npoint_step2 G ha hcont ha hb hab hne m X h_indep hX hlaw N hN n Am r₀ ξ hAm hr₀ hξ
    hga hgb h h' A hA hder hbd hh L hL

/-- **(3b) Steps 2–5 of `prop:dotLN-diff` with ALL geometric hypotheses discharged.**  Setting as in
`npoint_step2_geom`, in addition `m₀ μH[n] ≤ m` with `m₀ > 0`, and a number `s₀ > 0`.  There are
`A_m ≥ 0`, `r₀ > 0`, `c_q > 0`, `ξ₀ > 0` (depending only on `G`, `a`, `b`, `m₀`, `m₁`, `s₀` and the
manifold) such that for every sample of independent points with law `m`, every `N ≥ 1`,
`0 < ξ ≤ ξ₀`, every differentiable profile `h ≥ 0` with `|h|, |h'| ≤ A e^{−t}` (`A > 0`) and
`h ≥ h₀ > 0` on `[0, s₀]`, every measurable `f` with `|f| ≤ B_f`, and every `L > 0` satisfying the two
explicit smallness conditions with `c = c_q h₀ ξⁿ`, the conclusion of `npoint_step5` holds:
with probability at least `1 − 15N·2e^{−L}`, for all `i < N` the time difference quotient of the
sample walk average differs from the population one at `X_i` by at most `err5`. -/
theorem npoint_step5_geom {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁)
    (hlow : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ),
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 0 < N → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (h h' : ℝ → ℝ) (A h₀ : ℝ), 0 < A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
        (∀ t, 0 ≤ h t) → 0 < h₀ → (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) →
      ∀ (f : M → ℝ), Measurable f → ∀ Bf : ℝ, 0 ≤ Bf → (∀ x, |f x| ≤ Bf) →
      ∀ L : ℝ, 0 < L →
      dev N A (vKern n Am r₀ ξ A) L / (cq * h₀ * ξ ^ n) ≤ 1 / 2 →
      errT N A (vKern n Am r₀ ξ A) (cq * h₀ * ξ ^ n) L 1 / (cq * h₀ * ξ ^ n / A) ≤ 1 / 2 →
      μ.real {ω | ∃ i < N,
        err5 N A (vKern n Am r₀ ξ A) (2 * G.κ * A) (vInc G.κ n Am r₀ ξ A a b) (cq * h₀ * ξ ^ n) L
            (2 * Bf) (cq * h₀ * ξ ^ n / A)
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
        ≤ 15 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨Am, hAm, r₀, hr₀, hga, hgb⟩ := growth_two_times G ha hb hcont m m₁ hm₁ hup
  obtain ⟨cq, hcq, ξ₀, hξ₀, hq⟩ := popNorm_lower_two_times G ha hb hcont m m₀ hm₀ hlow s₀ hs₀
  refine ⟨Am, hAm, r₀, hr₀, cq, hcq, ξ₀, hξ₀, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Bf hBf hfb L hL hsmall hsmallD
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have hqab := hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo ξ hξ hξξ₀
  exact npoint_step5 G ha hcont ha hb hab hne m X h_indep hX hlaw N hN n Am r₀ ξ hAm hr₀ hξ
    hga hgb h h' A hA hder hbd hh hh0 f hf Bf hBf hfb (cq * h₀ * ξ ^ n) (by positivity)
    (fun y => (hqab y).1) (fun y => (hqab y).2) L hL hsmall hsmallD

end CTG.NPointGeom
