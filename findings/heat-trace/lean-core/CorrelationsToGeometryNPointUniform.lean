/-
Twentieth file: the N-point statement of `CorrelationsToGeometryNPointLip.lean` for finitely many pairs of
times with constants that do not depend on the pair, and measurability of the exceptional sets.  Namespace
`CTG.NPointUniform`; imports the nineteenth file (compiled module
`.tools/leanbuild/CorrelationsToGeometryNPointLip.olean`); check with `./check_npoint_uniform.sh`.
Window versions with a fixed reference time `a₀` (`growth_window`, `popNorm_window`, `lip_window`),
`npoint_lip_pairs` (all pairs `(a_j, b_j)`, `j < J`, in the window `κ|τ − a₀| ≤ 1` simultaneously, probability
of failure at most `J·30/N²`), `npoint_step5_lip_geom_log_set_measurable`, `npoint_lip_pairs_set_measurable`.
NOT formalised: all pairs of times in a window at once (time grid), the limit `η → 0`, Step 6.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryNPointLip

open Set MeasureTheory ProbabilityTheory
open CTG.NPoint CTG.NPointSharp CTG.NPointLip

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.NPointUniform

section Meas

variable {E : Type*} [MeasurableSpace E] {m : Measure E} [IsProbabilityMeasure m]

theorem sampAvg_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) (K : E → E → ℝ)
    (hK : Measurable fun p : E × E => K p.1 p.2) (j : ℕ) :
    Measurable fun ω => sampAvg X N K j ω := by
  unfold sampAvg
  exact measurable_const.mul (Finset.measurable_sum _ fun l _ => hK.comp ((hX j).prodMk (hX l)))

theorem sampW_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) (K g : E → E → ℝ)
    (hK : Measurable fun p : E × E => K p.1 p.2) (hg : Measurable fun p : E × E => g p.1 p.2)
    (i : ℕ) : Measurable fun ω => sampW X N K g i ω := by
  unfold sampW avgN
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    ((hK.comp ((hX i).prodMk (hX j))).mul (hg.comp ((hX i).prodMk (hX j)))).mul
      (measurable_const.div (sampAvg_meas X hX N K hK j)))

theorem popW_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (K g : E → E → ℝ)
    (hK : Measurable fun p : E × E => K p.1 p.2) (hg : Measurable fun p : E × E => g p.1 p.2)
    (i : ℕ) : Measurable fun ω => popW m K g (X i ω) :=
  (popAvg_measurable m (wKer m K g) ((hK.mul hg).mul (inv_pop_meas K hK))).comp (hX i)

theorem qDiff_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) (Ka Kb : E → E → ℝ)
    (hKa : Measurable fun p : E × E => Ka p.1 p.2) (hKb : Measurable fun p : E × E => Kb p.1 p.2)
    (f : E → ℝ) (hf : Measurable f) (η : ℝ) (i : ℕ) :
    Measurable fun ω => qDiff X N m Ka Kb f η i ω := by
  have hg : Measurable fun p : E × E => f p.2 - f p.1 :=
    (hf.comp measurable_snd).sub (hf.comp measurable_fst)
  have hg1 : Measurable fun p : E × E => (fun _ _ => (1:ℝ)) p.1 p.2 := measurable_const
  unfold qDiff
  exact ((((sampW_meas X hX N Kb _ hKb hg i).div (sampW_meas X hX N Kb _ hKb hg1 i)).sub
      ((sampW_meas X hX N Ka _ hKa hg i).div (sampW_meas X hX N Ka _ hKa hg1 i))).div_const η).sub
    ((((popW_meas (m := m) X hX Kb _ hKb hg i).div (popW_meas (m := m) X hX Kb _ hKb hg1 i)).sub
      ((popW_meas (m := m) X hX Ka _ hKa hg i).div
        (popW_meas (m := m) X hX Ka _ hKa hg1 i))).div_const η)

/-- The exceptional set `{ω | ∃ i < N, K < |qDiff_i(ω)|/D}` is measurable, for any reals `K`, `D`. -/
theorem excSet_meas {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) (Ka Kb : E → E → ℝ)
    (hKa : Measurable fun p : E × E => Ka p.1 p.2) (hKb : Measurable fun p : E × E => Kb p.1 p.2)
    (f : E → ℝ) (hf : Measurable f) (η K D : ℝ) :
    MeasurableSet {ω | ∃ i < N, K < |qDiff X N m Ka Kb f η i ω| / D} := by
  have e : {ω | ∃ i < N, K < |qDiff X N m Ka Kb f η i ω| / D}
      = ⋃ i, ⋃ (_ : i < N), {ω | K < |qDiff X N m Ka Kb f η i ω| / D} := by
    ext ω; simp
  rw [e]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ =>
    measurableSet_lt measurable_const
      ((qDiff_meas X hX N Ka Kb hKa hKb f hf η i).abs.div_const D)

end Meas

section GeomUniform

open Bundle Manifold CTG.ManifoldDistance CTG.ManifoldVolume CTG.NPointGeom
open scoped Manifold ENNReal

universe u

variable {n : ℕ} {M : Type*} [EMetricSpace M] [ChartedSpace (Fin n → ℝ) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M]
  [IsContinuousRiemannianBundle (Fin n → ℝ) (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsRiemannianManifold 𝓘(ℝ, Fin n → ℝ) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [PreconnectedSpace M]

/-- **(3) Measurability of the exceptional set of `npoint_step5_lip_geom_log`**, literally the same
set (for arbitrary values of the constants), for measurable sample points, continuous profile and
measurable `f`. -/
theorem npoint_step5_lip_geom_log_set_measurable {s : Set ℝ}
    (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (m : Measure M) [IsProbabilityMeasure m] {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → M)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) (ξ : ℝ) (h : ℝ → ℝ) (hhc : Continuous h)
    (f : M → ℝ) (hf : Measurable f) (Am r₀ A cq h₀ Lip ch : ℝ) :
    MeasurableSet {ω | ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
        < |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω| / (ch * ξ ^ 2 / 2)} :=
  excSet_meas X hX N _ _ (kern_measurable G ha ha hcont h hhc ξ)
    (kern_measurable G ha hb hcont h hhc ξ) f hf (b - a) _ _

/-- **Window version of the upper growth.**  With the metric continuous at a reference time `a₀`:
one pair `A_m, r₀` serves every time `τ ∈ s` with `κ|τ − a₀| ≤ 1`. -/
theorem growth_window {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) (m₁ : ℝ) (hm₁ : 0 ≤ m₁) (hm : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∀ τ ∈ s, G.κ * |τ - a₀| ≤ 1 →
      ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y τ < r} ≤ ENNReal.ofReal (Am * r ^ n) := by
  obtain ⟨A, hA, r₁, hr₁, h⟩ := sampling_upper_growth_time G ha₀ hcont m m₁ hm₁ hm
  have hE : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  refine ⟨A * Real.exp 1 ^ n, by positivity, r₁ / Real.exp 1, by positivity,
    fun τ hτ hτw x r hr hrr => ?_⟩
  have hEr : Real.exp 1 * r ≤ r₁ := by rwa [le_div_iff₀ hE0, mul_comm] at hrr
  have hsub : {y | G.dist x y τ < r} ⊆ {y | G.dist x y a₀ < Real.exp 1 * r} := by
    intro y hy
    have h3 := dist_le_exp_dist G ha₀ hτ hcont x y
    have h4 : Real.exp (G.κ * |τ - a₀|) ≤ Real.exp 1 := Real.exp_le_exp.2 hτw
    have hd := G.dist_nonneg x y τ
    simp only [mem_setOf_eq] at hy ⊢
    calc G.dist x y a₀ ≤ Real.exp (G.κ * |τ - a₀|) * G.dist x y τ := h3
      _ ≤ Real.exp 1 * G.dist x y τ := mul_le_mul_of_nonneg_right h4 hd
      _ < Real.exp 1 * r := mul_lt_mul_of_pos_left hy hE0
  refine (measure_mono hsub).trans ((h x (Real.exp 1 * r) (by positivity) hEr).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  ring

/-- **Window version of the lower bound of the population normalisation.**  One pair `c_q, ξ₀`
serves every time `τ ∈ s` with `κ|τ − a₀| ≤ 1` (comparison constant `e^{κ|τ−a₀|} C_{a₀} ≤ e C_{a₀}`). -/
theorem popNorm_window {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsFiniteMeasure m] (m₀ : ℝ) (hm₀ : 0 < m₀)
    (hm : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ∀ (h : ℝ → ℝ) (A h₀ : ℝ), Continuous h → 0 ≤ A →
      (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ h t) → 0 ≤ h₀ →
      (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) → ∀ τ ∈ s, G.κ * |τ - a₀| ≤ 1 →
      ∀ ξ, 0 < ξ → ξ ≤ ξ₀ → ∀ x : M, cq * h₀ * ξ ^ n ≤ popNorm G h ξ τ m x := by
  obtain ⟨a', ha', r₀, hr₀, hlow⟩ := sampling_normalisation_lower m m₀ hm₀.le hm
  obtain ⟨C0, hC0, hle0⟩ := G.redist_le_edist ha₀ ha₀ hcont
  set K := max (Real.exp 1 * C0.toReal) 1 with hKdef
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK0 : 0 < K := by linarith
  refine ⟨m₀ * a' * (s₀ / K) ^ n, by positivity, r₀ * K / s₀, by positivity,
    fun h A h₀ hhc hA hh hh0 hh₀ hlo τ hτ hτw ξ hξ hξ₀ x => ?_⟩
  have hξr : s₀ * ξ / K ≤ r₀ := by
    rw [div_le_iff₀ hK0]
    rw [le_div_iff₀ hs₀] at hξ₀
    linarith
  have hCτt : ENNReal.ofReal (Real.exp (G.κ * |τ - a₀|)) * C0 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC0
  have hleτ : ∀ x y : M, (letI := G.norms τ; Manifold.riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y)
      ≤ ENNReal.ofReal (Real.exp (G.κ * |τ - a₀|)) * C0 * edist x y := by
    intro x y
    calc (letI := G.norms τ; Manifold.riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y)
        ≤ ENNReal.ofReal (Real.exp (G.κ * |τ - a₀|))
            * (letI := G.norms a₀; Manifold.riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y) :=
          G.riemannianEDist_le ha₀ hτ x y
      _ ≤ ENNReal.ofReal (Real.exp (G.κ * |τ - a₀|)) * (C0 * edist x y) :=
          mul_le_mul_left' (hle0 x y) _
      _ = ENNReal.ofReal (Real.exp (G.κ * |τ - a₀|)) * C0 * edist x y := by rw [mul_assoc]
  have hKτ : (ENNReal.ofReal (Real.exp (G.κ * |τ - a₀|)) * C0).toReal ≤ K := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    refine le_trans ?_ (le_max_left _ _)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hτw) ENNReal.toReal_nonneg
  have e : m₀ * a' * (s₀ / K) ^ n * h₀ * ξ ^ n = h₀ * m₀ * a' * (s₀ * ξ / K) ^ n := by
    rw [div_pow, div_pow, mul_pow]; ring
  rw [e]
  exact popNorm_lower_one G ha₀ hτ hcont m _ hCτt hleτ K hKτ hK0 m₀ a' r₀ hlow h hhc A hA hh
    hh0 h₀ s₀ hh₀ hs₀ hlo ξ hξ hξr x

/-- Lipschitz in `d_{a₀}` gives Lipschitz in `d_τ` with constant `e·Lip` for `κ|τ − a₀| ≤ 1`. -/
theorem lip_window {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (f : M → ℝ) (Lip : ℝ) (hLip : 0 ≤ Lip) (hL : ∀ x y, |f y - f x| ≤ Lip * G.dist x y a₀)
    (τ : ℝ) (hτ : τ ∈ s) (hτw : G.κ * |τ - a₀| ≤ 1) :
    ∀ x y, |f y - f x| ≤ Lip * Real.exp 1 * G.dist x y τ := by
  intro x y
  have hd := G.dist_nonneg x y τ
  have hE : Real.exp (G.κ * |τ - a₀|) ≤ Real.exp 1 := Real.exp_le_exp.2 hτw
  calc |f y - f x| ≤ Lip * G.dist x y a₀ := hL x y
    _ ≤ Lip * (Real.exp (G.κ * |τ - a₀|) * G.dist x y τ) :=
        mul_le_mul_of_nonneg_left (dist_le_exp_dist G ha₀ hτ hcont x y) hLip
    _ ≤ Lip * (Real.exp 1 * G.dist x y τ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hE hd) hLip
    _ = Lip * Real.exp 1 * G.dist x y τ := by ring

/-- **(1) Finitely many time pairs simultaneously.**  Reference time `a₀ ∈ s` with the metric
continuous in the base point at `a₀`; sampling law `m₀ μH[n] ≤ m ≤ m₁ μH[n]`; `s₀ > 0`.  There are
`A_m, r₀, c_q, ξ₀` depending only on `G, a₀, m₀, m₁, s₀` (NOT on the pairs) such that: for every sample,
`N ≥ 2`, `ξ ≤ ξ₀`, profile as in `npoint_step5_lip_geom_log`, measurable `f` that is `Lip`-Lipschitz in
`d_{a₀}` (HYPOTHESIS), `c_h > 0`, and every finite family of pairs `(a_j, b_j)`, `j < J`, in the window
(HYPOTHESES: `a_j, b_j ∈ s`, `κ|a_j − a₀| ≤ 1`, `κ|b_j − a₀| ≤ 1`, `κ|b_j − a_j| ≤ 1`, `b_j ≠ a_j`),
under `92416 Λ¹⁴ · 3 log N ≤ N ξⁿ` (`Λ = lipLam n A_m r₀ A κ (c_q h₀) (e·Lip)`, the same for all `j`):
with probability at least `1 − 30 J/N²`, for all `j < J` and `i < N`,
`|Δ_{η_j}(L_N f)(i) − Δ_{η_j}(L_ξ f)(X_i)| ≤ (2/c_h)·3 660 000 Λ²⁰ √(3 log N/(N ξⁿ)) / ξ`. -/
theorem npoint_lip_pairs {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] (m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁)
    (hlow : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ξ₀ ≤ 1 ∧
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 2 ≤ N → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (h h' : ℝ → ℝ) (A h₀ : ℝ), 0 < A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
        (∀ t, 0 ≤ h t) → 0 < h₀ → (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) →
      ∀ (f : M → ℝ), Measurable f → ∀ Lip : ℝ, 0 ≤ Lip →
        (∀ x y, |f y - f x| ≤ Lip * G.dist x y a₀) →
      ∀ ch : ℝ, 0 < ch →
      ∀ (J : ℕ) (a b : ℕ → ℝ), (∀ j < J, a j ∈ s ∧ b j ∈ s ∧ G.κ * |a j - a₀| ≤ 1
          ∧ G.κ * |b j - a₀| ≤ 1 ∧ G.κ * |b j - a j| ≤ 1 ∧ b j ≠ a j) →
      92416 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 14 * (3 * Real.log N)
        ≤ N * ξ ^ n →
      μ.real {ω | ∃ j < J, ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
        < |qDiff X N m (kern G h ξ (a j)) (kern G h ξ (b j)) f (b j - a j) i ω|
            / (ch * ξ ^ 2 / 2)}
        ≤ J * (30 / (N : ℝ) ^ 2) := by
  obtain ⟨Am, hAm, r₀, hr₀, hg⟩ := growth_window G ha₀ hcont m m₁ hm₁ hup
  obtain ⟨cq, hcq, ξ₀, hξ₀, hq⟩ := popNorm_window G ha₀ hcont m m₀ hm₀ hlow s₀ hs₀
  refine ⟨Am, hAm, r₀, hr₀, cq, hcq, min ξ₀ 1, lt_min hξ₀ one_pos, min_le_right _ _, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Lip hLip hL ch hch J a b hab hNL
  have hN0 : 0 < N := by omega
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Set Ω, ∀ j, S j = {ω | ∃ i < N,
      2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
        * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
      < |qDiff X N m (kern G h ξ (a j)) (kern G h ξ (b j)) f (b j - a j) i ω|
          / (ch * ξ ^ 2 / 2)} := ⟨_, fun j => rfl⟩
  have hsub : {ω | ∃ j < J, ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
        < |qDiff X N m (kern G h ξ (a j)) (kern G h ξ (b j)) f (b j - a j) i ω|
            / (ch * ξ ^ 2 / 2)} ⊆ ⋃ j ∈ Finset.range J, S j := by
    rintro ω ⟨j, hj, hi⟩
    exact mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hj, by rw [hS]; exact hi⟩
  have hSj : ∀ j ∈ Finset.range J, μ.real (S j) ≤ 30 / (N : ℝ) ^ 2 := by
    intro j hj
    obtain ⟨haj, hbj, hwa, hwb, hκ, hne⟩ := hab j (Finset.mem_range.1 hj)
    rw [hS, ← exp_neg_three_log N hN0]
    exact npoint_step5_lip_norm G ha₀ hcont haj hbj hκ hne m X h_indep hX hlaw N hN0 n Am r₀ ξ
      hAm hr₀ hξ (hξξ₀.trans (min_le_right _ _)) (hg _ haj hwa) (hg _ hbj hwb) h h' A hA hder hbd
      hh hh0 f hf (Lip * Real.exp 1) (by positivity) (lip_window G ha₀ hcont f Lip hLip hL _ haj hwa)
      (lip_window G ha₀ hcont f Lip hLip hL _ hbj hwb) (cq * h₀) (by positivity)
      (fun y => hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo _ haj hwa ξ hξ
        (hξξ₀.trans (min_le_left _ _)) y)
      (fun y => hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo _ hbj hwb ξ hξ
        (hξξ₀.trans (min_le_left _ _)) y)
      (3 * Real.log N) (three_log_ge_one N hN) hNL ch hch
  calc μ.real _ ≤ μ.real (⋃ j ∈ Finset.range J, S j) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range J, μ.real (S j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range J, 30 / (N : ℝ) ^ 2 := Finset.sum_le_sum hSj
    _ = J * (30 / (N : ℝ) ^ 2) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Measurability of the exceptional set of `npoint_lip_pairs` (finite union of the sets of
`npoint_step5_lip_geom_log_set_measurable`), for pairs in `s` and the metric continuous at `a₀`. -/
theorem npoint_lip_pairs_set_measurable {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s)
    {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → M)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) (ξ : ℝ) (h : ℝ → ℝ) (hhc : Continuous h)
    (f : M → ℝ) (hf : Measurable f) (Am r₀ A cq h₀ Lip ch : ℝ) (J : ℕ) (a b : ℕ → ℝ)
    (hab : ∀ j < J, a j ∈ s ∧ b j ∈ s) :
    MeasurableSet {ω | ∃ j < J, ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
        < |qDiff X N m (kern G h ξ (a j)) (kern G h ξ (b j)) f (b j - a j) i ω|
            / (ch * ξ ^ 2 / 2)} := by
  have e : {ω | ∃ j < J, ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
        < |qDiff X N m (kern G h ξ (a j)) (kern G h ξ (b j)) f (b j - a j) i ω|
            / (ch * ξ ^ 2 / 2)}
      = ⋃ j, ⋃ (_ : j < J), {ω | ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
        < |qDiff X N m (kern G h ξ (a j)) (kern G h ξ (b j)) f (b j - a j) i ω|
            / (ch * ξ ^ 2 / 2)} := by
    ext ω; simp
  rw [e]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj =>
    excSet_meas X hX N _ _ (kern_measurable G ha₀ (hab j hj).1 hcont h hhc ξ)
      (kern_measurable G ha₀ (hab j hj).2 hcont h hhc ξ) f hf (b j - a j) _ _

end GeomUniform

end CTG.NPointUniform
