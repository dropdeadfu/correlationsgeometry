/-
From Correlations to Geometry -- twelfth Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the ninth file `CorrelationsToGeometryManifold.lean` (time-dependent metric, distance, integral
bounds) and the eleventh `CorrelationsToGeometryReal3b.lean` (abstract Bernstein step, quotient rule).
Content: Steps 2 to 5 of the proof of Proposition "dotLN-diff" (Appendix H of the paper, the N-point version
for data at two times) for independent sample points on a compact connected manifold with a time-dependent
metric.  The geometry enters ONLY through HYPOTHESES on the sampling law: upper volume growth of balls at the
two times, and a lower bound for the population normalisation; two smallness conditions are hypotheses as
well.  The bounds are explicit (`dev`, `err5`) and are NOT brought to the form `C δ'/ξ` of the paper; the
test function is only bounded; Step 6 (which needs the Laplace--Beltrami limit) is not formalised.
Check with `cd lean && ./check_npoint.sh` (against the COMPILED ninth and eleventh files).
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryManifold
import CorrelationsToGeometryReal3b

/-!
# A119: Steps 2–5 of the proof of Proposition `prop:dotLN-diff` (N-point version for data at two times)

Scratch block, NOT part of the repository's Lean files.  Namespace `CTG.NPoint`.  No `sorry`, no `axiom`,
no `native_decide`.

* Abstract template (any measurable space `E`, independent points `X j` with law `m`):
  `centered_bernstein`, `sample_avg_dev`, `sample_avg_dev'` (Bernstein + union bound over `i < N`, self-term
  `j = i` handled explicitly: the term `2B/N` of `dev`).
* Step 2 on a manifold (`npoint_step2`): sample normalisations at two times and their difference quotient,
  with the variance proxies `vKern`, `vInc` from the integral bounds of the ninth file.  HYPOTHESIS: the upper
  volume-growth bound `m{y : d_τ(x,y) < r} ≤ A_m r^d` (`0 < r ≤ r₀`) at both times, uniformly in `x`.
* Steps 3–4 (`step34_det`, `bad34_prob`): sample weighted averages `(1/N) Σ_j K_ij g_ij / q_j` against the
  population integrals, at one time and as difference quotient (product rule), for a bounded measurable
  test kernel `g`; no Taylor expansion, population quantities stay integrals.
* Step 5 (`step5`, `step5_nonneg`, `npoint_step5`): the difference quotient of `𝒩/𝒟` via
  `TimeAppendix4.quotient_dq_perturb`.  HYPOTHESIS: `q^τ(x) ≥ c` at both times (in the paper `c ξ^d`), and the
  smallness conditions "relative errors ≤ 1/2".
NOT done: Step 6 (needs `thm:LB`), the gain `|f(y) − f(x)| ≤ ‖df‖ d(x,y)` (here `|g| ≤ 2‖f‖_∞`, so the
numerator error is not of order `ξ δ'`), the simplification of `dev`, `err5` to the form `C δ'`, the division
by `c_h ξ²/2`.
-/

open MeasureTheory ProbabilityTheory Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.NPoint

section Abstract

variable {E : Type*} [MeasurableSpace E]

/-- Population average `∫ F(x,z) dm(z)`. -/
def popAvg (m : Measure E) (F : E → E → ℝ) (x : E) : ℝ := ∫ z, F x z ∂m

/-- Sample average `(1/N) Σ_{j<N} F(X_i, X_j)` (the self-term `j = i` included). -/
def sampAvg {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (F : E → E → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (1 / (N : ℝ)) * ∑ j ∈ Finset.range N, F (X i ω) (X j ω)

theorem popAvg_measurable (m : Measure E) [SFinite m] (F : E → E → ℝ)
    (hF : Measurable fun p : E × E => F p.1 p.2) : Measurable (popAvg m F) :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := m)).measurable

theorem integrable_of_bound (m : Measure E) [IsFiniteMeasure m] (F : E → E → ℝ)
    (hF : Measurable fun p : E × E => F p.1 p.2) {B : ℝ} (hbd : ∀ x z, |F x z| ≤ B) (x : E) :
    Integrable (F x) m :=
  Integrable.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable B
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hbd x z)

theorem popAvg_abs_le (m : Measure E) [IsProbabilityMeasure m] (F : E → E → ℝ) {B : ℝ}
    (hbd : ∀ x z, |F x z| ≤ B) (x : E) : |popAvg m F x| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := m) (f := F x) (C := B)
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hbd x z)
  simpa [popAvg, Real.norm_eq_abs] using h

/-- The variance is at most the second moment. -/
theorem centered_sq_le (m : Measure E) [IsProbabilityMeasure m] (F : E → E → ℝ)
    (hF : Measurable fun p : E × E => F p.1 p.2) {B : ℝ} (hbd : ∀ x z, |F x z| ≤ B) (x : E) :
    ∫ z, (F x z - popAvg m F x) ^ 2 ∂m ≤ ∫ z, F x z ^ 2 ∂m := by
  set c := popAvg m F x
  have hi := integrable_of_bound m F hF hbd x
  have hmeas : Measurable (F x) := hF.comp (measurable_const.prodMk measurable_id)
  have hi2 : Integrable (fun z => F x z ^ 2) m :=
    Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable (B ^ 2)
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd x z) 2)
  have e : ∀ z, (F x z - c) ^ 2 = (F x z ^ 2 - (2 * c) * F x z) + c ^ 2 := fun z => by ring
  simp_rw [e]
  rw [integral_add (f := fun z => F x z ^ 2 - (2 * c) * F x z) (g := fun _ => c ^ 2)
      (by exact hi2.sub (hi.const_mul (2 * c))) (integrable_const _),
    integral_sub (f := fun z => F x z ^ 2) (g := fun z => (2 * c) * F x z) hi2
      (hi.const_mul (2 * c)),
    integral_const_mul, integral_const]
  have hc : ∫ z, F x z ∂m = c := rfl
  rw [hc]
  simp
  nlinarith [sq_nonneg c]

/-- Bernstein for the centred summands `F(X_i,X_j) − ∫F(X_i,·)` (generic form of Steps 2–4). -/
theorem centered_bernstein {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : Measure E) [IsProbabilityMeasure m]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (i : ℕ) (T : Finset ℕ) (hiT : i ∉ T)
    (F : E → E → ℝ) (hF : Measurable fun p : E × E => F p.1 p.2) {B v L : ℝ}
    (hB : 0 < B) (hv : 0 ≤ v) (hL : 0 < L)
    (hbd : ∀ x z, |F x z| ≤ B) (hvar : ∀ x, ∫ z, F x z ^ 2 ∂m ≤ v) :
    μ.real {ω | 2 * (2 * B) * L + 2 * Real.sqrt (T.card * v * L)
        ≤ |∑ j ∈ T, (F (X i ω) (X j ω) - popAvg m F (X i ω))|} ≤ 2 * Real.exp (-L) := by
  have hP := popAvg_measurable m F hF
  refine CTG.Reals2.TimeAppendix5.bernstein_conditioned m X h_indep hX hlaw i T hiT
    (fun x z => F x z - popAvg m F x) (hF.sub (hP.comp measurable_fst)) (by linarith) hv hL
    (fun x z => ?_) (fun x => ?_) (fun x => (centered_sq_le m F hF hbd x).trans (hvar x))
  · have h1 := hbd x z; have h2 := popAvg_abs_le m F hbd x
    calc |F x z - popAvg m F x| ≤ |F x z| + |popAvg m F x| := abs_sub _ _
      _ ≤ 2 * B := by linarith
  · rw [integral_sub (integrable_of_bound m F hF hbd x) (integrable_const _), integral_const]
    simp [popAvg]

/-- Deterministic decomposition: the sample average minus the population average is
`(1/N)(Σ_{j≠i} (F(x_i,x_j) − ∫F(x_i,·)) + (F(x_i,x_i) − ∫F(x_i,·)))`. -/
theorem sampAvg_sub_popAvg {Ω : Type*} (m : Measure E) (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N)
    (F : E → E → ℝ) (i : ℕ) (hi : i < N) (ω : Ω) :
    sampAvg X N F i ω - popAvg m F (X i ω)
      = (1 / (N : ℝ)) * (∑ j ∈ (Finset.range N).erase i,
            (F (X i ω) (X j ω) - popAvg m F (X i ω))
          + (F (X i ω) (X i ω) - popAvg m F (X i ω))) := by
  have hmem : i ∈ Finset.range N := Finset.mem_range.2 hi
  rw [Finset.sum_erase_add _ _ hmem, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, sampAvg]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Step 2 template (one kernel, all `i < N`): with probability at least `1 − N·2e^{−L}`,
`|(1/N)Σ_j F(X_i,X_j) − ∫F(X_i,·)dm| ≤ (4BL + 2√(NvL) + 2B)/N` for all `i < N`.  The self-term
`j = i` is the `2B/N`. -/
theorem sample_avg_dev {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : Measure E) [IsProbabilityMeasure m]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (F : E → E → ℝ) (hF : Measurable fun p : E × E => F p.1 p.2) {B v L : ℝ}
    (hB : 0 < B) (hv : 0 ≤ v) (hL : 0 < L)
    (hbd : ∀ x z, |F x z| ≤ B) (hvar : ∀ x, ∫ z, F x z ^ 2 ∂m ≤ v) :
    μ.real {ω | ∃ i < N, (2 * (2 * B) * L + 2 * Real.sqrt (N * v * L) + 2 * B) / N
        < |sampAvg X N F i ω - popAvg m F (X i ω)|} ≤ N * (2 * Real.exp (-L)) := by
  set S : ℕ → Set Ω := fun i => {ω | 2 * (2 * B) * L
      + 2 * Real.sqrt (((Finset.range N).erase i).card * v * L)
        ≤ |∑ j ∈ (Finset.range N).erase i, (F (X i ω) (X j ω) - popAvg m F (X i ω))|}
  have hsub : {ω | ∃ i < N, (2 * (2 * B) * L + 2 * Real.sqrt (N * v * L) + 2 * B) / N
        < |sampAvg X N F i ω - popAvg m F (X i ω)|} ⊆ ⋃ i ∈ Finset.range N, S i := by
    intro ω ⟨i, hi, hlt⟩
    simp only [mem_iUnion, Finset.mem_range]
    refine ⟨i, hi, ?_⟩
    by_contra hcon
    simp only [S, mem_setOf_eq, not_le] at hcon
    have hcard : (((Finset.range N).erase i).card : ℝ) ≤ N := by
      rw [Finset.card_erase_of_mem (Finset.mem_range.2 hi), Finset.card_range]
      exact_mod_cast Nat.sub_le N 1
    have hsq : Real.sqrt (((Finset.range N).erase i).card * v * L) ≤ Real.sqrt (N * v * L) :=
      Real.sqrt_le_sqrt (by
        have := mul_le_mul_of_nonneg_right hcard hv
        exact mul_le_mul_of_nonneg_right this hL.le)
    have hself : |F (X i ω) (X i ω) - popAvg m F (X i ω)| ≤ 2 * B := by
      have h1 := hbd (X i ω) (X i ω); have h2 := popAvg_abs_le m F hbd (X i ω)
      calc _ ≤ |F (X i ω) (X i ω)| + |popAvg m F (X i ω)| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    rw [sampAvg_sub_popAvg m X N hN F i hi ω, abs_mul] at hlt
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [abs_of_pos (by positivity), one_div_mul_eq_div] at hlt
    have := (abs_add_le _ _).trans (add_le_add hcon.le hself)
    have h3 : (2 * (2 * B) * L + 2 * Real.sqrt (N * v * L) + 2 * B) / N
        < (2 * (2 * B) * L + 2 * Real.sqrt (((Finset.range N).erase i).card * v * L) + 2 * B) / N :=
      lt_of_lt_of_le hlt (div_le_div_of_nonneg_right this hNpos.le)
    have h4 := (div_lt_div_iff_of_pos_right hNpos).1 h3
    linarith
  calc μ.real _ ≤ μ.real (⋃ i ∈ Finset.range N, S i) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.range N, μ.real (S i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, 2 * Real.exp (-L) := Finset.sum_le_sum fun i hi =>
        centered_bernstein m X h_indep hX hlaw i _ (Finset.notMem_erase i _) F hF hB hv hL hbd hvar
    _ = N * (2 * Real.exp (-L)) := by simp

end Abstract

section Abstract2

variable {E : Type*} [MeasurableSpace E]

/-- `sample_avg_dev` for `0 ≤ B` (for `B = 0` the kernel vanishes and the event is empty). -/
theorem sample_avg_dev' {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (m : Measure E) [IsProbabilityMeasure m]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (F : E → E → ℝ) (hF : Measurable fun p : E × E => F p.1 p.2) {B v L : ℝ}
    (hB : 0 ≤ B) (hv : 0 ≤ v) (hL : 0 < L)
    (hbd : ∀ x z, |F x z| ≤ B) (hvar : ∀ x, ∫ z, F x z ^ 2 ∂m ≤ v) :
    μ.real {ω | ∃ i < N, (2 * (2 * B) * L + 2 * Real.sqrt (N * v * L) + 2 * B) / N
        < |sampAvg X N F i ω - popAvg m F (X i ω)|} ≤ N * (2 * Real.exp (-L)) := by
  rcases hB.lt_or_eq with hBp | hB0
  · exact sample_avg_dev m X h_indep hX hlaw N hN F hF hBp hv hL hbd hvar
  · have hF0 : ∀ x z, F x z = 0 := fun x z => by
      have := hbd x z; rw [← hB0] at this; exact abs_nonpos_iff.1 this
    have hempty : {ω | ∃ i < N, (2 * (2 * B) * L + 2 * Real.sqrt (N * v * L) + 2 * B) / N
        < |sampAvg X N F i ω - popAvg m F (X i ω)|} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists, not_and, not_lt]
      intro i _
      simp only [sampAvg, popAvg, hF0, Finset.sum_const_zero, mul_zero, integral_zero, sub_zero,
        abs_zero]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [← hB0]
      have := Real.sqrt_nonneg (N * v * L)
      positivity
    rw [hempty, measureReal_empty]
    positivity

/-- Linearity of the sample average for the increment kernel. -/
theorem sampAvg_inc {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (K1 K2 : E → E → ℝ) (η : ℝ) (i : ℕ)
    (ω : Ω) :
    sampAvg X N (fun x z => (K2 x z - K1 x z) / η) i ω
      = (sampAvg X N K2 i ω - sampAvg X N K1 i ω) / η := by
  simp only [sampAvg, ← Finset.sum_div, Finset.sum_sub_distrib]
  ring

/-- Linearity of the population average for the increment kernel. -/
theorem popAvg_inc (m : Measure E) [IsFiniteMeasure m] (K1 K2 : E → E → ℝ)
    (hK1 : Measurable fun p : E × E => K1 p.1 p.2) (hK2 : Measurable fun p : E × E => K2 p.1 p.2)
    {B1 B2 : ℝ} (hb1 : ∀ x z, |K1 x z| ≤ B1) (hb2 : ∀ x z, |K2 x z| ≤ B2) (η : ℝ) (x : E) :
    popAvg m (fun x z => (K2 x z - K1 x z) / η) x = (popAvg m K2 x - popAvg m K1 x) / η := by
  simp only [popAvg]
  rw [integral_div, integral_sub (integrable_of_bound m K2 hK2 hb2 x)
    (integrable_of_bound m K1 hK1 hb1 x)]

/-- From a bound on the lower integral (in the form of the integral bounds of the ninth file)
to a bound on the integral. -/
theorem integral_le_of_lintegral_le (m : Measure E) [IsProbabilityMeasure m] (f : E → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hfm : Measurable f) (R1 R2 : ℝ) (h1 : 0 ≤ R1) (h2 : 0 ≤ R2)
    (h : ∫⁻ z, ENNReal.ofReal (f z) ∂m ≤ ENNReal.ofReal R1 + ENNReal.ofReal R2 * m univ) :
    ∫ z, f z ∂m ≤ R1 + R2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm.aestronglyMeasurable]
  rw [measure_univ, mul_one, ← ENNReal.ofReal_add h1 h2] at h
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

end Abstract2

section Manifold

open Bundle Manifold CTG.ManifoldDistance

variable {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EE H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle EE (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M]

/-- The kernel `K^τ(x,y) = h(d_τ(x,y)/ξ)` of a time-dependent metric. -/
def kern {s : Set ℝ} (G : TimeMetric I M s) (h : ℝ → ℝ) (ξ τ : ℝ) (x y : M) : ℝ :=
  h (G.dist x y τ / ξ)

/-- The difference quotient `Δ_η K = (K^b − K^a)/(b − a)` of the kernel. -/
def kernInc {s : Set ℝ} (G : TimeMetric I M s) (h : ℝ → ℝ) (ξ a b : ℝ) (x y : M) : ℝ :=
  (kern G h ξ b x y - kern G h ξ a x y) / (b - a)

/-- Sample normalisation `q^τ_i = (1/N) Σ_{j<N} K^τ(X_i,X_j)`. -/
def sampNorm {s : Set ℝ} (G : TimeMetric I M s) (h : ℝ → ℝ) (ξ τ : ℝ) {Ω : Type*}
    (X : ℕ → Ω → M) (N : ℕ) (i : ℕ) (ω : Ω) : ℝ :=
  sampAvg X N (kern G h ξ τ) i ω

/-- Population normalisation `q^τ(x) = ∫ h(d_τ(x,y)/ξ) dm(y)`. -/
def popNorm {s : Set ℝ} (G : TimeMetric I M s) (h : ℝ → ℝ) (ξ τ : ℝ) (m : Measure M) (x : M) :
    ℝ := popAvg m (kern G h ξ τ) x

theorem sexp_le_one (t : ℝ) (ht : 0 ≤ t) : t * Real.exp (-Real.exp (-1) * t) ≤ 1 := by
  have h1 := Real.add_one_le_exp (Real.exp (-1) * t - 1)
  have h2 : Real.exp (Real.exp (-1) * t - 1) = Real.exp (Real.exp (-1) * t) * Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have h3 : t ≤ Real.exp (Real.exp (-1) * t) := by
    have : Real.exp (-1) * t ≤ Real.exp (Real.exp (-1) * t) * Real.exp (-1) := by linarith
    nlinarith [Real.exp_pos 1, Real.exp_pos (Real.exp (-1) * t)]
  have h4 : Real.exp (-Real.exp (-1) * t) * Real.exp (Real.exp (-1) * t) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-Real.exp (-1) * t)]

variable {s : Set ℝ}

theorem kern_measurable (G : TimeMetric I M s) {a₀ τ : ℝ} (ha₀ : a₀ ∈ s) (hτ : τ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (h : ℝ → ℝ) (hhc : Continuous h) (ξ : ℝ) :
    Measurable fun p : M × M => kern G h ξ τ p.1 p.2 :=
  (hhc.comp ((G.dist_continuous_pair ha₀ hτ hcont).div_const ξ)).measurable

theorem kern_abs_le (G : TimeMetric I M s) (h : ℝ → ℝ) (A ξ τ : ℝ) (hξ : 0 < ξ)
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hA : 0 ≤ A) (x y : M) :
    |kern G h ξ τ x y| ≤ A := by
  have ht : 0 ≤ G.dist x y τ / ξ := div_nonneg (G.dist_nonneg x y τ) hξ.le
  refine (hh _ ht).trans ?_
  have : Real.exp (-(G.dist x y τ / ξ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  nlinarith

theorem kernInc_abs_le (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (h h' : ℝ → ℝ) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (x y : M) : |kernInc G h ξ a b x y| ≤ 2 * G.κ * A := by
  have hk := G.kernel_increment_le ha hb hab x y (G.riemannianEDist_ne_top ha₀ ha hcont x y)
    h h' A ξ hA hξ hder hbd
  have hd : 0 < |b - a| := abs_pos.2 (sub_ne_zero.2 hne)
  have hs := sexp_le_one (G.dist x y a / ξ) (div_nonneg (G.dist_nonneg x y a) hξ.le)
  have hc : 0 ≤ 2 * (G.κ * |b - a|) * A := by have := G.κ_nonneg; positivity
  rw [pow_one] at hk
  unfold kernInc kern
  rw [abs_div, div_le_iff₀ hd]
  calc |h (G.dist x y b / ξ) - h (G.dist x y a / ξ)|
      ≤ 2 * (G.κ * |b - a|) * A * (G.dist x y a / ξ * Real.exp (-Real.exp (-1) * (G.dist x y a / ξ))) := hk
    _ ≤ 2 * (G.κ * |b - a|) * A * 1 := mul_le_mul_of_nonneg_left hs hc
    _ = 2 * G.κ * A * |b - a| := by ring

/-- Second-moment constant of the kernel (from `exp_profile_integral` with `j = 0`, `b = 2`). -/
def vKern (d : ℕ) (Am r₀ ξ A : ℝ) : ℝ :=
  Am * (∑' n : ℕ, A ^ 2 * (((n : ℝ) + 1) ^ 0 * Real.exp (-2 * n)) * ((n : ℝ) + 1) ^ d) * ξ ^ d
    + A ^ 2 * (((0 : ℕ).factorial : ℝ) * (2 / 2) ^ 0 * Real.exp (-2 * (r₀ / ξ) / 2))

/-- Second-moment constant of the kernel increment (the bound of
`TimeMetric.kernel_increment_sq_integral` divided by `(b − a)²`). -/
def vInc (κ : ℝ) (d : ℕ) (Am r₀ ξ A a b : ℝ) : ℝ :=
  (Am * (∑' n : ℕ, (2 * (κ * |b - a|) * A) ^ 2
      * (((n : ℝ) + 1) ^ 2 * Real.exp (-(2 * Real.exp (-1)) * n)) * ((n : ℝ) + 1) ^ d) * ξ ^ d
    + (2 * (κ * |b - a|) * A) ^ 2 * (((2 : ℕ).factorial : ℝ) * (2 / (2 * Real.exp (-1))) ^ 2
      * Real.exp (-(2 * Real.exp (-1)) * (r₀ / ξ) / 2))) / (b - a) ^ 2

theorem tsum_nonneg_aux (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) : 0 ≤ ∑' n, f n := tsum_nonneg hf

theorem kern_sq_integral (G : TimeMetric I M s) {a₀ τ : ℝ} (ha₀ : a₀ ∈ s) (hτ : τ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ) (x : M)
    (hgrowth : ∀ r, 0 < r → r ≤ r₀ → m {y | G.dist x y τ < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h : ℝ → ℝ) (hhc : Continuous h) (A : ℝ) (hA : 0 ≤ A)
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) :
    ∫ y, kern G h ξ τ x y ^ 2 ∂m ≤ vKern d Am r₀ ξ A := by
  have hρm : Measurable (fun y => G.dist x y τ) :=
    ((G.dist_continuous_pair ha₀ hτ hcont).comp (continuous_const.prodMk continuous_id)).measurable
  have hpt : ∀ y, kern G h ξ τ x y ^ 2
      ≤ A ^ 2 * ((G.dist x y τ / ξ) ^ 0 * Real.exp (-2 * (G.dist x y τ / ξ))) := by
    intro y
    have ht : 0 ≤ G.dist x y τ / ξ := div_nonneg (G.dist_nonneg x y τ) hξ.le
    have h1 := hh _ ht
    have h2 : kern G h ξ τ x y ^ 2 ≤ (A * Real.exp (-(G.dist x y τ / ξ))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans (le_of_eq ?_)
    rw [pow_zero, one_mul, mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hlin := exp_profile_integral m (fun y => G.dist x y τ) hρm (fun y => G.dist_nonneg x y τ)
    d Am r₀ ξ hAm hr₀ hξ hgrowth (A ^ 2) 2 0 (sq_nonneg A) two_pos
  have hmeasK : Measurable fun y => kern G h ξ τ x y :=
    hhc.measurable.comp (hρm.div_const ξ)
  have hint : ∫ y, kern G h ξ τ x y ^ 2 ∂m
      ≤ ∫ y, A ^ 2 * ((G.dist x y τ / ξ) ^ 0 * Real.exp (-2 * (G.dist x y τ / ξ))) ∂m := by
    refine integral_mono_of_nonneg (ae_of_all _ fun y => sq_nonneg _) ?_ (ae_of_all _ hpt)
    refine Integrable.of_bound ?_ (A ^ 2) (ae_of_all _ fun y => ?_)
    · exact (measurable_const.mul ((hρm.div_const ξ).pow_const 0 |>.mul
        (measurable_const.mul (hρm.div_const ξ)).exp)).aestronglyMeasurable
    · have ht : 0 ≤ G.dist x y τ / ξ := div_nonneg (G.dist_nonneg x y τ) hξ.le
      have : Real.exp (-2 * (G.dist x y τ / ξ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_zero, one_mul]
      nlinarith [sq_nonneg A, Real.exp_pos (-2 * (G.dist x y τ / ξ))]
  refine hint.trans ?_
  refine integral_le_of_lintegral_le m _ (fun y => by positivity)
    (measurable_const.mul ((hρm.div_const ξ).pow_const 0 |>.mul
        (measurable_const.mul (hρm.div_const ξ)).exp)) _ _ ?_ (by positivity) hlin
  exact mul_nonneg (mul_nonneg hAm (tsum_nonneg fun n => by positivity)) (by positivity)

theorem kernInc_sq_integral (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1)
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ) (x : M)
    (hgrowth : ∀ r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) :
    ∫ y, kernInc G h ξ a b x y ^ 2 ∂m ≤ vInc G.κ d Am r₀ ξ A a b := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have hlin := G.kernel_increment_sq_integral ha₀ hcont ha hb hab m x d Am r₀ ξ hAm hr₀ hξ hgrowth
    h h' A hA hder hbd
  have hmb : Measurable fun y : M => kern G h ξ b x y :=
    (kern_measurable G ha₀ hb hcont h hhc ξ).comp (measurable_const.prodMk measurable_id)
  have hma : Measurable fun y : M => kern G h ξ a x y :=
    (kern_measurable G ha₀ ha hcont h hhc ξ).comp (measurable_const.prodMk measurable_id)
  have hfm : Measurable fun y => |h (G.dist x y b / ξ) - h (G.dist x y a / ξ)| ^ 2 :=
    ((hmb.sub hma).abs).pow_const 2
  have hc : 0 ≤ 2 * (G.κ * |b - a|) * A := by have := G.κ_nonneg; positivity
  have h1 := integral_le_of_lintegral_le m _ (fun y => by positivity) hfm _ _
    (mul_nonneg (mul_nonneg hAm (tsum_nonneg fun n => by positivity)) (by positivity))
    (by positivity) hlin
  have e : ∀ y, kernInc G h ξ a b x y ^ 2
      = |h (G.dist x y b / ξ) - h (G.dist x y a / ξ)| ^ 2 / (b - a) ^ 2 := by
    intro y; rw [kernInc, div_pow, sq_abs]; rfl
  simp_rw [e]
  rw [integral_div, vInc]
  exact div_le_div_of_nonneg_right h1 (sq_nonneg _)

end Manifold

/-! ### Steps 3–5 in abstract form -/

section Steps345

variable {E : Type*} [MeasurableSpace E]

/-- Average `(1/N) Σ_{j<N} f j`. -/
def avgN (N : ℕ) (f : ℕ → ℝ) : ℝ := (1 / (N : ℝ)) * ∑ j ∈ Finset.range N, f j

/-- The hypotheses of the Bernstein template for one kernel `F`: measurable, `|F| ≤ B`,
`∫ F(x,·)² dm ≤ v` for every `x`. -/
structure Good (m : Measure E) (F : E → E → ℝ) (B v : ℝ) : Prop where
  meas : Measurable fun p : E × E => F p.1 p.2
  B_nonneg : 0 ≤ B
  v_nonneg : 0 ≤ v
  bd : ∀ x z, |F x z| ≤ B
  var : ∀ x, ∫ z, F x z ^ 2 ∂m ≤ v

/-- The Bernstein threshold of the template, divided by `N`, with the self-term:
`(4BL + 2√(NvL) + 2B)/N`. -/
def dev (N : ℕ) (B v L : ℝ) : ℝ := (2 * (2 * B) * L + 2 * Real.sqrt (N * v * L) + 2 * B) / N

/-- The exceptional event of the template for one kernel. -/
def badSet {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (m : Measure E) (F : E → E → ℝ) (B v L : ℝ) :
    Set Ω :=
  {ω | ∃ i < N, dev N B v L < |sampAvg X N F i ω - popAvg m F (X i ω)|}

theorem Good.prob {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : Measure E} [IsProbabilityMeasure m]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) {F : E → E → ℝ} {B v L : ℝ}
    (hG : Good m F B v) (hL : 0 < L) :
    μ.real (badSet X N m F B v L) ≤ N * (2 * Real.exp (-L)) :=
  sample_avg_dev' m X h_indep hX hlaw N hN F hG.meas hG.B_nonneg hG.v_nonneg hL hG.bd hG.var

theorem not_badSet {Ω : Type*} {X : ℕ → Ω → E} {N : ℕ} {m : Measure E} {F : E → E → ℝ}
    {B v L : ℝ} {ω : Ω} (h : ω ∉ badSet X N m F B v L) {i : ℕ} (hi : i < N) :
    |sampAvg X N F i ω - popAvg m F (X i ω)| ≤ dev N B v L := by
  by_contra hc
  exact h ⟨i, hi, lt_of_not_ge hc⟩

theorem bdd_integrable (m : Measure E) [IsFiniteMeasure m] (f : E → ℝ) (hf : Measurable f)
    (C : ℝ) (h : ∀ z, |f z| ≤ C) : Integrable f m :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun z => by
    simpa [Real.norm_eq_abs] using h z)

theorem Good.mul {m : Measure E} [IsProbabilityMeasure m] {F : E → E → ℝ} {B v : ℝ}
    (hG : Good m F B v) (w : E → E → ℝ) (hw : Measurable fun p : E × E => w p.1 p.2) (c : ℝ)
    (hc : 0 ≤ c) (hwb : ∀ x z, |w x z| ≤ c) :
    Good m (fun x z => F x z * w x z) (B * c) (c ^ 2 * v) where
  meas := hG.meas.mul hw
  B_nonneg := mul_nonneg hG.B_nonneg hc
  v_nonneg := mul_nonneg (sq_nonneg c) hG.v_nonneg
  bd := fun x z => by
    show |F x z * w x z| ≤ B * c
    rw [abs_mul]; exact mul_le_mul (hG.bd x z) (hwb x z) (abs_nonneg _) hG.B_nonneg
  var := fun x => by
    show ∫ z, (F x z * w x z) ^ 2 ∂m ≤ c ^ 2 * v
    have hFx : Measurable (F x) := hG.meas.comp (measurable_const.prodMk measurable_id)
    have hint : Integrable (fun z => F x z ^ 2) m :=
      bdd_integrable m _ (hFx.pow_const 2) (B ^ 2) fun z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hG.bd x z) 2
    have h1 : ∫ z, (F x z * w x z) ^ 2 ∂m ≤ ∫ z, c ^ 2 * F x z ^ 2 ∂m := by
      refine integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) (hint.const_mul _)
        (ae_of_all _ fun z => ?_)
      have hw2 : w x z ^ 2 ≤ c ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) (hwb x z) 2; rwa [sq_abs] at this
      have := sq_nonneg (F x z)
      simp only [mul_pow]
      nlinarith
    rw [integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hG.var x) (sq_nonneg c))

theorem Good.add {m : Measure E} [IsProbabilityMeasure m] {F1 F2 : E → E → ℝ} {B1 B2 v1 v2 : ℝ}
    (h1 : Good m F1 B1 v1) (h2 : Good m F2 B2 v2) :
    Good m (fun x z => F1 x z + F2 x z) (B1 + B2) (2 * v1 + 2 * v2) where
  meas := h1.meas.add h2.meas
  B_nonneg := add_nonneg h1.B_nonneg h2.B_nonneg
  v_nonneg := by have := h1.v_nonneg; have := h2.v_nonneg; positivity
  bd := fun x z => by
    show |F1 x z + F2 x z| ≤ B1 + B2
    exact (abs_add_le _ _).trans (add_le_add (h1.bd x z) (h2.bd x z))
  var := fun x => by
    show ∫ z, (F1 x z + F2 x z) ^ 2 ∂m ≤ 2 * v1 + 2 * v2
    have hF1 : Measurable (F1 x) := h1.meas.comp (measurable_const.prodMk measurable_id)
    have hF2 : Measurable (F2 x) := h2.meas.comp (measurable_const.prodMk measurable_id)
    have i1 : Integrable (fun z => F1 x z ^ 2) m :=
      bdd_integrable m _ (hF1.pow_const 2) (B1 ^ 2) fun z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.bd x z) 2
    have i2 : Integrable (fun z => F2 x z ^ 2) m :=
      bdd_integrable m _ (hF2.pow_const 2) (B2 ^ 2) fun z => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (h2.bd x z) 2
    have hle : ∫ z, (F1 x z + F2 x z) ^ 2 ∂m ≤ ∫ z, (2 * F1 x z ^ 2 + 2 * F2 x z ^ 2) ∂m :=
      integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _)
        ((i1.const_mul 2).add (i2.const_mul 2))
        (ae_of_all _ fun z => by nlinarith [sq_nonneg (F1 x z - F2 x z)])
    rw [integral_add (f := fun z => 2 * F1 x z ^ 2) (g := fun z => 2 * F2 x z ^ 2)
      (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul] at hle
    linarith [h1.var x, h2.var x]

theorem Good.abs {m : Measure E} {F : E → E → ℝ} {B v : ℝ} (hG : Good m F B v) :
    Good m (fun x z => |F x z|) B v where
  meas := continuous_abs.measurable.comp hG.meas
  B_nonneg := hG.B_nonneg
  v_nonneg := hG.v_nonneg
  bd := fun x z => by
    show |(|F x z|)| ≤ B
    rw [abs_abs]; exact hG.bd x z
  var := fun x => by
    show ∫ z, |F x z| ^ 2 ∂m ≤ v
    simp_rw [sq_abs]; exact hG.var x

/-- Deterministic core of Steps 3 and 4 (one weight): replacing the sample weights `w_j` by the
population weights `W_j` costs `e · (average of |F|)`. -/
theorem weighted_det (N : ℕ) (hN : 0 < N) (Fx w W : ℕ → ℝ) (e d1 d2 P1 P2 : ℝ) (he : 0 ≤ e)
    (hw : ∀ j < N, |w j - W j| ≤ e)
    (h1 : |avgN N (fun j => |Fx j|) - P1| ≤ d1)
    (h2 : |avgN N (fun j => Fx j * W j) - P2| ≤ d2) :
    |avgN N (fun j => Fx j * w j) - P2| ≤ e * (P1 + d1) + d2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : avgN N (fun j => Fx j * w j) - P2
      = avgN N (fun j => Fx j * (w j - W j)) + (avgN N (fun j => Fx j * W j) - P2) := by
    simp only [avgN, mul_sub, Finset.sum_sub_distrib]; ring
  have hA : |avgN N (fun j => Fx j * (w j - W j))| ≤ e * avgN N (fun j => |Fx j|) := by
    unfold avgN
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (N : ℝ) * |∑ j ∈ Finset.range N, Fx j * (w j - W j)|
        ≤ 1 / (N : ℝ) * ∑ j ∈ Finset.range N, |Fx j| * e :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j hj => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hw j (Finset.mem_range.1 hj)) (abs_nonneg _)))
            (by positivity)
      _ = e * (1 / (N : ℝ) * ∑ j ∈ Finset.range N, |Fx j|) := by rw [← Finset.sum_mul]; ring
  have hP1 : avgN N (fun j => |Fx j|) ≤ P1 + d1 := by linarith [(abs_le.1 h1).2]
  rw [hsplit]
  calc _ ≤ |avgN N (fun j => Fx j * (w j - W j))| + |avgN N (fun j => Fx j * W j) - P2| :=
        abs_add_le _ _
    _ ≤ e * (P1 + d1) + d2 := add_le_add (hA.trans (mul_le_mul_of_nonneg_left hP1 he)) h2

/-- Deterministic core of Step 3/4 for the difference quotient (two weights). -/
theorem weighted2_det (N : ℕ) (hN : 0 < N) (F1 F2 u U w W : ℕ → ℝ)
    (e1 e2 d1 d1' d2 P1 P1' P2 : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hu : ∀ j < N, |u j - U j| ≤ e1) (hw : ∀ j < N, |w j - W j| ≤ e2)
    (h1 : |avgN N (fun j => |F1 j|) - P1| ≤ d1) (h1' : |avgN N (fun j => |F2 j|) - P1'| ≤ d1')
    (h2 : |avgN N (fun j => F1 j * U j + F2 j * W j) - P2| ≤ d2) :
    |avgN N (fun j => F1 j * u j + F2 j * w j) - P2| ≤ e1 * (P1 + d1) + e2 * (P1' + d1') + d2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : avgN N (fun j => F1 j * u j + F2 j * w j) - P2
      = avgN N (fun j => F1 j * (u j - U j)) + avgN N (fun j => F2 j * (w j - W j))
        + (avgN N (fun j => F1 j * U j + F2 j * W j) - P2) := by
    simp only [avgN, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]; ring
  have key : ∀ (G a A : ℕ → ℝ) (e : ℝ), (∀ j < N, |a j - A j| ≤ e) →
      |avgN N (fun j => G j * (a j - A j))| ≤ e * avgN N (fun j => |G j|) := by
    intro G a A e ha
    unfold avgN
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (N : ℝ) * |∑ j ∈ Finset.range N, G j * (a j - A j)|
        ≤ 1 / (N : ℝ) * ∑ j ∈ Finset.range N, |G j| * e :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j hj => by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (ha j (Finset.mem_range.1 hj)) (abs_nonneg _)))
            (by positivity)
      _ = e * (1 / (N : ℝ) * ∑ j ∈ Finset.range N, |G j|) := by rw [← Finset.sum_mul]; ring
  have hP1 : avgN N (fun j => |F1 j|) ≤ P1 + d1 := by linarith [(abs_le.1 h1).2]
  have hP1' : avgN N (fun j => |F2 j|) ≤ P1' + d1' := by linarith [(abs_le.1 h1').2]
  rw [hsplit]
  have a1 := (key F1 u U e1 hu).trans (mul_le_mul_of_nonneg_left hP1 he1)
  have a2 := (key F2 w W e2 hw).trans (mul_le_mul_of_nonneg_left hP1' he2)
  calc _ ≤ |avgN N (fun j => F1 j * (u j - U j)) + avgN N (fun j => F2 j * (w j - W j))|
        + |avgN N (fun j => F1 j * U j + F2 j * W j) - P2| := abs_add_le _ _
    _ ≤ (|avgN N (fun j => F1 j * (u j - U j))| + |avgN N (fun j => F2 j * (w j - W j))|) + d2 :=
        add_le_add (abs_add_le _ _) h2
    _ ≤ _ := by linarith

/-- The difference quotient of `1/q`: sample against population.  With `|q_τ − p_τ| ≤ e ≤ c/2`,
`p_τ ≥ c`, `|Δq − Δp| ≤ eΔ` and `|Δp| ≤ BΔ`:
`|Δ(1/q) − Δ(1/p)| ≤ 4eΔ/c² + 6BΔ(e/c)/c²`. -/
theorem inv_inc_perturb (qa qb pa pb η e eΔ c BΔ : ℝ) (hc : 0 < c) (hpa : c ≤ pa) (hpb : c ≤ pb)
    (he : 0 ≤ e) (he2 : e / c ≤ 1 / 2) (hBΔ0 : 0 ≤ BΔ)
    (ha : |qa - pa| ≤ e) (hb : |qb - pb| ≤ e)
    (hΔ : |(qb - qa) / η - (pb - pa) / η| ≤ eΔ) (hBΔ : |(pb - pa) / η| ≤ BΔ) :
    |(1 / qb - 1 / qa) / η - (1 / pb - 1 / pa) / η| ≤ 4 * eΔ / c ^ 2 + 6 * BΔ * (e / c) / c ^ 2 := by
  have hε : 0 ≤ e / c := div_nonneg he hc.le
  have rel : ∀ q p : ℝ, c ≤ p → |q - p| ≤ e → |q - p| ≤ e / c * p := fun q p hp h => by
    refine h.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; exact mul_le_mul_of_nonneg_left hp he
  obtain ⟨hqa, hUa, hUua⟩ := CTG.Reals2.TimeAppendix4.inv_perturb qa pa c (e / c) hc hpa hε he2
    (rel qa pa hpa ha)
  obtain ⟨hqb, hUb, hUub⟩ := CTG.Reals2.TimeAppendix4.inv_perturb qb pb c (e / c) hc hpb hε he2
    (rel qb pb hpb hb)
  have hpa0 : 0 < pa := lt_of_lt_of_le hc hpa
  have hpb0 : 0 < pb := lt_of_lt_of_le hc hpb
  have hua : |1 / pa| ≤ 1 / c := by
    rw [abs_of_pos (by positivity)]; exact one_div_le_one_div_of_le hc hpa
  have hub : |1 / pb| ≤ 1 / c := by
    rw [abs_of_pos (by positivity)]; exact one_div_le_one_div_of_le hc hpb
  have eS : (1 / qb - 1 / qa) / η = (qb - qa) / η * (1 / qa * (1 / qb)) * (-1) := by
    rw [CTG.Reals2.TimeAppendix4.dq_inv qa qb η hqa.ne' hqb.ne']; field_simp
  have eP : (1 / pb - 1 / pa) / η = (pb - pa) / η * (1 / pa * (1 / pb)) * (-1) := by
    rw [CTG.Reals2.TimeAppendix4.dq_inv pa pb η hpa0.ne' hpb0.ne']; field_simp
  rw [eS, eP, ← sub_mul, abs_mul, abs_neg, abs_one, mul_one]
  have tQ : |1 / qa * (1 / qb) - 1 / pa * (1 / pb)| ≤ 2 * (e / c) / c * (2 / c) + 1 / c * (2 * (e / c) / c) :=
    (CTG.Reals2.TimeAppendix4.abs_mul_sub_mul_le _ _ _ _).trans
      (add_le_add (mul_le_mul hUua hUb (abs_nonneg _) (by positivity))
        (mul_le_mul hua hUub (abs_nonneg _) (by positivity)))
  have hQ : |1 / qa * (1 / qb)| ≤ 2 / c * (2 / c) := by
    rw [abs_mul]; exact mul_le_mul hUa hUb (abs_nonneg _) (by positivity)
  have t := (CTG.Reals2.TimeAppendix4.abs_mul_sub_mul_le ((qb - qa) / η) ((pb - pa) / η)
    (1 / qa * (1 / qb)) (1 / pa * (1 / pb))).trans
    (add_le_add (mul_le_mul hΔ hQ (abs_nonneg _) ((abs_nonneg _).trans hΔ))
      (mul_le_mul hBΔ tQ (abs_nonneg _) hBΔ0))
  refine t.trans (le_of_eq ?_)
  field_simp
  ring

/-- `1/q` against `1/p`: `|1/q − 1/p| ≤ 2(e/c)/c` and `q > 0`. -/
theorem inv_close (q p e c : ℝ) (hc : 0 < c) (hp : c ≤ p) (he : 0 ≤ e) (he2 : e / c ≤ 1 / 2)
    (h : |q - p| ≤ e) : 0 < q ∧ |1 / q - 1 / p| ≤ 2 * (e / c) / c := by
  have hε : 0 ≤ e / c := div_nonneg he hc.le
  have h' : |q - p| ≤ e / c * p := by
    refine h.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; exact mul_le_mul_of_nonneg_left hp he
  obtain ⟨h1, -, h3⟩ := CTG.Reals2.TimeAppendix4.inv_perturb q p c (e / c) hc hp hε he2 h'
  exact ⟨h1, h3⟩

end Steps345

/-! ### Steps 3, 4 and 5 assembled (abstract kernels on a measurable space) -/

section Assembly

variable {E : Type*} [MeasurableSpace E]

/-- Kernel of the population weighted average: `K(x,y) g(x,y) / p(y)`, `p = ∫ K(y,·) dm`. -/
def wKer (m : Measure E) (K g : E → E → ℝ) (x y : E) : ℝ := K x y * g x y * (1 / popAvg m K y)

/-- Sample weighted average `(1/N) Σ_j K(X_i,X_j) g(X_i,X_j) / q_j`, `q_j = (1/N) Σ_k K(X_j,X_k)`:
the numerator `𝒩_i` for `g(x,y) = f(y) − f(x)`, the denominator `𝒟_i` for `g = 1`. -/
def sampW {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (K g : E → E → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  avgN N (fun j => K (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N K j ω))

/-- Population weighted average `∫ K(x,y) g(x,y)/p(y) dm(y)`. -/
def popW (m : Measure E) (K g : E → E → ℝ) (x : E) : ℝ := popAvg m (wKer m K g) x

/-- Kernel of the difference quotient of the population weighted average (product rule):
`Δ_ηK · g / p_b + K_a · g · Δ_η(1/p)`. -/
def dKer (m : Measure E) (Ka Kb g : E → E → ℝ) (η : ℝ) (x y : E) : ℝ :=
  (Kb x y - Ka x y) / η * g x y * (1 / popAvg m Kb y)
    + Ka x y * g x y * ((1 / popAvg m Kb y - 1 / popAvg m Ka y) / η)

theorem sampW_inc {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (Ka Kb g : E → E → ℝ) (η : ℝ) (i : ℕ)
    (ω : Ω) :
    (sampW X N Kb g i ω - sampW X N Ka g i ω) / η
      = avgN N (fun j => (Kb (X i ω) (X j ω) - Ka (X i ω) (X j ω)) / η * g (X i ω) (X j ω)
            * (1 / sampAvg X N Kb j ω)
          + Ka (X i ω) (X j ω) * g (X i ω) (X j ω)
            * ((1 / sampAvg X N Kb j ω - 1 / sampAvg X N Ka j ω) / η)) := by
  unfold sampW avgN
  rw [← mul_sub, ← Finset.sum_sub_distrib, mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dKer_eq (m : Measure E) (Ka Kb g : E → E → ℝ) (η : ℝ) :
    dKer m Ka Kb g η = fun x z => (wKer m Kb g x z - wKer m Ka g x z) / η := by
  funext x z; unfold dKer wKer; ring

theorem dev_nonneg (N : ℕ) {B v L : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v) (hL : 0 ≤ L) :
    0 ≤ dev N B v L := by
  unfold dev; have := Real.sqrt_nonneg (N * v * L); positivity

/-- Error of `1/q_j` (from Step 2). -/
def err1 (N : ℕ) (BK vK c L : ℝ) : ℝ := 2 * (dev N BK vK L / c) / c

/-- Error of `Δ_η(1/q_j)` (from Step 2). -/
def err2 (N : ℕ) (BK vK BI vI c L : ℝ) : ℝ :=
  4 * dev N BI vI L / c ^ 2 + 6 * BI * (dev N BK vK L / c) / c ^ 2

/-- Error of the weighted average at one time (Steps 3/4, `|g| ≤ Bg`). -/
def errT (N : ℕ) (BK vK c L Bg : ℝ) : ℝ :=
  err1 N BK vK c L * (BK * Bg + dev N (BK * Bg) (Bg ^ 2 * vK) L)
    + dev N (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK)) L

/-- Error of the difference quotient of the weighted average (Steps 3/4, `|g| ≤ Bg`). -/
def errD (N : ℕ) (BK vK BI vI c L Bg : ℝ) : ℝ :=
  err1 N BK vK c L * (BI * Bg + dev N (BI * Bg) (Bg ^ 2 * vI) L)
    + err2 N BK vK BI vI c L * (BK * Bg + dev N (BK * Bg) (Bg ^ 2 * vK) L)
    + dev N (BI * Bg * (1 / c) + BK * Bg * (BI / c ^ 2))
        (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((BI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) L

/-- Exceptional event of Step 2 (three kernels: `K_a`, `K_b`, `Δ_ηK`). -/
def bad2 {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (m : Measure E) (Ka Kb : E → E → ℝ) (η BK vK BI vI L : ℝ) :
    Set Ω :=
  badSet X N m Ka BK vK L ∪ badSet X N m Kb BK vK L
    ∪ badSet X N m (fun x z => (Kb x z - Ka x z) / η) BI vI L

/-- Exceptional event of Steps 3/4 for one test kernel `g` (six kernels). -/
def bad34 {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (m : Measure E) (Ka Kb g : E → E → ℝ)
    (η BK vK BI vI c L Bg : ℝ) : Set Ω :=
  badSet X N m (fun x z => |Ka x z * g x z|) (BK * Bg) (Bg ^ 2 * vK) L
    ∪ badSet X N m (fun x z => |Kb x z * g x z|) (BK * Bg) (Bg ^ 2 * vK) L
    ∪ badSet X N m (fun x z => |(Kb x z - Ka x z) / η * g x z|) (BI * Bg) (Bg ^ 2 * vI) L
    ∪ badSet X N m (wKer m Ka g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK)) L
    ∪ badSet X N m (wKer m Kb g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK)) L
    ∪ badSet X N m (dKer m Ka Kb g η) (BI * Bg * (1 / c) + BK * Bg * (BI / c ^ 2))
        (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((BI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) L

variable {m : Measure E} [IsProbabilityMeasure m]

theorem inv_pop_meas (K : E → E → ℝ) (hK : Measurable fun p : E × E => K p.1 p.2) :
    Measurable fun p : E × E => 1 / popAvg m K p.2 :=
  measurable_const.div ((popAvg_measurable m K hK).comp measurable_snd)

theorem inv_pop_bd (K : E → E → ℝ) {c : ℝ} (hc : 0 < c) (hp : ∀ y, c ≤ popAvg m K y) (y : E) :
    |1 / popAvg m K y| ≤ 1 / c := by
  have := hp y
  rw [abs_of_pos (by have := lt_of_lt_of_le hc this; positivity)]
  exact one_div_le_one_div_of_le hc this

theorem popAvg_inc' (Ka Kb : E → E → ℝ) {BK vK : ℝ} (GKa : Good m Ka BK vK)
    (GKb : Good m Kb BK vK) (η : ℝ) (y : E) :
    (popAvg m Kb y - popAvg m Ka y) / η = popAvg m (fun x z => (Kb x z - Ka x z) / η) y :=
  (popAvg_inc m Ka Kb GKa.meas GKb.meas GKa.bd GKb.bd η y).symm

theorem W_bd (Ka Kb : E → E → ℝ) {BK vK BI vI c : ℝ} (GKa : Good m Ka BK vK)
    (GKb : Good m Kb BK vK) (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y) (y : E) :
    |(1 / popAvg m Kb y - 1 / popAvg m Ka y) / η| ≤ BI / c ^ 2 := by
  have ha := hpa y; have hb := hpb y
  have ha0 : 0 < popAvg m Ka y := lt_of_lt_of_le hc ha
  have hb0 : 0 < popAvg m Kb y := lt_of_lt_of_le hc hb
  rw [CTG.Reals2.TimeAppendix4.dq_inv _ _ η ha0.ne' hb0.ne', abs_div, abs_neg,
    popAvg_inc' Ka Kb GKa GKb η y, abs_of_pos (mul_pos ha0 hb0)]
  have h1 := popAvg_abs_le m _ GKi.bd y
  have hcc : c ^ 2 ≤ popAvg m Ka y * popAvg m Kb y := by
    rw [sq]; exact mul_le_mul ha hb hc.le ha0.le
  calc _ ≤ BI / (popAvg m Ka y * popAvg m Kb y) :=
        div_le_div_of_nonneg_right h1 (mul_pos ha0 hb0).le
    _ ≤ BI / c ^ 2 := div_le_div_of_nonneg_left (GKi.B_nonneg) (by positivity) hcc

/-- The six kernels of Steps 3/4 satisfy the template hypotheses. -/
theorem goods34 (Ka Kb g : E → E → ℝ) (η : ℝ) {BK vK BI vI c Bg : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg) :
    Good m (fun x z => |Ka x z * g x z|) (BK * Bg) (Bg ^ 2 * vK)
    ∧ Good m (fun x z => |Kb x z * g x z|) (BK * Bg) (Bg ^ 2 * vK)
    ∧ Good m (fun x z => |(Kb x z - Ka x z) / η * g x z|) (BI * Bg) (Bg ^ 2 * vI)
    ∧ Good m (wKer m Ka g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK))
    ∧ Good m (wKer m Kb g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK))
    ∧ Good m (dKer m Ka Kb g η) (BI * Bg * (1 / c) + BK * Bg * (BI / c ^ 2))
        (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((BI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) := by
  have hc1 : (0 : ℝ) ≤ 1 / c := by positivity
  have Ga := GKa.mul g hg Bg hBg hgb
  have Gb := GKb.mul g hg Bg hBg hgb
  have Gi := GKi.mul g hg Bg hBg hgb
  have hWm : Measurable fun p : E × E => (1 / popAvg m Kb p.2 - 1 / popAvg m Ka p.2) / η :=
    ((inv_pop_meas Kb GKb.meas).sub (inv_pop_meas Ka GKa.meas)).div_const η
  refine ⟨Ga.abs, Gb.abs, Gi.abs,
    Ga.mul (fun _ z => 1 / popAvg m Ka z) (inv_pop_meas Ka GKa.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Ka hc hpa z),
    Gb.mul (fun _ z => 1 / popAvg m Kb z) (inv_pop_meas Kb GKb.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Kb hc hpb z), ?_⟩
  exact (Gi.mul (fun _ z => 1 / popAvg m Kb z) (inv_pop_meas Kb GKb.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Kb hc hpb z)).add
    (Ga.mul (fun _ z => (1 / popAvg m Kb z - 1 / popAvg m Ka z) / η) hWm (BI / c ^ 2)
      (by have := GKi.B_nonneg; positivity)
      (fun x z => W_bd Ka Kb GKa GKb GKi hc hpa hpb z))

/-- Steps 3 and 4, deterministic part: outside the exceptional events of Steps 2–4, for every
`i < N`, the sample weighted averages at both times and their difference quotient are close to the
population versions. -/
theorem step34_det {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (Ka Kb g : E → E → ℝ)
    (η : ℝ) {BK vK BI vI c L Bg : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg)
    (hsmall : dev N BK vK L / c ≤ 1 / 2) (ω : Ω)
    (h2 : ω ∉ bad2 X N m Ka Kb η BK vK BI vI L)
    (h34 : ω ∉ bad34 X N m Ka Kb g η BK vK BI vI c L Bg) (i : ℕ) (hi : i < N) :
    |sampW X N Ka g i ω - popW m Ka g (X i ω)| ≤ errT N BK vK c L Bg
    ∧ |sampW X N Kb g i ω - popW m Kb g (X i ω)| ≤ errT N BK vK c L Bg
    ∧ |(sampW X N Kb g i ω - sampW X N Ka g i ω) / η
        - (popW m Kb g (X i ω) - popW m Ka g (X i ω)) / η| ≤ errD N BK vK BI vI c L Bg := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ := goods34 Ka Kb g η GKa GKb GKi hc hpa hpb hg hBg hgb
  simp only [bad2, bad34, mem_union, not_or] at h2 h34
  obtain ⟨⟨hKa, hKb⟩, hKi⟩ := h2
  obtain ⟨⟨⟨⟨⟨b1, b1b⟩, b2⟩, b3a⟩, b3b⟩, b4⟩ := h34
  have hBK := GKa.B_nonneg; have hvK := GKa.v_nonneg
  have hBI := GKi.B_nonneg; have hvI := GKi.v_nonneg
  have heQ := dev_nonneg N hBK hvK hL.le
  have he1 : 0 ≤ err1 N BK vK c L := by unfold err1; positivity
  have he2 : 0 ≤ err2 N BK vK BI vI c L := by
    unfold err2; have := dev_nonneg N hBI hvI hL.le; positivity
  -- weights at the two times
  have wa : ∀ j < N, |1 / sampAvg X N Ka j ω - 1 / popAvg m Ka (X j ω)| ≤ err1 N BK vK c L :=
    fun j hj => (inv_close _ _ _ c hc (hpa _) heQ hsmall (not_badSet hKa hj)).2
  have wb : ∀ j < N, |1 / sampAvg X N Kb j ω - 1 / popAvg m Kb (X j ω)| ≤ err1 N BK vK c L :=
    fun j hj => (inv_close _ _ _ c hc (hpb _) heQ hsmall (not_badSet hKb hj)).2
  have wΔ : ∀ j < N, |(1 / sampAvg X N Kb j ω - 1 / sampAvg X N Ka j ω) / η
      - (1 / popAvg m Kb (X j ω) - 1 / popAvg m Ka (X j ω)) / η| ≤ err2 N BK vK BI vI c L := by
    intro j hj
    have hΔ := not_badSet hKi hj
    rw [sampAvg_inc, ← popAvg_inc' Ka Kb GKa GKb η] at hΔ
    have hB := popAvg_abs_le m _ GKi.bd (X j ω)
    rw [← popAvg_inc' Ka Kb GKa GKb η] at hB
    exact inv_inc_perturb _ _ _ _ η _ _ c BI hc (hpa _) (hpb _) heQ hsmall hBI
      (not_badSet hKa hj) (not_badSet hKb hj) hΔ hB
  have P1a := (abs_le.1 (popAvg_abs_le m _ G1.bd (X i ω))).2
  have P1b := (abs_le.1 (popAvg_abs_le m _ G1b.bd (X i ω))).2
  have P1i := (abs_le.1 (popAvg_abs_le m _ G2.bd (X i ω))).2
  refine ⟨?_, ?_, ?_⟩
  · have h := weighted_det N hN (fun j => Ka (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Ka j ω) (fun j => 1 / popAvg m Ka (X j ω)) _ _ _ _ _ he1 wa
      (not_badSet b1 hi) (not_badSet b3a hi)
    refine h.trans ?_
    unfold errT
    have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
    gcongr
  · have h := weighted_det N hN (fun j => Kb (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Kb j ω) (fun j => 1 / popAvg m Kb (X j ω)) _ _ _ _ _ he1 wb
      (not_badSet b1b hi) (not_badSet b3b hi)
    refine h.trans ?_
    unfold errT
    gcongr
  · rw [sampW_inc]
    have hpop : (popW m Kb g (X i ω) - popW m Ka g (X i ω)) / η
        = popAvg m (dKer m Ka Kb g η) (X i ω) := by
      rw [dKer_eq]
      exact (popAvg_inc m (wKer m Ka g) (wKer m Kb g) G3a.meas G3b.meas G3a.bd G3b.bd η
        (X i ω)).symm
    rw [hpop]
    have h := weighted2_det N hN
      (fun j => (Kb (X i ω) (X j ω) - Ka (X i ω) (X j ω)) / η * g (X i ω) (X j ω))
      (fun j => Ka (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Kb j ω) (fun j => 1 / popAvg m Kb (X j ω))
      (fun j => (1 / sampAvg X N Kb j ω - 1 / sampAvg X N Ka j ω) / η)
      (fun j => (1 / popAvg m Kb (X j ω) - 1 / popAvg m Ka (X j ω)) / η)
      _ _ _ _ _ _ _ _ he1 he2 wb wΔ (not_badSet b2 hi) (not_badSet b1 hi) (not_badSet b4 hi)
    refine h.trans ?_
    unfold errD
    have := dev_nonneg N (mul_nonneg hBI hBg) (mul_nonneg (sq_nonneg Bg) hvI) hL.le
    have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
    gcongr

theorem bad34_prob {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb g : E → E → ℝ) (η : ℝ)
    {BK vK BI vI c L Bg : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg) :
    μ.real (bad34 X N m Ka Kb g η BK vK BI vI c L Bg) ≤ 6 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ := goods34 Ka Kb g η GKa GKb GKi hc hpa hpb hg hBg hgb
  have p := fun {F : E → E → ℝ} {B v : ℝ} (hG : Good m F B v) =>
    hG.prob X h_indep hX hlaw N hN hL
  unfold bad34
  refine (measureReal_union_le _ _).trans ?_
  refine (add_le_add (measureReal_union_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl)
    le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl)
    le_rfl) le_rfl) le_rfl).trans ?_
  linarith [p G1, p G1b, p G2, p G3a, p G3b, p G4]

theorem bad2_prob {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb : E → E → ℝ) (η : ℝ)
    {BK vK BI vI L : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hL : 0 < L) :
    μ.real (bad2 X N m Ka Kb η BK vK BI vI L) ≤ 3 * (N * (2 * Real.exp (-L))) := by
  unfold bad2
  refine (measureReal_union_le _ _).trans ?_
  refine (add_le_add (measureReal_union_le _ _) le_rfl).trans ?_
  linarith [GKa.prob X h_indep hX hlaw N hN hL, GKb.prob X h_indep hX hlaw N hN hL,
    GKi.prob X h_indep hX hlaw N hN hL]

/-- Population bound of the weighted average and of its difference quotient. -/
theorem popW_bd (Ka Kb g : E → E → ℝ) (η : ℝ) {BK vK BI vI c Bg : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg)
    (x : E) :
    |popW m Ka g x| ≤ BK * Bg * (1 / c)
    ∧ |(popW m Kb g x - popW m Ka g x) / η| ≤ BI * Bg * (1 / c) + BK * Bg * (BI / c ^ 2) := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ := goods34 Ka Kb g η GKa GKb GKi hc hpa hpb hg hBg hgb
  refine ⟨popAvg_abs_le m _ G3a.bd x, ?_⟩
  have hpop : (popW m Kb g x - popW m Ka g x) / η = popAvg m (dKer m Ka Kb g η) x := by
    rw [dKer_eq]
    exact (popAvg_inc m (wKer m Ka g) (wKer m Kb g) G3a.meas G3b.meas G3a.bd G3b.bd η x).symm
  rw [hpop]; exact popAvg_abs_le m _ G4.bd x

/-- The final error of Step 5 (the right-hand side of `quotient_dq_perturb`). -/
def err5 (N : ℕ) (BK vK BI vI c L Bf cD : ℝ) : ℝ :=
  let a := errT N BK vK c L Bf + errD N BK vK BI vI c L Bf
  let ε := errT N BK vK c L 1 / cD
  let ε' := errD N BK vK BI vI c L 1
  let B := BK * Bf * (1 / c) + (BI * Bf * (1 / c) + BK * Bf * (BI / c ^ 2))
  let C := BI * 1 * (1 / c) + BK * 1 * (BI / c ^ 2)
  2 * a / cD + 2 * B * ε / cD + 4 * (a * (C + ε') + B * ε') / cD ^ 2 + 6 * B * C * ε / cD ^ 2

/-- **Steps 2–5 of `prop:dotLN-diff`, abstract form.**  Independent points with law `m`, two
kernels `K_a`, `K_b` (the kernel at the two times) with `Δ_ηK = (K_b − K_a)/η`, a test kernel
`g` (in the paper `g(x,y) = f(y) − f(x)`), `|g| ≤ B_f`.  HYPOTHESES: the template bounds
(`Good`) for `K_a`, `K_b` (constants `B_K`, `v_K`) and `Δ_ηK` (`B_I`, `v_I`); the lower bound
`p_τ ≥ c` of the population normalisations; the lower bound `c_D` of the population
denominators `𝒟_τ = ∫ K_τ/p_τ`; and the two smallness conditions (relative errors `≤ 1/2`).
Then, outside an event of probability at most `15 · N · 2e^{−L}`, for every `i < N` the
difference quotient of the sample quotient `𝒩_i/𝒟_i` differs from that of the population
quotient at `X_i` by at most `err5`. -/
theorem step5 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb gf : E → E → ℝ) (η : ℝ)
    {BK vK BI vI c L Bf cD : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hg : Measurable fun p : E × E => gf p.1 p.2) (hBf : 0 ≤ Bf) (hgb : ∀ x z, |gf x z| ≤ Bf)
    (hcD : 0 < cD) (hDa : ∀ x, cD ≤ popW m Ka (fun _ _ => 1) x)
    (hDb : ∀ x, cD ≤ popW m Kb (fun _ _ => 1) x)
    (hsmall : dev N BK vK L / c ≤ 1 / 2) (hsmallD : errT N BK vK c L 1 / cD ≤ 1 / 2) :
    μ.real {ω | ∃ i < N, err5 N BK vK BI vI c L Bf cD
        < |(sampW X N Kb gf i ω / sampW X N Kb (fun _ _ => 1) i ω
              - sampW X N Ka gf i ω / sampW X N Ka (fun _ _ => 1) i ω) / η
          - (popW m Kb gf (X i ω) / popW m Kb (fun _ _ => 1) (X i ω)
              - popW m Ka gf (X i ω) / popW m Ka (fun _ _ => 1) (X i ω)) / η|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  set g1 : E → E → ℝ := fun _ _ => 1
  have hg1 : Measurable fun p : E × E => g1 p.1 p.2 := measurable_const
  have hg1b : ∀ x z, |g1 x z| ≤ 1 := fun x z => by simp [g1]
  have hsub : {ω | ∃ i < N, err5 N BK vK BI vI c L Bf cD
        < |(sampW X N Kb gf i ω / sampW X N Kb g1 i ω
              - sampW X N Ka gf i ω / sampW X N Ka g1 i ω) / η
          - (popW m Kb gf (X i ω) / popW m Kb g1 (X i ω)
              - popW m Ka gf (X i ω) / popW m Ka g1 (X i ω)) / η|}
      ⊆ bad2 X N m Ka Kb η BK vK BI vI L ∪ bad34 X N m Ka Kb gf η BK vK BI vI c L Bf
        ∪ bad34 X N m Ka Kb g1 η BK vK BI vI c L 1 := by
    intro ω ⟨i, hi, hlt⟩
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨h2, h34f⟩, h341⟩ := hcon
    obtain ⟨eNa, -, eΔN⟩ := step34_det X N hN Ka Kb gf η GKa GKb GKi hc hL hpa hpb hg hBf hgb
      hsmall ω h2 h34f i hi
    obtain ⟨eDa, eDb, eΔD⟩ := step34_det X N hN Ka Kb g1 η GKa GKb GKi hc hL hpa hpb hg1
      zero_le_one hg1b hsmall ω h2 h341 i hi
    obtain ⟨bn, bx⟩ := popW_bd Ka Kb gf η GKa GKb GKi hc hpa hpb hg hBf hgb (X i ω)
    obtain ⟨-, by'⟩ := popW_bd Ka Kb g1 η GKa GKb GKi hc hpa hpb hg1 zero_le_one hg1b (X i ω)
    have hBK := GKa.B_nonneg; have hBI := GKi.B_nonneg
    have hvK := GKa.v_nonneg; have hvI := GKi.v_nonneg
    have heQ := dev_nonneg N hBK hvK hL.le
    have he1 : 0 ≤ err1 N BK vK c L := by unfold err1; positivity
    have he2 : 0 ≤ err2 N BK vK BI vI c L := by
      unfold err2; have := dev_nonneg N hBI hvI hL.le; positivity
    have hT : ∀ Bg, 0 ≤ Bg → 0 ≤ errT N BK vK c L Bg := fun Bg hBg => by
      unfold errT
      have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
      have := dev_nonneg N (mul_nonneg (mul_nonneg hBK hBg) (by positivity : (0:ℝ) ≤ 1 / c))
        (mul_nonneg (sq_nonneg (1 / c)) (mul_nonneg (sq_nonneg Bg) hvK)) hL.le
      positivity
    have hD : ∀ Bg, 0 ≤ Bg → 0 ≤ errD N BK vK BI vI c L Bg := fun Bg hBg => by
      unfold errD
      have := dev_nonneg N (mul_nonneg hBI hBg) (mul_nonneg (sq_nonneg Bg) hvI) hL.le
      have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
      have := dev_nonneg N (B := BI * Bg * (1 / c) + BK * Bg * (BI / c ^ 2))
        (v := 2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((BI / c ^ 2) ^ 2 * (Bg ^ 2 * vK)))
        (by positivity) (by positivity) hL.le
      positivity
    set a := errT N BK vK c L Bf + errD N BK vK BI vI c L Bf with ha
    set ε := errT N BK vK c L 1 / cD with hε
    set ε' := errD N BK vK BI vI c L 1 with hε'
    set B := BK * Bf * (1 / c) + (BI * Bf * (1 / c) + BK * Bf * (BI / c ^ 2)) with hB
    set C := BI * 1 * (1 / c) + BK * 1 * (BI / c ^ 2) with hC
    have hTf := hT Bf hBf; have hDf := hD Bf hBf
    have hrel : ∀ (Dv dv : ℝ), cD ≤ dv → |Dv - dv| ≤ errT N BK vK c L 1 → |Dv - dv| ≤ ε * dv :=
      fun Dv dv hdv h => by
        refine h.trans ?_
        rw [hε, div_mul_eq_mul_div, le_div_iff₀ hcD]
        exact mul_le_mul_of_nonneg_left hdv (hT 1 zero_le_one)
    have hda := hDa (X i ω); have hdb := hDb (X i ω)
    have rDa := hrel _ _ hda eDa; have rDb := hrel _ _ hdb eDb
    have hεnn : 0 ≤ ε := div_nonneg (hT 1 zero_le_one) hcD.le
    obtain ⟨hDa0, -, -⟩ := CTG.Reals2.TimeAppendix4.inv_perturb _ _ cD ε hcD hda hεnn hsmallD rDa
    obtain ⟨hDb0, -, -⟩ := CTG.Reals2.TimeAppendix4.inv_perturb _ _ cD ε hcD hdb hεnn hsmallD rDb
    have hda0 : 0 < popW m Ka g1 (X i ω) := lt_of_lt_of_le hcD hda
    have hdb0 : 0 < popW m Kb g1 (X i ω) := lt_of_lt_of_le hcD hdb
    have hq := CTG.Reals2.TimeAppendix4.quotient_dq_perturb
      ((sampW X N Kb gf i ω - sampW X N Ka gf i ω) / η)
      ((popW m Kb gf (X i ω) - popW m Ka gf (X i ω)) / η)
      (sampW X N Ka gf i ω) (popW m Ka gf (X i ω))
      ((sampW X N Kb g1 i ω - sampW X N Ka g1 i ω) / η)
      ((popW m Kb g1 (X i ω) - popW m Ka g1 (X i ω)) / η)
      (sampW X N Ka g1 i ω) (popW m Ka g1 (X i ω))
      (sampW X N Kb g1 i ω) (popW m Kb g1 (X i ω)) a B C cD ε ε' hcD hda hdb hεnn hsmallD
      (by positivity) (by positivity) (by positivity) (hD 1 zero_le_one) rDa rDb
      (eΔN.trans (by linarith)) (eNa.trans (by linarith)) eΔD
      (bx.trans (by have : 0 ≤ BK * Bf * (1 / c) := by positivity
                    linarith))
      (bn.trans (by have : 0 ≤ BI * Bf * (1 / c) + BK * Bf * (BI / c ^ 2) := by positivity
                    linarith))
      by'
    rw [← CTG.Reals2.TimeAppendix4.dq_quotient _ _ _ _ η hDa0.ne' hDb0.ne',
      ← CTG.Reals2.TimeAppendix4.dq_quotient _ _ _ _ η hda0.ne' hdb0.ne'] at hq
    have : err5 N BK vK BI vI c L Bf cD
        = 2 * a / cD + 2 * B * ε / cD + 4 * (a * (C + ε') + B * ε') / cD ^ 2
          + 6 * B * C * ε / cD ^ 2 := rfl
    rw [this] at hlt
    linarith
  calc μ.real _ ≤ μ.real (bad2 X N m Ka Kb η BK vK BI vI L
        ∪ bad34 X N m Ka Kb gf η BK vK BI vI c L Bf
        ∪ bad34 X N m Ka Kb g1 η BK vK BI vI c L 1) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (bad2 X N m Ka Kb η BK vK BI vI L ∪ bad34 X N m Ka Kb gf η BK vK BI vI c L Bf)
        + μ.real (bad34 X N m Ka Kb g1 η BK vK BI vI c L 1) := measureReal_union_le _ _
    _ ≤ (μ.real (bad2 X N m Ka Kb η BK vK BI vI L)
          + μ.real (bad34 X N m Ka Kb gf η BK vK BI vI c L Bf))
        + μ.real (bad34 X N m Ka Kb g1 η BK vK BI vI c L 1) :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ 3 * (N * (2 * Real.exp (-L))) + 6 * (N * (2 * Real.exp (-L)))
        + 6 * (N * (2 * Real.exp (-L))) := by
        linarith [bad2_prob X h_indep hX hlaw N hN Ka Kb η GKa GKb GKi hL,
          bad34_prob X h_indep hX hlaw N hN Ka Kb gf η GKa GKb GKi hc hL hpa hpb hg hBf hgb,
          bad34_prob X h_indep hX hlaw N hN Ka Kb g1 η GKa GKb GKi hc hL hpa hpb hg1
            zero_le_one hg1b]
    _ = 15 * (N * (2 * Real.exp (-L))) := by ring

end Assembly

/-! ### Lower bound of the population denominator for a non-negative kernel -/

section Denominator

variable {E : Type*} [MeasurableSpace E] {m : Measure E} [IsProbabilityMeasure m]

/-- For `K ≥ 0` with `|K| ≤ B_K` and `p = ∫K(y,·) ≥ c`: `𝒟(x) = ∫ K(x,y)/p(y) dm(y) ≥ c/B_K`. -/
theorem popW_one_ge (K : E → E → ℝ) {BK vK c : ℝ} (GK : Good m K BK vK) (hc : 0 < c)
    (hK0 : ∀ x y, 0 ≤ K x y) (hp : ∀ y, c ≤ popAvg m K y) (x : E) :
    c / BK ≤ popW m K (fun _ _ => 1) x := by
  have hBK : 0 < BK := lt_of_lt_of_le hc ((hp x).trans (abs_le.1 (popAvg_abs_le m K GK.bd x)).2)
  have hKx : Measurable (K x) := GK.meas.comp (measurable_const.prodMk measurable_id)
  have hpm : Measurable fun y => 1 / popAvg m K y :=
    measurable_const.div (popAvg_measurable m K GK.meas)
  have hpos : ∀ y, 0 < popAvg m K y := fun y => lt_of_lt_of_le hc (hp y)
  have hle : ∀ y, 1 / BK ≤ 1 / popAvg m K y := fun y =>
    one_div_le_one_div_of_le (hpos y) (abs_le.1 (popAvg_abs_le m K GK.bd y)).2
  have hint1 : Integrable (fun y => K x y * (1 / BK)) m :=
    (integrable_of_bound m K GK.meas GK.bd x).mul_const _
  have hint2 : Integrable (fun y => K x y * 1 * (1 / popAvg m K y)) m :=
    bdd_integrable m _ ((hKx.mul measurable_const).mul hpm) (BK * (1 / c)) fun y => by
      rw [mul_one, abs_mul]
      exact mul_le_mul (GK.bd x y) (inv_pop_bd K hc hp y) (abs_nonneg _) hBK.le
  have h1 : ∫ y, K x y * (1 / BK) ∂m ≤ popW m K (fun _ _ => 1) x :=
    integral_mono hint1 hint2 fun y => by
      show K x y * (1 / BK) ≤ K x y * 1 * (1 / popAvg m K y)
      rw [mul_one]; exact mul_le_mul_of_nonneg_left (hle y) (hK0 x y)
  rw [integral_mul_const] at h1
  have h2 : c / BK ≤ (∫ y, K x y ∂m) * (1 / BK) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right (hp x) hBK.le
  linarith

/-- `step5` for a non-negative kernel, with `c_D = c/B_K` (the lower bound of the denominators is
derived, not assumed). -/
theorem step5_nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb gf : E → E → ℝ) (η : ℝ)
    {BK vK BI vI c L Bf : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hBK : 0 < BK) (hKa0 : ∀ x y, 0 ≤ Ka x y) (hKb0 : ∀ x y, 0 ≤ Kb x y)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hg : Measurable fun p : E × E => gf p.1 p.2) (hBf : 0 ≤ Bf) (hgb : ∀ x z, |gf x z| ≤ Bf)
    (hsmall : dev N BK vK L / c ≤ 1 / 2) (hsmallD : errT N BK vK c L 1 / (c / BK) ≤ 1 / 2) :
    μ.real {ω | ∃ i < N, err5 N BK vK BI vI c L Bf (c / BK)
        < |(sampW X N Kb gf i ω / sampW X N Kb (fun _ _ => 1) i ω
              - sampW X N Ka gf i ω / sampW X N Ka (fun _ _ => 1) i ω) / η
          - (popW m Kb gf (X i ω) / popW m Kb (fun _ _ => 1) (X i ω)
              - popW m Ka gf (X i ω) / popW m Ka (fun _ _ => 1) (X i ω)) / η|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  exact step5 X h_indep hX hlaw N hN Ka Kb gf η GKa GKb GKi hc hL hpa hpb hg hBf hgb
    (div_pos hc hBK) (fun x => popW_one_ge Ka GKa hc hKa0 hpa x)
    (fun x => popW_one_ge Kb GKb hc hKb0 hpb x) hsmall hsmallD

end Denominator

/-! ### Steps 2–5 for a time-dependent metric on a compact connected manifold -/

section ManifoldSteps

open Bundle Manifold CTG.ManifoldDistance

variable {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EE H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle EE (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {s : Set ℝ}

theorem vKern_nonneg (d : ℕ) {Am r₀ ξ A : ℝ} (hAm : 0 ≤ Am) (hξ : 0 < ξ) :
    0 ≤ vKern d Am r₀ ξ A := by
  unfold vKern
  have : 0 ≤ ∑' n : ℕ, A ^ 2 * (((n : ℝ) + 1) ^ 0 * Real.exp (-2 * n)) * ((n : ℝ) + 1) ^ d :=
    tsum_nonneg fun n => by positivity
  positivity

theorem vInc_nonneg (κ : ℝ) (d : ℕ) {Am r₀ ξ A a b : ℝ} (hAm : 0 ≤ Am) (hξ : 0 < ξ) :
    0 ≤ vInc κ d Am r₀ ξ A a b := by
  unfold vInc
  have : 0 ≤ ∑' n : ℕ, (2 * (κ * |b - a|) * A) ^ 2
      * (((n : ℝ) + 1) ^ 2 * Real.exp (-(2 * Real.exp (-1)) * n)) * ((n : ℝ) + 1) ^ d :=
    tsum_nonneg fun n => by positivity
  positivity

/-- The kernel at one time satisfies the template hypotheses with `B = A`, `v = vKern`, under the
upper volume-growth HYPOTHESIS at that time (uniform in the centre). -/
theorem good_kern (G : TimeMetric I M s) {a₀ τ : ℝ} (ha₀ : a₀ ∈ s) (hτ : τ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hgrowth : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y τ < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h : ℝ → ℝ) (hhc : Continuous h) (A : ℝ) (hA : 0 ≤ A)
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) :
    Good m (kern G h ξ τ) A (vKern d Am r₀ ξ A) where
  meas := kern_measurable G ha₀ hτ hcont h hhc ξ
  B_nonneg := hA
  v_nonneg := vKern_nonneg d hAm hξ
  bd := kern_abs_le G h A ξ τ hξ hh hA
  var := fun x => kern_sq_integral G ha₀ hτ hcont m d Am r₀ ξ hAm hr₀ hξ x (hgrowth x) h hhc A hA hh

/-- The difference quotient of the kernel satisfies the template hypotheses with `B = 2κA`,
`v = vInc`, under the upper growth HYPOTHESIS at time `a`. -/
theorem good_inc (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hgrowth : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) :
    Good m (fun x z => (kern G h ξ b x z - kern G h ξ a x z) / (b - a)) (2 * G.κ * A)
      (vInc G.κ d Am r₀ ξ A a b) where
  meas := by
    have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
    exact ((kern_measurable G ha₀ hb hcont h hhc ξ).sub
      (kern_measurable G ha₀ ha hcont h hhc ξ)).div_const _
  B_nonneg := by have := G.κ_nonneg; positivity
  v_nonneg := vInc_nonneg _ d hAm hξ
  bd := kernInc_abs_le G ha₀ hcont ha hb hab hne h h' A ξ hA hξ hder hbd
  var := fun x => kernInc_sq_integral G ha₀ hcont ha hb hab m d Am r₀ ξ hAm hr₀ hξ x (hgrowth x)
    h h' A hA hder hbd

/-- **Step 2 of `prop:dotLN-diff` on the manifold.**  Independent sample points with law `m`;
kernel `K^τ(x,y) = h(d_τ(x,y)/ξ)` of a `TimeMetric` with `|h(t)| ≤ A e^{−t}`, `|h'(t)| ≤ A e^{−t}`;
upper volume-growth HYPOTHESIS `m{y : d_τ(x,y) < r} ≤ A_m r^d` (`0 < r ≤ r₀`) at `τ = a` and
`τ = b`, uniformly in `x`.  Then with probability at least `1 − 3N·2e^{−L}`, for all `i < N`:
`|q^a_i − q^a(X_i)| ≤ dev(A, v_K)`, `|q^b_i − q^b(X_i)| ≤ dev(A, v_K)` and
`|Δq_i − Δq(X_i)| ≤ dev(2κA, v_I)`, where `dev(B,v) = (4BL + 2√(NvL) + 2B)/N` (the last `2B/N`
is the self-term `j = i`), `v_K = vKern = O(ξ^d)` and `v_I = vInc = O(κ² ξ^d)`. -/
theorem npoint_step2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (L : ℝ) (hL : 0 < L) :
    μ.real {ω | ∃ i < N,
        dev N A (vKern d Am r₀ ξ A) L < |sampNorm G h ξ a X N i ω - popNorm G h ξ a m (X i ω)|
        ∨ dev N A (vKern d Am r₀ ξ A) L
            < |sampNorm G h ξ b X N i ω - popNorm G h ξ b m (X i ω)|
        ∨ dev N (2 * G.κ * A) (vInc G.κ d Am r₀ ξ A a b) L
            < |(sampNorm G h ξ b X N i ω - sampNorm G h ξ a X N i ω) / (b - a)
              - (popNorm G h ξ b m (X i ω) - popNorm G h ξ a m (X i ω)) / (b - a)|}
      ≤ 3 * (N * (2 * Real.exp (-L))) := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have GKa := good_kern G ha₀ ha hcont m d Am r₀ ξ hAm hr₀ hξ hga h hhc A hA hh
  have GKb := good_kern G ha₀ hb hcont m d Am r₀ ξ hAm hr₀ hξ hgb h hhc A hA hh
  have GKi := good_inc G ha₀ hcont ha hb hab hne m d Am r₀ ξ hAm hr₀ hξ hga h h' A hA hder hbd
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (bad2_prob X h_indep hX hlaw N hN _ _ (b - a) GKa GKb GKi hL)
  intro ω ⟨i, hi, hor⟩
  simp only [bad2, mem_union, badSet, mem_setOf_eq]
  rcases hor with h1 | h1 | h1
  · exact Or.inl (Or.inl ⟨i, hi, h1⟩)
  · exact Or.inl (Or.inr ⟨i, hi, h1⟩)
  · refine Or.inr ⟨i, hi, ?_⟩
    rw [sampAvg_inc, popAvg_inc m _ _ GKa.meas GKb.meas GKa.bd GKb.bd]
    exact h1

/-- **Steps 2–5 of `prop:dotLN-diff` on the manifold.**  In addition to the hypotheses of
`npoint_step2`: `h ≥ 0`; a bounded measurable test function `f` (`|f| ≤ B_f`), test kernel
`g(x,y) = f(y) − f(x)`; the lower bound `q^τ(x) ≥ c` of the population normalisations at both times
(HYPOTHESIS; in the paper `c ξ^d ≤ q_ξ`, from a lower volume-growth bound and a positive density);
and the two smallness conditions (relative errors `≤ 1/2`).  Then, with probability at least
`1 − 15N·2e^{−L}`, for all `i < N` the difference quotient in time of the sample quotient
`𝒩_i/𝒟_i` (the random-walk average `Σ_j K_ij f_j/q_j / Σ_j K_ij/q_j` minus `f_i`) differs from
that of the population quotient at `X_i` by at most `err5` (explicit, built from the Bernstein
deviations `dev`).  NOT included: Taylor expansion of the population quantities, the division by
`c_h ξ²/2`, and Step 6. -/
theorem npoint_step5 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (f : M → ℝ) (hf : Measurable f) (Bf : ℝ) (hBf : 0 ≤ Bf) (hfb : ∀ x, |f x| ≤ Bf)
    (c : ℝ) (hc : 0 < c)
    (hqa : ∀ y, c ≤ popNorm G h ξ a m y) (hqb : ∀ y, c ≤ popNorm G h ξ b m y)
    (L : ℝ) (hL : 0 < L)
    (hsmall : dev N A (vKern d Am r₀ ξ A) L / c ≤ 1 / 2)
    (hsmallD : errT N A (vKern d Am r₀ ξ A) c L 1 / (c / A) ≤ 1 / 2) :
    μ.real {ω | ∃ i < N,
        err5 N A (vKern d Am r₀ ξ A) (2 * G.κ * A) (vInc G.κ d Am r₀ ξ A a b) c L (2 * Bf) (c / A)
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have GKa := good_kern G ha₀ ha hcont m d Am r₀ ξ hAm hr₀ hξ hga h hhc A hA.le hh
  have GKb := good_kern G ha₀ hb hcont m d Am r₀ ξ hAm hr₀ hξ hgb h hhc A hA.le hh
  have GKi := good_inc G ha₀ hcont ha hb hab hne m d Am r₀ ξ hAm hr₀ hξ hga h h' A hA.le hder hbd
  exact step5_nonneg X h_indep hX hlaw N hN (kern G h ξ a) (kern G h ξ b)
    (fun x y => f y - f x) (b - a) GKa GKb GKi hc hL hA (fun x y => hh0 _) (fun x y => hh0 _)
    hqa hqb (hf.comp measurable_snd |>.sub (hf.comp measurable_fst)) (by positivity)
    (fun x z => by
      calc |f z - f x| ≤ |f z| + |f x| := abs_sub _ _
        _ ≤ 2 * Bf := by linarith [hfb x, hfb z]) hsmall hsmallD

end ManifoldSteps

end CTG.NPoint
