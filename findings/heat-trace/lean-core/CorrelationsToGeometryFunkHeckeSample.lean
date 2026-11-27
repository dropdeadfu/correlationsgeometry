/-
Twenty-seventh file: sampled walk on the sphere `S²` at FIXED scale.  Imports
`CorrelationsToGeometryFunkHecke` (compiled module under `.tools/leanbuild`); namespace `CTG.FunkHecke.Sample`;
check with `./check_funk_hecke_sample.sh`.
Independent points with the normalised surface measure, kernel `gk ξ ⟨x,y⟩`, walk WITH self-loop.  The population
degree is constant (`zonalOp_one`); `walk_one_step`: for continuous `f`, the sampled walk at all sample points is
within an explicit error of `Pinf (gk ξ) f`, outside an event of probability `4N exp(−(N−1)η²/(2F²))` (Hoeffding,
conditioning on the centre point); `walk_harmonic`: for `f = Re (a·y)^l` the sampled function is an approximate
eigenvector with value `sphS ξ l`; `walk_harmonic_ae`: almost surely, for every `ε`, eventually in `N`.
NOT formalised: powers of the sampled walk, the trace and the eigenvalues of the sample matrix, the walk without
self-loops, a rate in `ξ`, measurability of the exceptional sets.  The sample in the almost-sure statement is
nested (the first `N` points of one sequence).  No `sorry`, no `axiom`, no `native_decide`.
Written by a sub-task of an AI session on 26 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHecke

/-!
# A138: samples on the sphere at FIXED scale

Scratch block (namespace `CTG.FunkHecke.Sample`), importing only Mathlib and the seventeenth Lean
file (`CorrelationsToGeometryFunkHecke`).

Setting: `X : ℕ → Ω → S²` independent, measurable, each with law `σ` (normalised surface
measure), the angular Gaussian kernel `K(x,y) = gk ξ ⟨x,y⟩` at a FIXED scale `ξ`, and the sample
walk WITH self-loop
`(P_N f)(X_i) = ∑_{j<N} K(X_i,X_j) f(X_j) / ∑_{j<N} K(X_i,X_j)`.

* `sigma_real_univ`, instance `IsProbabilityMeasure sigma`.
* Stage (1): `zonalOp_one` (the population degree `q(x) = ∫ K(x,y) dσ(y) = sphZ ξ / 2` is constant
  and positive), `hoeffding_fn` (Hoeffding at a fixed point for a bounded function of the sample),
  `cond_one` (the same with the centre a sample point `X_i`, by conditioning on `X_i`).
* Stage (2): `ratio_det` (deterministic), `walk_one_step`: with probability at least
  `1 - 4 N exp(-(N-1) η² / (2 F²))`, for ALL `i < N`,
  `|P_N f(X_i) - P_∞ f(X_i)| ≤ 4 (η (1+F) + 2F/(N-1)) / sphZ ξ`.
* Stage (3): `walk_harmonic` (the sampled function `Re (a·y)^l`, `a` isotropic, is an approximate
  eigenvector of the sample walk with value `s_l = sphS ξ l`), `walk_harmonic_ae` (almost surely,
  for every `ε > 0`, eventually in `N`, for all `i < N`, error `≤ ε`).

No hypotheses beyond: independence, measurability and law of the points; continuity and a bound
`|f| ≤ F` (with `1 ≤ F`) for the test function; `N ≥ 2`; `0 < η ≤ sphZ ξ / 4`.
-/

open MeasureTheory ProbabilityTheory Set Metric Real Filter
open scoped RealInnerProductSpace ENNReal NNReal

namespace CTG.FunkHecke.Sample

open CTG.FunkHecke

/-! ## Preliminaries -/

theorem sigma_real_univ : sigma.real univ = 1 := by
  have h := integral_sigma (fun _ => (1:ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [h, sigma0_real_univ]
  field_simp

instance : IsProbabilityMeasure sigma :=
  ⟨by rw [← ofReal_measureReal, sigma_real_univ, ENNReal.ofReal_one]⟩

instance : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

theorem integrable_cont (f : S2 → ℝ) (hf : Continuous f) : Integrable f sigma := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => hC y (Set.mem_univ y))

/-- The kernel `K(x,y) = gk ξ ⟨x,y⟩` on `S² × S²`. -/
noncomputable def Kx (ξ : ℝ) (x y : S2) : ℝ := gk ξ ⟪(x : E3), (y : E3)⟫

theorem Kx_pos (ξ : ℝ) (x y : S2) : 0 < Kx ξ x y := Real.exp_pos _

theorem Kx_le_one (ξ : ℝ) (x y : S2) : Kx ξ x y ≤ 1 :=
  (le_abs_self _).trans (abs_gk_le ξ _)

theorem Kx_continuous (ξ : ℝ) : Continuous (fun p : S2 × S2 => Kx ξ p.1 p.2) :=
  (gk_continuous ξ).comp ((continuous_subtype_val.comp continuous_fst).inner
    (continuous_subtype_val.comp continuous_snd))

/-! ## Stage (1): the population degree is constant -/

/-- The population degree `q(x) = ∫ K(x,y) dσ(y)` equals `sphZ ξ / 2 > 0` for every `x`. -/
theorem zonalOp_one (ξ : ℝ) (x : S2) : zonalOp (gk ξ) (fun _ => 1) x = (1/2) * sphZ ξ := by
  have h0 : ∫ t in (-1:ℝ)..1, gk ξ t = sphZ ξ := by
    have := zonal_weight ξ (fun _ => 1) continuous_const
    simpa only [mul_one] using this
  rw [zonalOp_const _ (gk_continuous ξ).measurable, h0, mul_one]

theorem degree_eq (ξ : ℝ) (x : S2) : ∫ z, Kx ξ x z ∂sigma = (1/2) * sphZ ξ := by
  have := zonalOp_one ξ x
  unfold zonalOp at this
  simpa only [mul_one] using this

theorem degree_pos (ξ : ℝ) (x : S2) : 0 < ∫ z, Kx ξ x z ∂sigma := by
  rw [degree_eq]; have := sphZ_pos ξ; positivity

/-- A parametric integral of a jointly continuous bounded function is continuous. -/
theorem param_continuous (H : S2 → S2 → ℝ) (hH : Continuous (fun p : S2 × S2 => H p.1 p.2))
    {B : ℝ} (hHB : ∀ x z, |H x z| ≤ B) : Continuous (fun x => ∫ z, H x z ∂sigma) := by
  refine continuous_of_dominated (bound := fun _ => B) (fun x => ?_) (fun x => ?_)
    (integrable_const _) ?_
  · exact (hH.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hHB x z
  · exact Filter.Eventually.of_forall fun z => hH.comp (continuous_id.prodMk continuous_const)

/-! ## Hoeffding for a bounded function of the sample -/

section Hoeffding

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem hoeffding_one (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma)
    (h : S2 → ℝ) (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B) (hhB : ∀ z, |h z| ≤ B)
    (T : Finset ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ j ∈ T, (h (X j ω) - ∫ z, h z ∂sigma)}
      ≤ Real.exp (-ε ^ 2 / (2 * (T.card * B ^ 2))) := by
  have hmean : ∀ j, ∫ ω, h (X j ω) ∂μ = ∫ z, h z ∂sigma := fun j => by
    rw [← hlaw j, integral_map (hX j).aemeasurable hh.aestronglyMeasurable]
  have hsub : ∀ j ∈ T, HasSubgaussianMGF (fun ω => h (X j ω) - ∫ z, h z ∂sigma)
      ((‖B - -B‖₊ / 2) ^ 2) μ := by
    intro j _
    have := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := fun ω => h (X j ω)) (a := -B) (b := B)
      (hh.comp (hX j)).aemeasurable (Filter.Eventually.of_forall fun ω => abs_le.mp (hhB _))
    rwa [hmean j] at this
  have hind' : iIndepFun (fun j ω => h (X j ω) - ∫ z, h z ∂sigma) μ :=
    hind.comp (fun _ y => h y - ∫ z, h z ∂sigma) (fun _ => hh.sub_const _)
  have H := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind' hsub hε
  refine H.trans (le_of_eq ?_)
  congr 3
  have hc : (((‖B - -B‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = B ^ 2 := by
    rw [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs,
      show B - -B = 2 * B by ring, abs_of_nonneg (by positivity)]
    push_cast; ring
  push_cast
  rw [Finset.sum_const, nsmul_eq_mul, ← hc]
  push_cast; ring

/-- **Hoeffding at a fixed point.** For a measurable `h` with `|h| ≤ B` and any finite index set `T`:
`P(|∑_{j∈T} (h(X_j) - ∫h dσ)| ≥ ε) ≤ 2 exp(-ε²/(2 |T| B²))`. -/
theorem hoeffding_fn (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma)
    (h : S2 → ℝ) (hh : Measurable h) {B : ℝ} (hB : 0 ≤ B) (hhB : ∀ z, |h z| ≤ B)
    (T : Finset ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T, (h (X j ω) - ∫ z, h z ∂sigma)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * (T.card * B ^ 2))) := by
  have h1 := hoeffding_one X hind hX hlaw h hh hB hhB T hε
  have h2 := hoeffding_one X hind hX hlaw (fun z => -h z) hh.neg hB
    (fun z => by rw [abs_neg]; exact hhB z) T hε
  have hsub : {ω | ε ≤ |∑ j ∈ T, (h (X j ω) - ∫ z, h z ∂sigma)|}
      ⊆ {ω | ε ≤ ∑ j ∈ T, (h (X j ω) - ∫ z, h z ∂sigma)}
        ∪ {ω | ε ≤ ∑ j ∈ T, (-h (X j ω) - ∫ z, -h z ∂sigma)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have e : ∑ j ∈ T, (-h (X j ω) - ∫ z, -h z ∂sigma)
        = -∑ j ∈ T, (h (X j ω) - ∫ z, h z ∂sigma) := by
      rw [integral_neg, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

/-- Conditioning on part of an independent sample (copy of `sample_cond_bound` of the second
Lean file, which this file does not import). -/
theorem sample_cond_bound {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j)) (S T : Finset ℕ) (hST : Disjoint S T)
    (A : Set ((S → E) × (T → E))) (hA : MeasurableSet A) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ u : S → E, μ.real {ω | (u, fun j : T => X j ω) ∈ A} ≤ q) :
    μ.real {ω | ((fun i : S => X i ω), (fun j : T => X j ω)) ∈ A} ≤ q := by
  set U : Ω → (S → E) := fun ω (i : S) => X i ω
  set V : Ω → (T → E) := fun ω (j : T) => X j ω
  have hU : Measurable U := measurable_pi_lambda _ fun i => hX i
  have hV : Measurable V := measurable_pi_lambda _ fun j => hX j
  have hind : IndepFun U V μ := h_indep.indepFun_finset S T hST hX
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).mp hind
  have hUV : Measurable fun ω => (U ω, V ω) := hU.prodMk hV
  have h1 : μ {ω | (U ω, V ω) ∈ A} = (μ.map fun ω => (U ω, V ω)) A := by
    rw [Measure.map_apply hUV hA]; rfl
  haveI : IsProbabilityMeasure (μ.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  haveI : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hq' : ∀ u, μ {ω | (u, V ω) ∈ A} ≤ ENNReal.ofReal q := fun u => by
    have := hq u
    rw [Measure.real] at this
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hq0).mpr this
  have key : μ {ω | (U ω, V ω) ∈ A} ≤ ENNReal.ofReal q := by
    rw [h1, hmap, Measure.prod_apply hA]
    calc ∫⁻ u, (μ.map V) (Prod.mk u ⁻¹' A) ∂(μ.map U)
        ≤ ∫⁻ _u, ENNReal.ofReal q ∂(μ.map U) := by
          refine lintegral_mono fun u => ?_
          rw [Measure.map_apply hV (measurable_prodMk_left hA)]
          exact hq' u
      _ = ENNReal.ofReal q := by simp
  rw [Measure.real]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hq0).mp key

/-- **Hoeffding centred at a sample point.** For a jointly continuous `H` with `|H| ≤ B`, an index
`i ∉ T`: `P(|∑_{j∈T} (H(X_i,X_j) - ∫ H(X_i,z) dσ(z))| ≥ ε) ≤ 2 exp(-ε²/(2|T|B²))`. -/
theorem cond_one (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma)
    (H : S2 → S2 → ℝ) (hH : Continuous (fun p : S2 × S2 => H p.1 p.2))
    {B : ℝ} (hB : 0 ≤ B) (hHB : ∀ x z, |H x z| ≤ B)
    (i : ℕ) (T : Finset ℕ) (hi : i ∉ T) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T, (H (X i ω) (X j ω) - ∫ z, H (X i ω) z ∂sigma)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * (T.card * B ^ 2))) := by
  set M : S2 → ℝ := fun x => ∫ z, H x z ∂sigma
  have hM : Continuous M := param_continuous H hH hHB
  have hi0 : i ∈ ({i} : Finset ℕ) := Finset.mem_singleton_self i
  have hST : Disjoint ({i} : Finset ℕ) T := Finset.disjoint_singleton_left.mpr hi
  set A : Set ((({i} : Finset ℕ) → S2) × (T → S2)) :=
    {p | ε ≤ |∑ j : T, (H (p.1 ⟨i, hi0⟩) (p.2 j) - M (p.1 ⟨i, hi0⟩))|}
  have hcont : Continuous (fun p : (({i} : Finset ℕ) → S2) × (T → S2) =>
      |∑ j : T, (H (p.1 ⟨i, hi0⟩) (p.2 j) - M (p.1 ⟨i, hi0⟩))|) := by
    refine continuous_abs.comp (continuous_finset_sum _ fun j _ => ?_)
    have c1 : Continuous (fun p : (({i} : Finset ℕ) → S2) × (T → S2) => p.1 ⟨i, hi0⟩) :=
      (continuous_apply (⟨i, hi0⟩ : ({i} : Finset ℕ))).comp continuous_fst
    have c2 : Continuous (fun p : (({i} : Finset ℕ) → S2) × (T → S2) => p.2 j) :=
      (continuous_apply j).comp continuous_snd
    exact (hH.comp (c1.prodMk c2)).sub (hM.comp c1)
  have hA : MeasurableSet A := measurableSet_le measurable_const hcont.measurable
  have key := sample_cond_bound X hind hX {i} T hST A hA
    (q := 2 * Real.exp (-ε ^ 2 / (2 * (T.card * B ^ 2)))) (by positivity) (fun u => by
    have hset : {ω | (u, fun j : T => X j ω) ∈ A}
        = {ω | ε ≤ |∑ j ∈ T, (H (u ⟨i, hi0⟩) (X j ω) - ∫ z, H (u ⟨i, hi0⟩) z ∂sigma)|} := by
      ext ω
      simp only [A, Set.mem_setOf_eq, M]
      rw [Finset.sum_coe_sort T (fun j => H (u ⟨i, hi0⟩) (X j ω) - ∫ z, H (u ⟨i, hi0⟩) z ∂sigma)]
    rw [hset]
    exact hoeffding_fn X hind hX hlaw (H (u ⟨i, hi0⟩))
      (hH.comp (continuous_const.prodMk continuous_id)).measurable hB (hHB _) T hε)
  have hset : {ω | ε ≤ |∑ j ∈ T, (H (X i ω) (X j ω) - ∫ z, H (X i ω) z ∂sigma)|}
      = {ω | ((fun k : ({i} : Finset ℕ) => X k ω), (fun j : T => X j ω)) ∈ A} := by
    ext ω
    simp only [A, Set.mem_setOf_eq, M]
    rw [Finset.sum_coe_sort T (fun j => H (X i ω) (X j ω) - ∫ z, H (X i ω) z ∂sigma)]
  rw [hset]
  exact key

end Hoeffding

/-! ## Stage (2): one step of the sample walk -/

/-- Deterministic ratio estimate. -/
theorem ratio_det {AT BT k fx a b n F η : ℝ} (hb : 0 < b) (hn : 0 < n) (hF : 0 ≤ F)
    (ha : |a| ≤ F * b) (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hfx : |fx| ≤ F)
    (hA : |AT - n * a| ≤ n * η) (hB : |BT - n * b| ≤ n * η) (hη : η ≤ b / 2) :
    |(AT + k * fx) / (BT + k) - a / b| ≤ 2 * (η * (1 + F) + 2 * F / n) / b := by
  have hBT : n * b / 2 ≤ BT := by
    have := (abs_le.mp hB).1
    nlinarith
  have hBpos : 0 < BT + k := by nlinarith [mul_pos hn hb]
  have hη0 : 0 ≤ η := by
    have := abs_nonneg (AT - n * a)
    nlinarith
  rw [div_sub_div _ _ hBpos.ne' hb.ne', abs_div, abs_of_pos (mul_pos hBpos hb),
    div_le_iff₀ (mul_pos hBpos hb)]
  have e : (AT + k * fx) * b - (BT + k) * a
      = (AT - n * a) * b + k * (fx * b - a) - (BT - n * b) * a := by ring
  have h1 : |(AT - n * a) * b| ≤ n * η * b := by
    rw [abs_mul, abs_of_pos hb]; exact mul_le_mul_of_nonneg_right hA hb.le
  have h2 : |k * (fx * b - a)| ≤ 2 * F * b := by
    rw [abs_mul, abs_of_nonneg hk0]
    have : |fx * b - a| ≤ 2 * F * b := by
      calc |fx * b - a| ≤ |fx * b| + |a| := abs_sub _ _
        _ = |fx| * b + |a| := by rw [abs_mul, abs_of_pos hb]
        _ ≤ F * b + F * b := add_le_add (mul_le_mul_of_nonneg_right hfx hb.le) ha
        _ = 2 * F * b := by ring
    calc k * |fx * b - a| ≤ 1 * (2 * F * b) :=
          mul_le_mul hk1 this (abs_nonneg _) zero_le_one
      _ = 2 * F * b := one_mul _
  have h3 : |(BT - n * b) * a| ≤ n * η * (F * b) := by
    rw [abs_mul]; exact mul_le_mul hB ha (abs_nonneg _) (by positivity)
  have hnum : |(AT + k * fx) * b - (BT + k) * a| ≤ b * (n * η * (1 + F) + 2 * F) := by
    rw [e]
    calc |(AT - n * a) * b + k * (fx * b - a) - (BT - n * b) * a|
        ≤ |(AT - n * a) * b + k * (fx * b - a)| + |(BT - n * b) * a| := abs_sub _ _
      _ ≤ |(AT - n * a) * b| + |k * (fx * b - a)| + |(BT - n * b) * a| := by
          gcongr; exact abs_add_le _ _
      _ ≤ n * η * b + 2 * F * b + n * η * (F * b) := by gcongr
      _ = b * (n * η * (1 + F) + 2 * F) := by ring
  have hR0 : 0 ≤ 2 * (η * (1 + F) + 2 * F / n) / b := by positivity
  calc |(AT + k * fx) * b - (BT + k) * a| ≤ b * (n * η * (1 + F) + 2 * F) := hnum
    _ = 2 * (η * (1 + F) + 2 * F / n) / b * (n * b / 2 * b) := by
        field_simp
    _ ≤ 2 * (η * (1 + F) + 2 * F / n) / b * ((BT + k) * b) := by
        apply mul_le_mul_of_nonneg_left _ hR0
        apply mul_le_mul_of_nonneg_right _ hb.le
        linarith

/-- The sample walk WITH self-loop: `(P_N f)(X_i) = ∑_{j<N} K(X_i,X_j) f(X_j) / ∑_{j<N} K(X_i,X_j)`. -/
noncomputable def walk {Ω : Type*} (ξ : ℝ) (f : S2 → ℝ) (X : ℕ → Ω → S2) (N : ℕ) (ω : Ω)
    (i : ℕ) : ℝ :=
  (∑ j ∈ Finset.range N, Kx ξ (X i ω) (X j ω) * f (X j ω))
    / ∑ j ∈ Finset.range N, Kx ξ (X i ω) (X j ω)

theorem zonal_eq (ξ : ℝ) (f : S2 → ℝ) (x : S2) :
    zonalOp (gk ξ) f x = ∫ z, Kx ξ x z * f z ∂sigma := by
  unfold zonalOp Kx; rfl

theorem abs_zonal_le (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f) {F : ℝ} (hfF : ∀ y, |f y| ≤ F)
    (x : S2) : |zonalOp (gk ξ) f x| ≤ F * ∫ z, Kx ξ x z ∂sigma := by
  have hc : Continuous (fun z : S2 => Kx ξ x z) := by
    unfold Kx
    exact (gk_continuous ξ).comp (continuous_const.inner continuous_subtype_val)
  have hK : Integrable (fun z => Kx ξ x z) sigma := integrable_cont _ hc
  have hKf : Integrable (fun z => Kx ξ x z * f z) sigma := integrable_cont _ (hc.mul hf)
  rw [zonal_eq, ← integral_const_mul]
  rw [abs_le]
  constructor
  · rw [← integral_neg]
    refine integral_mono (hK.const_mul F).neg hKf fun z => ?_
    have := (abs_le.mp (hfF z)).1
    have := (Kx_pos ξ x z).le
    simp only; nlinarith
  · refine integral_mono hKf (hK.const_mul F) fun z => ?_
    have := (abs_le.mp (hfF z)).2
    have := (Kx_pos ξ x z).le
    simp only; nlinarith

section Walk

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **One step of the sample walk on `S²` at fixed scale.** For a continuous `f` with
`|f| ≤ F`, `1 ≤ F`, `N ≥ 2`, `0 < η ≤ sphZ ξ / 4`: outside an event of probability at most
`4 N exp(-(N-1) η² / (2 F²))`, for ALL `i < N`,
`|P_N f(X_i) - P_∞ f(X_i)| ≤ 4 (η (1+F) + 2F/(N-1)) / sphZ ξ`. -/
theorem walk_one_step (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f)
    {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F) {N : ℕ} (hN : 2 ≤ N)
    {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) :
    μ.real {ω | ∃ i < N, 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk ξ f X N ω i - Pinf (gk ξ) f (X i ω)|}
      ≤ 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
  have hF0 : 0 ≤ F := by linarith
  have hZ := sphZ_pos ξ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set n : ℝ := (N : ℝ) - 1 with hn
  have hnpos : 0 < n := by linarith
  set ε : ℝ := n * η
  have hε : 0 ≤ ε := by positivity
  set H1 : S2 → S2 → ℝ := fun x z => Kx ξ x z * f z
  set H2 : S2 → S2 → ℝ := fun x z => Kx ξ x z
  have hH1 : Continuous (fun p : S2 × S2 => H1 p.1 p.2) :=
    (Kx_continuous ξ).mul (hf.comp continuous_snd)
  have hH2 : Continuous (fun p : S2 × S2 => H2 p.1 p.2) := Kx_continuous ξ
  have hH1B : ∀ x z, |H1 x z| ≤ F := fun x z => by
    simp only [H1]; rw [abs_mul, abs_of_pos (Kx_pos ξ x z)]
    calc Kx ξ x z * |f z| ≤ 1 * F :=
          mul_le_mul (Kx_le_one ξ x z) (hfF z) (abs_nonneg _) zero_le_one
      _ = F := one_mul F
  have hH2B : ∀ x z, |H2 x z| ≤ F := fun x z => by
    simp only [H2]; rw [abs_of_pos (Kx_pos ξ x z)]; linarith [Kx_le_one ξ x z]
  set E1 : ℕ → Set Ω := fun i =>
    {ω | ε ≤ |∑ j ∈ (Finset.range N).erase i, (H1 (X i ω) (X j ω) - ∫ z, H1 (X i ω) z ∂sigma)|}
  set E2 : ℕ → Set Ω := fun i =>
    {ω | ε ≤ |∑ j ∈ (Finset.range N).erase i, (H2 (X i ω) (X j ω) - ∫ z, H2 (X i ω) z ∂sigma)|}
  have hcard : ∀ i ∈ Finset.range N, (((Finset.range N).erase i).card : ℝ) = n := by
    intro i hi
    rw [Finset.card_erase_of_mem hi, Finset.card_range, Nat.cast_sub (by omega)]
    simp [hn]
  have hexp : 2 * Real.exp (-ε ^ 2 / (2 * (n * F ^ 2)))
      = 2 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
    congr 2
    simp only [ε, hn]
    have : (0:ℝ) < (N:ℝ) - 1 := by linarith
    field_simp
  have hP1 : ∀ i ∈ Finset.range N, μ.real (E1 i)
      ≤ 2 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
    intro i hi
    have := cond_one X hind hX hlaw H1 hH1 hF0 hH1B i ((Finset.range N).erase i)
      (Finset.notMem_erase i _) hε
    rwa [hcard i hi, hexp] at this
  have hP2 : ∀ i ∈ Finset.range N, μ.real (E2 i)
      ≤ 2 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
    intro i hi
    have := cond_one X hind hX hlaw H2 hH2 hF0 hH2B i ((Finset.range N).erase i)
      (Finset.notMem_erase i _) hε
    rwa [hcard i hi, hexp] at this
  have hsub : {ω | ∃ i < N, 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk ξ f X N ω i - Pinf (gk ξ) f (X i ω)|}
      ⊆ ⋃ i ∈ Finset.range N, (E1 i ∪ E2 i) := by
    intro ω hω
    obtain ⟨i, hi, hlt⟩ := hω
    have hiN : i ∈ Finset.range N := Finset.mem_range.mpr hi
    simp only [Set.mem_iUnion]
    refine ⟨i, hiN, ?_⟩
    by_contra hnot
    simp only [Set.mem_union, E1, E2, Set.mem_setOf_eq, not_or, not_le] at hnot
    obtain ⟨h1, h2⟩ := hnot
    set x := X i ω
    set a := zonalOp (gk ξ) f x
    set b := ∫ z, Kx ξ x z ∂sigma
    have hb : b = (1/2) * sphZ ξ := degree_eq ξ x
    have hbpos : 0 < b := degree_pos ξ x
    have hbq : zonalOp (gk ξ) (fun _ => 1) x = b := by rw [zonalOp_one, hb]
    have hT : ∀ (g : ℕ → ℝ), ∑ j ∈ Finset.range N, g j
        = ∑ j ∈ (Finset.range N).erase i, g j + g i := fun g =>
      (Finset.sum_erase_add _ _ hiN).symm
    set AT := ∑ j ∈ (Finset.range N).erase i, Kx ξ x (X j ω) * f (X j ω)
    set BT := ∑ j ∈ (Finset.range N).erase i, Kx ξ x (X j ω)
    have hA : |AT - n * a| ≤ n * η := by
      have e : ∑ j ∈ (Finset.range N).erase i, (H1 x (X j ω) - ∫ z, H1 x z ∂sigma)
          = AT - n * a := by
        have ha : ∫ z, H1 x z ∂sigma = a := (zonal_eq ξ f x).symm
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard i hiN, ha]
      rw [← e]; exact h1.le
    have hB : |BT - n * b| ≤ n * η := by
      have e : ∑ j ∈ (Finset.range N).erase i, (H2 x (X j ω) - ∫ z, H2 x z ∂sigma)
          = BT - n * b := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard i hiN]
      rw [← e]; exact h2.le
    have hwalk : walk ξ f X N ω i = (AT + Kx ξ x x * f x) / (BT + Kx ξ x x) := by
      unfold walk
      rw [hT (fun j => Kx ξ (X i ω) (X j ω) * f (X j ω)),
        hT (fun j => Kx ξ (X i ω) (X j ω))]
    have hPinf : Pinf (gk ξ) f x = a / b := by unfold Pinf; rw [hbq]
    have hfin := ratio_det hbpos hnpos hF0 (abs_zonal_le ξ f hf hfF x) (Kx_pos ξ x x).le
      (Kx_le_one ξ x x) (hfF x) hA hB (by rw [hb]; linarith)
    rw [hwalk, hPinf] at hlt
    have : 2 * (η * (1 + F) + 2 * F / n) / b = 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ := by
      rw [hb, hn]; field_simp; ring
    rw [this] at hfin
    exact absurd hfin (not_le.mpr hlt)
  calc _ ≤ μ.real (⋃ i ∈ Finset.range N, (E1 i ∪ E2 i)) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.range N, μ.real (E1 i ∪ E2 i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, 4 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        calc μ.real (E1 i ∪ E2 i) ≤ μ.real (E1 i) + μ.real (E2 i) := measureReal_union_le _ _
          _ ≤ _ := by linarith [hP1 i hi, hP2 i hi]
    _ = 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end Walk

/-! ## Stage (3): sampled spherical harmonics are approximate eigenvectors -/

theorem harm_cont (p q : E3) (l : ℕ) : Continuous (fun y : S2 => (cdot p q (y : E3) ^ l).re) :=
  Complex.continuous_re.comp (((continuous_cdot p q).comp continuous_subtype_val).pow l)

/-- The bound used for `Re (a·y)^l`. -/
noncomputable def harmF (p q : E3) (l : ℕ) : ℝ := max 1 ((‖p‖ + ‖q‖) ^ l)

theorem harm_bound (p q : E3) (l : ℕ) (y : S2) : |(cdot p q (y : E3) ^ l).re| ≤ harmF p q l := by
  refine le_trans ?_ (le_max_right _ _)
  calc |(cdot p q (y : E3) ^ l).re| ≤ ‖cdot p q (y : E3) ^ l‖ := Complex.abs_re_le_norm _
    _ = ‖cdot p q (y : E3)‖ ^ l := norm_pow _ _
    _ ≤ (‖p‖ + ‖q‖) ^ l := pow_le_pow_left₀ (norm_nonneg _)
        (norm_cdot_le p q y (mem_sphere_zero_iff_norm.1 y.2)) l

theorem one_le_harmF (p q : E3) (l : ℕ) : 1 ≤ harmF p q l := le_max_left _ _

section Harmonic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The sampled spherical harmonic is an approximate eigenvector of the sample walk.** For
`a = p + i q` isotropic, `f(y) = Re (a·y)^l`, `F = harmF p q l`, `N ≥ 2`, `0 < η ≤ sphZ ξ / 4`:
outside an event of probability at most `4 N exp(-(N-1) η² / (2 F²))`, for ALL `i < N`,
`|P_N f(X_i) - s_l f(X_i)| ≤ 4 (η (1+F) + 2F/(N-1)) / sphZ ξ` with `s_l = sphS ξ l`. -/
theorem walk_harmonic (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (p q : E3) (hpq : Isotropic p q) (l : ℕ)
    {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) :
    μ.real {ω | ∃ i < N,
        4 * (η * (1 + harmF p q l) + 2 * harmF p q l / (N - 1)) / sphZ ξ
        < |walk ξ (fun y => (cdot p q (y : E3) ^ l).re) X N ω i
            - sphS ξ l * (cdot p q (X i ω : E3) ^ l).re|}
      ≤ 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * harmF p q l ^ 2)) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (walk_one_step X hind hX hlaw ξ _ (harm_cont p q l)
    (one_le_harmF p q l) (harm_bound p q l) hN hη hηb)
  rintro ω ⟨i, hi, h⟩
  exact ⟨i, hi, by rwa [Pinf_harmonic ξ p q hpq l]⟩

/-- Borel–Cantelli for bounds `C N e^{-cN}` (valid for `N ≥ 2`). -/
theorem bc_lin (B : ℕ → Set Ω) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hB : ∀ N, 2 ≤ N → μ.real (B N) ≤ C * (N * Real.exp (-(c * N)))) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ω ∉ B N := by
  set B' : ℕ → Set Ω := fun N => if 2 ≤ N then B N else ∅
  have hsum : Summable (fun N : ℕ => C * ((N:ℝ) ^ 1 * Real.exp (-c * N))) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 1 hc).mul_left C
  have hle : ∀ N, μ (B' N) ≤ ENNReal.ofReal (C * ((N:ℝ) ^ 1 * Real.exp (-c * N))) := by
    intro N
    by_cases h : 2 ≤ N
    · simp only [B', if_pos h]
      rw [← ofReal_measureReal]
      apply ENNReal.ofReal_le_ofReal
      have := hB N h
      rw [pow_one, neg_mul]; exact this
    · simp [B', if_neg h]
  have hfin : ∑' N, μ (B' N) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω, eventually_ge_atTop 2] with N hN h2
  simpa [B', if_pos h2] using hN

/-- Almost surely, for a fixed `η`, eventually for all `i < N` the error of `walk_harmonic`. -/
theorem walk_harmonic_ae_eta (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (p q : E3)
    (hpq : Isotropic p q) (l : ℕ) {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ∀ i < N,
      |walk ξ (fun y => (cdot p q (y : E3) ^ l).re) X N ω i
          - sphS ξ l * (cdot p q (X i ω : E3) ^ l).re|
        ≤ 4 * (η * (1 + harmF p q l) + 2 * harmF p q l / (N - 1)) / sphZ ξ := by
  set F := harmF p q l
  have hF : 0 < F := lt_of_lt_of_le zero_lt_one (one_le_harmF p q l)
  set c : ℝ := η ^ 2 / (2 * F ^ 2)
  have hc : 0 < c := by positivity
  have h := bc_lin (μ := μ) (fun N => {ω | ∃ i < N,
      4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk ξ (fun y => (cdot p q (y : E3) ^ l).re) X N ω i
            - sphS ξ l * (cdot p q (X i ω : E3) ^ l).re|})
    (C := 4 * Real.exp c) (by positivity) hc (fun N hN => by
      refine (walk_harmonic X hind hX hlaw ξ p q hpq l hN hη hηb).trans (le_of_eq ?_)
      have : Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) = Real.exp c * Real.exp (-(c * N)) := by
        rw [← Real.exp_add]; congr 1; simp only [c]; field_simp; ring
      rw [this]; ring)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with N hN
  intro i hi
  by_contra hlt
  exact hN ⟨i, hi, not_le.mp hlt⟩

/-- **Almost surely, the sampled spherical harmonic becomes an exact eigenvector in the limit**:
for every `ε > 0`, eventually in `N`, `|P_N f(X_i) - s_l f(X_i)| ≤ ε` for all `i < N`
(sample walk with self-loop, fixed scale `ξ`). -/
theorem walk_harmonic_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (p q : E3)
    (hpq : Isotropic p q) (l : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |walk ξ (fun y => (cdot p q (y : E3) ^ l).re) X N ω i
          - sphS ξ l * (cdot p q (X i ω : E3) ^ l).re| ≤ ε := by
  set F := harmF p q l
  have hF1 : 1 ≤ F := one_le_harmF p q l
  set Z := sphZ ξ
  have hZ : 0 < Z := sphZ_pos ξ
  set ηk : ℕ → ℝ := fun k => min (Z / 4) (1 / ((k:ℝ) + 1))
  have hηk : ∀ k, 0 < ηk k := fun k => lt_min (by positivity) (by positivity)
  have hall := ae_all_iff.mpr (fun k => walk_harmonic_ae_eta X hind hX hlaw ξ p q hpq l
    (hηk k) (min_le_left _ _))
  filter_upwards [hall] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (8 * (1 + F) / (Z * ε))
  obtain ⟨M, hM⟩ := exists_nat_gt (16 * F / (Z * ε) + 1)
  filter_upwards [hω k, eventually_ge_atTop (M + 2)] with N hN hNM
  intro i hi
  refine (hN i hi).trans ?_
  have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hη1 : ηk k * ((k:ℝ) + 1) ≤ 1 := by
    have : ηk k ≤ 1 / ((k:ℝ) + 1) := min_le_right _ _
    rwa [le_div_iff₀ hk1] at this
  have hkZ : 8 * (1 + F) < ((k:ℝ) + 1) * (Z * ε) := by
    rw [div_lt_iff₀ (by positivity)] at hk; nlinarith
  have hNr : (M:ℝ) + 2 ≤ N := by exact_mod_cast hNM
  have hMZ : 16 * F < ((M:ℝ) - 1 + 1) * (Z * ε) := by
    have : 16 * F / (Z * ε) < M := by linarith
    rw [div_lt_iff₀ (by positivity)] at this; nlinarith
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  have e : 4 * (ηk k * (1 + F) + 2 * F / (N - 1)) / Z
      = 4 * ηk k * (1 + F) / Z + 8 * F / (((N:ℝ) - 1) * Z) := by
    field_simp; ring
  rw [e]
  have t1 : 4 * ηk k * (1 + F) / Z ≤ ε / 2 := by
    rw [div_le_iff₀ hZ]
    refine le_of_mul_le_mul_left ?_ hk1
    have := mul_le_mul_of_nonneg_left hη1 (show (0:ℝ) ≤ 4 * (1 + F) by linarith)
    nlinarith
  have t2 : 8 * F / (((N:ℝ) - 1) * Z) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : ((M:ℝ) - 1 + 1) * (Z * ε) ≤ ((N:ℝ) - 1) * (Z * ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  linarith

end Harmonic

end CTG.FunkHecke.Sample
