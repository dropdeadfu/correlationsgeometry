/-
From Correlations to Geometry -- fourteenth Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the ninth file `CorrelationsToGeometryManifold.lean`.  Content: the volume-growth bounds that the
ninth and the twelfth file use as HYPOTHESES are derived here for a compact Riemannian manifold WITHOUT
constructing a Riemannian volume measure: the reference measure is the n-dimensional Hausdorff measure of the
Riemannian distance (Mathlib's `hausdorffMeasure`); that it equals the Riemannian volume up to a constant is
NOT proven.  Stages: local bi-Lipschitz comparison of the Riemannian distance with the chart distance; Hausdorff
measure of small balls between `a r^n` and `A r^n`; uniform constants on a compact manifold; for a sampling law
`m` with `m₀ μ ≤ m ≤ m₁ μ`: the upper growth hypothesis of `IntegralBounds` (also for a `TimeMetric`) and a
lower bound for the population normalisation.  The manifold is modelled on `Fin n → ℝ` with the sup norm,
without boundary.  Check with `cd lean && ./check_volume.sh` (against the COMPILED ninth file).
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryManifold

/-!
# Volume growth of small Riemannian balls without a Riemannian volume measure (block A124)

Scratch file of the project "From Correlations to Geometry" (not part of `lean/`).

Route (A): the measure is the `n`-dimensional Hausdorff measure `μH[n]` of the Riemannian distance
(Mathlib's `MeasureTheory.Measure.hausdorffMeasure`); its identification with the Riemannian volume is
NOT proven.  Stages:
(1) `local_upper_comparison`, `local_lower_comparison`: local bi-Lipschitz comparison of the
    Riemannian distance with the distance in the extended chart (any model, any `E`);
(2) `local_hausdorff_ball`: `a rⁿ ≤ μH[n](B(y,r)) ≤ A rⁿ` near each point, for manifolds modelled on
    `ℝⁿ` with the sup norm, without boundary (`𝓘(ℝ, Fin n → ℝ)`);
(3) `hausdorff_ball_uniform`: the same uniformly on a compact manifold;
(4) `sampling_upper_growth`, `sampling_upper_growth_time`, `sampling_normalisation_lower`: for a
    sampling law with `m₀ μH[n] ≤ m ≤ m₁ μH[n]`, the upper growth hypothesis of `IntegralBounds`
    (for the Riemannian distance and for the distance at one time of a `TimeMetric`) and the lower
    bound `q(x) ≥ h₀ m₀ a ξⁿ` of the population normalisation.
No `sorry`, no `axiom`, no `native_decide`.
-/

open Set MeasureTheory Bundle Manifold Filter Metric
open scoped Manifold ENNReal ContDiff Topology NNReal

noncomputable section

namespace CTG.ManifoldVolume

section LocalComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
attribute [local instance] normedSpaceTangentSpaceVectorSpace

omit [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] in
/-- Chart estimate along a path that stays in a set where the derivative of the extended chart is
bounded by `C`. -/
theorem chart_edist_le_pathELength (x : M) (C : ℝ≥0) (u : Set M)
    (hu : u ⊆ {y | ‖mfderiv% (extChartAt I x) y‖ₑ < C}) (uc : u ⊆ (chartAt H x).source)
    {γ : ℝ → M} (hγ : CMDiff[Icc 0 1] 1 γ) (hγu : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ u) :
    edist (extChartAt I x (γ 0)) (extChartAt I x (γ 1)) ≤ C * pathELength I γ 0 1 := by
  let γ' := extChartAt I x ∘ γ
  have hC : CMDiff[Icc 0 1] 1 γ' :=
    contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt H x).source)
      hγ (fun t' ht' ↦ uc <| hγu t' ht')
  rw [edist_comm, edist_eq_enorm_sub]
  calc
      ‖γ' 1 - γ' 0‖ₑ
    _ ≤ ∫⁻ t' in Icc 0 1, ‖derivWithin γ' (Icc 0 1) t'‖ₑ := by
      apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ zero_le_one
      rwa [← contMDiffOn_iff_contDiffOn]
    _ = ∫⁻ t' in Icc 0 1, ‖mfderiv[Icc 0 1] γ' t' 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t' in Icc 0 1, C * ‖mfderiv[Icc 0 1] γ t' 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc (fun t' ht' ↦ ?_)
      have : mfderiv[Icc 0 1] γ' t' =
          (mfderiv% (extChartAt I x) (γ t')) ∘L (mfderiv[Icc 0 1] γ t') := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (uc (hγu t' ht'))
        · exact (hγ.mdifferentiableOn one_ne_zero) _ ht'
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one _ ht'
      have : mfderiv[Icc 0 1] γ' t' 1 =
          (mfderiv% (extChartAt I x) (γ t')) (mfderiv[Icc 0 1] γ t' 1) :=
        congr($this 1)
      rw [this]
      apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
      gcongr
      exact (hu (hγu t' ht')).le
    _ = C * pathELength I γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]

/-- (Stage 1, upper) Around any point `x`, the inverse extended chart is Lipschitz from the
Euclidean distance of the chart to the Riemannian distance, on a ball of the chart (intersected
with `range I`): `d(φ⁻¹p, φ⁻¹q) ≤ C ‖p − q‖`.  The two-point version of Mathlib's
`eventually_riemannianEDist_le_edist_extChartAt` (same proof, segment from `p` to `q`). -/
theorem local_upper_comparison (x : M) :
    ∃ C > (0:ℝ≥0), ∃ r > (0:ℝ),
      ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∧
      ∀ p ∈ ball (extChartAt I x x) r ∩ range I, ∀ q ∈ ball (extChartAt I x x) r ∩ range I,
        riemannianEDist I ((extChartAt I x).symm p) ((extChartAt I x).symm q)
          ≤ C * edist p q := by
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C} :=
    mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  refine ⟨r, r_pos, fun p hp => (hr hp).1, fun p hp q hq => ?_⟩
  let η := ContinuousAffineMap.lineMap (R := ℝ) p q
  set γ := (extChartAt I x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
     ← segment_eq_image_lineMap, η]
    apply Subset.trans _ hr
    exact ((convex_ball _ _).inter I.convex_range).segment_subset hp hq
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have : riemannianEDist I ((extChartAt I x).symm p) ((extChartAt I x).symm q)
      ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  apply this.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have : mfderiv[Icc 0 1] γ t =
      (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range I] (extChartAt I x).symm (η t)) (mfderiv[Icc 0 1] η t 1) := congr($this 1)
  rw [this]
  apply (ContinuousLinearMap.le_opNorm_enorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

variable [RegularSpace M]

/-- (Stage 1, lower) Around any point `x` there are a neighbourhood `W`, a radius `c > 0` and a
constant `C > 0` such that for `y ∈ W` and `d(y,z) < c` the point `z` lies in the chart at `x` and
`‖φ y − φ z‖ ≤ C d(y, z)` (`φ` the extended chart at `x`).  Escape argument of Mathlib's
`setOf_riemannianEDist_lt_subset_nhds`, applied to paths starting at `y` instead of `x`. -/
theorem local_lower_comparison (x : M) :
    ∃ C > (0:ℝ≥0), ∃ c > (0:ℝ≥0∞), ∃ W ∈ 𝓝 x, ∀ y ∈ W, ∀ z, riemannianEDist I y z < c →
      z ∈ (chartAt H x).source ∧
      edist (extChartAt I x y) (extChartAt I x z) ≤ C * riemannianEDist I y z := by
  rcases eventually_enorm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  obtain ⟨u, u_mem, hu, uc⟩ : ∃ u ∈ 𝓝 x, u ⊆ {y | ‖mfderiv% (extChartAt I x) y‖ₑ < C} ∧
      u ⊆ (chartAt H x).source :=
    ⟨_, inter_mem hC (chart_source_mem_nhds H x), inter_subset_left, inter_subset_right⟩
  obtain ⟨c₀, c₀_pos, hc₀⟩ := setOf_riemannianEDist_lt_subset_nhds' I u_mem
  have hc2 : (0:ℝ≥0∞) < c₀ / 2 := ENNReal.half_pos c₀_pos.ne'
  refine ⟨C, C_pos, c₀ / 2, hc2, {y | riemannianEDist I x y < c₀ / 2},
    eventually_riemannianEDist_lt I x hc2, ?_⟩
  intro y hy z hz
  have hy' : riemannianEDist I x y < c₀ / 2 := hy
  have key : ∀ L, riemannianEDist I y z < L → L ≤ c₀ / 2 →
      z ∈ (chartAt H x).source ∧ edist (extChartAt I x y) (extChartAt I x z) ≤ C * L := by
    intro L hL hLc
    rcases exists_lt_locally_constant_of_riemannianEDist_lt hL zero_lt_one with
      ⟨γ, hγy, hγz, γ_smooth, hγ, -⟩
    have hin : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ u := by
      intro t ht
      apply hc₀
      show riemannianEDist I x (γ t) < c₀
      calc riemannianEDist I x (γ t)
          ≤ riemannianEDist I x y + riemannianEDist I y (γ t) := riemannianEDist_triangle
        _ ≤ riemannianEDist I x y + pathELength I γ 0 t := by
            gcongr
            exact riemannianEDist_le_pathELength γ_smooth.contMDiffOn hγy rfl ht.1
        _ ≤ riemannianEDist I x y + pathELength I γ 0 1 := by
            gcongr
            exact ht.2
        _ < c₀ / 2 + c₀ / 2 := ENNReal.add_lt_add hy' (hγ.trans_le hLc)
        _ = c₀ := ENNReal.add_halves c₀
    have h1 := chart_edist_le_pathELength I x C u hu uc γ_smooth.contMDiffOn hin
    rw [hγy, hγz] at h1
    refine ⟨hγz ▸ uc (hin 1 ⟨zero_le_one, le_rfl⟩), h1.trans ?_⟩
    gcongr
  refine ⟨(key _ hz le_rfl).1, ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  have hd : riemannianEDist I y z < b / C := by
    rwa [ENNReal.lt_div_iff_mul_lt (Or.inl (by exact_mod_cast C_pos.ne'))
      (Or.inl ENNReal.coe_ne_top), mul_comm]
  obtain ⟨L, hL1, hL2⟩ := exists_between (lt_min hz hd)
  calc edist (extChartAt I x y) (extChartAt I x z)
      ≤ (C:ℝ≥0∞) * L := (key L hL1 (hL2.le.trans (min_le_left _ _))).2
    _ ≤ C * (b / C) := by gcongr; exact hL2.le.trans (min_le_right _ _)
    _ ≤ b := ENNReal.mul_div_le

end LocalComparison

section HausdorffBalls

variable {n : ℕ} {M : Type*} [EMetricSpace M] [ChartedSpace (Fin n → ℝ) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M]
  [IsContinuousRiemannianBundle (Fin n → ℝ) (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsRiemannianManifold 𝓘(ℝ, Fin n → ℝ) M]
  [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- On a Riemannian manifold, `edist` is the Riemannian distance. -/
theorem edist_eq_riemannian (y z : M) : edist y z = riemannianEDist 𝓘(ℝ, Fin n → ℝ) y z :=
  IsRiemannianManifold.out y z

/-- Hausdorff measure of a sup-norm ball in `ℝⁿ`. -/
theorem hausdorff_pi_ball (p : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    μH[(n:ℝ)] (Metric.ball p r) = ENNReal.ofReal ((2 * r) ^ n) := by
  have h := hausdorffMeasure_pi_real (ι := Fin n)
  rw [Fintype.card_fin] at h
  rw [h, Real.volume_pi_ball p hr, Fintype.card_fin]

theorem hausdorff_pi_closedBall (p : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    μH[(n:ℝ)] (Metric.closedBall p r) = ENNReal.ofReal ((2 * r) ^ n) := by
  have h := hausdorffMeasure_pi_real (ι := Fin n)
  rw [Fintype.card_fin] at h
  rw [h, Real.volume_pi_closedBall p hr, Fintype.card_fin]

set_option synthInstance.maxHeartbeats 200000 in
/-- (Stage 2) Near every point `x` of a Riemannian manifold modelled on `ℝⁿ` (sup norm, no boundary),
the `n`-dimensional Hausdorff measure of the Riemannian distance has two-sided growth on small
balls: `a rⁿ ≤ μH[n](B(y,r)) ≤ A rⁿ` for `y` near `x` and `0 < r ≤ r₀`. -/
theorem local_hausdorff_ball (x : M) :
    ∃ a > (0:ℝ), ∃ A : ℝ, ∃ r₀ > (0:ℝ), ∀ᶠ y in 𝓝 x, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ n) ≤ μH[(n:ℝ)] (Metric.eball y (ENNReal.ofReal r)) ∧
      μH[(n:ℝ)] (Metric.eball y (ENNReal.ofReal r)) ≤ ENNReal.ofReal (A * r ^ n) := by
  set φ := extChartAt 𝓘(ℝ, Fin n → ℝ) x
  obtain ⟨C₂, C₂_pos, ρ, ρ_pos, htarget, hup⟩ := local_upper_comparison (M := M) 𝓘(ℝ, Fin n → ℝ) x
  obtain ⟨K, K_pos, c, c_pos, W, W_mem, hlow⟩ := local_lower_comparison (M := M) 𝓘(ℝ, Fin n → ℝ) x
  have hrange : range 𝓘(ℝ, Fin n → ℝ) = univ := ModelWithCorners.range_eq_univ _
  -- δ: chart ball whose inverse image lies in `W`
  have hWpre : φ.symm ⁻¹' W ∈ 𝓝 (φ x) := by
    apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
    rwa [extChartAt_to_inv]
  obtain ⟨δ₀, δ₀_pos, hδ₀⟩ := Metric.mem_nhds_iff.1 hWpre
  set δ := min δ₀ ρ with hδ
  have δ_pos : 0 < δ := lt_min δ₀_pos ρ_pos
  have hballW : Metric.ball (φ x) δ ⊆ φ.symm ⁻¹' W :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hδ₀
  have hballρ : Metric.ball (φ x) δ ⊆ Metric.ball (φ x) ρ :=
    Metric.ball_subset_ball (min_le_right _ _)
  -- Lipschitz properties
  have hLipSymm : LipschitzOnWith C₂ φ.symm (Metric.ball (φ x) ρ) := by
    intro p hp q hq
    rw [edist_eq_riemannian (n := n)]
    exact hup p ⟨hp, by rw [hrange]; trivial⟩ q ⟨hq, by rw [hrange]; trivial⟩
  set c₁ : ℝ := (min c 1).toReal
  have hc₁ : 0 < c₁ := ENNReal.toReal_pos (lt_min c_pos one_pos).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  have hc₁c : ENNReal.ofReal c₁ ≤ c := by
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _
  have K_pos' : (0:ℝ) < K := K_pos
  have C₂_pos' : (0:ℝ) < C₂ := C₂_pos
  set r₀ := min (c₁ / 2) (min (δ / (2 * K)) (C₂ * δ / 2))
  have r₀_pos : 0 < r₀ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨(2 / C₂) ^ n / K ^ n, by positivity, C₂ ^ n * (2 * K) ^ n, r₀, r₀_pos, ?_⟩
  have hN : φ ⁻¹' Metric.ball (φ x) (δ / 2) ∩ (chartAt (Fin n → ℝ) x).source ∈ 𝓝 x :=
    inter_mem ((continuousAt_extChartAt x).preimage_mem_nhds
      (Metric.ball_mem_nhds _ (by positivity))) (chart_source_mem_nhds _ x)
  filter_upwards [hN] with y ⟨hyb, hys⟩ r hr hrr₀
  have hyb' : dist (φ y) (φ x) < δ / 2 := hyb
  have hys' : y ∈ φ.source := by rwa [extChartAt_source]
  have hyy : φ.symm (φ y) = y := φ.left_inv hys'
  have hyW : y ∈ W := by
    have := hballW (Metric.ball_subset_ball (by linarith) hyb)
    rwa [mem_preimage, hyy] at this
  have hr1 : r ≤ c₁ / 2 := hrr₀.trans (min_le_left _ _)
  have hr2 : r ≤ δ / (2 * K) := hrr₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr3 : r ≤ C₂ * δ / 2 := hrr₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKr : K * r ≤ δ / 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * K)] at hr2; nlinarith
  set B := Metric.eball y (ENNReal.ofReal r)
  -- points of `B`: in the chart, image close to `φ y`
  have hBpt : ∀ z ∈ B, z ∈ φ.source ∧ dist (φ y) (φ z) ≤ K * r := by
    intro z hz0
    have hz : edist y z < ENNReal.ofReal r := by rw [edist_comm]; exact hz0
    have hz' : riemannianEDist 𝓘(ℝ, Fin n → ℝ) y z < c := by
      rw [← edist_eq_riemannian (n := n)]
      refine lt_of_lt_of_le hz (le_trans ?_ hc₁c)
      exact ENNReal.ofReal_le_ofReal (by linarith)
    obtain ⟨hzs, hzd⟩ := hlow y hyW z hz'
    refine ⟨by rwa [extChartAt_source], ?_⟩
    rw [← edist_eq_riemannian (n := n)] at hzd
    have h2 : edist (φ y) (φ z) ≤ ENNReal.ofReal (K * r) := by
      calc edist (φ y) (φ z) ≤ K * edist y z := hzd
        _ ≤ K * ENNReal.ofReal r := by gcongr
        _ = ENNReal.ofReal (K * r) := by
          rw [ENNReal.ofReal_mul K_pos'.le, ENNReal.ofReal_coe_nnreal]
    rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have hBin : ∀ z ∈ B, φ z ∈ Metric.ball (φ x) δ := by
    intro z hz
    have := (hBpt z hz).2
    show dist (φ z) (φ x) < δ
    calc dist (φ z) (φ x) ≤ dist (φ z) (φ y) + dist (φ y) (φ x) := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by rw [dist_comm]; linarith
      _ = δ := by ring
  have hBW : ∀ z ∈ B, z ∈ W := by
    intro z hz
    have := hballW (hBin z hz)
    rwa [mem_preimage, φ.left_inv (hBpt z hz).1] at this
  constructor
  · -- lower bound
    have hLip : LipschitzOnWith K φ B := by
      intro z hz w hw
      have hzw : riemannianEDist 𝓘(ℝ, Fin n → ℝ) z w < c := by
        rw [← edist_eq_riemannian (n := n)]
        calc edist z w ≤ edist z y + edist y w := edist_triangle _ _ _
          _ < ENNReal.ofReal r + ENNReal.ofReal r := by
              exact ENNReal.add_lt_add hz (by rw [edist_comm]; exact hw)
          _ = ENNReal.ofReal (2 * r) := by rw [← ENNReal.ofReal_add hr.le hr.le]; ring_nf
          _ ≤ c := le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hc₁c
      have := (hlow z (hBW z hz) w hzw).2
      rwa [← edist_eq_riemannian (n := n)] at this
    have hsub : Metric.ball (φ y) (r / C₂) ⊆ φ '' B := by
      intro p hp
      have hp' : dist p (φ y) < r / C₂ := hp
      have hrC : r / C₂ ≤ δ / 2 := by
        rw [div_le_iff₀ C₂_pos']; nlinarith
      have hpx : p ∈ Metric.ball (φ x) δ := by
        show dist p (φ x) < δ
        calc dist p (φ x) ≤ dist p (φ y) + dist (φ y) (φ x) := dist_triangle _ _ _
          _ < δ / 2 + δ / 2 := by linarith
          _ = δ := by ring
      have hpt : p ∈ φ.target := by
        apply htarget; exact ⟨hballρ hpx, by rw [hrange]; trivial⟩
      refine ⟨φ.symm p, ?_, φ.right_inv hpt⟩
      rw [Metric.mem_eball, edist_comm]
      have hyρ : φ y ∈ Metric.ball (φ x) ρ :=
        hballρ (Metric.ball_subset_ball (by linarith) hyb)
      calc edist y (φ.symm p) = edist (φ.symm (φ y)) (φ.symm p) := by rw [hyy]
        _ ≤ C₂ * edist (φ y) p := hLipSymm hyρ (hballρ hpx)
        _ < C₂ * ENNReal.ofReal (r / C₂) := by
            gcongr
            · exact ENNReal.coe_ne_top
            · rw [edist_dist, dist_comm]
              exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hp'
        _ = ENNReal.ofReal r := by
            rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C₂_pos'.le]
            congr 1; field_simp
    have h1 : μH[(n:ℝ)] (Metric.ball (φ y) (r / C₂)) ≤ (K : ℝ≥0∞) ^ (n:ℝ) * μH[(n:ℝ)] B :=
      (measure_mono hsub).trans (hLip.hausdorffMeasure_image_le (Nat.cast_nonneg n))
    rw [hausdorff_pi_ball _ (by positivity), ENNReal.rpow_natCast] at h1
    have hKn : (K : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast K_pos.ne')
    have hKt : (K : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
    have h2 : ENNReal.ofReal ((2 * (r / C₂)) ^ n) / (K : ℝ≥0∞) ^ n ≤ μH[(n:ℝ)] B := by
      rw [ENNReal.div_le_iff hKn hKt, mul_comm (μH[(n:ℝ)] B)]; exact h1
    refine le_trans (le_of_eq ?_) h2
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    rw [mul_div_assoc', div_pow, div_pow, mul_pow]
    field_simp
  · -- upper bound
    have hsub : B ⊆ φ.symm '' Metric.closedBall (φ y) (K * r) := by
      intro z hz
      refine ⟨φ z, ?_, φ.left_inv (hBpt z hz).1⟩
      show dist (φ z) (φ y) ≤ K * r
      rw [dist_comm]; exact (hBpt z hz).2
    have hcb : Metric.closedBall (φ y) (K * r) ⊆ Metric.ball (φ x) ρ := by
      intro p hp
      have hp' : dist p (φ y) ≤ K * r := hp
      apply hballρ
      show dist p (φ x) < δ
      calc dist p (φ x) ≤ dist p (φ y) + dist (φ y) (φ x) := dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    have h1 : μH[(n:ℝ)] B ≤ (C₂ : ℝ≥0∞) ^ (n:ℝ) * μH[(n:ℝ)] (Metric.closedBall (φ y) (K * r)) :=
      (measure_mono hsub).trans ((hLipSymm.mono hcb).hausdorffMeasure_image_le (Nat.cast_nonneg n))
    rw [hausdorff_pi_closedBall _ (by positivity), ENNReal.rpow_natCast] at h1
    refine h1.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow C₂_pos'.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring

end HausdorffBalls

/-- A local property with constants `a` (lower, positive), `A` (upper), `r` (radius), monotone in
the constants, holds globally with one triple of constants on a compact space. -/
theorem compact_three {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (P : X → ℝ → ℝ → ℝ → Prop)
    (hmono : ∀ y a a' A A' r r', 0 < a' → a' ≤ a → A ≤ A' → 0 < r' → r' ≤ r →
      P y a A r → P y a' A' r')
    (hloc : ∀ x, ∃ a > (0:ℝ), ∃ A : ℝ, ∃ r > (0:ℝ), ∀ᶠ y in 𝓝 x, P y a A r) :
    ∃ a > (0:ℝ), ∃ A : ℝ, ∃ r > (0:ℝ), ∀ y, P y a A r := by
  choose a ha A r hr hP using hloc
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => {y | P y (a x) (A x) (r x)}) hP
  rcases t.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, 0, 1, one_pos, fun y => ?_⟩
    have hy : y ∈ ⋃ x ∈ t, {y | P y (a x) (A x) (r x)} := by rw [ht]; trivial
    simp [h] at hy
  · have hapos : 0 < t.inf' hne a := (Finset.lt_inf'_iff hne).2 fun x _ => ha x
    have hrpos : 0 < t.inf' hne r := (Finset.lt_inf'_iff hne).2 fun x _ => hr x
    refine ⟨t.inf' hne a, hapos, t.sup' hne A, t.inf' hne r, hrpos, fun y => ?_⟩
    have hy : y ∈ ⋃ x ∈ t, {y | P y (a x) (A x) (r x)} := by rw [ht]; trivial
    simp only [Set.mem_iUnion] at hy
    obtain ⟨x, hx, hPy⟩ := hy
    exact hmono y _ _ _ _ _ _ hapos (Finset.inf'_le _ hx) (Finset.le_sup' _ hx) hrpos
      (Finset.inf'_le _ hx) hPy

section Uniform

variable {n : ℕ} {M : Type*} [EMetricSpace M] [ChartedSpace (Fin n → ℝ) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M]
  [IsContinuousRiemannianBundle (Fin n → ℝ) (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsRiemannianManifold 𝓘(ℝ, Fin n → ℝ) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- (Stage 3) Uniform two-sided growth of the `n`-dimensional Hausdorff measure of the Riemannian
distance on a compact Riemannian manifold modelled on `ℝⁿ`: there are `0 < a`, `A`, `r₀ > 0` with
`a rⁿ ≤ μH[n](B(y,r)) ≤ A rⁿ` for ALL `y` and `0 < r ≤ r₀`. -/
theorem hausdorff_ball_uniform :
    ∃ a > (0:ℝ), ∃ A : ℝ, ∃ r₀ > (0:ℝ), ∀ y : M, ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ n) ≤ μH[(n:ℝ)] (Metric.eball y (ENNReal.ofReal r)) ∧
      μH[(n:ℝ)] (Metric.eball y (ENNReal.ofReal r)) ≤ ENNReal.ofReal (A * r ^ n) := by
  apply compact_three (fun (y : M) a A r₀ => ∀ r, 0 < r → r ≤ r₀ →
      ENNReal.ofReal (a * r ^ n) ≤ μH[(n:ℝ)] (Metric.eball y (ENNReal.ofReal r)) ∧
      μH[(n:ℝ)] (Metric.eball y (ENNReal.ofReal r)) ≤ ENNReal.ofReal (A * r ^ n))
  · intro y a a' A A' r r' _ haa hAA _ hrr h s hs hsr
    obtain ⟨h1, h2⟩ := h s hs (hsr.trans hrr)
    exact ⟨le_trans (ENNReal.ofReal_le_ofReal (by gcongr)) h1,
      h2.trans (ENNReal.ofReal_le_ofReal (by gcongr))⟩
  · exact local_hausdorff_ball

/-- (Stage 4, upper) For a sampling law `m ≤ m₁ μH[n]` (e.g. a density bounded by `m₁` with respect
to `μH[n]`) on a compact connected Riemannian manifold modelled on `ℝⁿ`: the upper growth bound in
the form of the hypothesis `hgrowth` of `CTG.ManifoldDistance.annulus_bound` for `ρ y = d(x,y)`,
uniformly in `x`. -/
theorem sampling_upper_growth [PreconnectedSpace M] (m : Measure M) (m₁ : ℝ) (hm₁ : 0 ≤ m₁)
    (hm : ∀ s, m s ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] s) :
    ∃ A ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∀ x : M, ∀ r, 0 < r → r ≤ r₀ →
      m {y | (edist x y).toReal < r} ≤ ENNReal.ofReal (A * r ^ n) := by
  obtain ⟨a, ha, A, r₀, hr₀, h⟩ := hausdorff_ball_uniform (n := n) (M := M)
  refine ⟨m₁ * max A 0, by positivity, r₀, hr₀, fun x r hr hrr => ?_⟩
  have hset : {y | (edist x y).toReal < r} = Metric.eball x (ENNReal.ofReal r) := by
    ext y
    rw [mem_setOf_eq, Metric.mem_eball, edist_comm y x]
    exact (ENNReal.lt_ofReal_iff_toReal_lt
      (CTG.ManifoldDistance.edist_ne_top_of_preconnected x y)).symm
  rw [hset]
  calc m _ ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] (Metric.eball x (ENNReal.ofReal r)) := hm _
    _ ≤ ENNReal.ofReal m₁ * ENNReal.ofReal (max A 0 * r ^ n) := by
        gcongr
        exact (h x r hr hrr).2.trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
    _ = ENNReal.ofReal (m₁ * max A 0 * r ^ n) := by
        rw [← ENNReal.ofReal_mul hm₁]; ring_nf

/-- (Stage 4, upper, time metric) The same growth bound for the balls of the distance at time `a`
of a `TimeMetric` that is continuous in the base point at time `a`: this is literally the
hypothesis `hgrowth` of `TimeMetric.kernel_increment_integral` and
`TimeMetric.kernel_increment_sq_integral`. -/
theorem sampling_upper_growth_time [PreconnectedSpace M]
    {s : Set ℝ} (G : CTG.ManifoldDistance.TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a : ℝ} (ha : a ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (m : Measure M) (m₁ : ℝ) (hm₁ : 0 ≤ m₁) (hm : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) :
    ∃ A ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∀ x : M, ∀ r, 0 < r → r ≤ r₀ →
      m {y | G.dist x y a < r} ≤ ENNReal.ofReal (A * r ^ n) := by
  obtain ⟨a', ha', A, r₀, hr₀, h⟩ := hausdorff_ball_uniform (n := n) (M := M)
  obtain ⟨c₁, c₂, -, -, hc₂0, hc₂t, hcmp⟩ :=
    CTG.ManifoldDistance.quadENorm_riemannianEDist_comparable (G.g a) hcont (G.pos a ha)
  set k := c₂.toReal
  have hk : 0 < k := ENNReal.toReal_pos hc₂0 hc₂t
  refine ⟨m₁ * max A 0 * k ^ n, by positivity, r₀ / k, by positivity, fun x r hr hrr => ?_⟩
  have hkr : k * r ≤ r₀ := by rwa [le_div_iff₀ hk, mul_comm] at hrr
  have hsub : {y | G.dist x y a < r} ⊆ Metric.eball x (ENNReal.ofReal (k * r)) := by
    intro y hy
    have hfin := G.riemannianEDist_ne_top ha ha hcont x y
    have h1 : (letI := G.norms a; Manifold.riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y)
        < ENNReal.ofReal r := (ENNReal.lt_ofReal_iff_toReal_lt hfin).2 hy
    show edist y x < _
    rw [edist_comm, edist_eq_riemannian (n := n)]
    calc riemannianEDist _ x y
        ≤ c₂ * (letI := G.norms a; Manifold.riemannianEDist 𝓘(ℝ, Fin n → ℝ) x y) := (hcmp x y).2
      _ < c₂ * ENNReal.ofReal r := by
          rw [mul_comm c₂, mul_comm c₂]; exact ENNReal.mul_lt_mul_left hc₂0 hc₂t h1
      _ = ENNReal.ofReal (k * r) := by rw [ENNReal.ofReal_mul hk.le, ENNReal.ofReal_toReal hc₂t]
  calc m {y | G.dist x y a < r} ≤ m (Metric.eball x (ENNReal.ofReal (k * r))) := measure_mono hsub
    _ ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] (Metric.eball x (ENNReal.ofReal (k * r))) := hm _
    _ ≤ ENNReal.ofReal m₁ * ENNReal.ofReal (max A 0 * (k * r) ^ n) := by
        gcongr
        exact (h x _ (by positivity) hkr).2.trans
          (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
    _ = ENNReal.ofReal (m₁ * max A 0 * k ^ n * r ^ n) := by
        rw [← ENNReal.ofReal_mul hm₁]; ring_nf

/-- (Stage 4, lower) For a sampling law `m ≥ m₀ μH[n]` on a compact Riemannian manifold modelled on
`ℝⁿ` and any profile `h` with `h ≥ h₀ ≥ 0` on `[0,1]` (and `h` arbitrary elsewhere): the population
normalisation satisfies `q(x) = ∫ h(d(x,y)/ξ) dm(y) ≥ h₀ m₀ a ξⁿ` for all `x` and `0 < ξ ≤ r₀`
(as a lower integral of `ofReal ∘ h`; constants `a`, `r₀` from `hausdorff_ball_uniform`). -/
theorem sampling_normalisation_lower (m : Measure M) (m₀ : ℝ) (hm₀ : 0 ≤ m₀)
    (hm : ∀ s, ENNReal.ofReal m₀ * μH[(n:ℝ)] s ≤ m s) :
    ∃ a > (0:ℝ), ∃ r₀ > (0:ℝ), ∀ (h : ℝ → ℝ) (h₀ : ℝ), 0 ≤ h₀ →
      (∀ t, 0 ≤ t → t ≤ 1 → h₀ ≤ h t) → ∀ x : M, ∀ ξ, 0 < ξ → ξ ≤ r₀ →
        ENNReal.ofReal (h₀ * m₀ * a * ξ ^ n)
          ≤ ∫⁻ y, ENNReal.ofReal (h ((edist x y).toReal / ξ)) ∂m := by
  obtain ⟨a, ha, A, r₀, hr₀, hb⟩ := hausdorff_ball_uniform (n := n) (M := M)
  refine ⟨a, ha, r₀, hr₀, fun h h₀ hh₀ hh x ξ hξ hξr => ?_⟩
  set B := Metric.eball x (ENNReal.ofReal ξ)
  have hB : MeasurableSet B := Metric.isOpen_eball.measurableSet
  calc ENNReal.ofReal (h₀ * m₀ * a * ξ ^ n)
      = ENNReal.ofReal h₀ * (ENNReal.ofReal m₀ * ENNReal.ofReal (a * ξ ^ n)) := by
        rw [← ENNReal.ofReal_mul hm₀, ← ENNReal.ofReal_mul hh₀]; ring_nf
    _ ≤ ENNReal.ofReal h₀ * (ENNReal.ofReal m₀ * μH[(n:ℝ)] B) := by
        gcongr; exact (hb x ξ hξ hξr).1
    _ ≤ ENNReal.ofReal h₀ * m B := by gcongr; exact hm B
    _ = ∫⁻ _ in B, ENNReal.ofReal h₀ ∂m := (setLIntegral_const B _).symm
    _ ≤ ∫⁻ y in B, ENNReal.ofReal (h ((edist x y).toReal / ξ)) ∂m := by
        apply setLIntegral_mono' hB
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        apply hh
        · positivity
        · rw [div_le_one hξ]
          have hy' : edist y x < ENNReal.ofReal ξ := hy
          rw [edist_comm] at hy'
          exact ENNReal.toReal_le_of_le_ofReal hξ.le hy'.le
    _ ≤ ∫⁻ y, ENNReal.ofReal (h ((edist x y).toReal / ξ)) ∂m := setLIntegral_le_lintegral _ _

end Uniform

end CTG.ManifoldVolume
