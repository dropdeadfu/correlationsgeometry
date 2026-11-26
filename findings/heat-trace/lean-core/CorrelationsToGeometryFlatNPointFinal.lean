/-
Thirty-second file: closing gaps of the flat N-point statement.  Imports `CorrelationsToGeometryFlatNPointRate`
(compiled module under `.tools/leanbuild`); namespace `CTG.FlatNPointFinal`; check with
`./check_flat_npoint_final.sh`.
`fderiv_bound_of_per` (a periodic `C¹` function has a bounded derivative), `flat_npoint_final` (the statement of
`flat_npoint_rate` with a bound `M₁` on the derivative of `f` in place of the Lipschitz hypothesis),
`badRate_measurable` (the exceptional set is measurable), `flat_npoint_pairs` (finitely many pairs of times on one
event, probability of failure at most `|P|·30/N²`), `dotL_flat` (population level, derivative in the time:
`|d/dτ L^τ_ξ f − 2 a'(τ) lapG S f / a(τ)³| ≤ C ξ²`, i.e. `prop:dotL` in the flat conformal case, with an error
`ξ²`; HYPOTHESIS: `τ ↦ L^τ_ξ f(x)` is differentiable at `τ`).
NOT formalised: all pairs of times of a window (grid), the differentiability just named, Gaussian profiles.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatNPointRate

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4 CTG.FlatNPoint
  CTG.FlatNPointRate

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointFinal

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### (1) The Lipschitz constant of `f` -/

/-- A bound on the derivative gives the Lipschitz constant. -/
theorem lip_of_fderiv {f : E → ℝ} (hf : Differentiable ℝ f) {M₁ : ℝ}
    (hb : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁) (x y : E) : |f y - f x| ≤ M₁ * ‖y - x‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (s := univ) (fun z _ => hf z)
    (fun z _ => hb z) convex_univ (mem_univ x) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- The closed cube `[-1/2, 1/2]ⁿ` (as a subset of Euclidean space) is compact. -/
theorem cube_compact :
    IsCompact (WithLp.toLp 2 '' (Set.pi univ fun _ : Fin n => Icc (-(1/2):ℝ) (1/2)) : Set E) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

theorem fr_mem_cube (v : E) :
    fr v ∈ (WithLp.toLp 2 '' (Set.pi univ fun _ : Fin n => Icc (-(1/2):ℝ) (1/2)) : Set E) := by
  refine ⟨fun i => v i - ⌊v i + 1 / 2⌋, fun i _ => ?_, rfl⟩
  have h1 := Int.floor_le (v i + 1 / 2)
  have h2 := Int.lt_floor_add_one (v i + 1 / 2)
  constructor <;> linarith

/-- **(1)** A periodic `C¹` function has a bounded derivative. -/
theorem fderiv_bound_of_per {f : E → ℝ} (hf : ContDiff ℝ 1 f) (hper : Per f) :
    ∃ M₁, 0 ≤ M₁ ∧ ∀ y, ‖fderiv ℝ f y‖ ≤ M₁ := by
  have hc : Continuous fun y => fderiv ℝ f y := hf.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := cube_compact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  set g := y - fr y
  have hg : g ∈ Lat (n := n) := sub_fr_mem y
  have hfun : (fun w => f (g + w)) = f := funext fun w => hper g hg w
  have e : fderiv ℝ f y = fderiv ℝ f (fr y) := by
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := f) (x := fr y) g
    rw [hfun] at this
    rw [this]; congr 1; simp [g]
  rw [e]
  exact (hC _ (fr_mem_cube y)).trans (le_max_left _ _)

/-! ### (2) The exceptional set and its measurability -/

/-- The exceptional set of `flat_npoint_rate` (literally), with `Λ` as a parameter. -/
def badRate {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E)
    (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ) (τa τb Λ M₄ μ₄ K₀ a₀ La : ℝ) : Set Ω :=
  {ω | ∃ i < N, ¬ (
        |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          - (Lmet h m₂ S (a τb) ξ f (X i ω) - Lmet h m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * Λ ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * Λ ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)))}

theorem perK_measurable {κ : E → ℝ} (hκ : Measurable κ) :
    Measurable fun p : E × E => perK κ p.1 p.2 :=
  hκ.comp (fr_measurable.comp (measurable_snd.sub measurable_fst))

theorem sampAvg_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) {K : E → E → ℝ}
    (hK : Measurable fun p : E × E => K p.1 p.2) (j : ℕ) :
    Measurable fun ω => sampAvg X N K j ω := by
  unfold sampAvg
  exact (Finset.measurable_sum _ fun k _ => hK.comp ((hX j).prodMk (hX k))).const_mul _

theorem sampW_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) {K g : E → E → ℝ}
    (hK : Measurable fun p : E × E => K p.1 p.2) (hg : Measurable fun p : E × E => g p.1 p.2)
    (i : ℕ) : Measurable fun ω => sampW X N K g i ω := by
  unfold sampW avgN
  refine (Finset.measurable_sum _ fun j _ => ?_).const_mul _
  exact ((hK.comp ((hX i).prodMk (hX j))).mul (hg.comp ((hX i).prodMk (hX j)))).mul
    ((sampAvg_measurable X hX N hK j).const_div 1)

theorem LN_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) {h : ℝ → ℝ} (hh : Measurable h) (m₂ : ℝ)
    (S : E ≃L[ℝ] E) (a ξ : ℝ) {f : E → ℝ} (hfc : Continuous f) (i : ℕ) :
    Measurable fun ω => LN X N h m₂ S a ξ f i ω := by
  have hK := perK_measurable (kap_measurable hh S (ξ / a))
  have hg : Measurable fun p : E × E => gd f p.1 p.2 :=
    (hfc.measurable.comp measurable_snd).sub (hfc.measurable.comp measurable_fst)
  unfold LN
  exact ((sampW_measurable X hX N hK hg i).div
    (sampW_measurable X hX N hK measurable_const i)).const_mul _

theorem PG_measurable {h : ℝ → ℝ} (hh : Measurable h) (S : E ≃L[ℝ] E) (ξ : ℝ) {f : E → ℝ}
    (hfc : Continuous f) : Measurable (PG h S ξ f) := by
  have hF : Measurable fun p : E × E => h (‖S.symm p.2‖ / ξ) * f (p.1 + p.2) :=
    ((kap_measurable hh S ξ).comp measurable_snd).mul
      (hfc.measurable.comp (measurable_fst.add measurable_snd))
  unfold PG
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E))).measurable.div_const _

theorem Lmet_measurable {h : ℝ → ℝ} (hh : Measurable h) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a ξ : ℝ)
    {f : E → ℝ} (hfc : Continuous f) : Measurable (Lmet h m₂ S a ξ f) := by
  unfold Lmet
  exact (hfc.measurable.sub (PG_measurable hh S (ξ / a) hfc)).const_mul _

theorem lapG_measurable (S : E ≃L[ℝ] E) {f : E → ℝ} (hf : ContDiff ℝ 4 f) :
    Measurable (lapG S f) := by
  have hc : Continuous fun x => iteratedFDeriv ℝ 2 f x :=
    hf.continuous_iteratedFDeriv (by norm_num)
  unfold lapG
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ
    (fun _ => S (eb i))).continuous.comp hc).measurable

/-- **(2)** The exceptional set of `flat_npoint_rate` is measurable. -/
theorem badRate_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) {h : ℝ → ℝ} (hh : Measurable h) (m₂ : ℝ)
    (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) {f : E → ℝ} (hf : ContDiff ℝ 4 f)
    (τa τb Λ M₄ μ₄ K₀ a₀ La : ℝ) :
    MeasurableSet (badRate X N h m₂ S a ξ f τa τb Λ M₄ μ₄ K₀ a₀ La) := by
  have hfc : Continuous f := hf.continuous
  have hLb := fun i => LN_measurable X hX N hh m₂ S (a τb) ξ hfc i
  have hLa := fun i => LN_measurable X hX N hh m₂ S (a τa) ξ hfc i
  have hMb := fun i => (Lmet_measurable hh m₂ S (a τb) ξ hfc).comp (hX i)
  have hMa := fun i => (Lmet_measurable hh m₂ S (a τa) ξ hfc).comp (hX i)
  have hG := fun i => (lapG_measurable S hf).comp (hX i)
  have e : badRate X N h m₂ S a ξ f τa τb Λ M₄ μ₄ K₀ a₀ La = ⋃ i : ℕ, {ω | i < N ∧ ¬ (
        |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          - (Lmet h m₂ S (a τb) ξ f (X i ω) - Lmet h m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * Λ ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * Λ ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)))} := by
    ext ω; simp only [badRate, mem_setOf_eq, mem_iUnion]
  rw [e]
  refine MeasurableSet.iUnion fun i => ?_
  refine (MeasurableSet.const (i < N)).inter ?_
  refine MeasurableSet.compl ?_
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le
      (((((hLb i).sub (hLa i)).div_const _).sub (((hMb i).sub (hMa i)).div_const _))).abs
      measurable_const
  · exact measurableSet_le
      (((((hLb i).sub (hLa i)).div_const _).add
        ((((hG i).div_const _).sub ((hG i).div_const _)).div_const _))).abs
      measurable_const

/-! ### The final single-pair statement without `hLip` -/

/-- **`prop:dotLN-diff`, flat periodic case, rate form, with the Lipschitz constant of `f` from a
bound `M₁` on its derivative.** Same set as `flat_npoint_rate` (`badRate`), probability `≤ 30/N²`. -/
theorem flat_npoint_final {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real (badRate X N h m₂ S a ξ f τa τb (rLam A K₀ Lh R La a₀ a₁ M₁ S) M₄ μ₄ K₀ a₀ La)
      ≤ 30 / (N : ℝ) ^ 2 :=
  flat_npoint_rate X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper
    (le_trans (norm_nonneg _) (hM₁ 0)) (lip_of_fderiv (hf.differentiable (by norm_num)) hM₁)
    S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh τa τb hne hNL

/-! ### (3) Finitely many pairs of times on one event -/

/-- **(3)** For a finite set `P` of pairs `(τa, τb)` with `τb ≠ τa`, all statements hold
simultaneously outside an event of probability `≤ |P|·30/N²`. -/
theorem flat_npoint_pairs {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (Pairs : Finset (ℝ × ℝ)) (hne : ∀ p ∈ Pairs, p.2 ≠ p.1)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real (⋃ p ∈ Pairs,
        badRate X N h m₂ S a ξ f p.1 p.2 (rLam A K₀ Lh R La a₀ a₁ M₁ S) M₄ μ₄ K₀ a₀ La)
      ≤ Pairs.card * (30 / (N : ℝ) ^ 2) := by
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc ∑ p ∈ Pairs, μ.real (badRate X N h m₂ S a ξ f p.1 p.2
          (rLam A K₀ Lh R La a₀ a₁ M₁ S) M₄ μ₄ K₀ a₀ La)
        ≤ ∑ p ∈ Pairs, (30 / (N : ℝ) ^ 2) := Finset.sum_le_sum fun p hp =>
          flat_npoint_final X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper hM₁
            S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh p.1 p.2 (hne p hp) hNL
    _ = Pairs.card * (30 / (N : ℝ) ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### (4) The derivative version at population level -/

/-- **(4) `prop:dotL` in the flat case (population level).**  If `τ ↦ L^τ_ξ f(x)` has a derivative
`DL` at `τ` (HYPOTHESIS), then `|DL − 2 a'(τ) Δ_{g₀} f(x)/a(τ)³| ≤ ξ² M₄‖S‖⁴μ₄L_a/(3m₂K₀a₀⁵)`;
`−2a'Δ_{g₀}f/a³` is the derivative of `Δ_{g_τ} f(x) = Δ_{g₀} f(x)/a(τ)²`. -/
theorem dotL_flat {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : E) (τ : ℝ) {DL : ℝ}
    (hDL : HasDerivAt (fun t => Lmet h m₂ S (a t) ξ f x) DL τ) :
    |DL - 2 * a' τ * lapG S f x / a τ ^ 3|
      ≤ ξ ^ 2 * (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)) := by
  have hpos : ∀ t, 0 < a t := fun t => lt_of_lt_of_le ha₀ (ha t)
  set c := lapG S f x
  set B := ξ ^ 2 * (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5))
  set g : ℝ → ℝ := fun t => Lmet h m₂ S (a t) ξ f x + c / a t ^ 2
  have hq : HasDerivAt (fun t => c / a t ^ 2) (-(2 * a' τ * c / a τ ^ 3)) τ := by
    have h1 := (hasDerivAt_const τ c).div ((hda τ).pow 2) (pow_ne_zero 2 (hpos τ).ne')
    refine h1.congr_deriv ?_
    have := (hpos τ).ne'
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hg : HasDerivAt g (DL + -(2 * a' τ * c / a τ ^ 3)) τ := hDL.add hq
  have hsl := hasDerivAt_iff_tendsto_slope.1 hg
  have hlim : Tendsto (fun t => |slope g τ t|) (𝓝[≠] τ)
      (𝓝 |DL + -(2 * a' τ * c / a τ ^ 3)|) := (continuous_abs.tendsto _).comp hsl
  have hev : ∀ᶠ t in 𝓝[≠] τ, |slope g τ t| ≤ B := by
    refine eventually_nhdsWithin_of_forall fun t ht => ?_
    have hne : t ≠ τ := ht
    have hb := metric_dq_min hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ x τ t hne
    rw [slope_def_field]
    have e : (g t - g τ) / (t - τ)
        = (Lmet h m₂ S (a t) ξ f x - Lmet h m₂ S (a τ) ξ f x) / (t - τ)
          + (lapG S f x / a t ^ 2 - lapG S f x / a τ ^ 2) / (t - τ) := by
      simp only [g, c]; ring
    rw [e]
    exact hb.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _))
  have := le_of_tendsto hlim hev
  have e2 : DL + -(2 * a' τ * c / a τ ^ 3) = DL - 2 * a' τ * c / a τ ^ 3 := by ring
  rwa [e2] at this

end CTG.FlatNPointFinal

#print axioms CTG.FlatNPointFinal.fderiv_bound_of_per
#print axioms CTG.FlatNPointFinal.badRate_measurable
#print axioms CTG.FlatNPointFinal.flat_npoint_final
#print axioms CTG.FlatNPointFinal.flat_npoint_pairs
#print axioms CTG.FlatNPointFinal.dotL_flat
