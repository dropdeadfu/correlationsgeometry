/-
Fifty-eighth file: final form of the lattice window statement and measurability of its exceptional set.
Namespace `CTG.FlatNPointLatticeWindowFinal`; imports the fifty-sixth file (`FlatNPointLatticeWindow`) and the
fifty-third file (`GaussMoment`), both as compiled modules.  Check with `./check_flat_npoint_lattice_window_final.sh`.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
`flat_npoint_lattice_window_final`: `flat_npoint_lattice_window_N2` with `m₂ = 1` (`gam₂_eq_one`) and with the
normalised population operator `LPK mT (latK S (ξ / a τ)) 1 ξ f` of the same lattice-sum kernel
(`Lmet_pop_lat`) on the population side.
`latK_self_ge`, `sampAvgK_pos`, `denK_pos`: the self-term `latK(x,x) ≥ gauss 0 = 1` makes all sample
normalisations positive for EVERY sample.  `LNK_cont`: `τ ↦ LNK …(latK S (ξ / a τ))… i ω` is continuous for every
`ω` (from `latK_tlip`, without any event).  `LPK_cont`: `τ ↦ LPK mT (latK S (ξ / a τ)) 1 ξ f x` is continuous.
`window_final_set_measurable`: the exceptional set (arbitrary constants `Er`, `C₁`, `C₂`) is measurable;
`flat_npoint_lattice_window_final_set_measurable`: literally the set of `flat_npoint_lattice_window_final`;
`flat_npoint_lattice_window_N2_set_measurable`: literally the set of `flat_npoint_lattice_window_N2`.
Several auxiliary statements (`cont_of_lip`, `fr_zero`, `C2_nonneg`, `exists_param_measurable`) are copies from
the forty-first file (`FlatNPointWindow2`), which has no compiled module.
No sorry, no axiom, no native_decide.
-/
import CorrelationsToGeometryFlatNPointLatticeWindow
import CorrelationsToGeometryGaussMoment

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss CTG.FlatNPointGaussFull
  CTG.FlatNPointGaussLattice CTG.FlatNPointLatticePop CTG.FlatNPointLatticeDirect
  CTG.FlatNPointClose CTG.FlatNPointWindow CTG.FlatNPointLatticeWindow

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointLatticeWindowFinal

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Stage 1: the final form of the window statement -/

set_option maxHeartbeats 1600000 in
/-- **Final window statement.**  `flat_npoint_lattice_window_N2` with `m₂ = 1` and with the normalised
population operator `LPK` of the same lattice-sum kernel: for ALL pairs of times `τa, τb ∈ [p, q]` with
`|τb − τa| ≥ η₀`, on one event (outer measure bound; measurability below), both inequalities with factor 2. -/
theorem flat_npoint_lattice_window_final (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B M₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B) (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * (4 * Real.log N) ≤ N * ξ ^ n)
    {p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
          - (LPK mT (latK S (ξ / a τb)) (1 : ℝ) ξ f (X i ω)
              - LPK mT (latK S (ξ / a τa)) (1 : ℝ) ξ f (X i ω)) / (τb - τa)|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (1 : ℝ) (4 * Real.log N) N ξ
        ∧ |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
            + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (1 : ℝ) (4 * Real.log N) N ξ
            + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (1 : ℝ) (gaK₀ n) a₀ S)
                (Ctwo M₄ (gaμ₄ n) (1 : ℝ) (gaK₀ n) a₀ La S) (τb - τa))}
      ≤ 32 * Dwin η₀ (P0c S a₁ * ξ ^ n) (cIk a₀ a₁ La * Gb n S a₀)
          (LsumK n S a₀ a₁ La Lip ξ M₄ M₂) (1 : ℝ) p q ^ 2 / (N : ℝ) ^ 2 := by
  have H := flat_npoint_lattice_window_N2 hn X h_indep hX hlaw N hN hf hM hM₄ hper hLip0 hLip
    hB hM₂ S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hNL (p := p) (q := q) hη₀
  unfold dqIK dqIIK at H
  rw [CTG.GaussMoment.gam₂_eq_one hn] at H
  have e : ∀ τ x, Lmet gauss (1 : ℝ) S (a τ) ξ f x = LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x :=
    fun τ x => Lmet_pop_lat 1 S (lt_of_lt_of_le ha₀ (ha τ)) hξ hf.continuous hB hper x
  simp only [e] at H
  exact H

/-! ### Stage 2: continuity in time for every sample, and measurability -/

/-- copy from the forty-first file. -/
theorem cont_of_lip {F : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ s t, |F t - F s| ≤ C * |t - s|) : Continuous F :=
  (LipschitzWith.of_dist_le_mul (K := ⟨C, hC⟩) fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hF y x).continuous

/-- copy from the forty-first file. -/
theorem fr_zero : fr (0 : E) = 0 :=
  fr_of_mem 0 fun i => by simp only [PiLp.zero_apply, zero_add]; constructor <;> norm_num

/-- **The self-term of the lattice kernel is at least `gauss 0 = 1`.** -/
theorem latK_self_ge (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (x : E) : 1 ≤ latK S (ξ / a) x x := by
  have h := nearest_le_latK S hξ ha₀ ha x x
  have e : perK (kap gauss S (ξ / a)) x x = 1 := by
    unfold perK kap gauss
    rw [sub_self, fr_zero]
    simp
  rw [e] at h; exact h

theorem sampAvgK_pos {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (ω : Ω) {j : ℕ} (hj : j < N) :
    0 < sampAvg X N (latK S (ξ / a)) j ω := by
  have hN' : (0:ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le j) hj)
  unfold sampAvg
  have hs : latK S (ξ / a) (X j ω) (X j ω)
      ≤ ∑ k ∈ Finset.range N, latK S (ξ / a) (X j ω) (X k ω) :=
    Finset.single_le_sum (f := fun k => latK S (ξ / a) (X j ω) (X k ω))
      (fun k _ => (latK_nonneg S hξ hξ1 ha₀ ha _ _).2.1) (Finset.mem_range.2 hj)
  have h1 := latK_self_ge S hξ ha₀ ha (X j ω)
  exact mul_pos (by positivity) (by linarith)

theorem denK_pos {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (ω : Ω) {i : ℕ} (hi : i < N) :
    0 < sampW X N (latK S (ξ / a)) (fun _ _ => 1) i ω := by
  have hN' : (0:ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i) hi)
  unfold sampW avgN
  have hterm : ∀ k ∈ Finset.range N, 0 ≤ latK S (ξ / a) (X i ω) (X k ω) * 1
      * (1 / sampAvg X N (latK S (ξ / a)) k ω) := fun k hk =>
    mul_nonneg (mul_nonneg (latK_nonneg S hξ hξ1 ha₀ ha _ _).2.1 zero_le_one)
      (one_div_pos.2 (sampAvgK_pos X S hξ hξ1 ha₀ ha ω (Finset.mem_range.1 hk))).le
  have hs := Finset.single_le_sum hterm (Finset.mem_range.2 hi)
  have hi0 : 0 < latK S (ξ / a) (X i ω) (X i ω) * 1
      * (1 / sampAvg X N (latK S (ξ / a)) i ω) := by
    rw [mul_one]
    exact mul_pos (lt_of_lt_of_le one_pos (latK_self_ge S hξ ha₀ ha _))
      (one_div_pos.2 (sampAvgK_pos X S hξ hξ1 ha₀ ha ω hi))
  exact mul_pos (by positivity) (lt_of_lt_of_le hi0 hs)

/-- **`τ ↦ LNK X N (latK S (ξ / a τ)) m₂ ξ f i ω` is continuous for EVERY sample `ω`** (no event). -/
theorem LNK_cont {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ} (ha₀ : 0 < a₀)
    (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1) (m₂ : ℝ) (f : E → ℝ) {i : ℕ} (hi : i < N) (ω : Ω) :
    Continuous fun τ => LNK X N (latK S (ξ / a τ)) m₂ ξ f i ω := by
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hBI : 0 ≤ cIk a₀ a₁ La * Gb n S a₀ := by
    have := Gb_pos S a₀; unfold cIk; positivity
  have hK : ∀ x z : E, Continuous fun τ => latK S (ξ / a τ) x z := fun x z =>
    cont_of_lip hBI fun s t => latK_tlip S a a' hda ha₀ ha ha₁ hLa hξ hξ1 s t x z
  have hA : ∀ j, Continuous fun τ => sampAvg X N (latK S (ξ / a τ)) j ω := fun j =>
    cont_of_lip hBI fun s t => sampAvg_close X hN
      (fun x z => latK_tlip S a a' hda ha₀ ha ha₁ hLa hξ hξ1 s t x z) j ω
  have hW : ∀ g : E → E → ℝ,
      Continuous fun τ => sampW X N (latK S (ξ / a τ)) g i ω := by
    intro g
    unfold sampW avgN
    refine continuous_const.mul (continuous_finset_sum _ fun j hj => ?_)
    exact ((hK _ _).mul continuous_const).mul (continuous_const.div (hA j)
      fun τ => (sampAvgK_pos X S hξ hξ1 ha₀ (ha τ) ω (Finset.mem_range.1 hj)).ne')
  unfold LNK
  exact continuous_const.mul ((hW _).div (hW _)
    fun τ => (denK_pos X S hξ hξ1 ha₀ (ha τ) ω hi).ne')

/-- copy from the forty-first file. -/
theorem C2_nonneg {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    {M₄ a₀ La : ℝ} (hM₄ : 0 ≤ M₄) (ha₀ : 0 < a₀) (hLa : 0 ≤ La) (S : E ≃L[ℝ] E) :
    0 ≤ Ctwo M₄ μ₄ m₂ K₀ a₀ La S := by
  have hK := hk.kern.mass_pos
  have hμ₄ : 0 ≤ μ₄ := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  unfold Ctwo; positivity

/-- `τ ↦ Lmet gauss (gam₂ n) S (a τ) ξ f x` is continuous. -/
theorem Lmet_gauss_cont (hn : 1 ≤ n) {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : E) :
    Continuous fun τ => Lmet gauss (gam₂ n) S (a τ) ξ f x := by
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hm₂ := gam₂_pos hn
  have hC := C2_nonneg (radK_gauss (n := n)) hm₂ hM₄ ha₀ hLa0 S
  exact cont_of_lip
    (C := ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + |lapG S f x| * (2 * La / a₀ ^ 3))
    (by positivity) fun s t =>
      Lmet_lip (radK_gauss (n := n)) hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ x le_rfl s t

/-- **`τ ↦ LPK mT (latK S (ξ / a τ)) 1 ξ f x` is continuous.** -/
theorem LPK_cont (hn : 1 ≤ n) {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ B : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (hper : Per f)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : E) :
    Continuous fun τ => LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x := by
  have h := Lmet_gauss_cont hn hf hM hM₄ S a a' hda ha₀ ha hLa hξ x
  rw [CTG.GaussMoment.gam₂_eq_one hn] at h
  have e : (fun τ => LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x)
      = fun τ => Lmet gauss (1 : ℝ) S (a τ) ξ f x :=
    funext fun τ => (Lmet_pop_lat 1 S (lt_of_lt_of_le ha₀ (ha τ)) hξ hf.continuous hB hper x).symm
  rw [e]; exact h

theorem LPK_measurable {f : E → ℝ} (hf : ContDiff ℝ 4 f) {B : ℝ} (hper : Per f)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E) {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ) :
    Measurable fun x => LPK mT (latK S (ξ / a)) (1 : ℝ) ξ f x := by
  have e : (fun x => LPK mT (latK S (ξ / a)) (1 : ℝ) ξ f x) = Lmet gauss (1 : ℝ) S a ξ f :=
    funext fun x => (Lmet_pop_lat 1 S ha hξ hf.continuous hB hper x).symm
  rw [e]; exact Lmet_measurable CTG.FlatNPointGauss.gauss_continuous.measurable 1 S a ξ hf.continuous

/-- copy from the forty-first file: reduction of an existential over a set of parameters to a countable
dense subset. -/
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

/-- The domain of pairs of times. -/
def DpairK (p q η₀ : ℝ) : Set (ℝ × ℝ) := {t | t.1 ∈ Icc p q ∧ t.2 ∈ Icc p q ∧ η₀ ≤ |t.2 - t.1|}

/-- The two functions of one time whose difference quotients appear in the final form. -/
def FIF {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (i : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  LNK X N (latK S (ξ / a τ)) (1 : ℝ) ξ f i ω - LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f (X i ω)

def FIIF {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (i : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  LNK X N (latK S (ξ / a τ)) (1 : ℝ) ξ f i ω + lapG S f (X i ω) / a τ ^ 2

/-- The two difference quotients of the final form (named; `dqIF_def`/`dqIIF_def` by `rfl`). -/
def dqIF {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (τa τb : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
      - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
    - (LPK mT (latK S (ξ / a τb)) (1 : ℝ) ξ f (X i ω)
      - LPK mT (latK S (ξ / a τa)) (1 : ℝ) ξ f (X i ω)) / (τb - τa)

def dqIIF {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (τa τb : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
      - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
    + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)

set_option maxHeartbeats 1600000 in
/-- **Measurability of the exceptional set of the final window statement**, for arbitrary constants
`Er`, `C₁`, `C₂`.  No hypothesis on the sample beyond measurability of the `X j`. -/
theorem window_final_set_measurable (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : ℕ → Ω → E) (hX : ∀ j, Measurable (X j)) {N : ℕ} (hN : 0 < N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ B : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (hper : Per f)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {p q η₀ Er C₁ C₂ : ℝ} (hη₀ : 0 < η₀) :
    MeasurableSet {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqIF X N S a ξ f τa τb i ω| ≤ 2 * Er
        ∧ |dqIIF X N S a ξ f τa τb i ω| ≤ 2 * Er + 2 * popErr ξ C₁ C₂ (τb - τa))} := by
  have hne : ∀ t ∈ DpairK p q η₀, t.2 - t.1 ≠ 0 := fun t ht hz => by
    have h1 : η₀ ≤ |t.2 - t.1| := ht.2.2
    rw [hz, abs_zero] at h1; linarith
  have hac : Continuous a := continuous_iff_continuousAt.2 fun τ => (hda τ).continuousAt
  have hfc : Continuous f := hf.continuous
  have hLN : ∀ τ i, Measurable fun ω => LNK X N (latK S (ξ / a τ)) (1 : ℝ) ξ f i ω := fun τ i =>
    CTG.GaussMoment.LNK_measurable X hX N (CTG.GaussMoment.latK_measurable S hξ ha₀ (ha τ)) 1 ξ hfc i
  have hLP : ∀ τ, Measurable fun x => LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x := fun τ =>
    LPK_measurable hf hper hB S (lt_of_lt_of_le ha₀ (ha τ)) hξ
  have hG := fun i => (lapG_measurable S hf).comp (hX i)
  have hFI : ∀ i < N, ∀ ω, Continuous (FIF X N S a ξ f i ω) := fun i hi ω => by
    unfold FIF
    exact (LNK_cont X hN S a a' hda ha₀ ha ha₁ hLa hξ hξ1 1 f hi ω).sub
      (LPK_cont hn hf hM hM₄ hper hB S a a' hda ha₀ ha hLa hξ _)
  have hFII : ∀ i < N, ∀ ω, Continuous (FIIF X N S a ξ f i ω) := fun i hi ω => by
    unfold FIIF
    exact (LNK_cont X hN S a a' hda ha₀ ha ha₁ hLa hξ hξ1 1 f hi ω).add
      (continuous_const.div (hac.pow 2)
        fun τ => pow_ne_zero 2 (lt_of_lt_of_le ha₀ (ha τ)).ne')
  have hdiff : ContinuousOn (fun t : ℝ × ℝ => t.2 - t.1) (DpairK p q η₀) :=
    (continuous_snd.sub continuous_fst).continuousOn
  have eI : ∀ τa τb i ω, dqIF X N S a ξ f τa τb i ω
      = (FIF X N S a ξ f i ω τb - FIF X N S a ξ f i ω τa) / (τb - τa) := by
    intro τa τb i ω; unfold dqIF FIF; ring
  have eII : ∀ τa τb i ω, dqIIF X N S a ξ f τa τb i ω
      = (FIIF X N S a ξ f i ω τb - FIIF X N S a ξ f i ω τa) / (τb - τa) := by
    intro τa τb i ω; unfold dqIIF FIIF; ring
  have e : {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqIF X N S a ξ f τa τb i ω| ≤ 2 * Er ∧ |dqIIF X N S a ξ f τa τb i ω| ≤ 2 * Er + 2 * popErr ξ C₁ C₂ (τb - τa))}
      = ⋃ i, ⋃ (_ : i < N),
        ({ω | ∃ t ∈ DpairK p q η₀, 0 < |dqIF X N S a ξ f t.1 t.2 i ω| - 2 * Er}
        ∪ {ω | ∃ t ∈ DpairK p q η₀, 0 < |dqIIF X N S a ξ f t.1 t.2 i ω|
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
  · refine exists_param_measurable (F := fun t ω => |dqIF X N S a ξ f t.1 t.2 i ω| - 2 * Er) ?_ ?_
    · intro t _
      unfold dqIF
      exact ((((hLN t.2 i).sub (hLN t.1 i)).div_const _).sub
        ((((hLP t.2).comp (hX i)).sub ((hLP t.1).comp (hX i))).div_const _)).abs.sub_const _
    · intro ω
      have ee : (fun t : ℝ × ℝ => |dqIF X N S a ξ f t.1 t.2 i ω| - 2 * Er)
          = fun t => |(FIF X N S a ξ f i ω t.2 - FIF X N S a ξ f i ω t.1)
              / (t.2 - t.1)| - 2 * Er := by
        funext t; rw [eI]
      rw [ee]
      exact ((((hFI i hi ω).comp continuous_snd).sub
        ((hFI i hi ω).comp continuous_fst)).continuousOn.div hdiff hne).abs.sub continuousOn_const
  · refine exists_param_measurable
      (F := fun t ω => |dqIIF X N S a ξ f t.1 t.2 i ω| - (2 * Er + 2 * popErr ξ C₁ C₂ (t.2 - t.1))) ?_ ?_
    · intro t _
      unfold dqIIF
      have hL1 := ((hLN t.2 i).sub (hLN t.1 i)).div_const (t.2 - t.1)
      have hL2 := (((hG i).div_const (a t.2 ^ 2)).sub ((hG i).div_const (a t.1 ^ 2))).div_const
        (t.2 - t.1)
      exact (hL1.add hL2).abs.sub_const _
    · intro ω
      have ee : (fun t : ℝ × ℝ => |dqIIF X N S a ξ f t.1 t.2 i ω|
            - (2 * Er + 2 * popErr ξ C₁ C₂ (t.2 - t.1)))
          = fun t => |(FIIF X N S a ξ f i ω t.2 - FIIF X N S a ξ f i ω t.1)
              / (t.2 - t.1)| - (2 * Er + 2 * (ξ ^ 2 * min (C₁ / |t.2 - t.1|) C₂)) := by
        funext t; rw [eII]; rfl
      rw [ee]
      refine ((((hFII i hi ω).comp continuous_snd).sub
        ((hFII i hi ω).comp continuous_fst)).continuousOn.div hdiff hne).abs.sub
        (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.mul
          (ContinuousOn.inf (continuousOn_const.div hdiff.abs
            fun t ht => abs_ne_zero.2 (hne t ht)) continuousOn_const))))

set_option maxHeartbeats 1600000 in
/-- **The exceptional set of `flat_npoint_lattice_window_final`, literally, is measurable.** -/
theorem flat_npoint_lattice_window_final_set_measurable (hn : 1 ≤ n) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → E) (hX : ∀ j, Measurable (X j)) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (hper : Per f)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    MeasurableSet {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
          - (LPK mT (latK S (ξ / a τb)) (1 : ℝ) ξ f (X i ω)
              - LPK mT (latK S (ξ / a τa)) (1 : ℝ) ξ f (X i ω)) / (τb - τa)|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (1 : ℝ) (4 * Real.log N) N ξ
        ∧ |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
            + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (1 : ℝ) (4 * Real.log N) N ξ
            + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (1 : ℝ) (gaK₀ n) a₀ S)
                (Ctwo M₄ (gaμ₄ n) (1 : ℝ) (gaK₀ n) a₀ La S) (τb - τa))} :=
  window_final_set_measurable hn X hX (by omega) hf hM hM₄ hper hB S a a' hda ha₀ ha ha₁ hLa hξ hξ1
    hη₀

set_option maxHeartbeats 1600000 in
/-- **The exceptional set of `flat_npoint_lattice_window_N2` (with `gam₂ n` and `Lmet gauss`),
literally, is measurable.** -/
theorem flat_npoint_lattice_window_N2_set_measurable (hn : 1 ≤ n) {Ω : Type*}
    {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → E) (hX : ∀ j, Measurable (X j)) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (hper : Per f)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    MeasurableSet {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqIK X N S a ξ f τa τb i ω|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) (4 * Real.log N) N ξ
        ∧ |dqIIK X N S a ξ f τa τb i ω|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) (4 * Real.log N) N ξ
            + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
                (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (τb - τa))} := by
  have H := flat_npoint_lattice_window_final_set_measurable (Lip := Lip) hn X hX N hN hf hM hM₄
    hper hB S a a' hda ha₀ ha ha₁ hLa hξ hξ1 (p := p) (q := q) hη₀
  unfold dqIK dqIIK
  rw [CTG.GaussMoment.gam₂_eq_one hn]
  have e : ∀ τ x, Lmet gauss (1 : ℝ) S (a τ) ξ f x = LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x :=
    fun τ x => Lmet_pop_lat 1 S (lt_of_lt_of_le ha₀ (ha τ)) hξ hf.continuous hB hper x
  simp only [e]
  exact H

end CTG.FlatNPointLatticeWindowFinal
