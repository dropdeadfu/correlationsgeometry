/-
Fifty-third file: the normalising second moment of the Gaussian profile equals one.
Namespace `CTG.GaussMoment`; imports the fifty-second file (compiled module); check with `./check_gauss_moment.sh`.
`radial`: `∫_0^∞ y^q exp(−y²/2) dy` through the Gamma function; `norm_int`: `∫_{ℝⁿ} ‖z‖^k exp(−‖z‖²/2) dz` by the
radial integration formula of Mathlib; `second_moment`: `(∫ ‖z‖² g)/(n ∫ g) = 1` for `n ≥ 1`;
`gam₂_eq_one`: the constant `gam₂ n` of the fifty-second file equals `1`, so that `m₂ = 1` in
`flat_npoint_lattice_direct` (the normalisation `c_h = 1` of the paper for the Gaussian profile).
`flat_npoint_lattice_final`: the statement of the fifty-second file with `m₂ = 1` and with the population
operator of the same lattice-sum kernel on the population side.
`latK_measurable`, `LNK_measurable`, `exc_measurable`, `flat_npoint_lattice_final_set_measurable`: the exceptional
set of the final form is measurable.
No hypothesis in the moment statements.  No sorry, no axiom, no native_decide.
Written by the author-side AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryFlatNPointLatticeDirect

open MeasureTheory Real Set

noncomputable section
namespace CTG.GaussMoment

open CTG.FlatNPointGauss (gauss)
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- radial integral `∫_0^∞ y^q exp(−y²/2) dy`. -/
lemma radial (q : ℝ) (hq : -1 < q) :
    ∫ y in Ioi (0:ℝ), y ^ q * Real.exp (-(1/2) * y ^ (2:ℝ)) =
      (1/2:ℝ) ^ (-(q + 1) / 2) * (1 / 2) * Real.Gamma ((q + 1) / 2) :=
  integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hq (by norm_num)

lemma nontriv (hn : 1 ≤ n) : Nontrivial E := by
  apply Module.nontrivial_of_finrank_pos (R := ℝ)
  rw [finrank_euclideanSpace_fin]; omega

lemma norm_int (hn : 1 ≤ n) (k : ℕ) :
    ∫ z : E, ‖z‖ ^ k * gauss ‖z‖ =
      (n : ℝ) * (volume.real (Metric.ball (0 : E) 1) *
        ((1/2:ℝ) ^ (-((n:ℝ) - 1 + k + 1) / 2) * (1 / 2) * Real.Gamma (((n:ℝ) - 1 + k + 1) / 2))) := by
  haveI := nontriv (n := n) hn
  have h := integral_fun_norm_addHaar (volume : Measure E) (fun r : ℝ => r ^ k * gauss r)
  rw [h, finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
  congr 2
  rw [← radial ((n:ℝ) - 1 + k) (by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    have : (0:ℝ) ≤ k := Nat.cast_nonneg k
    linarith)]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy' : (0:ℝ) < y := hy
  have e1 : y ^ ((n:ℝ) - 1 + k) = y ^ (n - 1) * y ^ k := by
    rw [Real.rpow_add hy', Real.rpow_natCast, ← Real.rpow_natCast y (n - 1), Nat.cast_sub hn,
      Nat.cast_one]
  have e2 : Real.exp (-(1/2) * y ^ (2:ℝ)) = gauss y := by
    unfold gauss; rw [Real.rpow_two]; congr 1; ring
  show y ^ (n - 1) • (y ^ k * gauss y) = _
  rw [e1, e2, smul_eq_mul]; ring

/-- The second moment of the Gaussian profile per coordinate, normalised by the mass, equals `1`. -/
theorem second_moment (hn : 1 ≤ n) :
    (∫ z : E, ‖z‖ ^ 2 * gauss ‖z‖) / (n * ∫ z : E, gauss ‖z‖) = 1 := by
  have h2 := norm_int (n := n) hn 2
  have h0 := norm_int (n := n) hn 0
  simp only [pow_zero, one_mul] at h0
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  haveI := nontriv (n := n) hn
  have hV : 0 < volume.real (Metric.ball (0 : E) 1) := by
    exact ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne'
      (measure_ball_lt_top).ne
  have hG : Real.Gamma (((n:ℝ) - 1 + (2:ℕ) + 1) / 2) = (n:ℝ) / 2 * Real.Gamma ((n:ℝ) / 2) := by
    rw [show ((n:ℝ) - 1 + (2:ℕ) + 1) / 2 = (n:ℝ) / 2 + 1 by push_cast; ring]
    exact Real.Gamma_add_one (by positivity)
  have hG0 : 0 < Real.Gamma ((n:ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hp : (1/2:ℝ) ^ (-((n:ℝ) - 1 + (2:ℕ) + 1) / 2) = (1/2:ℝ) ^ (-((n:ℝ)) / 2) * 2 := by
    rw [show (-((n:ℝ) - 1 + (2:ℕ) + 1) / 2) = -(n:ℝ) / 2 + (-1) by push_cast; ring,
      Real.rpow_add (by norm_num), Real.rpow_neg_one]; norm_num
  have hp0 : (0:ℝ) < (1/2:ℝ) ^ (-((n:ℝ)) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  rw [h2, h0, hG, hp]
  have e0 : ((n:ℝ) - 1 + (0:ℕ) + 1) / 2 = (n:ℝ) / 2 := by push_cast; ring
  have e1 : (-((n:ℝ) - 1 + (0:ℕ) + 1) / 2) = -(n:ℝ) / 2 := by push_cast; ring
  rw [e0, e1]
  field_simp

/-- The constant `gam₂ n` of the fifty-second file equals `1`. -/
theorem gam₂_eq_one (hn : 1 ≤ n) : CTG.FlatNPointLatticeDirect.gam₂ n = 1 := by
  unfold CTG.FlatNPointLatticeDirect.gam₂ CTG.FlatNPointLatticeDirect.gaK₀
  exact second_moment hn


open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGaussLattice CTG.FlatNPointLatticePop
open ProbabilityTheory

/-- **Final flat form.** `flat_npoint_lattice_direct` with the normalisation `m₂ = 1` inserted
(`gam₂_eq_one`) and the population operator written as the normalised population operator `LPK` of the SAME
lattice-sum kernel (`Lmet_pop_lat`): Proposition `prop:dotLN-diff`, both inequalities in the rate form, for the
periodised Gaussian kernel on the flat torus with the metrics `a(τ)² g₀`. -/
theorem flat_npoint_lattice_final (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * CTG.FlatNPointLatticeDirect.dLam S a₀ a₁ La Lip ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
          - (LPK mT (latK S (ξ / a τb)) (1 : ℝ) ξ f (X i ω)
              - LPK mT (latK S (ξ / a τa)) (1 : ℝ) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * CTG.FlatNPointLatticeDirect.dLam S a₀ a₁ La Lip ^ 20 / (1 : ℝ)
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * CTG.FlatNPointLatticeDirect.dLam S a₀ a₁ La Lip ^ 20 / (1 : ℝ)
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * CTG.FlatNPointLatticeDirect.gaμ₄ n
                / (6 * (1 : ℝ) * CTG.FlatNPointLatticeDirect.gaK₀ n * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * CTG.FlatNPointLatticeDirect.gaμ₄ n * La / (3 * (1 : ℝ) * CTG.FlatNPointLatticeDirect.gaK₀ n * a₀ ^ 5)))}
      ≤ 30 / (N : ℝ) ^ 2 := by
  have h := CTG.FlatNPointLatticeDirect.flat_npoint_lattice_direct hn X h_indep hX hlaw N hN hf hM hM₄ hper
    hLip0 hLip hB S a a' hda ha₀ ha ha₁ hLa hξ hξ1 τa τb hne hNL
  rw [gam₂_eq_one hn] at h
  have e : ∀ τ x, Lmet gauss (1 : ℝ) S (a τ) ξ f x = LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x :=
    fun τ x => Lmet_pop_lat 1 S (lt_of_lt_of_le ha₀ (ha τ)) hξ hf.continuous hB hper x
  simp only [e] at h
  exact h


/-! ### Measurability of the exceptional set -/

open Filter Topology in
/-- The lattice-sum kernel is jointly measurable. -/
theorem latK_measurable (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a) :
    Measurable fun p : E × E => latK S (ξ / a) p.1 p.2 := by
  have hterm : ∀ m : Fin n → ℤ, Measurable fun p : E × E =>
      gauss (‖S.symm (fr (p.2 - p.1) + latV m)‖ / (ξ / a)) := fun m =>
    CTG.FlatNPointGauss.gauss_continuous.measurable.comp
      (((continuous_norm.comp S.symm.continuous).measurable.comp
        ((fr_measurable.comp (measurable_snd.sub measurable_fst)).add_const _)).div_const _)
  refine measurable_of_tendsto_metrizable' atTop
    (f := fun (s : Finset (Fin n → ℤ)) (p : E × E) =>
      ∑ m ∈ s, gauss (‖S.symm (fr (p.2 - p.1) + latV m)‖ / (ξ / a)))
    (fun s => Finset.measurable_sum _ fun m _ => hterm m) ?_
  rw [tendsto_pi_nhds]
  intro p
  exact (latK_summable S hξ ha₀ ha p.1 p.2).hasSum

theorem LNK_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : ℕ → Ω → E)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) {K : E → E → ℝ}
    (hK : Measurable fun p : E × E => K p.1 p.2) (m₂ ξ : ℝ) {f : E → ℝ} (hfc : Continuous f) (i : ℕ) :
    Measurable fun ω => LNK X N K m₂ ξ f i ω := by
  have hg : Measurable fun p : E × E => gd f p.1 p.2 :=
    (hfc.measurable.comp measurable_snd).sub (hfc.measurable.comp measurable_fst)
  unfold LNK
  exact ((sampW_measurable X hX N hK hg i).div
    (sampW_measurable X hX N hK measurable_const i)).const_mul _

/-- generic shape of the exceptional sets. -/
theorem exc_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (N : ℕ) (A B G : ℕ → Ω → ℝ)
    (hA : ∀ i, Measurable (A i)) (hB : ∀ i, Measurable (B i)) (hG : ∀ i, Measurable (G i))
    (c₁ c₂ : ℝ) :
    MeasurableSet {ω | ∃ i < N, ¬ (|A i ω - B i ω| ≤ c₁ ∧ |A i ω + G i ω| ≤ c₂)} := by
  have e : {ω | ∃ i < N, ¬ (|A i ω - B i ω| ≤ c₁ ∧ |A i ω + G i ω| ≤ c₂)}
      = ⋃ i : ℕ, {ω | i < N ∧ ¬ (|A i ω - B i ω| ≤ c₁ ∧ |A i ω + G i ω| ≤ c₂)} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [e]
  refine MeasurableSet.iUnion fun i => (MeasurableSet.const (i < N)).inter ?_
  refine MeasurableSet.compl (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le ((hA i).sub (hB i)).abs measurable_const
  · exact measurableSet_le ((hA i).add (hG i)).abs measurable_const

/-- **The exceptional set of `flat_npoint_lattice_final` is measurable.** -/
theorem flat_npoint_lattice_final_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : ℕ → Ω → E) (hX : ∀ j, Measurable (X j)) (N : ℕ)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hper : Per f) (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a : ℝ → ℝ) {a₀ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hξ : 0 < ξ) (τa τb : ℝ) (a₁ : ℝ) :
    MeasurableSet {ω | ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
          - (LPK mT (latK S (ξ / a τb)) (1 : ℝ) ξ f (X i ω)
              - LPK mT (latK S (ξ / a τa)) (1 : ℝ) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * CTG.FlatNPointLatticeDirect.dLam S a₀ a₁ La Lip ^ 20 / (1 : ℝ)
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * CTG.FlatNPointLatticeDirect.dLam S a₀ a₁ La Lip ^ 20 / (1 : ℝ)
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * CTG.FlatNPointLatticeDirect.gaμ₄ n
                / (6 * (1 : ℝ) * CTG.FlatNPointLatticeDirect.gaK₀ n * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * CTG.FlatNPointLatticeDirect.gaμ₄ n * La / (3 * (1 : ℝ) * CTG.FlatNPointLatticeDirect.gaK₀ n * a₀ ^ 5)))} := by
  have hfc : Continuous f := hf.continuous
  have hLN : ∀ τ i, Measurable fun ω => LNK X N (latK S (ξ / a τ)) (1 : ℝ) ξ f i ω := fun τ i =>
    LNK_measurable X hX N (latK_measurable S hξ ha₀ (ha τ)) 1 ξ hfc i
  have hLP : ∀ τ, Measurable fun x => LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x := by
    intro τ
    have e : (fun x => LPK mT (latK S (ξ / a τ)) (1 : ℝ) ξ f x) = Lmet gauss (1 : ℝ) S (a τ) ξ f :=
      funext fun x => (Lmet_pop_lat 1 S (lt_of_lt_of_le ha₀ (ha τ)) hξ hfc hB hper x).symm
    rw [e]; exact Lmet_measurable CTG.FlatNPointGauss.gauss_continuous.measurable 1 S (a τ) ξ hfc
  have hG := fun i => (lapG_measurable S hf).comp (hX i)
  exact exc_measurable N
    (fun i ω => (LNK X N (latK S (ξ / a τb)) (1 : ℝ) ξ f i ω
      - LNK X N (latK S (ξ / a τa)) (1 : ℝ) ξ f i ω) / (τb - τa))
    (fun i ω => (LPK mT (latK S (ξ / a τb)) (1 : ℝ) ξ f (X i ω)
      - LPK mT (latK S (ξ / a τa)) (1 : ℝ) ξ f (X i ω)) / (τb - τa))
    (fun i ω => (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa))
    (fun i => ((hLN τb i).sub (hLN τa i)).div_const _)
    (fun i => ((((hLP τb).comp (hX i)).sub ((hLP τa).comp (hX i)))).div_const _)
    (fun i => (((hG i).div_const _).sub ((hG i).div_const _)).div_const _) _ _

end CTG.GaussMoment
