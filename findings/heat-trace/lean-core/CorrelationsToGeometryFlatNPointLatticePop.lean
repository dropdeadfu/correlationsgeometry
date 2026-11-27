/-
Fiftieth file: the population side of `flat_npoint_lattice` as the population operator of the lattice-sum
kernel `latK`.  Imports the forty-seventh file (compiled module).  Written by a sub-task of an AI session on
27 November 2026; read by nobody.  Namespace `CTG.FlatNPointLatticePop`; check with `./check_flat_npoint_lattice_pop.sh`.  Probabilities are bounds for the outer measure; the error terms are those of `flat_npoint_lattice`, unchanged.
* `hasSum_fd`: for integrable `f` on `ℝⁿ`, `Σ_{g ∈ ℤⁿ} ∫_{[0,1)ⁿ} f(g + z) dz = ∫_{ℝⁿ} f` (as `HasSum`).
* `latE`: the bijection `ℤⁿ ≃ Lat`, `m ↦ latV m`.
* `tsum_fr_shift`: `Σ_m Φ(fr y + m) = Σ_{g ∈ Lat} Φ(g + y)` (reindexing, no summability needed).
* `lat_unfold`: for integrable `Φ`, `∫_{[0,1)ⁿ} Σ_m Φ(fr(z − x) + m) dz = ∫_{ℝⁿ} Φ`.
* `latK_integral` (statement (1)): for continuous, bounded, `ℤⁿ`-periodic `f`,
  `∫_{ℝⁿ} gauss(‖S⁻¹y‖/ξ') f(x + y) dy = ∫ latK S ξ' x z · f(z) dmT(z)`; `latK_integral'` with `y − x`.
* `popAvg_latK`, `popW_latK_one`, `popW_latK_gd`, `pop_ratio_lat`, `Lmet_pop_lat` (statement (2)).
* `LPK`, `flat_npoint_lattice_both` (statement (3)): `flat_npoint_lattice` with the normalised population
  operator of the SAME kernel `latK` in place of `Lmet gauss`.
No sorry, no axiom, no native_decide.
-/
import CorrelationsToGeometryFlatNPointGaussLattice

open MeasureTheory ProbabilityTheory Set
open scoped Pointwise
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss CTG.FlatNPointGaussFull
  CTG.FlatNPointGaussLattice

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointLatticePop

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Unfolding over the lattice -/

theorem fd : IsAddFundamentalDomain (Lat (n := n)).toAddSubgroup (DT (n := n)) volume :=
  ZSpan.isAddFundamentalDomain' _ volume

theorem vadd_eq (g : (Lat (n := n)).toAddSubgroup) (z : E) : g +ᵥ z = (g : E) + z := rfl

/-- `Σ_{g ∈ ℤⁿ} ∫_{[0,1)ⁿ} f(g + z) dz = ∫ f`, for integrable `f`. -/
theorem hasSum_fd {f : E → ℝ} (hf : Integrable f) :
    HasSum (fun g : (Lat (n := n)).toAddSubgroup => ∫ z in DT (n := n), f ((g : E) + z))
      (∫ v, f v) := by
  have hs := fd (n := n)
  have h1 : HasSum (fun g : (Lat (n := n)).toAddSubgroup => ∫ z in g +ᵥ DT (n := n), f z)
      (∫ v, f v) := by
    have hf' : Integrable f (Measure.sum fun g : (Lat (n := n)).toAddSubgroup =>
        (volume : Measure E).restrict (g +ᵥ DT (n := n))) := by
      rw [hs.sum_restrict]; exact hf
    have := hasSum_integral_measure hf'
    rwa [hs.sum_restrict] at this
  convert h1 using 1
  funext g
  rw [← image_vadd, (measurePreserving_vadd g (volume : Measure E)).setIntegral_image_emb
    (measurableEmbedding_const_vadd _) f (DT (n := n))]
  rfl

theorem latV_mem (m : Fin n → ℤ) : latV m ∈ Lat (n := n) :=
  (mem_Lat _).2 fun i => ⟨m i, by rw [latV_apply]⟩

/-- The bijection `ℤⁿ ≃ Lat`. -/
def latE : (Fin n → ℤ) ≃ (Lat (n := n)).toAddSubgroup :=
  Equiv.ofBijective (fun m => ⟨latV m, latV_mem m⟩) (by
    constructor
    · intro m m' h
      have h' : latV m = latV m' := congrArg Subtype.val h
      funext i
      have := congrArg (fun v : E => v i) h'
      simp only [latV_apply] at this
      exact_mod_cast this
    · intro g
      have hg : (g : E) ∈ Lat (n := n) := g.2
      rw [mem_Lat] at hg
      choose k hk using hg
      refine ⟨k, Subtype.ext ?_⟩
      ext i
      show latV k i = (g : E) i
      rw [latV_apply, hk i])

theorem latE_coe (m : Fin n → ℤ) : ((latE m : (Lat (n := n)).toAddSubgroup) : E) = latV m := rfl

/-- Reindexing: `Σ_m Φ(fr y + latV m) = Σ_{g ∈ Lat} Φ(g + y)`. -/
theorem tsum_fr_shift (Φ : E → ℝ) (y : E) :
    ∑' m : Fin n → ℤ, Φ (fr y + latV m)
      = ∑' g : (Lat (n := n)).toAddSubgroup, Φ ((g : E) + y) := by
  set w : (Lat (n := n)).toAddSubgroup := ⟨y - fr y, sub_fr_mem y⟩ with hw
  have e1 : ∑' m : Fin n → ℤ, Φ (fr y + latV m)
      = ∑' g : (Lat (n := n)).toAddSubgroup, Φ (fr y + (g : E)) :=
    (latE (n := n)).tsum_eq (fun g : (Lat (n := n)).toAddSubgroup => Φ (fr y + (g : E)))
  rw [e1, ← (Equiv.addRight w).tsum_eq]
  refine tsum_congr fun g => ?_
  congr 1
  show fr y + ((g : E) + (y - fr y)) = (g : E) + y
  abel

/-- **Unfolding over the lattice.** For integrable `Φ`,
`∫_{[0,1)ⁿ} Σ_{m ∈ ℤⁿ} Φ(fr(z − x) + m) dz = ∫_{ℝⁿ} Φ`. -/
theorem lat_unfold {Φ : E → ℝ} (hΦ : Integrable Φ) (x : E) :
    ∫ z in DT (n := n), ∑' m : Fin n → ℤ, Φ (fr (z - x) + latV m) = ∫ v, Φ v := by
  set Ψ : E → ℝ := fun y => Φ (y - x) with hΨ
  have hΨi : Integrable Ψ := hΦ.comp_sub_right x
  have e : (fun z => ∑' m : Fin n → ℤ, Φ (fr (z - x) + latV m))
      = fun z => ∑' g : (Lat (n := n)).toAddSubgroup, Ψ ((g : E) + z) := by
    funext z
    rw [tsum_fr_shift]
    refine tsum_congr fun g => ?_
    show Φ _ = Φ (((g : E) + z) - x)
    congr 1; abel
  rw [e]
  have hint : ∀ g : (Lat (n := n)).toAddSubgroup,
      Integrable (fun z => Ψ ((g : E) + z)) ((volume : Measure E).restrict (DT (n := n))) :=
    fun g => (hΨi.comp_add_left (g : E)).integrableOn
  have hsum : Summable fun g : (Lat (n := n)).toAddSubgroup =>
      ∫ z in DT (n := n), ‖Ψ ((g : E) + z)‖ :=
    (hasSum_fd (f := fun y => ‖Ψ y‖) hΨi.norm).summable
  rw [← integral_tsum_of_summable_integral_norm hint hsum, (hasSum_fd hΨi).tsum_eq]
  exact integral_sub_right_eq_self Φ x

/-! ### Statement (1): the ℝⁿ integral is the cube integral of the lattice-sum kernel -/

theorem kapG_integrable (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') {φ : E → ℝ} (hφ : Continuous φ)
    {B : ℝ} (hB : ∀ y, |φ y| ≤ B) :
    Integrable (fun y : E => gauss (‖S.symm y‖ / ξ') * φ y) :=
  gauss_kap_integrable S hξ hφ hB gauss_continuous (fun s => (gauss_pos s).le) (fun s => le_rfl)

/-- **Statement (1).**  For continuous, bounded, `ℤⁿ`-periodic `f` and every `x`,
`∫_{ℝⁿ} gauss(‖S⁻¹y‖/ξ') f(x + y) dy = ∫_{[0,1)ⁿ} latK S ξ' x z · f(z) dz`. -/
theorem latK_integral (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') {f : E → ℝ} (hfc : Continuous f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (hper : Per f) (x : E) :
    ∫ y, gauss (‖S.symm y‖ / ξ') * f (x + y) = ∫ z, latK S ξ' x z * f z ∂mT := by
  have hφ : Continuous fun y : E => f (x + y) := hfc.comp (continuous_const.add continuous_id)
  have hi := kapG_integrable S hξ hφ (fun y => hB (x + y))
  rw [← lat_unfold hi x]
  show _ = ∫ z in DT (n := n), latK S ξ' x z * f z
  refine setIntegral_congr_fun DT_measurable fun z _ => ?_
  show ∑' m : Fin n → ℤ, gauss (‖S.symm (fr (z - x) + latV m)‖ / ξ') * f (x + (fr (z - x) + latV m))
    = (∑' m : Fin n → ℤ, gauss (‖S.symm (fr (z - x) + latV m)‖ / ξ')) * f z
  rw [← tsum_mul_right]
  refine tsum_congr fun m => ?_
  congr 1
  have h1 := per_fr hper x z
  have h2 := hper (latV m) (latV_mem m) (x + fr (z - x))
  rw [show x + (fr (z - x) + latV m) = latV m + (x + fr (z - x)) by abel, h2, ← h1]

/-- Statement (1) with the kernel written as a function of `y − x`. -/
theorem latK_integral' (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') {f : E → ℝ} (hfc : Continuous f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (hper : Per f) (x : E) :
    ∫ y, gauss (‖S.symm (y - x)‖ / ξ') * f y = ∫ z, latK S ξ' x z * f z ∂mT := by
  rw [← latK_integral S hξ hfc hB hper x,
    ← integral_add_left_eq_self (fun y => gauss (‖S.symm (y - x)‖ / ξ') * f y) x]
  simp only [add_sub_cancel_left]

/-- The mass of the lattice-sum kernel over the cube is the mass of the flat Gaussian kernel. -/
theorem latK_mass (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') (x : E) :
    ∫ z, latK S ξ' x z ∂mT = ∫ v, kap gauss S ξ' v := by
  have h := latK_integral S hξ (f := fun _ => (1:ℝ)) continuous_const (B := 1)
    (fun _ => by simp) (fun _ _ _ => rfl) x
  simp only [mul_one] at h
  rw [← h]; rfl

theorem kapG_mass_pos (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') : 0 < ∫ v, kap gauss S ξ' v := by
  rw [kap_int gauss S hξ, gauss_integral]
  have := dS_pos S
  positivity

/-! ### Statement (2): `PG gauss` and `Lmet gauss` as population operators of `latK` -/

/-- The normalisation of the lattice-sum kernel is the constant `∫ κ`. -/
theorem popAvg_latK (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') (y : E) :
    popAvg mT (latK S ξ') y = ∫ v, kap gauss S ξ' v :=
  latK_mass S hξ y

theorem popW_latK_one (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') (x : E) :
    popW mT (latK S ξ') (fun _ _ => 1) x = 1 := by
  have hp := kapG_mass_pos S hξ
  unfold popW wKer
  simp only [popAvg_latK S hξ, mul_one]
  show ∫ z, latK S ξ' x z * (1 / ∫ v, kap gauss S ξ' v) ∂mT = 1
  rw [integral_mul_const, latK_mass S hξ x]
  field_simp

theorem popW_latK_gd (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') {f : E → ℝ} (hfc : Continuous f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (hper : Per f) (x : E) :
    popW mT (latK S ξ') (gd f) x
      = (∫ y, kap gauss S ξ' y * (f (x + y) - f x)) * (1 / ∫ v, kap gauss S ξ' v) := by
  unfold popW wKer
  simp only [popAvg_latK S hξ]
  show ∫ z, latK S ξ' x z * (f z - f x) * (1 / ∫ v, kap gauss S ξ' v) ∂mT = _
  rw [integral_mul_const]
  congr 1
  have hc : Continuous fun y => f y - f x := hfc.sub continuous_const
  have hB' : ∀ y, |f y - f x| ≤ 2 * B := fun y => by
    calc |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB y, hB x]
  have hper' : Per fun y => f y - f x := fun g hg z => by
    show f (g + z) - f x = f z - f x
    rw [hper g hg z]
  exact (latK_integral S hξ hc hB' hper' x).symm

/-- **Statement (2a).**  `popW(latK, f(y) − f(x)) / popW(latK, 1) = PG gauss − f`. -/
theorem pop_ratio_lat (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') {f : E → ℝ} (hfc : Continuous f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) (hper : Per f) (x : E) :
    popW mT (latK S ξ') (gd f) x / popW mT (latK S ξ') (fun _ _ => 1) x
      = PG gauss S ξ' f x - f x := by
  have hp := kapG_mass_pos S hξ
  rw [popW_latK_one S hξ, div_one, popW_latK_gd S hξ hfc hB hper]
  have hφ : Continuous fun y : E => f (x + y) := hfc.comp (continuous_const.add continuous_id)
  have hI3 : Integrable fun y => kap gauss S ξ' y * f (x + y) :=
    kapG_integrable S hξ hφ (fun y => hB (x + y))
  have hI2 : Integrable fun y => kap gauss S ξ' y * f x := by
    have := kapG_integrable S hξ (φ := fun _ => f x) continuous_const (B := |f x|) (fun _ => le_rfl)
    exact this
  have e : ∫ y, kap gauss S ξ' y * (f (x + y) - f x)
      = (∫ y, kap gauss S ξ' y * f (x + y)) - (∫ v, kap gauss S ξ' v) * f x := by
    rw [show (fun y => kap gauss S ξ' y * (f (x + y) - f x))
        = fun y => kap gauss S ξ' y * f (x + y) - kap gauss S ξ' y * f x from funext fun y => by ring,
      integral_sub hI3 hI2, integral_mul_const]
  rw [e]
  unfold PG
  show _ = (∫ y : E, kap gauss S ξ' y * f (x + y)) / (∫ y : E, kap gauss S ξ' y) - f x
  field_simp

/-- Normalised population operator of an arbitrary kernel `K` (the population counterpart of `LNK`). -/
def LPK (m : Measure E) (K : E → E → ℝ) (m₂ ξ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  -(2 / (m₂ * ξ ^ 2)) * (popW m K (gd f) x / popW m K (fun _ _ => 1) x)

/-- **Statement (2b).**  `Lmet gauss` is the normalised population operator of the lattice-sum kernel. -/
theorem Lmet_pop_lat (m₂ : ℝ) (S : E ≃L[ℝ] E) {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ) {f : E → ℝ}
    (hfc : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (hper : Per f) (x : E) :
    Lmet gauss m₂ S a ξ f x = LPK mT (latK S (ξ / a)) m₂ ξ f x := by
  unfold LPK
  rw [pop_ratio_lat S (div_pos hξ ha) hfc hB hper x]
  unfold Lmet; ring

/-! ### Statement (3): the lattice-sum kernel on both sides -/

set_option maxHeartbeats 1600000 in
/-- **Statement (3).**  `flat_npoint_lattice` with the normalised population operator of the SAME kernel
`latK S (ξ/a(τ))` (with respect to the uniform law `mT` on the cube) in place of `Lmet gauss`.  Hypotheses,
error terms and probability as in `flat_npoint_lattice`. -/
theorem flat_npoint_lattice_both (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (gm₂ n R) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gm₂ n R) ξ f i ω) / (τb - τa)
          - (LPK mT (latK S (ξ / a τb)) (gm₂ n R) ξ f (X i ω)
              - LPK mT (latK S (ξ / a τa)) (gm₂ n R) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + 2 * (errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + (gauss R + latTail n S ξ a₀))
                (gauss R + latTail n S ξ a₀) B
              + errP n (gm₂ n R) ξ R B) / |τb - τa|
      ∧ |(LNK X N (latK S (ξ / a τb)) (gm₂ n R) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gm₂ n R) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * gm₂ n R * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * gm₂ n R * gK₀ n R * a₀ ^ 5))
          + 2 * errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + (gauss R + latTail n S ξ a₀))
                (gauss R + latTail n S ξ a₀) B / |τb - τa|)}
      ≤ 34 / (N : ℝ) ^ 2 := by
  have hfc : Continuous f := hf.continuous
  have key : ∀ τ y, LPK mT (latK S (ξ / a τ)) (gm₂ n R) ξ f y
      = Lmet gauss (gm₂ n R) S (a τ) ξ f y := fun τ y =>
    (Lmet_pop_lat (gm₂ n R) S (lt_of_lt_of_le ha₀ (ha τ)) hξ hfc hB hper y).symm
  simp only [key]
  exact flat_npoint_lattice hn X h_indep hX hlaw N hN hR hf hM hM₄ hper hLip0 hLip hB S a a' hda
    ha₀ ha ha₁ hLa hξ hξ1 hρh τa τb hne hNL

end CTG.FlatNPointLatticePop
