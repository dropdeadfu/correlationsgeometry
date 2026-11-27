/-
Fifty-second file: the flat N-point statement (both inequalities of `prop:dotLN-diff`, rate form) DIRECTLY for
the lattice-sum Gaussian kernel `latK`, without the cut-off radius `R` and without additional terms.
Namespace `CTG.FlatNPointLatticeDirect`; imports the fiftieth file (compiled module).  Check with `./check_flat_npoint_lattice_direct.sh`.  The sub-task was stopped before its report; the file was checked by the author-side session itself.  Probability is a bound for the outer measure (measurability not shown).  HYPOTHESES on `f`: Lipschitz with constant `Lip`, bounded by `B` (true for periodic `C¹` functions, not derived here).  NOT shown: that the second moment `gam₂ n` of the Gaussian profile equals 1; pairs of times uniformly; the kernel is the lattice sum of the profile `exp(−s²/2)`, the population operator `Lmet gauss` is identified with that of the same kernel by `Lmet_pop_lat` of the fiftieth file (not restated here).
Written by a sub-task of an AI session on 27 November 2026; read by nobody.

STAGE 1 (analysis, as a comment).  How `flat_npoint` / `flat_npoint_rate` depend on the profile:
* The probabilistic core is `CTG.NPointLip.step5g`; it is stated for ARBITRARY kernels `Ka Kb gf` on a
  probability space `m` and needs only the abstract template data: `Good m Ka BK vK`, `Good m Kb BK vK`,
  `Good m ((Kb−Ka)/η) BI vI`, the three `Good` for the products with `gf`, the `L¹` bounds `M, MI, MF, MFi`,
  lower bounds `c ≤ popAvg` and `cD ≤ popW(·,1)`, and the two smallness conditions.  This IS the "version
  for general kernels with abstract bounds"; nothing in it refers to the profile.
* The profile enters `flat_npoint` only through `good_per` (needs `Prof` = compact support with radius
  `< 1/2`, used for `int_per`/`unfold`), `popAvg_perK`, `popW_perK_one`, `Lmet_pop` (identification of the
  population ratio, again through `unfold`), and the HYPOTHESES `hBI`, `hMI`.  `flat_npoint_rate` adds
  `mass_eq`, `hBI_of`, `hMI_of` (Lipschitz profile with support in `[0,R]`) and the `Λ` bookkeeping
  (`Ctx`, `small'_le`, `err5g_le`, `err5g_scale`), which is again profile-free.
* Hence for `latK` one can call `step5g` directly.  Replacements: `lat_unfold` (for the `L¹` bounds and the
  masses), `popAvg_latK` / `popW_latK_one` / `Lmet_pop_lat` (identification, EXACT constant normalisation);
  the sup bounds come from the lattice decay `lat_term_le` of the forty-seventh file and the Gaussian
  domination `u^k e^{−u²/2} ≤ C_k e^{−u²/8}` (stage 2 below); the time difference quotient from the mean
  value theorem for `s ↦ gauss(t s)`.  The population second inequality uses `metric_dq_min` with a `RadK`
  for the full Gaussian profile `gauss` (proved here, `radK_gauss`).
No sorry, no axiom, no native_decide.
-/
import CorrelationsToGeometryFlatNPointLatticePop

open MeasureTheory ProbabilityTheory Set
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss CTG.FlatNPointGaussFull
  CTG.FlatNPointGaussLattice CTG.FlatNPointLatticePop

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointLatticeDirect

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Stage 2 (a): Gaussian domination in one variable -/

theorem gauss_half (u : ℝ) : gauss (u / 2) = Real.exp (-(u ^ 2) / 8) := by
  unfold gauss; congr 1; ring

theorem gauss_split (u : ℝ) :
    gauss u = Real.exp (-(u ^ 2) / 8) * Real.exp (-(3 * u ^ 2 / 8)) := by
  unfold gauss; rw [← Real.exp_add]; congr 1; ring

theorem sq_le_exp38 (u : ℝ) : u ^ 2 ≤ 3 * Real.exp (3 * u ^ 2 / 8) := by
  have := Real.add_one_le_exp (3 * u ^ 2 / 8)
  nlinarith [sq_nonneg u]

theorem four_le_exp38 (u : ℝ) : u ^ 4 ≤ 15 * Real.exp (3 * u ^ 2 / 8) := by
  have h := Real.pow_div_factorial_le_exp (3 * u ^ 2 / 8) (by positivity) 2
  norm_num [Nat.factorial] at h
  nlinarith [h, pow_nonneg (sq_nonneg u) 2]

theorem dom_core {u K : ℝ} (P : ℝ) (hP : P ≤ K * Real.exp (3 * u ^ 2 / 8)) :
    P * gauss u ≤ K * gauss (u / 2) := by
  rw [gauss_split, gauss_half]
  have e : Real.exp (3 * u ^ 2 / 8) * Real.exp (-(3 * u ^ 2 / 8)) = 1 := by
    rw [← Real.exp_add]; simp
  have hA := Real.exp_pos (-(u ^ 2) / 8)
  have hB := Real.exp_pos (-(3 * u ^ 2 / 8))
  calc P * (Real.exp (-(u ^ 2) / 8) * Real.exp (-(3 * u ^ 2 / 8)))
      ≤ (K * Real.exp (3 * u ^ 2 / 8)) * (Real.exp (-(u ^ 2) / 8) * Real.exp (-(3 * u ^ 2 / 8))) :=
        mul_le_mul_of_nonneg_right hP (by positivity)
    _ = K * Real.exp (-(u ^ 2) / 8) * (Real.exp (3 * u ^ 2 / 8) * Real.exp (-(3 * u ^ 2 / 8))) := by
        ring
    _ = K * Real.exp (-(u ^ 2) / 8) := by rw [e, mul_one]

theorem dom0 (u : ℝ) : gauss u ≤ gauss (u / 2) := by
  have h := dom_core (u := u) (K := 1) 1 (by
    have := Real.add_one_le_exp (3 * u ^ 2 / 8); nlinarith [sq_nonneg u])
  simpa using h

theorem dom2 (u : ℝ) : u ^ 2 * gauss u ≤ 3 * gauss (u / 2) := dom_core _ (sq_le_exp38 u)

theorem dom1 {u : ℝ} (hu : 0 ≤ u) : u * gauss u ≤ 4 * gauss (u / 2) := by
  have h1 : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
  apply dom_core
  have := Real.add_one_le_exp (3 * u ^ 2 / 8)
  nlinarith [sq_le_exp38 u, Real.exp_pos (3 * u ^ 2 / 8)]

theorem dom3 {u : ℝ} (hu : 0 ≤ u) : u ^ 3 * gauss u ≤ 18 * gauss (u / 2) := by
  have h1 : u ^ 3 ≤ u ^ 2 + u ^ 4 := by nlinarith [sq_nonneg (u - 1), sq_nonneg u, mul_nonneg hu (sq_nonneg (u-1))]
  apply dom_core
  nlinarith [sq_le_exp38 u, four_le_exp38 u]

/-! ### Stage 2 (b): the mean value estimate for the time difference quotient -/

theorem gauss_scale_diff {t a₀ a₁ α β : ℝ} (ht : 0 ≤ t) (ha₀ : 0 ≤ a₀) (hα : a₀ ≤ α)
    (hα1 : α ≤ a₁) (hβ : a₀ ≤ β) (hβ1 : β ≤ a₁) :
    |gauss (t * β) - gauss (t * α)| ≤ t ^ 2 * a₁ * gauss (t * a₀) * |β - α| := by
  have hd : ∀ s, HasDerivAt (fun s => gauss (t * s)) (-(t * s) * gauss (t * s) * t) s := by
    intro s
    have h1 := (gauss_hasDerivAt (t * s)).comp s ((hasDerivAt_id' s).const_mul t)
    convert h1 using 1
    ring
  have hb : ∀ s ∈ Set.uIcc α β, ‖-(t * s) * gauss (t * s) * t‖ ≤ t ^ 2 * a₁ * gauss (t * a₀) := by
    intro s hs
    have hs' : a₀ ≤ s ∧ s ≤ a₁ := by
      rcases Set.mem_uIcc.1 hs with h | h
      · exact ⟨hα.trans h.1, h.2.trans hβ1⟩
      · exact ⟨hβ.trans h.1, h.2.trans hα1⟩
    have hts : 0 ≤ t * s := mul_nonneg ht (ha₀.trans hs'.1)
    have hg := gauss_anti (mul_nonneg ht ha₀) (mul_le_mul_of_nonneg_left hs'.1 ht)
    have hgp := gauss_pos (t * s)
    rw [Real.norm_eq_abs, show -(t * s) * gauss (t * s) * t = -(t * (t * s) * gauss (t * s)) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
    have ha1 : 0 ≤ a₁ := ha₀.trans (hα.trans hα1)
    calc t * (t * s) * gauss (t * s) ≤ t * (t * a₁) * gauss (t * a₀) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs'.2 ht) ht) hg
            hgp.le (by positivity)
      _ = t ^ 2 * a₁ * gauss (t * a₀) := by ring
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => gauss (t * s))
    (fun s _ => (hd s).hasDerivWithinAt) hb (convex_uIcc α β) Set.left_mem_uIcc Set.right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

/-! ### Stage 2 (c): lattice sums of dominated functions -/

/-- Lattice sum `Σ_{m ∈ ℤⁿ} Φ(fr(z − x) + m)`. -/
def latS (Φ : E → ℝ) (x z : E) : ℝ := ∑' m : Fin n → ℤ, Φ (fr (z - x) + latV m)

theorem latK_eq (S : E ≃L[ℝ] E) (ξ' : ℝ) (x z : E) :
    latK S ξ' x z = latS (fun y => gauss (‖S.symm y‖ / ξ')) x z := rfl

/-- The decay constant `c₀ = a₀²/(32(‖S‖+1)²)` (valid for all `ξ ≤ 1`). -/
def c0 (S : E ≃L[ℝ] E) (a₀ : ℝ) : ℝ := a₀ ^ 2 / (32 * (‖(S : E →L[ℝ] E)‖ + 1) ^ 2)

/-- The uniform bound `(1 + √(π/c₀))ⁿ` for lattice sums. -/
def Gb (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (a₀ : ℝ) : ℝ :=
  (1 + Real.sqrt (Real.pi / c0 S a₀)) ^ n

theorem c0_pos (S : E ≃L[ℝ] E) {a₀ : ℝ} (ha₀ : 0 < a₀) : 0 < c0 S a₀ := by
  unfold c0; positivity

theorem Gb_pos (S : E ≃L[ℝ] E) (a₀ : ℝ) : 0 < Gb n S a₀ := by
  unfold Gb; positivity

theorem c0_le_latC (S : E ≃L[ℝ] E) {ξ a₀ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀) :
    c0 S a₀ ≤ latC S (2 * ξ) a₀ := by
  unfold c0 latC
  have hM : 0 < (‖(S : E →L[ℝ] E)‖ + 1) ^ 2 := by positivity
  have hξ2 : ξ ^ 2 ≤ 1 := by nlinarith
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem lat_dom_term (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (v : E) (hv : ∀ i, |v i| ≤ 1 / 2) (m : Fin n → ℤ) :
    gauss (‖S.symm (v + latV m)‖ / (2 * ξ / a))
      ≤ Real.exp (-(c0 S a₀) * ∑ i, ((m i : ℤ) : ℝ) ^ 2) := by
  refine (lat_term_le S (by positivity : 0 < 2 * ξ) ha₀ ha v hv m).trans (Real.exp_le_exp.2 ?_)
  have := c0_le_latC S hξ hξ1 ha₀
  have hs : 0 ≤ ∑ i, ((m i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

/-- **Lattice sums of dominated functions**: summable, nonnegative and bounded by `C·Gb`. -/
theorem lat_bound (S : E ≃L[ℝ] E) {ξ a a₀ C : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (hC : 0 ≤ C) {Φ : E → ℝ} (hΦ0 : ∀ y, 0 ≤ Φ y)
    (hΦ : ∀ y, Φ y ≤ C * gauss (‖S.symm y‖ / (2 * ξ / a))) (x z : E) :
    Summable (fun m : Fin n → ℤ => Φ (fr (z - x) + latV m)) ∧ 0 ≤ latS Φ x z
      ∧ latS Φ x z ≤ C * Gb n S a₀ := by
  have hc := c0_pos S ha₀
  have hterm : ∀ m : Fin n → ℤ, Φ (fr (z - x) + latV m)
      ≤ C * Real.exp (-(c0 S a₀) * ∑ i, ((m i : ℤ) : ℝ) ^ 2) := fun m =>
    (hΦ _).trans (mul_le_mul_of_nonneg_left (lat_dom_term S hξ hξ1 ha₀ ha _ (abs_fr_le _) m) hC)
  have hsum := (CTG.Reals.gauss_summable hc n).mul_left C
  have hs : Summable (fun m : Fin n → ℤ => Φ (fr (z - x) + latV m)) :=
    Summable.of_nonneg_of_le (fun m => hΦ0 _) hterm hsum
  refine ⟨hs, tsum_nonneg fun m => hΦ0 _, ?_⟩
  calc latS Φ x z ≤ ∑' m : Fin n → ℤ, C * Real.exp (-(c0 S a₀) * ∑ i, ((m i : ℤ) : ℝ) ^ 2) :=
        Summable.tsum_le_tsum hterm hs hsum
    _ = C * ∑' m : Fin n → ℤ, Real.exp (-(c0 S a₀) * ∑ i, ((m i : ℤ) : ℝ) ^ 2) := tsum_mul_left
    _ ≤ C * Gb n S a₀ := mul_le_mul_of_nonneg_left (CTG.Reals.gauss_tsum_le hc n) hC

theorem latS_measurable {Φ : E → ℝ} (hΦ : Measurable Φ)
    (hs : ∀ x z, Summable fun m : Fin n → ℤ => Φ (fr (z - x) + latV m)) :
    Measurable fun p : E × E => latS Φ p.1 p.2 := by
  have hterm : ∀ m : Fin n → ℤ, Measurable fun p : E × E => Φ (fr (p.2 - p.1) + latV m) :=
    fun m => hΦ.comp ((fr_measurable.comp (measurable_snd.sub measurable_fst)).add_const _)
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Fin n → ℤ)))
    (f := fun s p => ∑ m ∈ s, Φ (fr (p.2 - p.1) + latV m))
    (fun s => Finset.measurable_sum s fun m _ => hterm m) ?_
  rw [tendsto_pi_nhds]
  intro p
  exact (hs p.1 p.2).hasSum

/-- Integrability of a function dominated by a scaled Gaussian kernel. -/
theorem dom_integrable (S : E ≃L[ℝ] E) {ξ'' C : ℝ} (hξ : 0 < ξ'') {Φ : E → ℝ} (hΦm : Measurable Φ)
    (hΦ0 : ∀ y, 0 ≤ Φ y) (hΦ : ∀ y, Φ y ≤ C * gauss (‖S.symm y‖ / ξ'')) : Integrable Φ := by
  have hi := kapG_integrable S hξ (φ := fun _ => C) continuous_const (B := |C|) (fun _ => le_rfl)
  refine hi.mono' hΦm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 y)]
  exact (hΦ y).trans (le_of_eq (by ring))

/-- The integral of a dominated function. -/
theorem dom_integral_le (S : E ≃L[ℝ] E) {ξ'' C : ℝ} (hξ : 0 < ξ'') {Φ : E → ℝ} (hΦm : Measurable Φ)
    (hΦ0 : ∀ y, 0 ≤ Φ y) (hΦ : ∀ y, Φ y ≤ C * gauss (‖S.symm y‖ / ξ'')) :
    ∫ y, Φ y ≤ C * ((2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * ξ'' ^ n) := by
  have hi := kapG_integrable S hξ (φ := fun _ => C) continuous_const (B := |C|) (fun _ => le_rfl)
  calc ∫ y, Φ y ≤ ∫ y, gauss (‖S.symm y‖ / ξ'') * C :=
        integral_mono_of_nonneg (ae_of_all _ hΦ0) hi (ae_of_all _ fun y => (hΦ y).trans
          (le_of_eq (by ring)))
    _ = (∫ y, kap gauss S ξ'' y) * C := integral_mul_const _ _
    _ = C * ((2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * ξ'' ^ n) := by
        rw [kap_int gauss S hξ, gauss_integral]; ring

/-- The scale bound `(2ξ/a)ⁿ ≤ 2ⁿ ξⁿ / a₀ⁿ`. -/
theorem scale_pow_le {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a) :
    (2 * ξ / a) ^ n ≤ 2 ^ n / a₀ ^ n * ξ ^ n := by
  have hapos : 0 < a := lt_of_lt_of_le ha₀ ha
  rw [div_pow, mul_pow]
  rw [show 2 ^ n / a₀ ^ n * ξ ^ n = 2 ^ n * ξ ^ n / a₀ ^ n by ring]
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos ha₀ n) (pow_le_pow_left₀ ha₀.le ha n)

/-- The mass constant `Ic = (2π)^{n/2} |det S| 2ⁿ / a₀ⁿ`. -/
def Ic (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (a₀ : ℝ) : ℝ :=
  (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * (2 ^ n / a₀ ^ n)

theorem Ic_pos (S : E ≃L[ℝ] E) {a₀ : ℝ} (ha₀ : 0 < a₀) : 0 < Ic n S a₀ := by
  have := dS_pos S; unfold Ic; positivity

theorem latS_measurable_right {Φ : E → ℝ} (hΦ : Measurable Φ) (x : E)
    (hs : ∀ z, Summable fun m : Fin n → ℤ => Φ (fr (z - x) + latV m)) :
    Measurable fun z : E => latS Φ x z := by
  have hterm : ∀ m : Fin n → ℤ, Measurable fun z : E => Φ (fr (z - x) + latV m) :=
    fun m => hΦ.comp ((fr_measurable.comp (measurable_id.sub measurable_const)).add_const _)
  refine measurable_of_tendsto_metrizable' (Filter.atTop : Filter (Finset (Fin n → ℤ)))
    (f := fun s z => ∑ m ∈ s, Φ (fr (z - x) + latV m))
    (fun s => Finset.measurable_sum s fun m _ => hterm m) ?_
  rw [tendsto_pi_nhds]
  intro z
  exact (hs z).hasSum

theorem latS_integrable (S : E ≃L[ℝ] E) {ξ a a₀ C : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (hC : 0 ≤ C) {Φ : E → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ y, 0 ≤ Φ y)
    (hΦ : ∀ y, Φ y ≤ C * gauss (‖S.symm y‖ / (2 * ξ / a))) (x : E) :
    Integrable (fun z => latS Φ x z) mT := by
  have hB : ∀ z, Summable (fun m : Fin n → ℤ => Φ (fr (z - x) + latV m)) ∧ 0 ≤ latS Φ x z
      ∧ latS Φ x z ≤ C * Gb n S a₀ := fun z => lat_bound S hξ hξ1 ha₀ ha hC hΦ0 hΦ x z
  have hLm : Measurable fun z : E => latS Φ x z :=
    latS_measurable_right hΦm x fun z => (hB z).1
  have hbd : ∀ z, ‖latS Φ x z‖ ≤ C * Gb n S a₀ := fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hB z).2.1]
    exact (hB z).2.2
  exact Integrable.of_bound (μ := mT) hLm.aestronglyMeasurable (C * Gb n S a₀) (ae_of_all _ hbd)

theorem latS_int_eq {Φ : E → ℝ} (hΦi : Integrable Φ) (x : E) :
    ∫ z, latS Φ x z ∂mT = ∫ y, Φ y :=
  lat_unfold hΦi x

theorem Ic_scale (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a) :
    (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * (2 * ξ / a) ^ n ≤ Ic n S a₀ * ξ ^ n := by
  have hd := dS_pos S
  have h := scale_pow_le (n := n) hξ ha₀ ha
  have hc : 0 ≤ (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S := by positivity
  calc (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * (2 * ξ / a) ^ n
      ≤ (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * (2 ^ n / a₀ ^ n * ξ ^ n) :=
        mul_le_mul_of_nonneg_left h hc
    _ = Ic n S a₀ * ξ ^ n := by unfold Ic; ring

/-- **`L¹` bound of a kernel dominated by a lattice sum.** -/
theorem lat_L1 (S : E ≃L[ℝ] E) {ξ a a₀ C : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (hC : 0 ≤ C) {Φ : E → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ y, 0 ≤ Φ y)
    (hΦ : ∀ y, Φ y ≤ C * gauss (‖S.symm y‖ / (2 * ξ / a))) {F : E → E → ℝ}
    (hF : ∀ x z, |F x z| ≤ latS Φ x z) (x : E) :
    ∫ z, |F x z| ∂mT ≤ C * (Ic n S a₀ * ξ ^ n) := by
  have hapos : 0 < a := lt_of_lt_of_le ha₀ ha
  have hξ2 : 0 < 2 * ξ / a := by positivity
  have hLi := latS_integrable S hξ hξ1 ha₀ ha hC hΦm hΦ0 hΦ x
  have hΦi : Integrable Φ := dom_integrable S hξ2 hΦm hΦ0 hΦ
  have h1 : ∫ z, |F x z| ∂mT ≤ ∫ z, latS Φ x z ∂mT :=
    integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) hLi (ae_of_all _ (hF x))
  have h2 := latS_int_eq hΦi x
  have h3 := dom_integral_le S hξ2 hΦm hΦ0 hΦ
  have h4 := mul_le_mul_of_nonneg_left (Ic_scale (n := n) S hξ ha₀ ha) hC
  linarith

/-- **`Good` from a sup bound and an `L¹` bound.** -/
theorem good_of (F : E → E → ℝ) (hFm : Measurable fun p : E × E => F p.1 p.2) {B M : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x z, |F x z| ≤ B) (hM0 : 0 ≤ M) (hM : ∀ x, ∫ z, |F x z| ∂mT ≤ M) :
    Good mT F B (B * M) := by
  refine ⟨hFm, hB0, mul_nonneg hB0 hM0, hB, fun x => ?_⟩
  have hm : Measurable fun z => F x z := hFm.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun z => B * |F x z|) mT :=
    (Integrable.of_bound hm.aestronglyMeasurable B (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]; exact hB x z)).abs.const_mul B
  calc ∫ z, F x z ^ 2 ∂mT ≤ ∫ z, B * |F x z| ∂mT :=
        integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) hi (ae_of_all _ fun z => by
          show F x z ^ 2 ≤ B * |F x z|
          rw [← sq_abs]; nlinarith [abs_nonneg (F x z), hB x z])
    _ = B * ∫ z, |F x z| ∂mT := integral_const_mul _ _
    _ ≤ B * M := mul_le_mul_of_nonneg_left (hM x) hB0

theorem good_mono {m : Measure E} {F : E → E → ℝ} {B v B' v' : ℝ} (G : Good m F B v) (hB : B ≤ B')
    (hv : v ≤ v') : Good m F B' v' :=
  ⟨G.meas, G.B_nonneg.trans hB, G.v_nonneg.trans hv, fun x z => (G.bd x z).trans hB,
    fun x => (G.var x).trans hv⟩


/-! ### Stage 2 (d): `RadK` for the full Gaussian profile -/

/-- Mass of the Gaussian profile. -/
def gaK₀ (n : ℕ) : ℝ := ∫ z : EuclideanSpace ℝ (Fin n), gauss ‖z‖

/-- Second moment per coordinate, normalised by the mass. -/
def gam₂ (n : ℕ) : ℝ := (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 * gauss ‖z‖) / (n * gaK₀ n)

def gaμ₃ (n : ℕ) : ℝ := ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 3 * gauss ‖z‖

def gaμ₄ (n : ℕ) : ℝ := ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 4 * gauss ‖z‖

theorem pow_le_one_add_four {r : ℝ} (hr : 0 ≤ r) (k : ℕ) (hk : k ≤ 4) : r ^ k ≤ 1 + r ^ 4 := by
  rcases le_total r 1 with h | h
  · have := pow_le_one₀ hr h (n := k)
    nlinarith [pow_nonneg hr 4]
  · have := pow_le_pow_right₀ h hk
    linarith

theorem gint {g : E → ℝ} (hg : Continuous g) (hb : ∀ z, |g z| ≤ 1 + ‖z‖ ^ 4) :
    Integrable (fun z : E => g z * gauss ‖z‖) := by
  refine ((even_moment_integrable (n := n) 0).add (even_moment_integrable (n := n) 2)).mono'
    ((hg.mul (gauss_continuous.comp continuous_norm)).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  have hgp := (gauss_pos ‖z‖).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgp]
  simp only [Pi.add_apply, mul_zero, pow_zero, one_mul, show 2 * 2 = 4 by rfl]
  nlinarith [hb z]

theorem gaK₀_eq : gaK₀ n = (2 * Real.pi) ^ ((n : ℝ) / 2) := gauss_integral

theorem gaK₀_pos : 0 < gaK₀ n := by rw [gaK₀_eq]; positivity

theorem gsecond_pos (hn : 1 ≤ n) : 0 < ∫ z : E, ‖z‖ ^ 2 * gauss ‖z‖ := by
  haveI : NeZero n := ⟨by omega⟩
  have hi : Integrable (fun z : E => ‖z‖ ^ 2 * gauss ‖z‖) := by
    simpa using even_moment_integrable (n := n) 1
  rw [integral_pos_iff_support_of_nonneg (fun z => mul_nonneg (sq_nonneg _) (gauss_pos _).le) hi]
  have hb : 0 < volume (Metric.ball (0 : E) 1 \ {0}) := by
    rw [measure_diff_null (measure_singleton 0)]
    exact Metric.measure_ball_pos volume (0 : E) one_pos
  refine lt_of_lt_of_le hb (measure_mono ?_)
  intro z ⟨_, hz0⟩
  have h1 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  exact (mul_pos (pow_pos h1 2) (gauss_pos _)).ne'

theorem gam₂_pos (hn : 1 ≤ n) : 0 < gam₂ n := by
  unfold gam₂
  have : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (gsecond_pos hn) (mul_pos this gaK₀_pos)

theorem gmom1 (i : Fin n) : ∫ z : E, z i * gauss ‖z‖ = 0 := by
  have h := integral_isom (flipL i) (fun z : E => z i * gauss ‖z‖)
  simp only [flipL_apply, LinearIsometryEquiv.norm_map, ↓reduceIte, neg_mul, integral_neg] at h
  linarith

theorem gmom2_off {i j : Fin n} (hij : i ≠ j) : ∫ z : E, z i * z j * gauss ‖z‖ = 0 := by
  have h := integral_isom (flipL i) (fun z : E => z i * z j * gauss ‖z‖)
  simp only [flipL_apply, if_neg (Ne.symm hij), LinearIsometryEquiv.norm_map, ↓reduceIte,
    neg_mul, integral_neg] at h
  linarith

theorem gmom2_swap (i j : Fin n) :
    ∫ z : E, z i * z i * gauss ‖z‖ = ∫ z : E, z j * z j * gauss ‖z‖ := by
  have h := integral_isom (swapL i j) (fun z : E => z i * z i * gauss ‖z‖)
  simp only [swapL_apply, Equiv.swap_apply_left, LinearIsometryEquiv.norm_map] at h
  exact h.symm

theorem coord_bd (i : Fin n) (z : E) : |z i| ≤ 1 + ‖z‖ ^ 4 :=
  (abs_coord_le z i).trans (by simpa using pow_le_one_add_four (norm_nonneg z) 1 (by norm_num))

theorem coord2_bd (i j : Fin n) (z : E) : |z i * z j| ≤ 1 + ‖z‖ ^ 4 := by
  rw [abs_mul]
  have := pow_le_one_add_four (norm_nonneg z) 2 (by norm_num)
  nlinarith [abs_coord_le z i, abs_coord_le z j, abs_nonneg (z i), abs_nonneg (z j)]

theorem gmom2_diag (i : Fin n) : ∫ z : E, z i * z i * gauss ‖z‖ = gam₂ n * gaK₀ n := by
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := Fin.pos i
    exact_mod_cast this.ne'
  have hK := (gaK₀_pos (n := n)).ne'
  have hsum : ∫ z : E, ‖z‖ ^ 2 * gauss ‖z‖ = n * ∫ z : E, z i * z i * gauss ‖z‖ := by
    have e1 : (fun z : E => ‖z‖ ^ 2 * gauss ‖z‖) = fun z => ∑ j, z j * z j * gauss ‖z‖ := by
      funext z
      rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, integral_finset_sum _ fun j _ =>
      gint (g := fun z : E => z j * z j) (by fun_prop) (coord2_bd j j)]
    rw [Finset.sum_congr rfl fun j _ => gmom2_swap (n := n) j i]
    simp
  unfold gam₂
  rw [hsum]; field_simp

/-- **`RadK` for the full Gaussian profile.** -/
theorem radK_gauss :
    RadK n gauss (gaK₀ n) (gam₂ n) (gaμ₃ n) (gaμ₄ n) where
  kern :=
    { nonneg := fun z => (gauss_pos ‖z‖).le
      int0 := by simpa using even_moment_integrable (n := n) 0
      int1 := fun i => gint (g := fun z : E => z i) (by fun_prop) (coord_bd i)
      int2 := fun i j => gint (g := fun z : E => z i * z j) (by fun_prop) (coord2_bd i j)
      int3 := gint (g := fun z : E => ‖z‖ ^ 3) (by fun_prop) (fun z => by
        rw [abs_of_nonneg (by positivity)]; exact pow_le_one_add_four (norm_nonneg z) 3 (by norm_num))
      mass := rfl
      mass_pos := gaK₀_pos
      mom1 := fun i => gmom1 i
      mom2 := fun i j => by
        split_ifs with h
        · subst h; exact gmom2_diag i
        · exact gmom2_off h
      mom3 := rfl }
  int1 := gint (g := fun z : E => ‖z‖) (by fun_prop) (fun z => by
    rw [abs_of_nonneg (norm_nonneg z)]; simpa using pow_le_one_add_four (norm_nonneg z) 1 (by norm_num))
  int4 := by simpa using even_moment_integrable (n := n) 2
  mom4 := rfl

/-! ### Stage 2 (e): the four kernels and their dominating lattice sums -/

theorem norm_le_S (S : E ≃L[ℝ] E) (y : E) : ‖y‖ ≤ ‖(S : E →L[ℝ] E)‖ * ‖S.symm y‖ := by
  have e : ‖y‖ = ‖(S : E →L[ℝ] E) (S.symm y)‖ := by
    rw [ContinuousLinearEquiv.coe_coe, S.apply_symm_apply]
  rw [e]; exact (S : E →L[ℝ] E).le_opNorm _

/-- The increment of a periodic Lipschitz function is bounded by EVERY lattice representative. -/
theorem f_inc {f : E → ℝ} (hper : Per f) {Lip : ℝ} (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (x z : E) (m : Fin n → ℤ) : |gd f x z| ≤ Lip * ‖fr (z - x) + latV m‖ := by
  have h1 := per_fr hper x z
  have h2 := hper (latV m) (latV_mem m) (x + fr (z - x))
  have e : f z = f (x + (fr (z - x) + latV m)) := by
    rw [show x + (fr (z - x) + latV m) = latV m + (x + fr (z - x)) by abel, h2, ← h1]
  unfold gd; rw [e]
  have := hLip x (x + (fr (z - x) + latV m))
  rwa [add_sub_cancel_left] at this

theorem arg_half (w ξ a : ℝ) (hξ : 0 < ξ) (ha : 0 < a) : w / (2 * ξ / a) = w / (ξ / a) / 2 := by
  field_simp

/-- Dominating function of the kernel itself. -/
def ΦK (S : E ≃L[ℝ] E) (ξ a : ℝ) (y : E) : ℝ := gauss (‖S.symm y‖ / (ξ / a))

/-- Dominating function of the kernel times the test increment. -/
def Φ1 (S : E ≃L[ℝ] E) (ξ a Lip : ℝ) (y : E) : ℝ := Lip * ‖y‖ * gauss (‖S.symm y‖ / (ξ / a))

/-- Dominating function of the time difference quotient of the kernel. -/
def ΦD (S : E ≃L[ℝ] E) (ξ a₀ a₁ La : ℝ) (y : E) : ℝ :=
  a₁ * La * (‖S.symm y‖ / ξ) ^ 2 * gauss (‖S.symm y‖ / ξ * a₀)

/-- Dominating function of the time difference quotient times the test increment. -/
def ΦDt (S : E ≃L[ℝ] E) (ξ a₀ a₁ La Lip : ℝ) (y : E) : ℝ := Lip * ‖y‖ * ΦD S ξ a₀ a₁ La y

theorem cont_arg (S : E ≃L[ℝ] E) (c : ℝ) : Continuous fun y : E => ‖S.symm y‖ / c :=
  (continuous_norm.comp S.symm.continuous).div_const c

theorem ΦK_meas (S : E ≃L[ℝ] E) (ξ a : ℝ) : Measurable (ΦK S ξ a) :=
  (gauss_continuous.comp (cont_arg S _)).measurable

theorem Φ1_meas (S : E ≃L[ℝ] E) (ξ a Lip : ℝ) : Measurable (Φ1 S ξ a Lip) :=
  ((continuous_const.mul continuous_norm).mul (gauss_continuous.comp (cont_arg S _))).measurable

theorem ΦD_meas (S : E ≃L[ℝ] E) (ξ a₀ a₁ La : ℝ) : Measurable (ΦD S ξ a₀ a₁ La) :=
  ((continuous_const.mul ((cont_arg S ξ).pow 2)).mul
    (gauss_continuous.comp ((cont_arg S ξ).mul continuous_const))).measurable

theorem ΦDt_meas (S : E ≃L[ℝ] E) (ξ a₀ a₁ La Lip : ℝ) : Measurable (ΦDt S ξ a₀ a₁ La Lip) :=
  ((continuous_const.mul continuous_norm).measurable).mul (ΦD_meas S ξ a₀ a₁ La)

theorem ΦK_nonneg (S : E ≃L[ℝ] E) (ξ a : ℝ) (y : E) : 0 ≤ ΦK S ξ a y := (gauss_pos _).le

theorem Φ1_nonneg (S : E ≃L[ℝ] E) (ξ a : ℝ) {Lip : ℝ} (hL : 0 ≤ Lip) (y : E) :
    0 ≤ Φ1 S ξ a Lip y := by
  unfold Φ1; have := gauss_pos (‖S.symm y‖ / (ξ / a)); positivity

theorem ΦD_nonneg (S : E ≃L[ℝ] E) (ξ a₀ : ℝ) {a₁ La : ℝ} (h1 : 0 ≤ a₁) (h2 : 0 ≤ La) (y : E) :
    0 ≤ ΦD S ξ a₀ a₁ La y := by
  unfold ΦD; have := gauss_pos (‖S.symm y‖ / ξ * a₀); positivity

theorem ΦDt_nonneg (S : E ≃L[ℝ] E) (ξ a₀ : ℝ) {a₁ La Lip : ℝ} (h1 : 0 ≤ a₁) (h2 : 0 ≤ La)
    (hL : 0 ≤ Lip) (y : E) : 0 ≤ ΦDt S ξ a₀ a₁ La Lip y := by
  unfold ΦDt; have := ΦD_nonneg S ξ a₀ h1 h2 y; positivity

theorem ΦK_dom (S : E ≃L[ℝ] E) {ξ a : ℝ} (hξ : 0 < ξ) (ha : 0 < a) (y : E) :
    ΦK S ξ a y ≤ 1 * gauss (‖S.symm y‖ / (2 * ξ / a)) := by
  rw [arg_half _ _ _ hξ ha, one_mul]; exact dom0 _

theorem Φ1_dom (S : E ≃L[ℝ] E) {ξ a a₀ Lip : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (hL : 0 ≤ Lip) (y : E) :
    Φ1 S ξ a Lip y ≤ ξ * (4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀) * gauss (‖S.symm y‖ / (2 * ξ / a)) := by
  have hapos : 0 < a := lt_of_lt_of_le ha₀ ha
  rw [arg_half _ _ _ hξ hapos]
  unfold Φ1
  set u := ‖S.symm y‖ / (ξ / a) with hu
  have hu0 : 0 ≤ u := by positivity
  have hnorm : ‖S.symm y‖ = u * (ξ / a) := by rw [hu]; field_simp
  have hS := norm_nonneg (S : E →L[ℝ] E)
  have hy : ‖y‖ ≤ ‖(S : E →L[ℝ] E)‖ * (ξ / a₀) * u := by
    calc ‖y‖ ≤ ‖(S : E →L[ℝ] E)‖ * ‖S.symm y‖ := norm_le_S S y
      _ = ‖(S : E →L[ℝ] E)‖ * (ξ / a) * u := by rw [hnorm]; ring
      _ ≤ ‖(S : E →L[ℝ] E)‖ * (ξ / a₀) * u :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left hξ.le ha₀ ha) hS) hu0
  have hg := gauss_pos u
  have hd := dom1 hu0
  calc Lip * ‖y‖ * gauss u ≤ Lip * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀) * u) * gauss u :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy hL) hg.le
    _ = Lip * ‖(S : E →L[ℝ] E)‖ * (ξ / a₀) * (u * gauss u) := by ring
    _ ≤ Lip * ‖(S : E →L[ℝ] E)‖ * (ξ / a₀) * (4 * gauss (u / 2)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = ξ * (4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀) * gauss (u / 2) := by ring

theorem ΦD_dom (S : E ≃L[ℝ] E) {ξ a₀ a₁ La : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (h1 : 0 ≤ a₁)
    (h2 : 0 ≤ La) (y : E) :
    ΦD S ξ a₀ a₁ La y ≤ (3 * a₁ * La / a₀ ^ 2) * gauss (‖S.symm y‖ / (2 * ξ / a₀)) := by
  rw [arg_half _ _ _ hξ ha₀]
  unfold ΦD
  set u := ‖S.symm y‖ / (ξ / a₀) with hu
  have e1 : ‖S.symm y‖ / ξ * a₀ = u := by rw [hu]; field_simp
  have e2 : ‖S.symm y‖ / ξ = u / a₀ := by rw [← e1]; field_simp
  rw [e1, e2]
  have hd := dom2 u
  calc a₁ * La * (u / a₀) ^ 2 * gauss u = a₁ * La / a₀ ^ 2 * (u ^ 2 * gauss u) := by
        ring
    _ ≤ a₁ * La / a₀ ^ 2 * (3 * gauss (u / 2)) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ = 3 * a₁ * La / a₀ ^ 2 * gauss (u / 2) := by ring

theorem ΦDt_dom (S : E ≃L[ℝ] E) {ξ a₀ a₁ La Lip : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (h1 : 0 ≤ a₁)
    (h2 : 0 ≤ La) (hL : 0 ≤ Lip) (y : E) :
    ΦDt S ξ a₀ a₁ La Lip y
      ≤ ξ * (18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3) * gauss (‖S.symm y‖ / (2 * ξ / a₀)) := by
  rw [arg_half _ _ _ hξ ha₀]
  unfold ΦDt ΦD
  set u := ‖S.symm y‖ / (ξ / a₀) with hu
  have hu0 : 0 ≤ u := by positivity
  have e1 : ‖S.symm y‖ / ξ * a₀ = u := by rw [hu]; field_simp
  have e2 : ‖S.symm y‖ / ξ = u / a₀ := by rw [← e1]; field_simp
  have hnorm : ‖S.symm y‖ = ξ * (u / a₀) := by rw [← e2]; field_simp
  rw [e1, e2]
  have hS := norm_nonneg (S : E →L[ℝ] E)
  have hy : ‖y‖ ≤ ‖(S : E →L[ℝ] E)‖ * (ξ * (u / a₀)) := by
    rw [← hnorm]; exact norm_le_S S y
  have hg := gauss_pos u
  have hd := dom3 hu0
  have hA : 0 ≤ a₁ * La * (u / a₀) ^ 2 * gauss u := by positivity
  calc Lip * ‖y‖ * (a₁ * La * (u / a₀) ^ 2 * gauss u)
      ≤ Lip * (‖(S : E →L[ℝ] E)‖ * (ξ * (u / a₀))) * (a₁ * La * (u / a₀) ^ 2 * gauss u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy hL) hA
    _ = ξ * (Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3) * (u ^ 3 * gauss u) := by
        ring
    _ ≤ ξ * (Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3) * (18 * gauss (u / 2)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
    _ = ξ * (18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3) * gauss (u / 2) := by ring

/-- One term of the time difference quotient. -/
theorem D_term (S : E ≃L[ℝ] E) {ξ a₀ a₁ La aa ab η : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀)
    (haa : a₀ ≤ aa) (haa1 : aa ≤ a₁) (hab : a₀ ≤ ab) (hab1 : ab ≤ a₁) (hη : η ≠ 0)
    (hd : |ab - aa| ≤ La * |η|) (y : E) :
    |(gauss (‖S.symm y‖ / (ξ / ab)) - gauss (‖S.symm y‖ / (ξ / aa))) / η| ≤ ΦD S ξ a₀ a₁ La y := by
  have hpa : 0 < aa := lt_of_lt_of_le ha₀ haa
  have hpb : 0 < ab := lt_of_lt_of_le ha₀ hab
  set t := ‖S.symm y‖ / ξ with ht
  have ht0 : 0 ≤ t := by positivity
  have eb : ‖S.symm y‖ / (ξ / ab) = t * ab := by rw [ht]; field_simp
  have ea : ‖S.symm y‖ / (ξ / aa) = t * aa := by rw [ht]; field_simp
  rw [eb, ea, abs_div, div_le_iff₀ (abs_pos.2 hη)]
  have h := gauss_scale_diff ht0 ha₀.le haa haa1 hab hab1
  have hg := gauss_pos (t * a₀)
  have ha1 : 0 ≤ a₁ := ha₀.le.trans (haa.trans haa1)
  have hc : 0 ≤ t ^ 2 * a₁ * gauss (t * a₀) := by positivity
  calc |gauss (t * ab) - gauss (t * aa)| ≤ t ^ 2 * a₁ * gauss (t * a₀) * |ab - aa| := h
    _ ≤ t ^ 2 * a₁ * gauss (t * a₀) * (La * |η|) := mul_le_mul_of_nonneg_left hd hc
    _ = ΦD S ξ a₀ a₁ La y * |η| := by unfold ΦD; rw [← ht]; ring

/-- `|(Σ T)·c| ≤ Σ Φ` from termwise bounds. -/
theorem tsum_mul_le {T Φ : (Fin n → ℤ) → ℝ} (c : ℝ) (hΦ : Summable Φ)
    (h : ∀ m, |T m * c| ≤ Φ m) : |(∑' m, T m) * c| ≤ ∑' m, Φ m := by
  rw [← tsum_mul_right]
  exact tsum_of_norm_bounded hΦ.hasSum fun m => by rw [Real.norm_eq_abs]; exact h m

theorem latK_nonneg (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (x z : E) :
    Summable (fun m : Fin n → ℤ => ΦK S ξ a (fr (z - x) + latV m))
      ∧ 0 ≤ latK S (ξ / a) x z ∧ latK S (ξ / a) x z ≤ 1 * Gb n S a₀ :=
  lat_bound S hξ hξ1 ha₀ ha zero_le_one (ΦK_nonneg S ξ a)
    (ΦK_dom S hξ (lt_of_lt_of_le ha₀ ha)) x z

theorem latK_test (S : E ≃L[ℝ] E) {ξ a a₀ Lip : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (hL : 0 ≤ Lip) {f : E → ℝ} (hper : Per f)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖) (x z : E) :
    |latK S (ξ / a) x z * gd f x z| ≤ latS (Φ1 S ξ a Lip) x z := by
  have hC : 0 ≤ ξ * (4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀) := by positivity
  have hs1 := (lat_bound S hξ hξ1 ha₀ ha hC (Φ1_nonneg S ξ a hL) (Φ1_dom S hξ ha₀ ha hL) x z).1
  refine tsum_mul_le _ hs1 fun m => ?_
  rw [abs_mul, abs_of_nonneg (gauss_pos _).le]
  calc gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / a)) * |gd f x z|
      ≤ gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / a)) * (Lip * ‖fr (z - x) + latV m‖) :=
        mul_le_mul_of_nonneg_left (f_inc hper hLip x z m) (gauss_pos _).le
    _ = Φ1 S ξ a Lip (fr (z - x) + latV m) := by unfold Φ1; ring

/-- The time difference quotient of the lattice kernel, as a lattice sum. -/
theorem latK_dq_eq (S : E ≃L[ℝ] E) {ξ a₀ aa ab : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (haa : a₀ ≤ aa) (hab : a₀ ≤ ab) (η : ℝ) (x z : E) :
    (latK S (ξ / ab) x z - latK S (ξ / aa) x z) / η
      = ∑' m : Fin n → ℤ, (gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / ab))
          - gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / aa))) / η := by
  have hsb : Summable fun m : Fin n → ℤ => gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / ab)) :=
    (latK_nonneg S hξ hξ1 ha₀ hab x z).1
  have hsa : Summable fun m : Fin n → ℤ => gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / aa)) :=
    (latK_nonneg S hξ hξ1 ha₀ haa x z).1
  rw [tsum_div_const, hsb.tsum_sub hsa]
  rfl

theorem latK_dq (S : E ≃L[ℝ] E) {ξ a₀ a₁ La aa ab η : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (haa : a₀ ≤ aa) (haa1 : aa ≤ a₁) (hab : a₀ ≤ ab) (hab1 : ab ≤ a₁) (hLa : 0 ≤ La) (hη : η ≠ 0)
    (hd : |ab - aa| ≤ La * |η|) (x z : E) :
    |(latK S (ξ / ab) x z - latK S (ξ / aa) x z) / η| ≤ latS (ΦD S ξ a₀ a₁ La) x z := by
  have ha1 : 0 ≤ a₁ := ha₀.le.trans (haa.trans haa1)
  have hC : 0 ≤ 3 * a₁ * La / a₀ ^ 2 := by positivity
  have hsD := (lat_bound S hξ hξ1 ha₀ le_rfl hC (ΦD_nonneg S ξ a₀ ha1 hLa)
    (ΦD_dom S hξ ha₀ ha1 hLa) x z).1
  rw [latK_dq_eq S hξ hξ1 ha₀ haa hab η x z]
  exact tsum_of_norm_bounded hsD.hasSum fun m => by
    rw [Real.norm_eq_abs]; exact D_term S hξ ha₀ haa haa1 hab hab1 hη hd _

theorem latK_dq_test (S : E ≃L[ℝ] E) {ξ a₀ a₁ La aa ab η Lip : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (ha₀ : 0 < a₀) (haa : a₀ ≤ aa) (haa1 : aa ≤ a₁) (hab : a₀ ≤ ab) (hab1 : ab ≤ a₁)
    (hLa : 0 ≤ La) (hη : η ≠ 0) (hd : |ab - aa| ≤ La * |η|) (hL : 0 ≤ Lip) {f : E → ℝ}
    (hper : Per f) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖) (x z : E) :
    |(latK S (ξ / ab) x z - latK S (ξ / aa) x z) / η * gd f x z|
      ≤ latS (ΦDt S ξ a₀ a₁ La Lip) x z := by
  have ha1 : 0 ≤ a₁ := ha₀.le.trans (haa.trans haa1)
  have hC : 0 ≤ ξ * (18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3) := by positivity
  have hsD := (lat_bound S hξ hξ1 ha₀ le_rfl hC (ΦDt_nonneg S ξ a₀ ha1 hLa hL)
    (ΦDt_dom S hξ ha₀ ha1 hLa hL) x z).1
  rw [latK_dq_eq S hξ hξ1 ha₀ haa hab η x z]
  refine tsum_mul_le _ hsD fun m => ?_
  rw [abs_mul]
  have h1 := D_term S hξ ha₀ haa haa1 hab hab1 hη hd (fr (z - x) + latV m)
  have h2 := f_inc hper hLip x z m
  have h0 := ΦD_nonneg S ξ a₀ ha1 hLa (fr (z - x) + latV m)
  calc _ ≤ ΦD S ξ a₀ a₁ La (fr (z - x) + latV m) * (Lip * ‖fr (z - x) + latV m‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) h0
    _ = ΦDt S ξ a₀ a₁ La Lip (fr (z - x) + latV m) := by unfold ΦDt; ring

/-! ### Stage 3: the N-point statement directly for the lattice-sum kernel -/

/-- Lower mass constant `P₀ = (2π)^{n/2} |det S| / a₁ⁿ`. -/
def P0c (S : E ≃L[ℝ] E) (a₁ : ℝ) : ℝ := (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S / a₁ ^ n

/-- The constant `Λ` of the direct lattice statement. -/
def dLam (S : E ≃L[ℝ] E) (a₀ a₁ La Lip : ℝ) : ℝ :=
  max 1 (max (Gb n S a₀) (max (3 * a₁ * La / a₀ ^ 2 * Gb n S a₀) (max (Ic n S a₀)
    (max (3 * a₁ * La / a₀ ^ 2 * Ic n S a₀) (max (P0c S a₁)⁻¹
    (max (4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀ * Gb n S a₀)
    (max (4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀ * Ic n S a₀)
    (max (18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3 * Gb n S a₀)
      (18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3 * Ic n S a₀)))))))))

theorem dLam_bounds (S : E ≃L[ℝ] E) (a₀ a₁ La Lip : ℝ) :
    let Λ := dLam S a₀ a₁ La Lip
    1 ≤ Λ ∧ Gb n S a₀ ≤ Λ ∧ 3 * a₁ * La / a₀ ^ 2 * Gb n S a₀ ≤ Λ ∧ Ic n S a₀ ≤ Λ
      ∧ 3 * a₁ * La / a₀ ^ 2 * Ic n S a₀ ≤ Λ ∧ (P0c S a₁)⁻¹ ≤ Λ
      ∧ 4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀ * Gb n S a₀ ≤ Λ
      ∧ 4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀ * Ic n S a₀ ≤ Λ
      ∧ 18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3 * Gb n S a₀ ≤ Λ
      ∧ 18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3 * Ic n S a₀ ≤ Λ := by
  intro Λ
  refine ⟨le_max_left _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_max_of_le_right (le_max_left _ _)
  · exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_left _ _))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_left _ _)))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_left _ _))))))))
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
      (le_max_right _ _))))))))

/-- The exact normalisation of the lattice kernel is at least `P₀ ξⁿ`. -/
theorem popAvg_latK_ge (S : E ≃L[ℝ] E) {ξ a a₁ : ℝ} (hξ : 0 < ξ) (ha : 0 < a) (ha₁ : a ≤ a₁)
    (y : E) : P0c S a₁ * ξ ^ n ≤ popAvg mT (latK S (ξ / a)) y := by
  rw [popAvg_latK S (div_pos hξ ha), kap_int gauss S (div_pos hξ ha), gauss_integral]
  have hd := dS_pos S
  unfold P0c
  rw [div_pow]
  have h1 : (0:ℝ) < a ^ n := pow_pos ha n
  have h2 : a ^ n ≤ a₁ ^ n := pow_le_pow_left₀ ha.le ha₁ n
  have hK : (0:ℝ) < (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * ξ ^ n := by positivity
  calc (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S / a₁ ^ n * ξ ^ n
      = (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * ξ ^ n * (1 / a₁ ^ n) := by ring
    _ ≤ (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * ξ ^ n * (1 / a ^ n) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h1 h2) hK.le
    _ = (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * (ξ ^ n / a ^ n) := by ring

set_option maxHeartbeats 3200000 in
/-- **`prop:dotLN-diff` for the LATTICE-SUM Gaussian kernel, directly (no cut-off).**
Uniform sample of the flat torus `ℝⁿ/ℤⁿ` (law `mT`), kernel
`latK S (ξ/a(τ)) = Σ_{m ∈ ℤⁿ} exp(−‖S⁻¹(fr(z−x)+m)‖² a(τ)²/(2ξ²))` on the sample side, population operator
`Lmet gauss` (= the normalised population operator of the same kernel, `Lmet_pop_lat`), metrics
`g_τ = a(τ)² g₀`, periodic `C⁴` test function `f`, Lipschitz with constant `Lip` and bounded by `B`
(HYPOTHESES), `0 < ξ ≤ 1`, `a₀ ≤ a ≤ a₁`, `|a'| ≤ L_a`, `N ≥ 2`, `92416 Λ¹⁴·3 log N ≤ N ξⁿ`.
With probability at least `1 − 30/N²`, for every `i < N`, with `δ' = √(3 log N/(N ξⁿ))`:
(i)  `|Δ_η L_N f(i) − Δ_η L_ξ f(X_i)| ≤ (7320000 Λ²⁰/m₂) δ'/ξ`;
(ii) `|Δ_η L_N f(i) + Δ_η(Δ_{g_τ} f)(X_i)| ≤ (7320000 Λ²⁰/m₂) δ'/ξ + ξ² min{C₁/|η|, C₂}`,
with `m₂ = gam₂ n`, `K₀ = gaK₀ n`, `μ₄ = gaμ₄ n` the moments of the FULL Gaussian profile.
No cut-off radius, no additional terms. -/
theorem flat_npoint_lattice_direct (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω) / (τb - τa)
          - (Lmet gauss (gam₂ n) S (a τb) ξ f (X i ω)
              - Lmet gauss (gam₂ n) S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * dLam S a₀ a₁ La Lip ^ 20 / gam₂ n
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * dLam S a₀ a₁ La Lip ^ 20 / gam₂ n
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gaμ₄ n
                / (6 * gam₂ n * gaK₀ n * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gaμ₄ n * La / (3 * gam₂ n * gaK₀ n * a₀ ^ 5)))}
      ≤ 30 / (N : ℝ) ^ 2 := by
  obtain ⟨l1, lG, lIG, lI, lII, lP0, lFG, lFI, lFiG, lFiI⟩ := dLam_bounds S a₀ a₁ La Lip
  set Λ := dLam S a₀ a₁ La Lip with hΛ
  set L := 3 * Real.log N with hLdef
  set xn := ξ ^ n with hx
  set δ := Real.sqrt (L / (N * xn)) with hδdef
  set G := Gb n S a₀ with hG
  set I := Ic n S a₀ with hI
  set P0 := P0c S a₁ with hP0
  set cI := 3 * a₁ * La / a₀ ^ 2 with hcI
  set cF := 4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀ with hcF
  set cFi := 18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3 with hcFi
  set m₂ := gam₂ n with hm₂def
  set η := τb - τa with hη
  have hm₂ : 0 < m₂ := gam₂_pos hn
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hL1 : 1 ≤ L := FlatNPointRate.three_log_ge_one N hN
  have hx0 : 0 < xn := pow_pos hξ n
  have hx1 : xn ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hd := dS_pos S
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hfc : Continuous f := hf.continuous
  have hη0 : η ≠ 0 := sub_ne_zero.2 hne
  have hdiff : |a τb - a τa| ≤ La * |η| := a_lip a a' hda hLa τa τb
  have hG0 : 0 < G := Gb_pos S a₀
  have hI0 : 0 < I := Ic_pos S ha₀
  have hP00 : 0 < P0 := by simp only [hP0, P0c]; positivity
  have hcI0 : 0 ≤ cI := by rw [hcI]; positivity
  have hcF0 : 0 ≤ cF := by rw [hcF]; positivity
  have hcFi0 : 0 ≤ cFi := by rw [hcFi]; positivity
  have hΛ0 : 0 < Λ := by linarith
  have hIx0 : 0 ≤ I * xn := by positivity
  -- measurability
  have hKm : ∀ τ, Measurable fun p : E × E => latK S (ξ / a τ) p.1 p.2 := fun τ =>
    latS_measurable (ΦK_meas S ξ (a τ)) fun x z => (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).1
  have hgm : Measurable fun p : E × E => gd f p.1 p.2 :=
    (hfc.measurable.comp measurable_snd).sub (hfc.measurable.comp measurable_fst)
  -- the kernels
  have bK : ∀ τ x z, |latK S (ξ / a τ) x z| ≤ G := fun τ x z => by
    obtain ⟨-, h0, h1⟩ := latK_nonneg S hξ hξ1 ha₀ (ha τ) x z
    rw [abs_of_nonneg h0, hG]; linarith
  have LK : ∀ τ x, ∫ z, |latK S (ξ / a τ) x z| ∂mT ≤ I * xn := fun τ x' => by
    have := lat_L1 S hξ hξ1 ha₀ (ha τ) zero_le_one (ΦK_meas S ξ (a τ)) (ΦK_nonneg S ξ (a τ))
      (ΦK_dom S hξ (hpos τ)) (fun x z => le_of_eq (abs_of_nonneg
        (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).2.1)) x'
    rw [hI, hx]; exact this.trans (le_of_eq (one_mul _))
  have GK : ∀ τ, Good mT (latK S (ξ / a τ)) G (G * (I * xn)) := fun τ =>
    good_of _ (hKm τ) hG0.le (bK τ) hIx0 (LK τ)
  -- the kernels times the test increment
  have bF : ∀ τ x z, |latK S (ξ / a τ) x z * gd f x z| ≤ ξ * (cF * G) := fun τ x z => by
    have h1 := latK_test S hξ hξ1 ha₀ (ha τ) hLip0 hper hLip x z
    have h2 := (lat_bound S hξ hξ1 ha₀ (ha τ) (by positivity) (Φ1_nonneg S ξ (a τ) hLip0)
      (Φ1_dom S hξ ha₀ (ha τ) hLip0) x z).2.2
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = ξ * (cF * G) := by rw [hcF, hG]; ring
  have hFm : ∀ τ, Measurable fun p : E × E => latK S (ξ / a τ) p.1 p.2 * gd f p.1 p.2 :=
    fun τ => (hKm τ).mul hgm
  have LF : ∀ τ x, ∫ z, |latK S (ξ / a τ) x z * gd f x z| ∂mT ≤ ξ * (cF * (I * xn)) :=
    fun τ x' => by
      have := lat_L1 S hξ hξ1 ha₀ (ha τ) (by positivity) (Φ1_meas S ξ (a τ) Lip)
        (Φ1_nonneg S ξ (a τ) hLip0) (Φ1_dom S hξ ha₀ (ha τ) hLip0)
        (fun x z => latK_test S hξ hξ1 ha₀ (ha τ) hLip0 hper hLip x z) x'
      calc _ ≤ _ := this
        _ = ξ * (cF * (I * xn)) := by rw [hcF, hI, hx]; ring
  have GF : ∀ τ, Good mT (fun x z => latK S (ξ / a τ) x z * gd f x z) (ξ * (cF * G))
      (ξ ^ 2 * (cF * G * (cF * (I * xn)))) := fun τ =>
    good_mono (good_of _ (hFm τ) (by positivity) (bF τ) (by positivity) (LF τ)) le_rfl
      (le_of_eq (by ring))
  -- the time difference quotient
  have bD : ∀ x z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η| ≤ cI * G := fun x z => by
    have h1 := latK_dq S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff x z
    have h2 := (lat_bound S hξ hξ1 ha₀ le_rfl hcI0 (ΦD_nonneg S ξ a₀ ha₁0.le hLa0)
      (ΦD_dom S hξ ha₀ ha₁0.le hLa0) x z).2.2
    rw [hcI, hG]; exact h1.trans h2
  have hDm : Measurable fun p : E × E => (latK S (ξ / a τb) p.1 p.2 - latK S (ξ / a τa) p.1 p.2) / η :=
    ((hKm τb).sub (hKm τa)).div_const _
  have LD : ∀ x, ∫ z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η| ∂mT ≤ cI * (I * xn) :=
    fun x' => by
      have := lat_L1 S hξ hξ1 ha₀ le_rfl (by positivity) (ΦD_meas S ξ a₀ a₁ La)
        (ΦD_nonneg S ξ a₀ ha₁0.le hLa0) (ΦD_dom S hξ ha₀ ha₁0.le hLa0)
        (fun x z => latK_dq S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff x z) x'
      rw [hcI, hI, hx]; exact this
  have GD : Good mT (fun x z => (latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η) (cI * G)
      (cI * G * (cI * (I * xn))) :=
    good_of _ hDm (by positivity) bD (by positivity) LD
  have bDt : ∀ x z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η * gd f x z|
      ≤ ξ * (cFi * G) := fun x z => by
    have h1 := latK_dq_test S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff hLip0
      hper hLip x z
    have h2 := (lat_bound S hξ hξ1 ha₀ le_rfl (by positivity) (ΦDt_nonneg S ξ a₀ ha₁0.le hLa0 hLip0)
      (ΦDt_dom S hξ ha₀ ha₁0.le hLa0 hLip0) x z).2.2
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = ξ * (cFi * G) := by rw [hcFi, hG]; ring
  have hDtm : Measurable fun p : E × E =>
      (latK S (ξ / a τb) p.1 p.2 - latK S (ξ / a τa) p.1 p.2) / η * gd f p.1 p.2 := hDm.mul hgm
  have LDt : ∀ x, ∫ z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η * gd f x z| ∂mT
      ≤ ξ * (cFi * (I * xn)) := fun x' => by
    have := lat_L1 S hξ hξ1 ha₀ le_rfl (by positivity) (ΦDt_meas S ξ a₀ a₁ La Lip)
      (ΦDt_nonneg S ξ a₀ ha₁0.le hLa0 hLip0) (ΦDt_dom S hξ ha₀ ha₁0.le hLa0 hLip0)
      (fun x z => latK_dq_test S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff
        hLip0 hper hLip x z) x'
    calc _ ≤ _ := this
      _ = ξ * (cFi * (I * xn)) := by rw [hcFi, hI, hx]; ring
  have GDt : Good mT (fun x z => (latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η * gd f x z)
      (ξ * (cFi * G)) (ξ ^ 2 * (cFi * G * (cFi * (I * xn)))) :=
    good_mono (good_of _ hDtm (by positivity) bDt (by positivity) LDt) le_rfl (le_of_eq (by ring))
  -- normalisations
  have hc : 0 < P0 * xn := mul_pos hP00 hx0
  have hpa : ∀ y, P0 * xn ≤ popAvg mT (latK S (ξ / a τa)) y := fun y =>
    popAvg_latK_ge S hξ (hpos τa) (ha₁ τa) y
  have hpb : ∀ y, P0 * xn ≤ popAvg mT (latK S (ξ / a τb)) y := fun y =>
    popAvg_latK_ge S hξ (hpos τb) (ha₁ τb) y
  have hDa : ∀ y, (1:ℝ) ≤ popW mT (latK S (ξ / a τa)) (fun _ _ => 1) y := fun y => by
    rw [popW_latK_one S (div_pos hξ (hpos τa))]
  have hDb : ∀ y, (1:ℝ) ≤ popW mT (latK S (ξ / a τb)) (fun _ _ => 1) y := fun y => by
    rw [popW_latK_one S (div_pos hξ (hpos τb))]
  -- smallness and Ctx
  have hNx : (N : ℝ) * xn ≠ 0 := (mul_pos hN' hx0).ne'
  have hδ : δ ^ 2 * (N * xn) = L := by
    rw [hδdef, Real.sq_sqrt (div_nonneg (by linarith) (mul_pos hN' hx0).le)]; field_simp
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hPp : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * xn) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ 1 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((1 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hPp] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ l1
    nlinarith
  have C : Ctx N Λ xn xn⁻¹ δ L :=
    { hN := hN0, hΛ := l1, hx := hx0, hx1 := hx1, hxy := mul_inv_cancel₀ hx0.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL1 }
  have hvK : G * (I * xn) ≤ Λ ^ 2 * xn := by
    calc G * (I * xn) ≤ Λ * (Λ * xn) := mul_le_mul lG (mul_le_mul_of_nonneg_right lI hx0.le)
          hIx0 hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have hM' : I * xn ≤ Λ * xn := mul_le_mul_of_nonneg_right lI hx0.le
  have hci : (P0 * xn)⁻¹ ≤ Λ * xn⁻¹ := by
    rw [mul_inv]; exact mul_le_mul_of_nonneg_right lP0 (by positivity)
  have hcD1 : (1:ℝ)⁻¹ ≤ Λ ^ 2 := by rw [inv_one]; nlinarith
  have hsmall := C.small'_le hG0.le lG (by positivity) hvK hIx0 hM' hc hci one_pos hcD1 hsm
  have hMI : cI * (I * xn) ≤ Λ * xn := by
    calc cI * (I * xn) = cI * I * xn := by ring
      _ ≤ Λ * xn := mul_le_mul_of_nonneg_right lII hx0.le
  have hvI : cI * G * (cI * (I * xn)) ≤ Λ ^ 2 * xn := by
    calc cI * G * (cI * (I * xn)) ≤ Λ * (Λ * xn) := mul_le_mul lIG hMI (by positivity) hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have hMF : cF * (I * xn) ≤ Λ * xn := by
    calc cF * (I * xn) = cF * I * xn := by ring
      _ ≤ Λ * xn := mul_le_mul_of_nonneg_right lFI hx0.le
  have hvF : cF * G * (cF * (I * xn)) ≤ Λ ^ 2 * xn := by
    calc cF * G * (cF * (I * xn)) ≤ Λ * (Λ * xn) := mul_le_mul lFG hMF (by positivity) hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have hMFi : cFi * (I * xn) ≤ Λ * xn := by
    calc cFi * (I * xn) = cFi * I * xn := by ring
      _ ≤ Λ * xn := mul_le_mul_of_nonneg_right lFiI hx0.le
  have hvFi : cFi * G * (cFi * (I * xn)) ≤ Λ ^ 2 * xn := by
    calc cFi * G * (cFi * (I * xn)) ≤ Λ * (Λ * xn) := mul_le_mul lFiG hMFi (by positivity) hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have he := err5g_le C hG0.le lG (by positivity) hvK (by positivity) lIG (by positivity) hvI
    hIx0 hM' (by positivity) hMI hc hci one_pos hcD1
    (by positivity) lFG (by positivity) hvF (by positivity) hMF
    (by positivity) lFiG (by positivity) hvFi (by positivity) hMFi
  -- the template
  have H := step5g X h_indep hX hlaw N hN0 (latK S (ξ / a τa)) (latK S (ξ / a τb)) (gd f) η
    (GK τa) (GK τb) GD hc (by linarith) hpa hpb hIx0 (LK τa) (LK τb) (by positivity) LD
    (GF τa) (GF τb) GDt (by positivity) (LF τa) (LF τb) (by positivity) LDt one_pos hDa hDb
    hsmall.1 hsmall.2
  rw [err5g_scale N hξ.le] at H
  rw [← prob_30 N hN]
  refine le_trans (measureReal_mono ?_) H
  intro ω hω
  obtain ⟨i, hi, hfail⟩ := hω
  refine ⟨i, hi, ?_⟩
  by_contra hle
  push_neg at hle
  apply hfail
  set e := err5g N G (G * (I * xn)) (cI * G) (cI * G * (cI * (I * xn))) (I * xn) (cI * (I * xn))
    (P0 * xn) L (cF * (I * xn)) (cF * G) (cF * G * (cF * (I * xn))) (cFi * (I * xn)) (cFi * G)
    (cFi * G * (cFi * (I * xn))) 1 with he_def
  set k := 2 / (m₂ * ξ ^ 2) with hk'
  have hk0 : 0 < k := by positivity
  set y := X i ω
  set rb := sampW X N (latK S (ξ / a τb)) (gd f) i ω / sampW X N (latK S (ξ / a τb)) (fun _ _ => 1) i ω
  set ra := sampW X N (latK S (ξ / a τa)) (gd f) i ω / sampW X N (latK S (ξ / a τa)) (fun _ _ => 1) i ω
  set Pb := popW mT (latK S (ξ / a τb)) (gd f) y / popW mT (latK S (ξ / a τb)) (fun _ _ => 1) y
  set Pa := popW mT (latK S (ξ / a τa)) (gd f) y / popW mT (latK S (ξ / a τa)) (fun _ _ => 1) y
  have eLb : LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω = -k * rb := rfl
  have eLa : LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω = -k * ra := rfl
  have eMb : Lmet gauss m₂ S (a τb) ξ f y = -k * Pb :=
    Lmet_pop_lat m₂ S (hpos τb) hξ hfc hB hper y
  have eMa : Lmet gauss m₂ S (a τa) ξ f y = -k * Pa :=
    Lmet_pop_lat m₂ S (hpos τa) hξ hfc hB hper y
  have key : (LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η
      = -k * ((rb - ra) / η - (Pb - Pa) / η) := by
    rw [eLb, eLa, eMb, eMa]; field_simp; ring
  have hbound : k * (ξ * e) ≤ 7320000 * Λ ^ 20 / m₂ * δ / ξ := by
    have h1 : k * (ξ * e) = 2 / m₂ * e / ξ := by rw [hk']; field_simp
    rw [h1]
    have h2 : 2 / m₂ * e ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    calc 2 / m₂ * e / ξ ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) / ξ :=
          div_le_div_of_nonneg_right h2 hξ.le
      _ = 7320000 * Λ ^ 20 / m₂ * δ / ξ := by ring
  have hI' : |(LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η|
      ≤ 7320000 * Λ ^ 20 / m₂ * δ / ξ := by
    rw [key, abs_mul, abs_neg, abs_of_pos hk0]
    exact (mul_le_mul_of_nonneg_left hle hk0.le).trans hbound
  refine ⟨hI', ?_⟩
  have hpop := metric_dq_min (radK_gauss (n := n)) hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ y τa τb hne
  have tri := abs_add_le
    ((LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η)
    ((Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η
      + (lapG S f y / a τb ^ 2 - lapG S f y / a τa ^ 2) / η)
  have e2 : (LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      + (lapG S f y / a τb ^ 2 - lapG S f y / a τa ^ 2) / η
      = ((LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η)
      + ((Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η
      + (lapG S f y / a τb ^ 2 - lapG S f y / a τa ^ 2) / η) := by ring
  rw [e2]
  exact le_trans tri (add_le_add hI' hpop)

end CTG.FlatNPointLatticeDirect
