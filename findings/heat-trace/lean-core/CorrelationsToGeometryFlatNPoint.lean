/-
Twenty-eighth file: both inequalities of `prop:dotLN-diff` as ONE statement on the flat torus.  Imports
`CorrelationsToGeometryNPointLip` and `CorrelationsToGeometryFlatLB4` (compiled modules under
`.tools/leanbuild`); namespace `CTG.FlatNPoint`; check with `./check_flat_npoint.sh`.
Setting: sample law = Lebesgue measure on the unit cube (fundamental domain of `ℤⁿ`), periodised kernel
`h(‖S⁻¹ fr(z − x)‖ a(τ)/ξ)` of a profile with COMPACT support (radius of the scaled kernel `< 1/2`), metrics
`g_τ = a(τ)² g₀`, test function `C⁴` and `ℤⁿ`-periodic.  `unfold` (integral over the cube of a periodised
function supported in the ball of radius 1/2 = integral over `ℝⁿ`), `pop_ratio` / `Lmet_pop` (population operator
of the N-point files = averaging operator of the flat files), `flat_npoint`: with probability at least
`1 − 15·N·2e^{−L}`, (i) and (ii) hold at all sample points, with the error `(2/(m₂ξ²))·err5g(…)` and in (ii) the
additional term `ξ² min{C₁/|η|, C₂}`.
NOT formalised: the error in the RATE FORM `C δ'/ξ` with probability `1 − C/N²` (the constants of `err5g` are
explicit but not rewritten in `δ'`); the bounds `hBI`, `hMI` for the time difference quotient of the kernel are
HYPOTHESES here; Gaussian profiles; measurability; uniformity over pairs of times; `f` Lipschitz/bounded are
hypotheses.  No `sorry`, no `axiom`, no `native_decide`.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryNPointLip
import CorrelationsToGeometryFlatLB4
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Group.FundamentalDomain

open MeasureTheory ProbabilityTheory Set Submodule
open scoped Pointwise
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB3 CTG.FlatLB4

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPoint

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The standard basis, as a `Basis`. -/
def bF : Module.Basis (Fin n) ℝ E := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

theorem bF_repr (x : E) (i : Fin n) : (bF (n := n)).repr x i = x i := by
  simp [bF]

/-- The unit cube `[0,1)ⁿ`, a fundamental domain of `ℤⁿ`. -/
def DT : Set E := ZSpan.fundamentalDomain (bF (n := n))

theorem mem_DT (x : E) : x ∈ DT (n := n) ↔ ∀ i, x i ∈ Ico (0:ℝ) 1 := by
  simp [DT, ZSpan.fundamentalDomain, bF_repr]

theorem DT_measurable : MeasurableSet (DT (n := n)) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem volume_DT : volume (DT (n := n)) = 1 := by
  have h : DT (n := n) = (WithLp.ofLp) ⁻¹' (Set.pi univ fun _ : Fin n => Ico (0:ℝ) 1) := by
    ext x; simp [mem_DT]
  rw [h, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ico).nullMeasurableSet]
  simp [volume_pi_pi, Real.volume_Ico]

/-- Uniform law on the flat torus `ℝⁿ/ℤⁿ`, realised on the cube. -/
def mT : Measure E := volume.restrict (DT (n := n))

instance mT_prob : IsProbabilityMeasure (mT (n := n)) :=
  ⟨by simp [mT, volume_DT]⟩

/-- The lattice `ℤⁿ`. -/
abbrev Lat : Submodule ℤ E := span ℤ (range (bF (n := n)))

theorem mem_Lat (g : E) : g ∈ Lat (n := n) ↔ ∀ i, ∃ k : ℤ, (k : ℝ) = g i := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  simp [bF_repr]

instance Lat_countable : Countable (Lat (n := n)).toAddSubgroup :=
  (inferInstance : Countable (span ℤ (range (bF (n := n)))))

/-- Coordinatewise reduction to `[-1/2, 1/2)`. -/
def fr (v : E) : E := WithLp.toLp 2 (fun i => v i - ⌊v i + 1 / 2⌋)

theorem fr_apply (v : E) (i : Fin n) : fr v i = v i - ⌊v i + 1 / 2⌋ := rfl

theorem fr_of_mem (v : E) (h : ∀ i, v i + 1 / 2 ∈ Ico (0:ℝ) 1) : fr v = v := by
  ext i
  rw [fr_apply, Int.floor_eq_zero_iff.2 (h i)]; simp

theorem fr_add_lat (g : E) (hg : g ∈ Lat (n := n)) (v : E) : fr (g + v) = fr v := by
  rw [mem_Lat] at hg
  ext i
  obtain ⟨k, hk⟩ := hg i
  rw [fr_apply, fr_apply]
  simp only [PiLp.add_apply]
  rw [← hk, show (k:ℝ) + v i + 1 / 2 = (v i + 1 / 2) + k by ring, Int.floor_add_intCast]
  push_cast; ring

theorem sub_fr_mem (v : E) : v - fr v ∈ Lat (n := n) := by
  rw [mem_Lat]; intro i
  exact ⟨⌊v i + 1 / 2⌋, by simp [fr_apply]⟩

theorem coord_measurable (i : Fin n) : Measurable fun v : E => v i :=
  (PiLp.continuous_apply 2 _ i).measurable

theorem fr_measurable : Measurable (fr (n := n)) := by
  have : Measurable fun v : E => (fun i => v i - (⌊v i + 1 / 2⌋ : ℝ)) :=
    measurable_pi_lambda _ fun i =>
      (coord_measurable i).sub ((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
        ((coord_measurable i).add_const _).floor)
  exact (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable.comp this

theorem abs_coord_le (v : E) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  simpa [Real.norm_eq_abs] using this

/-- The vector with all coordinates `1/2`. -/
def half : E := WithLp.toLp 2 (fun _ => 1 / 2)


/-- **Unfolding.** For `Ψ` supported in the open ball of radius `1/2`,
`∫_{[0,1)ⁿ} Ψ(fr(z − x)) dz = ∫_{ℝⁿ} Ψ`, for every `x`. -/
theorem unfold (x : E) (Ψ : E → ℝ) (hΨ : ∀ v, Ψ v ≠ 0 → ‖v‖ < 1 / 2) :
    ∫ z in DT (n := n), Ψ (fr (z - x)) = ∫ v, Ψ v := by
  have hs : IsAddFundamentalDomain (Lat (n := n)).toAddSubgroup (DT (n := n)) volume :=
    ZSpan.isAddFundamentalDomain' _ volume
  set c : E := x - half
  have ht : IsAddFundamentalDomain (Lat (n := n)).toAddSubgroup (c +ᵥ DT (n := n)) volume :=
    hs.vadd_of_comm c
  have hinv : ∀ (g : (Lat (n := n)).toAddSubgroup) (z : E),
      Ψ (fr ((g +ᵥ z) - x)) = Ψ (fr (z - x)) := by
    intro g z
    show Ψ (fr (((g : E) + z) - x)) = _
    rw [show ((g : E) + z) - x = (g : E) + (z - x) by abel, fr_add_lat _ g.2]
  rw [hs.setIntegral_eq ht hinv]
  have hmem : ∀ z, z ∈ c +ᵥ DT (n := n) ↔ ∀ i, (z - x) i + 1 / 2 ∈ Ico (0:ℝ) 1 := by
    intro z
    rw [mem_vadd_set_iff_neg_vadd_mem, mem_DT]
    refine forall_congr' fun i => ?_
    have : (-c +ᵥ z) i = (z - x) i + 1 / 2 := by
      simp [c, half, vadd_eq_add]; ring
    rw [this]
  have htm : MeasurableSet (c +ᵥ DT (n := n)) := DT_measurable.const_vadd c
  rw [setIntegral_congr_fun htm (fun z hz => by
      show Ψ (fr (z - x)) = Ψ (z - x)
      rw [fr_of_mem _ ((hmem z).1 hz)])]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      by_contra hne
      apply hz
      rw [hmem]
      intro i
      have h1 := abs_coord_le (z - x) i
      have h2 := hΨ _ hne
      have := abs_lt.1 (lt_of_le_of_lt h1 h2)
      constructor <;> linarith [this.1, this.2])]
  exact integral_sub_right_eq_self (fun v => Ψ v) x


/-! ### (b) Periodised kernels and identification of the population operator -/

/-- Flat kernel `κ(v) = h(‖S⁻¹ v‖/ξ)`. -/
def kap (h : ℝ → ℝ) (S : E ≃L[ℝ] E) (ξ : ℝ) (v : E) : ℝ := h (‖S.symm v‖ / ξ)

/-- Periodised kernel on the torus: `K(x,z) = κ(fr(z − x))`. -/
def perK (κ : E → ℝ) (x z : E) : ℝ := κ (fr (z - x))

/-- Test kernel `g(x,y) = f(y) − f(x)`. -/
def gd (f : E → ℝ) (x y : E) : ℝ := f y - f x

/-- `ℤⁿ`-periodicity. -/
def Per (f : E → ℝ) : Prop := ∀ g ∈ Lat (n := n), ∀ z, f (g + z) = f z

theorem per_fr {f : E → ℝ} (hf : Per f) (x z : E) : f z = f (x + fr (z - x)) := by
  have := hf _ (sub_fr_mem (z - x)) (x + fr (z - x))
  rw [← this]; congr 1; abel

/-- HYPOTHESES on the profile: measurable, `0 ≤ h ≤ A`, `h(s) = 0` for `s ≥ R`. -/
structure Prof (h : ℝ → ℝ) (A R : ℝ) : Prop where
  meas : Measurable h
  nonneg : ∀ s, 0 ≤ h s
  le : ∀ s, h s ≤ A
  supp : ∀ s, R ≤ s → h s = 0

theorem kap_measurable {h : ℝ → ℝ} (hm : Measurable h) (S : E ≃L[ℝ] E) (ξ : ℝ) :
    Measurable (kap h S ξ) :=
  hm.comp ((continuous_norm.comp S.symm.continuous).div_const ξ).measurable

theorem kap_supp {h : ℝ → ℝ} {A R : ℝ} (hP : Prof h A R) (S : E ≃L[ℝ] E) {ξ ρ : ℝ} (hξ : 0 < ξ)
    (hρ : ‖(S : E →L[ℝ] E)‖ * (ξ * R) ≤ ρ) (v : E) (hv : kap h S ξ v ≠ 0) : ‖v‖ ≤ ρ := by
  have h1 : ‖S.symm v‖ / ξ < R := by
    by_contra hc; exact hv (hP.supp _ (not_lt.1 hc))
  have h2 : ‖S.symm v‖ ≤ ξ * R := by
    rw [div_lt_iff₀ hξ] at h1; linarith
  have h3 : ‖v‖ ≤ ‖(S : E →L[ℝ] E)‖ * ‖S.symm v‖ := by
    have e : ‖v‖ = ‖(S : E →L[ℝ] E) (S.symm v)‖ := by
      rw [ContinuousLinearEquiv.coe_coe, S.apply_symm_apply]
    rw [e]; exact (S : E →L[ℝ] E).le_opNorm _
  calc ‖v‖ ≤ ‖(S : E →L[ℝ] E)‖ * ‖S.symm v‖ := h3
    _ ≤ ‖(S : E →L[ℝ] E)‖ * (ξ * R) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ ρ := hρ

/-- A measurable function bounded by `B` and supported in the closed ball of radius `ρ` is
integrable. -/
theorem integrable_of_supp {φ : E → ℝ} (hm : Measurable φ) {B ρ : ℝ}
    (hB : ∀ w, |φ w| ≤ B) (hs : ∀ w, φ w ≠ 0 → ‖w‖ ≤ ρ) : Integrable φ := by
  have hg : Integrable ((Metric.closedBall (0:E) ρ).indicator fun _ => B) :=
    (integrableOn_const (C := B) (measure_closedBall_lt_top.ne)).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  refine hg.mono' hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  by_cases hw : φ w = 0
  · rw [hw, norm_zero]
    by_cases hw' : w ∈ Metric.closedBall (0:E) ρ
    · rw [indicator_of_mem hw']; exact le_trans (abs_nonneg _) (hB w)
    · rw [indicator_of_notMem hw']
  · have hw' : w ∈ Metric.closedBall (0:E) ρ := by simpa using hs w hw
    rw [indicator_of_mem hw', Real.norm_eq_abs]; exact hB w

/-- Averages of periodised kernels. -/
theorem int_per (Ψ : E → ℝ) {ρ : ℝ} (hρ : ρ < 1 / 2) (hs : ∀ w, Ψ w ≠ 0 → ‖w‖ ≤ ρ) (x : E) :
    ∫ z, Ψ (fr (z - x)) ∂mT = ∫ v, Ψ v :=
  unfold x Ψ fun v hv => lt_of_le_of_lt (hs v hv) hρ

/-- **Template constants of a periodised kernel and of its product with the test kernel.** -/
theorem good_per {f : E → ℝ} (hfc : Continuous f) {Lip : ℝ} (hLip0 : 0 ≤ Lip)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖) (hper : Per f)
    {φ : E → ℝ} (hm : Measurable φ) {Bφ Mφ ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2)
    (hB : ∀ w, |φ w| ≤ Bφ) (hs : ∀ w, φ w ≠ 0 → ‖w‖ ≤ ρ) (hM : ∫ w, |φ w| ≤ Mφ) :
    Good mT (perK φ) Bφ (Bφ * Mφ) ∧ (∀ x, ∫ z, |perK φ x z| ∂mT ≤ Mφ)
      ∧ Good mT (fun x z => perK φ x z * gd f x z) (Bφ * (Lip * ρ)) ((Lip * ρ) ^ 2 * (Bφ * Mφ))
      ∧ (∀ x, ∫ z, |perK φ x z * gd f x z| ∂mT ≤ Lip * ρ * Mφ) := by
  have hB0 : 0 ≤ Bφ := le_trans (abs_nonneg _) (hB 0)
  have hi : Integrable φ := integrable_of_supp hm hB hs
  have hM0 : 0 ≤ Mφ := le_trans (integral_nonneg fun _ => abs_nonneg _) hM
  have hLρ : 0 ≤ Lip * ρ := mul_nonneg hLip0 hρ0
  have hfr : Measurable fun p : E × E => fr (p.2 - p.1) :=
    fr_measurable.comp (measurable_snd.sub measurable_fst)
  -- f-increment on the support
  have hinc : ∀ x w, φ w ≠ 0 → |f (x + w) - f x| ≤ Lip * ρ := by
    intro x w hw
    calc |f (x + w) - f x| ≤ Lip * ‖(x + w) - x‖ := hLip x (x + w)
      _ = Lip * ‖w‖ := by rw [add_sub_cancel_left]
      _ ≤ Lip * ρ := mul_le_mul_of_nonneg_left (hs w hw) hLip0
  have hsq : ∀ w, φ w ^ 2 ≤ Bφ * |φ w| := by
    intro w
    rw [← sq_abs]; nlinarith [abs_nonneg (φ w), hB w]
  -- the test kernel as a function of `fr(z − x)`
  have hT : (fun x z => perK φ x z * gd f x z)
      = fun x z => (fun w => φ w * (f (x + w) - f x)) (fr (z - x)) := by
    funext x z; simp only [perK, gd]; rw [← per_fr hper x z]
  refine ⟨⟨hm.comp hfr, hB0, mul_nonneg hB0 hM0, fun x z => hB _, fun x => ?_⟩,
    fun x => ?_, ?_, fun x => ?_⟩
  · rw [show (fun z => perK φ x z ^ 2) = fun z => (fun w => φ w ^ 2) (fr (z - x)) from rfl,
      int_per (fun w => φ w ^ 2) hρ (fun w hw => hs w (by intro h0; apply hw; simp [h0])) x]
    calc ∫ w, φ w ^ 2 ≤ ∫ w, Bφ * |φ w| :=
          integral_mono_of_nonneg (ae_of_all _ fun w => sq_nonneg _) (hi.abs.const_mul Bφ)
            (ae_of_all _ hsq)
      _ = Bφ * ∫ w, |φ w| := integral_const_mul _ _
      _ ≤ Bφ * Mφ := mul_le_mul_of_nonneg_left hM hB0
  · rw [show (fun z => |perK φ x z|) = fun z => (fun w => |φ w|) (fr (z - x)) from rfl,
      int_per (fun w => |φ w|) hρ (fun w hw => hs w (by intro h0; apply hw; simp [h0])) x]
    exact hM
  · rw [hT]
    refine ⟨?_, mul_nonneg hB0 hLρ, by positivity, fun x z => ?_, fun x => ?_⟩
    · have : Measurable fun q : E × E => φ q.2 * (f (q.1 + q.2) - f q.1) :=
        (hm.comp measurable_snd).mul
          ((hfc.measurable.comp (measurable_fst.add measurable_snd)).sub
            (hfc.measurable.comp measurable_fst))
      exact this.comp (measurable_fst.prodMk hfr)
    · show |φ (fr (z - x)) * (f (x + fr (z - x)) - f x)| ≤ Bφ * (Lip * ρ)
      by_cases h0 : φ (fr (z - x)) = 0
      · rw [h0, zero_mul, abs_zero]; exact mul_nonneg hB0 hLρ
      · rw [abs_mul]
        exact mul_le_mul (hB _) (hinc x _ h0) (abs_nonneg _) hB0
    · show ∫ z, (φ (fr (z - x)) * (f (x + fr (z - x)) - f x)) ^ 2 ∂mT ≤ _
      rw [int_per (fun w => (φ w * (f (x + w) - f x)) ^ 2) hρ
        (fun w hw => hs w (by intro h0; apply hw; simp [h0])) x]
      calc ∫ w, (φ w * (f (x + w) - f x)) ^ 2 ≤ ∫ w, (Lip * ρ) ^ 2 * (Bφ * |φ w|) :=
            integral_mono_of_nonneg (ae_of_all _ fun w => sq_nonneg _)
              ((hi.abs.const_mul Bφ).const_mul _) (ae_of_all _ fun w => by
                by_cases h0 : φ w = 0
                · simp [h0]
                · have e1 := hinc x w h0
                  have e2 : (f (x + w) - f x) ^ 2 ≤ (Lip * ρ) ^ 2 := by
                    rw [← sq_abs]; nlinarith [abs_nonneg (f (x + w) - f x)]
                  rw [mul_pow]
                  have := hsq w
                  nlinarith [sq_nonneg (φ w), sq_nonneg (f (x + w) - f x)])
        _ = (Lip * ρ) ^ 2 * (Bφ * ∫ w, |φ w|) := by
            rw [integral_const_mul, integral_const_mul]
        _ ≤ (Lip * ρ) ^ 2 * (Bφ * Mφ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM hB0) (sq_nonneg _)
  · rw [show (fun z => |perK φ x z * gd f x z|)
        = fun z => |φ (fr (z - x)) * (f (x + fr (z - x)) - f x)| from
      funext fun z => by rw [congrFun (congrFun hT x) z]]
    rw [int_per (fun w => |φ w * (f (x + w) - f x)|) hρ
      (fun w hw => hs w (by intro h0; apply hw; simp [h0])) x]
    calc ∫ w, |φ w * (f (x + w) - f x)| ≤ ∫ w, Lip * ρ * |φ w| :=
          integral_mono_of_nonneg (ae_of_all _ fun w => abs_nonneg _) (hi.abs.const_mul _)
            (ae_of_all _ fun w => by
              show |φ w * (f (x + w) - f x)| ≤ Lip * ρ * |φ w|
              by_cases h0 : φ w = 0
              · simp [h0]
              · rw [abs_mul, mul_comm (Lip * ρ)]
                exact mul_le_mul_of_nonneg_left (hinc x w h0) (abs_nonneg _))
      _ = Lip * ρ * ∫ w, |φ w| := integral_const_mul _ _
      _ ≤ Lip * ρ * Mφ := mul_le_mul_of_nonneg_left hM hLρ

/-- Population average of a periodised kernel: the constant `∫ κ`. -/
theorem popAvg_perK (κ : E → ℝ) {ρ : ℝ} (hρ : ρ < 1 / 2) (hs : ∀ w, κ w ≠ 0 → ‖w‖ ≤ ρ)
    (x : E) : popAvg mT (perK κ) x = ∫ v, κ v :=
  int_per κ hρ hs x

/-- **Identification (b), denominator**: `popW(K, 1) = 1`. -/
theorem popW_perK_one (κ : E → ℝ) {ρ : ℝ} (hρ : ρ < 1 / 2) (hs : ∀ w, κ w ≠ 0 → ‖w‖ ≤ ρ)
    (hp : ∫ v, κ v ≠ 0) (x : E) : popW mT (perK κ) (fun _ _ => 1) x = 1 := by
  unfold popW wKer
  simp only [popAvg_perK κ hρ hs, mul_one]
  show ∫ z, (fun w => κ w * (1 / ∫ v, κ v)) (fr (z - x)) ∂mT = 1
  rw [int_per (fun w => κ w * (1 / ∫ v, κ v)) hρ (fun w hw => hs w (by
    intro h0; apply hw; simp [h0])) x, integral_mul_const]
  field_simp

/-- **Identification (b), numerator**: `popW(K, f(y) − f(x)) = (∫ κ(v)(f(x+v) − f(x)) dv)/∫κ`
for periodic `f`. -/
theorem popW_perK_gd (κ : E → ℝ) {ρ : ℝ} (hρ : ρ < 1 / 2) (hs : ∀ w, κ w ≠ 0 → ‖w‖ ≤ ρ)
    {f : E → ℝ} (hper : Per f) (x : E) :
    popW mT (perK κ) (gd f) x = (∫ v, κ v * (f (x + v) - f x)) * (1 / ∫ v, κ v) := by
  unfold popW wKer
  simp only [popAvg_perK κ hρ hs]
  have e : (fun z => perK κ x z * gd f x z * (1 / ∫ v, κ v))
      = fun z => (fun w => κ w * (f (x + w) - f x) * (1 / ∫ v, κ v)) (fr (z - x)) := by
    funext z; simp only [perK, gd]; rw [← per_fr hper x z]
  show ∫ z, perK κ x z * gd f x z * (1 / ∫ v, κ v) ∂mT = _
  rw [e, int_per (fun w => κ w * (f (x + w) - f x) * (1 / ∫ v, κ v)) hρ
    (fun w hw => hs w (by intro h0; apply hw; simp [h0])) x, integral_mul_const]

/-- Positivity of the mass of the flat kernel (from `RadK`). -/
theorem kap_mass_pos {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hP : Prof h A R) (S : E ≃L[ℝ] E) {ξ : ℝ} (hξ : 0 < ξ) : 0 < ∫ v, kap h S ξ v := by
  obtain ⟨s, hs, hsub⟩ := subst S
  set t := |(ξ ^ Module.finrank ℝ E)⁻¹| with ht
  have hsc : ∀ u : E, ‖ξ • u‖ / ξ = ‖u‖ := fun u => by
    rw [norm_smul, Real.norm_of_nonneg hξ.le]; field_simp
  have eD : ∫ z : E, h ‖z‖ = t * (s * ∫ y : E, h (‖S.symm y‖ / ξ)) := by
    have h1 := hsub (fun y => h (‖S.symm y‖ / ξ))
    simp only [ContinuousLinearEquiv.symm_apply_apply] at h1
    have h2 := Measure.integral_comp_smul (volume : Measure E) (fun w : E => h (‖w‖ / ξ)) ξ
    simp only [hsc, smul_eq_mul] at h2
    rw [h2, h1]
  have hK : ∫ z : E, h ‖z‖ = K₀ := hk.kern.mass
  have hne : ∫ y : E, h (‖S.symm y‖ / ξ) ≠ 0 := by
    intro h0; rw [h0] at eD; simp at eD; linarith [hk.kern.mass_pos]
  have hnn : 0 ≤ ∫ y : E, h (‖S.symm y‖ / ξ) := integral_nonneg fun _ => hP.nonneg _
  exact lt_of_le_of_ne hnn (Ne.symm hne)

/-- **Identification (b)**: the population ratio is `PG − f`, i.e. `−(m₂ξ²/2)·L_ξ f`. -/
theorem pop_ratio {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hP : Prof h A R) (S : E ≃L[ℝ] E) {ξ ρ : ℝ} (hξ : 0 < ξ)
    (hρ : ‖(S : E →L[ℝ] E)‖ * (ξ * R) ≤ ρ) (hρh : ρ < 1 / 2)
    {f : E → ℝ} (hfc : Continuous f) (hper : Per f) {Lip : ℝ} (hLip0 : 0 ≤ Lip)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖) (x : E) :
    popW mT (perK (kap h S ξ)) (gd f) x / popW mT (perK (kap h S ξ)) (fun _ _ => 1) x
      = PG h S ξ f x - f x := by
  have hs := kap_supp hP S hξ hρ
  have hp := kap_mass_pos hk hP S hξ
  have hm := kap_measurable hP.meas S ξ
  have hB : ∀ w, |kap h S ξ w| ≤ A := fun w =>
    (abs_of_nonneg (hP.nonneg (‖S.symm w‖ / ξ))).trans_le (hP.le _)
  have hi : Integrable (kap h S ξ) := integrable_of_supp hm hB hs
  rw [popW_perK_one _ hρh hs hp.ne', div_one, popW_perK_gd _ hρh hs hper]
  have hρ0 : 0 ≤ ρ := by
    by_contra hc
    push_neg at hc
    have h0 : ∀ v, kap h S ξ v = 0 := fun v => by
      by_contra hv; linarith [hs v hv, norm_nonneg v]
    simp [h0] at hp
  have hI1 : Integrable fun v => kap h S ξ v * (f (x + v) - f x) := by
    refine integrable_of_supp (B := A * (Lip * ρ)) (ρ := ρ)
      (hm.mul ((hfc.measurable.comp (measurable_const.add measurable_id)).sub measurable_const))
      (fun w => ?_) (fun w hw => hs w (by intro h0; apply hw; simp [h0]))
    by_cases h0 : kap h S ξ w = 0
    · rw [h0, zero_mul, abs_zero]
      exact mul_nonneg (le_trans (abs_nonneg _) (hB 0)) (mul_nonneg hLip0 hρ0)
    · rw [abs_mul]
      refine mul_le_mul (hB w) ?_ (abs_nonneg _) (le_trans (abs_nonneg _) (hB 0))
      calc |f (x + w) - f x| ≤ Lip * ‖(x + w) - x‖ := hLip x (x + w)
        _ = Lip * ‖w‖ := by rw [add_sub_cancel_left]
        _ ≤ Lip * ρ := mul_le_mul_of_nonneg_left (hs w h0) hLip0
  have hI2 : Integrable fun v => kap h S ξ v * f x := hi.mul_const _
  have hI3 : Integrable fun v => kap h S ξ v * f (x + v) :=
    (hI1.add hI2).congr (ae_of_all _ fun v => by simp only [Pi.add_apply]; ring)
  have e : ∫ v, kap h S ξ v * (f (x + v) - f x)
      = (∫ v, kap h S ξ v * f (x + v)) - (∫ v, kap h S ξ v) * f x := by
    rw [show (fun v => kap h S ξ v * (f (x + v) - f x))
        = fun v => kap h S ξ v * f (x + v) - kap h S ξ v * f x from funext fun v => by ring,
      integral_sub hI3 hI2, integral_mul_const]
  rw [e]
  unfold PG
  show _ = (∫ y : E, kap h S ξ y * f (x + y)) / (∫ y : E, kap h S ξ y) - f x
  field_simp


/-! ### (c), (d) Population bound and the composite statement -/

/-- The sample operator `L_N f(i) = (2/(m₂ξ²)) (f(X_i) − Σ_j w_j f(X_j)/Σ_j w_j)` with the
periodised kernel of `g = a² g₀` (`a` the conformal factor at this time) and the estimated
normalisation `q_j`. -/
def LN {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a ξ : ℝ)
    (f : E → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  -(2 / (m₂ * ξ ^ 2)) * (sampW X N (perK (kap h S (ξ / a))) (gd f) i ω
      / sampW X N (perK (kap h S (ξ / a))) (fun _ _ => 1) i ω)

/-- Mass `∫ κ_τ` of the flat kernel at scale `ξ/a`. -/
def pmass (h : ℝ → ℝ) (S : E ≃L[ℝ] E) (a ξ : ℝ) : ℝ := ∫ v, kap h S (ξ / a) v

/-- The population operator in the form of `CTG.FlatLB4.Lmet`. -/
theorem Lmet_pop {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hP : Prof h A R) (S : E ≃L[ℝ] E) {a ξ ρ : ℝ} (ha : 0 < a) (hξ : 0 < ξ)
    (hρ : ‖(S : E →L[ℝ] E)‖ * (ξ / a * R) ≤ ρ) (hρh : ρ < 1 / 2)
    {f : E → ℝ} (hfc : Continuous f) (hper : Per f) {Lip : ℝ} (hLip0 : 0 ≤ Lip)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖) (x : E) :
    Lmet h m₂ S a ξ f x = -(2 / (m₂ * ξ ^ 2))
      * (popW mT (perK (kap h S (ξ / a))) (gd f) x
          / popW mT (perK (kap h S (ξ / a))) (fun _ _ => 1) x) := by
  rw [pop_ratio hk hP S (div_pos hξ ha) hρ hρh hfc hper hLip0 hLip x]
  unfold Lmet; ring

theorem scale_le {S : E ≃L[ℝ] E} {ξ a a₀ R ρ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (hR : 0 ≤ R) (hρ : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) ≤ ρ) :
    ‖(S : E →L[ℝ] E)‖ * (ξ / a * R) ≤ ρ := by
  refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hR) (norm_nonneg _)) hρ
  exact div_le_div_of_nonneg_left hξ.le ha₀ ha

/-- **The composite statement (`prop:dotLN-diff` in the flat periodic frame).**
Uniform sample on the flat torus `ℝⁿ/ℤⁿ` (law `mT`), metrics `g_τ = a(τ)² g₀`,
`g₀(v,v) = ‖S⁻¹v‖²`, profile `h` with support in `[0,R]` and `‖S‖(ξ/a₀)R ≤ ρ < 1/2`
(so the periodised kernel has at most one lattice term), periodic `C⁴` test function `f`.
With probability at least `1 − 15·N·2e^{−L}`, for every `i < N`:
(i)  `|Δ_η L_N f(i) − Δ_η L_ξ f(X_i)| ≤ (2/(m₂ξ²))·err5g`, and
(ii) `|Δ_η L_N f(i) + Δ_η(Δ_{g_τ} f)(X_i)| ≤ (2/(m₂ξ²))·err5g + ξ²·min{C₁/|η|, C₂}`,
with every template constant of `err5g` explicit in `A, BI, MI, Lip, ρ` and the two masses.
HYPOTHESES beyond the setting: `hBI`, `hMI` (pointwise and `L¹` bound of the difference quotient
of the FLAT kernel in time), the two smallness conditions `hsmall`, `hsmallD`. -/
theorem flat_npoint {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 0 < N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ ρ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ)
    (hρ : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) ≤ ρ) (hρh : ρ < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa) {BI MI L : ℝ}
    (hBI : ∀ v, |(kap h S (ξ / a τb) v - kap h S (ξ / a τa) v) / (τb - τa)| ≤ BI)
    (hMI : ∫ v, |(kap h S (ξ / a τb) v - kap h S (ξ / a τa) v) / (τb - τa)| ≤ MI)
    (hL : 0 < L)
    (hsmall : dev N A (A * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) L
        / min (pmass h S (a τa) ξ) (pmass h S (a τb) ξ) ≤ 1 / 2)
    (hsmallD : errT' N A (A * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ))
        (max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ))
        (min (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) L 1 / 1 ≤ 1 / 2) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          - (Lmet h m₂ S (a τb) ξ f (X i ω) - Lmet h m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 2 / (m₂ * ξ ^ 2) * err5g N A (A * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) BI
            (BI * MI) (max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) MI
            (min (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) L
            (Lip * ρ * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) (A * (Lip * ρ))
            ((Lip * ρ) ^ 2 * (A * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)))
            (Lip * ρ * MI) (BI * (Lip * ρ)) ((Lip * ρ) ^ 2 * (BI * MI)) 1
      ∧ |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 2 / (m₂ * ξ ^ 2) * err5g N A (A * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) BI
            (BI * MI) (max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) MI
            (min (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) L
            (Lip * ρ * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)) (A * (Lip * ρ))
            ((Lip * ρ) ^ 2 * (A * max (pmass h S (a τa) ξ) (pmass h S (a τb) ξ)))
            (Lip * ρ * MI) (BI * (Lip * ρ)) ((Lip * ρ) ^ 2 * (BI * MI)) 1
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)))}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hfc : Continuous f := hf.continuous
  set κa := kap h S (ξ / a τa) with hκa
  set κb := kap h S (ξ / a τb) with hκb
  set pa := pmass h S (a τa) ξ with hpa
  set pb := pmass h S (a τb) ξ with hpb
  set η := τb - τa with hη
  have hρa := scale_le (S := S) hξ ha₀ (ha τa) hR hρ
  have hρb := scale_le (S := S) hξ ha₀ (ha τb) hR hρ
  have hsa := kap_supp hP S (div_pos hξ (hpos τa)) hρa
  have hsb := kap_supp hP S (div_pos hξ (hpos τb)) hρb
  have hρ0 : 0 ≤ ρ := le_trans (mul_nonneg (norm_nonneg _)
    (mul_nonneg (div_pos hξ ha₀).le hR)) hρ
  have hpa0 : 0 < pa := kap_mass_pos hk hP S (div_pos hξ (hpos τa))
  have hpb0 : 0 < pb := kap_mass_pos hk hP S (div_pos hξ (hpos τb))
  have hA : ∀ (ξ' : ℝ) w, |kap h S ξ' w| ≤ A := fun ξ' w =>
    (abs_of_nonneg (hP.nonneg (‖S.symm w‖ / ξ'))).trans_le (hP.le _)
  have habs : ∀ ξ' : ℝ, ∫ w, |kap h S ξ' w| = ∫ w, kap h S ξ' w := fun ξ' =>
    integral_congr_ae (ae_of_all _ fun w => abs_of_nonneg (hP.nonneg (‖S.symm w‖ / ξ')))
  have hMa : ∫ w, |κa w| ≤ max pa pb := by rw [habs]; exact le_max_left _ _
  have hMb : ∫ w, |κb w| ≤ max pa pb := by rw [habs]; exact le_max_right _ _
  obtain ⟨GKa, LKa, GFa, LFa⟩ := good_per hfc hLip0 hLip hper (kap_measurable hP.meas S _)
    hρ0 hρh (hA _) hsa hMa
  obtain ⟨GKb, LKb, GFb, LFb⟩ := good_per hfc hLip0 hLip hper (kap_measurable hP.meas S _)
    hρ0 hρh (hA _) hsb hMb
  have hsI : ∀ w, (κb w - κa w) / η ≠ 0 → ‖w‖ ≤ ρ := by
    intro w hw
    by_cases h0 : κb w = 0
    · exact hsa w (by intro h1; apply hw; rw [h0, show κa w = 0 from h1]; simp)
    · exact hsb w h0
  obtain ⟨GKi, LKi, GFi, LFi⟩ := good_per hfc hLip0 hLip hper (φ := fun w => (κb w - κa w) / η)
    (((kap_measurable hP.meas S _).sub (kap_measurable hP.meas S _)).div_const _)
    hρ0 hρh hBI hsI hMI
  have hc : 0 < min pa pb := lt_min hpa0 hpb0
  have hMI0 : 0 ≤ MI := le_trans (integral_nonneg fun _ => abs_nonneg _) hMI
  have hM0 : 0 ≤ max pa pb := le_trans hpa0.le (le_max_left _ _)
  have hLρ : 0 ≤ Lip * ρ := mul_nonneg hLip0 hρ0
  have H := step5g X h_indep hX hlaw N hN (perK κa) (perK κb) (gd f) η GKa GKb GKi hc hL
    (fun y => by rw [popAvg_perK κa hρh hsa]; exact min_le_left _ _)
    (fun y => by rw [popAvg_perK κb hρh hsb]; exact min_le_right _ _)
    hM0 LKa LKb hMI0 LKi GFa GFb GFi (mul_nonneg hLρ hM0) LFa LFb (mul_nonneg hLρ hMI0) LFi
    one_pos (fun x => by rw [popW_perK_one κa hρh hsa hpa0.ne'])
    (fun x => by rw [popW_perK_one κb hρh hsb hpb0.ne']) hsmall hsmallD
  refine le_trans (measureReal_mono ?_) H
  intro ω hω
  obtain ⟨i, hi, hfail⟩ := hω
  refine ⟨i, hi, ?_⟩
  by_contra hle
  push_neg at hle
  apply hfail
  set e := err5g N A (A * max pa pb) BI (BI * MI) (max pa pb) MI (min pa pb) L
    (Lip * ρ * max pa pb) (A * (Lip * ρ)) ((Lip * ρ) ^ 2 * (A * max pa pb)) (Lip * ρ * MI)
    (BI * (Lip * ρ)) ((Lip * ρ) ^ 2 * (BI * MI)) 1 with he
  set k := 2 / (m₂ * ξ ^ 2) with hk'
  have hk0 : 0 < k := by positivity
  set x := X i ω
  set rb := sampW X N (perK κb) (gd f) i ω / sampW X N (perK κb) (fun _ _ => 1) i ω
  set ra := sampW X N (perK κa) (gd f) i ω / sampW X N (perK κa) (fun _ _ => 1) i ω
  set Pb := popW mT (perK κb) (gd f) x / popW mT (perK κb) (fun _ _ => 1) x
  set Pa := popW mT (perK κa) (gd f) x / popW mT (perK κa) (fun _ _ => 1) x
  have eLb : LN X N h m₂ S (a τb) ξ f i ω = -k * rb := rfl
  have eLa : LN X N h m₂ S (a τa) ξ f i ω = -k * ra := rfl
  have eMb : Lmet h m₂ S (a τb) ξ f x = -k * Pb :=
    Lmet_pop hk hP S (hpos τb) hξ hρb hρh hfc hper hLip0 hLip x
  have eMa : Lmet h m₂ S (a τa) ξ f x = -k * Pa :=
    Lmet_pop hk hP S (hpos τa) hξ hρa hρh hfc hper hLip0 hLip x
  have hη0 : η ≠ 0 := sub_ne_zero.2 hne
  have key : (LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / η
      - (Lmet h m₂ S (a τb) ξ f x - Lmet h m₂ S (a τa) ξ f x) / η
      = -k * ((rb - ra) / η - (Pb - Pa) / η) := by
    rw [eLb, eLa, eMb, eMa]; field_simp; ring
  have hpop := metric_dq_min hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ x τa τb hne
  -- if the template bound holds, both inequalities hold
  have hI : |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / η
      - (Lmet h m₂ S (a τb) ξ f x - Lmet h m₂ S (a τa) ξ f x) / η| ≤ k * e := by
    rw [key, abs_mul, abs_neg, abs_of_pos hk0]
    exact mul_le_mul_of_nonneg_left hle hk0.le
  refine ⟨hI, ?_⟩
  have tri := abs_add_le
    ((LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / η
      - (Lmet h m₂ S (a τb) ξ f x - Lmet h m₂ S (a τa) ξ f x) / η)
    ((Lmet h m₂ S (a τb) ξ f x - Lmet h m₂ S (a τa) ξ f x) / η
      + (lapG S f x / a τb ^ 2 - lapG S f x / a τa ^ 2) / η)
  have e2 : (LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / η
      + (lapG S f x / a τb ^ 2 - lapG S f x / a τa ^ 2) / η
      = ((LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / η
      - (Lmet h m₂ S (a τb) ξ f x - Lmet h m₂ S (a τa) ξ f x) / η)
      + ((Lmet h m₂ S (a τb) ξ f x - Lmet h m₂ S (a τa) ξ f x) / η
      + (lapG S f x / a τb ^ 2 - lapG S f x / a τa ^ 2) / η) := by ring
  rw [e2]
  exact le_trans tri (add_le_add hI hpop)

end CTG.FlatNPoint

#print axioms CTG.FlatNPoint.unfold
#print axioms CTG.FlatNPoint.good_per
#print axioms CTG.FlatNPoint.pop_ratio
#print axioms CTG.FlatNPoint.Lmet_pop
#print axioms CTG.FlatNPoint.flat_npoint
