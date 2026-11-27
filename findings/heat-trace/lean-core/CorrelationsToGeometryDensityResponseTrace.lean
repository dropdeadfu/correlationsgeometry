/-
Forty-eighth file (Mathlib and the compiled module of the forty-third file): derivatives of the iterated kernels
and of their traces for the density response with integral kernels.
Namespace `CTG.DensityResponseCont.Trace`; check with `./check_density_response_trace.sh`.
Frame: `Hyp` of the forty-third file (finite measure, measurable kernel `0 ≤ K ≤ B`, `φ` measurable and bounded,
`n⁰ > 0`, and the HYPOTHESIS `κhom` of a homogeneous background, `∫ K(x,y) dμ(y) = κ > 0`).  No new hypothesis.
Part G/W/C (generic): iterated kernels are measurable and bounded, semigroup law `kpow_assoc`; weighted iterated
kernels `KA`, their derivative in a parameter `KA_hasDerivAt` and that of the trace `trace_hasDerivAt`;
cyclic form `trace_const` (no symmetry of `K` used).
Part P: `hasDerivAt_A0` (`d/dε A_ε(x)|₀ = A_0(x) a(x)`, `a = φ/2 − 𝒢φ + 𝒢²φ/2`), `hasDerivAt_S0`
(`S_0(x,y)(a(x)+a(y))`), `hasDerivAt_A1` (derivative for every `|ε| < 1` with uniform bounds),
`kpow2_diag_hasDerivAt`, `kpow_S_hasDerivAt` (every iterate, pointwise), and
`trace_S_hasDerivAt`: `d/dε ∫ S_ε^{(j)}(x,x) dμ(x)|₀ = (j+1) ∫ 2a(x) S_0^{(j)}(x,x) dμ(x)`, `2a = (1−𝒢)²φ`
(continuum counterpart of `hasDerivAt_trace_P_pow` of the fortieth file).
NOT formalised: remainders of second order; the trace of the iterates of `P` as a separate statement (the
diagonals agree by `Sc_kpow_diag`); the summation with `1 − √(1−s)`, the coefficient `c(a)` and its limit; the
graph without self-loops.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryDensityResponseCont

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Metric Function

namespace CTG.DensityResponseCont.Trace

open CTG.DensityResponseCont

variable {E : Type*} [MeasurableSpace E]

/-! ## Part G: generic facts -/

section Generic

variable (μ : Measure E) [IsFiniteMeasure μ]

lemma int_bound {f : E → ℝ} {M : ℝ} (hf : ∀ y, |f y| ≤ M) :
    |∫ y, f y ∂μ| ≤ M * μ.real Set.univ := by
  rw [← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hf y)

lemma integrable_bdd {f : E → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM y)

lemma meas_param (H : E → E → E → ℝ)
    (hH : Measurable (fun q : (E × E) × E => H q.1.1 q.2 q.1.2)) :
    Measurable (uncurry fun x z => ∫ y, H x y z ∂μ) :=
  (StronglyMeasurable.integral_prod_right (ν := μ) (f := fun (p : E × E) (y : E) => H p.1 y p.2)
    hH.stronglyMeasurable).measurable

lemma meas_param1 (H : E → E → ℝ) (hH : Measurable (uncurry H)) :
    Measurable (fun x => ∫ y, H x y ∂μ) :=
  (StronglyMeasurable.integral_prod_right (ν := μ) (f := H) hH.stronglyMeasurable).measurable

lemma swap_bdd (f : E → E → ℝ) (hf : Measurable (uncurry f)) {M : ℝ} (hM : ∀ x y, |f x y| ≤ M) :
    ∫ x, ∫ y, f x y ∂μ ∂μ = ∫ y, ∫ x, f x y ∂μ ∂μ :=
  integral_integral_swap (Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hM p.1 p.2))

variable {K : E → E → ℝ} {B : ℝ}

lemma kpow_meas (hKm : Measurable (uncurry K)) : ∀ j, Measurable (uncurry (kpow μ K j))
  | 0 => hKm
  | j + 1 => by
    show Measurable (uncurry fun x z => ∫ y, K x y * kpow μ K j y z ∂μ)
    exact meas_param μ _ ((hKm.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      ((kpow_meas hKm j).comp (measurable_snd.prodMk measurable_fst.snd)))

/-- Bound of the iterated kernels. -/
noncomputable def kB (μ : Measure E) (B : ℝ) (j : ℕ) : ℝ := B * (B * μ.real Set.univ) ^ j

lemma kpow_bdd (hKB : ∀ x y, |K x y| ≤ B) : ∀ j x z, |kpow μ K j x z| ≤ kB μ B j
  | 0, x, z => by simpa [kB] using hKB x z
  | j + 1, x, z => by
    show |∫ y, K x y * kpow μ K j y z ∂μ| ≤ _
    refine (int_bound μ (M := B * kB μ B j) fun y => ?_).trans (le_of_eq (by unfold kB; ring))
    rw [abs_mul]
    exact mul_le_mul (hKB x y) (kpow_bdd hKB j y z) (abs_nonneg _) ((abs_nonneg _).trans (hKB x y))

/-- Associativity (semigroup law) of the iterated kernels: `K^{(m+n+1)} = K^{(m)} ∘ K^{(n)}`. -/
theorem kpow_assoc (hKm : Measurable (uncurry K)) (hKB : ∀ x y, |K x y| ≤ B) (n : ℕ) :
    ∀ m x z, kpow μ K (m + n + 1) x z = ∫ y, kpow μ K m x y * kpow μ K n y z ∂μ
  | 0, x, z => by rw [Nat.zero_add]; rfl
  | m + 1, x, z => by
    rw [show m + 1 + n + 1 = (m + n + 1) + 1 by ring]
    show ∫ u, K x u * kpow μ K (m + n + 1) u z ∂μ =
      ∫ y, (∫ u, K x u * kpow μ K m u y ∂μ) * kpow μ K n y z ∂μ
    have h1 : (fun u => K x u * kpow μ K (m + n + 1) u z) =
        fun u => ∫ y, K x u * kpow μ K m u y * kpow μ K n y z ∂μ := by
      funext u
      rw [kpow_assoc hKm hKB n m u z, ← integral_const_mul]
      congr 1; funext y; ring
    have h2 : (fun y => (∫ u, K x u * kpow μ K m u y ∂μ) * kpow μ K n y z) =
        fun y => ∫ u, K x u * kpow μ K m u y * kpow μ K n y z ∂μ := by
      funext y; rw [← integral_mul_const]
    rw [h1, h2]
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hKB x x)
    refine swap_bdd μ (fun u y => K x u * kpow μ K m u y * kpow μ K n y z) ?_
      (M := B * kB μ B m * kB μ B n) fun u y => ?_
    · exact ((hKm.comp (measurable_const.prodMk measurable_fst)).mul (kpow_meas μ hKm m)).mul
        ((kpow_meas μ hKm n).comp (measurable_snd.prodMk measurable_const))
    · rw [abs_mul, abs_mul]
      have h3 := kpow_bdd μ hKB m u y
      have h4 := kpow_bdd μ hKB n y z
      have h5 : 0 ≤ kB μ B m := (abs_nonneg _).trans h3
      exact mul_le_mul (mul_le_mul (hKB x u) h3 (abs_nonneg _) hB0) h4 (abs_nonneg _)
        (mul_nonneg hB0 h5)

end Generic


/-! ## Part W: weighted iterated kernels and their ε-derivatives (generic) -/

/-- Weighted iterated kernels `KA_ε^{(0)} = K`, `KA_ε^{(j+1)}(x,z) = ∫ K(x,y) w_ε(y) KA_ε^{(j)}(y,z)`. -/
noncomputable def KA (μ : Measure E) (K : E → E → ℝ) (w : ℝ → E → ℝ) (ε : ℝ) : ℕ → E → E → ℝ
  | 0 => K
  | j + 1 => fun x z => ∫ y, K x y * w ε y * KA μ K w ε j y z ∂μ

/-- Their ε-derivatives (defined recursively by the product rule). -/
noncomputable def KD (μ : Measure E) (K : E → E → ℝ) (w w' : ℝ → E → ℝ) (ε : ℝ) :
    ℕ → E → E → ℝ
  | 0 => fun _ _ => 0
  | j + 1 => fun x z =>
      ∫ y, K x y * (w' ε y * KA μ K w ε j y z + w ε y * KD μ K w w' ε j y z) ∂μ

/-- Standing hypotheses on the kernel and the weight family on an open set `U` of parameters. -/
structure WHyp (μ : Measure E) (K : E → E → ℝ) (w w' : ℝ → E → ℝ) (U : Set ℝ) (B Mw Mw' : ℝ) :
    Prop where
  Km : Measurable (uncurry K)
  KB : ∀ x y, |K x y| ≤ B
  B0 : 0 ≤ B
  wm : ∀ ε, Measurable (w ε)
  w'm : ∀ ε, Measurable (w' ε)
  Mw0 : 0 ≤ Mw
  Mw'0 : 0 ≤ Mw'
  wb : ∀ ε ∈ U, ∀ y, |w ε y| ≤ Mw
  w'b : ∀ ε ∈ U, ∀ y, |w' ε y| ≤ Mw'
  wd : ∀ ε ∈ U, ∀ y, HasDerivAt (fun e => w e y) (w' ε y) ε
  Uo : IsOpen U

/-- Bound of `KA`. -/
noncomputable def aB (μ : Measure E) (B Mw : ℝ) (j : ℕ) : ℝ := B * (B * Mw * μ.real Set.univ) ^ j

/-- Bound of `KD`. -/
noncomputable def dB (μ : Measure E) (B Mw Mw' : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => B * (Mw' * aB μ B Mw j + Mw * dB μ B Mw Mw' j) * μ.real Set.univ

section Weighted

variable {μ : Measure E} [IsFiniteMeasure μ] {K : E → E → ℝ} {w w' : ℝ → E → ℝ} {U : Set ℝ}
  {B Mw Mw' : ℝ} (h : WHyp μ K w w' U B Mw Mw')
include h

lemma aB_nonneg (j : ℕ) : 0 ≤ aB μ B Mw j := by
  unfold aB; have := h.B0; have := h.Mw0; positivity

lemma dB_nonneg : ∀ j, 0 ≤ dB μ B Mw Mw' j
  | 0 => le_rfl
  | j + 1 => by
    show 0 ≤ B * (Mw' * aB μ B Mw j + Mw * dB μ B Mw Mw' j) * μ.real Set.univ
    have := h.B0; have := h.Mw0; have := h.Mw'0; have := aB_nonneg h j; have := dB_nonneg j
    positivity

lemma KA_meas (ε : ℝ) : ∀ j, Measurable (uncurry (KA μ K w ε j))
  | 0 => h.Km
  | j + 1 => by
    show Measurable (uncurry fun x z => ∫ y, K x y * w ε y * KA μ K w ε j y z ∂μ)
    exact meas_param μ _ (((h.Km.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      ((h.wm ε).comp measurable_snd)).mul
      ((KA_meas ε j).comp (measurable_snd.prodMk measurable_fst.snd)))

lemma KD_meas (ε : ℝ) : ∀ j, Measurable (uncurry (KD μ K w w' ε j))
  | 0 => measurable_const
  | j + 1 => by
    show Measurable (uncurry fun x z =>
      ∫ y, K x y * (w' ε y * KA μ K w ε j y z + w ε y * KD μ K w w' ε j y z) ∂μ)
    exact meas_param μ _ ((h.Km.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      ((((h.w'm ε).comp measurable_snd).mul
        ((KA_meas h ε j).comp (measurable_snd.prodMk measurable_fst.snd))).add
       (((h.wm ε).comp measurable_snd).mul
        ((KD_meas ε j).comp (measurable_snd.prodMk measurable_fst.snd)))))

lemma KA_bdd : ∀ j, ∀ ε ∈ U, ∀ x z, |KA μ K w ε j x z| ≤ aB μ B Mw j
  | 0, ε, _, x, z => by simpa [aB, KA] using h.KB x z
  | j + 1, ε, hε, x, z => by
    show |∫ y, K x y * w ε y * KA μ K w ε j y z ∂μ| ≤ _
    refine (int_bound μ (M := B * Mw * aB μ B Mw j) fun y => ?_).trans
      (le_of_eq (by unfold aB; ring))
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (h.KB x y) (h.wb ε hε y) (abs_nonneg _) h.B0)
      (KA_bdd j ε hε y z) (abs_nonneg _) (mul_nonneg h.B0 h.Mw0)

lemma KD_bdd : ∀ j, ∀ ε ∈ U, ∀ x z, |KD μ K w w' ε j x z| ≤ dB μ B Mw Mw' j
  | 0, ε, _, x, z => by simp [KD, dB]
  | j + 1, ε, hε, x, z => by
    show |∫ y, K x y * (w' ε y * KA μ K w ε j y z + w ε y * KD μ K w w' ε j y z) ∂μ| ≤
      B * (Mw' * aB μ B Mw j + Mw * dB μ B Mw Mw' j) * μ.real Set.univ
    refine int_bound μ fun y => ?_
    rw [abs_mul]
    refine mul_le_mul (h.KB x y) ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _) h.B0
    · rw [abs_mul]
      exact mul_le_mul (h.w'b ε hε y) (KA_bdd h j ε hε y z) (abs_nonneg _) h.Mw'0
    · rw [abs_mul]
      exact mul_le_mul (h.wb ε hε y) (KD_bdd j ε hε y z) (abs_nonneg _) h.Mw0

/-- **Derivative of the weighted iterated kernels**, at every parameter of `U`. -/
theorem KA_hasDerivAt : ∀ j, ∀ ε0 ∈ U, ∀ x z,
    HasDerivAt (fun ε => KA μ K w ε j x z) (KD μ K w w' ε0 j x z) ε0
  | 0, ε0, _, x, z => by
    show HasDerivAt (fun _ => K x z) 0 ε0
    exact hasDerivAt_const _ _
  | j + 1, ε0, hε0, x, z => by
    show HasDerivAt (fun ε => ∫ y, K x y * w ε y * KA μ K w ε j y z ∂μ)
      (∫ y, K x y * (w' ε0 y * KA μ K w ε0 j y z + w ε0 y * KD μ K w w' ε0 j y z) ∂μ) ε0
    have hmeasF : ∀ ε, Measurable (fun y => K x y * w ε y * KA μ K w ε j y z) := fun ε =>
      ((h.Km.comp (measurable_const.prodMk measurable_id)).mul (h.wm ε)).mul
        ((KA_meas h ε j).comp (measurable_id.prodMk measurable_const))
    have hmeasF' : Measurable
        (fun y => K x y * (w' ε0 y * KA μ K w ε0 j y z + w ε0 y * KD μ K w w' ε0 j y z)) :=
      (h.Km.comp (measurable_const.prodMk measurable_id)).mul
        (((h.w'm ε0).mul ((KA_meas h ε0 j).comp (measurable_id.prodMk measurable_const))).add
          ((h.wm ε0).mul ((KD_meas h ε0 j).comp (measurable_id.prodMk measurable_const))))
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun ε y => K x y * w ε y * KA μ K w ε j y z)
      (F' := fun ε y => K x y * (w' ε y * KA μ K w ε j y z + w ε y * KD μ K w w' ε j y z))
      (x₀ := ε0) (bound := fun _ => B * (Mw' * aB μ B Mw j + Mw * dB μ B Mw Mw' j))
      (h.Uo.mem_nhds hε0)
      (Eventually.of_forall fun ε => (hmeasF ε).aestronglyMeasurable)
      (integrable_bdd μ (hmeasF ε0) (M := B * Mw * aB μ B Mw j) fun y => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (h.KB x y) (h.wb ε0 hε0 y) (abs_nonneg _) h.B0)
          (KA_bdd h j ε0 hε0 y z) (abs_nonneg _) (mul_nonneg h.B0 h.Mw0))
      hmeasF'.aestronglyMeasurable
      (ae_of_all _ fun y ε hε => by
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul (h.KB x y) ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (abs_nonneg _)
          h.B0
        · rw [abs_mul]
          exact mul_le_mul (h.w'b ε hε y) (KA_bdd h j ε hε y z) (abs_nonneg _) h.Mw'0
        · rw [abs_mul]
          exact mul_le_mul (h.wb ε hε y) (KD_bdd h j ε hε y z) (abs_nonneg _) h.Mw0)
      (integrable_const _)
      (ae_of_all _ fun y ε hε => by
        have := ((h.wd ε hε y).const_mul (K x y)).mul (KA_hasDerivAt j ε hε y z)
        convert this using 1; ring)
    exact this.2

/-- **Derivative of the weighted trace** `∫ w_ε(x) KA_ε^{(j)}(x,x) dμ(x)`. -/
theorem trace_hasDerivAt (j : ℕ) (ε0 : ℝ) (hε0 : ε0 ∈ U) :
    HasDerivAt (fun ε => ∫ x, w ε x * KA μ K w ε j x x ∂μ)
      (∫ x, (w' ε0 x * KA μ K w ε0 j x x + w ε0 x * KD μ K w w' ε0 j x x) ∂μ) ε0 := by
  have hd : ∀ ε, Measurable (fun x => KA μ K w ε j x x) := fun ε =>
    (KA_meas h ε j).comp (measurable_id.prodMk measurable_id)
  have hdD : ∀ ε, Measurable (fun x => KD μ K w w' ε j x x) := fun ε =>
    (KD_meas h ε j).comp (measurable_id.prodMk measurable_id)
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun ε x => w ε x * KA μ K w ε j x x)
    (F' := fun ε x => w' ε x * KA μ K w ε j x x + w ε x * KD μ K w w' ε j x x)
    (x₀ := ε0) (bound := fun _ => Mw' * aB μ B Mw j + Mw * dB μ B Mw Mw' j)
    (h.Uo.mem_nhds hε0)
    (Eventually.of_forall fun ε => ((h.wm ε).mul (hd ε)).aestronglyMeasurable)
    (integrable_bdd μ ((h.wm ε0).mul (hd ε0)) (M := Mw * aB μ B Mw j) fun x => by
      rw [abs_mul]
      exact mul_le_mul (h.wb ε0 hε0 x) (KA_bdd h j ε0 hε0 x x) (abs_nonneg _) h.Mw0)
    ((((h.w'm ε0).mul (hd ε0)).add ((h.wm ε0).mul (hdD ε0)))).aestronglyMeasurable
    (ae_of_all _ fun x ε hε => by
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul (h.w'b ε hε x) (KA_bdd h j ε hε x x) (abs_nonneg _) h.Mw'0
      · rw [abs_mul]
        exact mul_le_mul (h.wb ε hε x) (KD_bdd h j ε hε x x) (abs_nonneg _) h.Mw0)
    (integrable_const _)
    (ae_of_all _ fun x ε hε => (h.wd ε hε x).mul (KA_hasDerivAt h j ε hε x x))
  exact this.2

/-! ### Constant weight at the base point: cyclic form of the derivative -/

lemma KA_const (ε0 c : ℝ) (hc : ∀ y, w ε0 y = c) :
    ∀ j x z, KA μ K w ε0 j x z = c ^ j * kpow μ K j x z
  | 0, x, z => by simp [KA, kpow]
  | j + 1, x, z => by
    show ∫ y, K x y * w ε0 y * KA μ K w ε0 j y z ∂μ = c ^ (j + 1) * ∫ y, K x y * kpow μ K j y z ∂μ
    rw [← integral_const_mul]
    congr 1; funext y
    rw [hc y, KA_const ε0 c hc j y z]; ring

end Weighted


section Cyclic

variable {μ : Measure E} [IsFiniteMeasure μ] {K : E → E → ℝ} {w w' : ℝ → E → ℝ} {U : Set ℝ}
  {B Mw Mw' : ℝ} (h : WHyp μ K w w' U B Mw Mw')
include h

lemma tri_meas (v : E → ℝ) (hv : Measurable v) (i m : ℕ) (z : E) :
    Measurable (uncurry fun y u => kpow μ K i y u * v u * kpow μ K m u z) :=
  ((kpow_meas μ h.Km i).mul (hv.comp measurable_snd)).mul
    ((kpow_meas μ h.Km m).comp (measurable_snd.prodMk measurable_const))

lemma tri_bdd (v : E → ℝ) {Mv : ℝ} (hMv : 0 ≤ Mv) (hv : ∀ y, |v y| ≤ Mv) (i m : ℕ) (x y z : E) :
    |kpow μ K i x y * v y * kpow μ K m y z| ≤ kB μ B i * Mv * kB μ B m := by
  rw [abs_mul, abs_mul]
  have h3 := kpow_bdd μ h.KB i x y
  have h4 := kpow_bdd μ h.KB m y z
  exact mul_le_mul (mul_le_mul h3 (hv y) (abs_nonneg _) ((abs_nonneg _).trans h3)) h4
    (abs_nonneg _) (mul_nonneg ((abs_nonneg _).trans h3) hMv)

/-- Moving one factor `K` out of a sandwich (one Fubini step). -/
lemma shift_term (v : E → ℝ) (hv : Measurable v) {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ y, |v y| ≤ Mv)
    (i m : ℕ) (x z : E) :
    ∫ y, kpow μ K (i + 1) x y * v y * kpow μ K m y z ∂μ =
      ∫ u, K x u * ∫ y, kpow μ K i u y * v y * kpow μ K m y z ∂μ ∂μ := by
  show ∫ y, (∫ u, K x u * kpow μ K i u y ∂μ) * v y * kpow μ K m y z ∂μ = _
  have h1 : (fun y => (∫ u, K x u * kpow μ K i u y ∂μ) * v y * kpow μ K m y z) =
      fun y => ∫ u, K x u * (kpow μ K i u y * v y * kpow μ K m y z) ∂μ := by
    funext y; rw [← integral_mul_const, ← integral_mul_const]; congr 1; funext u; ring
  have h2 : (fun u => K x u * ∫ y, kpow μ K i u y * v y * kpow μ K m y z ∂μ) =
      fun u => ∫ y, K x u * (kpow μ K i u y * v y * kpow μ K m y z) ∂μ := by
    funext u; rw [← integral_const_mul]
  rw [h1, h2]
  refine (swap_bdd μ (fun u y => K x u * (kpow μ K i u y * v y * kpow μ K m y z)) ?_
    (M := B * (kB μ B i * Mv * kB μ B m)) fun u y => ?_).symm
  · exact (h.Km.comp (measurable_const.prodMk measurable_fst)).mul (tri_meas h v hv i m z)
  · rw [abs_mul]
    exact mul_le_mul (h.KB x u) (tri_bdd h v hMv hvb i m u y z) (abs_nonneg _) h.B0

/-- Cyclic step for the trace (one Fubini step and the semigroup law). -/
lemma cyc_term (v : E → ℝ) (hv : Measurable v) {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ y, |v y| ≤ Mv)
    (i m : ℕ) :
    ∫ x, ∫ y, kpow μ K i x y * v y * kpow μ K m y x ∂μ ∂μ =
      ∫ y, v y * kpow μ K (m + i + 1) y y ∂μ := by
  rw [swap_bdd μ (fun x y => kpow μ K i x y * v y * kpow μ K m y x) ?_
    (M := kB μ B i * Mv * kB μ B m) fun x y => tri_bdd h v hMv hvb i m x y x]
  · congr 1; funext y
    rw [kpow_assoc μ h.Km h.KB i m y y, ← integral_const_mul]
    congr 1; funext x; ring
  · exact ((kpow_meas μ h.Km i).mul (hv.comp measurable_snd)).mul
      ((kpow_meas μ h.Km m).comp (measurable_snd.prodMk measurable_fst))

/-- **`KD` at a constant weight**: a sum of sandwiches `K^{(i)} w' K^{(j-i)}`. -/
lemma KD_const (ε0 c : ℝ) (hε0 : ε0 ∈ U) (hc : ∀ y, w ε0 y = c) :
    ∀ j x z, KD μ K w w' ε0 (j + 1) x z =
      c ^ j * ∑ i ∈ Finset.range (j + 1),
        ∫ y, kpow μ K i x y * w' ε0 y * kpow μ K (j - i) y z ∂μ
  | 0, x, z => by
    show ∫ y, K x y * (w' ε0 y * KA μ K w ε0 0 y z + w ε0 y * KD μ K w w' ε0 0 y z) ∂μ = _
    simp only [pow_zero, one_mul, zero_add, Finset.sum_range_one, Nat.sub_self]
    congr 1; funext y
    show K x y * (w' ε0 y * K y z + w ε0 y * 0) = K x y * w' ε0 y * K y z
    ring
  | j + 1, x, z => by
    have hw'b := h.w'b ε0 hε0
    set g : ℕ → E → ℝ := fun i y => ∫ u, kpow μ K i y u * w' ε0 u * kpow μ K (j - i) u z ∂μ
      with hg
    have hgm : ∀ i, Measurable (g i) := fun i =>
      meas_param1 μ _ (tri_meas h (w' ε0) (h.w'm ε0) i (j - i) z)
    have hgb : ∀ i y, |g i y| ≤ kB μ B i * Mw' * kB μ B (j - i) * μ.real Set.univ := fun i y =>
      int_bound μ fun u => tri_bdd h (w' ε0) h.Mw'0 hw'b i (j - i) y u z
    show ∫ y, K x y * (w' ε0 y * KA μ K w ε0 (j + 1) y z + w ε0 y * KD μ K w w' ε0 (j + 1) y z) ∂μ
      = _
    have hpt : (fun y => K x y * (w' ε0 y * KA μ K w ε0 (j + 1) y z +
        w ε0 y * KD μ K w w' ε0 (j + 1) y z)) = fun y => c ^ (j + 1) *
        (K x y * w' ε0 y * kpow μ K (j + 1) y z + ∑ i ∈ Finset.range (j + 1), K x y * g i y) := by
      funext y
      rw [KA_const h ε0 c hc (j + 1) y z, hc y, KD_const ε0 c hε0 hc j y z, ← Finset.mul_sum]
      simp only [hg]
      ring
    have hint0 : Integrable (fun y => K x y * w' ε0 y * kpow μ K (j + 1) y z) μ :=
      integrable_bdd μ (((h.Km.comp (measurable_const.prodMk measurable_id)).mul (h.w'm ε0)).mul
        ((kpow_meas μ h.Km (j + 1)).comp (measurable_id.prodMk measurable_const)))
        (M := B * Mw' * kB μ B (j + 1)) fun y => by
          rw [abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul (h.KB x y) (hw'b y) (abs_nonneg _) h.B0)
            (kpow_bdd μ h.KB (j + 1) y z) (abs_nonneg _) (mul_nonneg h.B0 h.Mw'0)
    have hinti : ∀ i ∈ Finset.range (j + 1), Integrable (fun y => K x y * g i y) μ := fun i _ =>
      integrable_bdd μ ((h.Km.comp (measurable_const.prodMk measurable_id)).mul (hgm i))
        (M := B * (kB μ B i * Mw' * kB μ B (j - i) * μ.real Set.univ)) fun y => by
          rw [abs_mul]
          exact mul_le_mul (h.KB x y) (hgb i y) (abs_nonneg _) h.B0
    rw [hpt, integral_const_mul, integral_add hint0 (integrable_finset_sum _ hinti),
      integral_finset_sum _ hinti, Finset.sum_range_succ' _ (j + 1)]
    congr 1
    rw [add_comm]
    congr 1
    all_goals first
      | (refine Finset.sum_congr rfl fun i hi => ?_
         rw [shift_term h (w' ε0) (h.w'm ε0) h.Mw'0 hw'b i (j + 1 - (i + 1)) x z,
           Nat.add_sub_add_right])
      | (simp only [Nat.sub_zero]; done)
      | (simp only [Nat.sub_zero]; rfl)

/-- **Cyclic form of the derivative of the trace at a constant weight.** -/
theorem trace_const (j : ℕ) (ε0 c : ℝ) (hε0 : ε0 ∈ U) (hc : ∀ y, w ε0 y = c) :
    ∫ x, (w' ε0 x * KA μ K w ε0 j x x + w ε0 x * KD μ K w w' ε0 j x x) ∂μ =
      ((j : ℝ) + 1) * c ^ j * ∫ x, w' ε0 x * kpow μ K j x x ∂μ := by
  have hw'b := h.w'b ε0 hε0
  cases j with
  | zero =>
    simp only [Nat.cast_zero, zero_add, pow_zero, one_mul]
    congr 1; funext x
    show w' ε0 x * K x x + w ε0 x * 0 = w' ε0 x * K x x
    ring
  | succ m =>
    set g : ℕ → E → ℝ := fun i x => ∫ y, kpow μ K i x y * w' ε0 y * kpow μ K (m - i) y x ∂μ
      with hg
    have hgm : ∀ i, Measurable (g i) := fun i =>
      meas_param1 μ _ (((kpow_meas μ h.Km i).mul ((h.w'm ε0).comp measurable_snd)).mul
        ((kpow_meas μ h.Km (m - i)).comp (measurable_snd.prodMk measurable_fst)))
    have hgb : ∀ i x, |g i x| ≤ kB μ B i * Mw' * kB μ B (m - i) * μ.real Set.univ := fun i x =>
      int_bound μ fun y => tri_bdd h (w' ε0) h.Mw'0 hw'b i (m - i) x y x
    have hpt : (fun x => w' ε0 x * KA μ K w ε0 (m + 1) x x + w ε0 x * KD μ K w w' ε0 (m + 1) x x)
        = fun x => c ^ (m + 1) *
          (w' ε0 x * kpow μ K (m + 1) x x + ∑ i ∈ Finset.range (m + 1), g i x) := by
      funext x
      rw [KA_const h ε0 c hc (m + 1) x x, hc x, KD_const h ε0 c hε0 hc m x x]
      simp only [hg]
      ring
    have hint0 : Integrable (fun x => w' ε0 x * kpow μ K (m + 1) x x) μ :=
      integrable_bdd μ ((h.w'm ε0).mul
        ((kpow_meas μ h.Km (m + 1)).comp (measurable_id.prodMk measurable_id)))
        (M := Mw' * kB μ B (m + 1)) fun x => by
          rw [abs_mul]
          exact mul_le_mul (hw'b x) (kpow_bdd μ h.KB (m + 1) x x) (abs_nonneg _) h.Mw'0
    have hinti : ∀ i ∈ Finset.range (m + 1), Integrable (g i) μ := fun i _ =>
      integrable_bdd μ (hgm i) (hgb i)
    rw [hpt, integral_const_mul, integral_add hint0 (integrable_finset_sum _ hinti),
      integral_finset_sum _ hinti]
    have hcyc : ∀ i ∈ Finset.range (m + 1),
        ∫ x, g i x ∂μ = ∫ x, w' ε0 x * kpow μ K (m + 1) x x ∂μ := by
      intro i hi
      have him : m - i + i + 1 = m + 1 := by
        have := Finset.mem_range.mp hi; omega
      simp only [hg]
      rw [cyc_term h (w' ε0) (h.w'm ε0) h.Mw'0 hw'b i (m - i), him]
    rw [Finset.sum_congr rfl hcyc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

end Cyclic


/-- Conjugation passes to the weighted iterated kernels: if `T(x,y) = a(x)K(x,y)a(y)` and
`w_ε = a·a`, then `T^{(j)}(x,z) = a(x) KA_ε^{(j)}(x,z) a(z)` (no integrability needed). -/
lemma kpow_conj_KA (μ : Measure E) (K : E → E → ℝ) (w : ℝ → E → ℝ) (ε : ℝ) (a : E → ℝ)
    (T : E → E → ℝ) (hT : ∀ x y, T x y = a x * K x y * a y) (hw : ∀ y, w ε y = a y * a y) :
    ∀ j x z, kpow μ T j x z = a x * KA μ K w ε j x z * a z
  | 0, x, z => hT x z
  | j + 1, x, z => by
    show ∫ y, T x y * kpow μ T j y z ∂μ = a x * (∫ y, K x y * w ε y * KA μ K w ε j y z ∂μ) * a z
    rw [← integral_const_mul, ← integral_mul_const]
    congr 1; funext y
    rw [hT x y, kpow_conj_KA μ K w ε a T hT hw j y z, hw y]; ring

/-! ## Part P: application to the density-weighted kernel `S_ε = A_ε K A_ε` -/

/-- `A_ε(y)`. -/
noncomputable def Aε (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  Ac μ K (nε n0 φ ε) y
/-- `R'_ε(y) = ∫ K(y,z) g'_ε(z) dμ(z)`. -/
noncomputable def Rd (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  ∫ z, K y z * gR' μ K φ n0 ε z ∂μ
/-- The ε-derivative of `A_ε(y)` at an arbitrary parameter. -/
noncomputable def Ad (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  Aε μ K φ n0 ε y * (φ y / 2 - qd μ K φ n0 ε y / (2 * qc μ K (nε n0 φ ε) y)
    - Rd μ K φ n0 ε y / (2 * Rc μ K (nε n0 φ ε) y))
/-- `a = φ/2 − 𝒢φ + 𝒢²φ/2`. -/
noncomputable def aφ (μ : Measure E) (K : E → E → ℝ) (κ : ℝ) (φ : E → ℝ) (x : E) : ℝ :=
  φ x / 2 - Gc μ K κ φ x + Gc μ K κ (Gc μ K κ φ) x / 2
/-- The weight family `w_ε = A_ε²` and its derivative `2 A_ε A'_ε`. -/
noncomputable def wA (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  Aε μ K φ n0 ε y * Aε μ K φ n0 ε y
noncomputable def wA' (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  2 * Aε μ K φ n0 ε y * Ad μ K φ n0 ε y
/-- The (constant) value of `A_0`. -/
noncomputable def A00 (n0 κ : ℝ) : ℝ := Real.sqrt n0 / (n0 * κ * Real.sqrt (1 / (n0 * κ)))

section Apply

variable {μ : Measure E} [IsFiniteMeasure μ] {K : E → E → ℝ} {φ : E → ℝ} {n0 κ B C : ℝ}
  (h : Hyp μ K φ n0 κ B C)
include h

lemma Aε_pos (ε : ℝ) (y : E) : 0 < Aε μ K φ n0 ε y := by
  unfold Aε Ac
  exact div_pos (Real.sqrt_pos.mpr (nε_pos h ε y))
    (mul_pos (q_pos h ε y) (Real.sqrt_pos.mpr (D_pos h ε y)))

lemma Sc_eq (ε : ℝ) (x y : E) :
    Sc μ K (nε n0 φ ε) x y = Aε μ K φ n0 ε x * K x y * Aε μ K φ n0 ε y :=
  Sc_eq_conj μ K (nε n0 φ ε) x y (nε_pos h ε x) (nε_pos h ε y) (q_pos h ε x) (q_pos h ε y)
    (D_pos h ε x) (D_pos h ε y)

/-- **Stage 1a.** `d/dε A_ε(x) = A_0(x) a(x)` at `ε = 0`. -/
theorem hasDerivAt_A0 (x : E) :
    HasDerivAt (fun ε => Aε μ K φ n0 ε x) (Aε μ K φ n0 0 x * aφ μ K κ φ x) 0 := by
  have hl := (hasDerivAt_log_A h x).exp
  have heq : (fun ε => Aε μ K φ n0 ε x) =
      fun ε => Real.exp (Real.log (Ac μ K (nε n0 φ ε) x)) := by
    funext ε; rw [Real.exp_log (show 0 < Ac μ K (nε n0 φ ε) x from Aε_pos h ε x)]; rfl
  rw [heq]
  convert hl using 1
  rw [Real.exp_log (show 0 < Ac μ K (nε n0 φ 0) x from Aε_pos h 0 x)]; rfl

/-- **Stage 1b.** `d/dε S_ε(x,y) = S_0(x,y)(a(x)+a(y))` at `ε = 0`. -/
theorem hasDerivAt_S0 (x y : E) :
    HasDerivAt (fun ε => Sc μ K (nε n0 φ ε) x y)
      (Sc μ K (nε n0 φ 0) x y * (aφ μ K κ φ x + aφ μ K κ φ y)) 0 := by
  have heq : (fun ε => Sc μ K (nε n0 φ ε) x y) =
      fun ε => Aε μ K φ n0 ε x * K x y * Aε μ K φ n0 ε y := funext fun ε => Sc_eq h ε x y
  rw [heq]
  convert ((hasDerivAt_A0 h x).mul_const (K x y)).mul (hasDerivAt_A0 h y) using 1
  rw [Sc_eq h 0 x y]; ring

lemma R_eq (ε : ℝ) (y : E) :
    Rc μ K (nε n0 φ ε) y = ∫ z, K y z * gR μ K φ n0 ε z ∂μ := by
  unfold Rc gR; congr 1; funext z; ring

/-- Differentiation under the integral against `K(x,·)` on the parameter ball `|ε| < 1`. -/
lemma hasDerivAt_int_K1 (x : E) (g g' : ℝ → E → ℝ) (ε0 M M0 : ℝ) (hε0 : ε0 ∈ ball (0 : ℝ) 1)
    (hgm : ∀ ε, Measurable (g ε)) (hg'm : Measurable (g' ε0)) (hg0 : ∀ y, |g ε0 y| ≤ M0)
    (hd : ∀ y, ∀ ε ∈ ball (0 : ℝ) 1, HasDerivAt (fun e => g e y) (g' ε y) ε)
    (hb : ∀ y, ∀ ε ∈ ball (0 : ℝ) 1, |g' ε y| ≤ M) :
    HasDerivAt (fun ε => ∫ y, K x y * g ε y ∂μ) (∫ y, K x y * g' ε0 y ∂μ) ε0 := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun ε y => K x y * g ε y) (F' := fun ε y => K x y * g' ε y) (x₀ := ε0)
    (bound := fun _ => B * M) (isOpen_ball.mem_nhds hε0)
    (Eventually.of_forall fun ε => ((meas_Kx h x).mul (hgm ε)).aestronglyMeasurable)
    (int_K_mul h x (g ε0) (hgm ε0) M0 hg0)
    (((meas_Kx h x).mul hg'm).aestronglyMeasurable)
    (ae_of_all _ fun y ε hε => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.K0 x y)]
      exact mul_le_mul (h.KB x y) (hb y ε hε) (abs_nonneg _) h.B0)
    (integrable_const _)
    (ae_of_all _ fun y ε hε => (hd y ε hε).const_mul (K x y))
  exact this.2

lemma abs_le_one_of_ball {ε : ℝ} (hε : ε ∈ ball (0 : ℝ) 1) : |ε| ≤ 1 := by
  rw [mem_ball, Real.dist_eq, sub_zero] at hε; exact hε.le

/-- Derivative of `R_ε(x)` at every `|ε0| < 1`. -/
lemma hasDerivAt_R1 (ε0 : ℝ) (hε0 : ε0 ∈ ball (0 : ℝ) 1) (x : E) :
    HasDerivAt (fun ε => Rc μ K (nε n0 φ ε) x) (Rd μ K φ n0 ε0 x) ε0 := by
  have hd := hasDerivAt_int_K1 h x (gR μ K φ n0) (gR' μ K φ n0) ε0 _ _ hε0 (meas_gR h)
    (meas_gR' h ε0) (gR_abs_le h ε0 |ε0| le_rfl) (fun y ε _ => hasDerivAt_gR h ε y)
    (fun y ε hε => gR'_abs_le h ε (abs_le_one_of_ball h hε) y)
  rw [show (fun ε => Rc μ K (nε n0 φ ε) x) = fun ε => ∫ y, K x y * gR μ K φ n0 ε y ∂μ from
    funext fun ε => R_eq h ε x]
  exact hd

/-- `A_ε = exp(((log n⁰ + εφ) − log q_ε − log R_ε)/2)`. -/
lemma A_eq_exp (ε : ℝ) (y : E) : Aε μ K φ n0 ε y = Real.exp ((Real.log n0 + ε * φ y) / 2 -
    Real.log (qc μ K (nε n0 φ ε) y) / 2 - Real.log (Rc μ K (nε n0 φ ε) y) / 2) := by
  rw [← Real.exp_log (Aε_pos h ε y)]
  congr 1
  have hD := D_pos h ε y
  have hq := q_pos h ε y
  have hn := nε_pos h ε y
  have hR := R_pos h ε y
  unfold Aε Ac
  rw [Real.log_div (Real.sqrt_pos.mpr hn).ne' (mul_pos hq (Real.sqrt_pos.mpr hD)).ne',
    Real.log_mul hq.ne' (Real.sqrt_pos.mpr hD).ne', Real.log_sqrt hn.le, Real.log_sqrt hD.le,
    Dc_eq, Real.log_div hR.ne' hq.ne']
  have hnl : Real.log (nε n0 φ ε y) = Real.log n0 + ε * φ y := by
    unfold nε; rw [Real.log_mul h.n0pos.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [hnl]; ring

/-- **Derivative of `A_ε(y)` at every `|ε0| < 1`.** -/
theorem hasDerivAt_A1 (ε0 : ℝ) (hε0 : ε0 ∈ ball (0 : ℝ) 1) (y : E) :
    HasDerivAt (fun ε => Aε μ K φ n0 ε y) (Ad μ K φ n0 ε0 y) ε0 := by
  have hq := (hasDerivAt_q h ε0 y).log (q_pos h ε0 y).ne'
  have hR := (hasDerivAt_R1 h ε0 hε0 y).log (R_pos h ε0 y).ne'
  have hlin : HasDerivAt (fun ε : ℝ => (Real.log n0 + ε * φ y) / 2) (φ y / 2) ε0 := by
    have := (((hasDerivAt_id ε0).mul_const (φ y)).const_add (Real.log n0)).div_const 2
    convert this using 1; simp
  have hL := ((hlin.sub (hq.div_const 2)).sub (hR.div_const 2)).exp
  rw [show (fun ε => Aε μ K φ n0 ε y) = fun ε => Real.exp ((Real.log n0 + ε * φ y) / 2 -
    Real.log (qc μ K (nε n0 φ ε) y) / 2 - Real.log (Rc μ K (nε n0 φ ε) y) / 2) from
    funext fun ε => A_eq_exp h ε y]
  convert hL using 1
  unfold Ad
  rw [A_eq_exp h ε0 y]
  simp only [Pi.sub_apply]
  ring

/-- `A'_0 = A_0 a` (uniqueness of the derivative). -/
lemma Ad_zero (y : E) : Ad μ K φ n0 0 y = Aε μ K φ n0 0 y * aφ μ K κ φ y :=
  (hasDerivAt_A1 h 0 (mem_ball_self one_pos) y).unique (hasDerivAt_A0 h y)

/-- `A_0` is constant. -/
lemma A0_eq (y : E) : Aε μ K φ n0 0 y = A00 n0 κ := by
  unfold Aε Ac A00
  rw [Dc_eq, R_zero h, q_zero h]
  simp [nε]

/-! ### Measurability and uniform bounds on `|ε| < 1` -/

lemma meas_R (ε : ℝ) : Measurable (Rc μ K (nε n0 φ ε)) := by
  rw [show Rc μ K (nε n0 φ ε) = fun y => ∫ z, K y z * gR μ K φ n0 ε z ∂μ from
    funext fun y => R_eq h ε y]
  exact meas_int_K h _ (meas_gR h ε)

lemma meas_D (ε : ℝ) : Measurable (Dc μ K (nε n0 φ ε)) := by
  rw [show Dc μ K (nε n0 φ ε) = fun y => Rc μ K (nε n0 φ ε) y / qc μ K (nε n0 φ ε) y from
    funext fun y => Dc_eq μ K _ y]
  exact (meas_R h ε).div (meas_q h ε)

lemma meas_A (ε : ℝ) : Measurable (Aε μ K φ n0 ε) := by
  unfold Aε Ac
  exact (meas_nε h ε).sqrt.div ((meas_q h ε).mul (meas_D h ε).sqrt)

lemma meas_Rd (ε : ℝ) : Measurable (Rd μ K φ n0 ε) := meas_int_K h _ (meas_gR' h ε)

lemma meas_Ad (ε : ℝ) : Measurable (Ad μ K φ n0 ε) := by
  unfold Ad
  exact (meas_A h ε).mul (((h.φm.div_const 2).sub ((meas_qd h ε).div ((meas_q h ε).const_mul 2))).sub
    ((meas_Rd h ε).div ((meas_R h ε).const_mul 2)))

/-- Lower bound of `q` on `|ε| ≤ 1`. -/
noncomputable def qlo (n0 κ C : ℝ) : ℝ := n0 * Real.exp (-(1 * C)) * κ
/-- Lower bound of `R` on `|ε| ≤ 1`. -/
noncomputable def Rlo (κ C : ℝ) : ℝ := Real.exp (-(1 * C)) / (Real.exp (1 * C) * κ) * κ
/-- Bound of `|qd|`. -/
noncomputable def qdB (μ : Measure E) (n0 B C : ℝ) : ℝ :=
  B * (n0 * (Real.exp (1 * C) * C)) * μ.real Set.univ
/-- Bound of `|g'|` (from `gR'_abs_le`). -/
noncomputable def gB (μ : Measure E) (n0 κ B C : ℝ) : ℝ :=
  (n0 * (Real.exp C * C) * (n0 * Real.exp C * κ) +
    n0 * Real.exp C * (B * (n0 * (Real.exp C * C)) * μ.real Set.univ)) / (n0 * Real.exp (-C) * κ) ^ 2
/-- Bound of `A`. -/
noncomputable def Aup (n0 κ C : ℝ) : ℝ :=
  Real.exp ((Real.log n0 + C) / 2 - Real.log (qlo n0 κ C) / 2 - Real.log (Rlo κ C) / 2)
/-- Bound of `A'`. -/
noncomputable def AdB (μ : Measure E) (n0 κ B C : ℝ) : ℝ :=
  Aup n0 κ C * (C / 2 + qdB μ n0 B C / (2 * qlo n0 κ C) +
    B * gB μ n0 κ B C * μ.real Set.univ / (2 * Rlo κ C))

lemma qlo_pos : 0 < qlo n0 κ C := by
  unfold qlo; have := h.n0pos; have := h.κpos; positivity

lemma Rlo_pos : 0 < Rlo κ C := by
  unfold Rlo; have := h.κpos; positivity

lemma q_ge (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : qlo n0 κ C ≤ qc μ K (nε n0 φ ε) y :=
  (q_bounds h ε 1 hε y).1

lemma R_ge (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : Rlo κ C ≤ Rc μ K (nε n0 φ ε) y := by
  rw [R_eq h ε y]
  exact int_K_lower h y _ (meas_gR h ε) _ (gR_abs_le h ε 1 hε) _
    (fun z => (gR_bounds h ε 1 hε z).1)

lemma gB_nonneg : 0 ≤ gB μ n0 κ B C := by
  unfold gB; have := h.n0pos; have := h.κpos; have := h.C0; have := h.B0; positivity

lemma Rd_abs (ε : ℝ) (hε : |ε| ≤ 1) (y : E) :
    |Rd μ K φ n0 ε y| ≤ B * gB μ n0 κ B C * μ.real Set.univ := by
  unfold Rd
  refine int_bound μ fun z => ?_
  rw [abs_mul, abs_of_nonneg (h.K0 y z)]
  exact mul_le_mul (h.KB y z) (gR'_abs_le h ε hε z) (abs_nonneg _) h.B0

lemma A_le (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : Aε μ K φ n0 ε y ≤ Aup n0 κ C := by
  rw [A_eq_exp h ε y]
  unfold Aup
  apply Real.exp_le_exp.mpr
  have h1 : ε * φ y ≤ C := by
    calc ε * φ y ≤ |ε * φ y| := le_abs_self _
      _ = |ε| * |φ y| := abs_mul _ _
      _ ≤ 1 * C := mul_le_mul hε (h.φC y) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  have h2 := Real.log_le_log (qlo_pos h) (q_ge h ε hε y)
  have h3 := Real.log_le_log (Rlo_pos h) (R_ge h ε hε y)
  linarith

lemma Aup_nonneg : 0 ≤ Aup n0 κ C := (Real.exp_pos _).le

lemma AdB_nonneg : 0 ≤ AdB μ n0 κ B C := by
  unfold AdB qdB
  have := Aup_nonneg h; have := qlo_pos h; have := Rlo_pos h; have := gB_nonneg h
  have := h.n0pos; have := h.C0; have := h.B0
  positivity

lemma Ad_abs (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : |Ad μ K φ n0 ε y| ≤ AdB μ n0 κ B C := by
  unfold Ad AdB
  have hA := Aε_pos h ε y
  have hq := q_ge h ε hε y
  have hR := R_ge h ε hε y
  have hql := qlo_pos h
  have hRl := Rlo_pos h
  rw [abs_mul, abs_of_pos hA]
  refine mul_le_mul (A_le h ε hε y) ?_ (abs_nonneg _) (Aup_nonneg h)
  refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_div, abs_two]; exact div_le_div_of_nonneg_right (h.φC y) zero_le_two
  · rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * qc μ K (nε n0 φ ε) y)]
    exact div_le_div₀ (by unfold qdB; have := h.n0pos; have := h.C0; have := h.B0; positivity)
      (qd_abs_le h ε 1 hε y) (by linarith) (by linarith)
  · rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < 2 * Rc μ K (nε n0 φ ε) y)]
    exact div_le_div₀ (by have := gB_nonneg h; have := h.B0; positivity)
      (Rd_abs h ε hε y) (by linarith) (by linarith)

/-- The weight family `A_ε²` satisfies the standing hypotheses on `|ε| < 1`. -/
theorem wHyp : WHyp μ K (wA μ K φ n0) (wA' μ K φ n0) (ball (0 : ℝ) 1) B
    (Aup n0 κ C * Aup n0 κ C) (2 * Aup n0 κ C * AdB μ n0 κ B C) where
  Km := h.Km
  KB := fun x y => by rw [abs_of_nonneg (h.K0 x y)]; exact h.KB x y
  B0 := h.B0
  wm := fun ε => (meas_A h ε).mul (meas_A h ε)
  w'm := fun ε => (measurable_const.mul (meas_A h ε)).mul (meas_Ad h ε)
  Mw0 := mul_nonneg (Aup_nonneg h) (Aup_nonneg h)
  Mw'0 := mul_nonneg (mul_nonneg zero_le_two (Aup_nonneg h)) (AdB_nonneg h)
  wb := fun ε hε y => by
    unfold wA
    rw [abs_mul, abs_of_pos (Aε_pos h ε y)]
    have := A_le h ε (abs_le_one_of_ball h hε) y
    exact mul_le_mul this this (Aε_pos h ε y).le (Aup_nonneg h)
  w'b := fun ε hε y => by
    unfold wA'
    rw [abs_mul, abs_mul, abs_two, abs_of_pos (Aε_pos h ε y)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (A_le h ε (abs_le_one_of_ball h hε) y) zero_le_two)
      (Ad_abs h ε (abs_le_one_of_ball h hε) y) (abs_nonneg _)
      (mul_nonneg zero_le_two (Aup_nonneg h))
  wd := fun ε hε y => by
    unfold wA wA'
    convert (hasDerivAt_A1 h ε hε y).mul (hasDerivAt_A1 h ε hε y) using 1; ring
  Uo := isOpen_ball

lemma kpow_S_eq (ε : ℝ) (j : ℕ) (x z : E) :
    kpow μ (Sc μ K (nε n0 φ ε)) j x z =
      Aε μ K φ n0 ε x * KA μ K (wA μ K φ n0) ε j x z * Aε μ K φ n0 ε z :=
  kpow_conj_KA μ K (wA μ K φ n0) ε (Aε μ K φ n0 ε) _ (Sc_eq h ε) (fun y => rfl) j x z

/-- **Stage 3a (pointwise, every `j`).** Derivative of the iterated kernel `S_ε^{(j)}(x,z)` at
`ε = 0`, in terms of the derivative `KD` of the weighted iterated kernel. -/
theorem kpow_S_hasDerivAt (j : ℕ) (x z : E) :
    HasDerivAt (fun ε => kpow μ (Sc μ K (nε n0 φ ε)) j x z)
      (A00 n0 κ * aφ μ K κ φ x * KA μ K (wA μ K φ n0) 0 j x z * A00 n0 κ +
        A00 n0 κ * KD μ K (wA μ K φ n0) (wA' μ K φ n0) 0 j x z * A00 n0 κ +
        A00 n0 κ * KA μ K (wA μ K φ n0) 0 j x z * (A00 n0 κ * aφ μ K κ φ z)) 0 := by
  rw [show (fun ε => kpow μ (Sc μ K (nε n0 φ ε)) j x z) = fun ε =>
    Aε μ K φ n0 ε x * KA μ K (wA μ K φ n0) ε j x z * Aε μ K φ n0 ε z from
    funext fun ε => kpow_S_eq h ε j x z]
  have := ((hasDerivAt_A0 h x).mul (KA_hasDerivAt (wHyp h) j 0 (mem_ball_self one_pos) x z)).mul
    (hasDerivAt_A0 h z)
  convert this using 1
  simp only [Pi.mul_apply]
  rw [A0_eq h x, A0_eq h z]; ring

/-- **Stage 3b (trace, every `j`).** With `k = j + 1` factors:
`d/dε ∫ S_ε^{(j)}(x,x) dμ(x) = k ∫ 2a(x) S_0^{(j)}(x,x) dμ(x)` at `ε = 0`, where
`2a = (1 − 𝒢)²φ`.  (Continuum counterpart of `hasDerivAt_trace_P_pow` of the finite file.) -/
theorem trace_S_hasDerivAt (j : ℕ) :
    HasDerivAt (fun ε => ∫ x, kpow μ (Sc μ K (nε n0 φ ε)) j x x ∂μ)
      (((j : ℝ) + 1) * ∫ x, 2 * aφ μ K κ φ x * kpow μ (Sc μ K (nε n0 φ 0)) j x x ∂μ) 0 := by
  have wh := wHyp h
  have hfun : (fun ε => ∫ x, kpow μ (Sc μ K (nε n0 φ ε)) j x x ∂μ) =
      fun ε => ∫ x, wA μ K φ n0 ε x * KA μ K (wA μ K φ n0) ε j x x ∂μ := by
    funext ε; congr 1; funext x; rw [kpow_S_eq h ε j x x]; unfold wA; ring
  rw [hfun]
  have hd := trace_hasDerivAt wh j 0 (mem_ball_self one_pos)
  set c := A00 n0 κ * A00 n0 κ with hcdef
  have hc : ∀ y, wA μ K φ n0 0 y = c := fun y => by unfold wA; rw [A0_eq h y]
  rw [trace_const wh j 0 c (mem_ball_self one_pos) hc] at hd
  convert hd using 1
  have hint : (fun x => 2 * aφ μ K κ φ x * kpow μ (Sc μ K (nε n0 φ 0)) j x x) =
      fun x => c ^ j * (wA' μ K φ n0 0 x * kpow μ K j x x) := by
    funext x
    rw [kpow_S_eq h 0 j x x, KA_const wh 0 c hc j x x]
    unfold wA'
    rw [Ad_zero h x, A0_eq h x]
    ring
  rw [hint, integral_const_mul]; ring

/-- **Stage 2.** The second iterated kernel on the diagonal:
`d/dε ∫ S_ε(x,y) S_ε(y,x) dμ(y) = 2 ∫ S_0(x,y) S_0(y,x) (a(x)+a(y)) dμ(y)` at `ε = 0`. -/
theorem kpow2_diag_hasDerivAt (x : E) :
    HasDerivAt (fun ε => ∫ y, Sc μ K (nε n0 φ ε) x y * Sc μ K (nε n0 φ ε) y x ∂μ)
      (2 * ∫ y, Sc μ K (nε n0 φ 0) x y * Sc μ K (nε n0 φ 0) y x *
        (aφ μ K κ φ x + aφ μ K κ φ y) ∂μ) 0 := by
  have wh := wHyp h
  have hd := kpow_S_hasDerivAt h 1 x x
  change HasDerivAt (fun ε => kpow μ (Sc μ K (nε n0 φ ε)) 1 x x) _ 0
  convert hd using 1
  set c := A00 n0 κ with hcdef
  set a := aφ μ K κ φ with hadef
  -- the two integrals appearing in `KA` and `KD` at `j = 1`, `ε = 0`
  have hKA : KA μ K (wA μ K φ n0) 0 1 x x = c * c * ∫ y, K x y * K y x ∂μ := by
    show ∫ y, K x y * wA μ K φ n0 0 y * K y x ∂μ = _
    rw [← integral_const_mul]; congr 1; funext y; unfold wA; rw [A0_eq h y]; ring
  have hKD : KD μ K (wA μ K φ n0) (wA' μ K φ n0) 0 1 x x =
      2 * (c * c) * ∫ y, K x y * K y x * a y ∂μ := by
    show ∫ y, K x y * (wA' μ K φ n0 0 y * K y x + wA μ K φ n0 0 y * 0) ∂μ = _
    rw [← integral_const_mul]; congr 1; funext y
    unfold wA'; rw [Ad_zero h y, A0_eq h y]; ring
  have hKK : Integrable (fun y => K x y * K y x) μ :=
    integrable_bdd μ ((h.Km.comp (measurable_const.prodMk measurable_id)).mul
      (h.Km.comp (measurable_id.prodMk measurable_const))) (M := B * B) fun y => by
        rw [abs_mul, abs_of_nonneg (h.K0 x y), abs_of_nonneg (h.K0 y x)]
        exact mul_le_mul (h.KB x y) (h.KB y x) (h.K0 y x) h.B0
  have hKKa : Integrable (fun y => K x y * K y x * a y) μ := by
    have hGb := Gc_abs_le h φ C h.φC
    have hGGb := Gc_abs_le h (Gc μ K κ φ) _ hGb
    refine integrable_bdd μ (((h.Km.comp (measurable_const.prodMk measurable_id)).mul
      (h.Km.comp (measurable_id.prodMk measurable_const))).mul
      (((h.φm.div_const 2).sub (meas_Gc h φ h.φm)).add
        ((meas_Gc h _ (meas_Gc h φ h.φm)).div_const 2)))
      (M := B * B * (C / 2 + B * C * μ.real Set.univ / κ +
        B * (B * C * μ.real Set.univ / κ) * μ.real Set.univ / κ / 2)) fun y => ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (h.K0 x y), abs_of_nonneg (h.K0 y x)]
    refine mul_le_mul (mul_le_mul (h.KB x y) (h.KB y x) (h.K0 y x) h.B0) ?_ (abs_nonneg _)
      (mul_nonneg h.B0 h.B0)
    simp only [hadef, aφ]
    refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ (hGb y))) ?_)
    · rw [abs_div, abs_two]; exact div_le_div_of_nonneg_right (h.φC y) zero_le_two
    · rw [abs_div, abs_two]; exact div_le_div_of_nonneg_right (hGGb y) zero_le_two
  have hS : (fun y => Sc μ K (nε n0 φ 0) x y * Sc μ K (nε n0 φ 0) y x * (a x + a y)) =
      fun y => (c * c * (c * c) * a x) * (K x y * K y x) + (c * c * (c * c)) * (K x y * K y x * a y) := by
    funext y; rw [Sc_eq h 0 x y, Sc_eq h 0 y x, A0_eq h x, A0_eq h y]; ring
  rw [hS, integral_add (hKK.const_mul _) (hKKa.const_mul _), integral_const_mul, integral_const_mul,
    hKA, hKD]
  ring

end Apply

end CTG.DensityResponseCont.Trace
