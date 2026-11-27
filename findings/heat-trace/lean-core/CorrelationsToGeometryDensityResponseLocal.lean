/-
Fifty-first file: the LOCAL density response — derivative of the DIAGONAL of the iterated kernel
`S_ε^{(j)}(x,x)` at `ε = 0`.  Namespace `CTG.DensityResponseCont.Local`; imports the second and the forty-eighth file (compiled modules); check with `./check_density_response_local.sh`.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
Stage 1 (frame `Hyp`): closed formula in terms of iterated kernels of `S_0` and `a = φ/2 − 𝒢φ + 𝒢²φ/2`.
Stage 2 (convolution kernel on a commutative group, invariant finite measure, cosine mode with the
addition formula): the derivative is a factor independent of `x` times `c(x)`, the factor written
with convolution powers.
Stage 3 (flat torus, `heatTorus`): the factor as a Fourier sum.
No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryReal
import CorrelationsToGeometryDensityResponseTrace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Metric Function

namespace CTG.DensityResponseCont.Local

open CTG.DensityResponseCont CTG.DensityResponseCont.Trace CTG.Reals

variable {E : Type*} [MeasurableSpace E]

/-- `A_0² = 1/κ`. -/
lemma A00_sq {n0 κ : ℝ} (hn0 : 0 < n0) (hκ : 0 < κ) : A00 n0 κ * A00 n0 κ = 1 / κ := by
  unfold A00
  have h1 : 0 < n0 * κ := mul_pos hn0 hκ
  have hs := Real.mul_self_sqrt hn0.le
  have ht := Real.mul_self_sqrt (one_div_pos.mpr h1).le
  have hne : Real.sqrt (1 / (n0 * κ)) ≠ 0 := (Real.sqrt_pos.mpr (one_div_pos.mpr h1)).ne'
  rw [div_mul_div_comm, hs, show n0 * κ * Real.sqrt (1 / (n0 * κ)) * (n0 * κ * Real.sqrt (1 / (n0 * κ)))
    = (n0 * κ) ^ 2 * (Real.sqrt (1 / (n0 * κ)) * Real.sqrt (1 / (n0 * κ))) by ring, ht]
  field_simp

/-! ## Stage 1 -/

section Stage1

variable {μ : Measure E} [IsFiniteMeasure μ] {K : E → E → ℝ} {φ : E → ℝ} {n0 κ B C : ℝ}
  (h : Hyp μ K φ n0 κ B C)
include h

lemma wA_zero (y : E) : wA μ K φ n0 0 y = A00 n0 κ * A00 n0 κ := by
  unfold wA; rw [A0_eq h y]

lemma wA'_zero (y : E) : wA' μ K φ n0 0 y = 2 * (A00 n0 κ * A00 n0 κ) * aφ μ K κ φ y := by
  unfold wA'; rw [Ad_zero h y, A0_eq h y]; ring

/-- The iterated kernels of `S_0`: `S_0^{(j)} = (A_0²)^{j+1} K^{(j)}`. -/
theorem kpow_S0 (j : ℕ) (x z : E) :
    kpow μ (Sc μ K (nε n0 φ 0)) j x z = (A00 n0 κ * A00 n0 κ) ^ (j + 1) * kpow μ K j x z := by
  rw [kpow_S_eq h 0 j x z, KA_const (wHyp h) 0 _ (wA_zero h) j x z, A0_eq h x, A0_eq h z]; ring

/-- **Stage 1 (off the diagonal).** Closed formula for the derivative of `S_ε^{(j)}(x,z)` at `ε = 0`:
`(a(x)+a(z)) S_0^{(j)}(x,z) + 2 ∑_{i<j} ∫ S_0^{(i)}(x,y) a(y) S_0^{(j−1−i)}(y,z) dμ(y)`. -/
theorem kpow_S_local (j : ℕ) (x z : E) :
    HasDerivAt (fun ε => kpow μ (Sc μ K (nε n0 φ ε)) j x z)
      ((aφ μ K κ φ x + aφ μ K κ φ z) * kpow μ (Sc μ K (nε n0 φ 0)) j x z +
        2 * ∑ i ∈ Finset.range j, ∫ y, kpow μ (Sc μ K (nε n0 φ 0)) i x y * aφ μ K κ φ y *
          kpow μ (Sc μ K (nε n0 φ 0)) (j - 1 - i) y z ∂μ) 0 := by
  convert kpow_S_hasDerivAt h j x z using 1
  have wh := wHyp h
  rw [KA_const wh 0 _ (wA_zero h) j x z, kpow_S0 h j x z]
  cases j with
  | zero =>
    rw [show KD μ K (wA μ K φ n0) (wA' μ K φ n0) 0 0 x z = 0 from rfl]
    simp only [Finset.range_zero, Finset.sum_empty]
    ring
  | succ m =>
    rw [KD_const wh 0 _ (mem_ball_self one_pos) (wA_zero h) m x z]
    have hterm : ∀ i ∈ Finset.range (m + 1),
        ∫ y, kpow μ (Sc μ K (nε n0 φ 0)) i x y * aφ μ K κ φ y *
          kpow μ (Sc μ K (nε n0 φ 0)) (m + 1 - 1 - i) y z ∂μ =
        (A00 n0 κ * A00 n0 κ) ^ (m + 2) *
          ∫ y, kpow μ K i x y * aφ μ K κ φ y * kpow μ K (m - i) y z ∂μ := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [← integral_const_mul]; congr 1; funext y
      rw [kpow_S0 h i x y, kpow_S0 h _ y z, show m + 1 - 1 - i = m - i by omega]
      have : (A00 n0 κ * A00 n0 κ) ^ (m + 2) =
          (A00 n0 κ * A00 n0 κ) ^ (i + 1) * (A00 n0 κ * A00 n0 κ) ^ (m - i + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
    have hterm' : ∀ i ∈ Finset.range (m + 1),
        ∫ y, kpow μ K i x y * wA' μ K φ n0 0 y * kpow μ K (m - i) y z ∂μ =
        2 * (A00 n0 κ * A00 n0 κ) * ∫ y, kpow μ K i x y * aφ μ K κ φ y * kpow μ K (m - i) y z ∂μ := by
      intro i hi
      rw [← integral_const_mul]; congr 1; funext y
      rw [wA'_zero h y]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_congr rfl hterm']
    simp only [← Finset.mul_sum]
    ring

/-- **Stage 1 (diagonal).** `d/dε S_ε^{(j)}(x,x)|₀ = 2a(x) S_0^{(j)}(x,x)
+ 2 ∑_{i<j} ∫ S_0^{(i)}(x,y) a(y) S_0^{(j−1−i)}(y,x) dμ(y)`. -/
theorem kpow_S_diag (j : ℕ) (x : E) :
    HasDerivAt (fun ε => kpow μ (Sc μ K (nε n0 φ ε)) j x x)
      (2 * aφ μ K κ φ x * kpow μ (Sc μ K (nε n0 φ 0)) j x x +
        2 * ∑ i ∈ Finset.range j, ∫ y, kpow μ (Sc μ K (nε n0 φ 0)) i x y * aφ μ K κ φ y *
          kpow μ (Sc μ K (nε n0 φ 0)) (j - 1 - i) y x ∂μ) 0 := by
  convert kpow_S_local h j x x using 1; ring

/-- **Stage 1 (diagonal, in terms of `K` and `κ`).** With `S_0 = K/κ`:
`d/dε S_ε^{(j)}(x,x)|₀ = κ^{−(j+1)} (2a(x) K^{(j)}(x,x) + 2 ∑_{i<j} ∫ K^{(i)}(x,y) a(y) K^{(j−1−i)}(y,x))`. -/
theorem kpow_S_diag_K (j : ℕ) (x : E) :
    HasDerivAt (fun ε => kpow μ (Sc μ K (nε n0 φ ε)) j x x)
      ((1 / κ) ^ (j + 1) * (2 * aφ μ K κ φ x * kpow μ K j x x +
        2 * ∑ i ∈ Finset.range j, ∫ y, kpow μ K i x y * aφ μ K κ φ y *
          kpow μ K (j - 1 - i) y x ∂μ)) 0 := by
  convert kpow_S_diag h j x using 1
  have hc := A00_sq h.n0pos h.κpos
  have hterm : ∀ i ∈ Finset.range j,
      ∫ y, kpow μ (Sc μ K (nε n0 φ 0)) i x y * aφ μ K κ φ y *
        kpow μ (Sc μ K (nε n0 φ 0)) (j - 1 - i) y x ∂μ =
      (1 / κ) ^ (j + 1) * ∫ y, kpow μ K i x y * aφ μ K κ φ y * kpow μ K (j - 1 - i) y x ∂μ := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← integral_const_mul]; congr 1; funext y
    rw [kpow_S0 h i x y, kpow_S0 h _ y x, hc]
    have : (1 / κ) ^ (j + 1) = (1 / κ) ^ (i + 1) * (1 / κ) ^ (j - 1 - i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [this]; ring
  rw [Finset.sum_congr rfl hterm, kpow_S0 h j x x, hc, ← Finset.mul_sum]
  ring

end Stage1

/-! ## Stage 2: convolution kernels on a commutative group -/

section Stage2

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd G] [MeasurableNeg G]
  [MeasurableSub₂ G] (ν : Measure G) [IsFiniteMeasure ν] [ν.IsAddLeftInvariant]
  [ν.IsAddRightInvariant] [ν.IsNegInvariant]

/-- Iterated kernels of a convolution kernel are convolution kernels of the convolution powers. -/
theorem kpow_conv (k : G → ℝ) :
    ∀ i x z, kpow ν (fun x y => k (x - y)) i x z = convPow ν k i (x - z)
  | 0, x, z => rfl
  | i + 1, x, z => by
    have ih : ∀ y, kpow ν (fun x y => k (x - y)) i y z = convPow ν k i (y - z) :=
      fun y => kpow_conv k i y z
    show ∫ y, k (x - y) * kpow ν (fun x y => k (x - y)) i y z ∂ν =
      ∫ w, k (x - z - w) * convPow ν k i w ∂ν
    simp_rw [ih]
    rw [← integral_sub_right_eq_self (μ := ν) (fun w => k (x - z - w) * convPow ν k i w) z]
    congr 1; funext y; simp only [sub_sub_sub_cancel_right]

/-- Convolution powers of an even kernel are even. -/
theorem convPow_even (k : G → ℝ) (hk : ∀ u, k (-u) = k u) :
    ∀ i u, convPow ν k i (-u) = convPow ν k i u
  | 0, u => hk u
  | i + 1, u => by
    have ih : ∀ w, convPow ν k i (-w) = convPow ν k i w := fun w => convPow_even k hk i w
    show ∫ w, k (-u - w) * convPow ν k i w ∂ν = ∫ w, k (u - w) * convPow ν k i w ∂ν
    rw [← integral_neg_eq_self (fun w => k (-u - w) * convPow ν k i w) ν]
    congr 1; funext w
    rw [ih w, sub_neg_eq_add, ← hk (u - w), neg_sub, neg_add_eq_sub]

lemma convPow_eq_kpow (k : G → ℝ) (i : ℕ) (u : G) :
    convPow ν k i u = kpow ν (fun x y => k (x - y)) i u 0 := by
  rw [kpow_conv, sub_zero]

lemma convPow_meas {k : G → ℝ} (hkm : Measurable k) (i : ℕ) : Measurable (convPow ν k i) := by
  have : convPow ν k i = fun u => kpow ν (fun x y => k (x - y)) i u 0 :=
    funext fun u => convPow_eq_kpow ν k i u
  rw [this]
  exact (kpow_meas ν (K := fun x y => k (x - y)) (hkm.comp measurable_sub) i).comp
    (measurable_id.prodMk measurable_const)

lemma convPow_bdd {k : G → ℝ} {B : ℝ} (hkB : ∀ u, |k u| ≤ B) (i : ℕ) (u : G) :
    |convPow ν k i u| ≤ kB ν B i := by
  rw [convPow_eq_kpow]
  exact kpow_bdd ν (K := fun x y => k (x - y)) (fun x y => hkB _) i u 0

/-- **Stage 2.** Convolution kernel `K(x,y) = k(x−y)` (`k` measurable, even, `0 ≤ k ≤ B`, `κ = ∫k > 0`),
density `n_ε = n₀ e^{εc}`, `c` a cosine-type mode with `c(x−u) = c(x)c(u) + s(x)s(u)`, `s` odd, `c, s`
measurable and bounded.  Then, with `γ = (∫ k c)/κ`,
`d/dε S_ε^{(j)}(x,x)|₀ = (1−γ)² κ^{−(j+1)} (k^{*(j+1)}(0) + ∑_{i<j} ∫ k^{*(i+1)} k^{*(j−i)} c) · c(x)`. -/
theorem kpow_diag_conv (k c s : G → ℝ) (n0 B C : ℝ) (hkm : Measurable k) (hk0 : ∀ u, 0 ≤ k u)
    (hkB : ∀ u, k u ≤ B) (hB : 0 ≤ B) (hcm : Measurable c) (hcC : ∀ y, |c y| ≤ C) (hC : 0 ≤ C)
    (hsm : Measurable s) (hsC : ∀ y, |s y| ≤ C) (hn0 : 0 < n0) (hκ : 0 < ∫ u, k u ∂ν)
    (hk : ∀ u, k (-u) = k u) (hs : ∀ u, s (-u) = -s u)
    (hadd : ∀ x u, c (x - u) = c x * c u + s x * s u) (j : ℕ) (x : G) :
    HasDerivAt (fun ε => kpow ν (Sc ν (fun x y => k (x - y)) (nε n0 c ε)) j x x)
      ((1 - (∫ u, k u * c u ∂ν) / (∫ u, k u ∂ν)) ^ 2 * (1 / ∫ u, k u ∂ν) ^ (j + 1) *
        (convPow ν k j 0 + ∑ i ∈ Finset.range j,
          ∫ u, convPow ν k i u * convPow ν k (j - 1 - i) u * c u ∂ν) * c x) 0 := by
  set κ := ∫ u, k u ∂ν with hκdef
  set γ := (∫ u, k u * c u ∂ν) / κ with hγdef
  have h : Hyp ν (fun x y => k (x - y)) c n0 κ B C :=
    { Km := hkm.comp measurable_sub
      K0 := fun x y => hk0 _
      KB := fun x y => hkB _
      φm := hcm
      φC := hcC
      C0 := hC
      B0 := hB
      n0pos := hn0
      κhom := fun x => conv_homogeneous ν k x
      κpos := hκ }
  have hkB' : ∀ u, |k u| ≤ B := fun u => by rw [abs_of_nonneg (hk0 u)]; exact hkB u
  have hkc : Integrable (fun u => k u * c u) ν := by
    refine Integrable.of_bound (hkm.mul hcm).aestronglyMeasurable (B * C) (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hkB' u) (hcC u) (abs_nonneg _) hB
  have hks : Integrable (fun u => k u * s u) ν := by
    refine Integrable.of_bound (hkm.mul hsm).aestronglyMeasurable (B * C) (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hkB' u) (hsC u) (abs_nonneg _) hB
  have hG : ∀ y, Gc ν (fun x y => k (x - y)) κ c y = γ * c y := by
    intro y
    show (∫ z, k (y - z) * c z ∂ν) / κ = _
    rw [conv_cos_eigen ν k c s hk hs hadd hkc hks y, hγdef]; ring
  have hG2 : ∀ y, Gc ν (fun x y => k (x - y)) κ (Gc ν (fun x y => k (x - y)) κ c) y =
      γ * (γ * c y) := by
    intro y
    have e : Gc ν (fun x y => k (x - y)) κ c = fun z => γ * c z := funext hG
    rw [e]
    show (∫ z, k (y - z) * (γ * c z) ∂ν) / κ = _
    have : ∫ z, k (y - z) * (γ * c z) ∂ν = γ * ∫ z, k (y - z) * c z ∂ν := by
      rw [← integral_const_mul]; congr 1; funext z; ring
    rw [this, mul_div_assoc]
    rw [show (∫ z, k (y - z) * c z ∂ν) / κ = Gc ν (fun x y => k (x - y)) κ c y from rfl, hG y]
  have ha : ∀ y, aφ ν (fun x y => k (x - y)) κ c y = (1 - γ) ^ 2 / 2 * c y := by
    intro y; unfold aφ; rw [hG y, hG2 y]; ring
  have hkp : ∀ i x y, kpow ν (Sc ν (fun x y => k (x - y)) (nε n0 c 0)) i x y =
      (1 / κ) ^ (i + 1) * convPow ν k i (x - y) := by
    intro i x y; rw [kpow_S0 h, A00_sq hn0 hκ, kpow_conv]
  convert kpow_S_diag h j x using 1
  have hint : ∀ i ∈ Finset.range j,
      ∫ y, kpow ν (Sc ν (fun x y => k (x - y)) (nε n0 c 0)) i x y *
        aφ ν (fun x y => k (x - y)) κ c y *
        kpow ν (Sc ν (fun x y => k (x - y)) (nε n0 c 0)) (j - 1 - i) y x ∂ν =
      ((1 / κ) ^ (j + 1) * ((1 - γ) ^ 2 / 2) * c x) *
        ∫ u, convPow ν k i u * convPow ν k (j - 1 - i) u * c u ∂ν := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hFe : ∀ u, (fun u => convPow ν k i u * convPow ν k (j - 1 - i) u) (-u) =
        (fun u => convPow ν k i u * convPow ν k (j - 1 - i) u) u := fun u => by
      simp only [convPow_even ν k hk]
    have hFm : Measurable (fun u => convPow ν k i u * convPow ν k (j - 1 - i) u) :=
      (convPow_meas ν hkm i).mul (convPow_meas ν hkm _)
    have hFb : ∀ u, |convPow ν k i u * convPow ν k (j - 1 - i) u| ≤
        kB ν B i * kB ν B (j - 1 - i) := fun u => by
      rw [abs_mul]
      exact mul_le_mul (convPow_bdd ν hkB' i u) (convPow_bdd ν hkB' _ u) (abs_nonneg _)
        ((abs_nonneg _).trans (convPow_bdd ν hkB' i u))
    have hFc : Integrable (fun u => convPow ν k i u * convPow ν k (j - 1 - i) u * c u) ν := by
      refine Integrable.of_bound (hFm.mul hcm).aestronglyMeasurable (kB ν B i * kB ν B (j - 1 - i) * C) (ae_of_all _ fun u => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb u) (hcC u) (abs_nonneg _) ((abs_nonneg _).trans (hFb u))
    have hFs : Integrable (fun u => convPow ν k i u * convPow ν k (j - 1 - i) u * s u) ν := by
      refine Integrable.of_bound (hFm.mul hsm).aestronglyMeasurable (kB ν B i * kB ν B (j - 1 - i) * C) (ae_of_all _ fun u => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFb u) (hsC u) (abs_nonneg _) ((abs_nonneg _).trans (hFb u))
    have hF := conv_cos_eigen ν (fun u => convPow ν k i u * convPow ν k (j - 1 - i) u) c s hFe hs hadd
      hFc hFs x
    have hpow : (1 / κ) ^ (j + 1) = (1 / κ) ^ (i + 1) * (1 / κ) ^ (j - 1 - i + 1) := by
      rw [← pow_add]; congr 1; omega
    beta_reduce at hF
    rw [show ((1 / κ) ^ (j + 1) * ((1 - γ) ^ 2 / 2) * c x) *
        (∫ u, convPow ν k i u * convPow ν k (j - 1 - i) u * c u ∂ν) =
        ((1 / κ) ^ (j + 1) * ((1 - γ) ^ 2 / 2)) *
        ((∫ u, convPow ν k i u * convPow ν k (j - 1 - i) u * c u ∂ν) * c x) by ring,
      ← hF, ← integral_const_mul]
    congr 1; funext y
    rw [hkp, hkp, ha y, ← neg_sub x y, convPow_even ν k hk _ (x - y), hpow]
    ring
  rw [hkp j x x, sub_self, ha x, Finset.sum_congr rfl hint, ← Finset.mul_sum]
  ring

end Stage2


/-! ## Stage 3: the flat torus with the heat kernel -/

section Stage3

open CTG.Reals

/-- `e^{-c|n|²}`, the Fourier coefficients of `heatTorus d c`. -/
noncomputable def ga {d : ℕ} (c : ℝ) (n : Fin d → ℤ) : ℝ := Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)

lemma ga_neg {d : ℕ} (c : ℝ) (n : Fin d → ℤ) : ga c (-n) = ga c n := by
  unfold ga; simp

lemma ga_nonneg {d : ℕ} (c : ℝ) (n : Fin d → ℤ) : 0 ≤ ga c n := (Real.exp_pos _).le

lemma ga_le_one {d : ℕ} {c : ℝ} (hc : 0 ≤ c) (n : Fin d → ℤ) : ga c n ≤ 1 := by
  unfold ga
  apply Real.exp_le_one_iff.mpr
  have : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

lemma ga_summable {c : ℝ} (hc : 0 < c) (d : ℕ) : Summable fun n : Fin d → ℤ => |ga c n| := by
  simpa [ga, abs_of_pos (Real.exp_pos _)] using gauss_summable hc d

lemma heatTorus_eq_cos (d : ℕ) (c : ℝ) : heatTorus d c = cosSeries d (ga c) := rfl

lemma torusChar_neg_arg' (d : ℕ) (n : Fin d → ℤ) (u : FlatTorus d) :
    torusChar d n (-u) = (starRingEnd ℂ) (torusChar d n u) := by
  have h1 : torusChar d n (-u) * torusChar d n u = 1 := by
    rw [← torusChar_add, neg_add_cancel]; simp [torusChar]
  have h2 : torusChar d n u * (starRingEnd ℂ) (torusChar d n u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, torusChar_norm]; simp
  have hne : torusChar d n u ≠ 0 := by
    intro h; have := torusChar_norm d n u; rw [h, norm_zero] at this; norm_num at this
  have : torusChar d n (-u) * torusChar d n u
      = (starRingEnd ℂ) (torusChar d n u) * torusChar d n u := by rw [h1, mul_comm, h2]
  exact mul_right_cancel₀ hne this

lemma torusChar_im_neg' (d : ℕ) (n : Fin d → ℤ) (u : FlatTorus d) :
    (torusChar d n (-u)).im = -(torusChar d n u).im := by
  rw [torusChar_neg_arg']; simp

/-- `Re χ_m Re χ_n = (Re χ_{m+n} + Re χ_{m−n})/2`. -/
lemma re_mul_re (d : ℕ) (m n : Fin d → ℤ) (x : FlatTorus d) :
    (torusChar d m x).re * (torusChar d n x).re =
      ((torusChar d (m + n) x).re + (torusChar d (m - n) x).re) / 2 := by
  rw [sub_eq_add_neg, torusChar_add_freq, torusChar_add_freq, torusChar_neg_freq]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Fourier coefficient of the heat kernel: `∫ p_c Re χ_n = e^{-c|n|²}`. -/
lemma heat_coeff' {c : ℝ} (hc : 0 < c) (d : ℕ) (n : Fin d → ℤ) :
    ∫ u, heatTorus d c u * (torusChar d n u).re ∂flatTorusMeasure d = ga c n := by
  have h := (cosSeries_coeff d (ga c) (ga_summable hc d) (fun m => ga_neg c m) n).1
  rw [← h, heatTorus_eq_cos]
  congr 1; funext u; ring

lemma heat_re_integrable {c : ℝ} (hc : 0 < c) (d : ℕ) (n : Fin d → ℤ) :
    Integrable (fun u => heatTorus d c u * (torusChar d n u).re) (flatTorusMeasure d) :=
  ((heatTorus_continuous hc d).mul (Complex.continuous_re.comp (torusChar_continuous d n))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- **Product of two heat kernels against a cosine mode:**
`∫ p_{c₁} p_{c₂} Re χ_n = ∑_m e^{-c₁|m|²} e^{-c₂|m+n|²}`. -/
theorem heat_prod {c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2) (d : ℕ) (n : Fin d → ℤ) :
    ∫ u, heatTorus d c1 u * heatTorus d c2 u * (torusChar d n u).re ∂flatTorusMeasure d =
      ∑' m, ga c1 m * ga c2 (m + n) := by
  have hCm : ∀ k : Fin d → ℤ, Measurable fun x : FlatTorus d => (torusChar d k x).re := fun k =>
    (Complex.continuous_re.comp (torusChar_continuous d k)).measurable
  have hCb : ∀ (k : Fin d → ℤ) (x : FlatTorus d), |(torusChar d k x).re| ≤ 1 := fun k x =>
    (Complex.abs_re_le_norm _).trans (torusChar_norm d k x).le
  have hq : ∀ z, |heatTorus d c2 z * (torusChar d n z).re| ≤ (1 + Real.sqrt (Real.pi / c2)) ^ d := by
    intro z
    rw [abs_mul, abs_of_nonneg (heatTorus_nonneg hc2 d z)]
    have := heatTorus_le hc2 d z
    calc heatTorus d c2 z * |(torusChar d n z).re| ≤ heatTorus d c2 z * 1 :=
          mul_le_mul_of_nonneg_left (hCb n z) (heatTorus_nonneg hc2 d z)
      _ ≤ _ := by rw [mul_one]; exact this
  have h := series_kernel_integral (flatTorusMeasure d) (ga c1) (ga_summable hc1 d)
    (fun m z => (torusChar d m z).re) hCm hCb (fun z => heatTorus d c2 z * (torusChar d n z).re)
    ((heatTorus_continuous hc2 d).measurable.mul (hCm n)) hq
  have e : (fun u => heatTorus d c1 u * heatTorus d c2 u * (torusChar d n u).re) =
      fun u => (∑' m, ga c1 m * (torusChar d m u).re) * (heatTorus d c2 u * (torusChar d n u).re) := by
    funext u; rw [mul_assoc]; rfl
  rw [e, h]
  have hterm : ∀ m : Fin d → ℤ,
      ga c1 m * ∫ z, (torusChar d m z).re * (heatTorus d c2 z * (torusChar d n z).re)
        ∂flatTorusMeasure d = (ga c1 m * ga c2 (m + n) + ga c1 m * ga c2 (m - n)) / 2 := by
    intro m
    have e2 : (fun z => (torusChar d m z).re * (heatTorus d c2 z * (torusChar d n z).re)) =
        fun z => (heatTorus d c2 z * (torusChar d (m + n) z).re +
          heatTorus d c2 z * (torusChar d (m - n) z).re) / 2 := by
      funext z
      rw [show (torusChar d m z).re * (heatTorus d c2 z * (torusChar d n z).re) =
        heatTorus d c2 z * ((torusChar d m z).re * (torusChar d n z).re) by ring, re_mul_re]
      ring
    rw [e2, integral_div, integral_add (heat_re_integrable hc2 d _) (heat_re_integrable hc2 d _),
      heat_coeff' hc2, heat_coeff' hc2]
    ring
  have hf : Summable fun m : Fin d → ℤ => ga c1 m * ga c2 (m + n) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (ga_nonneg _ _) (ga_nonneg _ _))
      (fun m => by
        have := ga_le_one hc2.le (m + n)
        have := ga_nonneg c1 m
        nlinarith)
      ((ga_summable hc1 d).congr fun m => abs_of_nonneg (ga_nonneg _ _))
  have hg : Summable fun m : Fin d → ℤ => ga c1 m * ga c2 (m - n) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (ga_nonneg _ _) (ga_nonneg _ _))
      (fun m => by
        have := ga_le_one hc2.le (m - n)
        have := ga_nonneg c1 m
        nlinarith)
      ((ga_summable hc1 d).congr fun m => abs_of_nonneg (ga_nonneg _ _))
  have hfg : ∑' m, ga c1 m * ga c2 (m - n) = ∑' m, ga c1 m * ga c2 (m + n) := by
    rw [← (Equiv.neg (Fin d → ℤ)).tsum_eq]
    refine tsum_congr fun m => ?_
    simp only [Equiv.neg_apply]
    rw [ga_neg, show -m - n = -(m + n) by abel, ga_neg]
  rw [tsum_congr hterm, tsum_div_const, Summable.tsum_add hf hg, hfg]
  ring

/-- **Stage 3 (torus).** Kernel `heatTorus d c` (`c > 0`) on the flat torus, density
`n_ε = n₀ e^{ε Re χ_n}`: at `ε = 0`,
`d/dε S_ε^{(j)}(x,x) = (1 − e^{-c|n|²})² ( ∑_m e^{-(j+1)c|m|²}
  + ∑_{i<j} ∑_m e^{-(i+1)c|m|²} e^{-(j−i)c|m+n|²} ) · Re χ_n(x)`.
No hypothesis beyond `c > 0`, `n₀ > 0`. -/
theorem kpow_diag_torus {c : ℝ} (hc : 0 < c) (d : ℕ) (n : Fin d → ℤ) {n0 : ℝ} (hn0 : 0 < n0)
    (j : ℕ) (x : FlatTorus d) :
    HasDerivAt (fun ε => kpow (flatTorusMeasure d)
        (Sc (flatTorusMeasure d) (fun x y => heatTorus d c (x - y))
          (nε n0 (fun y => (torusChar d n y).re) ε)) j x x)
      ((1 - ga c n) ^ 2 * ((∑' m : Fin d → ℤ, ga (((j + 1 : ℕ) : ℝ) * c) m) +
        ∑ i ∈ Finset.range j, ∑' m, ga (((i + 1 : ℕ) : ℝ) * c) m * ga (((j - i : ℕ) : ℝ) * c) (m + n))
        * (torusChar d n x).re) 0 := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have hcm : Measurable fun y : FlatTorus d => (torusChar d n y).re :=
    (Complex.continuous_re.comp (torusChar_continuous d n)).measurable
  have hsm : Measurable fun y : FlatTorus d => (torusChar d n y).im :=
    (Complex.continuous_im.comp (torusChar_continuous d n)).measurable
  have h := kpow_diag_conv (flatTorusMeasure d) (heatTorus d c) (fun y => (torusChar d n y).re)
    (fun y => (torusChar d n y).im) n0 ((1 + Real.sqrt (Real.pi / c)) ^ d) 1
    (heatTorus_continuous hc d).measurable (fun u => heatTorus_nonneg hc d u)
    (fun u => heatTorus_le hc d u) (by positivity) hcm
    (fun y => (Complex.abs_re_le_norm _).trans (torusChar_norm d n y).le) zero_le_one hsm
    (fun y => (Complex.abs_im_le_norm _).trans (torusChar_norm d n y).le) hn0
    (by rw [heatTorus_mass hc]; exact one_pos)
    (fun u => heatTorus_even d c u) (fun u => torusChar_im_neg' d n u)
    (fun x u => torusChar_sub_re d n x u) j x
  rw [heatTorus_mass hc, heat_coeff' hc] at h
  convert h using 1
  have hcp : ∀ i, convPow (flatTorusMeasure d) (heatTorus d c) i =
      heatTorus d (((i + 1 : ℕ) : ℝ) * c) := fun i => (heatTorus_convPow hc d i).1
  simp_rw [hcp]
  have hint : ∀ i ∈ Finset.range j,
      ∫ u, heatTorus d (((i + 1 : ℕ) : ℝ) * c) u * heatTorus d (((j - 1 - i + 1 : ℕ) : ℝ) * c) u *
        (torusChar d n u).re ∂flatTorusMeasure d =
      ∑' m, ga (((i + 1 : ℕ) : ℝ) * c) m * ga (((j - i : ℕ) : ℝ) * c) (m + n) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [heat_prod (by positivity) (by positivity), show j - 1 - i + 1 = j - i by omega]
  rw [Finset.sum_congr rfl hint, heatTorus_eq_cos, cosSeries_zero]
  simp only [div_one, one_pow, mul_one]

end Stage3

end CTG.DensityResponseCont.Local
