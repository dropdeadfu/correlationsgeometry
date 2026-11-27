/-
Forty-fifth file: the torus instance of the density response.  Namespace `CTG.DensityResponseTorus`; imports the
second file and the forty-third (compiled modules); check with `./check_density_response_torus.sh`.
For `k = heatTorus d c` on the flat torus `(ℝ/ℤ)^d` with the product Haar measure and the mode `φ = Re χ_n`:
the addition formula (`torus_addition`) and `γ = e^{-c|n|²}` (`heat_coeff`, `heat_gamma`) are PROVED, hence
`d/dε log A_ε(x) |_{ε=0} = ½ (1 − e^{-c|n|²})² Re χ_n(x)` (`hasDerivAt_log_A_torus`), without hypothesis.
With `c = 2π²ξ²`, `a = 2π|n|` the factor is `½ (1 − e^{-ξ²a²/2})²` (`hasDerivAt_log_A_torus_xi`), and
`0 ≤ ½ (1 − e^{-ξ²a²/2})² ≤ (aξ)⁴/8` (`density_factor_fourth_order`).
NOT formalised: remainders of second order in the density, derivatives of iterated kernels and traces, the summation
with `1 − √(1−s)`, the coefficient `c(a)` and its limit; the sine mode `Im χ_n`; `heatTorus` is the kernel in Fourier
form (its identification with the periodised Gaussian is `heatTorus_eq_prod` of the second file, not used here).
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryReal
import CorrelationsToGeometryDensityResponseCont

set_option linter.unusedVariables false

open MeasureTheory

namespace CTG.DensityResponseTorus

open CTG.Reals

/-- `|n|² = ∑ n_i²`. -/
noncomputable def nsq {d : ℕ} (n : Fin d → ℤ) : ℝ := ∑ i, ((n i : ℤ) : ℝ) ^ 2

lemma nsq_nonneg {d : ℕ} (n : Fin d → ℤ) : 0 ≤ nsq n :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

/-- `χ_n(-u) = conj χ_n(u)`. -/
lemma torusChar_neg_arg (d : ℕ) (n : Fin d → ℤ) (u : FlatTorus d) :
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

/-- The sine part is odd. -/
lemma torusChar_im_neg (d : ℕ) (n : Fin d → ℤ) (u : FlatTorus d) :
    (torusChar d n (-u)).im = -(torusChar d n u).im := by
  rw [torusChar_neg_arg]; simp

/-- **The addition formula, proved:** `Re χ_n(x−u) = Re χ_n(x) Re χ_n(u) + Im χ_n(x) Im χ_n(u)`. -/
theorem torus_addition (d : ℕ) (n : Fin d → ℤ) (x u : FlatTorus d) :
    (torusChar d n (x - u)).re
      = (torusChar d n x).re * (torusChar d n u).re + (torusChar d n x).im * (torusChar d n u).im :=
  torusChar_sub_re d n x u

lemma gauss_abs_summable {c : ℝ} (hc : 0 < c) (d : ℕ) :
    Summable fun n : Fin d → ℤ => |Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := by
  simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc d

/-- **The Fourier coefficient of the heat kernel:** `∫ k · Re χ_n = e^{-c|n|²}`. -/
theorem heat_coeff {c : ℝ} (hc : 0 < c) (d : ℕ) (n : Fin d → ℤ) :
    ∫ u, heatTorus d c u * (torusChar d n u).re ∂flatTorusMeasure d = Real.exp (-c * nsq n) := by
  have h := (cosSeries_coeff d (fun n => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2))
    (gauss_abs_summable hc d) (fun m => by simp) n).1
  unfold heatTorus nsq
  rw [← h]
  congr 1; funext u; ring

/-- **The eigenvalue, proved:** `γ = (∫ k Re χ_n)/(∫ k) = e^{-c|n|²}`. -/
theorem heat_gamma {c : ℝ} (hc : 0 < c) (d : ℕ) (n : Fin d → ℤ) :
    (∫ u, heatTorus d c u * (torusChar d n u).re ∂flatTorusMeasure d)
      / (∫ u, heatTorus d c u ∂flatTorusMeasure d) = Real.exp (-c * nsq n) := by
  rw [heat_coeff hc, heatTorus_mass hc, div_one]

/-- **Torus instance of the density response.** Kernel `K(x,y) = heatTorus d c (x−y)`, `c > 0`,
density `n_ε = n₀ exp(ε Re χ_n)`, `n₀ > 0`: at `ε = 0`,
`d/dε log A_ε(x) = ½ (1 − e^{-c|n|²})² Re χ_n(x)`.  No hypothesis beyond `c > 0`, `n₀ > 0`. -/
theorem hasDerivAt_log_A_torus {c : ℝ} (hc : 0 < c) (d : ℕ) (n : Fin d → ℤ) {n0 : ℝ} (hn0 : 0 < n0)
    (x : FlatTorus d) :
    HasDerivAt (fun ε => Real.log (CTG.DensityResponseCont.Ac (flatTorusMeasure d)
        (fun x y => heatTorus d c (x - y))
        (CTG.DensityResponseCont.nε n0 (fun y => (torusChar d n y).re) ε) x))
      ((1 - Real.exp (-c * nsq n)) ^ 2 / 2 * (torusChar d n x).re) 0 := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have hcm : Measurable fun y : FlatTorus d => (torusChar d n y).re :=
    (Complex.continuous_re.comp (torusChar_continuous d n)).measurable
  have hsm : Measurable fun y : FlatTorus d => (torusChar d n y).im :=
    (Complex.continuous_im.comp (torusChar_continuous d n)).measurable
  have hkm : Measurable (heatTorus d c) := (heatTorus_continuous hc d).measurable
  have hks : Integrable (fun u => heatTorus d c u * (torusChar d n u).im) (flatTorusMeasure d) := by
    refine Integrable.of_bound (hkm.mul hsm).aestronglyMeasurable
      ((1 + Real.sqrt (Real.pi / c)) ^ d * 1) (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatTorus_nonneg hc d u)]
    exact mul_le_mul (heatTorus_le hc d u)
      ((Complex.abs_im_le_norm _).trans (torusChar_norm d n u).le) (abs_nonneg _) (by positivity)
  have h := CTG.DensityResponseCont.hasDerivAt_log_A_conv (flatTorusMeasure d) (heatTorus d c)
    (fun y => (torusChar d n y).re) (fun y => (torusChar d n y).im) n0
    ((1 + Real.sqrt (Real.pi / c)) ^ d) 1 hkm (fun u => heatTorus_nonneg hc d u)
    (fun u => heatTorus_le hc d u) (by positivity) hcm
    (fun y => (Complex.abs_re_le_norm _).trans (torusChar_norm d n y).le) zero_le_one hn0
    (by rw [heatTorus_mass hc]; exact one_pos)
    (fun u => heatTorus_even d c u) (fun u => torusChar_im_neg d n u)
    (fun x u => torusChar_sub_re d n x u) hks x
  rwa [heat_gamma hc] at h

/-- **The form of the paper.** With `c = 2π²ξ²` (variance `ξ²`) and `a = 2π|n|`, the derivative is
`½ (1 − e^{-ξ²a²/2})² Re χ_n(x)`. -/
theorem hasDerivAt_log_A_torus_xi {ξ : ℝ} (hξ : ξ ≠ 0) (d : ℕ) (n : Fin d → ℤ) {n0 : ℝ}
    (hn0 : 0 < n0) (x : FlatTorus d) :
    HasDerivAt (fun ε => Real.log (CTG.DensityResponseCont.Ac (flatTorusMeasure d)
        (fun x y => heatTorus d (2 * Real.pi ^ 2 * ξ ^ 2) (x - y))
        (CTG.DensityResponseCont.nε n0 (fun y => (torusChar d n y).re) ε) x))
      ((1 - Real.exp (-(ξ ^ 2 * (2 * Real.pi * Real.sqrt (nsq n)) ^ 2 / 2))) ^ 2 / 2
        * (torusChar d n x).re) 0 := by
  have hc : 0 < 2 * Real.pi ^ 2 * ξ ^ 2 := by
    have := pow_pos Real.pi_pos 2; have := pow_pos (abs_pos.mpr hξ) 2
    rw [sq_abs] at this; positivity
  have h := hasDerivAt_log_A_torus hc d n hn0 x
  have e : -(ξ ^ 2 * (2 * Real.pi * Real.sqrt (nsq n)) ^ 2 / 2) = -(2 * Real.pi ^ 2 * ξ ^ 2) * nsq n := by
    rw [mul_pow, Real.sq_sqrt (nsq_nonneg n)]; ring
  rwa [e]

/-- `0 ≤ ½(1 − e^{-t})² ≤ t²/2` for `t ≥ 0`. -/
theorem half_one_sub_exp_sq_le {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (1 - Real.exp (-t)) ^ 2 / 2 ∧ (1 - Real.exp (-t)) ^ 2 / 2 ≤ t ^ 2 / 2 := by
  refine ⟨by positivity, ?_⟩
  have h1 : 1 - t ≤ Real.exp (-t) := by have := Real.add_one_le_exp (-t); linarith
  have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : 0 ≤ 1 - Real.exp (-t) := by linarith
  have h4 : (1 - Real.exp (-t)) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h3 (by linarith) 2
  linarith

/-- **Fourth order:** `½(1 − e^{-ξ²a²/2})² ≤ (aξ)⁴/8`. -/
theorem density_factor_fourth_order (ξ a : ℝ) :
    0 ≤ (1 - Real.exp (-(ξ ^ 2 * a ^ 2 / 2))) ^ 2 / 2 ∧
      (1 - Real.exp (-(ξ ^ 2 * a ^ 2 / 2))) ^ 2 / 2 ≤ (a * ξ) ^ 4 / 8 := by
  have ht : 0 ≤ ξ ^ 2 * a ^ 2 / 2 := by positivity
  obtain ⟨h0, h1⟩ := half_one_sub_exp_sq_le ht
  refine ⟨h0, h1.trans (le_of_eq ?_)⟩
  ring

end CTG.DensityResponseTorus

#print axioms CTG.DensityResponseTorus.hasDerivAt_log_A_torus
#print axioms CTG.DensityResponseTorus.hasDerivAt_log_A_torus_xi
#print axioms CTG.DensityResponseTorus.heat_gamma
#print axioms CTG.DensityResponseTorus.density_factor_fourth_order
