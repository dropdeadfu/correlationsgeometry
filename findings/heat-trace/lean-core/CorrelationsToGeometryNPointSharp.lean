/-
From Correlations to Geometry -- eighteenth Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the fifteenth file `CorrelationsToGeometryNPointGeom.lean` (and with it the twelfth and fourteenth).
REPAIR of the quantitative weakness of the twelfth file found in the sixteenth: Steps 3 to 5 of the proof of
Proposition "dotLN-diff" (Appendix H of the paper) are re-proven with L¹ bounds of the kernels (of order `ξ^d`) in
place of suprema and with a lower bound of order one for the denominator.  Main statements: `step5'`,
`npoint_step5'`, `rate_bounds'`, `npoint_step5_sharp`, and without geometric hypotheses
`npoint_step5_sharp_geom`, `npoint_step5_sharp_geom_log`: on a compact connected Riemannian manifold modelled on
`Fin n → ℝ`, with a time-dependent metric and a sampling law comparable to the n-dimensional Hausdorff measure of
the Riemannian distance, under `92416 Λ¹⁴ · 3 log N ≤ N ξ^n` the difference quotient in the time of the sample
quotient differs from its population counterpart by at most `3 660 000 Λ²⁰ √(3 log N/(N ξ^n))` for all sample
points, outside an event of probability `30/N²`.
NOT the proposition as written: the test function is only bounded (no gain of `ξ` from its smoothness), there is no
normalisation by `c_h ξ²/2`, Step 6 is not formalised, the constants are crude and partly existential, the
reference measure is not identified with the Riemannian volume, the exceptional set is not shown measurable.
Check with `cd lean && ./check_npoint_sharp.sh`.  No `sorry`, no `axiom`, no `native_decide`.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryNPointGeom

open Set MeasureTheory ProbabilityTheory
open CTG.NPoint

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
namespace CTG.NPointSharp

/-- Closed bound for `Σ_k (k+1)^p e^{−βk}`. -/
def serC (p : ℕ) (β : ℝ) : ℝ :=
  (p.factorial : ℝ) * (2 / β) ^ p * Real.exp (β / 2) * (1 - Real.exp (-(β / 2)))⁻¹

theorem term_le (p : ℕ) {β : ℝ} (hβ : 0 < β) (k : ℕ) :
    ((k : ℝ) + 1) ^ p * Real.exp (-β * k)
      ≤ (p.factorial : ℝ) * (2 / β) ^ p * Real.exp (β / 2) * Real.exp (-(β / 2)) ^ k := by
  have hx : 0 ≤ β * ((k : ℝ) + 1) / 2 := by positivity
  have h1 := Real.pow_div_factorial_le_exp _ hx p
  have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  rw [div_le_iff₀ hf] at h1
  have e1 : ((k : ℝ) + 1) ^ p = (2 / β) ^ p * (β * ((k : ℝ) + 1) / 2) ^ p := by
    rw [← mul_pow]; congr 1; field_simp
  have e2 : Real.exp (-(β / 2)) ^ k = Real.exp (k * (-(β / 2))) := (Real.exp_nat_mul _ _).symm
  rw [e2, e1]
  have e3 : Real.exp (β / 2) * Real.exp (k * (-(β / 2))) * Real.exp (β * k)
      = Real.exp (β * ((k : ℝ) + 1) / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hpos : 0 < Real.exp (β * k) := Real.exp_pos _
  have e4 : Real.exp (-β * k) = (Real.exp (β * k))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [e4, ← div_eq_mul_inv, div_le_iff₀ hpos]
  have h2 : (2 / β) ^ p * (β * ((k : ℝ) + 1) / 2) ^ p
      ≤ (2 / β) ^ p * (Real.exp (β * ((k : ℝ) + 1) / 2) * p.factorial) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc (2 / β) ^ p * (β * ((k : ℝ) + 1) / 2) ^ p
      ≤ (2 / β) ^ p * (Real.exp (β * ((k : ℝ) + 1) / 2) * p.factorial) := h2
    _ = (p.factorial : ℝ) * (2 / β) ^ p * (Real.exp (β / 2) * Real.exp (k * (-(β / 2)))
          * Real.exp (β * k)) := by rw [e3]; ring
    _ = _ := by ring

theorem series_le (p : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∑' k : ℕ, ((k : ℝ) + 1) ^ p * Real.exp (-β * k) ≤ serC p β := by
  set r := Real.exp (-(β / 2))
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have hg : Summable (fun k : ℕ => (p.factorial : ℝ) * (2 / β) ^ p * Real.exp (β / 2) * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hf : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ p * Real.exp (-β * k)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) (term_le p hβ) hg
  calc ∑' k : ℕ, ((k : ℝ) + 1) ^ p * Real.exp (-β * k)
      ≤ ∑' k : ℕ, (p.factorial : ℝ) * (2 / β) ^ p * Real.exp (β / 2) * r ^ k :=
        hf.tsum_le_tsum (term_le p hβ) hg
    _ = serC p β := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]; rfl

theorem serC_nonneg (p : ℕ) {β : ℝ} (hβ : 0 < β) : 0 ≤ serC p β := by
  unfold serC
  have : Real.exp (-(β / 2)) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  have : 0 < 1 - Real.exp (-(β / 2)) := by linarith
  positivity

/-- Far term: `e^{−t/ξ} ≤ n! ξⁿ / tⁿ`. -/
theorem far_le (n : ℕ) {t ξ : ℝ} (ht : 0 < t) (hξ : 0 < ξ) :
    Real.exp (-(t / ξ)) ≤ (n.factorial : ℝ) / t ^ n * ξ ^ n := by
  have h1 := Real.pow_div_factorial_le_exp _ (div_pos ht hξ).le n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have key : 1 ≤ (n.factorial : ℝ) / t ^ n * ξ ^ n * Real.exp (t / ξ) := by
    calc (1:ℝ) = (n.factorial : ℝ) / t ^ n * ξ ^ n * ((t / ξ) ^ n / n.factorial) := by
          rw [div_pow]; field_simp
      _ ≤ (n.factorial : ℝ) / t ^ n * ξ ^ n * Real.exp (t / ξ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hprod : Real.exp (-(t / ξ)) * Real.exp (t / ξ) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (t / ξ), Real.exp_pos (-(t / ξ))]

end CTG.NPointSharp

namespace CTG.NPointSharp

/-- `dev` in terms of `δ` with `δ² N x = L`: `dev ≤ 6 B x δ² + 2 δ √(v x)`. -/
theorem dev_le (N : ℕ) (hN : 0 < N) {B v L x δ : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v) (hL : 1 ≤ L)
    (hx : 0 < x) (hδ0 : 0 ≤ δ) (hδ : δ ^ 2 * (N * x) = L) :
    dev N B v L ≤ 6 * B * x * δ ^ 2 + 2 * δ * Real.sqrt (v * x) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N * v * L) = N * δ * Real.sqrt (v * x) := by
    have e : (N : ℝ) * v * L = (N * δ) ^ 2 * (v * x) := by rw [← hδ]; ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  unfold dev
  rw [hs, div_le_iff₀ hN']
  have h1 : 2 * B ≤ 2 * B * L := by nlinarith
  have e2 : 6 * B * x * δ ^ 2 * N = 6 * B * L := by rw [← hδ]; ring
  nlinarith [e2]

/-- `dev` with upper bounds `B ≤ B'`, `v x ≤ s²`. -/
theorem dev_le' (N : ℕ) (hN : 0 < N) {B v L x δ B' s : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v)
    (hL : 1 ≤ L) (hx : 0 < x) (hδ0 : 0 ≤ δ) (hδ : δ ^ 2 * (N * x) = L) (hBB : B ≤ B')
    (hs0 : 0 ≤ s) (hvs : v * x ≤ s ^ 2) :
    dev N B v L ≤ 6 * B' * x * δ ^ 2 + 2 * δ * s := by
  have h := dev_le N hN hB hv hL hx hδ0 hδ
  have h2 : Real.sqrt (v * x) ≤ s := by
    calc Real.sqrt (v * x) ≤ Real.sqrt (s ^ 2) := Real.sqrt_le_sqrt hvs
      _ = s := Real.sqrt_sq hs0
  have h3 : 6 * B * x * δ ^ 2 ≤ 6 * B' * x * δ ^ 2 := by
    have : 0 ≤ x * δ ^ 2 := by positivity
    nlinarith
  have h4 : 2 * δ * Real.sqrt (v * x) ≤ 2 * δ * s := by nlinarith
  linarith

end CTG.NPointSharp

namespace CTG.NPointSharp

/-- Common arithmetic context: `Λ ≥ 1`, `0 < x ≤ 1`, `x y = 1`, `0 ≤ δ ≤ 1`, `δ² N x = L ≥ 1`. -/
structure Ctx (N : ℕ) (Λ x y δ L : ℝ) : Prop where
  hN : 0 < N
  hΛ : 1 ≤ Λ
  hx : 0 < x
  hx1 : x ≤ 1
  hxy : x * y = 1
  hδ0 : 0 ≤ δ
  hδ1 : δ ≤ 1
  hδ : δ ^ 2 * (N * x) = L
  hL : 1 ≤ L

namespace Ctx

variable {N : ℕ} {Λ x y δ L : ℝ}

theorem y_pos (C : Ctx N Λ x y δ L) : 0 < y := by
  have := C.hxy; have := C.hx
  by_contra h; push_neg at h; nlinarith

theorem y1 (C : Ctx N Λ x y δ L) : 1 ≤ y := by
  have := C.hxy; have := C.hx1; have := C.y_pos; nlinarith

theorem Λ0 (C : Ctx N Λ x y δ L) : 0 ≤ Λ := by linarith [C.hΛ]

/-- Monomials: `Λ^i y^j δ ≤ Λ^k y^l δ` for `i ≤ k`, `j ≤ l`. -/
theorem mono (C : Ctx N Λ x y δ L) {i j k l : ℕ} (hik : i ≤ k) (hjl : j ≤ l) :
    Λ ^ i * y ^ j * δ ≤ Λ ^ k * y ^ l * δ := by
  have h1 : Λ ^ i ≤ Λ ^ k := pow_le_pow_right₀ C.hΛ hik
  have h2 : y ^ j ≤ y ^ l := pow_le_pow_right₀ C.y1 hjl
  have := C.hδ0; have := C.Λ0; have := C.y_pos
  gcongr

theorem mono0 (C : Ctx N Λ x y δ L) {i j k l : ℕ} (hik : i ≤ k) (hjl : j ≤ l) :
    Λ ^ i * y ^ j ≤ Λ ^ k * y ^ l := by
  have := C.Λ0; have := C.y_pos
  exact mul_le_mul (pow_le_pow_right₀ C.hΛ hik) (pow_le_pow_right₀ C.y1 hjl) (by positivity)
    (by positivity)

/-- `dev` for kernel-type arguments: `B ≤ Λ`, `v ≤ Λ² x` ⇒ `dev ≤ 8 Λ x δ`. -/
theorem dev_K (C : Ctx N Λ x y δ L) {B v : ℝ} (hB : 0 ≤ B) (hB' : B ≤ Λ) (hv : 0 ≤ v)
    (hv' : v ≤ Λ ^ 2 * x) : dev N B v L ≤ 8 * Λ * x * δ := by
  have hx := C.hx
  have hvs : v * x ≤ (Λ * x) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hv' hx.le]
  have h := dev_le' N C.hN hB hv C.hL C.hx C.hδ0 C.hδ hB' (mul_nonneg C.Λ0 hx.le) hvs
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [C.hδ0, C.hδ1]
  have := mul_le_mul_of_nonneg_left hδ2 (mul_nonneg C.Λ0 hx.le)
  nlinarith

theorem err1_le (C : Ctx N Λ x y δ L) {A vK c : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ) (hv : 0 ≤ vK)
    (hv' : vK ≤ Λ ^ 2 * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y) :
    err1 N A vK c L ≤ 16 * Λ ^ 3 * y * δ := by
  unfold err1
  have hd := C.dev_K hA hA' hv hv'
  have hd0 := dev_nonneg N hA hv (by linarith [C.hL] : (0:ℝ) ≤ L)
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have e : 2 * (dev N A vK L / c) / c = 2 * (dev N A vK L * c⁻¹ ^ 2) := by ring
  rw [e]
  have := C.Λ0; have := C.hx; have := C.hδ0; have := C.y_pos
  calc 2 * (dev N A vK L * c⁻¹ ^ 2) ≤ 2 * ((8 * Λ * x * δ) * (Λ * y) ^ 2) := by gcongr
    _ = 16 * Λ ^ 3 * y * δ := by linear_combination (16 * Λ ^ 3 * y * δ) * C.hxy

end Ctx

end CTG.NPointSharp

namespace CTG.NPointSharp

/-- Constant of the closed bound `vKern ≤ C_v ξⁿ`. -/
def cV (n : ℕ) (Am r₀ A : ℝ) : ℝ := A ^ 2 * (Am * serC n 2 + (n.factorial : ℝ) / r₀ ^ n)

/-- Constant of the closed bound `vInc ≤ C_v' ξⁿ`. -/
def cV' (κ : ℝ) (n : ℕ) (Am r₀ A : ℝ) : ℝ :=
  4 * κ ^ 2 * A ^ 2 * (Am * serC (n + 2) (2 * Real.exp (-1))
    + 2 * (2 / (2 * Real.exp (-1))) ^ 2 * ((n.factorial : ℝ) / (Real.exp (-1) * r₀) ^ n))

theorem cV_nonneg (n : ℕ) {Am r₀ A : ℝ} (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) : 0 ≤ cV n Am r₀ A := by
  unfold cV; have := serC_nonneg n (two_pos : (0:ℝ) < 2); positivity

theorem cV'_nonneg (κ : ℝ) (n : ℕ) {Am r₀ A : ℝ} (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) :
    0 ≤ cV' κ n Am r₀ A := by
  unfold cV'
  have := serC_nonneg (n + 2) (by positivity : (0:ℝ) < 2 * Real.exp (-1)); positivity

/-- **(1a) Closed bound for the kernel variance proxy**: `vKern ≤ C_v ξⁿ` for every `ξ > 0`. -/
theorem vKern_le (n : ℕ) {Am r₀ ξ A : ℝ} (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ) :
    vKern n Am r₀ ξ A ≤ cV n Am r₀ A * ξ ^ n := by
  unfold vKern cV
  have e1 : (∑' k : ℕ, A ^ 2 * (((k : ℝ) + 1) ^ 0 * Real.exp (-2 * k)) * ((k : ℝ) + 1) ^ n)
      = A ^ 2 * ∑' k : ℕ, ((k : ℝ) + 1) ^ n * Real.exp (-2 * k) := by
    rw [← tsum_mul_left]; congr 1; funext k; ring
  have e2 : Real.exp (-2 * (r₀ / ξ) / 2) = Real.exp (-(r₀ / ξ)) := by congr 1; ring
  rw [e1, e2]
  have hs := series_le n (two_pos : (0:ℝ) < 2)
  have hf := far_le n hr₀ hξ
  have h1 : Am * (A ^ 2 * ∑' k : ℕ, ((k : ℝ) + 1) ^ n * Real.exp (-2 * k)) * ξ ^ n
      ≤ Am * (A ^ 2 * serC n 2) * ξ ^ n := by gcongr
  have h2 : A ^ 2 * (((0 : ℕ).factorial : ℝ) * (2 / 2) ^ 0 * Real.exp (-(r₀ / ξ)))
      ≤ A ^ 2 * ((n.factorial : ℝ) / r₀ ^ n * ξ ^ n) := by
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul]; gcongr
  calc _ ≤ Am * (A ^ 2 * serC n 2) * ξ ^ n + A ^ 2 * ((n.factorial : ℝ) / r₀ ^ n * ξ ^ n) :=
        add_le_add h1 h2
    _ = _ := by ring

/-- **(1b) Closed bound for the increment variance proxy**: `vInc ≤ C_v' ξⁿ` (`b ≠ a`). -/
theorem vInc_le (κ : ℝ) (n : ℕ) {Am r₀ ξ A a b : ℝ} (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hne : b ≠ a) : vInc κ n Am r₀ ξ A a b ≤ cV' κ n Am r₀ A * ξ ^ n := by
  unfold vInc cV'
  set W := (2 * (κ * |b - a|) * A) ^ 2 with hW
  set β := 2 * Real.exp (-1) with hβ
  have hβ0 : 0 < β := by positivity
  have e1 : (∑' k : ℕ, W * (((k : ℝ) + 1) ^ 2 * Real.exp (-β * k)) * ((k : ℝ) + 1) ^ n)
      = W * ∑' k : ℕ, ((k : ℝ) + 1) ^ (n + 2) * Real.exp (-β * k) := by
    rw [← tsum_mul_left]; congr 1; funext k; ring
  have e2 : Real.exp (-β * (r₀ / ξ) / 2) = Real.exp (-(Real.exp (-1) * r₀ / ξ)) := by
    congr 1; rw [hβ]; ring
  rw [e1, e2]
  have hba : (b - a) ≠ 0 := sub_ne_zero.2 hne
  have hW' : W = 4 * κ ^ 2 * A ^ 2 * (b - a) ^ 2 := by rw [hW, mul_pow, mul_pow, mul_pow, sq_abs]; ring
  set S := ∑' k : ℕ, ((k : ℝ) + 1) ^ (n + 2) * Real.exp (-β * k)
  set E := Real.exp (-(Real.exp (-1) * r₀ / ξ))
  have e3 : (Am * (W * S) * ξ ^ n + W * (((2 : ℕ).factorial : ℝ) * (2 / β) ^ 2 * E)) / (b - a) ^ 2
      = 4 * κ ^ 2 * A ^ 2 * (Am * S * ξ ^ n + 2 * (2 / β) ^ 2 * E) := by
    have hf2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
    have e4 : Am * (W * S) * ξ ^ n + W * (((2 : ℕ).factorial : ℝ) * (2 / β) ^ 2 * E)
        = (b - a) ^ 2 * (4 * κ ^ 2 * A ^ 2 * (Am * S * ξ ^ n + 2 * (2 / β) ^ 2 * E)) := by
      rw [hW', hf2]; ring
    rw [e4, mul_div_cancel_left₀ _ (pow_ne_zero 2 hba)]
  rw [e3]
  have hs : S ≤ serC (n + 2) β := series_le (n + 2) hβ0
  have hf : E ≤ (n.factorial : ℝ) / (Real.exp (-1) * r₀) ^ n * ξ ^ n :=
    far_le n (by positivity) hξ
  have h0 : 0 ≤ 4 * κ ^ 2 * A ^ 2 := by positivity
  calc 4 * κ ^ 2 * A ^ 2 * (Am * S * ξ ^ n + 2 * (2 / β) ^ 2 * E)
      ≤ 4 * κ ^ 2 * A ^ 2 * (Am * serC (n + 2) β * ξ ^ n
          + 2 * (2 / β) ^ 2 * ((n.factorial : ℝ) / (Real.exp (-1) * r₀) ^ n * ξ ^ n)) := by
        gcongr
    _ = _ := by ring

/-- **(1c) The Bernstein deviation in terms of `δ'_L = √(L/(N ξⁿ))`**: for `v ≤ C ξⁿ`, `L ≥ 1`,
`dev N B v L ≤ ξⁿ δ'_L (6 B δ'_L + 2 √C)`. -/
theorem dev_rate (N : ℕ) (hN : 0 < N) (n : ℕ) {B v L ξ Cc : ℝ} (hB : 0 ≤ B) (hv : 0 ≤ v)
    (hC : 0 ≤ Cc) (hvC : v ≤ Cc * ξ ^ n) (hL : 1 ≤ L) (hξ : 0 < ξ) :
    dev N B v L ≤ ξ ^ n * Real.sqrt (L / (N * ξ ^ n))
      * (6 * B * Real.sqrt (L / (N * ξ ^ n)) + 2 * Real.sqrt Cc) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < ξ ^ n := by positivity
  set δ := Real.sqrt (L / (N * ξ ^ n)) with hδdef
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδ : δ ^ 2 * (N * ξ ^ n) = L := by
    rw [hδdef, Real.sq_sqrt (by positivity)]; field_simp
  have hvs : v * ξ ^ n ≤ (Real.sqrt Cc * ξ ^ n) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]; nlinarith [mul_le_mul_of_nonneg_right hvC hx.le]
  have h := dev_le' N hN hB hv hL hx hδ0 hδ le_rfl (by positivity) hvs
  calc dev N B v L ≤ 6 * B * ξ ^ n * δ ^ 2 + 2 * δ * (Real.sqrt Cc * ξ ^ n) := h
    _ = _ := by ring

end CTG.NPointSharp

namespace CTG.NPointSharp

section AbstractSharp

variable {E : Type*} [MeasurableSpace E] {m : Measure E} [IsProbabilityMeasure m]

/-- `|∫ F(x,·)| ≤ ∫ |F(x,·)|`. -/
theorem popAvg_abs_le_L1 (F : E → E → ℝ) (x : E) :
    |popAvg m F x| ≤ ∫ z, |F x z| ∂m := abs_integral_le_integral_abs

/-- **Average instead of supremum**: `∫ |F(x,·) g(x,·)| ≤ B_g · ∫ |F(x,·)| ≤ B_g M_F`. -/
theorem popAvg_absmul_le (F g : E → E → ℝ) {BF vF : ℝ} (GF : Good m F BF vF)
    (hg : Measurable fun p : E × E => g p.1 p.2) {Bg : ℝ} (hBg : 0 ≤ Bg)
    (hgb : ∀ x z, |g x z| ≤ Bg) {MF : ℝ} (hMF : ∀ x, ∫ z, |F x z| ∂m ≤ MF) (x : E) :
    popAvg m (fun x z => |F x z * g x z|) x ≤ Bg * MF := by
  have hFx : Measurable (F x) := GF.meas.comp (measurable_const.prodMk measurable_id)
  have hgx : Measurable (g x) := hg.comp (measurable_const.prodMk measurable_id)
  have i1 : Integrable (fun z => |F x z * g x z|) m :=
    bdd_integrable m _ ((hFx.mul hgx).abs) (BF * Bg) (fun z => by
      rw [abs_abs, abs_mul]; exact mul_le_mul (GF.bd x z) (hgb x z) (abs_nonneg _) GF.B_nonneg)
  have i2 : Integrable (fun z => Bg * |F x z|) m :=
    (bdd_integrable m _ hFx.abs BF (fun z => by rw [abs_abs]; exact GF.bd x z)).const_mul Bg
  calc popAvg m (fun x z => |F x z * g x z|) x = ∫ z, |F x z * g x z| ∂m := rfl
    _ ≤ ∫ z, Bg * |F x z| ∂m := integral_mono i1 i2 (fun z => by
        show |F x z * g x z| ≤ Bg * |F x z|
        rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hgb x z) (abs_nonneg _))
    _ = Bg * ∫ z, |F x z| ∂m := integral_const_mul _ _
    _ ≤ Bg * MF := mul_le_mul_of_nonneg_left (hMF x) hBg

/-- Two-term version: if `|G(x,z)| ≤ a₁|F₁(x,z)| + a₂|F₂(x,z)|`, then
`|∫ G(x,·)| ≤ a₁ M₁ + a₂ M₂`. -/
theorem popAvg_comb_le (G F1 F2 : E → E → ℝ) {BG vG B1 v1 B2 v2 : ℝ} (GG : Good m G BG vG)
    (G1 : Good m F1 B1 v1) (G2 : Good m F2 B2 v2) {a1 a2 M1 M2 : ℝ} (ha1 : 0 ≤ a1)
    (ha2 : 0 ≤ a2) (hM1 : ∀ x, ∫ z, |F1 x z| ∂m ≤ M1) (hM2 : ∀ x, ∫ z, |F2 x z| ∂m ≤ M2)
    (hpt : ∀ x z, |G x z| ≤ a1 * |F1 x z| + a2 * |F2 x z|) (x : E) :
    |popAvg m G x| ≤ a1 * M1 + a2 * M2 := by
  have hGx : Measurable (G x) := GG.meas.comp (measurable_const.prodMk measurable_id)
  have h1x : Measurable (F1 x) := G1.meas.comp (measurable_const.prodMk measurable_id)
  have h2x : Measurable (F2 x) := G2.meas.comp (measurable_const.prodMk measurable_id)
  have iG : Integrable (fun z => |G x z|) m :=
    bdd_integrable m _ hGx.abs BG (fun z => by rw [abs_abs]; exact GG.bd x z)
  have i1 : Integrable (fun z => |F1 x z|) m :=
    bdd_integrable m _ h1x.abs B1 (fun z => by rw [abs_abs]; exact G1.bd x z)
  have i2 : Integrable (fun z => |F2 x z|) m :=
    bdd_integrable m _ h2x.abs B2 (fun z => by rw [abs_abs]; exact G2.bd x z)
  calc |popAvg m G x| ≤ ∫ z, |G x z| ∂m := popAvg_abs_le_L1 G x
    _ ≤ ∫ z, (a1 * |F1 x z| + a2 * |F2 x z|) ∂m :=
        integral_mono iG ((i1.const_mul a1).add (i2.const_mul a2)) (fun z => hpt x z)
    _ = a1 * ∫ z, |F1 x z| ∂m + a2 * ∫ z, |F2 x z| ∂m := by
        rw [integral_add (i1.const_mul a1) (i2.const_mul a2), integral_const_mul,
          integral_const_mul]
    _ ≤ a1 * M1 + a2 * M2 := add_le_add (mul_le_mul_of_nonneg_left (hM1 x) ha1)
        (mul_le_mul_of_nonneg_left (hM2 x) ha2)

/-- `|Δ(1/p)| ≤ M_I / c²` with the `L¹` bound `M_I` of the kernel increment. -/
theorem W_bd' (Ka Kb : E → E → ℝ) {η BK vK BI vI c MI : ℝ} (GKa : Good m Ka BK vK)
    (GKb : Good m Kb BK vK) (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y) (hMI0 : 0 ≤ MI)
    (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI) (y : E) :
    |(1 / popAvg m Kb y - 1 / popAvg m Ka y) / η| ≤ MI / c ^ 2 := by
  have ha := hpa y; have hb := hpb y
  have ha0 : 0 < popAvg m Ka y := lt_of_lt_of_le hc ha
  have hb0 : 0 < popAvg m Kb y := lt_of_lt_of_le hc hb
  rw [CTG.Reals2.TimeAppendix4.dq_inv _ _ η ha0.ne' hb0.ne', abs_div, abs_neg,
    popAvg_inc' Ka Kb GKa GKb η y, abs_of_pos (mul_pos ha0 hb0)]
  have h1 := (popAvg_abs_le_L1 (m := m) (fun x z => (Kb x z - Ka x z) / η) y).trans (hMI y)
  have hcc : c ^ 2 ≤ popAvg m Ka y * popAvg m Kb y := by
    rw [sq]; exact mul_le_mul ha hb hc.le ha0.le
  calc _ ≤ MI / (popAvg m Ka y * popAvg m Kb y) :=
        div_le_div_of_nonneg_right h1 (mul_pos ha0 hb0).le
    _ ≤ MI / c ^ 2 := div_le_div_of_nonneg_left hMI0 (by positivity) hcc

/-- The six kernels of Steps 3/4 with the improved bound for the last one. -/
theorem goods34' (Ka Kb g : E → E → ℝ) (η : ℝ) {BK vK BI vI c Bg MI : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg) :
    Good m (fun x z => |Ka x z * g x z|) (BK * Bg) (Bg ^ 2 * vK)
    ∧ Good m (fun x z => |Kb x z * g x z|) (BK * Bg) (Bg ^ 2 * vK)
    ∧ Good m (fun x z => |(Kb x z - Ka x z) / η * g x z|) (BI * Bg) (Bg ^ 2 * vI)
    ∧ Good m (wKer m Ka g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK))
    ∧ Good m (wKer m Kb g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK))
    ∧ Good m (dKer m Ka Kb g η) (BI * Bg * (1 / c) + BK * Bg * (MI / c ^ 2))
        (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((MI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) := by
  have hc1 : (0 : ℝ) ≤ 1 / c := by positivity
  have Ga := GKa.mul g hg Bg hBg hgb
  have Gb := GKb.mul g hg Bg hBg hgb
  have Gi := GKi.mul g hg Bg hBg hgb
  have hWm : Measurable fun p : E × E => (1 / popAvg m Kb p.2 - 1 / popAvg m Ka p.2) / η :=
    ((inv_pop_meas Kb GKb.meas).sub (inv_pop_meas Ka GKa.meas)).div_const η
  refine ⟨Ga.abs, Gb.abs, Gi.abs,
    Ga.mul (fun _ z => 1 / popAvg m Ka z) (inv_pop_meas Ka GKa.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Ka hc hpa z),
    Gb.mul (fun _ z => 1 / popAvg m Kb z) (inv_pop_meas Kb GKb.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Kb hc hpb z), ?_⟩
  exact (Gi.mul (fun _ z => 1 / popAvg m Kb z) (inv_pop_meas Kb GKb.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Kb hc hpb z)).add
    (Ga.mul (fun _ z => (1 / popAvg m Kb z - 1 / popAvg m Ka z) / η) hWm (MI / c ^ 2)
      (by positivity)
      (fun x z => W_bd' Ka Kb GKa GKb GKi hc hpa hpb hMI0 hMI z))

end AbstractSharp

/-- Error of `Δ_η(1/q_j)` with the `L¹` bound `M_I` of `Δ_ηK` in place of its supremum. -/
def err2' (N : ℕ) (BK vK BI vI MI c L : ℝ) : ℝ :=
  4 * dev N BI vI L / c ^ 2 + 6 * MI * (dev N BK vK L / c) / c ^ 2

/-- Error of the weighted average at one time with the `L¹` bound `M` of the kernel. -/
def errT' (N : ℕ) (BK vK M c L Bg : ℝ) : ℝ :=
  err1 N BK vK c L * (Bg * M + dev N (BK * Bg) (Bg ^ 2 * vK) L)
    + dev N (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK)) L

/-- Error of the difference quotient of the weighted average with `L¹` bounds `M`, `M_I`. -/
def errD' (N : ℕ) (BK vK BI vI M MI c L Bg : ℝ) : ℝ :=
  err1 N BK vK c L * (Bg * MI + dev N (BI * Bg) (Bg ^ 2 * vI) L)
    + err2' N BK vK BI vI MI c L * (Bg * M + dev N (BK * Bg) (Bg ^ 2 * vK) L)
    + dev N (BI * Bg * (1 / c) + BK * Bg * (MI / c ^ 2))
        (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((MI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) L

/-- Exceptional event of Steps 3/4 (six kernels), improved constants for `dKer`. -/
def bad34' {E : Type*} [MeasurableSpace E] {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (m : Measure E)
    (Ka Kb g : E → E → ℝ) (η BK vK BI vI MI c L Bg : ℝ) : Set Ω :=
  badSet X N m (fun x z => |Ka x z * g x z|) (BK * Bg) (Bg ^ 2 * vK) L
    ∪ badSet X N m (fun x z => |Kb x z * g x z|) (BK * Bg) (Bg ^ 2 * vK) L
    ∪ badSet X N m (fun x z => |(Kb x z - Ka x z) / η * g x z|) (BI * Bg) (Bg ^ 2 * vI) L
    ∪ badSet X N m (wKer m Ka g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK)) L
    ∪ badSet X N m (wKer m Kb g) (BK * Bg * (1 / c)) ((1 / c) ^ 2 * (Bg ^ 2 * vK)) L
    ∪ badSet X N m (dKer m Ka Kb g η) (BI * Bg * (1 / c) + BK * Bg * (MI / c ^ 2))
        (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((MI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) L

/-- The final error of Step 5 with the averaged constants. -/
def err5' (N : ℕ) (BK vK BI vI M MI c L Bf cD : ℝ) : ℝ :=
  let a := errT' N BK vK M c L Bf + errD' N BK vK BI vI M MI c L Bf
  let ε := errT' N BK vK M c L 1 / cD
  let ε' := errD' N BK vK BI vI M MI c L 1
  let B := Bf * M * (1 / c) + (Bf * MI * (1 / c) + Bf * M * (MI / c ^ 2))
  let C := 1 * MI * (1 / c) + 1 * M * (MI / c ^ 2)
  2 * a / cD + 2 * B * ε / cD + 4 * (a * (C + ε') + B * ε') / cD ^ 2 + 6 * B * C * ε / cD ^ 2

section AssemblySharp

variable {E : Type*} [MeasurableSpace E] {m : Measure E} [IsProbabilityMeasure m]

/-- Steps 3 and 4, deterministic part, with averages in place of suprema. -/
theorem step34_det' {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (Ka Kb g : E → E → ℝ)
    (η : ℝ) {BK vK BI vI c L Bg M MI : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMa : ∀ x, ∫ z, |Ka x z| ∂m ≤ M) (hMb : ∀ x, ∫ z, |Kb x z| ∂m ≤ M)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg)
    (hsmall : dev N BK vK L / c ≤ 1 / 2) (ω : Ω)
    (h2 : ω ∉ bad2 X N m Ka Kb η BK vK BI vI L)
    (h34 : ω ∉ bad34' X N m Ka Kb g η BK vK BI vI MI c L Bg) (i : ℕ) (hi : i < N) :
    |sampW X N Ka g i ω - popW m Ka g (X i ω)| ≤ errT' N BK vK M c L Bg
    ∧ |sampW X N Kb g i ω - popW m Kb g (X i ω)| ≤ errT' N BK vK M c L Bg
    ∧ |(sampW X N Kb g i ω - sampW X N Ka g i ω) / η
        - (popW m Kb g (X i ω) - popW m Ka g (X i ω)) / η| ≤ errD' N BK vK BI vI M MI c L Bg := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ :=
    goods34' Ka Kb g η GKa GKb GKi hc hpa hpb hMI0 hMI hg hBg hgb
  simp only [bad2, bad34', mem_union, not_or] at h2 h34
  obtain ⟨⟨hKa, hKb⟩, hKi⟩ := h2
  obtain ⟨⟨⟨⟨⟨b1, b1b⟩, b2⟩, b3a⟩, b3b⟩, b4⟩ := h34
  have hBK := GKa.B_nonneg; have hvK := GKa.v_nonneg
  have hBI := GKi.B_nonneg; have hvI := GKi.v_nonneg
  have heQ := dev_nonneg N hBK hvK hL.le
  have he1 : 0 ≤ err1 N BK vK c L := by unfold err1; positivity
  have he2 : 0 ≤ err2' N BK vK BI vI MI c L := by
    unfold err2'; have := dev_nonneg N hBI hvI hL.le; positivity
  have wa : ∀ j < N, |1 / sampAvg X N Ka j ω - 1 / popAvg m Ka (X j ω)| ≤ err1 N BK vK c L :=
    fun j hj => (inv_close _ _ _ c hc (hpa _) heQ hsmall (not_badSet hKa hj)).2
  have wb : ∀ j < N, |1 / sampAvg X N Kb j ω - 1 / popAvg m Kb (X j ω)| ≤ err1 N BK vK c L :=
    fun j hj => (inv_close _ _ _ c hc (hpb _) heQ hsmall (not_badSet hKb hj)).2
  have wΔ : ∀ j < N, |(1 / sampAvg X N Kb j ω - 1 / sampAvg X N Ka j ω) / η
      - (1 / popAvg m Kb (X j ω) - 1 / popAvg m Ka (X j ω)) / η|
        ≤ err2' N BK vK BI vI MI c L := by
    intro j hj
    have hΔ := not_badSet hKi hj
    rw [sampAvg_inc, ← popAvg_inc' Ka Kb GKa GKb η] at hΔ
    have hB : |(popAvg m Kb (X j ω) - popAvg m Ka (X j ω)) / η| ≤ MI := by
      rw [popAvg_inc' Ka Kb GKa GKb η]
      exact (popAvg_abs_le_L1 (m := m) _ _).trans (hMI _)
    exact inv_inc_perturb _ _ _ _ η _ _ c MI hc (hpa _) (hpb _) heQ hsmall hMI0
      (not_badSet hKa hj) (not_badSet hKb hj) hΔ hB
  have P1a := popAvg_absmul_le Ka g GKa hg hBg hgb hMa (X i ω)
  have P1b := popAvg_absmul_le Kb g GKb hg hBg hgb hMb (X i ω)
  have P1i := popAvg_absmul_le _ g GKi hg hBg hgb hMI (X i ω)
  refine ⟨?_, ?_, ?_⟩
  · have h := weighted_det N hN (fun j => Ka (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Ka j ω) (fun j => 1 / popAvg m Ka (X j ω)) _ _ _ _ _ he1 wa
      (not_badSet b1 hi) (not_badSet b3a hi)
    refine h.trans ?_
    unfold errT'
    have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
    gcongr
  · have h := weighted_det N hN (fun j => Kb (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Kb j ω) (fun j => 1 / popAvg m Kb (X j ω)) _ _ _ _ _ he1 wb
      (not_badSet b1b hi) (not_badSet b3b hi)
    refine h.trans ?_
    unfold errT'
    gcongr
  · rw [sampW_inc]
    have hpop : (popW m Kb g (X i ω) - popW m Ka g (X i ω)) / η
        = popAvg m (dKer m Ka Kb g η) (X i ω) := by
      rw [dKer_eq]
      exact (popAvg_inc m (wKer m Ka g) (wKer m Kb g) G3a.meas G3b.meas G3a.bd G3b.bd η
        (X i ω)).symm
    rw [hpop]
    have h := weighted2_det N hN
      (fun j => (Kb (X i ω) (X j ω) - Ka (X i ω) (X j ω)) / η * g (X i ω) (X j ω))
      (fun j => Ka (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Kb j ω) (fun j => 1 / popAvg m Kb (X j ω))
      (fun j => (1 / sampAvg X N Kb j ω - 1 / sampAvg X N Ka j ω) / η)
      (fun j => (1 / popAvg m Kb (X j ω) - 1 / popAvg m Ka (X j ω)) / η)
      _ _ _ _ _ _ _ _ he1 he2 wb wΔ (not_badSet b2 hi) (not_badSet b1 hi) (not_badSet b4 hi)
    refine h.trans ?_
    unfold errD'
    have := dev_nonneg N (mul_nonneg hBI hBg) (mul_nonneg (sq_nonneg Bg) hvI) hL.le
    have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
    gcongr

theorem bad34'_prob {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb g : E → E → ℝ) (η : ℝ)
    {BK vK BI vI MI c L Bg : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg) :
    μ.real (bad34' X N m Ka Kb g η BK vK BI vI MI c L Bg) ≤ 6 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ :=
    goods34' Ka Kb g η GKa GKb GKi hc hpa hpb hMI0 hMI hg hBg hgb
  have p := fun {F : E → E → ℝ} {B v : ℝ} (hG : Good m F B v) =>
    hG.prob X h_indep hX hlaw N hN hL
  unfold bad34'
  refine (measureReal_union_le _ _).trans ?_
  refine (add_le_add (measureReal_union_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl)
    le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl)
    le_rfl) le_rfl) le_rfl).trans ?_
  linarith [p G1, p G1b, p G2, p G3a, p G3b, p G4]

/-- Population bounds of the weighted average and its difference quotient, through `L¹` norms. -/
theorem popW_bd' (Ka Kb g : E → E → ℝ) (η : ℝ) {BK vK BI vI c Bg M MI : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMa : ∀ x, ∫ z, |Ka x z| ∂m ≤ M)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (hg : Measurable fun p : E × E => g p.1 p.2) (hBg : 0 ≤ Bg) (hgb : ∀ x z, |g x z| ≤ Bg)
    (x : E) :
    |popW m Ka g x| ≤ Bg * M * (1 / c)
    ∧ |(popW m Kb g x - popW m Ka g x) / η| ≤ Bg * MI * (1 / c) + Bg * M * (MI / c ^ 2) := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ :=
    goods34' Ka Kb g η GKa GKb GKi hc hpa hpb hMI0 hMI hg hBg hgb
  have hc1 : (0:ℝ) ≤ 1 / c := by positivity
  constructor
  · have h := popAvg_comb_le (m := m) (wKer m Ka g) Ka Ka G3a GKa GKa
      (mul_nonneg hBg hc1) (le_refl 0) hMa hMa (fun x z => by
        show |Ka x z * g x z * (1 / popAvg m Ka z)| ≤ Bg * (1 / c) * |Ka x z| + 0 * |Ka x z|
        rw [abs_mul, abs_mul, zero_mul, add_zero]
        have := inv_pop_bd Ka hc hpa z
        have h1 := hgb x z
        calc |Ka x z| * |g x z| * |1 / popAvg m Ka z| ≤ |Ka x z| * Bg * (1 / c) := by gcongr
          _ = Bg * (1 / c) * |Ka x z| := by ring) x
    refine h.trans (le_of_eq ?_)
    ring
  · have hpop : (popW m Kb g x - popW m Ka g x) / η = popAvg m (dKer m Ka Kb g η) x := by
      rw [dKer_eq]
      exact (popAvg_inc m (wKer m Ka g) (wKer m Kb g) G3a.meas G3b.meas G3a.bd G3b.bd η x).symm
    rw [hpop]
    have h := popAvg_comb_le (m := m) (dKer m Ka Kb g η) (fun x z => (Kb x z - Ka x z) / η) Ka
      G4 GKi GKa (mul_nonneg hBg hc1) (by positivity : 0 ≤ Bg * (MI / c ^ 2)) hMI hMa
      (fun x z => by
        show |(Kb x z - Ka x z) / η * g x z * (1 / popAvg m Kb z)
            + Ka x z * g x z * ((1 / popAvg m Kb z - 1 / popAvg m Ka z) / η)|
          ≤ Bg * (1 / c) * |(Kb x z - Ka x z) / η| + Bg * (MI / c ^ 2) * |Ka x z|
        have w1 := inv_pop_bd Kb hc hpb z
        have w2 := W_bd' Ka Kb GKa GKb GKi hc hpa hpb hMI0 hMI z
        have h1 := hgb x z
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_mul]
        have e1 : |(Kb x z - Ka x z) / η| * |g x z| * |1 / popAvg m Kb z|
            ≤ |(Kb x z - Ka x z) / η| * Bg * (1 / c) := by gcongr
        have e2 : |Ka x z| * |g x z| * |(1 / popAvg m Kb z - 1 / popAvg m Ka z) / η|
            ≤ |Ka x z| * Bg * (MI / c ^ 2) := by gcongr
        linarith) x
    refine h.trans (le_of_eq ?_)
    ring

/-- `𝒟(x) ≥ c/M` for `K ≥ 0` with `p ≥ c` and `∫|K(y,·)| ≤ M` (so `p ≤ M`): a lower bound of
order one when `c` and `M` are both of order `ξ^d`. -/
theorem popW_one_ge' (K : E → E → ℝ) {BK vK c M : ℝ} (GK : Good m K BK vK) (hc : 0 < c)
    (hK0 : ∀ x y, 0 ≤ K x y) (hp : ∀ y, c ≤ popAvg m K y) (hM : ∀ x, ∫ z, |K x z| ∂m ≤ M)
    (x : E) : c / M ≤ popW m K (fun _ _ => 1) x := by
  have hpM : ∀ y, popAvg m K y ≤ M := fun y =>
    ((le_abs_self _).trans (popAvg_abs_le_L1 (m := m) K y)).trans (hM y)
  have hMpos : 0 < M := lt_of_lt_of_le hc ((hp x).trans (hpM x))
  have hKx : Measurable (K x) := GK.meas.comp (measurable_const.prodMk measurable_id)
  have hpm : Measurable fun y => 1 / popAvg m K y :=
    measurable_const.div (popAvg_measurable m K GK.meas)
  have hpos : ∀ y, 0 < popAvg m K y := fun y => lt_of_lt_of_le hc (hp y)
  have hle : ∀ y, 1 / M ≤ 1 / popAvg m K y := fun y => one_div_le_one_div_of_le (hpos y) (hpM y)
  have hBK : 0 ≤ BK := GK.B_nonneg
  have hint1 : Integrable (fun y => K x y * (1 / M)) m :=
    (integrable_of_bound m K GK.meas GK.bd x).mul_const _
  have hint2 : Integrable (fun y => K x y * 1 * (1 / popAvg m K y)) m :=
    bdd_integrable m _ ((hKx.mul measurable_const).mul hpm) (BK * (1 / c)) fun y => by
      rw [mul_one, abs_mul]
      exact mul_le_mul (GK.bd x y) (inv_pop_bd K hc hp y) (abs_nonneg _) hBK
  have h1 : ∫ y, K x y * (1 / M) ∂m ≤ popW m K (fun _ _ => 1) x :=
    integral_mono hint1 hint2 fun y => by
      show K x y * (1 / M) ≤ K x y * 1 * (1 / popAvg m K y)
      rw [mul_one]; exact mul_le_mul_of_nonneg_left (hle y) (hK0 x y)
  rw [integral_mul_const] at h1
  have h2 : c / M ≤ (∫ y, K x y ∂m) * (1 / M) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right (hp x) hMpos.le
  linarith

/-- **Steps 2–5, averaged form.**  As `CTG.NPoint.step5`, with the `L¹` bounds `M` (kernel) and
`M_I` (kernel increment) as additional HYPOTHESES and the error `err5'`. -/
theorem step5' {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb gf : E → E → ℝ) (η : ℝ)
    {BK vK BI vI c L Bf cD M MI : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hM0 : 0 ≤ M) (hMa : ∀ x, ∫ z, |Ka x z| ∂m ≤ M) (hMb : ∀ x, ∫ z, |Kb x z| ∂m ≤ M)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (hg : Measurable fun p : E × E => gf p.1 p.2) (hBf : 0 ≤ Bf) (hgb : ∀ x z, |gf x z| ≤ Bf)
    (hcD : 0 < cD) (hDa : ∀ x, cD ≤ popW m Ka (fun _ _ => 1) x)
    (hDb : ∀ x, cD ≤ popW m Kb (fun _ _ => 1) x)
    (hsmall : dev N BK vK L / c ≤ 1 / 2) (hsmallD : errT' N BK vK M c L 1 / cD ≤ 1 / 2) :
    μ.real {ω | ∃ i < N, err5' N BK vK BI vI M MI c L Bf cD
        < |(sampW X N Kb gf i ω / sampW X N Kb (fun _ _ => 1) i ω
              - sampW X N Ka gf i ω / sampW X N Ka (fun _ _ => 1) i ω) / η
          - (popW m Kb gf (X i ω) / popW m Kb (fun _ _ => 1) (X i ω)
              - popW m Ka gf (X i ω) / popW m Ka (fun _ _ => 1) (X i ω)) / η|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  set g1 : E → E → ℝ := fun _ _ => 1
  have hg1 : Measurable fun p : E × E => g1 p.1 p.2 := measurable_const
  have hg1b : ∀ x z, |g1 x z| ≤ 1 := fun x z => by simp [g1]
  have hsub : {ω | ∃ i < N, err5' N BK vK BI vI M MI c L Bf cD
        < |(sampW X N Kb gf i ω / sampW X N Kb g1 i ω
              - sampW X N Ka gf i ω / sampW X N Ka g1 i ω) / η
          - (popW m Kb gf (X i ω) / popW m Kb g1 (X i ω)
              - popW m Ka gf (X i ω) / popW m Ka g1 (X i ω)) / η|}
      ⊆ bad2 X N m Ka Kb η BK vK BI vI L ∪ bad34' X N m Ka Kb gf η BK vK BI vI MI c L Bf
        ∪ bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1 := by
    intro ω ⟨i, hi, hlt⟩
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨h2, h34f⟩, h341⟩ := hcon
    obtain ⟨eNa, -, eΔN⟩ := step34_det' X N hN Ka Kb gf η GKa GKb GKi hc hL hpa hpb hMa hMb
      hMI0 hMI hg hBf hgb hsmall ω h2 h34f i hi
    obtain ⟨eDa, eDb, eΔD⟩ := step34_det' X N hN Ka Kb g1 η GKa GKb GKi hc hL hpa hpb hMa hMb
      hMI0 hMI hg1 zero_le_one hg1b hsmall ω h2 h341 i hi
    obtain ⟨bn, bx⟩ := popW_bd' Ka Kb gf η GKa GKb GKi hc hpa hpb hMa hMI0 hMI hg hBf hgb (X i ω)
    obtain ⟨-, by'⟩ := popW_bd' Ka Kb g1 η GKa GKb GKi hc hpa hpb hMa hMI0 hMI hg1 zero_le_one
      hg1b (X i ω)
    have hBK := GKa.B_nonneg; have hBI := GKi.B_nonneg
    have hvK := GKa.v_nonneg; have hvI := GKi.v_nonneg
    have heQ := dev_nonneg N hBK hvK hL.le
    have he1 : 0 ≤ err1 N BK vK c L := by unfold err1; positivity
    have he2 : 0 ≤ err2' N BK vK BI vI MI c L := by
      unfold err2'; have := dev_nonneg N hBI hvI hL.le; positivity
    have hT : ∀ Bg, 0 ≤ Bg → 0 ≤ errT' N BK vK M c L Bg := fun Bg hBg => by
      unfold errT'
      have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
      have := dev_nonneg N (mul_nonneg (mul_nonneg hBK hBg) (by positivity : (0:ℝ) ≤ 1 / c))
        (mul_nonneg (sq_nonneg (1 / c)) (mul_nonneg (sq_nonneg Bg) hvK)) hL.le
      positivity
    have hD : ∀ Bg, 0 ≤ Bg → 0 ≤ errD' N BK vK BI vI M MI c L Bg := fun Bg hBg => by
      unfold errD'
      have := dev_nonneg N (mul_nonneg hBI hBg) (mul_nonneg (sq_nonneg Bg) hvI) hL.le
      have := dev_nonneg N (mul_nonneg hBK hBg) (mul_nonneg (sq_nonneg Bg) hvK) hL.le
      have := dev_nonneg N (B := BI * Bg * (1 / c) + BK * Bg * (MI / c ^ 2))
        (v := 2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((MI / c ^ 2) ^ 2 * (Bg ^ 2 * vK)))
        (by positivity) (by positivity) hL.le
      positivity
    set a := errT' N BK vK M c L Bf + errD' N BK vK BI vI M MI c L Bf with ha
    set ε := errT' N BK vK M c L 1 / cD with hε
    set ε' := errD' N BK vK BI vI M MI c L 1 with hε'
    set B := Bf * M * (1 / c) + (Bf * MI * (1 / c) + Bf * M * (MI / c ^ 2)) with hB
    set C := 1 * MI * (1 / c) + 1 * M * (MI / c ^ 2) with hC
    have hTf := hT Bf hBf; have hDf := hD Bf hBf
    have hrel : ∀ (Dv dv : ℝ), cD ≤ dv → |Dv - dv| ≤ errT' N BK vK M c L 1 →
        |Dv - dv| ≤ ε * dv :=
      fun Dv dv hdv h => by
        refine h.trans ?_
        rw [hε, div_mul_eq_mul_div, le_div_iff₀ hcD]
        exact mul_le_mul_of_nonneg_left hdv (hT 1 zero_le_one)
    have hda := hDa (X i ω); have hdb := hDb (X i ω)
    have rDa := hrel _ _ hda eDa; have rDb := hrel _ _ hdb eDb
    have hεnn : 0 ≤ ε := div_nonneg (hT 1 zero_le_one) hcD.le
    obtain ⟨hDa0, -, -⟩ := CTG.Reals2.TimeAppendix4.inv_perturb _ _ cD ε hcD hda hεnn hsmallD rDa
    obtain ⟨hDb0, -, -⟩ := CTG.Reals2.TimeAppendix4.inv_perturb _ _ cD ε hcD hdb hεnn hsmallD rDb
    have hda0 : 0 < popW m Ka g1 (X i ω) := lt_of_lt_of_le hcD hda
    have hdb0 : 0 < popW m Kb g1 (X i ω) := lt_of_lt_of_le hcD hdb
    have hq := CTG.Reals2.TimeAppendix4.quotient_dq_perturb
      ((sampW X N Kb gf i ω - sampW X N Ka gf i ω) / η)
      ((popW m Kb gf (X i ω) - popW m Ka gf (X i ω)) / η)
      (sampW X N Ka gf i ω) (popW m Ka gf (X i ω))
      ((sampW X N Kb g1 i ω - sampW X N Ka g1 i ω) / η)
      ((popW m Kb g1 (X i ω) - popW m Ka g1 (X i ω)) / η)
      (sampW X N Ka g1 i ω) (popW m Ka g1 (X i ω))
      (sampW X N Kb g1 i ω) (popW m Kb g1 (X i ω)) a B C cD ε ε' hcD hda hdb hεnn hsmallD
      (by positivity) (by positivity) (by positivity) (hD 1 zero_le_one) rDa rDb
      (eΔN.trans (by linarith)) (eNa.trans (by linarith)) eΔD
      (bx.trans (by have : 0 ≤ Bf * M * (1 / c) := by positivity
                    linarith))
      (bn.trans (by have : 0 ≤ Bf * MI * (1 / c) + Bf * M * (MI / c ^ 2) := by positivity
                    linarith))
      by'
    rw [← CTG.Reals2.TimeAppendix4.dq_quotient _ _ _ _ η hDa0.ne' hDb0.ne',
      ← CTG.Reals2.TimeAppendix4.dq_quotient _ _ _ _ η hda0.ne' hdb0.ne'] at hq
    have : err5' N BK vK BI vI M MI c L Bf cD
        = 2 * a / cD + 2 * B * ε / cD + 4 * (a * (C + ε') + B * ε') / cD ^ 2
          + 6 * B * C * ε / cD ^ 2 := rfl
    rw [this] at hlt
    linarith
  calc μ.real _ ≤ μ.real (bad2 X N m Ka Kb η BK vK BI vI L
        ∪ bad34' X N m Ka Kb gf η BK vK BI vI MI c L Bf
        ∪ bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (bad2 X N m Ka Kb η BK vK BI vI L ∪ bad34' X N m Ka Kb gf η BK vK BI vI MI c L Bf)
        + μ.real (bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1) := measureReal_union_le _ _
    _ ≤ (μ.real (bad2 X N m Ka Kb η BK vK BI vI L)
          + μ.real (bad34' X N m Ka Kb gf η BK vK BI vI MI c L Bf))
        + μ.real (bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1) :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ 3 * (N * (2 * Real.exp (-L))) + 6 * (N * (2 * Real.exp (-L)))
        + 6 * (N * (2 * Real.exp (-L))) := by
        linarith [bad2_prob X h_indep hX hlaw N hN Ka Kb η GKa GKb GKi hL,
          bad34'_prob X h_indep hX hlaw N hN Ka Kb gf η GKa GKb GKi hc hL hpa hpb hMI0 hMI hg
            hBf hgb,
          bad34'_prob X h_indep hX hlaw N hN Ka Kb g1 η GKa GKb GKi hc hL hpa hpb hMI0 hMI hg1
            zero_le_one hg1b]
    _ = 15 * (N * (2 * Real.exp (-L))) := by ring

end AssemblySharp

end CTG.NPointSharp

namespace CTG.NPointSharp

/-- Closed constant of the `L¹` bound of a profile `c (ρ/ξ)^j e^{−bρ/ξ}`. -/
def profC (c b : ℝ) (j d : ℕ) (Am r₀ : ℝ) : ℝ :=
  c * (Am * serC (j + d) b + (j.factorial : ℝ) * (2 / b) ^ j * ((d.factorial : ℝ) / (b * r₀ / 2) ^ d))

theorem profC_nonneg {c b : ℝ} (j d : ℕ) {Am r₀ : ℝ} (hc : 0 ≤ c) (hb : 0 < b) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) : 0 ≤ profC c b j d Am r₀ := by
  unfold profC; have := serC_nonneg (j + d) hb; positivity

theorem profC_pos {c b : ℝ} (j d : ℕ) {Am r₀ : ℝ} (hc : 0 < c) (hb : 0 < b) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) : 0 < profC c b j d Am r₀ := by
  unfold profC; have := serC_nonneg (j + d) hb; positivity

/-- **`L¹` bound of an exponential profile** under upper volume growth:
`∫ c (ρ/ξ)^j e^{−bρ/ξ} dm ≤ profC c b j d A_m r₀ · ξ^d`. -/
theorem profile_L1 {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (ρ : X → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hgrowth : ∀ r, 0 < r → r ≤ r₀ → m {y | ρ y < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (c b : ℝ) (j : ℕ) (hc : 0 ≤ c) (hb : 0 < b) :
    ∫ y, c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ))) ∂m ≤ profC c b j d Am r₀ * ξ ^ d := by
  have hlin := CTG.ManifoldDistance.exp_profile_integral m ρ hρm hρ0 d Am r₀ ξ hAm hr₀ hξ
    hgrowth c b j hc hb
  have hS : (∑' n : ℕ, c * (((n : ℝ) + 1) ^ j * Real.exp (-b * n)) * ((n : ℝ) + 1) ^ d)
      = c * ∑' n : ℕ, ((n : ℝ) + 1) ^ (j + d) * Real.exp (-b * n) := by
    rw [← tsum_mul_left]; congr 1; funext n; ring
  have hS0 : 0 ≤ ∑' n : ℕ, ((n : ℝ) + 1) ^ (j + d) * Real.exp (-b * n) :=
    tsum_nonneg fun n => by positivity
  have hmeas : Measurable fun y => c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ))) :=
    measurable_const.mul (((hρm.div_const ξ).pow_const j).mul
      (measurable_const.mul (hρm.div_const ξ)).exp)
  have h1 := integral_le_of_lintegral_le m _ (fun y => by
      have := hρ0 y; positivity) hmeas _ _
    (by rw [hS]; positivity) (by positivity) hlin
  rw [hS] at h1
  have hs := series_le (j + d) hb
  have e2 : Real.exp (-b * (r₀ / ξ) / 2) = Real.exp (-((b * r₀ / 2) / ξ)) := by congr 1; ring
  rw [e2] at h1
  have hf := far_le d (by positivity : 0 < b * r₀ / 2) hξ
  have t1 : Am * (c * ∑' n : ℕ, ((n : ℝ) + 1) ^ (j + d) * Real.exp (-b * n)) * ξ ^ d
      ≤ Am * (c * serC (j + d) b) * ξ ^ d := by gcongr
  have t2 : c * ((j.factorial : ℝ) * (2 / b) ^ j * Real.exp (-((b * r₀ / 2) / ξ)))
      ≤ c * ((j.factorial : ℝ) * (2 / b) ^ j * ((d.factorial : ℝ) / (b * r₀ / 2) ^ d * ξ ^ d)) := by
    gcongr
  calc _ ≤ _ := h1
    _ ≤ Am * (c * serC (j + d) b) * ξ ^ d
        + c * ((j.factorial : ℝ) * (2 / b) ^ j * ((d.factorial : ℝ) / (b * r₀ / 2) ^ d * ξ ^ d)) :=
        add_le_add t1 t2
    _ = profC c b j d Am r₀ * ξ ^ d := by unfold profC; ring

section ManifoldL1

open Bundle Manifold CTG.ManifoldDistance

variable {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EE H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle EE (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {s : Set ℝ}

/-- `L¹` bound of the kernel: `∫ |K^τ(x,·)| dm ≤ profC A 1 0 d A_m r₀ · ξ^d`. -/
theorem kern_L1 (G : TimeMetric I M s) {a₀ τ : ℝ} (ha₀ : a₀ ∈ s) (hτ : τ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ) (x : M)
    (hgrowth : ∀ r, 0 < r → r ≤ r₀ → m {y | G.dist x y τ < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h : ℝ → ℝ) (hhc : Continuous h) (A : ℝ) (hA : 0 ≤ A)
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) :
    ∫ y, |kern G h ξ τ x y| ∂m ≤ profC A 1 0 d Am r₀ * ξ ^ d := by
  have hρm : Measurable (fun y => G.dist x y τ) :=
    ((G.dist_continuous_pair ha₀ hτ hcont).comp (continuous_const.prodMk continuous_id)).measurable
  have hL := profile_L1 m (fun y => G.dist x y τ) hρm (fun y => G.dist_nonneg x y τ) d Am r₀ ξ
    hAm hr₀ hξ hgrowth A 1 0 hA one_pos
  refine le_trans ?_ hL
  have hmeasK : Measurable fun y => kern G h ξ τ x y := hhc.measurable.comp (hρm.div_const ξ)
  refine integral_mono (bdd_integrable m _ hmeasK.abs A (fun y => by
      rw [abs_abs]; exact kern_abs_le G h A ξ τ hξ hh hA x y)) ?_ (fun y => ?_)
  · refine bdd_integrable m _ (measurable_const.mul (((hρm.div_const ξ).pow_const 0).mul
      (measurable_const.mul (hρm.div_const ξ)).exp)) A (fun y => ?_)
    have ht : 0 ≤ G.dist x y τ / ξ := div_nonneg (G.dist_nonneg x y τ) hξ.le
    have : Real.exp (-1 * (G.dist x y τ / ξ)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    rw [pow_zero, one_mul, abs_of_nonneg (by positivity)]
    nlinarith [Real.exp_pos (-1 * (G.dist x y τ / ξ))]
  · have ht : 0 ≤ G.dist x y τ / ξ := div_nonneg (G.dist_nonneg x y τ) hξ.le
    show |h (G.dist x y τ / ξ)| ≤ A * ((G.dist x y τ / ξ) ^ 0 * Real.exp (-1 * (G.dist x y τ / ξ)))
    rw [pow_zero, one_mul, neg_one_mul]; exact hh _ ht

/-- `L¹` bound of the kernel increment: `∫ |Δ_ηK(x,·)| dm ≤ profC (2κA) e⁻¹ 1 d A_m r₀ · ξ^d`. -/
theorem kernInc_L1 (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ) (x : M)
    (hgrowth : ∀ r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) :
    ∫ y, |(kern G h ξ b x y - kern G h ξ a x y) / (b - a)| ∂m
      ≤ profC (2 * G.κ * A) (Real.exp (-1)) 1 d Am r₀ * ξ ^ d := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have hρm : Measurable (fun y => G.dist x y a) :=
    ((G.dist_continuous_pair ha₀ ha hcont).comp (continuous_const.prodMk continuous_id)).measurable
  have hκA : 0 ≤ 2 * G.κ * A := by have := G.κ_nonneg; positivity
  have hL := profile_L1 m (fun y => G.dist x y a) hρm (fun y => G.dist_nonneg x y a) d Am r₀ ξ
    hAm hr₀ hξ hgrowth (2 * G.κ * A) (Real.exp (-1)) 1 hκA (Real.exp_pos _)
  refine le_trans ?_ hL
  have hmb : Measurable fun y : M => kern G h ξ b x y :=
    (kern_measurable G ha₀ hb hcont h hhc ξ).comp (measurable_const.prodMk measurable_id)
  have hma : Measurable fun y : M => kern G h ξ a x y :=
    (kern_measurable G ha₀ ha hcont h hhc ξ).comp (measurable_const.prodMk measurable_id)
  have hd : 0 < |b - a| := abs_pos.2 (sub_ne_zero.2 hne)
  refine integral_mono (bdd_integrable m _ ((hmb.sub hma).div_const _).abs (2 * G.κ * A)
      (fun y => by
        rw [abs_abs]
        exact kernInc_abs_le G ha₀ hcont ha hb hab hne h h' A ξ hA hξ hder hbd x y)) ?_
    (fun y => ?_)
  · refine bdd_integrable m _ (measurable_const.mul (((hρm.div_const ξ).pow_const 1).mul
      (measurable_const.mul (hρm.div_const ξ)).exp)) (2 * G.κ * A) (fun y => ?_)
    have ht : 0 ≤ G.dist x y a / ξ := div_nonneg (G.dist_nonneg x y a) hξ.le
    have hs := sexp_le_one (G.dist x y a / ξ) ht
    rw [pow_one, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right hκA hs
  · have hk := G.kernel_increment_le ha hb hab x y (G.riemannianEDist_ne_top ha₀ ha hcont x y)
      h h' A ξ hA hξ hder hbd
    show |(h (G.dist x y b / ξ) - h (G.dist x y a / ξ)) / (b - a)|
      ≤ 2 * G.κ * A * ((G.dist x y a / ξ) ^ 1 * Real.exp (-Real.exp (-1) * (G.dist x y a / ξ)))
    rw [abs_div, div_le_iff₀ hd]
    refine hk.trans (le_of_eq ?_)
    ring

/-- **Steps 2–5 of `prop:dotLN-diff` on the manifold, averaged form.**  Setting and HYPOTHESES as
`CTG.NPoint.npoint_step5` (upper growth at both times, `q^τ ≥ c`), but the error is `err5'` with the
`L¹` constants `M = profC A 1 0 d A_m r₀ ξ^d`, `M_I = profC (2κA) e⁻¹ 1 d A_m r₀ ξ^d` and the
denominator bound `c_D = c/M`. -/
theorem npoint_step5' {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (f : M → ℝ) (hf : Measurable f) (Bf : ℝ) (hBf : 0 ≤ Bf) (hfb : ∀ x, |f x| ≤ Bf)
    (c : ℝ) (hc : 0 < c)
    (hqa : ∀ y, c ≤ popNorm G h ξ a m y) (hqb : ∀ y, c ≤ popNorm G h ξ b m y)
    (L : ℝ) (hL : 0 < L)
    (hsmall : dev N A (vKern d Am r₀ ξ A) L / c ≤ 1 / 2)
    (hsmallD : errT' N A (vKern d Am r₀ ξ A) (profC A 1 0 d Am r₀ * ξ ^ d) c L 1
      / (c / (profC A 1 0 d Am r₀ * ξ ^ d)) ≤ 1 / 2) :
    μ.real {ω | ∃ i < N,
        err5' N A (vKern d Am r₀ ξ A) (2 * G.κ * A) (vInc G.κ d Am r₀ ξ A a b)
          (profC A 1 0 d Am r₀ * ξ ^ d) (profC (2 * G.κ * A) (Real.exp (-1)) 1 d Am r₀ * ξ ^ d)
          c L (2 * Bf) (c / (profC A 1 0 d Am r₀ * ξ ^ d))
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have GKa := good_kern G ha₀ ha hcont m d Am r₀ ξ hAm hr₀ hξ hga h hhc A hA.le hh
  have GKb := good_kern G ha₀ hb hcont m d Am r₀ ξ hAm hr₀ hξ hgb h hhc A hA.le hh
  have GKi := good_inc G ha₀ hcont ha hb hab hne m d Am r₀ ξ hAm hr₀ hξ hga h h' A hA.le hder hbd
  have hMpos : 0 < profC A 1 0 d Am r₀ * ξ ^ d :=
    mul_pos (profC_pos 0 d hA one_pos hAm hr₀) (pow_pos hξ d)
  have hMI0 : 0 ≤ profC (2 * G.κ * A) (Real.exp (-1)) 1 d Am r₀ * ξ ^ d :=
    mul_nonneg (profC_nonneg 1 d (by have := G.κ_nonneg; positivity) (Real.exp_pos _) hAm hr₀)
      (pow_pos hξ d).le
  have hMa := fun x => kern_L1 G ha₀ ha hcont m d Am r₀ ξ hAm hr₀ hξ x (hga x) h hhc A hA.le hh
  have hMb := fun x => kern_L1 G ha₀ hb hcont m d Am r₀ ξ hAm hr₀ hξ x (hgb x) h hhc A hA.le hh
  have hMI := fun x => kernInc_L1 G ha₀ hcont ha hb hab hne m d Am r₀ ξ hAm hr₀ hξ x (hga x)
    h h' A hA.le hder hbd
  exact step5' X h_indep hX hlaw N hN (kern G h ξ a) (kern G h ξ b)
    (fun x y => f y - f x) (b - a) GKa GKb GKi hc hL hqa hqb hMpos.le hMa hMb hMI0 hMI
    (hf.comp measurable_snd |>.sub (hf.comp measurable_fst)) (by positivity)
    (fun x z => by
      calc |f z - f x| ≤ |f z| + |f x| := abs_sub _ _
        _ ≤ 2 * Bf := by linarith [hfb x, hfb z])
    (div_pos hc hMpos)
    (fun x => popW_one_ge' _ GKa hc (fun x y => hh0 _) hqa hMa x)
    (fun x => popW_one_ge' _ GKb hc (fun x y => hh0 _) hqb hMb x)
    hsmall hsmallD

end ManifoldL1

end CTG.NPointSharp

namespace CTG.NPointSharp

namespace Ctx

variable {N : ℕ} {Λ x y δ L : ℝ}

theorem monoΛ (C : Ctx N Λ x y δ L) {i k : ℕ} (hik : i ≤ k) : Λ ^ i * δ ≤ Λ ^ k * δ :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ C.hΛ hik) C.hδ0

/-- Bracket of `errT'`/`errD'`: `B_g M + dev(B B_g, B_g² v) ≤ 9 Λ² x` when `M ≤ Λ x`. -/
theorem bracket'_le (C : Ctx N Λ x y δ L) {B v Bg MM : ℝ} (hB : 0 ≤ B) (hB' : B ≤ Λ)
    (hv : 0 ≤ v) (hv' : v ≤ Λ ^ 2 * x) (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ) (hM0 : 0 ≤ MM)
    (hM : MM ≤ Λ * x) :
    Bg * MM + dev N (B * Bg) (Bg ^ 2 * v) L ≤ 9 * Λ ^ 2 * x := by
  have := C.Λ0; have hx := C.hx; have := C.hδ0
  have h0 : Bg * MM ≤ Λ * (Λ * x) := mul_le_mul hg' hM hM0 C.Λ0
  have hBB : B * Bg ≤ Λ ^ 2 := by nlinarith [mul_le_mul hB' hg' hg C.Λ0]
  have hg2 : Bg ^ 2 ≤ Λ ^ 2 := by gcongr
  have hvs : Bg ^ 2 * v * x ≤ (Λ ^ 2 * x) ^ 2 := by
    have := mul_le_mul hg2 hv' hv (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right this hx.le]
  have h := dev_le' N C.hN (mul_nonneg hB hg) (by positivity) C.hL C.hx C.hδ0 C.hδ hBB
    (by positivity) hvs
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [C.hδ1]
  have h3 : Λ ^ 2 * x * δ ^ 2 ≤ Λ ^ 2 * x * 1 := mul_le_mul_of_nonneg_left hδ2 (by positivity)
  have h4 : Λ ^ 2 * x * δ ≤ Λ ^ 2 * x * 1 := mul_le_mul_of_nonneg_left C.hδ1 (by positivity)
  nlinarith

theorem err2'_le (C : Ctx N Λ x y δ L) {A vK BI vI MI c : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI) (hBI' : BI ≤ Λ) (hw : 0 ≤ vI)
    (hw' : vI ≤ Λ ^ 2 * x) (hMI0 : 0 ≤ MI) (hMI : MI ≤ Λ * x) (hc : 0 < c)
    (hci : c⁻¹ ≤ Λ * y) :
    err2' N A vK BI vI MI c L ≤ 80 * Λ ^ 5 * y * δ := by
  unfold err2'
  have hd := C.dev_K hA hA' hv hv'
  have hdI := C.dev_K hBI hBI' hw hw'
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have hd0 := dev_nonneg N hA hv hL0
  have hdI0 := dev_nonneg N hBI hw hL0
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have e : 4 * dev N BI vI L / c ^ 2 + 6 * MI * (dev N A vK L / c) / c ^ 2
      = 4 * (dev N BI vI L * c⁻¹ ^ 2) + 6 * (MI * dev N A vK L * c⁻¹ ^ 3) := by ring
  rw [e]
  have := C.Λ0; have := C.hx; have := C.hδ0; have := C.y_pos
  have h1 : dev N BI vI L * c⁻¹ ^ 2 ≤ (8 * Λ * x * δ) * (Λ * y) ^ 2 := by gcongr
  have h2 : MI * dev N A vK L * c⁻¹ ^ 3 ≤ (Λ * x) * (8 * Λ * x * δ) * (Λ * y) ^ 3 := by gcongr
  have e1 : (8 * Λ * x * δ) * (Λ * y) ^ 2 = 8 * (Λ ^ 3 * y * δ) := by
    linear_combination (8 * Λ ^ 3 * y * δ) * C.hxy
  have e2 : (Λ * x) * (8 * Λ * x * δ) * (Λ * y) ^ 3 = 8 * (Λ ^ 5 * y * δ) := by
    linear_combination (8 * Λ ^ 5 * y * δ * (x * y + 1)) * C.hxy
  have m1 : Λ ^ 3 * y * δ ≤ Λ ^ 5 * y * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ C.hΛ (by norm_num)) (by positivity)) C.hδ0
  linarith

theorem errT'_le (C : Ctx N Λ x y δ L) {A vK MM c Bg : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MM) (hM : MM ≤ Λ * x) (hc : 0 < c)
    (hci : c⁻¹ ≤ Λ * y) (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ) :
    errT' N A vK MM c L Bg ≤ 152 * Λ ^ 5 * δ := by
  unfold errT'
  have he1 := C.err1_le hA hA' hv hv' hc hci
  have hbr := C.bracket'_le hA hA' hv hv' hg hg' hM0 hM
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hbr0 : 0 ≤ Bg * MM + dev N (A * Bg) (Bg ^ 2 * vK) L := by
    have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL0; positivity
  have hB2 : A * Bg * (1 / c) ≤ Λ ^ 3 * y := by
    rw [one_div]
    calc A * Bg * c⁻¹ ≤ Λ * Λ * (Λ * y) := by gcongr
      _ = Λ ^ 3 * y := by ring
  have hv2 : (1 / c) ^ 2 * (Bg ^ 2 * vK) * x ≤ (Λ ^ 3) ^ 2 := by
    rw [one_div]
    calc c⁻¹ ^ 2 * (Bg ^ 2 * vK) * x ≤ (Λ * y) ^ 2 * (Λ ^ 2 * (Λ ^ 2 * x)) * x := by gcongr
      _ = (Λ ^ 3) ^ 2 := by linear_combination (Λ ^ 6 * (x * y + 1)) * C.hxy
  have hd2 := dev_le' N C.hN (by positivity : 0 ≤ A * Bg * (1 / c))
    (by positivity : 0 ≤ (1 / c) ^ 2 * (Bg ^ 2 * vK)) C.hL C.hx C.hδ0 C.hδ hB2 (by positivity) hv2
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [C.hδ1]
  have h3 : 6 * (Λ ^ 3 * y) * x * δ ^ 2 ≤ 6 * Λ ^ 3 * δ := by
    have e : 6 * (Λ ^ 3 * y) * x * δ ^ 2 = 6 * Λ ^ 3 * δ ^ 2 := by
      linear_combination (6 * Λ ^ 3 * δ ^ 2) * C.hxy
    rw [e]; have : 0 ≤ Λ ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hδ2 this
    linarith
  have hprod : err1 N A vK c L * (Bg * MM + dev N (A * Bg) (Bg ^ 2 * vK) L)
      ≤ (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) := mul_le_mul he1 hbr hbr0 (by positivity)
  have e3 : (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) = 144 * (Λ ^ 5 * δ) := by
    linear_combination (144 * Λ ^ 5 * δ) * C.hxy
  have m1 := C.monoΛ (i := 3) (k := 5) (by norm_num)
  linarith

set_option maxHeartbeats 800000 in
theorem errD'_le (C : Ctx N Λ x y δ L) {A vK BI vI MM MI c Bg : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI) (hBI' : BI ≤ Λ) (hw : 0 ≤ vI)
    (hw' : vI ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MM) (hM : MM ≤ Λ * x) (hMI0 : 0 ≤ MI)
    (hMI : MI ≤ Λ * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y) (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ) :
    errD' N A vK BI vI MM MI c L Bg ≤ 880 * Λ ^ 7 * δ := by
  unfold errD'
  have he1 := C.err1_le hA hA' hv hv' hc hci
  have he2 := C.err2'_le hA hA' hv hv' hBI hBI' hw hw' hMI0 hMI hc hci
  have hbrI := C.bracket'_le hBI hBI' hw hw' hg hg' hMI0 hMI
  have hbr := C.bracket'_le hA hA' hv hv' hg hg' hM0 hM
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have he10 : 0 ≤ err1 N A vK c L := by
    unfold err1; have := dev_nonneg N hA hv hL0; positivity
  have he20 : 0 ≤ err2' N A vK BI vI MI c L := by
    unfold err2'; have := dev_nonneg N hA hv hL0; have := dev_nonneg N hBI hw hL0; positivity
  have hbr0 : 0 ≤ Bg * MM + dev N (A * Bg) (Bg ^ 2 * vK) L := by
    have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL0; positivity
  have hbrI0 : 0 ≤ Bg * MI + dev N (BI * Bg) (Bg ^ 2 * vI) L := by
    have := dev_nonneg N (mul_nonneg hBI hg) (by positivity : 0 ≤ Bg ^ 2 * vI) hL0; positivity
  have hB2 : BI * Bg * (1 / c) + A * Bg * (MI / c ^ 2) ≤ 2 * Λ ^ 5 * y := by
    have e : BI * Bg * (1 / c) + A * Bg * (MI / c ^ 2) = BI * Bg * c⁻¹ + A * Bg * MI * c⁻¹ ^ 2 := by
      ring
    rw [e]
    have h1 : BI * Bg * c⁻¹ ≤ Λ * Λ * (Λ * y) := by gcongr
    have h2 : A * Bg * MI * c⁻¹ ^ 2 ≤ Λ * Λ * (Λ * x) * (Λ * y) ^ 2 := by gcongr
    have e2 : Λ * Λ * (Λ * x) * (Λ * y) ^ 2 = Λ ^ 5 * y := by
      linear_combination (Λ ^ 5 * y) * C.hxy
    have m : Λ ^ 3 * y ≤ Λ ^ 5 * y :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ C.hΛ (by norm_num)) (by positivity)
    nlinarith
  have hv2 : (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((MI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) * x
      ≤ (2 * Λ ^ 5) ^ 2 := by
    have e : (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((MI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) * x
        = 2 * (c⁻¹ ^ 2 * (Bg ^ 2 * vI) * x) + 2 * (MI ^ 2 * c⁻¹ ^ 4 * (Bg ^ 2 * vK) * x) := by ring
    rw [e]
    have h1 : c⁻¹ ^ 2 * (Bg ^ 2 * vI) * x ≤ (Λ * y) ^ 2 * (Λ ^ 2 * (Λ ^ 2 * x)) * x := by gcongr
    have h2 : MI ^ 2 * c⁻¹ ^ 4 * (Bg ^ 2 * vK) * x
        ≤ (Λ * x) ^ 2 * (Λ * y) ^ 4 * (Λ ^ 2 * (Λ ^ 2 * x)) * x := by gcongr
    have e1 : (Λ * y) ^ 2 * (Λ ^ 2 * (Λ ^ 2 * x)) * x = Λ ^ 6 := by
      linear_combination (Λ ^ 6 * (x * y + 1)) * C.hxy
    have e2 : (Λ * x) ^ 2 * (Λ * y) ^ 4 * (Λ ^ 2 * (Λ ^ 2 * x)) * x = Λ ^ 10 := by
      linear_combination (Λ ^ 10 * (x * y + 1) * (x ^ 2 * y ^ 2 + 1)) * C.hxy
    have m : Λ ^ 6 ≤ Λ ^ 10 := pow_le_pow_right₀ C.hΛ (by norm_num)
    nlinarith
  have hd2 := dev_le' N C.hN (by positivity) (by positivity) C.hL C.hx C.hδ0 C.hδ hB2
    (by positivity) hv2
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [C.hδ1]
  have h3 : 6 * (2 * Λ ^ 5 * y) * x * δ ^ 2 ≤ 12 * Λ ^ 5 * δ := by
    have e : 6 * (2 * Λ ^ 5 * y) * x * δ ^ 2 = 12 * Λ ^ 5 * δ ^ 2 := by
      linear_combination (12 * Λ ^ 5 * δ ^ 2) * C.hxy
    rw [e]; have : 0 ≤ Λ ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_left hδ2 this
    linarith
  have hp1 : err1 N A vK c L * (Bg * MI + dev N (BI * Bg) (Bg ^ 2 * vI) L)
      ≤ (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) := mul_le_mul he1 hbrI hbrI0 (by positivity)
  have hp2 : err2' N A vK BI vI MI c L * (Bg * MM + dev N (A * Bg) (Bg ^ 2 * vK) L)
      ≤ (80 * Λ ^ 5 * y * δ) * (9 * Λ ^ 2 * x) := mul_le_mul he2 hbr hbr0 (by positivity)
  have e3 : (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) = 144 * (Λ ^ 5 * δ) := by
    linear_combination (144 * Λ ^ 5 * δ) * C.hxy
  have e4 : (80 * Λ ^ 5 * y * δ) * (9 * Λ ^ 2 * x) = 720 * (Λ ^ 7 * δ) := by
    linear_combination (720 * Λ ^ 7 * δ) * C.hxy
  have m1 := C.monoΛ (i := 5) (k := 7) (by norm_num)
  linarith

theorem errT'_nonneg (N : ℕ) {A vK MM c L Bg : ℝ} (hA : 0 ≤ A) (hv : 0 ≤ vK) (hc : 0 < c)
    (hL : 0 ≤ L) (hg : 0 ≤ Bg) (hM0 : 0 ≤ MM) : 0 ≤ errT' N A vK MM c L Bg := by
  unfold errT' err1
  have := dev_nonneg N hA hv hL
  have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL
  have := dev_nonneg N (by positivity : 0 ≤ A * Bg * (1 / c))
    (by positivity : 0 ≤ (1 / c) ^ 2 * (Bg ^ 2 * vK)) hL
  positivity

theorem errD'_nonneg (N : ℕ) {A vK BI vI MM MI c L Bg : ℝ} (hA : 0 ≤ A) (hv : 0 ≤ vK)
    (hBI : 0 ≤ BI) (hw : 0 ≤ vI) (hc : 0 < c) (hL : 0 ≤ L) (hg : 0 ≤ Bg) (hM0 : 0 ≤ MM)
    (hMI0 : 0 ≤ MI) : 0 ≤ errD' N A vK BI vI MM MI c L Bg := by
  unfold errD' err1 err2'
  have := dev_nonneg N hA hv hL
  have := dev_nonneg N hBI hw hL
  have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL
  have := dev_nonneg N (mul_nonneg hBI hg) (by positivity : 0 ≤ Bg ^ 2 * vI) hL
  have := dev_nonneg N (by positivity : 0 ≤ BI * Bg * (1 / c) + A * Bg * (MI / c ^ 2))
    (by positivity : 0 ≤ 2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((MI / c ^ 2) ^ 2 * (Bg ^ 2 * vK)))
    hL
  positivity

set_option maxHeartbeats 800000 in
/-- **Arithmetic core, sharp form**: `err5' ≤ 3 660 000 Λ²⁰ δ` (no power of `x⁻¹`). -/
theorem err5'_le (C : Ctx N Λ x y δ L) {A vK BI vI MM MI c Bg cD : ℝ} (hA : 0 ≤ A)
    (hA' : A ≤ Λ) (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI) (hBI' : BI ≤ Λ)
    (hw : 0 ≤ vI) (hw' : vI ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MM) (hM : MM ≤ Λ * x) (hMI0 : 0 ≤ MI)
    (hMI : MI ≤ Λ * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y) (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ)
    (hcD : 0 < cD) (hcDi : cD⁻¹ ≤ Λ ^ 2) :
    err5' N A vK BI vI MM MI c L Bg cD ≤ 3660000 * Λ ^ 20 * δ := by
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hu0 : 0 ≤ cD⁻¹ := (inv_pos.2 hcD).le
  have h1Λ : (1:ℝ) ≤ Λ := C.hΛ
  have hT := C.errT'_le hA hA' hv hv' hM0 hM hc hci hg hg'
  have hD := C.errD'_le hA hA' hv hv' hBI hBI' hw hw' hM0 hM hMI0 hMI hc hci hg hg'
  have hT1 := C.errT'_le hA hA' hv hv' hM0 hM hc hci zero_le_one h1Λ
  have hD1 := C.errD'_le hA hA' hv hv' hBI hBI' hw hw' hM0 hM hMI0 hMI hc hci zero_le_one h1Λ
  have hT0 := errT'_nonneg N hA hv hc hL0 hg hM0
  have hD0 := errD'_nonneg N hA hv hBI hw hc hL0 hg hM0 hMI0
  have hT10 := errT'_nonneg N hA hv hc hL0 zero_le_one hM0
  have hD10 := errD'_nonneg N hA hv hBI hw hc hL0 zero_le_one hM0 hMI0
  set a := errT' N A vK MM c L Bg + errD' N A vK BI vI MM MI c L Bg with ha
  set e1 := errT' N A vK MM c L 1 with he1
  set e' := errD' N A vK BI vI MM MI c L 1 with he'
  set B := Bg * MM * (1 / c) + (Bg * MI * (1 / c) + Bg * MM * (MI / c ^ 2)) with hBdef
  set Cc := 1 * MI * (1 / c) + 1 * MM * (MI / c ^ 2) with hCdef
  have m57 := C.monoΛ (i := 5) (k := 7) (by norm_num)
  have ha0 : a ≤ 1032 * (Λ ^ 7 * δ) := by linarith
  have ha00 : 0 ≤ a := by linarith
  have hB : B ≤ 3 * Λ ^ 5 := by
    have e : B = Bg * MM * c⁻¹ + Bg * MI * c⁻¹ + Bg * MM * MI * c⁻¹ ^ 2 := by rw [hBdef]; ring
    rw [e]
    have h1 : Bg * MM * c⁻¹ ≤ Λ * (Λ * x) * (Λ * y) := by gcongr
    have h2 : Bg * MI * c⁻¹ ≤ Λ * (Λ * x) * (Λ * y) := by gcongr
    have h3 : Bg * MM * MI * c⁻¹ ^ 2 ≤ Λ * (Λ * x) * (Λ * x) * (Λ * y) ^ 2 := by gcongr
    have e1' : Λ * (Λ * x) * (Λ * y) = Λ ^ 3 := by linear_combination (Λ ^ 3) * C.hxy
    have e2' : Λ * (Λ * x) * (Λ * x) * (Λ * y) ^ 2 = Λ ^ 5 := by
      linear_combination (Λ ^ 5 * (x * y + 1)) * C.hxy
    have m : Λ ^ 3 ≤ Λ ^ 5 := pow_le_pow_right₀ C.hΛ (by norm_num)
    linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hCc : Cc ≤ 2 * Λ ^ 4 := by
    have e : Cc = MI * c⁻¹ + MM * MI * c⁻¹ ^ 2 := by rw [hCdef]; ring
    rw [e]
    have h1 : MI * c⁻¹ ≤ (Λ * x) * (Λ * y) := by gcongr
    have h2 : MM * MI * c⁻¹ ^ 2 ≤ (Λ * x) * (Λ * x) * (Λ * y) ^ 2 := by gcongr
    have e1' : (Λ * x) * (Λ * y) = Λ ^ 2 := by linear_combination (Λ ^ 2) * C.hxy
    have e2' : (Λ * x) * (Λ * x) * (Λ * y) ^ 2 = Λ ^ 4 := by
      linear_combination (Λ ^ 4 * (x * y + 1)) * C.hxy
    have m : Λ ^ 2 ≤ Λ ^ 4 := pow_le_pow_right₀ C.hΛ (by norm_num)
    linarith
  have hCc0 : 0 ≤ Cc := by rw [hCdef]; positivity
  have he'1 : e' ≤ 880 * Λ ^ 7 := by
    have : Λ ^ 7 * δ ≤ Λ ^ 7 * 1 := mul_le_mul_of_nonneg_left C.hδ1 (by positivity)
    linarith
  have hCe : Cc + e' ≤ 882 * Λ ^ 7 := by
    have m : Λ ^ 4 ≤ Λ ^ 7 := pow_le_pow_right₀ C.hΛ (by norm_num)
    linarith
  have eE : err5' N A vK BI vI MM MI c L Bg cD
      = 2 * a * cD⁻¹ + 2 * B * e1 * cD⁻¹ ^ 2 + 4 * (a * (Cc + e') + B * e') * cD⁻¹ ^ 2
        + 6 * B * Cc * e1 * cD⁻¹ ^ 3 := by
    dsimp only [err5']; rw [ha, he1, he', hBdef, hCdef]; ring
  rw [eE]
  have t1 : 2 * a * cD⁻¹ ≤ 2 * (1032 * (Λ ^ 7 * δ)) * Λ ^ 2 := by gcongr
  have t2 : 2 * B * e1 * cD⁻¹ ^ 2 ≤ 2 * (3 * Λ ^ 5) * (152 * Λ ^ 5 * δ) * (Λ ^ 2) ^ 2 := by
    gcongr
  have t3 : 4 * (a * (Cc + e') + B * e') * cD⁻¹ ^ 2
      ≤ 4 * ((1032 * (Λ ^ 7 * δ)) * (882 * Λ ^ 7) + (3 * Λ ^ 5) * (880 * Λ ^ 7 * δ))
        * (Λ ^ 2) ^ 2 := by
    have hCe0 : 0 ≤ Cc + e' := by linarith
    gcongr
  have t4 : 6 * B * Cc * e1 * cD⁻¹ ^ 3 ≤ 6 * (3 * Λ ^ 5) * (2 * Λ ^ 4) * (152 * Λ ^ 5 * δ)
      * (Λ ^ 2) ^ 3 := by gcongr
  have m1 := C.monoΛ (i := 9) (k := 20) (by norm_num)
  have m2 := C.monoΛ (i := 14) (k := 20) (by norm_num)
  have m3 := C.monoΛ (i := 18) (k := 20) (by norm_num)
  have m4 := C.monoΛ (i := 16) (k := 20) (by norm_num)
  have r1 : 2 * (1032 * (Λ ^ 7 * δ)) * Λ ^ 2 = 2064 * (Λ ^ 9 * δ) := by ring
  have r2 : 2 * (3 * Λ ^ 5) * (152 * Λ ^ 5 * δ) * (Λ ^ 2) ^ 2 = 912 * (Λ ^ 14 * δ) := by ring
  have r3 : 4 * ((1032 * (Λ ^ 7 * δ)) * (882 * Λ ^ 7) + (3 * Λ ^ 5) * (880 * Λ ^ 7 * δ))
        * (Λ ^ 2) ^ 2 = 3640896 * (Λ ^ 18 * δ) + 10560 * (Λ ^ 16 * δ) := by ring
  have r4 : 6 * (3 * Λ ^ 5) * (2 * Λ ^ 4) * (152 * Λ ^ 5 * δ) * (Λ ^ 2) ^ 3
      = 5472 * (Λ ^ 20 * δ) := by ring
  have hP : 0 ≤ Λ ^ 20 * δ := by positivity
  linarith

/-- **Smallness, sharp form**, under `304 Λ⁷ δ ≤ 1`. -/
theorem small'_le (C : Ctx N Λ x y δ L) {A vK MM c cD : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MM) (hM : MM ≤ Λ * x) (hc : 0 < c)
    (hci : c⁻¹ ≤ Λ * y) (hcD : 0 < cD) (hcDi : cD⁻¹ ≤ Λ ^ 2) (hsm : 304 * Λ ^ 7 * δ ≤ 1) :
    dev N A vK L / c ≤ 1 / 2 ∧ errT' N A vK MM c L 1 / cD ≤ 1 / 2 := by
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hu0 : 0 ≤ cD⁻¹ := (inv_pos.2 hcD).le
  have m27 := C.monoΛ (i := 2) (k := 7) (by norm_num)
  have m57 := C.monoΛ (i := 5) (k := 7) (by norm_num)
  constructor
  · have hd := C.dev_K hA hA' hv hv'
    have hd0 := dev_nonneg N hA hv hL0
    rw [div_eq_mul_inv]
    have h1 : dev N A vK L * c⁻¹ ≤ (8 * Λ * x * δ) * (Λ * y) := by gcongr
    have e : (8 * Λ * x * δ) * (Λ * y) = 8 * (Λ ^ 2 * δ) := by
      linear_combination (8 * Λ ^ 2 * δ) * C.hxy
    linarith
  · have hT := C.errT'_le hA hA' hv hv' hM0 hM hc hci zero_le_one C.hΛ
    have hT0 := errT'_nonneg N hA hv hc hL0 zero_le_one hM0
    rw [div_eq_mul_inv]
    have h1 : errT' N A vK MM c L 1 * cD⁻¹ ≤ (152 * Λ ^ 5 * δ) * Λ ^ 2 := by gcongr
    have e : (152 * Λ ^ 5 * δ) * Λ ^ 2 = 152 * (Λ ^ 7 * δ) := by ring
    linarith

end Ctx

/-- The single constant `Λ` of the sharp rate:
`max{1, A, 2κA, 2B_f, √C_v, √C_v', q⁻¹, M₁, M_I}` with the `L¹` constants
`M₁ = profC A 1 0 d A_m r₀`, `M_I = profC (2κA) e⁻¹ 1 d A_m r₀`. -/
def sharpLam (d : ℕ) (Am r₀ A κ Bf q : ℝ) : ℝ :=
  max (max (max 1 A) (max (2 * κ * A) (2 * Bf)))
    (max (max (Real.sqrt (cV d Am r₀ A)) (Real.sqrt (cV' κ d Am r₀ A)))
      (max q⁻¹ (max (profC A 1 0 d Am r₀) (profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀))))

section LamFacts
variable (d : ℕ) (Am r₀ A κ Bf q : ℝ)
theorem slam_one : 1 ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
theorem slam_A : A ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
theorem slam_BI : 2 * κ * A ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
theorem slam_Bf : 2 * Bf ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
theorem slam_cV : Real.sqrt (cV d Am r₀ A) ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
theorem slam_cV' : Real.sqrt (cV' κ d Am r₀ A) ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
theorem slam_q : q⁻¹ ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
theorem slam_M : profC A 1 0 d Am r₀ ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
theorem slam_MI : profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀ ≤ sharpLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
end LamFacts

theorem sq_le_of_sqrt_le {v Λ : ℝ} (hv : 0 ≤ v) (h : Real.sqrt v ≤ Λ) : v ≤ Λ ^ 2 := by
  have h0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  calc v = Real.sqrt v ^ 2 := (Real.sq_sqrt hv).symm
    _ ≤ Λ ^ 2 := pow_le_pow_left₀ h0 h 2

/-- **(2)+(3) sharp, deterministic part.**  For `0 < ξ ≤ 1`, `L ≥ 1`, `c = q ξᵈ`,
`M = M₁ ξᵈ`, `M_I = M_I' ξᵈ`, `c_D = c/M`, and the single hypothesis `92416 Λ¹⁴ L ≤ N ξᵈ`:
both smallness conditions of `npoint_step5'` hold and `err5' ≤ 3 660 000 Λ²⁰ √(L/(N ξᵈ))`. -/
theorem rate_bounds' (N : ℕ) (hN : 0 < N) (d : ℕ) {Am r₀ ξ A κ Bf q L a b : ℝ} (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hA : 0 < A) (hκ : 0 ≤ κ) (hBf : 0 ≤ Bf)
    (hq : 0 < q) (hne : b ≠ a) (hL : 1 ≤ L)
    (hNL : 92416 * sharpLam d Am r₀ A κ Bf q ^ 14 * L ≤ N * ξ ^ d) :
    dev N A (vKern d Am r₀ ξ A) L / (q * ξ ^ d) ≤ 1 / 2 ∧
    errT' N A (vKern d Am r₀ ξ A) (profC A 1 0 d Am r₀ * ξ ^ d) (q * ξ ^ d) L 1
      / (q * ξ ^ d / (profC A 1 0 d Am r₀ * ξ ^ d)) ≤ 1 / 2 ∧
    err5' N A (vKern d Am r₀ ξ A) (2 * κ * A) (vInc κ d Am r₀ ξ A a b)
        (profC A 1 0 d Am r₀ * ξ ^ d) (profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀ * ξ ^ d)
        (q * ξ ^ d) L (2 * Bf) (q * ξ ^ d / (profC A 1 0 d Am r₀ * ξ ^ d))
      ≤ 3660000 * sharpLam d Am r₀ A κ Bf q ^ 20 * Real.sqrt (L / (N * ξ ^ d)) := by
  set Λ := sharpLam d Am r₀ A κ Bf q with hΛdef
  set x := ξ ^ d with hxdef
  set δ := Real.sqrt (L / (N * x)) with hδdef
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < x := pow_pos hξ d
  have hx1 : x ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hΛ : 1 ≤ Λ := slam_one d Am r₀ A κ Bf q
  have hΛ0 : 0 < Λ := by linarith
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδ : δ ^ 2 * (N * x) = L := by
    rw [hδdef, Real.sq_sqrt (by positivity)]; field_simp
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hP : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * x) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ 1 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((1 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hP] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ hΛ
    nlinarith
  have C : Ctx N Λ x x⁻¹ δ L :=
    { hN := hN, hΛ := hΛ, hx := hx, hx1 := hx1, hxy := mul_inv_cancel₀ hx.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL }
  have hv0 := vKern_nonneg d (r₀ := r₀) (A := A) hAm hξ
  have hw0 := vInc_nonneg κ d (r₀ := r₀) (A := A) (a := a) (b := b) hAm hξ
  have hv' : vKern d Am r₀ ξ A ≤ Λ ^ 2 * x :=
    (vKern_le d hAm hr₀ hξ).trans (mul_le_mul_of_nonneg_right
      (sq_le_of_sqrt_le (cV_nonneg d hAm hr₀) (slam_cV d Am r₀ A κ Bf q)) hx.le)
  have hw' : vInc κ d Am r₀ ξ A a b ≤ Λ ^ 2 * x :=
    (vInc_le κ d hAm hr₀ hξ hne).trans (mul_le_mul_of_nonneg_right
      (sq_le_of_sqrt_le (cV'_nonneg κ d hAm hr₀) (slam_cV' d Am r₀ A κ Bf q)) hx.le)
  have hM1 : 0 < profC A 1 0 d Am r₀ := profC_pos 0 d hA one_pos hAm hr₀
  have hM0 : 0 ≤ profC A 1 0 d Am r₀ * x := by positivity
  have hM : profC A 1 0 d Am r₀ * x ≤ Λ * x :=
    mul_le_mul_of_nonneg_right (slam_M d Am r₀ A κ Bf q) hx.le
  have hMI0 : 0 ≤ profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀ * x :=
    mul_nonneg (profC_nonneg 1 d (by positivity) (Real.exp_pos _) hAm hr₀) hx.le
  have hMI : profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀ * x ≤ Λ * x :=
    mul_le_mul_of_nonneg_right (slam_MI d Am r₀ A κ Bf q) hx.le
  have hc : 0 < q * x := by positivity
  have hci : (q * x)⁻¹ ≤ Λ * x⁻¹ := by
    rw [mul_inv]; exact mul_le_mul_of_nonneg_right (slam_q d Am r₀ A κ Bf q) (by positivity)
  have hcD : 0 < q * x / (profC A 1 0 d Am r₀ * x) := by positivity
  have hcDi : (q * x / (profC A 1 0 d Am r₀ * x))⁻¹ ≤ Λ ^ 2 := by
    rw [inv_div, div_eq_mul_inv]
    calc profC A 1 0 d Am r₀ * x * (q * x)⁻¹ ≤ (Λ * x) * (Λ * x⁻¹) :=
          mul_le_mul hM hci (by positivity) (by positivity)
      _ = Λ ^ 2 := by field_simp
  have hBI0 : 0 ≤ 2 * κ * A := by positivity
  have hsmall := C.small'_le hA.le (slam_A d Am r₀ A κ Bf q) hv0 hv' hM0 hM hc hci hcD hcDi hsm
  have he := C.err5'_le hA.le (slam_A d Am r₀ A κ Bf q) hv0 hv' hBI0 (slam_BI d Am r₀ A κ Bf q)
    hw0 hw' hM0 hM hMI0 hMI hc hci (by positivity) (slam_Bf d Am r₀ A κ Bf q) hcD hcDi
  exact ⟨hsmall.1, hsmall.2, he⟩

end CTG.NPointSharp

namespace CTG.NPointSharp

section ManifoldSharp

open Bundle Manifold CTG.ManifoldDistance

variable {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EE H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle EE (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {s : Set ℝ}

/-- **Steps 2–5 with the rate of the paper (bounded test function).**  Setting and HYPOTHESES as
`npoint_step5'` (upper growth at both times; `q ξᵈ ≤ q^τ`), with `ξ ≤ 1`, `L ≥ 1`, and the single
quantitative hypothesis `92416 Λ¹⁴ L ≤ N ξᵈ` (`Λ = sharpLam d A_m r₀ A κ B_f q`).  With probability at
least `1 − 15N·2e^{−L}`, for all `i < N` the difference quotient of the sample quotient differs from
the population one by at most `3 660 000 Λ²⁰ √(L/(N ξᵈ))`. -/
theorem npoint_step5_sharp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (f : M → ℝ) (hf : Measurable f) (Bf : ℝ) (hBf : 0 ≤ Bf) (hfb : ∀ x, |f x| ≤ Bf)
    (q : ℝ) (hq : 0 < q)
    (hqa : ∀ y, q * ξ ^ d ≤ popNorm G h ξ a m y) (hqb : ∀ y, q * ξ ^ d ≤ popNorm G h ξ b m y)
    (L : ℝ) (hL : 1 ≤ L)
    (hNL : 92416 * sharpLam d Am r₀ A G.κ Bf q ^ 14 * L ≤ N * ξ ^ d) :
    μ.real {ω | ∃ i < N,
        3660000 * sharpLam d Am r₀ A G.κ Bf q ^ 20 * Real.sqrt (L / (N * ξ ^ d))
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨hs1, hs2, he⟩ := rate_bounds' N hN d (a := a) (b := b) hAm hr₀ hξ hξ1 hA G.κ_nonneg
    hBf hq hne hL hNL
  have h5 := npoint_step5' G ha₀ hcont ha hb hab hne m X h_indep hX hlaw N hN d Am r₀ ξ hAm hr₀
    hξ hga hgb h h' A hA hder hbd hh hh0 f hf Bf hBf hfb (q * ξ ^ d) (by positivity) hqa hqb L
    (by linarith) hs1 hs2
  refine le_trans (measureReal_mono ?_) h5
  rintro ω ⟨i, hi, hlt⟩
  exact ⟨i, hi, lt_of_le_of_lt he hlt⟩

end ManifoldSharp

theorem exp_neg_three_log (N : ℕ) (hN : 0 < N) :
    15 * ((N : ℝ) * (2 * Real.exp (-(3 * Real.log N)))) = 30 / (N : ℝ) ^ 2 := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have e : Real.exp (-(3 * Real.log N)) = ((N : ℝ) ^ 3)⁻¹ := by
    rw [Real.exp_neg]; congr 1
    rw [show (3:ℝ) * Real.log N = ((3 : ℕ) : ℝ) * Real.log N by norm_num, ← Real.log_pow,
      Real.exp_log (by positivity)]
  rw [e]; field_simp; ring

theorem three_log_ge_one (N : ℕ) (hN : 2 ≤ N) : 1 ≤ 3 * Real.log N := by
  have h2 : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have := Real.log_two_gt_d9
  linarith

section Geom

open Bundle Manifold CTG.ManifoldDistance CTG.ManifoldVolume CTG.NPointGeom
open scoped Manifold ENNReal

universe u

variable {n : ℕ} {M : Type*} [EMetricSpace M] [ChartedSpace (Fin n → ℝ) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M]
  [IsContinuousRiemannianBundle (Fin n → ℝ) (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsRiemannianManifold 𝓘(ℝ, Fin n → ℝ) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [PreconnectedSpace M]

/-- **(3) Steps 2–5 with the rate of the paper and ALL geometric hypotheses discharged.**  Compact
connected Riemannian manifold modelled on `Fin n → ℝ`, `TimeMetric` continuous in the base point at
time `a`, sampling law `m₀ μH[n] ≤ m ≤ m₁ μH[n]` (`μH[n]` the Hausdorff measure; NOT identified with
the Riemannian volume), `s₀ > 0`.  There are `A_m ≥ 0`, `r₀ > 0`, `c_q > 0`, `ξ₀ ∈ (0,1]` (from
`CTG.NPointGeom.growth_two_times`, `popNorm_lower_two_times`) such that for every sample, every
`N ≥ 1`, `0 < ξ ≤ ξ₀`, profile `h ≥ 0` with `|h|, |h'| ≤ A e^{−t}` (`A > 0`), `h ≥ h₀ > 0` on
`[0, s₀]`, measurable `f` with `|f| ≤ B_f`, and `L ≥ 1` with `92416 Λ¹⁴ L ≤ N ξⁿ`
(`Λ = sharpLam n A_m r₀ A κ B_f (c_q h₀)`): with probability at least `1 − 15N·2e^{−L}`, for all
`i < N` the error is at most `3 660 000 Λ²⁰ √(L/(N ξⁿ))`. -/
theorem npoint_step5_sharp_geom {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁)
    (hlow : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ξ₀ ≤ 1 ∧
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 0 < N → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (h h' : ℝ → ℝ) (A h₀ : ℝ), 0 < A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
        (∀ t, 0 ≤ h t) → 0 < h₀ → (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) →
      ∀ (f : M → ℝ), Measurable f → ∀ Bf : ℝ, 0 ≤ Bf → (∀ x, |f x| ≤ Bf) →
      ∀ L : ℝ, 1 ≤ L →
      92416 * sharpLam n Am r₀ A G.κ Bf (cq * h₀) ^ 14 * L ≤ N * ξ ^ n →
      μ.real {ω | ∃ i < N,
        3660000 * sharpLam n Am r₀ A G.κ Bf (cq * h₀) ^ 20 * Real.sqrt (L / (N * ξ ^ n))
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
        ≤ 15 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨Am, hAm, r₀, hr₀, hga, hgb⟩ := growth_two_times G ha hb hcont m m₁ hm₁ hup
  obtain ⟨cq, hcq, ξ₀, hξ₀, hq⟩ := popNorm_lower_two_times G ha hb hcont m m₀ hm₀ hlow s₀ hs₀
  refine ⟨Am, hAm, r₀, hr₀, cq, hcq, min ξ₀ 1, lt_min hξ₀ one_pos, min_le_right _ _, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Bf hBf hfb L hL hNL
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have hqab := hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo ξ hξ (hξξ₀.trans (min_le_left _ _))
  exact npoint_step5_sharp G ha hcont ha hb hab hne m X h_indep hX hlaw N hN n Am r₀ ξ hAm hr₀
    hξ (hξξ₀.trans (min_le_right _ _)) hga hgb h h' A hA hder hbd hh hh0 f hf Bf hBf hfb
    (cq * h₀) (by positivity) (fun y => (hqab y).1) (fun y => (hqab y).2) L hL hNL

/-- **The `L = 3 log N` corollary**: under the hypotheses of `npoint_step5_sharp_geom` with `N ≥ 2`
and `92416 Λ¹⁴ · 3 log N ≤ N ξⁿ`, probability at least `1 − 30/N²` and error at most
`3 660 000 Λ²⁰ √(3 log N/(N ξⁿ))`. -/
theorem npoint_step5_sharp_geom_log {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁)
    (hlow : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ξ₀ ≤ 1 ∧
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 2 ≤ N → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (h h' : ℝ → ℝ) (A h₀ : ℝ), 0 < A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
        (∀ t, 0 ≤ h t) → 0 < h₀ → (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) →
      ∀ (f : M → ℝ), Measurable f → ∀ Bf : ℝ, 0 ≤ Bf → (∀ x, |f x| ≤ Bf) →
      92416 * sharpLam n Am r₀ A G.κ Bf (cq * h₀) ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n →
      μ.real {ω | ∃ i < N,
        3660000 * sharpLam n Am r₀ A G.κ Bf (cq * h₀) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
        ≤ 30 / (N : ℝ) ^ 2 := by
  obtain ⟨Am, hAm, r₀, hr₀, cq, hcq, ξ₀, hξ₀, hξ₀1, H⟩ :=
    npoint_step5_sharp_geom (M := M) G ha hb hcont hab hne m m₀ m₁ hm₀ hm₁ hlow hup s₀ hs₀
  refine ⟨Am, hAm, r₀, hr₀, cq, hcq, ξ₀, hξ₀, hξ₀1, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Bf hBf hfb hNL
  have hN0 : 0 < N := by omega
  rw [← exp_neg_three_log N hN0]
  exact H Ω μ X h_indep hX hlaw N hN0 ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Bf hBf hfb (3 * Real.log N) (three_log_ge_one N hN) hNL

end Geom

end CTG.NPointSharp
