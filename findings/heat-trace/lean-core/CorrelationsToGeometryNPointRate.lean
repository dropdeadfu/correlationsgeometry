/-
From Correlations to Geometry -- sixteenth Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the twelfth file `CorrelationsToGeometryNPoint.lean` and makes the error bound `err5` and the two
smallness conditions of `npoint_step5` explicit in the kernel scale.  RESULT, AND LIMITATION OF THE TWELFTH FILE:
with `δ' = √(L/(N ξ^d))` the bound proven there is of the order `δ' · ξ^{-8d}`, and its smallness conditions
need `N ξ^{5d} ≳ L` -- NOT the error `C δ'` under `N ξ^d ≳ L` of Proposition "dotLN-diff" of the paper.  The loss
comes from the definitions of the twelfth file (averages of |K g| bounded by suprema, denominator bounded below
by a quantity of order `ξ^d`), not from the paper.  Statements: closed bounds `vKern ≤ cV ξ^d`, `vInc ≤ cV' ξ^d`,
`dev_rate`; `rate_bounds`; `npoint_step5_rate`, `npoint_step5_rate_log` (probability ≥ 1 − 30/N² with L = 3 log N).
The geometric hypotheses of `npoint_step5` remain hypotheses here (they are discharged in the fifteenth file).
Check with `cd lean && ./check_npoint_rate.sh`.  No `sorry`, no `axiom`, no `native_decide`.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryNPoint

open MeasureTheory ProbabilityTheory Set
open CTG.NPoint

noncomputable section

namespace CTG.NPointRate

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

end CTG.NPointRate

namespace CTG.NPointRate

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

end CTG.NPointRate


namespace CTG.NPointRate

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

theorem err2_le (C : Ctx N Λ x y δ L) {A vK BI vI c : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI) (hBI' : BI ≤ Λ) (hw : 0 ≤ vI)
    (hw' : vI ≤ Λ ^ 2 * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y) :
    err2 N A vK BI vI c L ≤ 80 * Λ ^ 5 * y ^ 2 * δ := by
  unfold err2
  have hd := C.dev_K hA hA' hv hv'
  have hdI := C.dev_K hBI hBI' hw hw'
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have hd0 := dev_nonneg N hA hv hL0
  have hdI0 := dev_nonneg N hBI hw hL0
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have e : 4 * dev N BI vI L / c ^ 2 + 6 * BI * (dev N A vK L / c) / c ^ 2
      = 4 * (dev N BI vI L * c⁻¹ ^ 2) + 6 * (BI * dev N A vK L * c⁻¹ ^ 3) := by ring
  rw [e]
  have := C.Λ0; have := C.hx; have := C.hδ0; have := C.y_pos
  have h1 : dev N BI vI L * c⁻¹ ^ 2 ≤ (8 * Λ * x * δ) * (Λ * y) ^ 2 := by gcongr
  have h2 : BI * dev N A vK L * c⁻¹ ^ 3 ≤ Λ * (8 * Λ * x * δ) * (Λ * y) ^ 3 := by gcongr
  have m1 := C.mono (i := 3) (j := 1) (k := 5) (l := 2) (by norm_num) (by norm_num)
  have e1 : (8 * Λ * x * δ) * (Λ * y) ^ 2 = 8 * (Λ ^ 3 * y ^ 1 * δ) := by
    linear_combination (8 * Λ ^ 3 * y * δ) * C.hxy
  have e2 : Λ * (8 * Λ * x * δ) * (Λ * y) ^ 3 = 8 * (Λ ^ 5 * y ^ 2 * δ) := by
    linear_combination (8 * Λ ^ 5 * y ^ 2 * δ) * C.hxy
  nlinarith

/-- Bracket `B Bg + dev(B Bg, Bg² v)` of `errT`/`errD`: at most `9 Λ²`. -/
theorem bracket_le (C : Ctx N Λ x y δ L) {B v Bg : ℝ} (hB : 0 ≤ B) (hB' : B ≤ Λ) (hv : 0 ≤ v)
    (hv' : v ≤ Λ ^ 2 * x) (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ) :
    B * Bg + dev N (B * Bg) (Bg ^ 2 * v) L ≤ 9 * Λ ^ 2 := by
  have := C.Λ0; have hx := C.hx; have := C.hδ0
  have hBB : B * Bg ≤ Λ ^ 2 := by nlinarith [mul_le_mul hB' hg' hg C.Λ0]
  have hg2 : Bg ^ 2 ≤ Λ ^ 2 := by gcongr
  have hvs : Bg ^ 2 * v * x ≤ (Λ ^ 2 * x) ^ 2 := by
    have := mul_le_mul hg2 hv' hv (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right this hx.le]
  have h := dev_le' N C.hN (mul_nonneg hB hg) (by positivity) C.hL C.hx C.hδ0 C.hδ hBB
    (by positivity) hvs
  have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [C.hδ1]
  have h3 : 6 * Λ ^ 2 * x * δ ^ 2 ≤ 6 * Λ ^ 2 := by
    have : x * δ ^ 2 ≤ 1 := by nlinarith [C.hx1]
    nlinarith
  have h4 : 2 * δ * (Λ ^ 2 * x) ≤ 2 * Λ ^ 2 := by
    have : δ * x ≤ 1 := by nlinarith [C.hx1, C.hδ1]
    nlinarith
  linarith

theorem errT_le (C : Ctx N Λ x y δ L) {A vK c Bg : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y)
    (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ) :
    errT N A vK c L Bg ≤ 152 * Λ ^ 5 * y * δ := by
  unfold errT
  have he1 := C.err1_le hA hA' hv hv' hc hci
  have hbr := C.bracket_le hA hA' hv hv' hg hg'
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have he10 : 0 ≤ err1 N A vK c L := by
    unfold err1; have := dev_nonneg N hA hv hL0; positivity
  have hbr0 : 0 ≤ A * Bg + dev N (A * Bg) (Bg ^ 2 * vK) L := by
    have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL0; positivity
  -- second dev
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
    nlinarith
  have hprod : err1 N A vK c L * (A * Bg + dev N (A * Bg) (Bg ^ 2 * vK) L)
      ≤ (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2) := mul_le_mul he1 hbr hbr0 (by positivity)
  have m1 := C.mono (i := 3) (j := 0) (k := 5) (l := 1) (by norm_num) (by norm_num)
  nlinarith

set_option maxHeartbeats 800000 in
theorem errD_le (C : Ctx N Λ x y δ L) {A vK BI vI c Bg : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI) (hBI' : BI ≤ Λ) (hw : 0 ≤ vI)
    (hw' : vI ≤ Λ ^ 2 * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y) (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ) :
    errD N A vK BI vI c L Bg ≤ 880 * Λ ^ 7 * y ^ 2 * δ := by
  unfold errD
  have he1 := C.err1_le hA hA' hv hv' hc hci
  have he2 := C.err2_le hA hA' hv hv' hBI hBI' hw hw' hc hci
  have hbrI := C.bracket_le hBI hBI' hw hw' hg hg'
  have hbr := C.bracket_le hA hA' hv hv' hg hg'
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have he10 : 0 ≤ err1 N A vK c L := by
    unfold err1; have := dev_nonneg N hA hv hL0; positivity
  have he20 : 0 ≤ err2 N A vK BI vI c L := by
    unfold err2; have := dev_nonneg N hA hv hL0; have := dev_nonneg N hBI hw hL0; positivity
  have hbr0 : 0 ≤ A * Bg + dev N (A * Bg) (Bg ^ 2 * vK) L := by
    have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL0; positivity
  have hbrI0 : 0 ≤ BI * Bg + dev N (BI * Bg) (Bg ^ 2 * vI) L := by
    have := dev_nonneg N (mul_nonneg hBI hg) (by positivity : 0 ≤ Bg ^ 2 * vI) hL0; positivity
  have hB2 : BI * Bg * (1 / c) + A * Bg * (BI / c ^ 2) ≤ 2 * Λ ^ 5 * y ^ 2 := by
    have e : BI * Bg * (1 / c) + A * Bg * (BI / c ^ 2) = BI * Bg * c⁻¹ + A * Bg * BI * c⁻¹ ^ 2 := by
      ring
    rw [e]
    have h1 : BI * Bg * c⁻¹ ≤ Λ * Λ * (Λ * y) := by gcongr
    have h2 : A * Bg * BI * c⁻¹ ^ 2 ≤ Λ * Λ * Λ * (Λ * y) ^ 2 := by gcongr
    have m := C.mono0 (i := 3) (j := 1) (k := 5) (l := 2) (by norm_num) (by norm_num)
    linarith
  have hv2 : (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((BI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) * x
      ≤ (2 * Λ ^ 5 * y) ^ 2 := by
    have e : (2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((BI / c ^ 2) ^ 2 * (Bg ^ 2 * vK))) * x
        = 2 * (c⁻¹ ^ 2 * (Bg ^ 2 * vI) * x) + 2 * (BI ^ 2 * c⁻¹ ^ 4 * (Bg ^ 2 * vK) * x) := by ring
    rw [e]
    have h1 : c⁻¹ ^ 2 * (Bg ^ 2 * vI) * x ≤ (Λ * y) ^ 2 * (Λ ^ 2 * (Λ ^ 2 * x)) * x := by gcongr
    have h2 : BI ^ 2 * c⁻¹ ^ 4 * (Bg ^ 2 * vK) * x
        ≤ Λ ^ 2 * (Λ * y) ^ 4 * (Λ ^ 2 * (Λ ^ 2 * x)) * x := by gcongr
    have e1 : (Λ * y) ^ 2 * (Λ ^ 2 * (Λ ^ 2 * x)) * x = Λ ^ 6 := by
      linear_combination (Λ ^ 6 * (x * y + 1)) * C.hxy
    have e2 : Λ ^ 2 * (Λ * y) ^ 4 * (Λ ^ 2 * (Λ ^ 2 * x)) * x = Λ ^ 10 * y ^ 2 := by
      linear_combination (Λ ^ 10 * y ^ 2 * (x * y + 1)) * C.hxy
    have m := C.mono0 (i := 6) (j := 0) (k := 10) (l := 2) (by norm_num) (by norm_num)
    linarith
  have hd2 := dev_le' N C.hN (by positivity) (by positivity) C.hL C.hx C.hδ0 C.hδ hB2
    (by positivity) hv2
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [C.hδ1]
  have h3 : 6 * (2 * Λ ^ 5 * y ^ 2) * x * δ ^ 2 ≤ 12 * Λ ^ 5 * y * δ := by
    have e : 6 * (2 * Λ ^ 5 * y ^ 2) * x * δ ^ 2 = 12 * Λ ^ 5 * y * δ ^ 2 := by
      linear_combination (12 * Λ ^ 5 * y * δ ^ 2) * C.hxy
    rw [e]; have : 0 ≤ Λ ^ 5 * y := by positivity
    have := mul_le_mul_of_nonneg_left hδ2 this
    linarith
  have hp1 : err1 N A vK c L * (BI * Bg + dev N (BI * Bg) (Bg ^ 2 * vI) L)
      ≤ (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2) := mul_le_mul he1 hbrI hbrI0 (by positivity)
  have hp2 : err2 N A vK BI vI c L * (A * Bg + dev N (A * Bg) (Bg ^ 2 * vK) L)
      ≤ (80 * Λ ^ 5 * y ^ 2 * δ) * (9 * Λ ^ 2) := mul_le_mul he2 hbr hbr0 (by positivity)
  have m1 := C.mono (i := 5) (j := 1) (k := 7) (l := 2) (by norm_num) (by norm_num)
  linarith

end Ctx

end CTG.NPointRate


namespace CTG.NPointRate

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

end CTG.NPointRate


namespace CTG.NPointRate

theorem errT_nonneg (N : ℕ) {A vK c L Bg : ℝ} (hA : 0 ≤ A) (hv : 0 ≤ vK) (hc : 0 < c)
    (hL : 0 ≤ L) (hg : 0 ≤ Bg) : 0 ≤ errT N A vK c L Bg := by
  unfold errT err1
  have := dev_nonneg N hA hv hL
  have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL
  have := dev_nonneg N (by positivity : 0 ≤ A * Bg * (1 / c))
    (by positivity : 0 ≤ (1 / c) ^ 2 * (Bg ^ 2 * vK)) hL
  positivity

theorem errD_nonneg (N : ℕ) {A vK BI vI c L Bg : ℝ} (hA : 0 ≤ A) (hv : 0 ≤ vK) (hBI : 0 ≤ BI)
    (hw : 0 ≤ vI) (hc : 0 < c) (hL : 0 ≤ L) (hg : 0 ≤ Bg) : 0 ≤ errD N A vK BI vI c L Bg := by
  unfold errD err1 err2
  have := dev_nonneg N hA hv hL
  have := dev_nonneg N hBI hw hL
  have := dev_nonneg N (mul_nonneg hA hg) (by positivity : 0 ≤ Bg ^ 2 * vK) hL
  have := dev_nonneg N (mul_nonneg hBI hg) (by positivity : 0 ≤ Bg ^ 2 * vI) hL
  have := dev_nonneg N (by positivity : 0 ≤ BI * Bg * (1 / c) + A * Bg * (BI / c ^ 2))
    (by positivity : 0 ≤ 2 * ((1 / c) ^ 2 * (Bg ^ 2 * vI)) + 2 * ((BI / c ^ 2) ^ 2 * (Bg ^ 2 * vK)))
    hL
  positivity

namespace Ctx

variable {N : ℕ} {Λ x y δ L : ℝ}

set_option maxHeartbeats 800000 in
/-- **The arithmetic core of (3)**: in the context `Ctx`, with `A, 2κA ≤ Λ`, `v_K, v_I ≤ Λ² x`,
`c⁻¹ ≤ Λ y`, `c_D⁻¹ ≤ Λ² y`, `0 ≤ B_g ≤ Λ`: `err5 ≤ 3 660 000 Λ²⁰ y⁸ δ`. -/
theorem err5_le (C : Ctx N Λ x y δ L) {A vK BI vI c Bg cD : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI) (hBI' : BI ≤ Λ) (hw : 0 ≤ vI)
    (hw' : vI ≤ Λ ^ 2 * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y) (hg : 0 ≤ Bg) (hg' : Bg ≤ Λ)
    (hcD : 0 < cD) (hcDi : cD⁻¹ ≤ Λ ^ 2 * y) :
    err5 N A vK BI vI c L Bg cD ≤ 3660000 * Λ ^ 20 * y ^ 8 * δ := by
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos; have hy1 := C.y1
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hu0 : 0 ≤ cD⁻¹ := (inv_pos.2 hcD).le
  have h1Λ : (1:ℝ) ≤ Λ := C.hΛ
  -- components
  have hT := C.errT_le hA hA' hv hv' hc hci hg hg'
  have hD := C.errD_le hA hA' hv hv' hBI hBI' hw hw' hc hci hg hg'
  have hT1 := C.errT_le hA hA' hv hv' hc hci zero_le_one h1Λ
  have hD1 := C.errD_le hA hA' hv hv' hBI hBI' hw hw' hc hci zero_le_one h1Λ
  have hT0 := errT_nonneg N hA hv hc hL0 hg
  have hD0 := errD_nonneg N hA hv hBI hw hc hL0 hg
  have hT10 := errT_nonneg N hA hv hc hL0 zero_le_one
  have hD10 := errD_nonneg N hA hv hBI hw hc hL0 zero_le_one
  set a := errT N A vK c L Bg + errD N A vK BI vI c L Bg with ha
  set e1 := errT N A vK c L 1 with he1
  set e' := errD N A vK BI vI c L 1 with he'
  set B := A * Bg * (1 / c) + (BI * Bg * (1 / c) + A * Bg * (BI / c ^ 2)) with hBdef
  set Cc := BI * 1 * (1 / c) + A * 1 * (BI / c ^ 2) with hCdef
  have hmono1 := C.mono (i := 5) (j := 1) (k := 7) (l := 2) (by norm_num) (by norm_num)
  have ha0 : a ≤ 1032 * (Λ ^ 7 * y ^ 2 * δ) := by
    have : 152 * Λ ^ 5 * y * δ ≤ 152 * (Λ ^ 7 * y ^ 2 * δ) := by
      have := hmono1; simp only [pow_one] at this; linarith
    linarith
  have ha00 : 0 ≤ a := by linarith
  have hB : B ≤ 3 * (Λ ^ 5 * y ^ 2) := by
    have e : B = A * Bg * c⁻¹ + BI * Bg * c⁻¹ + A * Bg * BI * c⁻¹ ^ 2 := by rw [hBdef]; ring
    rw [e]
    have h1 : A * Bg * c⁻¹ ≤ Λ * Λ * (Λ * y) := by gcongr
    have h2 : BI * Bg * c⁻¹ ≤ Λ * Λ * (Λ * y) := by gcongr
    have h3 : A * Bg * BI * c⁻¹ ^ 2 ≤ Λ * Λ * Λ * (Λ * y) ^ 2 := by gcongr
    have m := C.mono0 (i := 3) (j := 1) (k := 5) (l := 2) (by norm_num) (by norm_num)
    linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hCc : Cc ≤ 2 * (Λ ^ 4 * y ^ 2) := by
    have e : Cc = BI * c⁻¹ + A * BI * c⁻¹ ^ 2 := by rw [hCdef]; ring
    rw [e]
    have h1 : BI * c⁻¹ ≤ Λ * (Λ * y) := by gcongr
    have h2 : A * BI * c⁻¹ ^ 2 ≤ Λ * Λ * (Λ * y) ^ 2 := by gcongr
    have m := C.mono0 (i := 2) (j := 1) (k := 4) (l := 2) (by norm_num) (by norm_num)
    linarith
  have hCc0 : 0 ≤ Cc := by rw [hCdef]; positivity
  have he'1 : e' ≤ 880 * (Λ ^ 7 * y ^ 2) := by
    have : Λ ^ 7 * y ^ 2 * δ ≤ Λ ^ 7 * y ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left C.hδ1 (by positivity)
    linarith
  have hCe : Cc + e' ≤ 882 * (Λ ^ 7 * y ^ 2) := by
    have m := C.mono0 (i := 4) (j := 2) (k := 7) (l := 2) (by norm_num) (by norm_num)
    linarith
  -- assemble
  have eE : err5 N A vK BI vI c L Bg cD
      = 2 * a * cD⁻¹ + 2 * B * e1 * cD⁻¹ ^ 2 + 4 * (a * (Cc + e') + B * e') * cD⁻¹ ^ 2
        + 6 * B * Cc * e1 * cD⁻¹ ^ 3 := by
    dsimp only [err5]; rw [ha, he1, he', hBdef, hCdef]; ring
  rw [eE]
  have t1 : 2 * a * cD⁻¹ ≤ 2 * (1032 * (Λ ^ 7 * y ^ 2 * δ)) * (Λ ^ 2 * y) := by gcongr
  have t2 : 2 * B * e1 * cD⁻¹ ^ 2 ≤ 2 * (3 * (Λ ^ 5 * y ^ 2)) * (152 * Λ ^ 5 * y * δ)
      * (Λ ^ 2 * y) ^ 2 := by gcongr
  have t3 : 4 * (a * (Cc + e') + B * e') * cD⁻¹ ^ 2
      ≤ 4 * ((1032 * (Λ ^ 7 * y ^ 2 * δ)) * (882 * (Λ ^ 7 * y ^ 2))
        + (3 * (Λ ^ 5 * y ^ 2)) * (880 * Λ ^ 7 * y ^ 2 * δ)) * (Λ ^ 2 * y) ^ 2 := by
    have e'0 : 0 ≤ e' := hD10
    have hCe0 : 0 ≤ Cc + e' := by linarith
    gcongr
  have t4 : 6 * B * Cc * e1 * cD⁻¹ ^ 3 ≤ 6 * (3 * (Λ ^ 5 * y ^ 2)) * (2 * (Λ ^ 4 * y ^ 2))
      * (152 * Λ ^ 5 * y * δ) * (Λ ^ 2 * y) ^ 3 := by gcongr
  have m1 := C.mono (i := 9) (j := 3) (k := 20) (l := 8) (by norm_num) (by norm_num)
  have m2 := C.mono (i := 14) (j := 5) (k := 20) (l := 8) (by norm_num) (by norm_num)
  have m3 := C.mono (i := 18) (j := 6) (k := 20) (l := 8) (by norm_num) (by norm_num)
  have m4 := C.mono (i := 16) (j := 6) (k := 20) (l := 8) (by norm_num) (by norm_num)
  have r1 : 2 * (1032 * (Λ ^ 7 * y ^ 2 * δ)) * (Λ ^ 2 * y) = 2064 * (Λ ^ 9 * y ^ 3 * δ) := by ring
  have r2 : 2 * (3 * (Λ ^ 5 * y ^ 2)) * (152 * Λ ^ 5 * y * δ) * (Λ ^ 2 * y) ^ 2
      = 912 * (Λ ^ 14 * y ^ 5 * δ) := by ring
  have r3 : 4 * ((1032 * (Λ ^ 7 * y ^ 2 * δ)) * (882 * (Λ ^ 7 * y ^ 2))
        + (3 * (Λ ^ 5 * y ^ 2)) * (880 * Λ ^ 7 * y ^ 2 * δ)) * (Λ ^ 2 * y) ^ 2
      = 3640896 * (Λ ^ 18 * y ^ 6 * δ) + 10560 * (Λ ^ 16 * y ^ 6 * δ) := by ring
  have r4 : 6 * (3 * (Λ ^ 5 * y ^ 2)) * (2 * (Λ ^ 4 * y ^ 2)) * (152 * Λ ^ 5 * y * δ)
      * (Λ ^ 2 * y) ^ 3 = 5472 * (Λ ^ 20 * y ^ 8 * δ) := by ring
  have hP : 0 ≤ Λ ^ 20 * y ^ 8 * δ := by positivity
  linarith

/-- **The smallness conditions of (2)** in the context, under `304 Λ⁷ δ ≤ x²`. -/
theorem small_le (C : Ctx N Λ x y δ L) {A vK c cD : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y)
    (hcD : 0 < cD) (hcDi : cD⁻¹ ≤ Λ ^ 2 * y) (hsm : 304 * Λ ^ 7 * δ ≤ x ^ 2) :
    dev N A vK L / c ≤ 1 / 2 ∧ errT N A vK c L 1 / cD ≤ 1 / 2 := by
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have := C.y_pos
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hu0 : 0 ≤ cD⁻¹ := (inv_pos.2 hcD).le
  have hΛ7 : Λ ^ 2 ≤ Λ ^ 7 := pow_le_pow_right₀ C.hΛ (by norm_num)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [C.hx1]
  constructor
  · have hd := C.dev_K hA hA' hv hv'
    have hd0 := dev_nonneg N hA hv hL0
    rw [div_eq_mul_inv]
    have h1 : dev N A vK L * c⁻¹ ≤ (8 * Λ * x * δ) * (Λ * y) := by gcongr
    have e : (8 * Λ * x * δ) * (Λ * y) = 8 * Λ ^ 2 * δ := by
      linear_combination (8 * Λ ^ 2 * δ) * C.hxy
    have : Λ ^ 2 * δ ≤ Λ ^ 7 * δ := by nlinarith
    nlinarith
  · have hT := C.errT_le hA hA' hv hv' hc hci zero_le_one C.hΛ
    have hT0 := errT_nonneg N hA hv hc hL0 zero_le_one
    rw [div_eq_mul_inv]
    have h1 : errT N A vK c L 1 * cD⁻¹ ≤ (152 * Λ ^ 5 * y * δ) * (Λ ^ 2 * y) := by gcongr
    have e : (152 * Λ ^ 5 * y * δ) * (Λ ^ 2 * y) = 152 * (Λ ^ 7 * δ) * y ^ 2 := by ring
    have hy2 : x ^ 2 * y ^ 2 = 1 := by rw [← mul_pow, C.hxy, one_pow]
    have : 304 * Λ ^ 7 * δ * y ^ 2 ≤ x ^ 2 * y ^ 2 :=
      mul_le_mul_of_nonneg_right hsm (by positivity)
    nlinarith

end Ctx

end CTG.NPointRate


namespace CTG.NPointRate

/-- The single constant `Λ` of the rate statement:
`Λ = max{1, A, 2κA, 2B_f, √C_v, √C_v', q⁻¹}` (`q = c_q h₀`, the lower normalisation constant). -/
def rateLam (d : ℕ) (Am r₀ A κ Bf q : ℝ) : ℝ :=
  max (max (max 1 A) (max (2 * κ * A) (2 * Bf)))
    (max (max (Real.sqrt (cV d Am r₀ A)) (Real.sqrt (cV' κ d Am r₀ A))) q⁻¹)

section LamFacts
variable (d : ℕ) (Am r₀ A κ Bf q : ℝ)
theorem lam_one : 1 ≤ rateLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
theorem lam_A : A ≤ rateLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
theorem lam_BI : 2 * κ * A ≤ rateLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
theorem lam_Bf : 2 * Bf ≤ rateLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
theorem lam_cV : Real.sqrt (cV d Am r₀ A) ≤ rateLam d Am r₀ A κ Bf q :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
theorem lam_cV' : Real.sqrt (cV' κ d Am r₀ A) ≤ rateLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
theorem lam_q : q⁻¹ ≤ rateLam d Am r₀ A κ Bf q :=
  (le_max_right _ _).trans (le_max_right _ _)
end LamFacts

theorem sq_le_of_sqrt_le {v Λ : ℝ} (hv : 0 ≤ v) (h : Real.sqrt v ≤ Λ) : v ≤ Λ ^ 2 := by
  have h0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  calc v = Real.sqrt v ^ 2 := (Real.sq_sqrt hv).symm
    _ ≤ Λ ^ 2 := pow_le_pow_left₀ h0 h 2

/-- **(2)+(3), deterministic part.**  For `0 < ξ ≤ 1`, `L ≥ 1`, `c = q ξᵈ` and the single
quantitative hypothesis `92416 Λ¹⁴ L ≤ N ξ^{5d}`, both smallness conditions of `npoint_step5`
hold and `err5 ≤ 3 660 000 Λ²⁰ δ'_L / ξ^{8d}` with `δ'_L = √(L/(N ξᵈ))`. -/
theorem rate_bounds (N : ℕ) (hN : 0 < N) (d : ℕ) {Am r₀ ξ A κ Bf q L a b : ℝ} (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hA : 0 < A) (hκ : 0 ≤ κ) (hBf : 0 ≤ Bf)
    (hq : 0 < q) (hne : b ≠ a) (hL : 1 ≤ L)
    (hNL : 92416 * rateLam d Am r₀ A κ Bf q ^ 14 * L ≤ N * (ξ ^ d) ^ 5) :
    dev N A (vKern d Am r₀ ξ A) L / (q * ξ ^ d) ≤ 1 / 2 ∧
    errT N A (vKern d Am r₀ ξ A) (q * ξ ^ d) L 1 / (q * ξ ^ d / A) ≤ 1 / 2 ∧
    err5 N A (vKern d Am r₀ ξ A) (2 * κ * A) (vInc κ d Am r₀ ξ A a b) (q * ξ ^ d) L (2 * Bf)
        (q * ξ ^ d / A)
      ≤ 3660000 * rateLam d Am r₀ A κ Bf q ^ 20 * Real.sqrt (L / (N * ξ ^ d)) / (ξ ^ d) ^ 8 := by
  set Λ := rateLam d Am r₀ A κ Bf q with hΛdef
  set x := ξ ^ d with hxdef
  set δ := Real.sqrt (L / (N * x)) with hδdef
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < x := pow_pos hξ d
  have hx1 : x ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hΛ : 1 ≤ Λ := lam_one d Am r₀ A κ Bf q
  have hΛ0 : 0 < Λ := by linarith
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδ : δ ^ 2 * (N * x) = L := by
    rw [hδdef, Real.sq_sqrt (by positivity)]; field_simp
  have hsm : 304 * Λ ^ 7 * δ ≤ x ^ 2 := by
    have hP : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * x) ≤ (x ^ 2 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ x ^ 2 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((x ^ 2 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = x ^ 2 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hP] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ hΛ
    have : x ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have C : Ctx N Λ x x⁻¹ δ L :=
    { hN := hN, hΛ := hΛ, hx := hx, hx1 := hx1, hxy := mul_inv_cancel₀ hx.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL }
  have hv0 := vKern_nonneg d (r₀ := r₀) (A := A) hAm hξ
  have hw0 := vInc_nonneg κ d (r₀ := r₀) (A := A) (a := a) (b := b) hAm hξ
  have hv' : vKern d Am r₀ ξ A ≤ Λ ^ 2 * x :=
    (vKern_le d hAm hr₀ hξ).trans (mul_le_mul_of_nonneg_right
      (sq_le_of_sqrt_le (cV_nonneg d hAm hr₀) (lam_cV d Am r₀ A κ Bf q)) hx.le)
  have hw' : vInc κ d Am r₀ ξ A a b ≤ Λ ^ 2 * x :=
    (vInc_le κ d hAm hr₀ hξ hne).trans (mul_le_mul_of_nonneg_right
      (sq_le_of_sqrt_le (cV'_nonneg κ d hAm hr₀) (lam_cV' d Am r₀ A κ Bf q)) hx.le)
  have hc : 0 < q * x := by positivity
  have hci : (q * x)⁻¹ ≤ Λ * x⁻¹ := by
    rw [mul_inv]; exact mul_le_mul_of_nonneg_right (lam_q d Am r₀ A κ Bf q) (by positivity)
  have hcD : 0 < q * x / A := by positivity
  have hcDi : (q * x / A)⁻¹ ≤ Λ ^ 2 * x⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
    calc A * (q * x)⁻¹ ≤ Λ * (Λ * x⁻¹) :=
          mul_le_mul (lam_A d Am r₀ A κ Bf q) hci (by positivity) hΛ0.le
      _ = Λ ^ 2 * x⁻¹ := by ring
  have hBI0 : 0 ≤ 2 * κ * A := by positivity
  have hsmall := C.small_le hA.le (lam_A d Am r₀ A κ Bf q) hv0 hv' hc hci hcD hcDi hsm
  have he := C.err5_le hA.le (lam_A d Am r₀ A κ Bf q) hv0 hv' hBI0 (lam_BI d Am r₀ A κ Bf q)
    hw0 hw' hc hci (by positivity) (lam_Bf d Am r₀ A κ Bf q) hcD hcDi
  refine ⟨hsmall.1, hsmall.2, ?_⟩
  have e : 3660000 * Λ ^ 20 * δ / x ^ 8 = 3660000 * Λ ^ 20 * x⁻¹ ^ 8 * δ := by
    rw [inv_pow]; field_simp
  rw [e]; exact he

end CTG.NPointRate


namespace CTG.NPointRate

section ManifoldRate

open Bundle Manifold CTG.ManifoldDistance

variable {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EE H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle EE (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {s : Set ℝ}

/-- **(2)+(3) Steps 2–5 of `prop:dotLN-diff` with a rate.**  Same setting and hypotheses as
`CTG.NPoint.npoint_step5` (in particular the HYPOTHESES `hga`, `hgb` — upper volume growth at both
times — and `hqa`, `hqb` — lower bound `q ξᵈ` of the population normalisations; both are discharged
on a compact Riemannian manifold by `CTG.NPointGeom.growth_two_times` / `popNorm_lower_two_times`),
but the two smallness conditions are replaced by the single quantitative hypothesis
`92416 Λ¹⁴ L ≤ N ξ^{5d}` (and `ξ ≤ 1`, `L ≥ 1`), `Λ = rateLam d A_m r₀ A κ B_f q`.  Conclusion: with
probability at least `1 − 15N·2e^{−L}`, for all `i < N` the difference quotient of the sample quotient
differs from the population one by at most `3 660 000 Λ²⁰ √(L/(N ξᵈ)) / ξ^{8d}`. -/
theorem npoint_step5_rate {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
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
    (hNL : 92416 * rateLam d Am r₀ A G.κ Bf q ^ 14 * L ≤ N * (ξ ^ d) ^ 5) :
    μ.real {ω | ∃ i < N,
        3660000 * rateLam d Am r₀ A G.κ Bf q ^ 20 * Real.sqrt (L / (N * ξ ^ d)) / (ξ ^ d) ^ 8
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨hs1, hs2, he⟩ := rate_bounds N hN d (a := a) (b := b) hAm hr₀ hξ hξ1 hA G.κ_nonneg hBf
    hq hne hL hNL
  have h5 := npoint_step5 G ha₀ hcont ha hb hab hne m X h_indep hX hlaw N hN d Am r₀ ξ hAm hr₀ hξ
    hga hgb h h' A hA hder hbd hh hh0 f hf Bf hBf hfb (q * ξ ^ d) (by positivity) hqa hqb L
    (by linarith) hs1 hs2
  refine le_trans (measureReal_mono ?_) h5
  rintro ω ⟨i, hi, hlt⟩
  exact ⟨i, hi, lt_of_le_of_lt he hlt⟩

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

/-- **(3) with `L = 3 log N`**: probability at least `1 − 30/N²`, error at most
`3 660 000 Λ²⁰ √(3 log N/(N ξᵈ)) / ξ^{8d}`, under `92416 Λ¹⁴ · 3 log N ≤ N ξ^{5d}`, `N ≥ 2`. -/
theorem npoint_step5_rate_log {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 2 ≤ N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (f : M → ℝ) (hf : Measurable f) (Bf : ℝ) (hBf : 0 ≤ Bf) (hfb : ∀ x, |f x| ≤ Bf)
    (q : ℝ) (hq : 0 < q)
    (hqa : ∀ y, q * ξ ^ d ≤ popNorm G h ξ a m y) (hqb : ∀ y, q * ξ ^ d ≤ popNorm G h ξ b m y)
    (hNL : 92416 * rateLam d Am r₀ A G.κ Bf q ^ 14 * (3 * Real.log N) ≤ N * (ξ ^ d) ^ 5) :
    μ.real {ω | ∃ i < N,
        3660000 * rateLam d Am r₀ A G.κ Bf q ^ 20 * Real.sqrt (3 * Real.log N / (N * ξ ^ d))
          / (ξ ^ d) ^ 8
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
      ≤ 30 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  rw [← exp_neg_three_log N hN0]
  exact npoint_step5_rate G ha₀ hcont ha hb hab hne m X h_indep hX hlaw N hN0 d Am r₀ ξ hAm hr₀
    hξ hξ1 hga hgb h h' A hA hder hbd hh hh0 f hf Bf hBf hfb q hq hqa hqb (3 * Real.log N)
    (three_log_ge_one N hN) hNL

end ManifoldRate

end CTG.NPointRate
