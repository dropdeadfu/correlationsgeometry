/-
Fifty-fourth file (Mathlib only): the power series of `1 − √(1−s)` and the sum over the powers for one Fourier mode.
Namespace `CTG.SqrtSeries`; check with `./check_sqrt_series.sh`.
(1) `g x k = catalan k · x^k`; `partial_le_two`, `g_summable`, `g_functional` (`C = 1 + x C²` for `0 ≤ x ≤ 1/4`,
from the recursion of the Catalan numbers and the Cauchy product); `catalan_sqrt`; coefficients
`fc J = 2·catalan(J−1)/4^J ≥ 0`; `hasSum_one_sub_sqrt`: `Σ_J fc J s^J = 1 − √(1−s)` for `0 ≤ s ≤ 1` (including `s = 1`).
(2) `hJ u v J = Σ_{p=1}^{J} u^p v^{J−p}` (the mode factor of `kpow_diag_torus` of the fifty-first file for `J = j+1`);
`mode_sum_ne`: `Σ_J fc J hJ u v J = u/(√(1−u) + √(1−v))` for `u, v ∈ [0,1]`, `u ≠ v`;
`mode_sum_eq`: `Σ_J fc J hJ u u J = u/(2√(1−u))` for `0 ≤ u < 1` (monotone limit `v ↑ u`).
NOT formalised: the sum over the Fourier modes of the torus and the exchange with the sum over `J`; the exchange
of the derivative in the density with the sum over `J` (second-order remainders); the coefficient `c(a)` and its
limit.  For `u = v = 1` the series diverges (not a statement here).  No sorry, no axiom, no native_decide.
Written by the author-side AI session on 27 November 2026; read by nobody.
-/
import Mathlib

open Finset

noncomputable section
namespace CTG.SqrtSeries

/-- `g k = catalan k · x^k`. -/
def g (x : ℝ) (k : ℕ) : ℝ := (catalan k : ℝ) * x ^ k

lemma g_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) : 0 ≤ g x k := by unfold g; positivity

lemma g_succ (x : ℝ) (k : ℕ) :
    g x (k + 1) = x * ∑ i ∈ range (k + 1), g x i * g x (k - i) := by
  unfold g
  rw [catalan_succ, Finset.sum_range, mul_sum]
  push_cast
  rw [sum_mul]
  refine sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) ≤ k := Nat.lt_succ_iff.mp i.2
  have : x ^ (k + 1) = x * (x ^ (i : ℕ) * x ^ (k - i)) := by
    rw [← pow_add, Nat.add_sub_cancel' hi, pow_succ]; ring
  rw [this]; ring

/-- shifted partial sums. -/
lemma shift_sum (f : ℕ → ℝ) (i N : ℕ) :
    ∑ k ∈ range N, (if i ≤ k then f (k - i) else 0) = ∑ j ∈ range (N - i), f j := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    by_cases h : i ≤ N
    · rw [if_pos h, show N + 1 - i = (N - i) + 1 by omega, sum_range_succ]
    · rw [if_neg h, show N + 1 - i = N - i by omega, add_zero]

/-- triangle ≤ square. -/
lemma triangle_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    ∑ k ∈ range N, ∑ i ∈ range (k + 1), g x i * g x (k - i) ≤ (∑ k ∈ range N, g x k) ^ 2 := by
  have h1 : ∀ k ∈ range N, ∑ i ∈ range (k + 1), g x i * g x (k - i)
      = ∑ i ∈ range N, (if i ≤ k then g x i * g x (k - i) else 0) := by
    intro k hk
    have hk' : k < N := mem_range.mp hk
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext i; simp only [mem_range, mem_filter]; omega
  rw [sum_congr rfl h1, sum_comm, sq, sum_mul]
  refine sum_le_sum fun i _ => ?_
  have h2 : ∑ k ∈ range N, (if i ≤ k then g x i * g x (k - i) else 0)
      = g x i * ∑ k ∈ range N, (if i ≤ k then g x (k - i) else 0) := by
    rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  rw [h2, shift_sum]
  refine mul_le_mul_of_nonneg_left ?_ (g_nonneg hx i)
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le N i)) fun j _ _ => g_nonneg hx j

/-- partial sums of `Σ catalan k x^k` are at most `2` for `0 ≤ x ≤ 1/4`. -/
lemma partial_le_two {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) (N : ℕ) :
    ∑ k ∈ range N, g x k ≤ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ', show g x 0 = 1 by simp [g]]
    simp_rw [g_succ, ← mul_sum]
    have ht := triangle_le hx N
    have h0 : 0 ≤ ∑ k ∈ range N, g x k := sum_nonneg fun k _ => g_nonneg hx k
    have hsq : (∑ k ∈ range N, g x k) ^ 2 ≤ 4 := by nlinarith
    have h3 : 0 ≤ ∑ k ∈ range N, ∑ i ∈ range (k + 1), g x i * g x (k - i) :=
      sum_nonneg fun k _ => sum_nonneg fun i _ => mul_nonneg (g_nonneg hx i) (g_nonneg hx _)
    nlinarith

lemma g_summable {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) : Summable (g x) :=
  summable_of_sum_range_le (g_nonneg hx) (partial_le_two hx hx4)

lemma g_tsum_le {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) : ∑' k, g x k ≤ 2 :=
  (g_summable hx hx4).tsum_le_of_sum_range_le (partial_le_two hx hx4)

/-- the functional equation `C = 1 + x C²`. -/
lemma g_functional {x : ℝ} (hx : 0 ≤ x) (hx4 : x ≤ 1 / 4) :
    ∑' k, g x k = 1 + x * (∑' k, g x k) ^ 2 := by
  have hs := g_summable hx hx4
  have hn : Summable fun k => ‖g x k‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (g_nonneg hx _)] using hs
  have e1 : ∑' k, g x k = 1 + ∑' k, g x (k + 1) := by
    rw [hs.tsum_eq_zero_add]; simp [g]
  have e2 : (∑' k, g x k) ^ 2 = ∑' n, ∑ k ∈ range (n + 1), g x k * g x (n - k) := by
    rw [sq]; exact tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hn hn
  rw [e2, ← tsum_mul_left]
  conv_lhs => rw [e1]
  congr 1
  exact tsum_congr fun k => g_succ x k

/-- **The generating function of the Catalan numbers**, in the form needed:
for `0 ≤ s ≤ 1`, `2 (s/4) Σ_k catalan k (s/4)^k = 1 − √(1 − s)`. -/
theorem catalan_sqrt {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    2 * (s / 4) * ∑' k, g (s / 4) k = 1 - Real.sqrt (1 - s) := by
  have hx : 0 ≤ s / 4 := by positivity
  have hx4 : s / 4 ≤ 1 / 4 := by linarith
  set C := ∑' k, g (s / 4) k with hC
  have hf := g_functional hx hx4
  have hle := g_tsum_le hx hx4
  rw [← hC] at hf hle
  set F := 2 * (s / 4) * C with hF
  -- F = (s + F²)/2, F ≤ s ≤ 1
  have h1 : (1 - F) ^ 2 = 1 - s := by rw [hF]; nlinarith
  have h2 : 0 ≤ 1 - F := by rw [hF]; nlinarith
  have : Real.sqrt (1 - s) = 1 - F := by
    rw [← h1, Real.sqrt_sq h2]
  rw [this]; ring

/-- Coefficients `f_J = 2·catalan(J−1)/4^J` (`J ≥ 1`), `f_0 = 0`. -/
def fc (J : ℕ) : ℝ := if J = 0 then 0 else 2 * (catalan (J - 1) : ℝ) / 4 ^ J

lemma fc_nonneg (J : ℕ) : 0 ≤ fc J := by unfold fc; split_ifs <;> positivity

/-- **Power series of `1 − √(1−s)` on `[0,1]`** with non-negative coefficients. -/
theorem hasSum_one_sub_sqrt {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    HasSum (fun J => fc J * s ^ J) (1 - Real.sqrt (1 - s)) := by
  have hx : 0 ≤ s / 4 := by positivity
  have hx4 : s / 4 ≤ 1 / 4 := by linarith
  have hsum := (g_summable hx hx4).hasSum.mul_left (2 * (s / 4))
  rw [catalan_sqrt hs hs1] at hsum
  have e : (fun J => fc (J + 1) * s ^ (J + 1)) = fun k => 2 * (s / 4) * g (s / 4) k := by
    funext k
    unfold fc g
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, div_pow, pow_succ, pow_succ]
    field_simp
  have h0 : fc 0 * s ^ 0 = 0 := by simp [fc]
  have h3 : HasSum (fun J => fc (J + 1) * s ^ (J + 1)) (1 - Real.sqrt (1 - s)) := by
    rw [e]; exact hsum
  have h4 : HasSum (fun J => fc J * s ^ J)
      (1 - Real.sqrt (1 - s) + ∑ i ∈ range 1, fc i * s ^ i) :=
    (hasSum_nat_add_iff (f := fun J => fc J * s ^ J) 1).mp h3
  have h5 : fc 0 = 0 := by simp [fc]
  simpa [h5] using h4


/-! ## Sum over the powers for one Fourier mode -/

/-- `h_J(u,v) = Σ_{p=1}^{J} u^p v^{J−p}` (for `J = j+1` this is `u^J + Σ_{i<j} u^{i+1} v^{j−i}`). -/
def hJ (u v : ℝ) (J : ℕ) : ℝ := ∑ p ∈ range J, u ^ (p + 1) * v ^ (J - 1 - p)

lemma hJ_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (J : ℕ) : 0 ≤ hJ u v J :=
  sum_nonneg fun p _ => by positivity

lemma hJ_mul (u v : ℝ) (J : ℕ) : hJ u v J * (u - v) = u * (u ^ J - v ^ J) := by
  have h := Commute.geom_sum₂_mul (Commute.all u v) J
  unfold hJ
  rw [← h, ← mul_assoc, mul_sum]
  congr 1
  refine sum_congr rfl fun p _ => ?_
  rw [pow_succ]; ring

lemma hJ_mono {u v v' : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hvv : v ≤ v') (J : ℕ) :
    hJ u v J ≤ hJ u v' J :=
  sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hvv _) (by positivity)

lemma hJ_continuous (u : ℝ) (J : ℕ) : Continuous fun v => hJ u v J := by
  unfold hJ; fun_prop

/-- **Sum over the powers, `u ≠ v`.** For `u, v ∈ [0,1]`, `u ≠ v`:
`Σ_J f_J h_J(u,v) = u/(√(1−u) + √(1−v))`. -/
theorem mode_sum_ne {u v : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1) (hne : u ≠ v) :
    HasSum (fun J => fc J * hJ u v J) (u / (Real.sqrt (1 - u) + Real.sqrt (1 - v))) := by
  have hU := hasSum_one_sub_sqrt hu hu1
  have hV := hasSum_one_sub_sqrt hv hv1
  have hd : u - v ≠ 0 := sub_ne_zero.mpr hne
  have h := ((hU.sub hV).mul_left (u / (u - v)))
  have e : (fun J => u / (u - v) * (fc J * u ^ J - fc J * v ^ J)) = fun J => fc J * hJ u v J := by
    funext J
    have := hJ_mul u v J
    field_simp
    linear_combination (-(fc J)) * this
  rw [e] at h
  convert h using 1
  have hwu := Real.sqrt_nonneg (1 - u)
  have hwv := Real.sqrt_nonneg (1 - v)
  have su := Real.sq_sqrt (show (0:ℝ) ≤ 1 - u by linarith)
  have sv := Real.sq_sqrt (show (0:ℝ) ≤ 1 - v by linarith)
  have hpos : 0 < Real.sqrt (1 - u) + Real.sqrt (1 - v) := by
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr (by linarith)
      linarith
    · have : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.mpr (by linarith)
      linarith
  have key : (Real.sqrt (1 - v) - Real.sqrt (1 - u)) * (Real.sqrt (1 - u) + Real.sqrt (1 - v))
      = u - v := by nlinarith
  rw [div_mul_eq_mul_div, div_eq_div_iff hpos.ne' hd]
  have : 1 - Real.sqrt (1 - u) - (1 - Real.sqrt (1 - v)) = Real.sqrt (1 - v) - Real.sqrt (1 - u) := by
    ring
  rw [this, mul_assoc, key]

/-- **Sum over the powers, `u = v < 1`:** `Σ_J f_J h_J(u,u) = u/(2√(1−u))`. -/
theorem mode_sum_eq {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    HasSum (fun J => fc J * hJ u u J) (u / (2 * Real.sqrt (1 - u))) := by
  have hw : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr (by linarith)
  have hnn : ∀ J, 0 ≤ fc J * hJ u u J := fun J => mul_nonneg (fc_nonneg J) (hJ_nonneg hu hu J)
  rcases hu.eq_or_lt with h0 | hpos
  · subst h0
    have : (fun J => fc J * hJ 0 0 J) = fun _ => 0 := by
      funext J; unfold hJ; simp
    rw [this]; simpa using hasSum_zero
  -- values for v < u
  have hval : ∀ v, 0 ≤ v → v < u →
      HasSum (fun J => fc J * hJ u v J) (u / (Real.sqrt (1 - u) + Real.sqrt (1 - v))) :=
    fun v hv hvu => mode_sum_ne hu hu1.le hv (by linarith) (ne_of_gt hvu)
  have hwmono : ∀ v, v < u → Real.sqrt (1 - u) ≤ Real.sqrt (1 - v) :=
    fun v hvu => Real.sqrt_le_sqrt (by linarith)
  -- upper bound for the partial sums
  have hup : ∀ N, ∑ J ∈ range N, fc J * hJ u u J ≤ u / (2 * Real.sqrt (1 - u)) := by
    intro N
    have hc : Continuous fun v => ∑ J ∈ range N, fc J * hJ u v J :=
      continuous_finset_sum _ fun J _ => continuous_const.mul (hJ_continuous u J)
    have hev : ∀ᶠ v in nhdsWithin u (Set.Iio u),
        ∑ J ∈ range N, fc J * hJ u v J ≤ u / (2 * Real.sqrt (1 - u)) := by
      filter_upwards [Ioo_mem_nhdsLT hpos] with v hv
      have h1 : ∑ J ∈ range N, fc J * hJ u v J ≤ u / (Real.sqrt (1 - u) + Real.sqrt (1 - v)) :=
        sum_le_hasSum _ (fun J _ => mul_nonneg (fc_nonneg J) (hJ_nonneg hu hv.1.le J))
          (hval v hv.1.le hv.2)
      refine h1.trans (div_le_div_of_nonneg_left hu (by positivity) ?_)
      have := hwmono v hv.2; linarith
    exact le_of_tendsto (hc.continuousWithinAt.tendsto) hev
  have hs : Summable fun J => fc J * hJ u u J := summable_of_sum_range_le hnn hup
  have hle : ∑' J, fc J * hJ u u J ≤ u / (2 * Real.sqrt (1 - u)) :=
    hs.tsum_le_of_sum_range_le hup
  -- lower bound
  have hlow : ∀ᶠ v in nhdsWithin u (Set.Iio u),
      u / (Real.sqrt (1 - u) + Real.sqrt (1 - v)) ≤ ∑' J, fc J * hJ u u J := by
    filter_upwards [Ioo_mem_nhdsLT hpos] with v hv
    exact hasSum_le (fun J => mul_le_mul_of_nonneg_left (hJ_mono hu hv.1.le hv.2.le J) (fc_nonneg J))
      (hval v hv.1.le hv.2) hs.hasSum
  have hcont : ContinuousAt (fun v => u / (Real.sqrt (1 - u) + Real.sqrt (1 - v))) u := by
    refine ContinuousAt.div continuousAt_const ?_ (by positivity)
    exact continuousAt_const.add ((Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousAt)
  have hge : u / (2 * Real.sqrt (1 - u)) ≤ ∑' J, fc J * hJ u u J := by
    have := le_of_tendsto (hcont.continuousWithinAt.tendsto) hlow
    simpa [two_mul] using this
  have : ∑' J, fc J * hJ u u J = u / (2 * Real.sqrt (1 - u)) := le_antisymm hle hge
  rw [← this]; exact hs.hasSum

end CTG.SqrtSeries
