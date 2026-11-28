/-
Seventy-fifth file (A188, written by a subagent of the author-side session, checked by that session; read by nobody
else). Explicit value for the constant of Theorem LB on `S²` for smooth functions (seventieth file): with
W = Σ' l, √(2l+1)/(l(l+1)), `W_le` (W ≤ 74/25), `W_ge` (11/4 ≤ W, for orientation), `W_le_two_sqrt_three`, and
`LB_sphere_smooth_explicit`: |L_ξ f(x) + Δf(x)| ≤ 3·(74/25)·‖Δ⁴f‖₂·ξ² for 0 < ξ ≤ 1/20, under the assumptions of
`LB_sphere_smooth` (extrinsic Laplacian). Route: telescoping bounds, no integral. Namespace
`CTG.FunkHecke.LBSmoothExplicit`; imports the compiled module of the seventieth file. Check with
`./check_funk_hecke_lb_smooth_explicit.sh`. No sorry, no axiom, no native_decide.
-/
import CorrelationsToGeometryFunkHeckeLBSmooth

open Finset

namespace CTG.FunkHecke.LBSmoothExplicit

open CTG.FunkHecke.LBSmooth (wseq wseq_nonneg wseq_summable N4 LB_sphere_smooth)
open CTG.FunkHecke (S2)
open CTG.FunkHecke.SphereLB (Lxi)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)

/-- Upper telescoping sequence `a_l = 2√(2l+1)/l`. -/
noncomputable def aU (l : ℕ) : ℝ := 2 * Real.sqrt (2 * (l : ℝ) + 1) / l
/-- Lower telescoping sequence `b_l = 2√(2l−1)/l`. -/
noncomputable def bL (l : ℕ) : ℝ := 2 * Real.sqrt (2 * (l : ℝ) - 1) / l

theorem aU_nonneg (l : ℕ) : 0 ≤ aU l := by unfold aU; positivity
theorem bL_nonneg (l : ℕ) : 0 ≤ bL l := by unfold bL; positivity

private theorem le_of_sq_le {A B : ℝ} (hB : 0 ≤ B) (h : A ^ 2 ≤ B ^ 2) : A ≤ B := by
  by_contra hc; rw [not_le] at hc
  nlinarith [mul_self_lt_mul_self hB hc]

/-- `w_l ≤ a_l − a_{l+1}` for `l ≥ 1`. -/
theorem wseq_le_tel {l : ℕ} (hl : 1 ≤ l) : wseq l ≤ aU l - aU (l + 1) := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  set s := Real.sqrt (2 * (l : ℝ) + 1) with hs
  set t := Real.sqrt (2 * (l : ℝ) + 3) with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * (l : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have ht2 : t ^ 2 = 2 * (l : ℝ) + 3 := Real.sq_sqrt (by positivity)
  have key : 2 * (l : ℝ) * t ≤ (2 * l + 1) * s := by
    apply le_of_sq_le (by positivity)
    simp only [mul_pow, hs2, ht2]; nlinarith
  have hcast : ((l + 1 : ℕ) : ℝ) = (l : ℝ) + 1 := by push_cast; ring
  unfold wseq aU
  rw [hcast, show 2 * ((l : ℝ) + 1) + 1 = 2 * (l : ℝ) + 3 by ring, ← hs, ← ht]
  have hl0 : (0 : ℝ) < l := by linarith
  rw [div_sub_div _ _ hl0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (l:ℝ) * (l+1)) (sub_nonneg.2 key)]

/-- `b_l − b_{l+1} ≤ w_l` for `l ≥ 1`. -/
theorem tel_le_wseq {l : ℕ} (hl : 1 ≤ l) : bL l - bL (l + 1) ≤ wseq l := by
  have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
  set s := Real.sqrt (2 * (l : ℝ) - 1) with hs
  set t := Real.sqrt (2 * (l : ℝ) + 1) with ht
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 * (l : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = 2 * (l : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have key : 2 * ((l : ℝ) + 1) * s ≤ (2 * l + 1) * t := by
    apply le_of_sq_le (by positivity)
    simp only [mul_pow, hs2, ht2]; nlinarith
  have hcast : ((l + 1 : ℕ) : ℝ) = (l : ℝ) + 1 := by push_cast; ring
  unfold wseq bL
  rw [hcast, show 2 * ((l : ℝ) + 1) - 1 = 2 * (l : ℝ) + 1 by ring, ← hs, ← ht]
  have hl0 : (0 : ℝ) < l := by linarith
  rw [div_sub_div _ _ hl0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (l:ℝ) * (l+1)) (sub_nonneg.2 key)]

theorem partial_upper {k : ℕ} (hk : 1 ≤ k) {m : ℕ} (hm : k ≤ m) :
    ∑ i ∈ range m, wseq i ≤ ∑ i ∈ range k, wseq i + aU k - aU m := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [sum_range_succ]
    have := wseq_le_tel (le_trans hk hkn)
    linarith

theorem partial_lower {k : ℕ} (hk : 1 ≤ k) {m : ℕ} (hm : k ≤ m) :
    ∑ i ∈ range k, wseq i + bL k - bL m ≤ ∑ i ∈ range m, wseq i := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    rw [sum_range_succ]
    have := tel_le_wseq (le_trans hk hkn)
    linarith

/-- `W ≤ S_k + a_k` for every `k ≥ 1`. -/
theorem W_le_partial {k : ℕ} (hk : 1 ≤ k) :
    ∑' l, wseq l ≤ ∑ i ∈ range k, wseq i + aU k := by
  refine Real.tsum_le_of_sum_range_le wseq_nonneg (fun m => ?_)
  rcases le_or_gt k m with h | h
  · linarith [partial_upper hk h, aU_nonneg m]
  · have : ∑ i ∈ range m, wseq i ≤ ∑ i ∈ range k, wseq i :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h.le) (fun i _ _ => wseq_nonneg i)
    linarith [aU_nonneg k]

/-- `W ≥ S_k + b_k − b_m` for `1 ≤ k ≤ m`. -/
theorem partial_le_W {k : ℕ} (hk : 1 ≤ k) {m : ℕ} (hm : k ≤ m) :
    ∑ i ∈ range k, wseq i + bL k - bL m ≤ ∑' l, wseq l :=
  (partial_lower hk hm).trans (wseq_summable.sum_le_tsum _ (fun i _ => wseq_nonneg i))

theorem wseq_zero : wseq 0 = 0 := by simp [wseq]
theorem wseq_one : wseq 1 = Real.sqrt 3 / 2 := by
  unfold wseq; rw [show 2 * ((1 : ℕ) : ℝ) + 1 = 3 by norm_num]; push_cast; ring
theorem wseq_two : wseq 2 = Real.sqrt 5 / 6 := by
  unfold wseq; rw [show 2 * ((2 : ℕ) : ℝ) + 1 = 5 by norm_num]; push_cast; ring
theorem wseq_three : wseq 3 = Real.sqrt 7 / 12 := by
  unfold wseq; rw [show 2 * ((3 : ℕ) : ℝ) + 1 = 7 by norm_num]; push_cast; ring
theorem aU_one : aU 1 = 2 * Real.sqrt 3 := by
  unfold aU; rw [show 2 * ((1 : ℕ) : ℝ) + 1 = 3 by norm_num]; push_cast; ring
theorem aU_four : aU 4 = 3 / 2 := by
  unfold aU; rw [show 2 * ((4 : ℕ) : ℝ) + 1 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  push_cast; ring
theorem bL_four : bL 4 = Real.sqrt 7 / 2 := by
  unfold bL; rw [show 2 * ((4 : ℕ) : ℝ) - 1 = 7 by norm_num]; push_cast; ring
theorem bL_big : bL 10000 = 2 * Real.sqrt 19999 / 10000 := by
  unfold bL; rw [show 2 * ((10000 : ℕ) : ℝ) - 1 = 19999 by norm_num]; push_cast; ring

/-- **`W ≤ 2√3`.** -/
theorem W_le_two_sqrt_three : ∑' l, wseq l ≤ 2 * Real.sqrt 3 := by
  have h := W_le_partial (k := 1) le_rfl
  simp only [sum_range_succ, sum_range_zero, wseq_zero, aU_one] at h
  linarith

private theorem sqrt_le_of {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : Real.sqrt x ≤ y :=
  Real.sqrt_le_iff.2 ⟨hy, h⟩

private theorem le_sqrt_of {x y : ℝ} (h : y ^ 2 ≤ x) : y ≤ Real.sqrt x :=
  Real.le_sqrt_of_sq_le h

/-- **Explicit value `W₀ = 74/25`: `W = Σ_l √(2l+1)/(l(l+1)) ≤ 2.96`.** -/
theorem W_le : ∑' l, wseq l ≤ 74 / 25 := by
  have h := W_le_partial (k := 4) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, wseq_zero, wseq_one, wseq_two, wseq_three, aU_four] at h
  have h3 := sqrt_le_of (x := 3) (y := 17321 / 10000) (by norm_num) (by norm_num)
  have h5 := sqrt_le_of (x := 5) (y := 22361 / 10000) (by norm_num) (by norm_num)
  have h7 := sqrt_le_of (x := 7) (y := 26458 / 10000) (by norm_num) (by norm_num)
  linarith

/-- **Lower bound `W ≥ 11/4 = 2.75`** (for orientation). -/
theorem W_ge : 11 / 4 ≤ ∑' l, wseq l := by
  have h := partial_le_W (k := 4) (m := 10000) (by norm_num) (by norm_num)
  simp only [sum_range_succ, sum_range_zero, wseq_zero, wseq_one, wseq_two, wseq_three, bL_four,
    bL_big] at h
  have h3 := le_sqrt_of (x := 3) (y := 1732 / 1000) (by norm_num)
  have h5 := le_sqrt_of (x := 5) (y := 2236 / 1000) (by norm_num)
  have h7 := le_sqrt_of (x := 7) (y := 26457 / 10000) (by norm_num)
  have hb := sqrt_le_of (x := 19999) (y := 150) (by norm_num) (by norm_num)
  linarith

/-- **`thm:LB` on `S²` for smooth `f` with an explicit constant**: under the hypotheses of `LB_sphere_smooth`,
for `0 < ξ ≤ 1/20` and every `x`: `|L_ξ f(x) + Δ_{S²} f(x)| ≤ 3 · (74/25) · ‖Δ⁴ f‖_{L²(σ)} · ξ²`. -/
theorem LB_sphere_smooth_explicit {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (x : S2) :
    |Lxi ξ f x + sphLapS f x| ≤ 3 * (74 / 25) * N4 f * ξ ^ 2 := by
  obtain ⟨-, h1, h2⟩ := LB_sphere_smooth hf hξ hξ1 x
  have hN : 0 ≤ N4 f := Real.sqrt_nonneg _
  have : 3 * (∑' l, wseq l) * N4 f * ξ ^ 2 ≤ 3 * (74 / 25) * N4 f * ξ ^ 2 := by
    have := W_le
    have hx : 0 ≤ N4 f * ξ ^ 2 := by positivity
    nlinarith
  exact h1.trans (h2.trans this)

end CTG.FunkHecke.LBSmoothExplicit

#print axioms CTG.FunkHecke.LBSmoothExplicit.LB_sphere_smooth_explicit
#print axioms CTG.FunkHecke.LBSmoothExplicit.W_le
#print axioms CTG.FunkHecke.LBSmoothExplicit.W_ge
#print axioms CTG.FunkHecke.LBSmoothExplicit.W_le_two_sqrt_three
