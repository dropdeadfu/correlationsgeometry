import Mathlib

/-!
# The kernel recursion (deterministic part of Theorem G.28 of the paper)

Paper: M. Neuberger, *From Correlations to Geometry*, Appendix G (version of 17 November 2026).

Theorem G.28 compares the `k`-step kernel `N (P^k)_{ai}` of the normalised walk on `N` sample
points with the population kernel `p_k(x_a − x_i)`, uniformly in `k`. Its proof has a probabilistic
half (the consistency lemma, Lemma G.27) and a deterministic half. This file formalises the
deterministic half for an arbitrary row-stochastic kernel `P` on a finite type:

* `act_telescope`: the telescoping identity
  `P^k g_n = g_{n+k} + Σ_{j<k} P^{k−1−j} h_{n+j}` with the defect `h_m = P g_m − g_{m+1}`;
* `abs_act_le_sup`, `abs_act_le_weight`: the two bounds for `P^l h` (stability in the supremum
  norm, and a bound by the largest entry of `P^l` times the `ℓ¹` norm of `h`);
* `sum_inv_sqrt_le`: `Σ_{m=1}^k m^{-1/2} ≤ 2 √k`;
* `kernel_recursion`: the induction of Step 4, with the constant `24 + 12 A c`.

Dictionary with the paper: `q m b i = p_m(x_b − x_i)`, `μ m = m_m = p_m(0)`, `ε = δ'`,
`24 ε` bounds `4 δ`, `c` is the constant of Lemma G.27, `A = 2^d`, and `K` is the largest `m`
for which the lemma is used.

What is taken as input (hypotheses of `kernel_recursion`, not proven here): the two bounds of the
consistency lemma (`hsup`, `hL1`), the bound for the last step of the walk (`hlast`), and the
monotonicity and doubling of `m_s` (`hμ`, `hdbl`).
-/

open Finset

namespace CorrelationsGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `iter P k` is the `k`-th power of the kernel `P`: `iter P 0 = 1`,
`iter P (k + 1) = iter P k * P`. -/
def iter (P : ι → ι → ℝ) : ℕ → ι → ι → ℝ
  | 0 => fun a b => if a = b then 1 else 0
  | k + 1 => fun a b => ∑ c, iter P k a c * P c b

theorem iter_zero (P : ι → ι → ℝ) (a b : ι) : iter P 0 a b = if a = b then 1 else 0 := rfl

theorem iter_succ (P : ι → ι → ℝ) (k : ℕ) (a b : ι) :
    iter P (k + 1) a b = ∑ c, iter P k a c * P c b := rfl

theorem iter_one (P : ι → ι → ℝ) (a b : ι) : iter P 1 a b = P a b := by
  rw [iter_succ]
  simp [iter_zero]

/-- The entries of `P^k` are non-negative. -/
theorem iter_nonneg {P : ι → ι → ℝ} (hP0 : ∀ a b, 0 ≤ P a b) (k : ℕ) (a b : ι) :
    0 ≤ iter P k a b := by
  induction k generalizing b with
  | zero =>
    rw [iter_zero]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [iter_succ]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (ih c) (hP0 c b)

/-- `P^k` is row-stochastic. -/
theorem iter_row_sum {P : ι → ι → ℝ} (hP1 : ∀ a, ∑ b, P a b = 1) (k : ℕ) (a : ι) :
    ∑ b, iter P k a b = 1 := by
  induction k with
  | zero => simp [iter_zero]
  | succ k ih =>
    simp only [iter_succ]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hP1, mul_one]
    exact ih

/-- `act P l v = P^l v`. -/
def act (P : ι → ι → ℝ) (l : ℕ) (v : ι → ℝ) (a : ι) : ℝ := ∑ b, iter P l a b * v b

/-- **Stability.** A row-stochastic kernel does not increase the supremum norm. -/
theorem abs_act_le_sup {P : ι → ι → ℝ} (hP0 : ∀ a b, 0 ≤ P a b) (hP1 : ∀ a, ∑ b, P a b = 1)
    (l : ℕ) (v : ι → ℝ) (a : ι) {C : ℝ} (hv : ∀ b, |v b| ≤ C) : |act P l v a| ≤ C := by
  unfold act
  calc |∑ b, iter P l a b * v b| ≤ ∑ b, |iter P l a b * v b| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, iter P l a b * |v b| := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [abs_mul, abs_of_nonneg (iter_nonneg hP0 l a b)]
    _ ≤ ∑ b, iter P l a b * C :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hv b) (iter_nonneg hP0 l a b)
    _ = C := by rw [← Finset.sum_mul, iter_row_sum hP1, one_mul]

/-- `|P^l v| ≤ (largest entry of the row of P^l) · ‖v‖₁`. -/
theorem abs_act_le_weight {P : ι → ι → ℝ} (hP0 : ∀ a b, 0 ≤ P a b) (l : ℕ) (v : ι → ℝ) (a : ι)
    {W : ℝ} (hW : ∀ b, iter P l a b ≤ W) : |act P l v a| ≤ W * ∑ b, |v b| := by
  unfold act
  calc |∑ b, iter P l a b * v b| ≤ ∑ b, |iter P l a b * v b| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, iter P l a b * |v b| := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [abs_mul, abs_of_nonneg (iter_nonneg hP0 l a b)]
    _ ≤ ∑ b, W * |v b| :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hW b) (abs_nonneg _)
    _ = W * ∑ b, |v b| := by rw [Finset.mul_sum]

/-- The defect of a sequence of vectors: `h_m = P g_m − g_{m+1}`. -/
def defect (P : ι → ι → ℝ) (g : ℕ → ι → ℝ) (m : ℕ) (b : ι) : ℝ :=
  ∑ j, P b j * g m j - g (m + 1) b

/-- One step: `P^{l+1} g_n = P^l g_{n+1} + P^l h_n`. -/
theorem act_succ (P : ι → ι → ℝ) (g : ℕ → ι → ℝ) (l n : ℕ) (a : ι) :
    act P (l + 1) (g n) a = act P l (g (n + 1)) a + act P l (defect P g n) a := by
  unfold act defect
  simp only [iter_succ]
  rw [← Finset.sum_add_distrib]
  have h : ∑ b, (∑ c, iter P l a c * P c b) * g n b
      = ∑ c, iter P l a c * ∑ b, P c b * g n b := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **Telescoping (Step 1 of Theorem G.28).**
`P^k g_n = g_{n+k} + Σ_{j<k} P^{k−1−j} h_{n+j}`. -/
theorem act_telescope (P : ι → ι → ℝ) (g : ℕ → ι → ℝ) (a : ι) (k n : ℕ) :
    act P k (g n) a
      = g (n + k) a + ∑ j ∈ Finset.range k, act P (k - 1 - j) (defect P g (n + j)) a := by
  induction k generalizing n with
  | zero => simp [act, iter_zero]
  | succ k ih =>
    rw [act_succ, ih (n + 1), Finset.sum_range_succ']
    have h0 : act P (k + 1 - 1 - 0) (defect P g (n + 0)) a = act P k (defect P g n) a := by
      simp
    have hs : ∑ j ∈ Finset.range k, act P (k + 1 - 1 - (j + 1)) (defect P g (n + (j + 1))) a
        = ∑ j ∈ Finset.range k, act P (k - 1 - j) (defect P g (n + 1 + j)) a := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
      have e2 : n + (j + 1) = n + 1 + j := by omega
      rw [e1, e2]
    have h1 : n + 1 + k = n + (k + 1) := by omega
    rw [h0, hs, h1]
    ring

/-- `Σ_{m=1}^k m^{-1/2} ≤ 2 √k`. -/
theorem sum_inv_sqrt_le (k : ℕ) : ∑ j ∈ Finset.range k, 1 / √((j : ℝ) + 1) ≤ 2 * √(k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hs : 0 < √((k : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have hs2 : √((k : ℝ) + 1) * √((k : ℝ) + 1) = k + 1 := Real.mul_self_sqrt (by linarith)
    have hr2 : √(k : ℝ) * √(k : ℝ) = k := Real.mul_self_sqrt hk
    have key : 1 / √((k : ℝ) + 1) ≤ 2 * √((k : ℝ) + 1) - 2 * √(k : ℝ) := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (√((k : ℝ) + 1) - √(k : ℝ))]
    push_cast
    linarith

/-- **Deterministic part of Theorem G.28 (Steps 2 to 4).** Let `P` be a row-stochastic kernel on a
finite type, `q m b i` nonnegative numbers bounded by `μ m`, with `μ` non-increasing and
`μ l ≤ A μ (k+1)` whenever `k + 1 ≤ 4 l`. Assume the last step of the walk satisfies
`|N P_{bi} − q_1(b,i)| ≤ 24 ε q_1(b,i)`, and the defects `h_m^{(i)} = P q_m(·,i) − q_{m+1}(·,i)`
satisfy `|h_m^{(i)}(b)| ≤ c ε m^{-1/2} μ(6m)` and `(1/N) Σ_b |h_m^{(i)}(b)| ≤ 2 c ε m^{-1/2}` for
`1 ≤ m ≤ K`. Then, with `C₁ = 24 + 12 A c`,

  `|N (P^k)_{ai} − q_k(a,i)| ≤ C₁ ε √k μ_k`

for all `1 ≤ k ≤ K + 1` with `C₁ ε √k ≤ 1`. -/
theorem kernel_recursion {P : ι → ι → ℝ} (hP0 : ∀ a b, 0 ≤ P a b) (hP1 : ∀ a, ∑ b, P a b = 1)
    (q : ℕ → ι → ι → ℝ) (μ : ℕ → ℝ) {N ε c A : ℝ} {K : ℕ}
    (hN : 0 < N) (hε : 0 ≤ ε) (hε' : 24 * ε ≤ 1 / 2) (hc : 0 ≤ c) (hA : 1 ≤ A)
    (hμ0 : ∀ m, 0 ≤ μ m) (hqμ : ∀ m b i, q m b i ≤ μ m)
    (hμ : ∀ s t, s ≤ t → μ t ≤ μ s) (hdbl : ∀ l k, k + 1 ≤ 4 * l → μ l ≤ A * μ (k + 1))
    (hlast : ∀ b i, |N * P b i - q 1 b i| ≤ 24 * ε * q 1 b i)
    (hsup : ∀ m, 1 ≤ m → m ≤ K → ∀ i b,
      |defect P (fun n j => q n j i) m b| ≤ c * ε / √(m : ℝ) * μ (6 * m))
    (hL1 : ∀ m, 1 ≤ m → m ≤ K → ∀ i,
      ∑ b, |defect P (fun n j => q n j i) m b| ≤ N * (2 * c * ε / √(m : ℝ))) :
    ∀ k, 1 ≤ k → k ≤ K + 1 → (24 + 12 * A * c) * ε * √(k : ℝ) ≤ 1 → ∀ a i,
      |N * iter P k a i - q k a i| ≤ (24 + 12 * A * c) * ε * √(k : ℝ) * μ k := by
  have hA0 : 0 ≤ A := by linarith
  have hC1pos : 0 ≤ 24 + 12 * A * c := by
    have := mul_nonneg hA0 hc
    linarith
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkK hC a i
    rcases k with _ | k
    · omega
    have hkK' : k ≤ K := by omega
    push_cast at hC ⊢
    have hμk : 0 ≤ μ (k + 1) := hμ0 _
    have hsq1 : (1 : ℝ) ≤ √((k : ℝ) + 1) := by
      calc (1 : ℝ) = √1 := Real.sqrt_one.symm
        _ ≤ √((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hsqle : √(k : ℝ) ≤ √((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    -- Step 2: the last step of the walk
    have hU : |N * iter P (k + 1) a i - act P k (fun j => q 1 j i) a|
        ≤ 24 * ε * act P k (fun j => q 1 j i) a := by
      have e : N * iter P (k + 1) a i - act P k (fun j => q 1 j i) a
          = ∑ b, iter P k a b * (N * P b i - q 1 b i) := by
        unfold act
        rw [iter_succ, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      rw [e]
      calc |∑ b, iter P k a b * (N * P b i - q 1 b i)|
          ≤ ∑ b, |iter P k a b * (N * P b i - q 1 b i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ b, iter P k a b * (24 * ε * q 1 b i) := by
            refine Finset.sum_le_sum fun b _ => ?_
            rw [abs_mul, abs_of_nonneg (iter_nonneg hP0 k a b)]
            exact mul_le_mul_of_nonneg_left (hlast b i) (iter_nonneg hP0 k a b)
        _ = 24 * ε * act P k (fun j => q 1 j i) a := by
            unfold act
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            ring
    -- Step 1: telescoping
    have htel := act_telescope P (fun n j => q n j i) a k 1
    beta_reduce at htel
    -- Step 3 and the two cases of Step 4: a bound for each term
    have hterm : ∀ j ∈ Finset.range k,
        |act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a|
          ≤ 4 * A * c * ε * μ (k + 1) * (1 / √((j : ℝ) + 1)) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hm1 : 1 ≤ 1 + j := by omega
      have hmK : 1 + j ≤ K := by omega
      have hsq : 0 < √((j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hcast : ((1 + j : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      have hsupj := hsup (1 + j) hm1 hmK i
      have hL1j := hL1 (1 + j) hm1 hmK i
      rw [hcast] at hsupj hL1j
      have hX : 0 ≤ c * ε * μ (k + 1) * (1 / √((j : ℝ) + 1)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hc hε) hμk) (by positivity)
      by_cases hcase : k < 2 * (1 + j)
      · -- `m > k/2`: stability and `μ (6 m) ≤ μ (k + 1)`
        have h6 : μ (6 * (1 + j)) ≤ μ (k + 1) := hμ _ _ (by omega)
        have hce : 0 ≤ c * ε / √((j : ℝ) + 1) := div_nonneg (mul_nonneg hc hε) hsq.le
        have hb : |act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a|
            ≤ c * ε / √((j : ℝ) + 1) * μ (6 * (1 + j)) :=
          abs_act_le_sup hP0 hP1 _ _ a (fun b => hsupj b)
        calc |act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a|
            ≤ c * ε / √((j : ℝ) + 1) * μ (6 * (1 + j)) := hb
          _ ≤ c * ε / √((j : ℝ) + 1) * μ (k + 1) := mul_le_mul_of_nonneg_left h6 hce
          _ = c * ε * μ (k + 1) * (1 / √((j : ℝ) + 1)) := by ring
          _ ≤ (4 * A) * (c * ε * μ (k + 1) * (1 / √((j : ℝ) + 1))) :=
              le_mul_of_one_le_left hX (by linarith)
          _ = 4 * A * c * ε * μ (k + 1) * (1 / √((j : ℝ) + 1)) := by ring
      · -- `m ≤ k/2`: the induction hypothesis for `l = k − m` and the `ℓ¹` bound
        have hcase' : 2 * (1 + j) ≤ k := by omega
        have hl1 : 1 ≤ k - 1 - j := by omega
        have hlk : k - 1 - j < k + 1 := by omega
        have hlK : k - 1 - j ≤ K + 1 := by omega
        have hsql : √((k - 1 - j : ℕ) : ℝ) ≤ √((k : ℝ) + 1) := by
          refine Real.sqrt_le_sqrt ?_
          have : ((k - 1 - j : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : k - 1 - j ≤ k)
          linarith
        have hCl : (24 + 12 * A * c) * ε * √((k - 1 - j : ℕ) : ℝ) ≤ 1 :=
          (mul_le_mul_of_nonneg_left hsql (mul_nonneg hC1pos hε)).trans hC
        have hW : ∀ b, iter P (k - 1 - j) a b ≤ 2 * μ (k - 1 - j) / N := by
          intro b
          have h := ih (k - 1 - j) hlk hl1 hlK hCl a b
          have h2 := (abs_le.mp h).2
          have h3 : (24 + 12 * A * c) * ε * √((k - 1 - j : ℕ) : ℝ) * μ (k - 1 - j)
              ≤ 1 * μ (k - 1 - j) := mul_le_mul_of_nonneg_right hCl (hμ0 _)
          have h4 := hqμ (k - 1 - j) a b
          rw [le_div_iff₀ hN]
          linarith
        have hb := abs_act_le_weight hP0 (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a hW
        have hμl : μ (k - 1 - j) ≤ A * μ (k + 1) := hdbl _ _ (by omega)
        have hw0 : 0 ≤ 2 * μ (k - 1 - j) / N :=
          div_nonneg (mul_nonneg (by norm_num) (hμ0 _)) hN.le
        have hN' : N ≠ 0 := hN.ne'
        have hsq' : √((j : ℝ) + 1) ≠ 0 := hsq.ne'
        have hce4 : 0 ≤ 4 * c * ε := mul_nonneg (mul_nonneg (by norm_num) hc) hε
        have hinv : 0 ≤ 1 / √((j : ℝ) + 1) := by positivity
        calc |act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a|
            ≤ 2 * μ (k - 1 - j) / N * ∑ b, |defect P (fun n j => q n j i) (1 + j) b| := hb
          _ ≤ 2 * μ (k - 1 - j) / N * (N * (2 * c * ε / √((j : ℝ) + 1))) :=
              mul_le_mul_of_nonneg_left hL1j hw0
          _ = 4 * c * ε * μ (k - 1 - j) * (1 / √((j : ℝ) + 1)) := by
              field_simp
              ring
          _ ≤ 4 * c * ε * (A * μ (k + 1)) * (1 / √((j : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hμl hce4) hinv
          _ = 4 * A * c * ε * μ (k + 1) * (1 / √((j : ℝ) + 1)) := by ring
    -- the sum over `m`
    have hcoef : 0 ≤ 4 * A * c * ε * μ (k + 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hc) hε) hμk
    have hS : |∑ j ∈ Finset.range k,
          act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a|
        ≤ 4 * A * c * ε * μ (k + 1) * (2 * √(k : ℝ)) := by
      calc |∑ j ∈ Finset.range k,
            act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a|
          ≤ ∑ j ∈ Finset.range k,
              |act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Finset.range k, 4 * A * c * ε * μ (k + 1) * (1 / √((j : ℝ) + 1)) :=
            Finset.sum_le_sum hterm
        _ = 4 * A * c * ε * μ (k + 1) * ∑ j ∈ Finset.range k, 1 / √((j : ℝ) + 1) := by
            rw [Finset.mul_sum]
        _ ≤ 4 * A * c * ε * μ (k + 1) * (2 * √(k : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_inv_sqrt_le k) hcoef
    -- assemble
    generalize hSdef : (∑ j ∈ Finset.range k,
      act P (k - 1 - j) (defect P (fun n j => q n j i) (1 + j)) a) = S at htel hS
    have hUeq : act P k (fun j => q 1 j i) a = q (k + 1) a i + S := by
      rw [htel, Nat.add_comm 1 k]
    have hUle : act P k (fun j => q 1 j i) a ≤ μ (k + 1) + |S| := by
      rw [hUeq]
      linarith [hqμ (k + 1) a i, le_abs_self S]
    have key : |N * iter P (k + 1) a i - q (k + 1) a i|
        ≤ 24 * ε * μ (k + 1) + (1 + 24 * ε) * |S| := by
      have e : N * iter P (k + 1) a i - q (k + 1) a i
          = (N * iter P (k + 1) a i - act P k (fun j => q 1 j i) a) + S := by
        rw [hUeq]
        ring
      have h24 : (0 : ℝ) ≤ 24 * ε := by linarith
      rw [e]
      calc |(N * iter P (k + 1) a i - act P k (fun j => q 1 j i) a) + S|
          ≤ |N * iter P (k + 1) a i - act P k (fun j => q 1 j i) a| + |S| := abs_add_le _ _
        _ ≤ 24 * ε * act P k (fun j => q 1 j i) a + |S| := by linarith
        _ ≤ 24 * ε * (μ (k + 1) + |S|) + |S| := by
            have := mul_le_mul_of_nonneg_left hUle h24
            linarith
        _ = 24 * ε * μ (k + 1) + (1 + 24 * ε) * |S| := by ring
    have hfin : 24 * ε * μ (k + 1) + (1 + 24 * ε) * |S|
        ≤ (24 + 12 * A * c) * ε * √((k : ℝ) + 1) * μ (k + 1) := by
      have h15 : 1 + 24 * ε ≤ 3 / 2 := by linarith
      have h1 : (1 + 24 * ε) * |S| ≤ 3 / 2 * (4 * A * c * ε * μ (k + 1) * (2 * √(k : ℝ))) :=
        mul_le_mul h15 hS (abs_nonneg _) (by norm_num)
      have h24μ : 0 ≤ 24 * ε * μ (k + 1) := mul_nonneg (by linarith) hμk
      have h2 : 24 * ε * μ (k + 1) * 1 ≤ 24 * ε * μ (k + 1) * √((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hsq1 h24μ
      have h12 : 0 ≤ 12 * A * c * ε * μ (k + 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0) hc) hε) hμk
      have h3 : 12 * A * c * ε * μ (k + 1) * √(k : ℝ)
          ≤ 12 * A * c * ε * μ (k + 1) * √((k : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hsqle h12
      nlinarith [h1, h2, h3]
    exact key.trans hfin

end CorrelationsGeometry
