/-
Thirty-seventh file: the flat N-point statement for ALL pairs of times of a window, on one event.  Imports
`CorrelationsToGeometryFlatNPointClose` (compiled module under `.tools/leanbuild`); namespace
`CTG.FlatNPointWindow`; check with `./check_flat_npoint_window.sh`.
`rate_L` (the one-pair statement with a general Bernstein parameter `L`; the proof is a copy of that of
`flat_npoint_rate` with `3 log N` replaced by `L`), `norm_event` (lower bound of the sample normalisation at one
time), `LN_lip` (pathwise Lipschitz bound of `τ ↦ L_N(τ) f(i)` without powers of `N`), `window_det` (deterministic
assembly on a time grid), `flat_npoint_window`: for a window `[p,q]`, `η₀ > 0` and a grid width `w` with three
explicit conditions, with `K = ⌊(q−p)/w⌋`, outside an event of (outer) probability at most
`(K+1)·N·2e^{−L} + (K+1)²·15·N·2e^{−L}`, for all `τa, τb ∈ [p,q]` with `|τb − τa| ≥ η₀` and all sample points
`|dqI| ≤ 2E` and `|dqII| ≤ 2E + 2 ξ² min{C₁/|η|, C₂}`, `E` the rate term of `flat_npoint_rate` with `L` in place
of `3 log N`; `flat_npoint_window_log` (`L = c log N`).
HYPOTHESIS beyond the earlier files: a bound `G₂` for `|lapG S f|` (exists for periodic `C⁴` functions, not
derived here).  The grid width `w` is a free parameter; the Lipschitz constant is crude (of the order
`ξ^{−1−5n}`), so `w` must be polynomially small and `c` large; this choice is NOT made in a statement.
NOT formalised: measurability of the exceptional set (uncountable union; the bound is for the outer measure),
pairs with `|τb − τa| < η₀`, Gaussian profiles.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryFlatNPointClose

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB3 CTG.FlatLB4 CTG.FlatNPoint
  CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointClose

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointWindow

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### (0) Notation for the two difference quotients and the error terms -/

/-- `Δ_η L_N f(i) − Δ_η L_ξ f(X_i)` for the pair of times `(τa, τb)`. -/
def dqI {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ)
    (ξ : ℝ) (f : E → ℝ) (τa τb : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
    - (Lmet h m₂ S (a τb) ξ f (X i ω) - Lmet h m₂ S (a τa) ξ f (X i ω)) / (τb - τa)

/-- `Δ_η L_N f(i) + Δ_η(Δ_{g_τ} f)(X_i)` for the pair of times `(τa, τb)`. -/
def dqII {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ)
    (ξ : ℝ) (f : E → ℝ) (τa τb : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
    + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)

/-- The population error `ξ² min{C₁/|η|, C₂}`. -/
def popErr (ξ C₁ C₂ η : ℝ) : ℝ := ξ ^ 2 * min (C₁ / |η|) C₂

/-- `C₁ = M₄ ‖S‖⁴ μ₄/(6 m₂ K₀ a₀⁴)`. -/
def Cone (M₄ μ₄ m₂ K₀ a₀ : ℝ) (S : E ≃L[ℝ] E) : ℝ :=
  M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4)

/-- `C₂ = M₄ ‖S‖⁴ μ₄ L_a/(3 m₂ K₀ a₀⁵)`. -/
def Ctwo (M₄ μ₄ m₂ K₀ a₀ La : ℝ) (S : E ≃L[ℝ] E) : ℝ :=
  M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)

/-- The rate error `(7320000 Λ²⁰/m₂) √(L/(N ξ^d))/ξ`. -/
def rateE (d : ℕ) (Λ m₂ L : ℝ) (N : ℕ) (ξ : ℝ) : ℝ :=
  7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ d)) / ξ

/-- The exceptional set of one pair of times, with error `Er` and constants `C₁`, `C₂`. -/
def badL {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ)
    (ξ : ℝ) (f : E → ℝ) (τa τb Er C₁ C₂ : ℝ) : Set Ω :=
  {ω | ∃ i < N, ¬ (|dqI X N h m₂ S a ξ f τa τb i ω| ≤ Er
      ∧ |dqII X N h m₂ S a ξ f τa τb i ω| ≤ Er + popErr ξ C₁ C₂ (τb - τa))}

/-- The functions of time whose difference quotients are `dqI`, `dqII`. -/
def FI {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ)
    (ξ : ℝ) (f : E → ℝ) (i : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  LN X N h m₂ S (a τ) ξ f i ω - Lmet h m₂ S (a τ) ξ f (X i ω)

def FII {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ)
    (ξ : ℝ) (f : E → ℝ) (i : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  LN X N h m₂ S (a τ) ξ f i ω + lapG S f (X i ω) / a τ ^ 2

theorem dqI_eq {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E)
    (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ) (τa τb : ℝ) (i : ℕ) (ω : Ω) :
    dqI X N h m₂ S a ξ f τa τb i ω
      = (FI X N h m₂ S a ξ f i ω τb - FI X N h m₂ S a ξ f i ω τa) / (τb - τa) := by
  unfold dqI FI; ring

theorem dqII_eq {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E)
    (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ) (τa τb : ℝ) (i : ℕ) (ω : Ω) :
    dqII X N h m₂ S a ξ f τa τb i ω
      = (FII X N h m₂ S a ξ f i ω τb - FII X N h m₂ S a ξ f i ω τa) / (τb - τa) := by
  unfold dqII FII; ring

/-! ### (1) Finite averages -/

theorem avgN_close {N : ℕ} (hN : 0 < N) {F G : ℕ → ℝ} {B : ℝ}
    (h : ∀ j < N, |F j - G j| ≤ B) : |avgN N F - avgN N G| ≤ B := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  unfold avgN
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
  calc 1 / (N : ℝ) * |∑ k ∈ Finset.range N, (F k - G k)|
      ≤ 1 / (N : ℝ) * ∑ k ∈ Finset.range N, B :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k hk => h k (Finset.mem_range.1 hk))) (by positivity)
    _ = B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

theorem avgN_abs_le {N : ℕ} (hN : 0 < N) {F : ℕ → ℝ} {B : ℝ}
    (h : ∀ j < N, |F j| ≤ B) : |avgN N F| ≤ B := by
  have h0 : avgN N (fun _ => (0:ℝ)) = 0 := by simp [avgN]
  have := avgN_close hN (F := F) (G := fun _ => 0) (B := B) (fun j hj => by
    show |F j - 0| ≤ B
    rw [sub_zero]; exact h j hj)
  rwa [h0, sub_zero] at this

theorem avgN_mono {N : ℕ} {F G : ℕ → ℝ} (h : ∀ j < N, F j ≤ G j) : avgN N F ≤ avgN N G := by
  unfold avgN
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => h k (Finset.mem_range.1 hk))
    (by positivity)

/-- One term of a weighted average: `|b'/q' − b/q| ≤ D/c + U e/c²`. -/
theorem term_close {b b' q q' c U D e : ℝ} (hc : 0 < c) (hq : c ≤ q) (hq' : c ≤ q')
    (hU : |b| ≤ U) (hD : |b' - b| ≤ D) (he : |q' - q| ≤ e) :
    |b' * (1 / q') - b * (1 / q)| ≤ D / c + U * e / c ^ 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le hc hq
  have hq'0 : 0 < q' := lt_of_lt_of_le hc hq'
  have hU0 : 0 ≤ U := le_trans (abs_nonneg _) hU
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) hD
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) he
  have hqn := hq0.ne'
  have hq'n := hq'0.ne'
  have e1 : b' * (1 / q') - b * (1 / q) = (b' - b) / q' + b * (q - q') / (q * q') := by
    field_simp
    ring
  rw [e1]
  have t1 : |(b' - b) / q'| ≤ D / c := by
    rw [abs_div, abs_of_pos hq'0]
    exact div_le_div₀ hD0 hD hc hq'
  have t2 : |b * (q - q') / (q * q')| ≤ U * e / c ^ 2 := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hq0 hq'0)]
    refine div_le_div₀ (mul_nonneg hU0 he0)
      (mul_le_mul hU (by rw [abs_sub_comm]; exact he) (abs_nonneg _) hU0) (by positivity) ?_
    rw [sq]; exact mul_le_mul hq hq' hc.le hq0.le
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

theorem tri_helper {P Q b e : ℝ} (h1 : |P - Q| ≤ b) (h2 : |Q| ≤ e) : |P| ≤ e + b := by
  have := abs_add_le (P - Q) Q
  rw [sub_add_cancel] at this
  linarith

/-! ### (2) The sample operator is Lipschitz in time, given lower bounds of the normalisation -/

theorem sampAvg_le {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) {K : E → E → ℝ} {A : ℝ}
    (hnn : ∀ x z, 0 ≤ K x z) (hle : ∀ x z, K x z ≤ A) (j : ℕ) (ω : Ω) :
    sampAvg X N K j ω ≤ A := by
  have e : sampAvg X N K j ω = avgN N (fun k => K (X j ω) (X k ω)) := rfl
  rw [e]
  exact (abs_le.1 (avgN_abs_le hN fun k _ => by
    show |K (X j ω) (X k ω)| ≤ A
    rw [abs_of_nonneg (hnn _ _)]; exact hle _ _)).2

/-- Lower bound of the sample denominator: `𝒟_i ≥ c/A` if all `q_j ≥ c` and `0 ≤ K ≤ A`. -/
theorem den_lower {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) {K : E → E → ℝ} {A c : ℝ}
    (hnn : ∀ x z, 0 ≤ K x z) (hle : ∀ x z, K x z ≤ A) (hc : 0 < c) (ω : Ω)
    (hq : ∀ j < N, c ≤ sampAvg X N K j ω) {i : ℕ} (hi : i < N) :
    c / A ≤ sampW X N K (fun _ _ => 1) i ω := by
  have hqA : ∀ j, sampAvg X N K j ω ≤ A := fun j => sampAvg_le X hN hnn hle j ω
  have hA : 0 < A := lt_of_lt_of_le hc ((hq i hi).trans (hqA i))
  have e1 : sampW X N K (fun _ _ => 1) i ω
      = avgN N (fun j => K (X i ω) (X j ω) * 1 * (1 / sampAvg X N K j ω)) := rfl
  have e2 : avgN N (fun j => K (X i ω) (X j ω) * (1 / A)) = sampAvg X N K i ω * (1 / A) := by
    unfold avgN sampAvg; rw [← Finset.sum_mul]; ring
  rw [e1]
  calc c / A = c * (1 / A) := by ring
    _ ≤ sampAvg X N K i ω * (1 / A) :=
        mul_le_mul_of_nonneg_right (hq i hi) (one_div_pos.2 hA).le
    _ = avgN N (fun j => K (X i ω) (X j ω) * (1 / A)) := e2.symm
    _ ≤ avgN N (fun j => K (X i ω) (X j ω) * 1 * (1 / sampAvg X N K j ω)) :=
        avgN_mono fun j hj => by
          show K (X i ω) (X j ω) * (1 / A) ≤ K (X i ω) (X j ω) * 1 * (1 / sampAvg X N K j ω)
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (lt_of_lt_of_le hc (hq j hj)) (hqA j)) (hnn _ _)

/-- **Abstract comparison of the sample ratios of two kernels** that are pointwise `e`-close. -/
theorem ratio_lip {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) {Ks Kt g : E → E → ℝ}
    {A G e c : ℝ} (hc : 0 < c) (hG : 0 ≤ G)
    (hsn : ∀ x z, 0 ≤ Ks x z) (hsA : ∀ x z, Ks x z ≤ A)
    (htn : ∀ x z, 0 ≤ Kt x z) (htA : ∀ x z, Kt x z ≤ A)
    (hlip : ∀ x z, |Kt x z - Ks x z| ≤ e)
    (hsg : ∀ x z, |Ks x z * g x z| ≤ A * G)
    (hdg : ∀ x z, |Kt x z * g x z - Ks x z * g x z| ≤ e * G)
    (ω : Ω) (hqs : ∀ j < N, c ≤ sampAvg X N Ks j ω) (hqt : ∀ j < N, c ≤ sampAvg X N Kt j ω)
    {i : ℕ} (hi : i < N) :
    |sampW X N Kt g i ω / sampW X N Kt (fun _ _ => 1) i ω
        - sampW X N Ks g i ω / sampW X N Ks (fun _ _ => 1) i ω|
      ≤ (e * G / c + A * G * e / c ^ 2) / (c / A)
        + A * G / c * (e / c + A * e / c ^ 2) / (c / A) ^ 2 := by
  have hqsA := fun j => sampAvg_le X hN hsn hsA j ω
  have hA : 0 < A := lt_of_lt_of_le hc ((hqs i hi).trans (hqsA i))
  have hqd : ∀ j, |sampAvg X N Kt j ω - sampAvg X N Ks j ω| ≤ e := fun j =>
    sampAvg_close X hN hlip j ω
  have hNum : |sampW X N Kt g i ω - sampW X N Ks g i ω| ≤ e * G / c + A * G * e / c ^ 2 :=
    avgN_close hN
      (F := fun j => Kt (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Kt j ω))
      (G := fun j => Ks (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Ks j ω))
      fun j hj => term_close hc (hqs j hj) (hqt j hj) (hsg _ _) (hdg _ _) (hqd j)
  have hDen : |sampW X N Kt (fun _ _ => 1) i ω - sampW X N Ks (fun _ _ => 1) i ω|
      ≤ e / c + A * e / c ^ 2 :=
    avgN_close hN
      (F := fun j => Kt (X i ω) (X j ω) * 1 * (1 / sampAvg X N Kt j ω))
      (G := fun j => Ks (X i ω) (X j ω) * 1 * (1 / sampAvg X N Ks j ω))
      fun j hj => term_close hc (hqs j hj) (hqt j hj)
        (by rw [mul_one, abs_of_nonneg (hsn _ _)]; exact hsA _ _)
        (by rw [mul_one, mul_one]; exact hlip _ _) (hqd j)
  have hNs : |sampW X N Ks g i ω| ≤ A * G / c :=
    avgN_abs_le hN
      (F := fun j => Ks (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Ks j ω))
      fun j hj => by
        have hq0 : 0 < sampAvg X N Ks j ω := lt_of_lt_of_le hc (hqs j hj)
        show |Ks (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Ks j ω)| ≤ A * G / c
        rw [abs_mul, abs_of_pos (one_div_pos.2 hq0), div_eq_mul_one_div (A * G) c]
        exact mul_le_mul (hsg _ _) (one_div_le_one_div_of_le hc (hqs j hj))
          (one_div_pos.2 hq0).le (mul_nonneg hA.le hG)
  have hDs := den_lower X hN hsn hsA hc ω hqs hi
  have hDt := den_lower X hN htn htA hc ω hqt hi
  rw [div_eq_mul_one_div (sampW X N Kt g i ω), div_eq_mul_one_div (sampW X N Ks g i ω)]
  exact term_close (div_pos hc hA) hDs hDt hNs hNum hDen

/-- On the support of a kernel value `u` the increment of `f` is at most `M₁ ρ`. -/
theorem kg_bound {f : E → ℝ} (hfd : Differentiable ℝ f) (hper : Per f) {M₁ : ℝ}
    (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁) {ρ : ℝ} (hρ0 : 0 ≤ ρ) {u B : ℝ} (hB : |u| ≤ B) (x z : E)
    (hs : u ≠ 0 → ‖fr (z - x)‖ ≤ ρ) : |u * gd f x z| ≤ B * (M₁ * ρ) := by
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hB
  by_cases h0 : u = 0
  · rw [h0, zero_mul, abs_zero]; exact mul_nonneg hB0 (mul_nonneg hM0 hρ0)
  · rw [abs_mul]
    refine mul_le_mul hB ?_ (abs_nonneg _) hB0
    have h1 := lip_of_fderiv hfd hM₁ x (x + fr (z - x))
    rw [add_sub_cancel_left] at h1
    have h2 : gd f x z = f (x + fr (z - x)) - f x := by
      unfold gd; rw [← per_fr hper x z]
    rw [h2]
    exact h1.trans (mul_le_mul_of_nonneg_left (hs h0) hM0)

/-- The Lipschitz constant in time of the sample operator, given `q_j ≥ c`:
`(2/(m₂ξ²)) · [G κ/(c/A) + (A G/c) κ/(c/A)²]`, `κ = BI/c + A·BI/c²`. -/
def LNlip (m₂ ξ A BI G c : ℝ) : ℝ :=
  2 / (m₂ * ξ ^ 2) * (G * (BI / c + A * BI / c ^ 2) / (c / A)
    + A * G / c * (BI / c + A * BI / c ^ 2) / (c / A) ^ 2)

theorem LNlip_nonneg {m₂ ξ A BI G c : ℝ} (hm₂ : 0 < m₂) (hA : 0 ≤ A) (hBI : 0 ≤ BI)
    (hG : 0 ≤ G) (hc : 0 < c) : 0 ≤ LNlip m₂ ξ A BI G c := by
  unfold LNlip; positivity

/-- **`τ ↦ L_N(τ) f(i)` is Lipschitz between two times at which all sample normalisations are
`≥ c`**, with the constant `LNlip` (no power of `N`). -/
theorem LN_lip {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N)
    {h : ℝ → ℝ} {A R Lh : ℝ} (hP : Prof h A R) (hR : 0 ≤ R)
    (hL : LipProf h Lh) (hLh : 0 ≤ Lh) {m₂ : ℝ} (hm₂ : 0 < m₂)
    {f : E → ℝ} (hfd : Differentiable ℝ f) (hper : Per f) {M₁ : ℝ}
    (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) {c : ℝ} (hc : 0 < c) (s t : ℝ) (ω : Ω)
    (hqs : ∀ j < N, c ≤ sampAvg X N (perK (kap h S (ξ / a s))) j ω)
    (hqt : ∀ j < N, c ≤ sampAvg X N (perK (kap h S (ξ / a t))) j ω) {i : ℕ} (hi : i < N) :
    |LN X N h m₂ S (a t) ξ f i ω - LN X N h m₂ S (a s) ξ f i ω|
      ≤ LNlip m₂ ξ A (BIc Lh R La a₀) (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) c
        * |t - s| := by
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hρ0 : 0 ≤ ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (div_pos hξ ha₀).le hR)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hBI0 : 0 ≤ BIc Lh R La a₀ := by unfold BIc; positivity
  have hG0 : 0 ≤ M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)) := mul_nonneg hM0 hρ0
  have hnn : ∀ τ x z, 0 ≤ perK (kap h S (ξ / a τ)) x z := fun τ x z => hP.nonneg _
  have hle : ∀ τ x z, perK (kap h S (ξ / a τ)) x z ≤ A := fun τ x z => hP.le _
  have hsupp : ∀ τ x z, perK (kap h S (ξ / a τ)) x z ≠ 0
      → ‖fr (z - x)‖ ≤ ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) := fun τ x z hv =>
    kap_supp hP S (div_pos hξ (hpos τ)) (scale_le hξ ha₀ (ha τ) hR le_rfl) _ hv
  have hlip : ∀ x z, |perK (kap h S (ξ / a t)) x z - perK (kap h S (ξ / a s)) x z|
      ≤ BIc Lh R La a₀ * |t - s| := fun x z =>
    perK_time_lip hP hR hL hLh S a a' hda ha₀ ha hLa hξ s t x z
  have hsg : ∀ x z, |perK (kap h S (ξ / a s)) x z * gd f x z|
      ≤ A * (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) := fun x z =>
    kg_bound hfd hper hM₁ hρ0 (by rw [abs_of_nonneg (hnn s x z)]; exact hle s x z) x z
      (hsupp s x z)
  have hdg : ∀ x z, |perK (kap h S (ξ / a t)) x z * gd f x z
        - perK (kap h S (ξ / a s)) x z * gd f x z|
      ≤ BIc Lh R La a₀ * |t - s| * (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) := fun x z => by
    rw [← sub_mul]
    refine kg_bound hfd hper hM₁ hρ0 (hlip x z) x z fun hu => ?_
    by_cases h0 : perK (kap h S (ξ / a t)) x z = 0
    · refine hsupp s x z fun h1 => hu ?_
      rw [h0, h1, sub_self]
    · exact hsupp t x z h0
  have key := ratio_lip X hN (Ks := perK (kap h S (ξ / a s))) (Kt := perK (kap h S (ξ / a t)))
    (g := gd f) (A := A) (G := M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
    (e := BIc Lh R La a₀ * |t - s|) hc hG0 (hnn s) (hle s) (hnn t) (hle t) hlip hsg hdg ω
    hqs hqt hi
  have eL : LN X N h m₂ S (a t) ξ f i ω - LN X N h m₂ S (a s) ξ f i ω
      = -(2 / (m₂ * ξ ^ 2))
        * (sampW X N (perK (kap h S (ξ / a t))) (gd f) i ω
            / sampW X N (perK (kap h S (ξ / a t))) (fun _ _ => 1) i ω
          - sampW X N (perK (kap h S (ξ / a s))) (gd f) i ω
            / sampW X N (perK (kap h S (ξ / a s))) (fun _ _ => 1) i ω) := by
    unfold LN; ring
  have hk0 : (0:ℝ) < 2 / (m₂ * ξ ^ 2) := by positivity
  rw [eL, abs_mul, abs_neg, abs_of_pos hk0]
  refine (mul_le_mul_of_nonneg_left key hk0.le).trans (le_of_eq ?_)
  unfold LNlip; ring

/-! ### (3) The population side is Lipschitz in time -/

theorem inv_sq_lip (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) (s t : ℝ) :
    |1 / a t ^ 2 - 1 / a s ^ 2| ≤ 2 * La / a₀ ^ 3 * |t - s| := by
  have hs : 0 < a s := lt_of_lt_of_le ha₀ (ha s)
  have ht : 0 < a t := lt_of_lt_of_le ha₀ (ha t)
  have hs' := hs.ne'
  have ht' := ht.ne'
  have hl := a_lip a a' hda hLa s t
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have e : 1 / a t ^ 2 - 1 / a s ^ 2
      = (a s - a t) * (1 / (a t ^ 2 * a s) + 1 / (a t * a s ^ 2)) := by
    field_simp
    ring
  have h1 : 1 / (a t ^ 2 * a s) ≤ 1 / a₀ ^ 3 := by
    apply one_div_le_one_div_of_le (by positivity)
    calc a₀ ^ 3 = a₀ ^ 2 * a₀ := by ring
      _ ≤ a t ^ 2 * a s :=
          mul_le_mul (pow_le_pow_left₀ ha₀.le (ha t) 2) (ha s) ha₀.le (by positivity)
  have h2 : 1 / (a t * a s ^ 2) ≤ 1 / a₀ ^ 3 := by
    apply one_div_le_one_div_of_le (by positivity)
    calc a₀ ^ 3 = a₀ * a₀ ^ 2 := by ring
      _ ≤ a t * a s ^ 2 :=
          mul_le_mul (ha t) (pow_le_pow_left₀ ha₀.le (ha s) 2) (by positivity) ht.le
  have h3 : 0 ≤ 1 / (a t ^ 2 * a s) + 1 / (a t * a s ^ 2) := by positivity
  rw [e, abs_mul, abs_sub_comm (a s) (a t), abs_of_nonneg h3]
  calc |a t - a s| * (1 / (a t ^ 2 * a s) + 1 / (a t * a s ^ 2))
      ≤ La * |t - s| * (1 / a₀ ^ 3 + 1 / a₀ ^ 3) :=
        mul_le_mul hl (add_le_add h1 h2) h3 (mul_nonneg hLa0 (abs_nonneg _))
    _ = 2 * La / a₀ ^ 3 * |t - s| := by ring

theorem lapterm_lip (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) {c G₂ : ℝ} (hc : |c| ≤ G₂)
    (s t : ℝ) : |c / a t ^ 2 - c / a s ^ 2| ≤ G₂ * (2 * La / a₀ ^ 3) * |t - s| := by
  have e : c / a t ^ 2 - c / a s ^ 2 = c * (1 / a t ^ 2 - 1 / a s ^ 2) := by ring
  rw [e, abs_mul]
  have := inv_sq_lip a a' hda ha₀ ha hLa s t
  calc |c| * |1 / a t ^ 2 - 1 / a s ^ 2| ≤ G₂ * (2 * La / a₀ ^ 3 * |t - s|) :=
        mul_le_mul hc this (abs_nonneg _) (le_trans (abs_nonneg _) hc)
    _ = G₂ * (2 * La / a₀ ^ 3) * |t - s| := by ring

/-- `τ ↦ L^τ_ξ f(x)` is Lipschitz with constant `ξ² C₂ + G₂·2L_a/a₀³` (from `metric_dq_min`). -/
theorem Lmet_lip {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hm₂ : 0 < m₂) {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (x : E) {G₂ : ℝ} (hG₂ : |lapG S f x| ≤ G₂)
    (s t : ℝ) :
    |Lmet h m₂ S (a t) ξ f x - Lmet h m₂ S (a s) ξ f x|
      ≤ (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + G₂ * (2 * La / a₀ ^ 3)) * |t - s| := by
  by_cases hts : t = s
  · subst hts; simp only [sub_self, abs_zero, mul_zero, le_refl]
  · have hb := metric_dq_min hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ x s t hts
    have hb2 := hb.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _))
    rw [← add_div, abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hts))] at hb2
    have hl := lapterm_lip a a' hda ha₀ ha hLa hG₂ s t
    have hsplit : Lmet h m₂ S (a t) ξ f x - Lmet h m₂ S (a s) ξ f x
        = (Lmet h m₂ S (a t) ξ f x - Lmet h m₂ S (a s) ξ f x
            + (lapG S f x / a t ^ 2 - lapG S f x / a s ^ 2))
          - (lapG S f x / a t ^ 2 - lapG S f x / a s ^ 2) := by ring
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    unfold Ctwo
    linarith

/-! ### (4) Comparison with a grid pair -/

/-- `grid_compare` with the three Lipschitz inequalities that are actually used. -/
theorem grid_compare3 {F : ℝ → ℝ} {ℒ η₀ δg τa τb ga gb : ℝ} (hℒ : 0 ≤ ℒ)
    (hFb : |F τb - F gb| ≤ ℒ * |τb - gb|) (hFa : |F τa - F ga| ≤ ℒ * |τa - ga|)
    (hFg : |F gb - F ga| ≤ ℒ * |gb - ga|)
    (hη₀ : 0 < η₀) (hδ : 0 ≤ δg) (h4 : 4 * δg ≤ η₀)
    (ha : |τa - ga| ≤ δg) (hb : |τb - gb| ≤ δg) (hη : η₀ ≤ |τb - τa|) :
    |(F τb - F τa) / (τb - τa) - (F gb - F ga) / (gb - ga)| ≤ 4 * ℒ * δg / η₀ := by
  set η := τb - τa
  set η' := gb - ga
  have hdiff : |η - η'| ≤ 2 * δg := by
    have : η - η' = (τb - gb) - (τa - ga) := by simp only [η, η']; ring
    rw [this]; exact (abs_sub _ _).trans (by linarith)
  have hη'0 : η₀ / 2 ≤ |η'| := by
    have := abs_sub_abs_le_abs_sub η η'
    linarith
  have hηpos : 0 < |η| := by linarith
  have hη'pos : 0 < |η'| := by linarith
  set D := F τb - F τa
  set D' := F gb - F ga
  have hDD : |D - D'| ≤ 2 * ℒ * δg := by
    have : D - D' = (F τb - F gb) - (F τa - F ga) := by simp only [D, D']; ring
    rw [this]
    have h1 := hFb.trans (mul_le_mul_of_nonneg_left hb hℒ)
    have h2 := hFa.trans (mul_le_mul_of_nonneg_left ha hℒ)
    exact (abs_sub _ _).trans (by linarith)
  have hD' : |D'| ≤ ℒ * |η'| := hFg
  have hη0 : η ≠ 0 := abs_pos.1 hηpos
  have hη'0' : η' ≠ 0 := abs_pos.1 hη'pos
  have e : D / η - D' / η' = (D - D') / η + D' * (η' - η) / (η * η') := by
    field_simp; ring
  rw [e]
  have t1 : |(D - D') / η| ≤ 2 * ℒ * δg / η₀ := by
    rw [abs_div]
    calc |D - D'| / |η| ≤ 2 * ℒ * δg / |η| := div_le_div_of_nonneg_right hDD hηpos.le
      _ ≤ 2 * ℒ * δg / η₀ := div_le_div_of_nonneg_left (by positivity) hη₀ hη
  have t2 : |D' * (η' - η) / (η * η')| ≤ 2 * ℒ * δg / η₀ := by
    rw [abs_div, abs_mul, abs_mul]
    have hnum : |D'| * |η' - η| ≤ ℒ * |η'| * (2 * δg) :=
      mul_le_mul hD' (by rw [abs_sub_comm]; exact hdiff) (abs_nonneg _) (by positivity)
    calc |D'| * |η' - η| / (|η| * |η'|) ≤ ℒ * |η'| * (2 * δg) / (|η| * |η'|) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = 2 * ℒ * δg / |η| := by field_simp
      _ ≤ 2 * ℒ * δg / η₀ := div_le_div_of_nonneg_left (by positivity) hη₀ hη
  calc |(D - D') / η + D' * (η' - η) / (η * η')|
      ≤ |(D - D') / η| + |D' * (η' - η) / (η * η')| := abs_add_le _ _
    _ ≤ 2 * ℒ * δg / η₀ + 2 * ℒ * δg / η₀ := add_le_add t1 t2
    _ = 4 * ℒ * δg / η₀ := by ring

theorem grid_gap {η₀ δg τa τb ga gb : ℝ} (h4 : 4 * δg ≤ η₀)
    (ha : |τa - ga| ≤ δg) (hb : |τb - gb| ≤ δg) (hη : η₀ ≤ |τb - τa|) :
    |τb - τa| / 2 ≤ |gb - ga| := by
  have hdiff : |(τb - τa) - (gb - ga)| ≤ 2 * δg := by
    have : (τb - τa) - (gb - ga) = (τb - gb) - (τa - ga) := by ring
    rw [this]; exact (abs_sub _ _).trans (by linarith)
  have := abs_sub_abs_le_abs_sub (τb - τa) (gb - ga)
  linarith

theorem popErr_double {ξ C₁ C₂ η η' : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hη : 0 < |η|)
    (h : |η| / 2 ≤ |η'|) : popErr ξ C₁ C₂ η' ≤ 2 * popErr ξ C₁ C₂ η := by
  unfold popErr
  have h1 : min (C₁ / |η'|) C₂ / 2 ≤ C₁ / |η| := by
    have h5 : C₁ / |η'| ≤ C₁ / (|η| / 2) := div_le_div_of_nonneg_left hC₁ (by linarith) h
    have e : C₁ / (|η| / 2) = 2 * (C₁ / |η|) := by rw [div_div_eq_mul_div]; ring
    have := (min_le_left (C₁ / |η'|) C₂).trans (h5.trans_eq e)
    linarith
  have h2 : min (C₁ / |η'|) C₂ / 2 ≤ C₂ := by
    have := min_le_right (C₁ / |η'|) C₂
    linarith
  have h3 := le_min h1 h2
  have h6 : min (C₁ / |η'|) C₂ ≤ 2 * min (C₁ / |η|) C₂ := by linarith
  calc ξ ^ 2 * min (C₁ / |η'|) C₂ ≤ ξ ^ 2 * (2 * min (C₁ / |η|) C₂) :=
        mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
    _ = 2 * (ξ ^ 2 * min (C₁ / |η|) C₂) := by ring

/-! ### (5) The deterministic assembly -/

/-- **Deterministic window statement.**  Fix `ω`.  Let `T` be a finite set of times such that every
`τ ∈ [p, q]` is within `w` of a point of `T`, `4w ≤ η₀`, `BI·w ≤ c/4`.  If at every time of `T`
all sample normalisations are `≥ c/2` and at every pair of distinct times of `T` the two
inequalities hold with error `Er`, then for ALL `τa, τb ∈ [p, q]` with `|τb − τa| ≥ η₀` and all
`i < N` they hold with the additional term `4·ℒ·w/η₀` and with `2·popErr`. -/
theorem window_det {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ)
    {c w η₀ p q Er : ℝ} (hc : 0 < c) (hw : 0 ≤ w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀)
    (hwc : BIc Lh R La a₀ * w ≤ c / 4)
    (T : Finset ℝ) (hcov : ∀ τ ∈ Icc p q, ∃ g ∈ T, |τ - g| ≤ w) (ω : Ω)
    (hnorm : ∀ g ∈ T, ∀ j < N, c / 2 ≤ sampAvg X N (perK (kap h S (ξ / a g))) j ω)
    (hrate : ∀ ga ∈ T, ∀ gb ∈ T, gb ≠ ga → ∀ i < N,
      |dqI X N h m₂ S a ξ f ga gb i ω| ≤ Er
      ∧ |dqII X N h m₂ S a ξ f ga gb i ω|
          ≤ Er + popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (gb - ga))
    {τa τb : ℝ} (hτa : τa ∈ Icc p q) (hτb : τb ∈ Icc p q) (hη : η₀ ≤ |τb - τa|)
    {i : ℕ} (hi : i < N) :
    |dqI X N h m₂ S a ξ f τa τb i ω|
        ≤ Er + 4 * (LNlip m₂ ξ A (BIc Lh R La a₀)
              (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) (c / 4)
            + (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * w / η₀
    ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
        ≤ Er + 4 * (LNlip m₂ ξ A (BIc Lh R La a₀)
              (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) (c / 4)
            + G₂ * (2 * La / a₀ ^ 3)) * w / η₀
          + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa) := by
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hBI0 : 0 ≤ BIc Lh R La a₀ := by unfold BIc; positivity
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hG0 : 0 ≤ G₂ := le_trans (abs_nonneg _) (hG₂ 0)
  have hA0 : 0 ≤ A := le_trans (hP.nonneg 0) (hP.le 0)
  have hμ₄ : 0 ≤ μ₄ := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hK₀ := hk.kern.mass_pos
  have hC1 : 0 ≤ Cone M₄ μ₄ m₂ K₀ a₀ S := by unfold Cone; positivity
  have hC2 : 0 ≤ Ctwo M₄ μ₄ m₂ K₀ a₀ La S := by unfold Ctwo; positivity
  have hc4 : 0 < c / 4 := by linarith
  have hGG0 : 0 ≤ G₂ * (2 * La / a₀ ^ 3) := by positivity
  have hLL0 : 0 ≤ LNlip m₂ ξ A (BIc Lh R La a₀)
      (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) (c / 4) :=
    LNlip_nonneg hm₂ hA0 hBI0 (mul_nonneg hM0 (mul_nonneg (norm_nonneg _)
      (mul_nonneg (div_pos hξ ha₀).le hR))) hc4
  obtain ⟨ga, hga, hda'⟩ := hcov τa hτa
  obtain ⟨gb, hgb, hdb'⟩ := hcov τb hτb
  have hq : ∀ τ g, g ∈ T → |τ - g| ≤ w →
      ∀ j < N, c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a τ))) j ω := by
    intro τ g hg hτg j hj
    exact sampAvg_transfer X hN hP hR hLP hLh S a a' hda ha₀ ha hLa hξ
      ((mul_le_mul_of_nonneg_left hτg hBI0).trans hwc) j ω (hnorm g hg j hj)
  have hqa := hq τa ga hga hda'
  have hqb := hq τb gb hgb hdb'
  have hqga := hq ga ga hga (by rw [sub_self, abs_zero]; exact hw)
  have hqgb := hq gb gb hgb (by rw [sub_self, abs_zero]; exact hw)
  have hLN : ∀ s t, (∀ j < N, c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a s))) j ω) →
      (∀ j < N, c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a t))) j ω) →
      |LN X N h m₂ S (a s) ξ f i ω - LN X N h m₂ S (a t) ξ f i ω|
        ≤ LNlip m₂ ξ A (BIc Lh R La a₀)
            (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) (c / 4) * |s - t| := fun s t hs ht =>
    LN_lip X hN hP hR hLP hLh hm₂ hfd hper hM₁ S a a' hda ha₀ ha hLa hξ hc4 t s ω ht hs hi
  have hLm : ∀ s t, |Lmet h m₂ S (a s) ξ f (X i ω) - Lmet h m₂ S (a t) ξ f (X i ω)|
      ≤ (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + G₂ * (2 * La / a₀ ^ 3)) * |s - t| := fun s t =>
    Lmet_lip hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ (X i ω) (hG₂ _) t s
  have hLg : ∀ s t, |lapG S f (X i ω) / a s ^ 2 - lapG S f (X i ω) / a t ^ 2|
      ≤ G₂ * (2 * La / a₀ ^ 3) * |s - t| := fun s t =>
    lapterm_lip a a' hda ha₀ ha hLa (hG₂ _) t s
  have hF1 : ∀ s t, (∀ j < N, c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a s))) j ω) →
      (∀ j < N, c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a t))) j ω) →
      |FI X N h m₂ S a ξ f i ω s - FI X N h m₂ S a ξ f i ω t|
        ≤ (LNlip m₂ ξ A (BIc Lh R La a₀)
            (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) (c / 4)
          + (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * |s - t| := by
    intro s t hs ht
    have e : FI X N h m₂ S a ξ f i ω s - FI X N h m₂ S a ξ f i ω t
        = (LN X N h m₂ S (a s) ξ f i ω - LN X N h m₂ S (a t) ξ f i ω)
          - (Lmet h m₂ S (a s) ξ f (X i ω) - Lmet h m₂ S (a t) ξ f (X i ω)) := by
      unfold FI; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have h1 := hLN s t hs ht
    have h2 := hLm s t
    linarith
  have hF2 : ∀ s t, (∀ j < N, c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a s))) j ω) →
      (∀ j < N, c / 4 ≤ sampAvg X N (perK (kap h S (ξ / a t))) j ω) →
      |FII X N h m₂ S a ξ f i ω s - FII X N h m₂ S a ξ f i ω t|
        ≤ (LNlip m₂ ξ A (BIc Lh R La a₀)
            (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R))) (c / 4)
          + G₂ * (2 * La / a₀ ^ 3)) * |s - t| := by
    intro s t hs ht
    have e : FII X N h m₂ S a ξ f i ω s - FII X N h m₂ S a ξ f i ω t
        = (LN X N h m₂ S (a s) ξ f i ω - LN X N h m₂ S (a t) ξ f i ω)
          + (lapG S f (X i ω) / a s ^ 2 - lapG S f (X i ω) / a t ^ 2) := by
      unfold FII; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 := hLN s t hs ht
    have h2 := hLg s t
    linarith
  have hgap := grid_gap h4 hda' hdb' hη
  have hηpos : 0 < |τb - τa| := lt_of_lt_of_le hη₀ hη
  have hne : gb ≠ ga := by
    intro h0
    rw [h0, sub_self, abs_zero] at hgap
    linarith
  obtain ⟨r1, r2⟩ := hrate ga hga gb hgb hne i hi
  have g1 := grid_compare3 (F := FI X N h m₂ S a ξ f i ω)
    (add_nonneg hLL0 (add_nonneg (mul_nonneg (sq_nonneg ξ) hC2) hGG0))
    (hF1 τb gb hqb hqgb) (hF1 τa ga hqa hqga) (hF1 gb ga hqgb hqga) hη₀ hw h4 hda' hdb' hη
  have g2 := grid_compare3 (F := FII X N h m₂ S a ξ f i ω) (add_nonneg hLL0 hGG0)
    (hF2 τb gb hqb hqgb) (hF2 τa ga hqa hqga) (hF2 gb ga hqgb hqga) hη₀ hw h4 hda' hdb' hη
  rw [dqI_eq] at r1
  rw [dqII_eq] at r2
  rw [dqI_eq, dqII_eq]
  refine ⟨tri_helper g1 r1, ?_⟩
  have hp := popErr_double (ξ := ξ) hC1 hC2 hηpos hgap
  have := tri_helper g2 r2
  linarith

/-! ### (6) The single-pair statement with a general `L ≥ 1` -/

set_option maxHeartbeats 1600000 in
/-- `flat_npoint_rate` with a general Bernstein parameter `L ≥ 1` in place of `3 log N`
(same proof): probability of failure `≤ 15·N·2e^{−L}`, `δ' = √(L/(N ξⁿ))`. -/
theorem rate_L_raw {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 14 * L ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          - (Lmet h m₂ S (a τb) ξ f (X i ω) - Lmet h m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (L / (N * ξ ^ n)) / ξ
      ∧ |(LN X N h m₂ S (a τb) ξ f i ω - LN X N h m₂ S (a τa) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (L / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ / (6 * m₂ * K₀ * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * μ₄ * La / (3 * m₂ * K₀ * a₀ ^ 5)))}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨l1, lA, lBI, lP1, lMI, lP0, lALρ, lBILρ, lP1Lρ, lMILρ⟩ :=
    rLam_bounds A K₀ Lh R La a₀ a₁ Lip S
  -- notation
  set Λ := rLam A K₀ Lh R La a₀ a₁ Lip S with hΛ
  set x := ξ ^ n with hx
  set δ := Real.sqrt (L / (N * x)) with hδdef
  set ρ₁ := ‖(S : E →L[ℝ] E)‖ * R / a₀ with hρ₁
  set P1 := K₀ * dS S / a₀ ^ n with hP1
  set P0 := K₀ * dS S / a₁ ^ n with hP0
  set BI := BIc Lh R La a₀ with hBI
  set MI := MIc S Lh R La a₀ with hMI
  set Lρ := Lip * ρ₁ with hLρ
  set pa := pmass h S (a τa) ξ with hpa
  set pb := pmass h S (a τb) ξ with hpb
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hx0 : 0 < x := pow_pos hξ n
  have hx1 : x ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hd := dS_pos S
  have hK := hk.kern.mass_pos
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hP10 : 0 < P1 := by positivity
  have hP00 : 0 < P0 := by positivity
  have hBI0 : 0 ≤ BI := by simp only [hBI, BIc]; positivity
  have hMI0 : 0 ≤ MI := by simp only [hMI, MIc]; have := volB_nonneg (n := n); positivity
  have hρ₁0 : 0 ≤ ρ₁ := by positivity
  have hLρ0 : 0 ≤ Lρ := mul_nonneg hLip0 hρ₁0
  have hA0 : 0 ≤ A := le_trans (hP.nonneg 0) (hP.le 0)
  have hΛ0 : 0 < Λ := by linarith
  -- masses
  obtain ⟨pa0, pa1⟩ := pmass_bounds hk S ha₀ (ha τa) (ha₁ τa) hξ
  obtain ⟨pb0, pb1⟩ := pmass_bounds hk S ha₀ (ha τb) (ha₁ τb) hξ
  have hMx : max pa pb ≤ P1 * x := max_le pa1 pb1
  have hMx0 : 0 ≤ max pa pb := le_trans (mul_nonneg hP00.le hx0.le) (le_trans pa0 (le_max_left _ _))
  have hmn : P0 * x ≤ min pa pb := le_min pa0 pb0
  have hc : 0 < min pa pb := lt_of_lt_of_le (mul_pos hP00 hx0) hmn
  have hci : (min pa pb)⁻¹ ≤ Λ * x⁻¹ := by
    calc (min pa pb)⁻¹ ≤ (P0 * x)⁻¹ := inv_anti₀ (by positivity) hmn
      _ = P0⁻¹ * x⁻¹ := mul_inv _ _
      _ ≤ Λ * x⁻¹ := mul_le_mul_of_nonneg_right lP0 (by positivity)
  -- smallness and Ctx
  have hNx : (N : ℝ) * x ≠ 0 := (mul_pos hN' hx0).ne'
  have hδ : δ ^ 2 * (N * x) = L := by
    rw [hδdef, Real.sq_sqrt (div_nonneg (by linarith) (mul_pos hN' hx0).le)]; field_simp
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hPp : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * x) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
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
  have C : Ctx N Λ x x⁻¹ δ L :=
    { hN := hN0, hΛ := l1, hx := hx0, hx1 := hx1, hxy := mul_inv_cancel₀ hx0.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL1 }
  -- constant bounds
  have hvK : A * max pa pb ≤ Λ ^ 2 * x := by
    calc A * max pa pb ≤ Λ * (P1 * x) := mul_le_mul lA hMx hMx0 hΛ0.le
      _ ≤ Λ * (Λ * x) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right lP1 hx0.le) hΛ0.le
      _ = Λ ^ 2 * x := by ring
  have hM' : max pa pb ≤ Λ * x := hMx.trans (mul_le_mul_of_nonneg_right lP1 hx0.le)
  have hMIx : MI * x ≤ Λ * x := mul_le_mul_of_nonneg_right lMI hx0.le
  have hvI : BI * (MI * x) ≤ Λ ^ 2 * x := by
    calc BI * (MI * x) ≤ Λ * (Λ * x) := mul_le_mul lBI hMIx (by positivity) hΛ0.le
      _ = Λ ^ 2 * x := by ring
  have hcD1 : (1:ℝ)⁻¹ ≤ Λ ^ 2 := by rw [inv_one]; nlinarith
  have hsmall := C.small'_le hA0 lA (mul_nonneg hA0 hMx0) hvK hMx0 hM' hc hci one_pos hcD1 hsm
  have hMF : Lρ * max pa pb ≤ Λ * x := by
    calc Lρ * max pa pb ≤ Lρ * (P1 * x) := mul_le_mul_of_nonneg_left hMx hLρ0
      _ = (P1 * Lρ) * x := by ring
      _ ≤ Λ * x := mul_le_mul_of_nonneg_right lP1Lρ hx0.le
  have hvF : Lρ ^ 2 * (A * max pa pb) ≤ Λ ^ 2 * x := by
    calc Lρ ^ 2 * (A * max pa pb) ≤ Lρ ^ 2 * (A * (P1 * x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMx hA0) (sq_nonneg _)
      _ = (A * Lρ) * (P1 * Lρ) * x := by ring
      _ ≤ Λ * Λ * x := mul_le_mul_of_nonneg_right
          (mul_le_mul lALρ lP1Lρ (by positivity) hΛ0.le) hx0.le
      _ = Λ ^ 2 * x := by ring
  have hMFi : Lρ * (MI * x) ≤ Λ * x := by
    calc Lρ * (MI * x) = (MI * Lρ) * x := by ring
      _ ≤ Λ * x := mul_le_mul_of_nonneg_right lMILρ hx0.le
  have hvFi : Lρ ^ 2 * (BI * (MI * x)) ≤ Λ ^ 2 * x := by
    calc Lρ ^ 2 * (BI * (MI * x)) = (BI * Lρ) * (MI * Lρ) * x := by ring
      _ ≤ Λ * Λ * x := mul_le_mul_of_nonneg_right
          (mul_le_mul lBILρ lMILρ (by positivity) hΛ0.le) hx0.le
      _ = Λ ^ 2 * x := by ring
  have hMIx0 : 0 ≤ MI * x := mul_nonneg hMI0 hx0.le
  have he := err5g_le C hA0 lA (mul_nonneg hA0 hMx0) hvK hBI0 lBI (mul_nonneg hBI0 hMIx0) hvI
    hMx0 hM' hMIx0 hMIx hc hci one_pos hcD1
    (mul_nonneg hA0 hLρ0) lALρ (mul_nonneg (sq_nonneg _) (mul_nonneg hA0 hMx0)) hvF
    (mul_nonneg hLρ0 hMx0) hMF
    (mul_nonneg hBI0 hLρ0) lBILρ (mul_nonneg (sq_nonneg _) (mul_nonneg hBI0 hMIx0)) hvFi
    (mul_nonneg hLρ0 hMIx0) hMFi
  -- the composite statement with ρ = ξ ρ₁
  have hρeq : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) = ξ * ρ₁ := by rw [hρ₁]; field_simp
  have H := flat_npoint X h_indep hX hlaw N hN0 hk hm₂ hP hR hf hM hM₄ hper hLip0 hLip S a a'
    hda ha₀ ha hLa hξ (le_of_eq hρeq) (by rw [← hρeq]; exact hρh) τa τb hne
    (hBI_of hP hR hLP hLh S a a' hda ha₀ ha hLa hξ τa τb hne)
    (hMI_of hP hR hLP hLh S a a' hda ha₀ ha hLa hξ τa τb hne) (by linarith)
    hsmall.1 hsmall.2
  rw [err5g_flat N hξ.le A] at H
  refine le_trans (measureReal_mono ?_) H
  intro ω hω
  obtain ⟨i, hi, hfail⟩ := hω
  refine ⟨i, hi, fun hok => hfail ?_⟩
  -- the err5g bound implies the rate bound
  set e := err5g N A (A * max pa pb) BI (BI * (MI * x)) (max pa pb) (MI * x) (min pa pb) L
    (Lip * ρ₁ * max pa pb) (A * (Lip * ρ₁)) ((Lip * ρ₁) ^ 2 * (A * max pa pb))
    (Lip * ρ₁ * (MI * x)) (BI * (Lip * ρ₁)) ((Lip * ρ₁) ^ 2 * (BI * (MI * x))) 1 with he_def
  have hbound : 2 / (m₂ * ξ ^ 2) * (ξ * e)
      ≤ 7320000 * Λ ^ 20 / m₂ * δ / ξ := by
    have h1 : 2 / (m₂ * ξ ^ 2) * (ξ * e) = 2 / m₂ * e / ξ := by field_simp
    rw [h1]
    have h2 : 2 / m₂ * e ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    calc 2 / m₂ * e / ξ ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) / ξ :=
          div_le_div_of_nonneg_right h2 hξ.le
      _ = 7320000 * Λ ^ 20 / m₂ * δ / ξ := by ring
  exact ⟨hok.1.trans hbound, hok.2.trans (add_le_add hbound le_rfl)⟩

/-- **Single pair, general `L`**, in the notation of this file (`badL`, `rateE`, `Cone`, `Ctwo`),
with the Lipschitz constant of `f` from a bound `M₁` on its derivative. -/
theorem rate_L {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * L ≤ N * ξ ^ n) :
    μ.real (badL X N h m₂ S a ξ f τa τb (rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ)
        (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S))
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  unfold badL dqI dqII popErr rateE Cone Ctwo
  exact rate_L_raw X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper
    (le_trans (norm_nonneg _) (hM₁ 0)) (lip_of_fderiv (hf.differentiable (by norm_num)) hM₁)
    S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh τa τb hne hL1 hNL

/-! ### (7) The sample normalisation at one time -/

set_option maxHeartbeats 800000 in
/-- **Lower bound of the sample normalisation at one time `g`**: outside an event of probability
`≤ N·2e^{−L}`, all `q_j(g) ≥ (K₀|det S|/a₁ⁿ) ξⁿ/2`. -/
theorem norm_event {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hP : Prof h A R) (hR : 0 ≤ R)
    {f : E → ℝ} (hfc : Continuous f) {Lip : ℝ} (hper : Per f) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (a : ℝ → ℝ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (g : ℝ) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 14 * L ≤ N * ξ ^ n) :
    μ.real {ω | ∃ j < N, sampAvg X N (perK (kap h S (ξ / a g))) j ω
        < K₀ * dS S / a₁ ^ n * ξ ^ n / 2}
      ≤ N * (2 * Real.exp (-L)) := by
  obtain ⟨l1, lA, lBI, lP1, lMI, lP0, lALρ, lBILρ, lP1Lρ, lMILρ⟩ :=
    rLam_bounds A K₀ Lh R La a₀ a₁ Lip S
  set Λ := rLam A K₀ Lh R La a₀ a₁ Lip S with hΛ
  set x := ξ ^ n with hx
  set δ := Real.sqrt (L / (N * x)) with hδdef
  set P1 := K₀ * dS S / a₀ ^ n with hP1
  set P0 := K₀ * dS S / a₁ ^ n with hP0
  set pg := pmass h S (a g) ξ with hpg
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hx0 : 0 < x := pow_pos hξ n
  have hx1 : x ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hd := dS_pos S
  have hK := hk.kern.mass_pos
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hP10 : 0 < P1 := by positivity
  have hP00 : 0 < P0 := by positivity
  have hA0 : 0 ≤ A := le_trans (hP.nonneg 0) (hP.le 0)
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨pg0, pg1⟩ := pmass_bounds hk S ha₀ (ha g) (ha₁ g) hξ
  have hc : 0 < pg := lt_of_lt_of_le (mul_pos hP00 hx0) pg0
  have hci : pg⁻¹ ≤ Λ * x⁻¹ := by
    calc pg⁻¹ ≤ (P0 * x)⁻¹ := inv_anti₀ (by positivity) pg0
      _ = P0⁻¹ * x⁻¹ := mul_inv _ _
      _ ≤ Λ * x⁻¹ := mul_le_mul_of_nonneg_right lP0 (by positivity)
  have hNx : (N : ℝ) * x ≠ 0 := (mul_pos hN' hx0).ne'
  have hδ : δ ^ 2 * (N * x) = L := by
    rw [hδdef, Real.sq_sqrt (div_nonneg (by linarith) (mul_pos hN' hx0).le)]; field_simp
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hPp : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * x) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
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
  have C : Ctx N Λ x x⁻¹ δ L :=
    { hN := hN0, hΛ := l1, hx := hx0, hx1 := hx1, hxy := mul_inv_cancel₀ hx0.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL1 }
  have hvK : A * pg ≤ Λ ^ 2 * x := by
    calc A * pg ≤ Λ * (P1 * x) := mul_le_mul lA pg1 hc.le hΛ0.le
      _ ≤ Λ * (Λ * x) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right lP1 hx0.le) hΛ0.le
      _ = Λ ^ 2 * x := by ring
  have hM' : pg ≤ Λ * x := pg1.trans (mul_le_mul_of_nonneg_right lP1 hx0.le)
  have hcD1 : (1:ℝ)⁻¹ ≤ Λ ^ 2 := by rw [inv_one]; nlinarith
  have hsmall := (C.small'_le hA0 lA (mul_nonneg hA0 hc.le) hvK hc.le hM' hc hci one_pos hcD1
    hsm).1
  have hdev : dev N A (A * pg) L ≤ pg / 2 := by
    rw [div_le_iff₀ hc] at hsmall; linarith
  -- the Bernstein template for the kernel at time `g`
  have hρg := scale_le (S := S) hξ ha₀ (ha g) hR (le_refl (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
  have hsg := kap_supp hP S (div_pos hξ (hpos g)) hρg
  have hρ0 : 0 ≤ ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (div_pos hξ ha₀).le hR)
  have hAb : ∀ w, |kap h S (ξ / a g) w| ≤ A := fun w =>
    (abs_of_nonneg (hP.nonneg (‖S.symm w‖ / (ξ / a g)))).trans_le (hP.le _)
  have habs : ∫ w, |kap h S (ξ / a g) w| = ∫ w, kap h S (ξ / a g) w :=
    integral_congr_ae (ae_of_all _ fun w =>
      abs_of_nonneg (hP.nonneg (‖S.symm w‖ / (ξ / a g))))
  have hMg : ∫ w, |kap h S (ξ / a g) w| ≤ pg := habs.le
  obtain ⟨GK, -, -, -⟩ := good_per hfc hLip0 hLip hper (kap_measurable hP.meas S (ξ / a g))
    hρ0 hρh hAb hsg hMg
  have Hp := GK.prob X h_indep hX hlaw N hN0 (by linarith : 0 < L)
  refine le_trans (measureReal_mono ?_) Hp
  intro ω hω
  obtain ⟨j, hj, hlt⟩ := hω
  refine ⟨j, hj, ?_⟩
  have hpop : popAvg mT (perK (kap h S (ξ / a g))) (X j ω) = pg := popAvg_perK _ hρh hsg _
  rw [hpop]
  have h5 : sampAvg X N (perK (kap h S (ξ / a g))) j ω < pg / 2 :=
    lt_of_lt_of_le hlt (by linarith)
  calc dev N A (A * pg) L ≤ pg / 2 := hdev
    _ < pg - sampAvg X N (perK (kap h S (ξ / a g))) j ω := by linarith
    _ ≤ |pg - sampAvg X N (perK (kap h S (ξ / a g))) j ω| := le_abs_self _
    _ = |sampAvg X N (perK (kap h S (ξ / a g))) j ω - pg| := abs_sub_comm _ _

/-! ### (8) The time grid -/

/-- The grid `{p + k w : k ≤ K}`. -/
def grid (p w : ℝ) (K : ℕ) : Finset ℝ := (Finset.range (K + 1)).image fun k : ℕ => p + k * w

theorem grid_card_le (p w : ℝ) (K : ℕ) : (grid p w K).card ≤ K + 1 :=
  Finset.card_image_le.trans (by rw [Finset.card_range])

theorem grid_cover {p q w : ℝ} (hw : 0 < w) {τ : ℝ} (hτ : τ ∈ Icc p q) :
    ∃ g ∈ grid p w ⌊(q - p) / w⌋₊, |τ - g| ≤ w := by
  have h0 : 0 ≤ (τ - p) / w := div_nonneg (by linarith [hτ.1]) hw.le
  have hk1 : ((⌊(τ - p) / w⌋₊ : ℕ) : ℝ) ≤ (τ - p) / w := Nat.floor_le h0
  have hk2 : (τ - p) / w < (⌊(τ - p) / w⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  have hkK : ⌊(τ - p) / w⌋₊ ≤ ⌊(q - p) / w⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right (by linarith [hτ.2]) hw.le)
  refine ⟨p + (⌊(τ - p) / w⌋₊ : ℕ) * w,
    Finset.mem_image.2 ⟨⌊(τ - p) / w⌋₊, Finset.mem_range.2 (by omega), rfl⟩, ?_⟩
  rw [le_div_iff₀ hw] at hk1
  rw [div_lt_iff₀ hw] at hk2
  rw [abs_le]
  constructor <;> linarith

/-! ### (9) The window statement -/

set_option maxHeartbeats 800000 in
/-- **The window statement (`prop:dotLN-diff`, flat periodic case, all pairs of times of a window
on one event).**  Setting of `flat_npoint_final`; in addition a bound `G₂` on `|lapG S f|`
(HYPOTHESIS), a window `[p, q]`, a minimal separation `η₀ > 0`, a Bernstein parameter `L ≥ 1` with
`92416 Λ¹⁴ L ≤ N ξⁿ`, and a grid width `w > 0` with
`4w ≤ η₀`, `BI·w ≤ P₀ξⁿ/4` (`P₀ = K₀|det S|/a₁ⁿ`) and `4(ℒ_N + ξ²C₂ + 2G₂L_a/a₀³)·w ≤ E·η₀`,
where `E = (7320000 Λ²⁰/m₂) √(L/(N ξⁿ))/ξ` and `ℒ_N = LNlip(…, P₀ξⁿ/4)`.
Then outside an event of probability at most
`(K+1)·N·2e^{−L} + (K+1)²·15·N·2e^{−L}`, `K = ⌊(q−p)/w⌋`, for ALL `τa, τb ∈ [p, q]` with
`|τb − τa| ≥ η₀` and all `i < N`:
(i) `|Δ_η L_N f(i) − Δ_η L_ξ f(X_i)| ≤ 2E`,
(ii) `|Δ_η L_N f(i) + Δ_η(Δ_{g_τ} f)(X_i)| ≤ 2E + 2ξ² min{C₁/|η|, C₂}`. -/
theorem flat_npoint_window {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * L ≤ N * ξ ^ n)
    {p q w η₀ : ℝ} (hw : 0 < w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀)
    (hwc : BIc Lh R La a₀ * w ≤ K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
    (hwE : 4 * (LNlip m₂ ξ A (BIc Lh R La a₀) (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
              (K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
            + (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * w
          ≤ rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ * η₀) :
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ
            + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa))}
      ≤ ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) * (N * (2 * Real.exp (-L)))
        + ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
  classical
  have hN0 : 0 < N := by omega
  have hd := dS_pos S
  have hK := hk.kern.mass_pos
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < K₀ * dS S / a₁ ^ n * ξ ^ n := by positivity
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hM0 : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hμ₄ : 0 ≤ μ₄ := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hC2 : 0 ≤ Ctwo M₄ μ₄ m₂ K₀ a₀ La S := by unfold Ctwo; positivity
  set Kg := ⌊(q - p) / w⌋₊ with hKg
  set T := grid p w Kg with hT
  set Er := rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ L N ξ with hEr
  set Pairs : Finset (ℝ × ℝ) := (T ×ˢ T).filter fun pr => pr.2 ≠ pr.1 with hPairs
  have hcardT : (T.card : ℝ) ≤ (Kg : ℝ) + 1 := by exact_mod_cast grid_card_le p w Kg
  have hcardP : (Pairs.card : ℝ) ≤ ((Kg : ℝ) + 1) ^ 2 := by
    have h1 : Pairs.card ≤ (Kg + 1) ^ 2 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, sq]
      exact Nat.mul_le_mul (grid_card_le p w Kg) (grid_card_le p w Kg)
    exact_mod_cast h1
  have hsub : {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω| ≤ 2 * Er
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * Er
            + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa))}
      ⊆ (⋃ g ∈ T, {ω | ∃ j < N, sampAvg X N (perK (kap h S (ξ / a g))) j ω
            < K₀ * dS S / a₁ ^ n * ξ ^ n / 2})
        ∪ (⋃ pr ∈ Pairs, badL X N h m₂ S a ξ f pr.1 pr.2 Er
            (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S)) := by
    intro ω hω
    by_contra hnot
    rw [mem_union, not_or] at hnot
    obtain ⟨hn, hr⟩ := hnot
    obtain ⟨τa, hτa, τb, hτb, hη, i, hi, hfail⟩ := hω
    apply hfail
    have hnorm : ∀ g ∈ T, ∀ j < N,
        K₀ * dS S / a₁ ^ n * ξ ^ n / 2 ≤ sampAvg X N (perK (kap h S (ξ / a g))) j ω := by
      intro g hg j hj
      by_contra hlt
      exact hn (Set.mem_iUnion₂.2 ⟨g, hg, ⟨j, hj, not_le.1 hlt⟩⟩)
    have hrate : ∀ ga ∈ T, ∀ gb ∈ T, gb ≠ ga → ∀ i < N,
        |dqI X N h m₂ S a ξ f ga gb i ω| ≤ Er
        ∧ |dqII X N h m₂ S a ξ f ga gb i ω|
          ≤ Er + popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (gb - ga) := by
      intro ga hga gb hgb hne i hi
      by_contra hcon
      exact hr (Set.mem_iUnion₂.2 ⟨(ga, gb),
        Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hga, hgb⟩, hne⟩, ⟨i, hi, hcon⟩⟩)
    obtain ⟨w1, w2⟩ := window_det X hN0 hk hm₂ hP hR hLP hLh hf hM hM₄ hper hM₁ S hG₂ a a' hda
      ha₀ ha hLa hξ hc hw.le hη₀ h4 hwc T (fun τ hτ => grid_cover hw hτ) ω hnorm hrate
      hτa hτb hη hi
    have hE1 := (div_le_iff₀ hη₀).2 hwE
    have hE2 : 4 * (LNlip m₂ ξ A (BIc Lh R La a₀) (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
              (K₀ * dS S / a₁ ^ n * ξ ^ n / 4) + G₂ * (2 * La / a₀ ^ 3)) * w / η₀
        ≤ 4 * (LNlip m₂ ξ A (BIc Lh R La a₀) (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
              (K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
            + (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * w / η₀ := by
      refine div_le_div_of_nonneg_right ?_ hη₀.le
      have := mul_nonneg (mul_nonneg (sq_nonneg ξ) hC2) hw.le
      linarith
    exact ⟨by linarith, by linarith⟩
  have hexp : 0 ≤ (N : ℝ) * (2 * Real.exp (-L)) := by positivity
  have h1 : μ.real (⋃ g ∈ T, {ω | ∃ j < N, sampAvg X N (perK (kap h S (ξ / a g))) j ω
            < K₀ * dS S / a₁ ^ n * ξ ^ n / 2})
      ≤ ((Kg : ℝ) + 1) * (N * (2 * Real.exp (-L))) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ g ∈ T, μ.real {ω | ∃ j < N, sampAvg X N (perK (kap h S (ξ / a g))) j ω
            < K₀ * dS S / a₁ ^ n * ξ ^ n / 2}
        ≤ ∑ g ∈ T, (N * (2 * Real.exp (-L))) := Finset.sum_le_sum fun g _ =>
          norm_event X h_indep hX hlaw N hN hk hP hR hf.continuous hper hM0
            (lip_of_fderiv hfd hM₁) S a ha₀ ha ha₁ hξ hξ1 hρh g hL1 hNL
      _ = T.card * (N * (2 * Real.exp (-L))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Kg : ℝ) + 1) * (N * (2 * Real.exp (-L))) := mul_le_mul_of_nonneg_right hcardT hexp
  have h2 : μ.real (⋃ pr ∈ Pairs, badL X N h m₂ S a ξ f pr.1 pr.2 Er
            (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S))
      ≤ ((Kg : ℝ) + 1) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ pr ∈ Pairs, μ.real (badL X N h m₂ S a ξ f pr.1 pr.2 Er
            (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S))
        ≤ ∑ pr ∈ Pairs, (15 * (N * (2 * Real.exp (-L)))) := Finset.sum_le_sum fun pr hpr =>
          rate_L X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper hM₁ S a a' hda
            ha₀ ha ha₁ hLa hξ hξ1 hρh pr.1 pr.2 (Finset.mem_filter.1 hpr).2 hL1 hNL
      _ = Pairs.card * (15 * (N * (2 * Real.exp (-L)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Kg : ℝ) + 1) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) :=
          mul_le_mul_of_nonneg_right hcardP (by positivity)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add h1 h2))

/-- **The window statement with `L = c log N`**: the probability of failure is at most
`((K+1) + 15(K+1)²)·2·N^{1−c}`, `K = ⌊(q−p)/w⌋`. -/
theorem flat_npoint_window_log {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄) (hm₂ : 0 < m₂)
    (hP : Prof h A R) (hR : 0 ≤ R) (hLP : LipProf h Lh) (hLh : 0 ≤ Lh)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ M₁ G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hM₁ : ∀ y, ‖fderiv ℝ f y‖ ≤ M₁)
    (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    {c : ℝ} (hL1 : 1 ≤ c * Real.log N)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ M₁ S ^ 14 * (c * Real.log N) ≤ N * ξ ^ n)
    {p q w η₀ : ℝ} (hw : 0 < w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀)
    (hwc : BIc Lh R La a₀ * w ≤ K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
    (hwE : 4 * (LNlip m₂ ξ A (BIc Lh R La a₀) (M₁ * (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
              (K₀ * dS S / a₁ ^ n * ξ ^ n / 4)
            + (ξ ^ 2 * Ctwo M₄ μ₄ m₂ K₀ a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * w
          ≤ rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ (c * Real.log N) N ξ * η₀) :
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqI X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ (c * Real.log N) N ξ
        ∧ |dqII X N h m₂ S a ξ f τa τb i ω|
          ≤ 2 * rateE n (rLam A K₀ Lh R La a₀ a₁ M₁ S) m₂ (c * Real.log N) N ξ
            + 2 * popErr ξ (Cone M₄ μ₄ m₂ K₀ a₀ S) (Ctwo M₄ μ₄ m₂ K₀ a₀ La S) (τb - τa))}
      ≤ (((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) + 15 * ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) ^ 2)
          * (2 * (N : ℝ) ^ (1 - c)) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hexp : (N : ℝ) * (2 * Real.exp (-(c * Real.log N))) = 2 * (N : ℝ) ^ (1 - c) := by
    rw [Real.rpow_def_of_pos hN', show Real.log N * (1 - c) = Real.log N + -(c * Real.log N) by
      ring, Real.exp_add, Real.exp_log hN']
    ring
  have H := flat_npoint_window X h_indep hX hlaw N hN hk hm₂ hP hR hLP hLh hf hM hM₄ hper hM₁
    S hG₂ a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh hL1 hNL (p := p) (q := q) hw hη₀ h4 hwc hwE
  rw [hexp] at H
  refine H.trans (le_of_eq ?_)
  ring

end CTG.FlatNPointWindow
