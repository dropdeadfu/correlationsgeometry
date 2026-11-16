import Mathlib

/-!
# Small-correlation expansion of two-mode mutual information (Proposition 4.2, analytic half)

Paper: M. Neuberger, *From Correlations to Geometry* (November 2026).

Proposition 4.2 considers two bosonic modes in a Gaussian state with equal single-mode variances
`⟨φ²⟩ = x0`, `⟨π²⟩ = p0`, cross-correlations `⟨φ_A φ_B⟩ = x`, `⟨π_A π_B⟩ = p`, and
`ν = √(x0 p0) > 1/2`. Its proof has two halves.

* **Quantum half (not formalised here).** The symplectic eigenvalues of the pair are
  `ν± = √((x0 ± x)(p0 ± p))`, the entropy of a Gaussian state is the sum of
  `f(ν) = (ν + 1/2) ln(ν + 1/2) − (ν − 1/2) ln(ν − 1/2)` over its symplectic eigenvalues, hence
  `I(A : B) = 2 f(ν) − f(ν₊) − f(ν₋)`.
* **Analytic half (this file).** With `ε = x0 p + p0 x`, as `(x, p) → 0`,

    `2 f(ν) − f(ν₊) − f(ν₋)
        = ε² [f'(ν)/(4ν³) + 1/(4ν²(ν² − 1/4))] − (f'(ν)/ν) x p + O(|(x, p)|⁴)`,     (4.2)

  where `f'(ν) = ln((ν + 1/2)/(ν − 1/2))`.

The formula `2 f(ν) − f(ν₊) − f(ν₋)` enters as the *definition* `twoModeMI`. What Lean checks is
that this expression has the expansion (4.2), with a remainder of fourth order.

Main results:

* `hasDerivAt_entropyFn`: `f'(ν) = ln((ν + 1/2)/(ν − 1/2))` for `ν > 1/2`;
* `hasDerivAt_entropyFnDeriv`: `f''(ν) = −1/(ν² − 1/4)` for `ν > 1/2`;
* `two_mode_expansion`: equation (4.2) with an explicit remainder bound `C (x² + p²)²` for
  `|x|, |p| ≤ δ`;
* `two_mode_expansion_isBigO`: the same statement written as `O(‖(x, p)‖⁴)` near `0`;
* `twoModeMI_neg`: the symmetry `(x, p) ↦ (−x, −p)` used in the paper's proof.

The proof does not expand `ν±` as the paper does. It writes `f(ν±) = g(s₀ + a ± b)` with
`g(s) = f(√s)`, `s₀ = x0 p0`, `a = x p`, `b = ε`, and uses a general estimate
(`exists_abs_expansion_sub_le`) for four times continuously differentiable `g`:

  `|g(s₀ + a + b) + g(s₀ + a − b) − 2 g(s₀) − 2 g'(s₀) a − g''(s₀) b²| ≤ M (2a² + |a| b² + 2b⁴)`.

The odd powers of `b` cancel between the two terms, which is the paper's parity argument.
-/

open Set Filter Topology

namespace CorrelationsGeometry

/-! ## Mean value estimates -/

/-- If `φ 0 = 0` and `|φ'| ≤ K` between `0` and `t`, then `|φ t| ≤ K |t|`. -/
theorem abs_le_mul_abs_of_hasDerivAt {φ φ' : ℝ → ℝ} {t K : ℝ}
    (hd : ∀ τ, |τ| ≤ |t| → HasDerivAt φ (φ' τ) τ) (h0 : φ 0 = 0)
    (hb : ∀ τ, |τ| ≤ |t| → |φ' τ| ≤ K) : |φ t| ≤ K * |t| := by
  have h := (convex_Icc (-|t|) |t|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := φ) (f' := φ') (x := 0) (y := t) (C := K)
    (fun τ hτ => (hd τ (abs_le.mpr hτ)).hasDerivWithinAt)
    (fun τ hτ => by rw [Real.norm_eq_abs]; exact hb τ (abs_le.mpr hτ))
    ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩ ⟨neg_abs_le t, le_abs_self t⟩
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

section Local

variable {s₀ r M : ℝ}

/-- A function whose derivative is bounded by `M` near `s₀` is `M`-Lipschitz there. -/
theorem abs_shift_sub_le {h h1 : ℝ → ℝ}
    (hd : ∀ u, |u - s₀| ≤ r → HasDerivAt h (h1 u) u)
    (hM : ∀ u, |u - s₀| ≤ r → |h1 u| ≤ M) {c t : ℝ} (hct : |c - s₀| + |t| ≤ r) :
    |h (c + t) - h c| ≤ M * |t| := by
  have hp : ∀ τ, |τ| ≤ |t| → |c + τ - s₀| ≤ r := fun τ hτ => by
    have h' : |c + τ - s₀| ≤ |c - s₀| + |τ| := by
      rw [show c + τ - s₀ = (c - s₀) + τ by ring]
      exact abs_add_le _ _
    linarith
  have key := abs_le_mul_abs_of_hasDerivAt
    (φ := fun τ => h (c + τ) - h c) (φ' := fun τ => h1 (c + τ)) (t := t) (K := M)
    (fun τ hτ => ((hd _ (hp τ hτ)).comp_const_add c τ).sub_const (h c))
    (by show h (c + 0) - h c = 0; rw [add_zero, sub_self])
    (fun τ hτ => hM _ (hp τ hτ))
  exact key

/-- First-order Taylor estimate: if `|h''| ≤ M` near `s₀` then
`|h (c + t) − h c − h' c · t| ≤ M t²`. -/
theorem abs_shift_sub_sub_le {h h1 h2 : ℝ → ℝ}
    (hd1 : ∀ u, |u - s₀| ≤ r → HasDerivAt h (h1 u) u)
    (hd2 : ∀ u, |u - s₀| ≤ r → HasDerivAt h1 (h2 u) u)
    (hM : ∀ u, |u - s₀| ≤ r → |h2 u| ≤ M) {c t : ℝ} (hct : |c - s₀| + |t| ≤ r) :
    |h (c + t) - h c - h1 c * t| ≤ M * t ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (by linarith [abs_nonneg t]))
  have hp : ∀ τ, |τ| ≤ |t| → |c + τ - s₀| ≤ r := fun τ hτ => by
    have h' : |c + τ - s₀| ≤ |c - s₀| + |τ| := by
      rw [show c + τ - s₀ = (c - s₀) + τ by ring]
      exact abs_add_le _ _
    linarith
  have key := abs_le_mul_abs_of_hasDerivAt
    (φ := fun τ => h (c + τ) - h c - h1 c * τ) (φ' := fun τ => h1 (c + τ) - h1 c)
    (t := t) (K := M * |t|)
    (fun τ hτ => by
      have e1 := ((hd1 _ (hp τ hτ)).comp_const_add c τ).sub_const (h c)
      have e2 := (hasDerivAt_id' τ).const_mul (h1 c)
      have e : HasDerivAt (fun x => h (c + x) - h c - h1 c * x) (h1 (c + τ) - h1 c) τ :=
        (e1.fun_sub e2).congr_deriv (by ring)
      exact e)
    (by show h (c + 0) - h c - h1 c * 0 = 0; rw [add_zero, sub_self, mul_zero, sub_zero])
    (fun τ hτ => by
      have b := abs_shift_sub_le hd2 hM (c := c) (t := τ) (by linarith)
      exact b.trans (mul_le_mul_of_nonneg_left hτ hM0))
  calc |h (c + t) - h c - h1 c * t| ≤ M * |t| * |t| := key
    _ = M * t ^ 2 := by rw [mul_assoc, abs_mul_abs_self, sq]

/-- Second symmetric difference: if `|h⁗| ≤ M` near `s₀` then
`|h (c + t) + h (c − t) − 2 h c − h'' c · t²| ≤ 2 M t⁴`. -/
theorem abs_symm_diff_sub_le {h h1 h2 h3 h4 : ℝ → ℝ}
    (hd1 : ∀ u, |u - s₀| ≤ r → HasDerivAt h (h1 u) u)
    (hd2 : ∀ u, |u - s₀| ≤ r → HasDerivAt h1 (h2 u) u)
    (hd3 : ∀ u, |u - s₀| ≤ r → HasDerivAt h2 (h3 u) u)
    (hd4 : ∀ u, |u - s₀| ≤ r → HasDerivAt h3 (h4 u) u)
    (hM : ∀ u, |u - s₀| ≤ r → |h4 u| ≤ M) {c t : ℝ} (hct : |c - s₀| + |t| ≤ r) :
    |h (c + t) + h (c - t) - 2 * h c - h2 c * t ^ 2| ≤ 2 * M * t ^ 4 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (by linarith [abs_nonneg t]))
  have h2M : 0 ≤ 2 * M := by linarith
  have hp : ∀ τ, |τ| ≤ |t| → |c + τ - s₀| ≤ r := fun τ hτ => by
    have h' : |c + τ - s₀| ≤ |c - s₀| + |τ| := by
      rw [show c + τ - s₀ = (c - s₀) + τ by ring]
      exact abs_add_le _ _
    linarith
  have hm : ∀ τ, |τ| ≤ |t| → |c - τ - s₀| ≤ r := fun τ hτ => by
    have h' : |c - τ - s₀| ≤ |c - s₀| + |τ| := by
      rw [show c - τ - s₀ = (c - s₀) + -τ by ring, ← abs_neg τ]
      exact abs_add_le _ _
    linarith
  -- Step 1: the second symmetric difference of `h2` is of second order.
  have ha : ∀ τ, |τ| ≤ |t| → |h2 (c + τ) + h2 (c - τ) - 2 * h2 c| ≤ 2 * M * τ ^ 2 := by
    intro τ hτ
    have key := abs_le_mul_abs_of_hasDerivAt
      (φ := fun σ => h2 (c + σ) + h2 (c - σ) - 2 * h2 c)
      (φ' := fun σ => h3 (c + σ) - h3 (c - σ)) (t := τ) (K := 2 * M * |τ|)
      (fun σ hσ => by
        have e1 := (hd3 _ (hp σ (hσ.trans hτ))).comp_const_add c σ
        have e2 := (hd3 _ (hm σ (hσ.trans hτ))).comp_const_sub c σ
        have e : HasDerivAt (fun x => h2 (c + x) + h2 (c - x) - 2 * h2 c)
            (h3 (c + σ) - h3 (c - σ)) σ :=
          ((e1.fun_add e2).sub_const (2 * h2 c)).congr_deriv (by ring)
        exact e)
      (by show h2 (c + 0) + h2 (c - 0) - 2 * h2 c = 0; rw [add_zero, sub_zero]; ring)
      (fun σ hσ => by
        have hσt : |σ| ≤ |t| := hσ.trans hτ
        have b1 : |h3 (c + σ) - h3 c| ≤ M * |σ| :=
          abs_shift_sub_le hd4 hM (c := c) (t := σ) (by linarith)
        have b2 : |h3 (c + -σ) - h3 c| ≤ M * |-σ| :=
          abs_shift_sub_le hd4 hM (c := c) (t := -σ) (by rw [abs_neg]; linarith)
        rw [abs_neg, ← sub_eq_add_neg, abs_sub_comm] at b2
        have b3 : |h3 (c + σ) - h3 (c - σ)| ≤ |h3 (c + σ) - h3 c| + |h3 c - h3 (c - σ)| :=
          abs_sub_le _ _ _
        have b4 : M * |σ| ≤ M * |τ| := mul_le_mul_of_nonneg_left hσ hM0
        change |h3 (c + σ) - h3 (c - σ)| ≤ 2 * M * |τ|
        linarith)
    calc |h2 (c + τ) + h2 (c - τ) - 2 * h2 c| ≤ 2 * M * |τ| * |τ| := key
      _ = 2 * M * τ ^ 2 := by rw [mul_assoc, abs_mul_abs_self, sq]
  -- Step 2: integrate once.
  have hb : ∀ τ, |τ| ≤ |t| →
      |h1 (c + τ) - h1 (c - τ) - 2 * h2 c * τ| ≤ 2 * M * τ ^ 2 * |τ| := by
    intro τ hτ
    have key := abs_le_mul_abs_of_hasDerivAt
      (φ := fun σ => h1 (c + σ) - h1 (c - σ) - 2 * h2 c * σ)
      (φ' := fun σ => h2 (c + σ) + h2 (c - σ) - 2 * h2 c) (t := τ) (K := 2 * M * τ ^ 2)
      (fun σ hσ => by
        have e1 := (hd2 _ (hp σ (hσ.trans hτ))).comp_const_add c σ
        have e2 := (hd2 _ (hm σ (hσ.trans hτ))).comp_const_sub c σ
        have e3 := (hasDerivAt_id' σ).const_mul (2 * h2 c)
        have e : HasDerivAt (fun x => h1 (c + x) - h1 (c - x) - 2 * h2 c * x)
            (h2 (c + σ) + h2 (c - σ) - 2 * h2 c) σ :=
          ((e1.fun_sub e2).fun_sub e3).congr_deriv (by ring)
        exact e)
      (by show h1 (c + 0) - h1 (c - 0) - 2 * h2 c * 0 = 0; rw [add_zero, sub_zero]; ring)
      (fun σ hσ => (ha σ (hσ.trans hτ)).trans
        (mul_le_mul_of_nonneg_left (sq_le_sq.mpr hσ) h2M))
    exact key
  -- Step 3: integrate once more.
  have key := abs_le_mul_abs_of_hasDerivAt
    (φ := fun τ => h (c + τ) + h (c - τ) - 2 * h c - h2 c * τ ^ 2)
    (φ' := fun τ => h1 (c + τ) - h1 (c - τ) - 2 * h2 c * τ) (t := t) (K := 2 * M * t ^ 2 * |t|)
    (fun τ hτ => by
      have e1 := (hd1 _ (hp τ hτ)).comp_const_add c τ
      have e2 := (hd1 _ (hm τ hτ)).comp_const_sub c τ
      have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * τ) τ := by
        simpa using hasDerivAt_pow 2 τ
      have e3 := hsq.const_mul (h2 c)
      have e : HasDerivAt (fun x => h (c + x) + h (c - x) - 2 * h c - h2 c * x ^ 2)
          (h1 (c + τ) - h1 (c - τ) - 2 * h2 c * τ) τ :=
        (((e1.fun_add e2).sub_const (2 * h c)).fun_sub e3).congr_deriv (by ring)
      exact e)
    (by show h (c + 0) + h (c - 0) - 2 * h c - h2 c * 0 ^ 2 = 0; rw [add_zero, sub_zero]; ring)
    (fun τ hτ => (hb τ hτ).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (sq_le_sq.mpr hτ) h2M) hτ (abs_nonneg τ)
        (mul_nonneg h2M (sq_nonneg t))))
  calc |h (c + t) + h (c - t) - 2 * h c - h2 c * t ^ 2| ≤ 2 * M * t ^ 2 * |t| * |t| := key
    _ = 2 * M * t ^ 4 := by rw [mul_assoc, abs_mul_abs_self]; ring

/-- **Second-order expansion with a fourth-order symmetric remainder.** If `g` has derivatives
`g1, …, g4` near `s₀` and `|g2|, |g3|, |g4| ≤ M` there, then
`g (s₀ + a + b) + g (s₀ + a − b) = 2 g s₀ + 2 g1 s₀ · a + g2 s₀ · b²` up to
`M (2a² + |a| b² + 2b⁴)`. No odd power of `b` appears. -/
theorem abs_expansion_sub_le {g g1 g2 g3 g4 : ℝ → ℝ}
    (hd1 : ∀ u, |u - s₀| ≤ r → HasDerivAt g (g1 u) u)
    (hd2 : ∀ u, |u - s₀| ≤ r → HasDerivAt g1 (g2 u) u)
    (hd3 : ∀ u, |u - s₀| ≤ r → HasDerivAt g2 (g3 u) u)
    (hd4 : ∀ u, |u - s₀| ≤ r → HasDerivAt g3 (g4 u) u)
    (hM2 : ∀ u, |u - s₀| ≤ r → |g2 u| ≤ M)
    (hM3 : ∀ u, |u - s₀| ≤ r → |g3 u| ≤ M)
    (hM4 : ∀ u, |u - s₀| ≤ r → |g4 u| ≤ M) {a b : ℝ} (hab : |a| + |b| ≤ r) :
    |g (s₀ + a + b) + g (s₀ + a - b) - 2 * g s₀ - 2 * g1 s₀ * a - g2 s₀ * b ^ 2|
      ≤ M * (2 * a ^ 2 + |a| * b ^ 2 + 2 * b ^ 4) := by
  have hc : |s₀ + a - s₀| + |b| ≤ r := by rw [add_sub_cancel_left]; exact hab
  have h0 : |s₀ - s₀| + |a| ≤ r := by rw [sub_self, abs_zero, zero_add]; linarith [abs_nonneg b]
  have T1 : |g (s₀ + a + b) + g (s₀ + a - b) - 2 * g (s₀ + a) - g2 (s₀ + a) * b ^ 2|
      ≤ 2 * M * b ^ 4 := abs_symm_diff_sub_le hd1 hd2 hd3 hd4 hM4 hc
  have T2 : |g (s₀ + a) - g s₀ - g1 s₀ * a| ≤ M * a ^ 2 := abs_shift_sub_sub_le hd1 hd2 hM2 h0
  have T3 : |g2 (s₀ + a) - g2 s₀| ≤ M * |a| := abs_shift_sub_le hd3 hM3 h0
  have B2 : |2 * (g (s₀ + a) - g s₀ - g1 s₀ * a)| ≤ 2 * (M * a ^ 2) := by
    rw [abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left T2 (by norm_num)
  have B3 : |(g2 (s₀ + a) - g2 s₀) * b ^ 2| ≤ M * |a| * b ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg b)]
    exact mul_le_mul_of_nonneg_right T3 (sq_nonneg b)
  have e : g (s₀ + a + b) + g (s₀ + a - b) - 2 * g s₀ - 2 * g1 s₀ * a - g2 s₀ * b ^ 2
      = (g (s₀ + a + b) + g (s₀ + a - b) - 2 * g (s₀ + a) - g2 (s₀ + a) * b ^ 2)
        + 2 * (g (s₀ + a) - g s₀ - g1 s₀ * a) + (g2 (s₀ + a) - g2 s₀) * b ^ 2 := by ring
  rw [e]
  have tri := abs_add_three
    (g (s₀ + a + b) + g (s₀ + a - b) - 2 * g (s₀ + a) - g2 (s₀ + a) * b ^ 2)
    (2 * (g (s₀ + a) - g s₀ - g1 s₀ * a)) ((g2 (s₀ + a) - g2 s₀) * b ^ 2)
  linarith

end Local

/-- The estimate `abs_expansion_sub_le` for any function that is four times continuously
differentiable on an open set containing `s₀`, with the derivatives taken by `deriv`. -/
theorem exists_abs_expansion_sub_le {g : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hg : ContDiffOn ℝ 4 g J) {s₀ : ℝ} (hs : s₀ ∈ J) :
    ∃ M r : ℝ, 0 ≤ M ∧ 0 < r ∧ ∀ a b : ℝ, |a| + |b| ≤ r →
      |g (s₀ + a + b) + g (s₀ + a - b) - 2 * g s₀ - 2 * deriv g s₀ * a
          - deriv (deriv g) s₀ * b ^ 2| ≤ M * (2 * a ^ 2 + |a| * b ^ 2 + 2 * b ^ 4) := by
  obtain ⟨r, hr, hrJ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hJ.mem_nhds hs)
  have hball : ∀ u, |u - s₀| ≤ r → u ∈ Metric.closedBall s₀ r := fun u hu => by
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact hu
  have hg1 : ContDiffOn ℝ 3 (deriv g) J := hg.deriv_of_isOpen hJ (by norm_num)
  have hg2 : ContDiffOn ℝ 2 (deriv (deriv g)) J := hg1.deriv_of_isOpen hJ (by norm_num)
  have hg3 : ContDiffOn ℝ 1 (deriv (deriv (deriv g))) J := hg2.deriv_of_isOpen hJ (by norm_num)
  have hg4 : ContDiffOn ℝ 0 (deriv (deriv (deriv (deriv g)))) J :=
    hg3.deriv_of_isOpen hJ (by norm_num)
  have hd : ∀ (n : WithTop ℕ∞) (h : ℝ → ℝ), ContDiffOn ℝ n h J → n ≠ 0 →
      ∀ u, |u - s₀| ≤ r → HasDerivAt h (deriv h u) u := fun n h hh hn u hu =>
    ((hh.differentiableOn hn).differentiableAt (hJ.mem_nhds (hrJ (hball u hu)))).hasDerivAt
  have hK : IsCompact (Metric.closedBall s₀ r) := isCompact_closedBall s₀ r
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn (hg2.continuousOn.mono hrJ)
  obtain ⟨C3, hC3⟩ := hK.exists_bound_of_continuousOn (hg3.continuousOn.mono hrJ)
  obtain ⟨C4, hC4⟩ := hK.exists_bound_of_continuousOn (hg4.continuousOn.mono hrJ)
  refine ⟨max C2 (max C3 C4), r, ?_, hr, fun a b hab => ?_⟩
  · exact (norm_nonneg _).trans
      ((hC2 s₀ (Metric.mem_closedBall_self hr.le)).trans (le_max_left _ _))
  · exact abs_expansion_sub_le (hd 4 g hg (by norm_num)) (hd 3 _ hg1 (by norm_num))
      (hd 2 _ hg2 (by norm_num)) (hd 1 _ hg3 one_ne_zero)
      (fun u hu => by
        rw [← Real.norm_eq_abs]
        exact (hC2 u (hball u hu)).trans (le_max_left _ _))
      (fun u hu => by
        rw [← Real.norm_eq_abs]
        exact (hC3 u (hball u hu)).trans ((le_max_left _ _).trans (le_max_right _ _)))
      (fun u hu => by
        rw [← Real.norm_eq_abs]
        exact (hC4 u (hball u hu)).trans ((le_max_right _ _).trans (le_max_right _ _)))
      hab

/-! ## The entropy function of one mode -/

/-- The entropy of one bosonic mode with symplectic eigenvalue `ν`:
`f(ν) = (ν + 1/2) ln(ν + 1/2) − (ν − 1/2) ln(ν − 1/2)`. -/
noncomputable def entropyFn (ν : ℝ) : ℝ :=
  (ν + 1 / 2) * Real.log (ν + 1 / 2) - (ν - 1 / 2) * Real.log (ν - 1 / 2)

/-- The derivative of `entropyFn`: `f'(ν) = ln((ν + 1/2)/(ν − 1/2))`. -/
noncomputable def entropyFnDeriv (ν : ℝ) : ℝ :=
  Real.log ((ν + 1 / 2) / (ν - 1 / 2))

/-- **Proposition 4.2**, `f'(ν) = ln((ν + 1/2)/(ν − 1/2))`. -/
theorem hasDerivAt_entropyFn {ν : ℝ} (hν : 1 / 2 < ν) :
    HasDerivAt entropyFn (entropyFnDeriv ν) ν := by
  have hp : ν + 1 / 2 ≠ 0 := (by linarith : (0 : ℝ) < ν + 1 / 2).ne'
  have hm : ν - 1 / 2 ≠ 0 := (by linarith : (0 : ℝ) < ν - 1 / 2).ne'
  have e1 : HasDerivAt (fun y : ℝ => y + 1 / 2) 1 ν := (hasDerivAt_id' ν).add_const _
  have e2 : HasDerivAt (fun y : ℝ => y - 1 / 2) 1 ν := (hasDerivAt_id' ν).sub_const _
  have e : HasDerivAt
      (fun y : ℝ => (y + 1 / 2) * Real.log (y + 1 / 2) - (y - 1 / 2) * Real.log (y - 1 / 2))
      (entropyFnDeriv ν) ν := by
    refine ((e1.fun_mul (e1.log hp)).fun_sub (e2.fun_mul (e2.log hm))).congr_deriv ?_
    unfold entropyFnDeriv
    rw [Real.log_div hp hm, mul_one_div_cancel hp, mul_one_div_cancel hm]
    ring
  exact e

/-- **Proposition 4.2 (proof)**, `f''(ν) = −1/(ν² − 1/4)`. -/
theorem hasDerivAt_entropyFnDeriv {ν : ℝ} (hν : 1 / 2 < ν) :
    HasDerivAt entropyFnDeriv (-1 / (ν ^ 2 - 1 / 4)) ν := by
  have hp : ν + 1 / 2 ≠ 0 := (by linarith : (0 : ℝ) < ν + 1 / 2).ne'
  have hm : ν - 1 / 2 ≠ 0 := (by linarith : (0 : ℝ) < ν - 1 / 2).ne'
  have hq : ν ^ 2 - 1 / 4 ≠ 0 := (by nlinarith : (0 : ℝ) < ν ^ 2 - 1 / 4).ne'
  have e1 : HasDerivAt (fun y : ℝ => y + 1 / 2) 1 ν := (hasDerivAt_id' ν).add_const _
  have e2 : HasDerivAt (fun y : ℝ => y - 1 / 2) 1 ν := (hasDerivAt_id' ν).sub_const _
  have e : HasDerivAt (fun y : ℝ => Real.log ((y + 1 / 2) / (y - 1 / 2)))
      (-1 / (ν ^ 2 - 1 / 4)) ν := by
    refine ((e1.fun_div e2 hm).log (div_ne_zero hp hm)).congr_deriv ?_
    rw [show ν ^ 2 - 1 / 4 = (ν - 1 / 2) * (ν + 1 / 2) by ring]
    field_simp
    ring
  exact e

/-! ## The function `g(s) = f(√s)` -/

theorem half_lt_sqrt {s : ℝ} (hs : 1 / 4 < s) : 1 / 2 < √s := by
  rw [Real.lt_sqrt (by norm_num)]
  calc ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
    _ < s := hs

/-- `s ↦ f(√s)` is four times continuously differentiable on `(1/4, ∞)`. -/
theorem contDiffOn_entropyFn_sqrt :
    ContDiffOn ℝ 4 (fun s : ℝ => entropyFn (√s)) (Ioi (1 / 4)) := by
  intro s hs
  have hs' : (1 : ℝ) / 4 < s := hs
  have hs0 : s ≠ 0 := (by linarith : (0 : ℝ) < s).ne'
  have hsq : 1 / 2 < √s := half_lt_sqrt hs'
  have h0 : ContDiffAt ℝ 4 (fun s : ℝ => √s) s := Real.contDiffAt_sqrt hs0
  have hA : ContDiffAt ℝ 4 (fun s : ℝ => √s + 1 / 2) s := h0.add contDiffAt_const
  have hB : ContDiffAt ℝ 4 (fun s : ℝ => √s - 1 / 2) s := h0.sub contDiffAt_const
  have h : ContDiffAt ℝ 4
      (fun s : ℝ => (√s + 1 / 2) * Real.log (√s + 1 / 2) - (√s - 1 / 2) * Real.log (√s - 1 / 2))
      s :=
    (hA.mul (hA.log (by linarith : (0 : ℝ) < √s + 1 / 2).ne')).sub
      (hB.mul (hB.log (by linarith : (0 : ℝ) < √s - 1 / 2).ne'))
  exact h.contDiffWithinAt

/-- `g'(s) = f'(√s) / (2√s)`. -/
theorem hasDerivAt_entropyFn_sqrt {s : ℝ} (hs : 1 / 4 < s) :
    HasDerivAt (fun s : ℝ => entropyFn (√s)) (entropyFnDeriv (√s) / (2 * √s)) s := by
  have hs0 : s ≠ 0 := (by linarith : (0 : ℝ) < s).ne'
  have e : HasDerivAt (fun s : ℝ => entropyFn (√s)) (entropyFnDeriv (√s) * (1 / (2 * √s))) s :=
    (hasDerivAt_entropyFn (half_lt_sqrt hs)).comp s (Real.hasDerivAt_sqrt hs0)
  exact e.congr_deriv (mul_one_div _ _)

/-- `g''(s) = −1/(4ν²(ν² − 1/4)) − f'(ν)/(4ν³)` with `ν = √s`. -/
theorem hasDerivAt_entropyFnDeriv_sqrt_div {s : ℝ} (hs : 1 / 4 < s) :
    HasDerivAt (fun s : ℝ => entropyFnDeriv (√s) / (2 * √s))
      (-(1 / (4 * √s ^ 2 * (√s ^ 2 - 1 / 4))) - entropyFnDeriv (√s) / (4 * √s ^ 3)) s := by
  have hs0 : s ≠ 0 := (by linarith : (0 : ℝ) < s).ne'
  have hsq : 1 / 2 < √s := half_lt_sqrt hs
  have hν0 : √s ≠ 0 := (by linarith : (0 : ℝ) < √s).ne'
  have hq : √s ^ 2 - 1 / 4 ≠ 0 := (by nlinarith : (0 : ℝ) < √s ^ 2 - 1 / 4).ne'
  have eN : HasDerivAt (fun s : ℝ => entropyFnDeriv (√s))
      (-1 / (√s ^ 2 - 1 / 4) * (1 / (2 * √s))) s :=
    (hasDerivAt_entropyFnDeriv hsq).comp s (Real.hasDerivAt_sqrt hs0)
  have eD : HasDerivAt (fun s : ℝ => 2 * √s) (2 * (1 / (2 * √s))) s :=
    (Real.hasDerivAt_sqrt hs0).const_mul 2
  refine (eN.fun_div eD (mul_ne_zero two_ne_zero hν0)).congr_deriv ?_
  field_simp
  ring

/-! ## Proposition 4.2 -/

/-- The mutual information of the two modes as given by the symplectic eigenvalues,
`I = 2 f(ν) − f(ν₊) − f(ν₋)` with `ν = √(x0 p0)` and `ν± = √((x0 ± x)(p0 ± p))`.

That this expression is the mutual information of the Gaussian state is the quantum half of
Proposition 4.2 and is not proven here. -/
noncomputable def twoModeMI (x0 p0 x p : ℝ) : ℝ :=
  2 * entropyFn (√(x0 * p0)) - entropyFn (√((x0 + x) * (p0 + p)))
    - entropyFn (√((x0 - x) * (p0 - p)))

/-- The leading terms on the right-hand side of (4.2):
`ε² [f'(ν)/(4ν³) + 1/(4ν²(ν² − 1/4))] − (f'(ν)/ν) x p` with `ε = x0 p + p0 x`. -/
noncomputable def twoModeMILeading (x0 p0 x p : ℝ) : ℝ :=
  (x0 * p + p0 * x) ^ 2 *
      (entropyFnDeriv (√(x0 * p0)) / (4 * √(x0 * p0) ^ 3)
        + 1 / (4 * √(x0 * p0) ^ 2 * (√(x0 * p0) ^ 2 - 1 / 4)))
    - entropyFnDeriv (√(x0 * p0)) / √(x0 * p0) * (x * p)

@[simp]
theorem twoModeMI_zero (x0 p0 : ℝ) : twoModeMI x0 p0 0 0 = 0 := by
  unfold twoModeMI
  rw [add_zero, add_zero, sub_zero, sub_zero]
  ring

/-- `I` is even under `(x, p) ↦ (−x, −p)`, which exchanges `ν₊` and `ν₋`. -/
theorem twoModeMI_neg (x0 p0 x p : ℝ) : twoModeMI x0 p0 (-x) (-p) = twoModeMI x0 p0 x p := by
  unfold twoModeMI
  rw [← sub_eq_add_neg, ← sub_eq_add_neg, sub_neg_eq_add, sub_neg_eq_add]
  ring

/-- **Proposition 4.2, equation (4.2).** For `ν = √(x0 p0) > 1/2` there are `C` and `δ > 0` with

  `|I − (ε² [f'(ν)/(4ν³) + 1/(4ν²(ν² − 1/4))] − (f'(ν)/ν) x p)| ≤ C (x² + p²)²`

for all `|x|, |p| ≤ δ`, where `I = 2 f(ν) − f(ν₊) − f(ν₋)`. -/
theorem two_mode_expansion (x0 p0 : ℝ) (hν : 1 / 2 < √(x0 * p0)) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x p : ℝ, |x| ≤ δ → |p| ≤ δ →
      |twoModeMI x0 p0 x p - twoModeMILeading x0 p0 x p| ≤ C * (x ^ 2 + p ^ 2) ^ 2 := by
  have hs : (1 : ℝ) / 4 < x0 * p0 := by
    have h := (Real.lt_sqrt (by norm_num)).mp hν
    calc (1 : ℝ) / 4 = (1 / 2) ^ 2 := by norm_num
      _ < x0 * p0 := h
  obtain ⟨M, r, hM, hr, hbound⟩ :=
    exists_abs_expansion_sub_le isOpen_Ioi contDiffOn_entropyFn_sqrt (s₀ := x0 * p0) hs
  have hd1 : deriv (fun s : ℝ => entropyFn (√s)) (x0 * p0)
      = entropyFnDeriv (√(x0 * p0)) / (2 * √(x0 * p0)) := (hasDerivAt_entropyFn_sqrt hs).deriv
  have hd2 : deriv (deriv fun s : ℝ => entropyFn (√s)) (x0 * p0)
      = -(1 / (4 * √(x0 * p0) ^ 2 * (√(x0 * p0) ^ 2 - 1 / 4)))
        - entropyFnDeriv (√(x0 * p0)) / (4 * √(x0 * p0) ^ 3) := by
    have hev : (deriv fun s : ℝ => entropyFn (√s))
        =ᶠ[𝓝 (x0 * p0)] fun s : ℝ => entropyFnDeriv (√s) / (2 * √s) := by
      filter_upwards [isOpen_Ioi.mem_nhds hs] with s hs'
      exact (hasDerivAt_entropyFn_sqrt hs').deriv
    rw [hev.deriv_eq]
    exact (hasDerivAt_entropyFnDeriv_sqrt_div hs).deriv
  rw [hd1, hd2] at hbound
  have hpos : 0 < 1 + |x0| + |p0| := by positivity
  have hK : 0 ≤ x0 ^ 2 + p0 ^ 2 := by positivity
  refine ⟨M * (2 + (x0 ^ 2 + p0 ^ 2) + 2 * (x0 ^ 2 + p0 ^ 2) ^ 2),
    min 1 (r / (1 + |x0| + |p0|)), by positivity, lt_min one_pos (div_pos hr hpos), ?_⟩
  intro x p hx hp
  have hδ1 : min 1 (r / (1 + |x0| + |p0|)) ≤ 1 := min_le_left _ _
  have hδr : min 1 (r / (1 + |x0| + |p0|)) * (1 + |x0| + |p0|) ≤ r :=
    (le_div_iff₀ hpos).mp (min_le_right _ _)
  have hδ0 : 0 ≤ min 1 (r / (1 + |x0| + |p0|)) := (abs_nonneg x).trans hx
  -- the arguments stay inside the radius `r`
  have hab : |x * p| + |x0 * p + p0 * x| ≤ r := by
    have h1 : |x * p| ≤ min 1 (r / (1 + |x0| + |p0|)) := by
      rw [abs_mul]
      calc |x| * |p| ≤ min 1 (r / (1 + |x0| + |p0|)) * 1 :=
            mul_le_mul hx (hp.trans hδ1) (abs_nonneg p) hδ0
        _ = min 1 (r / (1 + |x0| + |p0|)) := mul_one _
    have h2 : |x0 * p + p0 * x| ≤ |x0| * min 1 (r / (1 + |x0| + |p0|))
        + |p0| * min 1 (r / (1 + |x0| + |p0|)) := by
      calc |x0 * p + p0 * x| ≤ |x0 * p| + |p0 * x| := abs_add_le _ _
        _ = |x0| * |p| + |p0| * |x| := by rw [abs_mul, abs_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg x0))
            (mul_le_mul_of_nonneg_left hx (abs_nonneg p0))
    linarith
  have hb := hbound (x * p) (x0 * p + p0 * x) hab
  rw [show x0 * p0 + x * p + (x0 * p + p0 * x) = (x0 + x) * (p0 + p) by ring,
    show x0 * p0 + x * p - (x0 * p + p0 * x) = (x0 - x) * (p0 - p) by ring] at hb
  -- the quantity in `hb` is minus the quantity to bound
  have e : twoModeMI x0 p0 x p - twoModeMILeading x0 p0 x p
      = -(entropyFn (√((x0 + x) * (p0 + p))) + entropyFn (√((x0 - x) * (p0 - p)))
          - 2 * entropyFn (√(x0 * p0))
          - 2 * (entropyFnDeriv (√(x0 * p0)) / (2 * √(x0 * p0))) * (x * p)
          - (-(1 / (4 * √(x0 * p0) ^ 2 * (√(x0 * p0) ^ 2 - 1 / 4)))
              - entropyFnDeriv (√(x0 * p0)) / (4 * √(x0 * p0) ^ 3)) * (x0 * p + p0 * x) ^ 2) := by
    unfold twoModeMI twoModeMILeading
    ring
  rw [e, abs_neg]
  refine hb.trans ?_
  -- bound the remainder by a multiple of `(x² + p²)²`
  have hρ : 0 ≤ x ^ 2 + p ^ 2 := by positivity
  have ha2 : (x * p) ^ 2 ≤ (x ^ 2 + p ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (p ^ 2), mul_nonneg (sq_nonneg x) (sq_nonneg p)]
  have ha1 : |x * p| ≤ x ^ 2 + p ^ 2 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (x + p)], by nlinarith [sq_nonneg (x - p)]⟩
  have hb2 : (x0 * p + p0 * x) ^ 2 ≤ (x0 ^ 2 + p0 ^ 2) * (x ^ 2 + p ^ 2) := by
    nlinarith [sq_nonneg (x0 * x - p0 * p)]
  have t2 : |x * p| * (x0 * p + p0 * x) ^ 2
      ≤ (x ^ 2 + p ^ 2) * ((x0 ^ 2 + p0 ^ 2) * (x ^ 2 + p ^ 2)) :=
    mul_le_mul ha1 hb2 (sq_nonneg _) hρ
  have t3 : (x0 * p + p0 * x) ^ 4 ≤ ((x0 ^ 2 + p0 ^ 2) * (x ^ 2 + p ^ 2)) ^ 2 := by
    calc (x0 * p + p0 * x) ^ 4 = ((x0 * p + p0 * x) ^ 2) ^ 2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) hb2 2
  calc M * (2 * (x * p) ^ 2 + |x * p| * (x0 * p + p0 * x) ^ 2 + 2 * (x0 * p + p0 * x) ^ 4)
      ≤ M * (2 * (x ^ 2 + p ^ 2) ^ 2 + (x ^ 2 + p ^ 2) * ((x0 ^ 2 + p0 ^ 2) * (x ^ 2 + p ^ 2))
          + 2 * ((x0 ^ 2 + p0 ^ 2) * (x ^ 2 + p ^ 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hM
    _ = M * (2 + (x0 ^ 2 + p0 ^ 2) + 2 * (x0 ^ 2 + p0 ^ 2) ^ 2) * (x ^ 2 + p ^ 2) ^ 2 := by ring

/-- **Proposition 4.2, equation (4.2)** in asymptotic notation: the difference between
`I = 2 f(ν) − f(ν₊) − f(ν₋)` and the leading terms is `O(‖(x, p)‖⁴)` as `(x, p) → 0`. -/
theorem two_mode_expansion_isBigO (x0 p0 : ℝ) (hν : 1 / 2 < √(x0 * p0)) :
    (fun z : ℝ × ℝ => twoModeMI x0 p0 z.1 z.2 - twoModeMILeading x0 p0 z.1 z.2)
      =O[𝓝 0] fun z : ℝ × ℝ => ‖z‖ ^ 4 := by
  obtain ⟨C, δ, hC, hδ, h⟩ := two_mode_expansion x0 p0 hν
  refine Asymptotics.IsBigO.of_bound (4 * C) ?_
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ × ℝ) hδ] with z hz
  have hz' : ‖z‖ ≤ δ := mem_closedBall_zero_iff.mp hz
  have h1 : |z.1| ≤ ‖z‖ := norm_fst_le z
  have h2 : |z.2| ≤ ‖z‖ := norm_snd_le z
  have hb := h z.1 z.2 (h1.trans hz') (h2.trans hz')
  have q1 : z.1 ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have q2 : z.2 ^ 2 ≤ ‖z‖ ^ 2 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
  have hsum : z.1 ^ 2 + z.2 ^ 2 ≤ 2 * ‖z‖ ^ 2 := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 4)]
  calc |twoModeMI x0 p0 z.1 z.2 - twoModeMILeading x0 p0 z.1 z.2|
      ≤ C * (z.1 ^ 2 + z.2 ^ 2) ^ 2 := hb
    _ ≤ C * (2 * ‖z‖ ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum 2) hC
    _ = 4 * C * ‖z‖ ^ 4 := by ring

end CorrelationsGeometry
