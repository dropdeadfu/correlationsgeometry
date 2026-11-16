import Mathlib

/-!
# The Poisson representation of the graph heat trace (Theorem 3.11 of the paper)

Paper: M. Neuberger, *From Correlations to Geometry* (November 2026).

For a symmetric matrix `W` with non-negative entries and positive row sums `Dᵢ = Σⱼ Wᵢⱼ`, put
`P = D⁻¹ W`, `S = D^{-1/2} W D^{-1/2}` and `L = c (1 − S)` (in the paper `c = 2/(c_h ξ²)`), and
`τ = t c`. Theorem 3.11 states

  `Tr e^{-tL} = e^{-τ} Σ_k τ^k/k! · Tr P^k`,  `Tr P^k ≥ 0`,  `N e^{-τ} ≤ Tr e^{-tL} ≤ N`.

All four statements are proven here: `theorem_3_11`.
-/

open Matrix NormedSpace

namespace CorrelationsGeometry

/-!
No norm is chosen on matrices in this file: every statement uses only the entrywise topology of
`Matrix n n ℝ`, as Mathlib's own matrix-exponential lemmas do. A norm is opened locally in the one
proof that needs the convergence of the exponential series.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Trace of a matrix exponential -/

/-- The trace of `exp A` is the sum of the traces of the terms of the exponential series. -/
theorem hasSum_trace_exp (A : Matrix n n ℝ) :
    HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ * (A ^ k).trace) (exp A).trace := by
  have h : HasSum (fun k : ℕ => ((k.factorial : ℝ))⁻¹ • A ^ k) (exp A) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A
  have h2 : HasSum (fun k : ℕ => Matrix.trace (((k.factorial : ℝ))⁻¹ • A ^ k)) (exp A).trace :=
    h.map (Matrix.traceAddMonoidHom n ℝ) (continuous_id.matrix_trace)
  simpa only [Matrix.trace_smul, smul_eq_mul] using h2

/-- `exp (τ (P − 1)) = e^{-τ} exp (τ P)`. -/
theorem exp_smul_sub_one (P : Matrix n n ℝ) (τ : ℝ) :
    exp (τ • (P - 1)) = Real.exp (-τ) • exp (τ • P) := by
  have hsplit : τ • (P - 1) = (-τ) • (1 : Matrix n n ℝ) + τ • P := by
    rw [smul_sub, neg_smul]; abel
  have hcomm : Commute ((-τ) • (1 : Matrix n n ℝ)) (τ • P) :=
    ((Commute.one_left P).smul_right τ).smul_left (-τ)
  have hscalar : exp ((-τ) • (1 : Matrix n n ℝ)) = Real.exp (-τ) • (1 : Matrix n n ℝ) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal, Pi.exp_def, Matrix.smul_one_eq_diagonal,
      Real.exp_eq_exp_ℝ]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, hscalar, smul_mul_assoc, one_mul]

/-- **Theorem 3.11, the series, for an arbitrary real matrix `P`.** -/
theorem poisson_trace (P : Matrix n n ℝ) (τ : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-τ) * (τ ^ k / k.factorial * (P ^ k).trace))
      (exp (τ • (P - 1))).trace := by
  rw [exp_smul_sub_one, Matrix.trace_smul, smul_eq_mul]
  have h := (hasSum_trace_exp (τ • P)).mul_left (Real.exp (-τ))
  convert h using 2
  rename_i k
  rw [smul_pow, Matrix.trace_smul, smul_eq_mul]
  ring

/-! ## The graph operators of Section 2.2 -/

variable (W : Matrix n n ℝ)

/-- The degree `Dᵢ = Σⱼ Wᵢⱼ`. -/
def deg (i : n) : ℝ := ∑ j, W i j

/-- The row-stochastic matrix `P = D⁻¹ W`. -/
noncomputable def walk : Matrix n n ℝ := diagonal (fun i => (deg W i)⁻¹) * W

/-- The symmetric matrix `S = D^{-1/2} W D^{-1/2}`. -/
noncomputable def symm : Matrix n n ℝ :=
  diagonal (fun i => (Real.sqrt (deg W i))⁻¹) * W * diagonal (fun i => (Real.sqrt (deg W i))⁻¹)

/-- The graph Laplacian `L = c (1 − S)`; in (2.6), `c = 2/(c_h ξ²)`. -/
noncomputable def laplacian (c : ℝ) : Matrix n n ℝ := c • (1 - symm W)

variable {W}

theorem symm_apply (i j : n) :
    symm W i j = (Real.sqrt (deg W i))⁻¹ * W i j * (Real.sqrt (deg W j))⁻¹ := by
  simp [symm, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem walk_apply (i j : n) : walk W i j = (deg W i)⁻¹ * W i j := by
  simp [walk, Matrix.diagonal_mul]

/-- `S = D^{1/2} P D^{-1/2}`. -/
theorem symm_eq_conj (hpos : ∀ i, 0 < deg W i) :
    symm W = diagonal (fun i => Real.sqrt (deg W i)) * walk W
      * diagonal (fun i => (Real.sqrt (deg W i))⁻¹) := by
  ext i j
  have hs : Real.sqrt (deg W i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
  have hd : (deg W i)⁻¹ = (Real.sqrt (deg W i) * Real.sqrt (deg W i))⁻¹ := by
    rw [Real.mul_self_sqrt (hpos i).le]
  have key : Real.sqrt (deg W i) * (deg W i)⁻¹ = (Real.sqrt (deg W i))⁻¹ := by
    rw [hd, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
  simp only [symm_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, walk_apply]
  rw [← key]
  ring

/-- `S^k = D^{1/2} P^k D^{-1/2}`. -/
theorem symm_pow (hpos : ∀ i, 0 < deg W i) (k : ℕ) :
    symm W ^ k = diagonal (fun i => Real.sqrt (deg W i)) * walk W ^ k
      * diagonal (fun i => (Real.sqrt (deg W i))⁻¹) := by
  have hBA : diagonal (fun i => (Real.sqrt (deg W i))⁻¹) * diagonal (fun i => Real.sqrt (deg W i))
      = (1 : Matrix n n ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos i)).ne'
  have hAB : diagonal (fun i => Real.sqrt (deg W i)) * diagonal (fun i => (Real.sqrt (deg W i))⁻¹)
      = (1 : Matrix n n ℝ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hpos i)).ne'
  induction k with
  | zero => simp [hAB]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ, symm_eq_conj hpos]
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc (diagonal fun i => (Real.sqrt (deg W i))⁻¹), hBA, Matrix.one_mul]

/-- `Tr S^k = Tr P^k`. -/
theorem trace_symm_pow (hpos : ∀ i, 0 < deg W i) (k : ℕ) :
    (symm W ^ k).trace = (walk W ^ k).trace := by
  rw [symm_pow hpos, Matrix.trace_mul_cycle, Matrix.diagonal_mul_diagonal]
  have : (diagonal fun i => (Real.sqrt (deg W i))⁻¹ * Real.sqrt (deg W i))
      = (1 : Matrix n n ℝ) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos i)).ne'
  rw [this, Matrix.one_mul]

/-- The entries of `P^k` are non-negative. -/
theorem walk_pow_nonneg (hnonneg : ∀ i j, 0 ≤ W i j) (hpos : ∀ i, 0 < deg W i) (k : ℕ) (i j : n) :
    0 ≤ (walk W ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) ?_
    rw [walk_apply]
    exact mul_nonneg (inv_nonneg.mpr (hpos l).le) (hnonneg l j)

/-- **Theorem 3.11:** `Tr P^k ≥ 0`. -/
theorem trace_walk_pow_nonneg (hnonneg : ∀ i j, 0 ≤ W i j) (hpos : ∀ i, 0 < deg W i) (k : ℕ) :
    0 ≤ (walk W ^ k).trace :=
  Finset.sum_nonneg fun i _ => walk_pow_nonneg hnonneg hpos k i i

/-- `−t L = τ (S − 1)` with `τ = t c`. -/
theorem neg_smul_laplacian (c t : ℝ) : -(t • laplacian W c) = (t * c) • (symm W - 1) := by
  rw [laplacian, smul_smul, ← smul_neg, neg_sub]

/-- **Theorem 3.11, equation (3.14):** `Tr e^{-tL} = e^{-τ} Σ_k τ^k/k! · Tr P^k`. -/
theorem hasSum_trace_exp_laplacian (hpos : ∀ i, 0 < deg W i) (c t : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-(t * c)) * ((t * c) ^ k / k.factorial * (walk W ^ k).trace))
      (exp (-(t • laplacian W c))).trace := by
  rw [neg_smul_laplacian]
  have h := poisson_trace (symm W) (t * c)
  simpa only [trace_symm_pow hpos] using h

/-- **Theorem 3.11, lower bound:** `N e^{-τ} ≤ Tr e^{-tL}` for `τ ≥ 0`. -/
theorem card_mul_exp_le_trace (hnonneg : ∀ i j, 0 ≤ W i j) (hpos : ∀ i, 0 < deg W i) (c t : ℝ)
    (hτ : 0 ≤ t * c) :
    (Fintype.card n : ℝ) * Real.exp (-(t * c)) ≤ (exp (-(t • laplacian W c))).trace := by
  have h := hasSum_trace_exp_laplacian hpos c t
  have h0 := le_hasSum h 0 (fun k _ => mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (div_nonneg (pow_nonneg hτ k) (Nat.cast_nonneg _))
      (trace_walk_pow_nonneg hnonneg hpos k)))
  simpa [Matrix.trace_one, mul_comm] using h0

/-! ## The upper bound -/

/-- For a positive semidefinite real matrix `M` and `τ ≥ 0`, `Tr e^{-τM} ≤ N`. -/
theorem trace_exp_neg_smul_le (M : Matrix n n ℝ) (hM : M.PosSemidef) (τ : ℝ) (hτ : 0 ≤ τ) :
    (exp (-(τ • M))).trace ≤ Fintype.card n := by
  set U : Matrix n n ℝ := (hM.1.eigenvectorUnitary : Matrix n n ℝ) with hU
  set ev : n → ℝ := hM.1.eigenvalues with hev
  have hstar : star U * U = 1 := Unitary.coe_star_mul_self hM.1.eigenvectorUnitary
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hstar
  have hunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr
    (Matrix.isUnit_det_of_left_inverse hstar)
  have hspec : M = U * diagonal ev * star U := by
    have h := hM.1.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, Function.comp_def] using h
  have hneg : -(τ • M) = U * diagonal (fun i => -(τ * ev i)) * U⁻¹ := by
    rw [hinv]
    conv_lhs => rw [hspec]
    have hd : diagonal (fun i => -(τ * ev i)) = -(τ • diagonal ev) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hd, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hneg, Matrix.exp_conj _ _ hunit, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det U).mp hunit), Matrix.one_mul, Matrix.exp_diagonal,
    Matrix.trace_diagonal, Pi.exp_def]
  have hle : ∀ i ∈ (Finset.univ : Finset n), NormedSpace.exp (-(τ * ev i)) ≤ (1 : ℝ) := by
    intro i _
    rw [← Real.exp_eq_exp_ℝ]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hτ (hM.eigenvalues_nonneg i)))
  calc ∑ i, NormedSpace.exp (-(τ * ev i)) ≤ ∑ _i : n, (1 : ℝ) := Finset.sum_le_sum hle
    _ = Fintype.card n := by simp

/-- `S` is symmetric when `W` is. -/
theorem symm_isSymm (hW : W.IsSymm) : (symm W).IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, symm_apply, symm_apply, hW.apply i j]
  ring

/-- `1 − S` is positive semidefinite: `xᵀ(1 − S)x = ½ Σᵢⱼ Wᵢⱼ (yᵢ − yⱼ)²` with `y = D^{-1/2} x`. -/
theorem one_sub_symm_posSemidef (hW : W.IsSymm) (hnonneg : ∀ i j, 0 ≤ W i j)
    (hpos : ∀ i, 0 < deg W i) : (1 - symm W).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_one, (symm_isSymm hW).eq]
  · intro x
    set a : n → ℝ := fun i => (Real.sqrt (deg W i))⁻¹ * x i with ha
    have hsq : ∀ i, deg W i * a i ^ 2 = x i * x i := by
      intro i
      have hs : Real.sqrt (deg W i) ≠ 0 := (Real.sqrt_pos.mpr (hpos i)).ne'
      have hd : deg W i = Real.sqrt (deg W i) * Real.sqrt (deg W i) :=
        (Real.mul_self_sqrt (hpos i).le).symm
      simp only [ha]
      nth_rewrite 1 [hd]
      field_simp
    have hT1 : ∑ i, ∑ j, W i j * a i ^ 2 = ∑ i, x i * x i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul]
      exact hsq i
    have hT2 : ∑ i, ∑ j, W i j * a j ^ 2 = ∑ i, x i * x i := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul]
      have : ∑ i, W i j = deg W j := by
        simp only [deg]
        exact Finset.sum_congr rfl fun i _ => hW.apply j i
      rw [this]
      exact hsq j
    have hT3 : ∑ i, ∑ j, W i j * (a i * a j) = x ⬝ᵥ (symm W *ᵥ x) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [symm_apply]
      simp only [ha]
      ring
    have hmain : 0 ≤ ∑ i, ∑ j, W i j * (a i - a j) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnonneg i j) (sq_nonneg _)
    have hexp : ∑ i, ∑ j, W i j * (a i - a j) ^ 2
        = (∑ i, ∑ j, W i j * a i ^ 2) + (∑ i, ∑ j, W i j * a j ^ 2)
          - 2 * ∑ i, ∑ j, W i j * (a i * a j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hexp, hT1, hT2, hT3] at hmain
    have hgoal : star x ⬝ᵥ ((1 - symm W) *ᵥ x) = (∑ i, x i * x i) - x ⬝ᵥ (symm W *ᵥ x) := by
      rw [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
      rfl
    rw [hgoal]
    linarith

/-- **Theorem 3.11, upper bound:** `Tr e^{-tL} ≤ N` for `τ = t c ≥ 0`. -/
theorem trace_exp_laplacian_le_card (hW : W.IsSymm) (hnonneg : ∀ i j, 0 ≤ W i j)
    (hpos : ∀ i, 0 < deg W i) (c t : ℝ) (hτ : 0 ≤ t * c) :
    (exp (-(t • laplacian W c))).trace ≤ Fintype.card n := by
  have h := trace_exp_neg_smul_le (1 - symm W) (one_sub_symm_posSemidef hW hnonneg hpos)
    (t * c) hτ
  rwa [laplacian, smul_smul]

/-- **Theorem 3.11 (Poisson representation), complete statement.** Let `W` be a symmetric matrix
with non-negative entries and positive row sums, `L = c (1 − S)` and `τ = t c ≥ 0`. Then

* `Tr e^{-tL} = e^{-τ} Σ_k τ^k/k! · Tr P^k` (as a convergent series),
* `Tr P^k ≥ 0` for every `k`,
* `N e^{-τ} ≤ Tr e^{-tL} ≤ N`, where `N` is the number of nodes. -/
theorem theorem_3_11 (hW : W.IsSymm) (hnonneg : ∀ i j, 0 ≤ W i j) (hpos : ∀ i, 0 < deg W i)
    (c t : ℝ) (hτ : 0 ≤ t * c) :
    HasSum (fun k : ℕ => Real.exp (-(t * c)) * ((t * c) ^ k / k.factorial * (walk W ^ k).trace))
        (exp (-(t • laplacian W c))).trace ∧
      (∀ k : ℕ, 0 ≤ (walk W ^ k).trace) ∧
      (Fintype.card n : ℝ) * Real.exp (-(t * c)) ≤ (exp (-(t • laplacian W c))).trace ∧
      (exp (-(t • laplacian W c))).trace ≤ Fintype.card n :=
  ⟨hasSum_trace_exp_laplacian hpos c t, trace_walk_pow_nonneg hnonneg hpos,
    card_mul_exp_le_trace hnonneg hpos c t hτ, trace_exp_laplacian_le_card hW hnonneg hpos c t hτ⟩

end CorrelationsGeometry
