/-
Fortieth file (Mathlib only): the algebraic core of the density response of the kernel graph, finite form.
Namespace `CTG.DensityResponse`; check with `./check_density_response.sh`.
Finite index set, weights `n_i > 0`, matrix `K ≥ 0`, `q_i = Σ_j K_ij n_j > 0`, `W = K/(q⊗q)`, `D_i = Σ_j W_ij n_j`,
`P = D⁻¹ W n` (row stochastic), `S = √n W √n / √(D⊗D)`.
(1) Exact: `Sn_eq_conj` (`S = diag(A) K diag(A)`, `A_i = √n_i/(q_i √D_i)`), `Sn_symm`, `Sn_similar`,
`Sn_pow_diag` (`(S^k)_ii = (P^k)_ii`), `Sn_pow_trace`.
(2) First order in `ε` for `n_i(ε) = n⁰_i exp(ε φ_i)` on a homogeneous background (HYPOTHESIS: constant row sums
`Σ_j K_ij n⁰_j = q₀ > 0`), with `𝒢 = K diag(n⁰)/q₀`: `hasDerivAt_log_q` (`𝒢φ`), `hasDerivAt_log_D` (`−𝒢²φ`),
`hasDerivAt_log_A'` (`½ (1−𝒢)² φ`), `hasDerivAt_log_A_eigen` (`½ (1−γ)² φ_i` if `𝒢φ = γφ`).
(3) `hasDerivAt_S`, `hasDerivAt_S_pow`, `hasDerivAt_trace_P_pow`
(`d/dε Tr P^{k+1} = (k+1) Σ_i ((1−𝒢)²φ)_i (P₀^{k+1})_ii`).
Neither `K` nor `𝒢` needs to be symmetric for (2), (3).  NOT formalised: the continuum version (integral
operators, Gaussian kernel, `𝒢` a convolution), remainders `O(φ²)`, the summation with `1 − √(1−s)`, the
coefficient `c(a)` and its limit.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 26/27 November 2026.
-/
import Mathlib

set_option linter.unusedSectionVars false

open Matrix Finset

namespace CTG.DensityResponse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `q_i = Σ_j K_ij n_j`. -/
noncomputable def qn (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) : ℝ := ∑ j, K i j * n j
/-- `W_ij = K_ij/(q_i q_j)`. -/
noncomputable def Wn (K : Matrix ι ι ℝ) (n : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => K i j / (qn K n i * qn K n j)
/-- `D_i = Σ_j W_ij n_j`. -/
noncomputable def Dn (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) : ℝ := ∑ j, Wn K n i j * n j
/-- The walk `P_ij = W_ij n_j / D_i`. -/
noncomputable def Pn (K : Matrix ι ι ℝ) (n : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => Wn K n i j * n j / Dn K n i
/-- The symmetrised walk `S_ij = √n_i W_ij √n_j / √(D_i D_j)`. -/
noncomputable def Sn (K : Matrix ι ι ℝ) (n : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => Real.sqrt (n i) * Wn K n i j * Real.sqrt (n j) / Real.sqrt (Dn K n i * Dn K n j)
/-- The multiplier `A_i = √n_i/(q_i √D_i)`. -/
noncomputable def An (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) : ℝ :=
  Real.sqrt (n i) / (qn K n i * Real.sqrt (Dn K n i))
/-- The similarity weight `r_i = √(n_i D_i)`. -/
noncomputable def rn (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) : ℝ := Real.sqrt (n i * Dn K n i)

/-- `D_i = (Σ_j K_ij n_j / q_j)/q_i`. -/
lemma Dn_eq (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) :
    Dn K n i = (∑ j, K i j * n j / qn K n j) / qn K n i := by
  unfold Dn Wn
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hi : qn K n i = 0
  · simp [hi]
  by_cases hj : qn K n j = 0
  · simp [hj]
  field_simp

/-- Positivity of `D` from `K ≥ 0`, `n > 0`, `q > 0`. -/
lemma Dn_pos (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) (i : ι) : 0 < Dn K n i := by
  rw [Dn_eq]
  refine div_pos ?_ (hq i)
  have hex : ∃ j, 0 < K i j * n j := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : qn K n i ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith [hq i]
  obtain ⟨j, hj⟩ := hex
  exact Finset.sum_pos' (fun l _ => div_nonneg (mul_nonneg (hK i l) (hn l).le) (hq l).le)
    ⟨j, Finset.mem_univ _, div_pos hj (hq j)⟩

/-- **Claim 1, discrete form (exact).** `S = diag(A) K diag(A)`. -/
theorem Sn_eq_conj (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) :
    Sn K n = diagonal (An K n) * K * diagonal (An K n) := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  have hDi := Dn_pos K n hK hn hq i
  have hDj := Dn_pos K n hK hn hq j
  have hqi := (hq i).ne'
  have hqj := (hq j).ne'
  have si : 0 < Real.sqrt (Dn K n i) := Real.sqrt_pos.mpr hDi
  have sj : 0 < Real.sqrt (Dn K n j) := Real.sqrt_pos.mpr hDj
  unfold Sn An Wn
  rw [Real.sqrt_mul hDi.le]
  field_simp

/-- `P` is row stochastic. -/
theorem Pn_row_sum (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) (i : ι) : ∑ j, Pn K n i j = 1 := by
  unfold Pn
  rw [← Finset.sum_div]
  exact div_self (Dn_pos K n hK hn hq i).ne'

/-- `S` is symmetric when `K` is. -/
theorem Sn_symm (K : Matrix ι ι ℝ) (n : ι → ℝ) (hKs : Kᵀ = K) : (Sn K n)ᵀ = Sn K n := by
  ext i j
  have : K j i = K i j := by rw [← transpose_apply K i j, hKs]
  simp only [transpose_apply, Sn, Wn, this]
  rw [mul_comm (Dn K n j), mul_comm (qn K n j)]
  ring

/-- Similarity: `S = diag(r) P diag(r)⁻¹`, `r_i = √(n_i D_i)`. -/
theorem Sn_similar (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) :
    Sn K n = diagonal (rn K n) * Pn K n * diagonal (fun i => (rn K n i)⁻¹) := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  have hDi := Dn_pos K n hK hn hq i
  have hDj := Dn_pos K n hK hn hq j
  have si : 0 < Real.sqrt (Dn K n i) := Real.sqrt_pos.mpr hDi
  have sj : 0 < Real.sqrt (Dn K n j) := Real.sqrt_pos.mpr hDj
  have ni : 0 < Real.sqrt (n i) := Real.sqrt_pos.mpr (hn i)
  have nj : 0 < Real.sqrt (n j) := Real.sqrt_pos.mpr (hn j)
  have hnj : Real.sqrt (n j) * Real.sqrt (n j) = n j := Real.mul_self_sqrt (hn j).le
  unfold Sn Pn rn
  rw [Real.sqrt_mul hDi.le, Real.sqrt_mul (hn i).le, Real.sqrt_mul (hn j).le]
  have hDi' : Real.sqrt (Dn K n i) * Real.sqrt (Dn K n i) = Dn K n i := Real.mul_self_sqrt hDi.le
  field_simp
  simp only [Real.sq_sqrt (hn j).le, Real.sq_sqrt hDi.le]
  ring

/-- Powers of a conjugated matrix. -/
lemma conj_pow (d e M : Matrix ι ι ℝ) (h : e * d = 1) (k : ℕ) :
    (d * M * e) ^ k = d * M ^ k * e ∨ k = 0 := by
  induction k with
  | zero => exact Or.inr rfl
  | succ k ih =>
    left
    rcases ih with ih | ih
    · rw [pow_succ, ih]
      calc d * M ^ k * e * (d * M * e) = d * M ^ k * (e * d) * M * e := by
            simp only [Matrix.mul_assoc]
        _ = d * M ^ (k + 1) * e := by rw [h, Matrix.mul_one, pow_succ]; simp only [Matrix.mul_assoc]
    · subst ih
      simp

/-- **Same return probabilities**: `(S^k)_ii = (P^k)_ii` for every `k`. -/
theorem Sn_pow_diag (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) (k : ℕ) (i : ι) :
    (Sn K n ^ k) i i = (Pn K n ^ k) i i := by
  have hr : ∀ i, rn K n i ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (mul_pos (hn i) (Dn_pos K n hK hn hq i))).ne'
  have he : diagonal (fun i => (rn K n i)⁻¹) * diagonal (rn K n) = 1 := by
    rw [diagonal_mul_diagonal]
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hr a]
    · simp [hab]
  rw [Sn_similar K n hK hn hq]
  rcases conj_pow _ _ (Pn K n) he k with h | h
  · rw [h, mul_diagonal, diagonal_mul]
    field_simp [hr i]
  · subst h; simp

/-- `Tr S^k = Tr P^k`. -/
theorem Sn_pow_trace (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) (k : ℕ) :
    trace (Sn K n ^ k) = trace (Pn K n ^ k) := by
  unfold trace
  exact Finset.sum_congr rfl fun i _ => Sn_pow_diag K n hK hn hq k i


/-- The perturbed density `n_i(ε) = n⁰_i exp(ε φ_i)`. -/
noncomputable def nε (n0 φ : ι → ℝ) (ε : ℝ) (i : ι) : ℝ := n0 i * Real.exp (ε * φ i)

/-- The smoothing operator `𝒢 = K diag(n⁰)/q₀`. -/
noncomputable def Gm (K : Matrix ι ι ℝ) (n0 : ι → ℝ) (q0 : ℝ) : Matrix ι ι ℝ :=
  fun i j => K i j * n0 j / q0

/-- `R_i = Σ_j K_ij n_j/q_j`, so that `D_i = R_i/q_i`. -/
noncomputable def Rn (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) : ℝ := ∑ j, K i j * n j / qn K n j

lemma nε_zero (n0 φ : ι → ℝ) : nε n0 φ 0 = n0 := by
  funext i; simp [nε]

lemma nε_pos (n0 φ : ι → ℝ) (hn0 : ∀ i, 0 < n0 i) (ε : ℝ) (i : ι) : 0 < nε n0 φ ε i :=
  mul_pos (hn0 i) (Real.exp_pos _)

lemma hasDerivAt_nε (n0 φ : ι → ℝ) (j : ι) :
    HasDerivAt (fun ε => nε n0 φ ε j) (n0 j * φ j) 0 := by
  have h := (((hasDerivAt_id (0:ℝ)).mul_const (φ j)).exp).const_mul (n0 j)
  convert h using 1
  simp

lemma log_nε (n0 φ : ι → ℝ) (hn0 : ∀ i, 0 < n0 i) (ε : ℝ) (i : ι) : Real.log (nε n0 φ ε i) = Real.log (n0 i) + ε * φ i := by
  unfold nε
  rw [Real.log_mul (hn0 i).ne' (Real.exp_pos _).ne', Real.log_exp]

section Homogeneous

variable (K : Matrix ι ι ℝ) (n0 φ : ι → ℝ) (q0 : ℝ)
  (hK : ∀ i j, 0 ≤ K i j) (hn0 : ∀ i, 0 < n0 i)
  -- HYPOTHESIS (homogeneous background): all row sums `Σ_j K_ij n⁰_j` equal `q₀ > 0`.
  (hq0 : ∀ i, qn K n0 i = q0) (hq0pos : 0 < q0)
include hK hn0 hq0 hq0pos

lemma qε_pos (ε : ℝ) (i : ι) : 0 < qn K (nε n0 φ ε) i := by
  have hex : ∃ j, 0 < K i j * n0 j := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : qn K n0 i ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith [hq0 i]
  obtain ⟨j, hj⟩ := hex
  refine Finset.sum_pos' (fun l _ => mul_nonneg (hK i l) (nε_pos n0 φ hn0 ε l).le)
    ⟨j, Finset.mem_univ _, ?_⟩
  have : K i j * nε n0 φ ε j = K i j * n0 j * Real.exp (ε * φ j) := by unfold nε; ring
  rw [this]; exact mul_pos hj (Real.exp_pos _)

lemma hasDerivAt_q (i : ι) :
    HasDerivAt (fun ε => qn K (nε n0 φ ε) i) (q0 * (Gm K n0 q0 *ᵥ φ) i) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hasDerivAt_nε n0 φ j).const_mul (K i j))
  convert h using 1
  simp only [mulVec, dotProduct, Gm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- `d/dε log q_i = (𝒢φ)_i` at `ε = 0`. -/
theorem hasDerivAt_log_q (i : ι) :
    HasDerivAt (fun ε => Real.log (qn K (nε n0 φ ε) i)) ((Gm K n0 q0 *ᵥ φ) i) 0 := by
  have h0 : qn K (nε n0 φ 0) i = q0 := by rw [nε_zero]; exact hq0 i
  have h := (hasDerivAt_q K n0 φ q0 hK hn0 hq0 hq0pos i).log (by rw [h0]; exact hq0pos.ne')
  convert h using 1
  rw [h0]; field_simp

lemma hasDerivAt_R (i : ι) :
    HasDerivAt (fun ε => Rn K (nε n0 φ ε) i)
      ((Gm K n0 q0 *ᵥ (φ - Gm K n0 q0 *ᵥ φ)) i) 0 := by
  have hterm : ∀ j ∈ (Finset.univ : Finset ι), HasDerivAt
      (fun ε => K i j * nε n0 φ ε j / qn K (nε n0 φ ε) j)
      (K i j * (n0 j * φ j) / q0 - K i j * n0 j * (q0 * (Gm K n0 q0 *ᵥ φ) j) / q0 ^ 2) 0 := by
    intro j _
    have h0 : qn K (nε n0 φ 0) j = q0 := by rw [nε_zero]; exact hq0 j
    have h := ((hasDerivAt_nε n0 φ j).const_mul (K i j)).div
      (hasDerivAt_q K n0 φ q0 hK hn0 hq0 hq0pos j) (by rw [h0]; exact hq0pos.ne')
    convert h using 1
    rw [h0, nε_zero]
    field_simp
  have h := HasDerivAt.fun_sum hterm
  convert h using 1
  simp only [mulVec, dotProduct, Gm, Pi.sub_apply, Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp

lemma Rn_zero (i : ι) : Rn K (nε n0 φ 0) i = 1 := by
  rw [nε_zero]
  unfold Rn
  simp only [hq0]
  rw [← Finset.sum_div]
  have h := hq0 i
  unfold qn at h
  rw [h]
  exact div_self hq0pos.ne'

/-- `d/dε log D_i = -(𝒢²φ)_i` at `ε = 0`. No symmetry of `K` or of `𝒢` is used. -/
theorem hasDerivAt_log_D (i : ι) :
    HasDerivAt (fun ε => Real.log (Dn K (nε n0 φ ε) i))
      (-(Gm K n0 q0 *ᵥ (Gm K n0 q0 *ᵥ φ)) i) 0 := by
  have hqpos := qε_pos K n0 φ q0 hK hn0 hq0 hq0pos
  have heq : (fun ε => Real.log (Dn K (nε n0 φ ε) i)) =
      fun ε => Real.log (Rn K (nε n0 φ ε) i) - Real.log (qn K (nε n0 φ ε) i) := by
    funext ε
    have hD := Dn_pos K (nε n0 φ ε) hK (nε_pos n0 φ hn0 ε) (hqpos ε) i
    have hDe := Dn_eq K (nε n0 φ ε) i
    have hR : Rn K (nε n0 φ ε) i = Dn K (nε n0 φ ε) i * qn K (nε n0 φ ε) i := by
      rw [hDe]; unfold Rn; field_simp [(hqpos ε i).ne']
    rw [hR, Real.log_mul hD.ne' (hqpos ε i).ne']
    ring
  rw [heq]
  have hR := (hasDerivAt_R K n0 φ q0 hK hn0 hq0 hq0pos i).log
    (by rw [Rn_zero K n0 φ q0 hK hn0 hq0 hq0pos]; exact one_ne_zero)
  have h := hR.sub (hasDerivAt_log_q K n0 φ q0 hK hn0 hq0 hq0pos i)
  convert h using 1
  rw [Rn_zero K n0 φ q0 hK hn0 hq0 hq0pos, Matrix.mulVec_sub]
  simp

/-- **Claim 2, discrete form.** `d/dε log A_i = ½φ_i − (𝒢φ)_i + ½(𝒢²φ)_i` at `ε = 0`. -/
theorem hasDerivAt_log_A (i : ι) :
    HasDerivAt (fun ε => Real.log (An K (nε n0 φ ε) i))
      (φ i / 2 - (Gm K n0 q0 *ᵥ φ) i + (Gm K n0 q0 *ᵥ (Gm K n0 q0 *ᵥ φ)) i / 2) 0 := by
  have hqpos := qε_pos K n0 φ q0 hK hn0 hq0 hq0pos
  have heq : (fun ε => Real.log (An K (nε n0 φ ε) i)) = fun ε =>
      (Real.log (n0 i) + ε * φ i) / 2 - Real.log (qn K (nε n0 φ ε) i)
        - Real.log (Dn K (nε n0 φ ε) i) / 2 := by
    funext ε
    have hD := Dn_pos K (nε n0 φ ε) hK (nε_pos n0 φ hn0 ε) (hqpos ε) i
    have hn := nε_pos n0 φ hn0 ε i
    unfold An
    rw [Real.log_div (Real.sqrt_pos.mpr hn).ne'
      (mul_pos (hqpos ε i) (Real.sqrt_pos.mpr hD)).ne',
      Real.log_mul (hqpos ε i).ne' (Real.sqrt_pos.mpr hD).ne',
      Real.log_sqrt hn.le, Real.log_sqrt hD.le, log_nε n0 φ hn0]
    ring
  rw [heq]
  have hlin : HasDerivAt (fun ε : ℝ => (Real.log (n0 i) + ε * φ i) / 2) (φ i / 2) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).mul_const (φ i)).const_add (Real.log (n0 i))).div_const 2
    convert this using 1; simp
  have h := (hlin.sub (hasDerivAt_log_q K n0 φ q0 hK hn0 hq0 hq0pos i)).sub
    ((hasDerivAt_log_D K n0 φ q0 hK hn0 hq0 hq0pos i).div_const 2)
  convert h using 1
  ring

/-- The same derivative written as `½((1 − 𝒢)²φ)_i`. -/
theorem hasDerivAt_log_A' (i : ι) :
    HasDerivAt (fun ε => Real.log (An K (nε n0 φ ε) i))
      ((((1 - Gm K n0 q0) * (1 - Gm K n0 q0)) *ᵥ φ) i / 2) 0 := by
  convert hasDerivAt_log_A K n0 φ q0 hK hn0 hq0 hq0pos i using 1
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_sub]
  simp only [Pi.sub_apply]
  ring

/-- Eigenvector case: if `𝒢φ = γφ`, the derivative is `½(1−γ)²φ_i`. -/
theorem hasDerivAt_log_A_eigen (γ : ℝ) (hφ : Gm K n0 q0 *ᵥ φ = γ • φ) (i : ι) :
    HasDerivAt (fun ε => Real.log (An K (nε n0 φ ε) i)) ((1 - γ) ^ 2 / 2 * φ i) 0 := by
  convert hasDerivAt_log_A K n0 φ q0 hK hn0 hq0 hq0pos i using 1
  rw [hφ, Matrix.mulVec_smul, hφ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end Homogeneous


/-- First-order term of `M(ε)^k` from `M(0) = M0`, `M'(0) = M1`:
`d₀ = 0`, `d_{k+1} = d_k M0 + M0^k M1`. -/
noncomputable def dpow (M0 M1 : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 0
  | k + 1 => dpow M0 M1 k * M0 + M0 ^ k * M1

/-- Entrywise product rule for matrix powers. -/
theorem hasDerivAt_pow_entry (M : ℝ → Matrix ι ι ℝ) (M1 : Matrix ι ι ℝ)
    (hM : ∀ i j, HasDerivAt (fun ε => M ε i j) (M1 i j) 0) (k : ℕ) (i j : ι) :
    HasDerivAt (fun ε => (M ε ^ k) i j) (dpow (M 0) M1 k i j) 0 := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, dpow]
    exact (hasDerivAt_const (0:ℝ) ((1 : Matrix ι ι ℝ) i j)).congr_deriv (by simp)
  | succ k ih =>
    simp only [pow_succ, mul_apply, dpow, add_apply]
    have h := HasDerivAt.fun_sum (u := Finset.univ)
      (fun l _ => (ih i l).mul (hM l j))
    convert h using 1
    rw [← Finset.sum_add_distrib]

/-- Trace of the first-order term: `Tr(d_{k+1} M0^j) = (k+1) Tr(M0^{k+j} M1)`. -/
lemma trace_dpow_mul (M0 M1 : Matrix ι ι ℝ) (k : ℕ) :
    ∀ j : ℕ, trace (dpow M0 M1 (k + 1) * M0 ^ j) = (k + 1) * trace (M0 ^ (k + j) * M1) := by
  induction k with
  | zero =>
    intro j
    simp only [dpow, Matrix.zero_mul, zero_add, pow_zero, Matrix.one_mul]
    rw [trace_mul_comm]; simp
  | succ k ih =>
    intro j
    have e1 : dpow M0 M1 (k + 1 + 1) * M0 ^ j =
        dpow M0 M1 (k + 1) * M0 ^ (j + 1) + M0 ^ (k + 1) * M1 * M0 ^ j := by
      simp only [dpow, Matrix.add_mul, Matrix.mul_assoc, pow_succ']
    rw [e1, trace_add, ih (j + 1)]
    have e2 : trace (M0 ^ (k + 1) * M1 * M0 ^ j) = trace (M0 ^ (k + 1 + j) * M1) := by
      rw [trace_mul_comm, ← Matrix.mul_assoc, ← pow_add]
      ring_nf
    rw [e2]
    push_cast
    ring_nf

/-- If `M1 = diag(a) M0 + M0 diag(a)`, then `Tr d_{k+1} = 2 (k+1) Σ_i a_i (M0^{k+1})_ii`. -/
theorem trace_dpow_diag (M0 : Matrix ι ι ℝ) (a : ι → ℝ) (k : ℕ) :
    trace (dpow M0 (diagonal a * M0 + M0 * diagonal a) (k + 1)) =
      2 * (k + 1) * ∑ i, a i * (M0 ^ (k + 1)) i i := by
  have h := trace_dpow_mul M0 (diagonal a * M0 + M0 * diagonal a) k 0
  rw [pow_zero, Matrix.mul_one, add_zero] at h
  rw [h, Matrix.mul_add, trace_add]
  have e1 : trace (M0 ^ k * (diagonal a * M0)) = trace (M0 ^ (k + 1) * diagonal a) := by
    rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← pow_succ']
  have e2 : trace (M0 ^ k * (M0 * diagonal a)) = trace (M0 ^ (k + 1) * diagonal a) := by
    rw [← Matrix.mul_assoc, ← pow_succ]
  have hT : trace (M0 ^ (k + 1) * diagonal a) = ∑ i, a i * (M0 ^ (k + 1)) i i := by
    simp only [trace, diag_apply, mul_diagonal]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1, e2, hT]
  ring

section Homogeneous

variable (K : Matrix ι ι ℝ) (n0 φ : ι → ℝ) (q0 : ℝ)
  (hK : ∀ i j, 0 ≤ K i j) (hn0 : ∀ i, 0 < n0 i)
  -- HYPOTHESIS (homogeneous background): all row sums `Σ_j K_ij n⁰_j` equal `q₀ > 0`.
  (hq0 : ∀ i, qn K n0 i = q0) (hq0pos : 0 < q0)
include hK hn0 hq0 hq0pos

/-- The logarithmic derivative `a_i = ½((1−𝒢)²φ)_i` of `A`. -/
noncomputable def aφ (i : ι) : ℝ :=
  φ i / 2 - (Gm K n0 q0 *ᵥ φ) i + (Gm K n0 q0 *ᵥ (Gm K n0 q0 *ᵥ φ)) i / 2

lemma hasDerivAt_A (i : ι) :
    HasDerivAt (fun ε => An K (nε n0 φ ε) i) (An K (nε n0 φ 0) i * aφ K n0 φ q0 i) 0 := by
  have hqpos := qε_pos K n0 φ q0 hK hn0 hq0 hq0pos
  have hpos : ∀ ε, 0 < An K (nε n0 φ ε) i := fun ε =>
    div_pos (Real.sqrt_pos.mpr (nε_pos n0 φ hn0 ε i))
      (mul_pos (hqpos ε i) (Real.sqrt_pos.mpr (Dn_pos K _ hK (nε_pos n0 φ hn0 ε) (hqpos ε) i)))
  have heq : (fun ε => An K (nε n0 φ ε) i) =
      fun ε => Real.exp (Real.log (An K (nε n0 φ ε) i)) := by
    funext ε; rw [Real.exp_log (hpos ε)]
  rw [heq]
  have h := (hasDerivAt_log_A K n0 φ q0 hK hn0 hq0 hq0pos i).exp
  convert h using 1
  rw [Real.exp_log (hpos 0)]; rfl

/-- First-order variation of `S`: `S'(0) = diag(a) S₀ + S₀ diag(a)` entrywise. -/
theorem hasDerivAt_S (i j : ι) :
    HasDerivAt (fun ε => Sn K (nε n0 φ ε) i j)
      ((diagonal (aφ K n0 φ q0) * Sn K (nε n0 φ 0) +
        Sn K (nε n0 φ 0) * diagonal (aφ K n0 φ q0)) i j) 0 := by
  have hqpos := qε_pos K n0 φ q0 hK hn0 hq0 hq0pos
  have heq : (fun ε => Sn K (nε n0 φ ε) i j) =
      fun ε => An K (nε n0 φ ε) i * K i j * An K (nε n0 φ ε) j := by
    funext ε
    rw [Sn_eq_conj K _ hK (nε_pos n0 φ hn0 ε) (hqpos ε), mul_diagonal, diagonal_mul]
  rw [heq]
  have h := ((hasDerivAt_A K n0 φ q0 hK hn0 hq0 hq0pos i).mul_const (K i j)).mul
    (hasDerivAt_A K n0 φ q0 hK hn0 hq0 hq0pos j)
  convert h using 1
  rw [Sn_eq_conj K _ hK (nε_pos n0 φ hn0 0) (hqpos 0)]
  simp only [add_apply, diagonal_mul, mul_diagonal]
  ring

/-- **Claim 3 (first order, return probabilities).** For every `k`, every entry of `S^k`
(in particular the diagonal `(S^k)_ii = (P^k)_ii`) is differentiable in `ε` at `0`, with
derivative the `(i,j)` entry of `dpow S₀ S₁ k`, `S₁ = diag(a) S₀ + S₀ diag(a)`, `a = ½(1−𝒢)²φ`. -/
theorem hasDerivAt_S_pow (k : ℕ) (i j : ι) :
    HasDerivAt (fun ε => (Sn K (nε n0 φ ε) ^ k) i j)
      (dpow (Sn K (nε n0 φ 0)) (diagonal (aφ K n0 φ q0) * Sn K (nε n0 φ 0) +
        Sn K (nε n0 φ 0) * diagonal (aφ K n0 φ q0)) k i j) 0 :=
  hasDerivAt_pow_entry (fun ε => Sn K (nε n0 φ ε)) _
    (hasDerivAt_S K n0 φ q0 hK hn0 hq0 hq0pos) k i j

/-- **Trace at first order.** `d/dε Tr P(ε)^{k+1} = (k+1) Σ_i ((1−𝒢)²φ)_i (P₀^{k+1})_ii`. -/
theorem hasDerivAt_trace_P_pow (k : ℕ) :
    HasDerivAt (fun ε => trace (Pn K (nε n0 φ ε) ^ (k + 1)))
      ((k + 1) * ∑ i, (2 * aφ K n0 φ q0 i) * (Pn K n0 ^ (k + 1)) i i) 0 := by
  have hqpos := qε_pos K n0 φ q0 hK hn0 hq0 hq0pos
  have heq : (fun ε => trace (Pn K (nε n0 φ ε) ^ (k + 1))) =
      fun ε => ∑ i, (Sn K (nε n0 φ ε) ^ (k + 1)) i i := by
    funext ε
    rw [← Sn_pow_trace K _ hK (nε_pos n0 φ hn0 ε) (hqpos ε)]; rfl
  rw [heq]
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => hasDerivAt_S_pow K n0 φ q0 hK hn0 hq0 hq0pos (k + 1) i i)
  convert h using 1
  have ht := trace_dpow_diag (Sn K (nε n0 φ 0)) (aφ K n0 φ q0) k
  simp only [trace, diag_apply] at ht
  rw [ht, nε_zero]
  simp only [Sn_pow_diag K n0 hK hn0 (fun i => hq0 i ▸ hq0pos)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end Homogeneous

end CTG.DensityResponse
