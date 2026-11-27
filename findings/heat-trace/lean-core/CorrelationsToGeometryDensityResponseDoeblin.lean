/-
Sixtieth file: the spectral gap of the background of a kernel graph from the strict positivity of the kernel (Doeblin
argument), and with it the exchange of the derivative in the density with the sum over the powers WITHOUT a gap
hypothesis.  Namespaces `CTG.DoeblinGap` (Mathlib only in content) and `CTG.DoeblinGraph`; imports Mathlib and the
compiled module of the fifty-ninth file; check with `./check_density_response_doeblin.sh`.
`doeblin_gap`: `S` symmetric, `S v = v`, `v·v = 1`, `v > 0`, `S_ij ≥ c v_i v_j` ⇒ `c ≤ 1` and `‖S − v vᵀ‖ ≤ 1 − c`
(L2 operator norm).  `Sn_gap`: for a symmetric kernel with `K_ij ≥ kmin > 0` and positive weights, the symmetrised walk
has the gap `1 − c` with an explicit `c > 0` (not sharp).  `Sn_minor_hom`: sharper minorisation on a homogeneous
background (HYPOTHESIS: constant row sums).
`graph_deriv_sum_powers_pos`: `K` symmetric with strictly positive entries, `n⁰ > 0` ⇒ the series of the termwise
derivatives is summable and is the derivative at `0` of `ε ↦ Σ_J f_J (S_ε^J)_{ii}` (`f_J` the coefficients of
`1 − √(1−s)`); no gap hypothesis.  `graph_deriv_sum_powers_hom_pos`: the same with the derivative written with
`a = ½(1−𝒢)²φ` (HYPOTHESIS: constant row sums).
NOT formalised: kernels that are only non-negative (connected, not bipartite); explicit `δ`, `C`; the continuum (for the
Gaussian kernel on `N` points the constant `c` is exponentially small, so this route says nothing uniform in `N`);
the coefficient `c(a)` and its limit.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryDensityResponseExchangeGraph

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Matrix Finset
open scoped Matrix.Norms.L2Operator

namespace CTG.DoeblinGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- L2 operator norm from a quadratic bound on all vectors. -/
theorem l2_opNorm_le_of_sq (A : Matrix ι ι ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ x : ι → ℝ, ∑ i, (A *ᵥ x) i ^ 2 ≤ ρ ^ 2 * ∑ i, x i ^ 2) : ‖A‖ ≤ ρ := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hρ fun x => ?_
  have hx : ‖x‖ = Real.sqrt (∑ i, (WithLp.ofLp x) i ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs]
  have hy : ‖((toEuclideanLin (𝕜 := ℝ) (m := ι) (n := ι)).trans
      LinearMap.toContinuousLinearMap A) x‖ = Real.sqrt (∑ i, (A *ᵥ (WithLp.ofLp x)) i ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [Real.norm_eq_abs, sq_abs, toEuclideanLin]
  rw [hx, hy, ← Real.sqrt_sq hρ, ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (h _)

/-- **Weighted Schur test.** `T ≥ 0` entrywise, symmetric, `T v = λ v` with `v > 0`:
`‖T x‖² ≤ λ² ‖x‖²`. -/
theorem schur_weighted (T : Matrix ι ι ℝ) (v : ι → ℝ) (lam : ℝ) (hT : ∀ i j, 0 ≤ T i j)
    (hTs : Tᵀ = T) (hv : ∀ i, 0 < v i) (hTv : T *ᵥ v = lam • v) (x : ι → ℝ) :
    ∑ i, (T *ᵥ x) i ^ 2 ≤ lam ^ 2 * ∑ i, x i ^ 2 := by
  have hrow : ∀ i, ∑ j, T i j * v j = lam * v i := by
    intro i; have := congrFun hTv i; simpa [mulVec, dotProduct] using this
  have hcol : ∀ j, ∑ i, T i j * v i = lam * v j := by
    intro j
    rw [← hrow j]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : T i j = T j i := by rw [← transpose_apply T j i, hTs]
    rw [this]
  have hsq : ∀ i, (T *ᵥ x) i ^ 2 ≤ (lam * v i) * ∑ j, T i j * (x j ^ 2 / v j) := by
    intro i
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset ι)
      (r := fun j => T i j * x j) (f := fun j => T i j * v j) (g := fun j => T i j * (x j ^ 2 / v j))
      (fun j _ => mul_nonneg (hT i j) (hv j).le)
      (fun j _ => mul_nonneg (hT i j) (div_nonneg (sq_nonneg _) (hv j).le))
      (fun j _ => by
        have := (hv j).ne'
        field_simp)
    simp only [mulVec, dotProduct]
    rw [← hrow i]
    exact hcs
  calc ∑ i, (T *ᵥ x) i ^ 2 ≤ ∑ i, (lam * v i) * ∑ j, T i j * (x j ^ 2 / v j) :=
        Finset.sum_le_sum fun i _ => hsq i
    _ = lam * ∑ j, (∑ i, T i j * v i) * (x j ^ 2 / v j) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    _ = lam ^ 2 * ∑ i, x i ^ 2 := by
        simp only [hcol]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have := (hv j).ne'
        field_simp

lemma vecMulVec_mulVec' (v x : ι → ℝ) : vecMulVec v v *ᵥ x = (v ⬝ᵥ x) • v := by
  funext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Doeblin gap (Stage 1).** `S` symmetric, `S v = v`, `‖v‖ = 1`, `v > 0`, minorised by `c v vᵀ`
entrywise: then `‖S − v vᵀ‖ ≤ 1 − c` in the L2 operator norm (and `c ≤ 1`). No sign of `c` is needed. -/
theorem doeblin_gap (S : Matrix ι ι ℝ) (v : ι → ℝ) (c : ℝ) (hS : Sᵀ = S) (hSv : S *ᵥ v = v)
    (hvv : v ⬝ᵥ v = 1) (hv : ∀ i, 0 < v i) (hmin : ∀ i j, c * (v i * v j) ≤ S i j) :
    c ≤ 1 ∧ ‖S - vecMulVec v v‖ ≤ 1 - c := by
  set T := S - c • vecMulVec v v with hTdef
  have hT : ∀ i j, 0 ≤ T i j := by
    intro i j; simp only [hTdef, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    linarith [hmin i j]
  have hTs : Tᵀ = T := by
    rw [hTdef, transpose_sub, transpose_smul, hS]
    congr 2; ext i j; simp [vecMulVec_apply, mul_comm]
  have hTv : T *ᵥ v = (1 - c) • v := by
    rw [hTdef, sub_mulVec, smul_mulVec, vecMulVec_mulVec', hvv, hSv]
    funext i; simp; ring
  -- c ≤ 1
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [dotProduct, Finset.univ_eq_empty] at hvv
  obtain ⟨i0⟩ := hne
  have hc1 : c ≤ 1 := by
    have h1 : 0 ≤ (T *ᵥ v) i0 := Finset.sum_nonneg fun j _ => mul_nonneg (hT i0 j) (hv j).le
    rw [hTv] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    nlinarith [hv i0]
  refine ⟨hc1, l2_opNorm_le_of_sq _ (by linarith) fun x => ?_⟩
  set a := v ⬝ᵥ x
  set y := x - a • v
  have hEq : (S - vecMulVec v v) *ᵥ x = T *ᵥ y := by
    have hTx : T *ᵥ x = S *ᵥ x - c • ((v ⬝ᵥ x) • v) := by
      rw [hTdef, sub_mulVec, smul_mulVec, vecMulVec_mulVec']
    rw [sub_mulVec, vecMulVec_mulVec', mulVec_sub, mulVec_smul, hTv, hTx]
    funext i; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hy : ∑ i, y i ^ 2 ≤ ∑ i, x i ^ 2 := by
    have : ∑ i, y i ^ 2 = ∑ i, x i ^ 2 - a ^ 2 := by
      have hvv' : ∑ i, v i ^ 2 = 1 := by rw [← hvv]; simp [dotProduct, sq]
      have ha : ∑ i, x i * v i = a := by simp [a, dotProduct, mul_comm]
      simp only [y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have : ∀ i, (x i - a * v i) ^ 2 = x i ^ 2 - 2 * a * (x i * v i) + a ^ 2 * v i ^ 2 := fun i => by ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ha, hvv']
      ring
    rw [this]; nlinarith [sq_nonneg a]
  rw [hEq]
  calc ∑ i, (T *ᵥ y) i ^ 2 ≤ (1 - c) ^ 2 * ∑ i, y i ^ 2 := schur_weighted T v (1 - c) hT hTs hv hTv y
    _ ≤ (1 - c) ^ 2 * ∑ i, x i ^ 2 := mul_le_mul_of_nonneg_left hy (sq_nonneg _)

end CTG.DoeblinGap

/-! ## Stage 2: minorisation for the kernel graph -/

namespace CTG.DoeblinGraph

open CTG.DoeblinGap CTG.DensityExchangeGraph
open CTG.DensityResponse (qn Wn Dn Pn Sn An nε Gm aφ dpow)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma An_eq (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) (i : ι) :
    An K n i = Real.sqrt (n i * Dn K n i) / (qn K n i * Dn K n i) := by
  have hD := CTG.DensityResponse.Dn_pos K n hK hn hq i
  have sD : 0 < Real.sqrt (Dn K n i) := Real.sqrt_pos.mpr hD
  have hqi := (hq i).ne'
  unfold An
  rw [Real.sqrt_mul (hn i).le]
  have h2 : Dn K n i = Real.sqrt (Dn K n i) * Real.sqrt (Dn K n i) := (Real.mul_self_sqrt hD.le).symm
  conv_rhs => rw [h2]
  field_simp
  rw [Real.sqrt_sq sD.le]

lemma vn_mul (K : Matrix ι ι ℝ) (n : ι → ℝ) [Nonempty ι] (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) (i j : ι) :
    vn K n i * vn K n j =
      Real.sqrt (n i * Dn K n i) * Real.sqrt (n j * Dn K n j) / ∑ k, n k * Dn K n k := by
  have hs := sum_nD_pos K n hK hn hq
  unfold vn
  rw [div_mul_div_comm, Real.mul_self_sqrt hs.le]

lemma vn_pos (K : Matrix ι ι ℝ) (n : ι → ℝ) [Nonempty ι] (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) (i : ι) : 0 < vn K n i := by
  unfold vn
  exact div_pos (Real.sqrt_pos.mpr (mul_pos (hn i) (CTG.DensityResponse.Dn_pos K n hK hn hq i)))
    (Real.sqrt_pos.mpr (sum_nD_pos K n hK hn hq))

/-- The explicit minorisation constant `c = kmin · Σ_k n_k D_k / B²`. -/
noncomputable def cmin (K : Matrix ι ι ℝ) (n : ι → ℝ) (kmin B : ℝ) : ℝ :=
  kmin * (∑ k, n k * Dn K n k) / B ^ 2

/-- **Stage 2 (minorisation).** For `K ≥ kmin ≥ 0` entrywise, `n > 0`, `q > 0` and any `B` with
`q_i D_i ≤ B` for all `i`: `S_ij ≥ c v_i v_j` with `c = kmin Σ_k n_k D_k / B²`. -/
theorem Sn_minor (K : Matrix ι ι ℝ) (n : ι → ℝ) [Nonempty ι] (kmin B : ℝ) (hkmin : 0 ≤ kmin)
    (hKmin : ∀ i j, kmin ≤ K i j) (hn : ∀ i, 0 < n i) (hq : ∀ i, 0 < qn K n i)
    (hB : ∀ i, qn K n i * Dn K n i ≤ B) (i j : ι) :
    cmin K n kmin B * (vn K n i * vn K n j) ≤ Sn K n i j := by
  have hK : ∀ i j, 0 ≤ K i j := fun i j => hkmin.trans (hKmin i j)
  have hs := sum_nD_pos K n hK hn hq
  have hD := CTG.DensityResponse.Dn_pos K n hK hn hq
  have hx : ∀ l, 0 < qn K n l * Dn K n l := fun l => mul_pos (hq l) (hD l)
  have hB0 : 0 < B := (hx i).trans_le (hB i)
  set ri := Real.sqrt (n i * Dn K n i)
  set rj := Real.sqrt (n j * Dn K n j)
  have hri : 0 ≤ ri := Real.sqrt_nonneg _
  have hrj : 0 ≤ rj := Real.sqrt_nonneg _
  have hS : Sn K n i j = An K n i * K i j * An K n j := by
    rw [CTG.DensityResponse.Sn_eq_conj K n hK hn hq, mul_diagonal, diagonal_mul]
  have hAi : 0 ≤ An K n i := by rw [An_eq K n hK hn hq]; exact div_nonneg hri (hx i).le
  have hAj : 0 ≤ An K n j := by rw [An_eq K n hK hn hq]; exact div_nonneg hrj (hx j).le
  have h1 : kmin * (An K n i * An K n j) ≤ Sn K n i j := by
    rw [hS]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hKmin i j) hAj) hAi
    nlinarith [this]
  have h2 : An K n i * An K n j = ri * rj / ((qn K n i * Dn K n i) * (qn K n j * Dn K n j)) := by
    rw [An_eq K n hK hn hq, An_eq K n hK hn hq, div_mul_div_comm]
  have h3 : ri * rj / B ^ 2 ≤ ri * rj / ((qn K n i * Dn K n i) * (qn K n j * Dn K n j)) := by
    apply div_le_div_of_nonneg_left (mul_nonneg hri hrj) (mul_pos (hx i) (hx j))
    rw [sq]; exact mul_le_mul (hB i) (hB j) (hx j).le hB0.le
  have h4 : cmin K n kmin B * (vn K n i * vn K n j) = kmin * (ri * rj / B ^ 2) := by
    rw [vn_mul K n hK hn hq, cmin]
    field_simp
    rfl
  rw [h4]
  calc kmin * (ri * rj / B ^ 2) ≤ kmin * (An K n i * An K n j) := by
        rw [h2]; exact mul_le_mul_of_nonneg_left h3 hkmin
    _ ≤ Sn K n i j := h1

/-- **Stage 2 (gap).** Symmetric `K ≥ kmin > 0`, `n > 0`: the background gap holds with
`ρ₀ = 1 − c`, `c = kmin Σ_k n_k D_k / (Σ_k q_k D_k)²`, and `0 < c ≤ 1`. -/
theorem Sn_gap (K : Matrix ι ι ℝ) (n : ι → ℝ) [Nonempty ι] (kmin : ℝ) (hkmin : 0 < kmin)
    (hKmin : ∀ i j, kmin ≤ K i j) (hKs : Kᵀ = K) (hn : ∀ i, 0 < n i) :
    let c := cmin K n kmin (∑ k, qn K n k * Dn K n k)
    0 < c ∧ c ≤ 1 ∧ ‖Sn K n - vecMulVec (vn K n) (vn K n)‖ ≤ 1 - c := by
  intro c
  have hK : ∀ i j, 0 ≤ K i j := fun i j => hkmin.le.trans (hKmin i j)
  have hq : ∀ i, 0 < qn K n i := fun i =>
    Finset.sum_pos (fun j _ => mul_pos (hkmin.trans_le (hKmin i j)) (hn j)) Finset.univ_nonempty
  have hD := CTG.DensityResponse.Dn_pos K n hK hn hq
  have hx : ∀ l, 0 < qn K n l * Dn K n l := fun l => mul_pos (hq l) (hD l)
  have hB : ∀ i, qn K n i * Dn K n i ≤ ∑ k, qn K n k * Dn K n k := fun i =>
    Finset.single_le_sum (f := fun k => qn K n k * Dn K n k) (fun k _ => (hx k).le) (Finset.mem_univ i)
  have hBpos : 0 < ∑ k, qn K n k * Dn K n k :=
    Finset.sum_pos (fun k _ => hx k) Finset.univ_nonempty
  have hc : 0 < c := div_pos (mul_pos hkmin (sum_nD_pos K n hK hn hq)) (pow_pos hBpos 2)
  obtain ⟨h1, h2⟩ := doeblin_gap (Sn K n) (vn K n) c (CTG.DensityResponse.Sn_symm K n hKs)
    (vn_eig K n hK hn hq) (vn_dot K n hK hn hq) (vn_pos K n hK hn hq)
    (fun i j => Sn_minor K n kmin _ hkmin.le hKmin hn hq hB i j)
  exact ⟨hc, h1, h2⟩

/-- **Stage 2, homogeneous background.** `n⁰_i = ν`, row sums `Σ_j K_ij ν = q₀`: then `q_i D_i = 1`,
and the minorisation holds with the explicit `c = kmin · M · ν / q₀` (`M = card ι`). -/
theorem Sn_minor_hom (K : Matrix ι ι ℝ) [Nonempty ι] (ν q0 kmin : ℝ) (hν : 0 < ν) (hq0 : 0 < q0)
    (hkmin : 0 ≤ kmin) (hKmin : ∀ i j, kmin ≤ K i j)
    -- HYPOTHESIS (homogeneous background): constant row sums
    (hrow : ∀ i, qn K (fun _ => ν) i = q0) (i j : ι) :
    kmin * Fintype.card ι * ν / q0 * (vn K (fun _ => ν) i * vn K (fun _ => ν) j) ≤
      Sn K (fun _ => ν) i j := by
  have hn : ∀ i : ι, 0 < (fun _ => ν) i := fun _ => hν
  have hq : ∀ i, 0 < qn K (fun _ => ν) i := fun i => (hrow i).symm ▸ hq0
  have hDi : ∀ i, Dn K (fun _ => ν) i = 1 / q0 := by
    intro i
    rw [CTG.DensityResponse.Dn_eq]
    simp only [hrow]
    rw [← Finset.sum_div]
    have : ∑ j, K i j * ν = q0 := hrow i
    rw [this, div_self hq0.ne']
  have hB : ∀ i, qn K (fun _ => ν) i * Dn K (fun _ => ν) i ≤ 1 := by
    intro i; rw [hrow, hDi]; field_simp; rfl
  have h := Sn_minor K (fun _ => ν) kmin 1 hkmin hKmin hn hq hB i j
  have hc : cmin K (fun _ => ν) kmin 1 = kmin * Fintype.card ι * ν / q0 := by
    simp only [cmin, hDi, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rwa [hc] at h

end CTG.DoeblinGraph

/-! ## Stage 3: the exchange without the gap hypothesis -/

namespace CTG.DoeblinGraph

open CTG.SqrtSeries CTG.DensityExchangeGraph
open CTG.DensityResponse (qn Wn Dn Pn Sn An nε Gm aφ dpow)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Strictly positive entries give a uniform lower bound. -/
lemma exists_kmin [Nonempty ι] (K : Matrix ι ι ℝ) (hKpos : ∀ i j, 0 < K i j) :
    ∃ kmin, 0 < kmin ∧ ∀ i j, kmin ≤ K i j := by
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image (Finset.univ : Finset (ι × ι)) (fun p => K p.1 p.2)
    Finset.univ_nonempty
  exact ⟨K p.1 p.2, hKpos _ _, fun i j => hp (i, j) (Finset.mem_univ _)⟩

/-- **Stage 3.** Symmetric `K` with strictly positive entries, `n⁰ > 0`: without any gap hypothesis
the series `Σ_J f_J (S_ε^J)_ii` is differentiable at `0`, with the (summable) series of the termwise
derivatives as derivative. -/
theorem graph_deriv_sum_powers_pos [Nonempty ι] (K : Matrix ι ι ℝ) (n0 φ : ι → ℝ)
    (hKpos : ∀ i j, 0 < K i j) (hKs : Kᵀ = K) (hn0 : ∀ i, 0 < n0 i) (i : ι) :
    Summable (fun J => fc J * CTG.DensityExchange.dpw (Sf K n0 φ 0) (Sf' K n0 φ 0) J i i) ∧
    HasDerivAt (fun ε => ∑' J, fc J * (Sn K (nε n0 φ ε) ^ J) i i)
      (∑' J, fc J * CTG.DensityExchange.dpw (Sf K n0 φ 0) (Sf' K n0 φ 0) J i i) 0 := by
  obtain ⟨kmin, hkmin, hKmin⟩ := exists_kmin K hKpos
  have hK : ∀ i j, 0 ≤ K i j := fun i j => (hKpos i j).le
  have hq : ∀ i, 0 < qn K n0 i := fun i =>
    Finset.sum_pos (fun j _ => mul_pos (hKpos i j) (hn0 j)) Finset.univ_nonempty
  obtain ⟨hc, -, hgap⟩ := Sn_gap K n0 kmin hkmin hKmin hKs hn0
  exact graph_deriv_sum_powers K n0 φ hK hn0 hq hKs _ (by linarith) hgap i

/-- **Stage 3, homogeneous background.** As `graph_deriv_sum_powers_pos`, with the derivative written
with `a = ½(1−𝒢)²φ`; HYPOTHESIS: constant row sums `q₀ > 0`. -/
theorem graph_deriv_sum_powers_hom_pos [Nonempty ι] (K : Matrix ι ι ℝ) (n0 φ : ι → ℝ) (q0 : ℝ)
    (hKpos : ∀ i j, 0 < K i j) (hKs : Kᵀ = K) (hn0 : ∀ i, 0 < n0 i)
    -- HYPOTHESIS (homogeneous background): constant row sums `q₀ > 0`
    (hq0 : ∀ i, qn K n0 i = q0) (hq0pos : 0 < q0) (i : ι) :
    Summable (fun J => fc J * dpow (Sn K n0)
      (diagonal (aφ K n0 φ q0) * Sn K n0 + Sn K n0 * diagonal (aφ K n0 φ q0)) J i i) ∧
    HasDerivAt (fun ε => ∑' J, fc J * (Sn K (nε n0 φ ε) ^ J) i i)
      (∑' J, fc J * dpow (Sn K n0)
        (diagonal (aφ K n0 φ q0) * Sn K n0 + Sn K n0 * diagonal (aφ K n0 φ q0)) J i i) 0 := by
  obtain ⟨kmin, hkmin, hKmin⟩ := exists_kmin K hKpos
  obtain ⟨hc, -, hgap⟩ := Sn_gap K n0 kmin hkmin hKmin hKs hn0
  exact graph_deriv_sum_powers_hom K n0 φ q0 (fun i j => (hKpos i j).le) hKs hn0 hq0 hq0pos _
    (by linarith) hgap i

end CTG.DoeblinGraph

