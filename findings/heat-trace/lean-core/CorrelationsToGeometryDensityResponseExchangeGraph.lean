/-
Fifty-ninth file: the exchange of the derivative in the density with the sum over the powers for the concrete
finite kernel graph.  Namespace `CTG.DensityExchangeGraph`; imports Mathlib and the compiled modules of the
fifty-seventh and the fortieth file; check with `./check_density_response_exchange_graph.sh`.
`Sn_mulVec_rn`: `r_i = √(n_i D_i)` is an eigenvector of the symmetrised walk `Sn` for the eigenvalue 1 (no symmetry of
`K` needed); `vn_eig`, `vn_dot` for the normalised vector.  `cd_S`, `cd_v`: for the density `n⁰ e^{εφ}` every entry of
`S_ε` and of `v_ε` is continuously differentiable in `ε` on the whole line.  `gap_near_zero`: from the gap of the
background at `ε = 0` (HYPOTHESIS: `‖S_0 − v_0 v_0ᵀ‖ ≤ ρ₀ < 1` in the L2 operator norm; not derived from connectedness)
the gap `(1+ρ₀)/2` and a bound for the derivative on a ball around `0`.
`graph_deriv_sum_powers`: for `K ≥ 0` symmetric, `n⁰ > 0`, positive row sums and that background gap, the series of the
termwise derivatives is summable and is the derivative of `ε ↦ Σ_J f_J (S_ε^J)_{ii}` at `0`, with `f_J` the
coefficients of `1 − √(1−s)`.  `graph_deriv_sum_powers_hom`: on a homogeneous background (HYPOTHESIS: constant row
sums) the derivative written with `a = ½(1−𝒢)²φ`.
NOT formalised: `δ` and `C` are not explicit; the background gap from properties of the graph; the continuum (flat
torus: compact operator, gap for small perturbations) and with it the coefficient `c(a)` and its limit.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryDensityResponseExchange
import CorrelationsToGeometryDensityResponse

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Finset Metric Filter Topology CTG.SqrtSeries
open scoped Matrix.Norms.L2Operator
open CTG.DensityResponse (qn Wn Dn Pn Sn nε Gm aφ dpow)

namespace CTG.DensityExchangeGraph

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Stage 1: the top eigenvector -/

/-- The similarity weight `r_i = √(n_i D_i)`. -/
noncomputable def rv (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) : ℝ := Real.sqrt (n i * Dn K n i)

/-- The normalised top eigenvector `v = r/‖r‖`. -/
noncomputable def vn (K : Matrix ι ι ℝ) (n : ι → ℝ) (i : ι) : ℝ :=
  Real.sqrt (n i * Dn K n i) / Real.sqrt (∑ k, n k * Dn K n k)

/-- **Top eigenvector (matrix form of `Sc_top_eigen`).** `S r = r` with `r = √(n D)`. -/
theorem Sn_mulVec_rn (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) : Sn K n *ᵥ rv K n = rv K n := by
  funext i
  have hr : ∀ j, 0 < rv K n j := fun j =>
    Real.sqrt_pos.mpr (mul_pos (hn j) (CTG.DensityResponse.Dn_pos K n hK hn hq j))
  have hS := CTG.DensityResponse.Sn_similar K n hK hn hq
  have hrow := CTG.DensityResponse.Pn_row_sum K n hK hn hq i
  simp only [mulVec, dotProduct]
  have : ∀ j, Sn K n i j * rv K n j = rv K n i * Pn K n i j := by
    intro j
    rw [hS, mul_diagonal, diagonal_mul]
    simp only [CTG.DensityResponse.rn, rv]
    have hj : Real.sqrt (n j * Dn K n j) ≠ 0 := (hr j).ne'
    field_simp
  rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, hrow, mul_one]

lemma sum_nD_pos [Nonempty ι] (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) : 0 < ∑ k, n k * Dn K n k :=
  Finset.sum_pos (fun k _ => mul_pos (hn k) (CTG.DensityResponse.Dn_pos K n hK hn hq k))
    Finset.univ_nonempty

theorem vn_eig (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) : Sn K n *ᵥ vn K n = vn K n := by
  have hv : vn K n = (Real.sqrt (∑ k, n k * Dn K n k))⁻¹ • rv K n := by
    funext i; simp [vn, rv, div_eq_inv_mul]
  rw [hv, mulVec_smul, Sn_mulVec_rn K n hK hn hq]

theorem vn_dot [Nonempty ι] (K : Matrix ι ι ℝ) (n : ι → ℝ) (hK : ∀ i j, 0 ≤ K i j) (hn : ∀ i, 0 < n i)
    (hq : ∀ i, 0 < qn K n i) : vn K n ⬝ᵥ vn K n = 1 := by
  have hs := sum_nD_pos K n hK hn hq
  have hD := CTG.DensityResponse.Dn_pos K n hK hn hq
  simp only [dotProduct, vn]
  have : ∀ i, Real.sqrt (n i * Dn K n i) / Real.sqrt (∑ k, n k * Dn K n k) *
      (Real.sqrt (n i * Dn K n i) / Real.sqrt (∑ k, n k * Dn K n k)) =
      (n i * Dn K n i) / (∑ k, n k * Dn K n k) := by
    intro i
    rw [div_mul_div_comm, Real.mul_self_sqrt (mul_pos (hn i) (hD i)).le, Real.mul_self_sqrt hs.le]
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_div, div_self hs.ne']

/-! ## Stage 1: smoothness in `ε` -/

section Family

variable (K : Matrix ι ι ℝ) (n0 φ : ι → ℝ)
  (hK : ∀ i j, 0 ≤ K i j) (hn0 : ∀ i, 0 < n0 i)
  -- positive row sums of the background (no homogeneity needed here)
  (hq : ∀ i, 0 < qn K n0 i)
include hK hn0 hq

lemma qpos (ε : ℝ) (i : ι) : 0 < qn K (nε n0 φ ε) i := by
  have hex : ∃ j, 0 < K i j * n0 j := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have : qn K n0 i ≤ 0 := Finset.sum_nonpos fun j _ => h j
    linarith [hq i]
  obtain ⟨j, hj⟩ := hex
  refine Finset.sum_pos' (fun l _ => mul_nonneg (hK i l) (CTG.DensityResponse.nε_pos n0 φ hn0 ε l).le)
    ⟨j, Finset.mem_univ _, ?_⟩
  have : K i j * nε n0 φ ε j = K i j * n0 j * Real.exp (ε * φ j) := by
    unfold CTG.DensityResponse.nε; ring
  rw [this]; exact mul_pos hj (Real.exp_pos _)

lemma Dpos (ε : ℝ) (i : ι) : 0 < Dn K (nε n0 φ ε) i :=
  CTG.DensityResponse.Dn_pos K _ hK (CTG.DensityResponse.nε_pos n0 φ hn0 ε) (qpos K n0 φ hK hn0 hq ε) i

omit hK hn0 hq in
lemma cd_n (j : ι) : ContDiff ℝ 1 (fun ε => nε n0 φ ε j) := by
  unfold CTG.DensityResponse.nε
  exact contDiff_const.mul ((contDiff_id.mul contDiff_const).exp)

omit hK hn0 hq in
lemma cd_q (i : ι) : ContDiff ℝ 1 (fun ε => qn K (nε n0 φ ε) i) := by
  unfold qn
  exact ContDiff.sum fun j _ => contDiff_const.mul (cd_n n0 φ j)

lemma cd_W (i j : ι) : ContDiff ℝ 1 (fun ε => Wn K (nε n0 φ ε) i j) := by
  unfold Wn
  exact contDiff_const.div ((cd_q K n0 φ i).mul (cd_q K n0 φ j))
    fun ε => (mul_pos (qpos K n0 φ hK hn0 hq ε i) (qpos K n0 φ hK hn0 hq ε j)).ne'

lemma cd_D (i : ι) : ContDiff ℝ 1 (fun ε => Dn K (nε n0 φ ε) i) := by
  unfold Dn
  exact ContDiff.sum fun j _ => (cd_W K n0 φ hK hn0 hq i j).mul (cd_n n0 φ j)

lemma cd_S (i j : ι) : ContDiff ℝ 1 (fun ε => Sn K (nε n0 φ ε) i j) := by
  unfold Sn
  have hsn : ∀ l, ContDiff ℝ 1 (fun ε => Real.sqrt (nε n0 φ ε l)) := fun l =>
    (cd_n n0 φ l).sqrt fun ε => (CTG.DensityResponse.nε_pos n0 φ hn0 ε l).ne'
  have hd : ContDiff ℝ 1 (fun ε => Real.sqrt (Dn K (nε n0 φ ε) i * Dn K (nε n0 φ ε) j)) :=
    ((cd_D K n0 φ hK hn0 hq i).mul (cd_D K n0 φ hK hn0 hq j)).sqrt
      fun ε => (mul_pos (Dpos K n0 φ hK hn0 hq ε i) (Dpos K n0 φ hK hn0 hq ε j)).ne'
  exact (((hsn i).mul (cd_W K n0 φ hK hn0 hq i j)).mul (hsn j)).div hd fun ε =>
    (Real.sqrt_pos.mpr (mul_pos (Dpos K n0 φ hK hn0 hq ε i) (Dpos K n0 φ hK hn0 hq ε j))).ne'

lemma cd_v [Nonempty ι] (i : ι) : ContDiff ℝ 1 (fun ε => vn K (nε n0 φ ε) i) := by
  unfold vn
  have hnd : ∀ l, ContDiff ℝ 1 (fun ε => nε n0 φ ε l * Dn K (nε n0 φ ε) l) := fun l =>
    (cd_n n0 φ l).mul (cd_D K n0 φ hK hn0 hq l)
  have hs : ContDiff ℝ 1 (fun ε => ∑ k, nε n0 φ ε k * Dn K (nε n0 φ ε) k) :=
    ContDiff.sum fun k _ => hnd k
  refine ((hnd i).sqrt fun ε => ?_).div (hs.sqrt fun ε => ?_) fun ε => ?_
  · exact (mul_pos (CTG.DensityResponse.nε_pos n0 φ hn0 ε i) (Dpos K n0 φ hK hn0 hq ε i)).ne'
  · exact (sum_nD_pos K _ hK (CTG.DensityResponse.nε_pos n0 φ hn0 ε) (qpos K n0 φ hK hn0 hq ε)).ne'
  · exact (Real.sqrt_pos.mpr
      (sum_nD_pos K _ hK (CTG.DensityResponse.nε_pos n0 φ hn0 ε) (qpos K n0 φ hK hn0 hq ε))).ne'

/-- The family `S_ε` and its entrywise derivative. -/
noncomputable def Sf (ε : ℝ) : Matrix ι ι ℝ := Sn K (nε n0 φ ε)
noncomputable def Sf' (ε : ℝ) : Matrix ι ι ℝ := fun i j => deriv (fun e => Sn K (nε n0 φ e) i j) ε
noncomputable def vf (ε : ℝ) : ι → ℝ := vn K (nε n0 φ ε)
noncomputable def vf' (ε : ℝ) : ι → ℝ := fun i => deriv (fun e => vn K (nε n0 φ e) i) ε

lemma hasDerivAt_Sf (ε : ℝ) (i j : ι) : HasDerivAt (fun e => Sf K n0 φ e i j) (Sf' K n0 φ ε i j) ε :=
  ((cd_S K n0 φ hK hn0 hq i j).differentiable one_ne_zero ε).hasDerivAt

lemma hasDerivAt_vf [Nonempty ι] (ε : ℝ) (i : ι) :
    HasDerivAt (fun e => vf K n0 φ e i) (vf' K n0 φ ε i) ε :=
  ((cd_v K n0 φ hK hn0 hq i).differentiable one_ne_zero ε).hasDerivAt

/-! ## Stage 2: gap and derivative bound near `0` from the background gap -/

lemma cont_R [Nonempty ι] :
    Continuous (fun ε => Sf K n0 φ ε - vecMulVec (vf K n0 φ ε) (vf K n0 φ ε)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.sub_apply, vecMulVec_apply]
  exact (cd_S K n0 φ hK hn0 hq a b).continuous.sub
    ((cd_v K n0 φ hK hn0 hq a).continuous.mul (cd_v K n0 φ hK hn0 hq b).continuous)

lemma cont_R' [Nonempty ι] :
    Continuous (fun ε => Sf' K n0 φ ε - CTG.DensityExchange.dPi (vf K n0 φ ε) (vf' K n0 φ ε)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Matrix.sub_apply, CTG.DensityExchange.dPi, Matrix.add_apply, vecMulVec_apply, Sf', vf, vf']
  have hva := cd_v K n0 φ hK hn0 hq a
  have hvb := cd_v K n0 φ hK hn0 hq b
  exact ((cd_S K n0 φ hK hn0 hq a b).continuous_deriv le_rfl).sub
    (((hva.continuous_deriv le_rfl).mul hvb.continuous).add
      (hva.continuous.mul (hvb.continuous_deriv le_rfl)))

/-- **Stage 2.** From the background gap `‖S_0 − v_0 v_0ᵀ‖ ≤ ρ₀ < 1` there is a ball on which the gap is
`≤ (1+ρ₀)/2` and the derivative of `S − v vᵀ` is bounded. -/
theorem gap_near_zero [Nonempty ι] (ρ₀ : ℝ) (hρ₀ : ρ₀ < 1)
    -- HYPOTHESIS (property of the background graph, e.g. connected and not bipartite): spectral gap at ε = 0
    (hgap0 : ‖Sn K n0 - vecMulVec (vn K n0) (vn K n0)‖ ≤ ρ₀) :
    ∃ δ > 0, ∃ C : ℝ, ∀ ε ∈ ball (0 : ℝ) δ,
      ‖Sf K n0 φ ε - vecMulVec (vf K n0 φ ε) (vf K n0 φ ε)‖ ≤ (1 + ρ₀) / 2 ∧
      ‖Sf' K n0 φ ε - CTG.DensityExchange.dPi (vf K n0 φ ε) (vf' K n0 φ ε)‖ ≤ C := by
  have h0 : Sf K n0 φ 0 - vecMulVec (vf K n0 φ 0) (vf K n0 φ 0) = Sn K n0 - vecMulVec (vn K n0) (vn K n0) := by
    simp only [Sf, vf, CTG.DensityResponse.nε_zero]
  have hA : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖Sf K n0 φ ε - vecMulVec (vf K n0 φ ε) (vf K n0 φ ε)‖ < (1 + ρ₀) / 2 := by
    have hc := ((cont_R K n0 φ hK hn0 hq).norm).continuousAt (x := 0)
    refine hc.eventually (gt_mem_nhds ?_)
    show ‖Sf K n0 φ 0 - vecMulVec (vf K n0 φ 0) (vf K n0 φ 0)‖ < (1 + ρ₀) / 2
    rw [h0]; linarith
  set C := ‖Sf' K n0 φ 0 - CTG.DensityExchange.dPi (vf K n0 φ 0) (vf' K n0 φ 0)‖ + 1
  have hB : ∀ᶠ ε in 𝓝 (0 : ℝ),
      ‖Sf' K n0 φ ε - CTG.DensityExchange.dPi (vf K n0 φ ε) (vf' K n0 φ ε)‖ < C := by
    have hc := ((cont_R' K n0 φ hK hn0 hq).norm).continuousAt (x := 0)
    exact hc.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hA.and hB)
  exact ⟨δ, hδ, C, fun ε hε => ⟨(hball ε hε).1.le, (hball ε hε).2.le⟩⟩

/-! ## Stage 3: the exchange for the concrete graph -/

/-- **Stage 3.** For the finite kernel graph (`K ≥ 0` symmetric, `n⁰ > 0`, positive row sums) with background gap
`ρ₀ < 1`, the series `Σ_J f_J (S_ε^J)_ii` is differentiable at `ε = 0` and its derivative is the sum of the termwise
derivatives `Σ_J f_J d/dε (S_ε^J)_ii |₀`; the series of termwise derivatives is summable. -/
theorem graph_deriv_sum_powers [Nonempty ι] (hKs : Kᵀ = K) (ρ₀ : ℝ) (hρ₀ : ρ₀ < 1)
    -- HYPOTHESIS (background gap)
    (hgap0 : ‖Sn K n0 - vecMulVec (vn K n0) (vn K n0)‖ ≤ ρ₀) (i : ι) :
    Summable (fun J => fc J * CTG.DensityExchange.dpw (Sf K n0 φ 0) (Sf' K n0 φ 0) J i i) ∧
    HasDerivAt (fun ε => ∑' J, fc J * (Sn K (nε n0 φ ε) ^ J) i i)
      (∑' J, fc J * CTG.DensityExchange.dpw (Sf K n0 φ 0) (Sf' K n0 φ 0) J i i) 0 := by
  obtain ⟨δ, hδ, C, hb⟩ := gap_near_zero K n0 φ hK hn0 hq ρ₀ hρ₀ hgap0
  have hρ0 : 0 ≤ ρ₀ := (norm_nonneg _).trans hgap0
  exact CTG.DensityExchange.deriv_sum_powers (Sf K n0 φ) (Sf' K n0 φ) (vf K n0 φ) (vf' K n0 φ)
    δ ((1 + ρ₀) / 2) C hδ (by linarith) (by linarith)
    (fun ε _ i j => hasDerivAt_Sf K n0 φ hK hn0 hq ε i j)
    (fun ε _ i => hasDerivAt_vf K n0 φ hK hn0 hq ε i)
    (fun ε _ => CTG.DensityResponse.Sn_symm K _ hKs)
    (fun ε _ => vn_eig K _ hK (CTG.DensityResponse.nε_pos n0 φ hn0 ε) (qpos K n0 φ hK hn0 hq ε))
    (fun ε _ => vn_dot K _ hK (CTG.DensityResponse.nε_pos n0 φ hn0 ε) (qpos K n0 φ hK hn0 hq ε))
    (fun ε hε => (hb ε hε).1) (fun ε hε => (hb ε hε).2) i

end Family

omit [Fintype ι] [DecidableEq ι] in
lemma dpw_eq_dpow [Fintype ι] [DecidableEq ι] (M M' : Matrix ι ι ℝ) :
    ∀ J, CTG.DensityExchange.dpw M M' J = dpow M M' J
  | 0 => rfl
  | J + 1 => by
    simp only [CTG.DensityExchange.dpw, CTG.DensityResponse.dpow, dpw_eq_dpow M M' J]

/-- **Stage 3, homogeneous background.** With constant row sums `q₀` the termwise derivative is the
first-order term of the powers along `S₁ = diag(a) S₀ + S₀ diag(a)`, `a = ½(1−𝒢)²φ` (`aφ`). -/
theorem graph_deriv_sum_powers_hom [Nonempty ι] (K : Matrix ι ι ℝ) (n0 φ : ι → ℝ) (q0 : ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hKs : Kᵀ = K) (hn0 : ∀ i, 0 < n0 i)
    -- HYPOTHESIS (homogeneous background): constant row sums `q₀ > 0`
    (hq0 : ∀ i, qn K n0 i = q0) (hq0pos : 0 < q0) (ρ₀ : ℝ) (hρ₀ : ρ₀ < 1)
    -- HYPOTHESIS (background gap)
    (hgap0 : ‖Sn K n0 - vecMulVec (vn K n0) (vn K n0)‖ ≤ ρ₀) (i : ι) :
    Summable (fun J => fc J * dpow (Sn K n0)
      (diagonal (aφ K n0 φ q0) * Sn K n0 + Sn K n0 * diagonal (aφ K n0 φ q0)) J i i) ∧
    HasDerivAt (fun ε => ∑' J, fc J * (Sn K (nε n0 φ ε) ^ J) i i)
      (∑' J, fc J * dpow (Sn K n0)
        (diagonal (aφ K n0 φ q0) * Sn K n0 + Sn K n0 * diagonal (aφ K n0 φ q0)) J i i) 0 := by
  have hq : ∀ i, 0 < qn K n0 i := fun i => hq0 i ▸ hq0pos
  have h := graph_deriv_sum_powers K n0 φ hK hn0 hq hKs ρ₀ hρ₀ hgap0 i
  have hS0 : Sf K n0 φ 0 = Sn K n0 := by simp only [Sf, CTG.DensityResponse.nε_zero]
  have hS' : Sf' K n0 φ 0 =
      diagonal (aφ K n0 φ q0) * Sn K n0 + Sn K n0 * diagonal (aφ K n0 φ q0) := by
    ext a b
    have h1 := hasDerivAt_Sf K n0 φ hK hn0 hq 0 a b
    have h2 := CTG.DensityResponse.hasDerivAt_S K n0 φ q0 hK hn0 hq0 hq0pos a b
    rw [CTG.DensityResponse.nε_zero] at h2
    exact h1.unique h2
  rw [hS0, hS'] at h
  simp only [dpw_eq_dpow] at h
  exact h

end CTG.DensityExchangeGraph
