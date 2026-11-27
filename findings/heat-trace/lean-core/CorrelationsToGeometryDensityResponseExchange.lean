/-
Fifty-seventh file: exchange of the derivative in a parameter with the sum over the powers, finite-dimensional and
abstract, and the top eigenfunction of the symmetrised kernel.  Namespaces `CTG.DensityExchange`,
`CTG.DensityExchangeCont`; imports Mathlib and the compiled modules of the fifty-fourth and forty-third files;
check with `./check_density_response_exchange.sh`.
Setting: `u(ε) = Σ_J f_J (S_ε^J)_{ii}` with the coefficients `f_J` of `1 − √(1−s)`.
Idea: split off the top mode.  If `S` is symmetric with `S v = v`, `v·v = 1`, `Π = v vᵀ`, `R = S − Π`, then
`S^J = Π + R^J` for `J ≥ 1` (`pow_split`), hence `u(ε) = v_i(ε)² + Σ_J f_J (R_ε^J)_{ii}`.
`deriv_sum_powers`: if on a ball around `0` the family `S_ε` is symmetric and entrywise differentiable, `v_ε` is a
differentiable unit eigenvector for the eigenvalue 1, and (HYPOTHESES of the statement) `‖S_ε − v_ε v_εᵀ‖ ≤ ρ < 1`
in the L2 operator norm (uniform gap) and `‖S'_ε − d(v vᵀ)‖ ≤ C`, then the series of the termwise derivatives
`Σ_J f_J (Σ_p S^p S' S^{J−1−p})_{ii}` is summable and equals the derivative of `u` at `0`.
`Sc_top_eigen` (frame of the forty-third file): `r = √(n D)` is an eigenfunction of the kernel `S` for the eigenvalue 1.
NOT formalised: the hypotheses for the concrete graph (differentiability of the normalised top eigenvector, the gap
for small `ε`); the infinite-dimensional case of the flat torus (compact self-adjoint operator, uniform operator gap
for small `ε`, diagonal bounds for the kernels of `R^J`), and with it the statement that the sum of the first-order
local responses is the derivative of the energy density; the coefficient `c(a)` and its limit.
Observation on `paper/drafts/density_response.tex`: the step "summing with non-negative coefficients (absolutely
convergent)" exchanges derivative and sum without argument; the termwise derivatives are bounded but do not decay,
so the exchange needs the splitting of the top mode and a uniform gap as here.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometrySqrtSeries
import CorrelationsToGeometryDensityResponseCont

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix Finset Metric Filter Topology CTG.SqrtSeries
open scoped Matrix.Norms.L2Operator

namespace CTG.DensityExchange

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Derivative of the `J`-th power along a direction `M'`: `dpw 0 = 0`, `dpw (J+1) = dpw J · M + M^J · M'`
(equal to `Σ_{p<J} M^p M' M^{J−1−p}`). -/
def dpw (M M' : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 0
  | J + 1 => dpw M M' J * M + M ^ J * M'

/-- Entrywise derivative of the powers of an entrywise differentiable matrix family. -/
theorem hasDerivAt_pow_entry (M : ℝ → Matrix ι ι ℝ) (M' : Matrix ι ι ℝ) (ε : ℝ)
    (hM : ∀ i j, HasDerivAt (fun e => M e i j) (M' i j) ε) :
    ∀ J i j, HasDerivAt (fun e => (M e ^ J) i j) (dpw (M ε) M' J i j) ε := by
  intro J
  induction J with
  | zero =>
    intro i j
    simp only [pow_zero, dpw, Matrix.zero_apply]
    exact hasDerivAt_const _ _
  | succ J ih =>
    intro i j
    have e1 : (fun e => (M e ^ (J + 1)) i j) = fun e => ∑ k, (M e ^ J) i k * M e k j := by
      funext e; rw [pow_succ, mul_apply]
    rw [e1]
    have h2 : HasDerivAt (fun e => ∑ k, (M e ^ J) i k * M e k j)
        (∑ k, (dpw (M ε) M' J i k * M ε k j + (M ε ^ J) i k * M' k j)) ε :=
      HasDerivAt.fun_sum fun k _ => (ih i k).mul (hM k j)
    convert h2 using 1
    simp only [dpw, Matrix.add_apply, mul_apply, Finset.sum_add_distrib]

/-- Decomposition of the powers. -/
theorem pow_split (S : Matrix ι ι ℝ) (v : ι → ℝ) (hsym : Sᵀ = S) (heig : S *ᵥ v = v)
    (hn : v ⬝ᵥ v = 1) (J : ℕ) (hJ : 1 ≤ J) :
    S ^ J = vecMulVec v v + (S - vecMulVec v v) ^ J := by
  set P := vecMulVec v v with hP
  have hPP : P * P = P := by
    ext i j
    simp only [hP, mul_apply, vecMulVec_apply]
    have : ∑ k, v i * v k * (v k * v j) = v i * v j * (v ⬝ᵥ v) := by
      rw [dotProduct, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hn, mul_one]
  have hSP : S * P = P := by
    ext i j
    simp only [hP, mul_apply, vecMulVec_apply]
    have : ∑ k, S i k * (v k * v j) = (S *ᵥ v) i * v j := by
      rw [mulVec, dotProduct, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, heig]
  have hPS : P * S = P := by
    ext i j
    simp only [hP, mul_apply, vecMulVec_apply]
    have hSji : ∀ k, S k j = S j k := fun k => by
      have := congrFun (congrFun hsym j) k; simpa [transpose_apply] using this
    have : ∑ k, v i * v k * S k j = v i * (S *ᵥ v) j := by
      rw [mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hSji k]; ring
    rw [this, heig]
  set R := S - P with hRdef
  have hRP : R * P = 0 := by rw [hRdef, sub_mul, hSP, hPP, sub_self]
  have hPR : P * R = 0 := by rw [hRdef, mul_sub, hPS, hPP, sub_self]
  have hS : S = P + R := by rw [hRdef]; abel
  induction J, hJ using Nat.le_induction with
  | base => rw [pow_one, pow_one, hS]
  | succ J hJ ih =>
    have hRJP : R ^ J * P = 0 := by
      obtain ⟨m, rfl⟩ : ∃ m, J = m + 1 := ⟨J - 1, by omega⟩
      rw [pow_succ, mul_assoc, hRP, mul_zero]
    calc S ^ (J + 1) = (P + R ^ J) * (P + R) := by rw [pow_succ, ih, ← hS]
      _ = P * P + P * R + (R ^ J * P + R ^ J * R) := by noncomm_ring
      _ = P + R ^ (J + 1) := by rw [hPP, hPR, hRJP, ← pow_succ]; abel

section Norms

/-- A diagonal entry is bounded by the L2 operator norm. -/
theorem abs_diag_le (A : Matrix ι ι ℝ) (i : ι) : |A i i| ≤ ‖A‖ := by
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i (1 : ℝ)
  have h1 := A.l2_opNorm_mulVec e
  have he : ‖e‖ = 1 := by simp [e]
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm (A *ᵥ e)) i
  have h3 : ((EuclideanSpace.equiv ι ℝ).symm (A *ᵥ e)) i = A i i := by
    simp [e]
  rw [h3, Real.norm_eq_abs] at h2
  rw [he, mul_one] at h1
  exact h2.trans h1

/-- Norm bound for `dpw`. -/
theorem norm_dpw_le (M M' : Matrix ι ι ℝ) (ρ C : ℝ) (hρ : 0 ≤ ρ) (hM : ‖M‖ ≤ ρ) (hM' : ‖M'‖ ≤ C) :
    ∀ J, ‖dpw M M' J‖ ≤ J * ρ ^ (J - 1) * C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hM'
  intro J
  induction J with
  | zero => simp [dpw]
  | succ J ih =>
    rcases Nat.eq_zero_or_pos J with h0 | hpos
    · subst h0; simp [dpw, hM']
    · have hJ1 : ‖M ^ J‖ ≤ ρ ^ J := (norm_pow_le' M hpos).trans (pow_le_pow_left₀ (norm_nonneg _) hM J)
      have hA : ‖dpw M M' J * M‖ ≤ J * ρ ^ (J - 1) * C * ρ :=
        (norm_mul_le _ _).trans (mul_le_mul ih hM (norm_nonneg _)
          (by have := pow_nonneg hρ (J - 1); positivity))
      have hB : ‖M ^ J * M'‖ ≤ ρ ^ J * C :=
        (norm_mul_le _ _).trans (mul_le_mul hJ1 hM' (norm_nonneg _) (pow_nonneg hρ _))
      have hpow : ρ ^ (J - 1) * ρ = ρ ^ J := by
        rw [← pow_succ]; congr 1; omega
      calc ‖dpw M M' (J + 1)‖ ≤ ‖dpw M M' J * M‖ + ‖M ^ J * M'‖ := norm_add_le _ _
        _ ≤ J * ρ ^ (J - 1) * C * ρ + ρ ^ J * C := add_le_add hA hB
        _ = ((J + 1 : ℕ) : ℝ) * ρ ^ (J + 1 - 1) * C := by
          rw [Nat.add_sub_cancel, show J * ρ ^ (J - 1) * C * ρ = J * (ρ ^ (J - 1) * ρ) * C by ring, hpow]
          push_cast; ring

theorem abs_pow_diag_le (M : Matrix ι ι ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hM : ‖M‖ ≤ ρ) (J : ℕ) (hJ : 1 ≤ J)
    (i : ι) : |(M ^ J) i i| ≤ ρ ^ J :=
  (abs_diag_le _ i).trans ((norm_pow_le' M hJ).trans (pow_le_pow_left₀ (norm_nonneg _) hM J))

end Norms

/-! ## The coefficients -/

lemma fc_zero : fc 0 = 0 := by simp [fc]

lemma hasSum_fc : HasSum fc 1 := by
  have h := hasSum_one_sub_sqrt (s := 1) zero_le_one le_rfl
  simpa using h

lemma fc_le_one (J : ℕ) : fc J ≤ 1 :=
  le_hasSum hasSum_fc J (fun j _ => fc_nonneg j)

lemma summable_geom_deriv {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (C : ℝ) :
    Summable fun J : ℕ => C * ((J : ℝ) * ρ ^ (J - 1)) := by
  refine Summable.mul_left C ?_
  rw [← summable_nat_add_iff 1]
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ρ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ)
  have h2 : Summable fun n : ℕ => ρ ^ n := summable_geometric_of_lt_one hρ0 hρ
  convert h1.add h2 using 1
  funext n
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_one]
  ring

/-! ## Main theorem (Stage 1) -/

/-- The derivative of the rank-one part `v vᵀ` along `v'`. -/
def dPi (v v' : ι → ℝ) : Matrix ι ι ℝ := vecMulVec v' v + vecMulVec v v'

/-- **Stage 1.** Interchange of `d/dε` and the sum over powers, finite-dimensional.
HYPOTHESES (all on a ball `|ε| < δ`): entrywise differentiability of `S_ε` and `v_ε`; `S_ε` symmetric with
eigenvector `v_ε` for the eigenvalue `1`, `v_ε · v_ε = 1`; spectral gap in L2 operator norm
`‖S_ε − v_ε v_εᵀ‖ ≤ ρ < 1`; a bound `C` for the derivative of `S_ε − v_ε v_εᵀ`.
CONCLUSION: the termwise derivatives form a summable series (with weights `f_J`), `u(ε) = Σ' f_J (S_ε^J)_{ii}`
is differentiable at `0`, and its derivative is the sum of the termwise derivatives. -/
theorem deriv_sum_powers (S S' : ℝ → Matrix ι ι ℝ) (v v' : ℝ → ι → ℝ) (δ ρ C : ℝ) (hδ : 0 < δ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hS : ∀ ε ∈ ball (0 : ℝ) δ, ∀ i j, HasDerivAt (fun e => S e i j) (S' ε i j) ε)
    (hv : ∀ ε ∈ ball (0 : ℝ) δ, ∀ i, HasDerivAt (fun e => v e i) (v' ε i) ε)
    (hsym : ∀ ε ∈ ball (0 : ℝ) δ, (S ε)ᵀ = S ε)
    (heig : ∀ ε ∈ ball (0 : ℝ) δ, S ε *ᵥ v ε = v ε)
    (hnorm : ∀ ε ∈ ball (0 : ℝ) δ, v ε ⬝ᵥ v ε = 1)
    (hgap : ∀ ε ∈ ball (0 : ℝ) δ,
      ‖S ε - vecMulVec (v ε) (v ε)‖ ≤ ρ)
    (hder : ∀ ε ∈ ball (0 : ℝ) δ,
      ‖S' ε - dPi (v ε) (v' ε)‖ ≤ C)
    (i : ι) :
    Summable (fun J => fc J * dpw (S 0) (S' 0) J i i) ∧
    HasDerivAt (fun ε => ∑' J, fc J * (S ε ^ J) i i) (∑' J, fc J * dpw (S 0) (S' 0) J i i) 0 := by
  have h0 : (0 : ℝ) ∈ ball (0 : ℝ) δ := mem_ball_self hδ
  set R : ℝ → Matrix ι ι ℝ := fun ε => S ε - vecMulVec (v ε) (v ε) with hR
  set R' : ℝ → Matrix ι ι ℝ := fun ε => S' ε - dPi (v ε) (v' ε) with hR'
  -- entrywise derivative of R
  have hRd : ∀ ε ∈ ball (0 : ℝ) δ, ∀ a b, HasDerivAt (fun e => R e a b) (R' ε a b) ε := by
    intro ε hε a b
    have := (hS ε hε a b).sub (((hv ε hε a).mul (hv ε hε b)))
    convert this using 1 <;> (try simp only [hR', dPi, Matrix.sub_apply, Matrix.add_apply,
      vecMulVec_apply]) <;> (try ring)
  have hPd : ∀ ε ∈ ball (0 : ℝ) δ, ∀ a b,
      HasDerivAt (fun e => vecMulVec (v e) (v e) a b) (dPi (v ε) (v' ε) a b) ε := by
    intro ε hε a b
    have := (hv ε hε a).mul (hv ε hε b)
    convert this using 1 <;> (try simp only [dPi, Matrix.add_apply, vecMulVec_apply]) <;> (try ring)
  -- termwise derivative of the R-series and its bound
  set g : ℕ → ℝ → ℝ := fun J ε => fc J * (R ε ^ J) i i with hg
  set g' : ℕ → ℝ → ℝ := fun J ε => fc J * dpw (R ε) (R' ε) J i i with hg'
  have hgd : ∀ J ε, ε ∈ ball (0 : ℝ) δ → HasDerivAt (g J) (g' J ε) ε := fun J ε hε =>
    (hasDerivAt_pow_entry R (R' ε) ε (hRd ε hε) J i i).const_mul (fc J)
  have hgb : ∀ J ε, ε ∈ ball (0 : ℝ) δ → ‖g' J ε‖ ≤ C * ((J : ℝ) * ρ ^ (J - 1)) := by
    intro J ε hε
    have hb := norm_dpw_le (R ε) (R' ε) ρ C hρ0 (hgap ε hε) (hder ε hε) J
    have he := abs_diag_le (dpw (R ε) (R' ε) J) i
    have hC : 0 ≤ C := (norm_nonneg _).trans (hder ε hε)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fc_nonneg J)]
    calc fc J * |dpw (R ε) (R' ε) J i i| ≤ 1 * (J * ρ ^ (J - 1) * C) :=
          mul_le_mul (fc_le_one J) (he.trans hb) (abs_nonneg _) zero_le_one
      _ = C * ((J : ℝ) * ρ ^ (J - 1)) := by ring
  -- summability of the R-series at every ε
  have hgs : ∀ ε ∈ ball (0 : ℝ) δ, Summable fun J => g J ε := by
    intro ε hε
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one hρ0 hρ) fun J => ?_
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; simp [hg, fc_zero]
    · rw [Real.norm_eq_abs, hg, abs_mul, abs_of_nonneg (fc_nonneg J)]
      calc fc J * |(R ε ^ J) i i| ≤ 1 * ρ ^ J :=
            mul_le_mul (fc_le_one J) (abs_pow_diag_le (R ε) ρ hρ0 (hgap ε hε) J hJ i) (abs_nonneg _)
              zero_le_one
        _ = ρ ^ J := one_mul _
  have hT := hasDerivAt_tsum_of_isPreconnected (summable_geom_deriv hρ0 hρ C) isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected hgd hgb h0 (hgs 0 h0) h0
  -- the rank-one part
  have hPi : HasDerivAt (fun ε => v ε i * v ε i) (dPi (v 0) (v' 0) i i) 0 := by
    have := (hv 0 h0 i).mul (hv 0 h0 i)
    convert this using 1 <;> (try simp only [dPi, Matrix.add_apply, vecMulVec_apply]) <;> (try ring)
  -- termwise identity  f_J (S^J)_ii = f_J v_i² + g J
  have hsplit : ∀ ε ∈ ball (0 : ℝ) δ, ∀ J, fc J * (S ε ^ J) i i = fc J * (v ε i * v ε i) + g J ε := by
    intro ε hε J
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; simp [hg, fc_zero]
    · rw [pow_split (S ε) (v ε) (hsym ε hε) (heig ε hε) (hnorm ε hε) J hJ]
      simp only [hg, hR, Matrix.add_apply, vecMulVec_apply]; ring
  have hu_eq : ∀ ε ∈ ball (0 : ℝ) δ,
      ∑' J, fc J * (S ε ^ J) i i = v ε i * v ε i + ∑' J, g J ε := by
    intro ε hε
    rw [tsum_congr (hsplit ε hε), Summable.tsum_add (hasSum_fc.summable.mul_right _) (hgs ε hε),
      tsum_mul_right, hasSum_fc.tsum_eq, one_mul]
  have hev : (fun ε => ∑' J, fc J * (S ε ^ J) i i) =ᶠ[𝓝 0]
      fun ε => v ε i * v ε i + ∑' J, g J ε :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds h0) hu_eq
  -- termwise identity of the derivatives at 0
  have hdsplit : ∀ J, fc J * dpw (S 0) (S' 0) J i i = fc J * dPi (v 0) (v' 0) i i + g' J 0 := by
    intro J
    rcases Nat.eq_zero_or_pos J with hJ | hJ
    · subst hJ; simp [hg', fc_zero]
    · have hA := hasDerivAt_pow_entry S (S' 0) 0 (hS 0 h0) J i i
      have hB := (hPd 0 h0 i i).add (hasDerivAt_pow_entry R (R' 0) 0 (hRd 0 h0) J i i)
      have hev2 : (fun e => (S e ^ J) i i) =ᶠ[𝓝 0]
          fun e => vecMulVec (v e) (v e) i i + (R e ^ J) i i := by
        refine Filter.eventually_of_mem (isOpen_ball.mem_nhds h0) fun e he => ?_
        simp only
        rw [pow_split (S e) (v e) (hsym e he) (heig e he) (hnorm e he) J hJ, Matrix.add_apply]
      have huniq := hA.unique (hB.congr_of_eventuallyEq hev2)
      simp only [hg']; rw [huniq]; ring
  have hsumP : Summable fun J => fc J * dPi (v 0) (v' 0) i i := hasSum_fc.summable.mul_right _
  have hsumR : Summable fun J => g' J 0 :=
    Summable.of_norm_bounded (summable_geom_deriv hρ0 hρ C) fun J => hgb J 0 h0
  refine ⟨?_, ?_⟩
  · rw [funext hdsplit]; exact hsumP.add hsumR
  · rw [tsum_congr hdsplit, Summable.tsum_add hsumP hsumR, tsum_mul_right, hasSum_fc.tsum_eq,
      one_mul]
    exact (hPi.add hT).congr_of_eventuallyEq hev

end CTG.DensityExchange

/-! ## Building block for Stage 2: the top eigenfunction in the continuous frame -/

section ContBlock
open MeasureTheory
namespace CTG.DensityExchangeCont

open CTG.DensityResponseCont

variable {E : Type*} [MeasurableSpace E]

/-- The walk kernel has unit row integrals (no integrability hypothesis needed: `∫ (f/c) = (∫ f)/c`). -/
theorem Pc_row (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x : E) (hD : Dc μ K n x ≠ 0) :
    ∫ y, Pc μ K n x y ∂μ = 1 := by
  unfold Pc
  rw [integral_div]
  exact div_self (by simpa [Dc] using hD)

/-- **Top eigenfunction.** `∫ S(x,y) r(y) dμ(y) = r(x)` for positive `n`, `D`. -/
theorem Sc_top_eigen (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (hn : ∀ x, 0 < n x)
    (hD : ∀ x, 0 < Dc μ K n x) (x : E) :
    ∫ y, Sc μ K n x y * rc μ K n y ∂μ = rc μ K n x := by
  have hr : ∀ y, 0 < rc μ K n y := fun y => Real.sqrt_pos.mpr (mul_pos (hn y) (hD y))
  have h1 : (fun y => Sc μ K n x y * rc μ K n y) = fun y => rc μ K n x * Pc μ K n x y := by
    funext y
    rw [Sc_similar μ K n x y (hn x) (hn y) (hD x) (hD y)]
    field_simp [(hr y).ne']
  rw [h1, integral_const_mul, Pc_row μ K n x (hD x).ne', mul_one]

end CTG.DensityExchangeCont
