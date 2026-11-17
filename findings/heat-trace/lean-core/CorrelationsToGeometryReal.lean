/-
  From Correlations to Geometry: instantiation over the real numbers.

  Second Lean file of the project. It USES MATHLIB (tag v4.29.0, Lean 4.29.0) and imports the
  core-library file `CorrelationsToGeometry.lean`, which is left unchanged. The core file proves
  its statements over an arbitrary ordered field with a function `exp` of which only
  `exp (x + y) = exp x * exp y` and `1 + x ≤ exp x` are assumed (`IsExp`), plus the Archimedean
  property where limits are taken. Here these hypotheses are discharged for the real numbers and
  the real exponential function, so that the statements below hold for `Real.exp` without any
  hypothesis on the exponential.

  Still hypotheses, as in the core file: the existence of the sums over infinitely many modes
  (HYPOTHESES `hT`, `hp` below), the spectral theorem, and everything probabilistic.

  How to check: see `docs/HANDOFF.md`, Section 13.
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import CorrelationsToGeometry

namespace CTG.Reals
open CTG.HeatTrace

/-- The cast of the core file agrees with the cast of Mathlib. -/
theorem ncast_eq (n : Nat) : (ncast n : ℝ) = (n : ℝ) := by
  induction n with
  | zero => simp [ncast]
  | succ k ih => simp [ncast, ih]

/-- The real numbers are Archimedean in the sense of the core file. -/
theorem real_archimedean : CTG.HeatTrace.Archimedean ℝ := by
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt x
  exact ⟨n, by rw [ncast_eq]; exact hn⟩

/-- The real exponential function satisfies the two defining properties used in the core file. -/
theorem real_isExp : IsExp Real.exp :=
  { add := Real.exp_add
    ge := fun x => by rw [add_comm]; exact Real.add_one_le_exp x }

/-- The Taylor bounds `IsExp2`, `IsExp3`, which the core file derives from `IsExp` in an
    Archimedean field by Riemann sums, hold for the real exponential. -/
theorem real_isExp2 : IsExp2 Real.exp := isExp2_of_arch real_isExp real_archimedean

theorem real_isExp3 : IsExp3 Real.exp := isExp3_of_arch real_isExp real_archimedean

/-- The partial sums of the exponential series converge to `Real.exp x` in the sense of the core
    file (`Tends`), for `x ≥ 0`. -/
theorem real_tends_pexp {x : ℝ} (hx : 0 ≤ x) : Tends (fun m => pexp m x) (Real.exp x) :=
  tends_pexp real_isExp real_archimedean hx

/-- Theorem "corrected estimator", one low mode, for the real exponential: the corrected graph
    mode differs from the heat mode `e^{-tau u}` by at most
    `(tau u^3/2 + (tau u^2/2)^2) e^{-tau u/2}`, for `0 ≤ u ≤ 1`. -/
theorem real_walk_mode_corrected {tau u : ℝ} (ht : 0 ≤ tau) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    -((tau * u * u * u / 2 + (tau * u * u / 2) * (tau * u * u / 2)) * Real.exp (-(tau * u / 2)))
        ≤ Real.exp (-(tau * (1 - Real.exp (-u))))
              * (1 - tau * (1 - Real.exp (-u)) * (1 - Real.exp (-u)) / 2)
            - Real.exp (-(tau * u)) ∧
    Real.exp (-(tau * (1 - Real.exp (-u))))
              * (1 - tau * (1 - Real.exp (-u)) * (1 - Real.exp (-u)) / 2)
            - Real.exp (-(tau * u))
        ≤ (tau * u * u * u / 2 + (tau * u * u / 2) * (tau * u * u / 2)) * Real.exp (-(tau * u / 2)) :=
  walk_mode_corrected real_isExp3 ht hu0 hu1

/-- The Poisson identity (Theorem "rate" (i), Theorem "Poisson representation") for real
    eigenvalues `s k ≥ 0` and the real exponential. HYPOTHESES `hT`, `hp`: the sums over the
    modes exist (`T` is the subtracted trace, `p j` the `j`-th return moment). Conclusion: the
    Poisson series of the return moments converges to the subtracted trace. -/
theorem real_poisson_identity {tau : ℝ} (ht : 0 ≤ tau) (s : Nat → ℝ) (hs : ∀ k, 0 ≤ s k)
    {p : Nat → ℝ} {T : ℝ}
    (hT : Tends (psumN fun k => Real.exp (-(tau * (1 - s k))) - Real.exp (-tau)) T)
    (hp : ∀ j, Tends (fun n => psumN (fun k => pw (s k) j) n) (p j)) :
    Tends (jsum fun j => poissonW Real.exp tau j * p j) T :=
  poisson_identity real_isExp real_archimedean ht s hs hT hp

/-! ### Bridge to the notions of Mathlib: limits and infinite sums -/

/-- The limit notion of the core file is convergence in the usual sense. -/
theorem tends_iff (f : ℕ → ℝ) (L : ℝ) : Tends f L ↔ Filter.Tendsto f Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h e he
    obtain ⟨N, hN⟩ := h e he
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [(hN n hn).1, (hN n hn).2]
  · intro h e he
    obtain ⟨N, hN⟩ := h e he
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [Real.dist_eq, abs_lt] at h1
    constructor <;> linarith [h1.1, h1.2]

theorem psumN_eq (f : ℕ → ℝ) : ∀ n, psumN f n = ∑ k ∈ Finset.range n, f k
  | 0 => by simp [psumN]
  | n + 1 => by rw [psumN, psumN_eq f n, Finset.sum_range_succ]

theorem jsum_eq (g : ℕ → ℝ) : ∀ m, jsum g m = ∑ j ∈ Finset.range (m + 1), g j
  | 0 => by simp [jsum]
  | m + 1 => by rw [jsum, jsum_eq g m, Finset.sum_range_succ (n := m + 1)]

theorem pw_eq (s : ℝ) : ∀ k, pw s k = s ^ k
  | 0 => by simp [pw]
  | k + 1 => by rw [pw, pw_eq s k, pow_succ, mul_comm]

/-- The Poisson identity with the infinite sums of Mathlib. If the sum over the modes of
    `e^{-tau (1 - s_k)} - e^{-tau}` is `T` (the subtracted trace) and, for every `j`, the sum of
    the `j`-th powers of the eigenvalues is `p j` (the `j`-th return moment), both in the sense of
    `HasSum` (HYPOTHESES `hT`, `hp`: these sums exist), then the partial sums of the Poisson
    series `sum_j e^{-tau} tau^j/j! p_j` converge to `T`. No hypothesis on the exponential. -/
theorem real_poisson_hasSum {tau : ℝ} (ht : 0 ≤ tau) (s : ℕ → ℝ) (hs : ∀ k, 0 ≤ s k)
    {p : ℕ → ℝ} {T : ℝ}
    (hT : HasSum (fun k => Real.exp (-(tau * (1 - s k))) - Real.exp (-tau)) T)
    (hp : ∀ j, HasSum (fun k => s k ^ j) (p j)) :
    Filter.Tendsto (fun m => ∑ j ∈ Finset.range (m + 1), poissonW Real.exp tau j * p j)
      Filter.atTop (nhds T) := by
  have hT' : Tends (psumN fun k => Real.exp (-(tau * (1 - s k))) - Real.exp (-tau)) T := by
    rw [tends_iff]
    have e : (psumN fun k => Real.exp (-(tau * (1 - s k))) - Real.exp (-tau))
        = fun n => ∑ k ∈ Finset.range n, (Real.exp (-(tau * (1 - s k))) - Real.exp (-tau)) :=
      funext (psumN_eq _)
    rw [e]
    exact hT.tendsto_sum_nat
  have hp' : ∀ j, Tends (fun n => psumN (fun k => pw (s k) j) n) (p j) := by
    intro j
    rw [tends_iff]
    have e : (fun n => psumN (fun k => pw (s k) j) n) = fun n => ∑ k ∈ Finset.range n, s k ^ j := by
      funext n
      rw [psumN_eq]
      exact Finset.sum_congr rfl (fun k _ => pw_eq (s k) j)
    rw [e]
    exact (hp j).tendsto_sum_nat
  have key := real_poisson_identity ht s hs hT' hp'
  rw [tends_iff] at key
  have e : (jsum fun j => poissonW Real.exp tau j * p j)
      = fun m => ∑ j ∈ Finset.range (m + 1), poissonW Real.exp tau j * p j := funext (jsum_eq _)
  rw [e] at key
  exact key

/-! ### The spectral theorem: from the matrix to the eigenvalues -/

section Spectral
open Matrix

/-- Bridge from the matrix to the sums over eigenvalues (spectral theorem of Mathlib): for a real
    symmetric matrix the trace of the `k`-th power is the sum of the `k`-th powers of the
    eigenvalues, with multiplicities. In the paper `A = S` and the trace is the return moment
    `m_k = Tr P^k`. -/
theorem trace_pow_eq_sum_eigenvalues {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (k : ℕ) : (A ^ k).trace = ∑ i, hA.eigenvalues i ^ k := by
  have hk : A ^ k = Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hA.eigenvalues) ^ k) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [map_pow]
  rw [hk, diagonal_pow, Unitary.conjStarAlgAut_apply, trace_mul_comm, ← mul_assoc]
  have hu : (star (hA.eigenvectorUnitary : Matrix n n ℝ)) * (hA.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
    Unitary.coe_star_mul_self _
  rw [hu, one_mul, trace_diagonal]
  simp

/-- The exponential series of the real exponential, as an infinite sum of Mathlib. -/
theorem real_hasSum_exp (x : ℝ) : HasSum (fun j : ℕ => x ^ j / (j.factorial : ℝ)) (Real.exp x) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) x
  rwa [← Real.exp_eq_exp_ℝ] at h

/-- Theorem "Poisson representation" (Theorem 3.11 of the paper) in spectral form, for an
    arbitrary real symmetric matrix `S` and every real `tau`, WITHOUT hypotheses:
    `sum_i e^{-tau (1 - s_i)} = sum_j e^{-tau} tau^j/j! Tr S^j`, the right side as an infinite sum.
    The left side is the trace of `e^{-tL}` for `L = (tau/t)(1 - S)` written through the
    eigenvalues `s_i` of `S`; see `poisson_representation_matrix` below for the form with the
    matrix exponential. -/
theorem poisson_representation {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (tau : ℝ) :
    HasSum (fun j : ℕ => Real.exp (-tau) * (tau ^ j / (j.factorial : ℝ)) * (S ^ j).trace)
      (∑ i, Real.exp (-(tau * (1 - hS.eigenvalues i)))) := by
  have h1 : ∀ i, HasSum (fun j : ℕ => Real.exp (-tau) * ((tau * hS.eigenvalues i) ^ j / (j.factorial : ℝ)))
      (Real.exp (-tau) * Real.exp (tau * hS.eigenvalues i)) :=
    fun i => (real_hasSum_exp (tau * hS.eigenvalues i)).mul_left _
  have h2 := hasSum_sum (s := Finset.univ) (fun i _ => h1 i)
  convert h2 using 1
  · funext j
    rw [trace_pow_eq_sum_eigenvalues S hS j, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_pow]; ring
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Real.exp_add]; congr 1; ring

/-- The trace of the matrix exponential of a real symmetric matrix is the sum of the
    exponentials of its eigenvalues. -/
theorem trace_exp_eq_sum_exp_eigenvalues {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) : (NormedSpace.exp A).trace = ∑ i, Real.exp (hA.eigenvalues i) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have h1 : U * star U = 1 := Unitary.coe_mul_star_self _
  have h2 : star U * U = 1 := Unitary.coe_star_mul_self _
  let u : (Matrix n n ℝ)ˣ := ⟨U, star U, h1, h2⟩
  have hA' : A = (u : Matrix n n ℝ) * diagonal (RCLike.ofReal ∘ hA.eigenvalues)
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hexp : NormedSpace.exp A = (u : Matrix n n ℝ)
      * NormedSpace.exp (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) :=
    (congrArg NormedSpace.exp hA').trans (Matrix.exp_units_conj u _)
  rw [hexp, Matrix.trace_units_conj, Matrix.exp_diagonal, trace_diagonal]
  simp [Real.exp_eq_exp_ℝ]

/-- The heat trace of the graph Laplacian through the eigenvalues: for a real symmetric `S`
    with eigenvalues `s_i`, `Tr exp(tau (S - 1)) = sum_i e^{-tau (1 - s_i)}`. In the paper
    `-t L = tau (S - 1)` with `tau = 2t/(c_h xi^2)`. -/
theorem trace_exp_heat {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (tau : ℝ) :
    (NormedSpace.exp (tau • (S - 1))).trace = ∑ i, Real.exp (-(tau * (1 - hS.eigenvalues i))) := by
  let U : Matrix n n ℝ := hS.eigenvectorUnitary
  have h1 : U * star U = 1 := Unitary.coe_mul_star_self _
  have h2 : star U * U = 1 := Unitary.coe_star_mul_self _
  let u : (Matrix n n ℝ)ˣ := ⟨U, star U, h1, h2⟩
  have hS' : S = (u : Matrix n n ℝ) * diagonal (RCLike.ofReal ∘ hS.eigenvalues)
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    conv_lhs => rw [hS.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hD : diagonal (fun i => tau * (hS.eigenvalues i - 1))
      = tau • (diagonal (RCLike.ofReal ∘ hS.eigenvalues) - 1) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hsub : S - 1 = (u : Matrix n n ℝ) * (diagonal (RCLike.ofReal ∘ hS.eigenvalues) - 1)
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, ← hS']
  have hL : tau • (S - 1) = (u : Matrix n n ℝ) * diagonal (fun i => tau * (hS.eigenvalues i - 1))
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    rw [hD, hsub, Matrix.mul_smul, Matrix.smul_mul]
  have hexp := (congrArg NormedSpace.exp hL).trans (Matrix.exp_units_conj u _)
  rw [hexp, Matrix.trace_units_conj, Matrix.exp_diagonal, trace_diagonal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [Real.exp_eq_exp_ℝ]
  congr 1; ring

/-- **Theorem "Poisson representation" (Theorem 3.11 of the paper) for matrices, without
    hypotheses.** For every real symmetric matrix `S` and every real `tau`,
    `Tr exp(tau (S - 1)) = sum_{j ≥ 0} e^{-tau} tau^j/j! Tr S^j`, the right side as an infinite sum
    of Mathlib. With `-t L = tau (S - 1)` the left side is `Tr e^{-tL}`, and the term `j = 0` is
    `N e^{-tau}`. -/
theorem poisson_representation_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (tau : ℝ) :
    HasSum (fun j : ℕ => Real.exp (-tau) * (tau ^ j / (j.factorial : ℝ)) * (S ^ j).trace)
      (NormedSpace.exp (tau • (S - 1))).trace := by
  rw [trace_exp_heat S hS tau]
  exact poisson_representation S hS tau

end Spectral

end CTG.Reals
