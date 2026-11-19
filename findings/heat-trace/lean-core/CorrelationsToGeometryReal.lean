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
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Haar.Unique
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

/-- Lower bound of Theorem "Poisson representation" for matrices: if `tau ≥ 0` and `Tr S ≥ 0`,
    then `N e^{-tau} ≤ Tr exp(tau (S - 1))`, with `N` the size of the matrix. In fact
    `e^{-tau} (N + tau Tr S) ≤ Tr exp(tau (S - 1))` for every real `tau` and every real symmetric
    `S` (second inequality of Proposition "refined bounds"). -/
theorem heat_two_term_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (tau : ℝ) :
    Real.exp (-tau) * ((Fintype.card n : ℝ) + tau * S.trace)
      ≤ (NormedSpace.exp (tau • (S - 1))).trace := by
  rw [trace_exp_heat S hS tau]
  have htr : S.trace = ∑ i, hS.eigenvalues i := by
    have h := hS.trace_eq_sum_eigenvalues (𝕜 := ℝ)
    simpa using h
  have hterm : ∀ i, Real.exp (-tau) * (1 + tau * hS.eigenvalues i)
      ≤ Real.exp (-(tau * (1 - hS.eigenvalues i))) := by
    intro i
    have h1 : -(tau * (1 - hS.eigenvalues i)) = -tau + tau * hS.eigenvalues i := by ring
    rw [h1, Real.exp_add]
    have h2 : 1 + tau * hS.eigenvalues i ≤ Real.exp (tau * hS.eigenvalues i) := by
      have := Real.add_one_le_exp (tau * hS.eigenvalues i); linarith
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  calc Real.exp (-tau) * ((Fintype.card n : ℝ) + tau * S.trace)
      = ∑ i, Real.exp (-tau) * (1 + tau * hS.eigenvalues i) := by
        rw [htr, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
        simp
    _ ≤ ∑ i, Real.exp (-(tau * (1 - hS.eigenvalues i))) :=
        Finset.sum_le_sum (fun i _ => hterm i)

theorem heat_lower_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {tau : ℝ} (ht : 0 ≤ tau) (htr : 0 ≤ S.trace) :
    (Fintype.card n : ℝ) * Real.exp (-tau) ≤ (NormedSpace.exp (tau • (S - 1))).trace := by
  have h := heat_two_term_matrix S hS tau
  have h2 : (Fintype.card n : ℝ) * Real.exp (-tau)
      ≤ Real.exp (-tau) * ((Fintype.card n : ℝ) + tau * S.trace) := by
    have := mul_nonneg ht htr
    nlinarith [Real.exp_pos (-tau)]
  linarith

/-! ### Theorem "Convergence of the heat trace" (Theorem 3.12): the deterministic part

  The proof of Theorem 3.12 splits the graph modes into low ones, `1 - s_a < kappa`, and high ones,
  compares the low modes with numbers `mu_a = t lambda_a` (in the paper the eigenvalues of the
  manifold), and estimates the high modes with `Tr S^2`. The theorem below is this splitting as an
  inequality for an arbitrary real symmetric matrix and arbitrary numbers `mu_a`, without
  hypotheses. What the paper adds, and what is NOT formalised: the eigenvalue estimates of Theorem
  "Eigenvalues" for the low modes, Weyl's law, the bounds `Tr P, Tr S^2 ≤ C xi^{-d}` (all on an
  event of probability one), and the passage to the limit. -/

/-- `|e^{-a} - e^{-b}| ≤ |a - b| e^{-min(a,b)}`. -/
theorem abs_exp_neg_sub (a b : ℝ) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| * Real.exp (-(min a b)) := by
  have key : ∀ x y : ℝ, x ≤ y →
      |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| * Real.exp (-(min x y)) := by
    intro x y hxy
    have h1 : Real.exp (-y) = Real.exp (-x) * Real.exp (-(y - x)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : 1 - (y - x) ≤ Real.exp (-(y - x)) := by
      have := Real.add_one_le_exp (-(y - x)); linarith
    have h3 : Real.exp (-(y - x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have hpos := Real.exp_pos (-x)
    have h4 : 0 ≤ Real.exp (-x) - Real.exp (-y) := by
      rw [h1]; nlinarith
    have h5 : Real.exp (-x) - Real.exp (-y) ≤ (y - x) * Real.exp (-x) := by
      rw [h1]; nlinarith
    rw [abs_of_nonneg h4, min_eq_left hxy, abs_of_nonpos (by linarith)]
    linarith
  rcases le_total a b with h | h
  · exact key a b h
  · have := key b a h
    rwa [abs_sub_comm, abs_sub_comm b a, min_comm] at this

/-- One high mode, `s ≤ 1 - kappa`: `0 ≤ e^{-tau(1-s)} - e^{-tau} - tau s e^{-tau}
    ≤ (tau s)^2/2 e^{-kappa tau}`. The upper bound is `high_mode` of the core file for `Real.exp`. -/
theorem real_high_mode {tau kappa s : ℝ} (ht : 0 ≤ tau) (hk1 : kappa ≤ 1) (hs : s ≤ 1 - kappa) :
    0 ≤ Real.exp (-(tau * (1 - s))) - Real.exp (-tau) - tau * s * Real.exp (-tau) ∧
    Real.exp (-(tau * (1 - s))) - Real.exp (-tau) - tau * s * Real.exp (-tau)
      ≤ (tau * s) * (tau * s) / 2 * Real.exp (-(kappa * tau)) := by
  have h1 : Real.exp (-(tau * (1 - s))) = Real.exp (-tau) * Real.exp (tau * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-(tau * (1 - s))) - Real.exp (-tau) - tau * s * Real.exp (-tau)
      = Real.exp (-tau) * (Real.exp (tau * s) - 1 - tau * s) := by rw [h1]; ring
  rw [h2]
  constructor
  · have := Real.add_one_le_exp (tau * s)
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  · exact high_mode real_isExp2 ht hk1 hs

/-- **The deterministic part of Theorem 3.12.** For every real symmetric matrix `S` with
    eigenvalues `s_i`, every `tau ≥ 0`, `kappa ≤ 1` and all real numbers `mu_i`: with the low modes
    `1 - s_i < kappa` and the high modes the others,
    `|Tr e^{-tL} - N e^{-tau} - sum_low e^{-mu_i}|` is at most the sum of four terms: the comparison
    of the low modes, `sum_low |tau (1 - s_i) - mu_i| e^{-min(tau(1 - s_i), mu_i)}`; the subtracted
    terms of the low modes, `n_low e^{-tau}`; the linear part of the high modes,
    `tau e^{-tau} |sum_high s_i|`; and the quadratic part, `tau^2/2 e^{-kappa tau} Tr S^2`.
    Here `Tr e^{-tL} = Tr exp(tau (S - 1))`. -/
theorem trace_deterministic {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {tau kappa : ℝ} (ht : 0 ≤ tau) (hk1 : kappa ≤ 1) (mu : n → ℝ) :
    |(NormedSpace.exp (tau • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-tau)
        - ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa), Real.exp (-(mu i))|
      ≤ ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa),
            |tau * (1 - hS.eigenvalues i) - mu i|
              * Real.exp (-(min (tau * (1 - hS.eigenvalues i)) (mu i)))
        + ((Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa)).card : ℝ) * Real.exp (-tau)
        + tau * Real.exp (-tau)
            * |∑ i ∈ Finset.univ.filter (fun i => ¬ (1 - hS.eigenvalues i < kappa)), hS.eigenvalues i|
        + tau ^ 2 / 2 * Real.exp (-(kappa * tau)) * (S ^ 2).trace := by
  set s := hS.eigenvalues with hs_def
  set low := Finset.univ.filter (fun i => 1 - s i < kappa) with hlow
  set high := Finset.univ.filter (fun i => ¬ (1 - s i < kappa)) with hhigh
  set E : n → ℝ := fun i => Real.exp (-(tau * (1 - s i))) with hE
  have hsplit : ∀ f : n → ℝ, ∑ i, f i = ∑ i ∈ low, f i + ∑ i ∈ high, f i := fun f =>
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 1 - s i < kappa) f).symm
  have htr : (NormedSpace.exp (tau • (S - 1))).trace = ∑ i, E i := trace_exp_heat S hS tau
  have hN : (Fintype.card n : ℝ) * Real.exp (-tau) = ∑ _i : n, Real.exp (-tau) := by
    simp [Finset.sum_const, Finset.card_univ]
  have hlowcard : ∑ _i ∈ low, Real.exp (-tau) = (low.card : ℝ) * Real.exp (-tau) := by
    simp [Finset.sum_const]
  -- the quantity inside the absolute value, rearranged
  have hid : (NormedSpace.exp (tau • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-tau)
        - ∑ i ∈ low, Real.exp (-(mu i))
      = ∑ i ∈ low, (E i - Real.exp (-(mu i))) - (low.card : ℝ) * Real.exp (-tau)
        + tau * Real.exp (-tau) * ∑ i ∈ high, s i
        + ∑ i ∈ high, (E i - Real.exp (-tau) - tau * s i * Real.exp (-tau)) := by
    rw [htr, hN, hsplit E, hsplit (fun _ => Real.exp (-tau)), hlowcard, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    have : ∑ i ∈ high, tau * s i * Real.exp (-tau) = ∑ i ∈ high, tau * Real.exp (-tau) * s i :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]; ring
  -- the four bounds
  have hb1 : |∑ i ∈ low, (E i - Real.exp (-(mu i)))|
      ≤ ∑ i ∈ low, |tau * (1 - s i) - mu i| * Real.exp (-(min (tau * (1 - s i)) (mu i))) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => abs_exp_neg_sub (tau * (1 - s i)) (mu i)))
  have hmode : ∀ i ∈ high, 0 ≤ E i - Real.exp (-tau) - tau * s i * Real.exp (-tau) ∧
      E i - Real.exp (-tau) - tau * s i * Real.exp (-tau)
        ≤ (tau * s i) * (tau * s i) / 2 * Real.exp (-(kappa * tau)) := by
    intro i hi
    have hi' : ¬ (1 - s i < kappa) := (Finset.mem_filter.mp hi).2
    exact real_high_mode ht hk1 (by linarith [not_lt.mp hi'])
  have hb4lo : 0 ≤ ∑ i ∈ high, (E i - Real.exp (-tau) - tau * s i * Real.exp (-tau)) :=
    Finset.sum_nonneg (fun i hi => (hmode i hi).1)
  have hsq : (S ^ 2).trace = ∑ i, s i ^ 2 := trace_pow_eq_sum_eigenvalues S hS 2
  have hb4 : ∑ i ∈ high, (E i - Real.exp (-tau) - tau * s i * Real.exp (-tau))
      ≤ tau ^ 2 / 2 * Real.exp (-(kappa * tau)) * (S ^ 2).trace := by
    calc ∑ i ∈ high, (E i - Real.exp (-tau) - tau * s i * Real.exp (-tau))
        ≤ ∑ i ∈ high, (tau * s i) * (tau * s i) / 2 * Real.exp (-(kappa * tau)) :=
          Finset.sum_le_sum (fun i hi => (hmode i hi).2)
      _ = tau ^ 2 / 2 * Real.exp (-(kappa * tau)) * ∑ i ∈ high, s i ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      _ ≤ tau ^ 2 / 2 * Real.exp (-(kappa * tau)) * (S ^ 2).trace := by
          rw [hsq, hsplit (fun i => s i ^ 2)]
          have hlowsq : 0 ≤ ∑ i ∈ low, s i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
          have hc : 0 ≤ tau ^ 2 / 2 * Real.exp (-(kappa * tau)) :=
            mul_nonneg (by positivity) (Real.exp_pos _).le
          nlinarith
  have hb2 : 0 ≤ (low.card : ℝ) * Real.exp (-tau) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hb3 : |tau * Real.exp (-tau) * ∑ i ∈ high, s i|
      = tau * Real.exp (-tau) * |∑ i ∈ high, s i| := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg ht (Real.exp_pos _).le)]
  rw [hid]
  have habs := abs_le.mp hb1
  have habs3 := abs_le.mp (le_of_eq hb3)
  rw [abs_le]
  constructor <;> linarith [habs.1, habs.2, habs3.1, habs3.2, neg_abs_le (tau * Real.exp (-tau) * ∑ i ∈ high, s i), le_abs_self (tau * Real.exp (-tau) * ∑ i ∈ high, s i)]

/-- **Theorem 3.12, conditional form.** HYPOTHESES (in the paper: Theorem "Eigenvalues" on an
    event of probability one, with `mu_i = t lambda_i` the eigenvalues of the manifold): for every
    low mode, `mu_i ≥ 0`, `|tau (1 - s_i) - mu_i| ≤ eps * mu_i` and `c * mu_i ≤ tau (1 - s_i)` with
    `c ≤ 1`. Conclusion: the subtracted trace differs from `sum_low e^{-mu_i}` by at most
    `eps * sum_low mu_i e^{-c mu_i} + n_low e^{-tau} + tau e^{-tau} |sum_high s_i|
     + tau^2/2 e^{-kappa tau} Tr S^2`. -/
theorem trace_conditional {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {tau kappa eps c : ℝ} (ht : 0 ≤ tau) (hk1 : kappa ≤ 1)
    (hc1 : c ≤ 1) (mu : n → ℝ)
    (hmu : ∀ i, 1 - hS.eigenvalues i < kappa → 0 ≤ mu i)
    (heig : ∀ i, 1 - hS.eigenvalues i < kappa →
      |tau * (1 - hS.eigenvalues i) - mu i| ≤ eps * mu i)
    (hlow : ∀ i, 1 - hS.eigenvalues i < kappa → c * mu i ≤ tau * (1 - hS.eigenvalues i)) :
    |(NormedSpace.exp (tau • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-tau)
        - ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa), Real.exp (-(mu i))|
      ≤ eps * ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa),
            mu i * Real.exp (-(c * mu i))
        + ((Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa)).card : ℝ) * Real.exp (-tau)
        + tau * Real.exp (-tau)
            * |∑ i ∈ Finset.univ.filter (fun i => ¬ (1 - hS.eigenvalues i < kappa)), hS.eigenvalues i|
        + tau ^ 2 / 2 * Real.exp (-(kappa * tau)) * (S ^ 2).trace := by
  have h := trace_deterministic S hS ht hk1 mu
  have hterm : ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa),
        |tau * (1 - hS.eigenvalues i) - mu i|
          * Real.exp (-(min (tau * (1 - hS.eigenvalues i)) (mu i)))
      ≤ eps * ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < kappa),
          mu i * Real.exp (-(c * mu i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' : 1 - hS.eigenvalues i < kappa := (Finset.mem_filter.mp hi).2
    have h0 := hmu i hi'
    have hmin : c * mu i ≤ min (tau * (1 - hS.eigenvalues i)) (mu i) :=
      le_min (hlow i hi') (by nlinarith)
    have hexp : Real.exp (-(min (tau * (1 - hS.eigenvalues i)) (mu i))) ≤ Real.exp (-(c * mu i)) :=
      Real.exp_le_exp.mpr (by linarith)
    calc |tau * (1 - hS.eigenvalues i) - mu i|
            * Real.exp (-(min (tau * (1 - hS.eigenvalues i)) (mu i)))
        ≤ (eps * mu i) * Real.exp (-(c * mu i)) :=
          mul_le_mul (heig i hi') hexp (Real.exp_pos _).le ((abs_nonneg _).trans (heig i hi'))
      _ = eps * (mu i * Real.exp (-(c * mu i))) := by ring
  linarith

/-- The comparison term of the low modes is bounded by a sum of exponentials (in the paper: by
    the heat trace at the time `c t / 2`): `sum mu_i e^{-c mu_i} ≤ (2/c) sum e^{-(c/2) mu_i}`. -/
theorem low_sum_le {ι : Type} (s : Finset ι) (mu : ι → ℝ) {c : ℝ} (hc : 0 < c) (hmu : ∀ i ∈ s, 0 ≤ mu i) :
    ∑ i ∈ s, mu i * Real.exp (-(c * mu i)) ≤ 2 / c * ∑ i ∈ s, Real.exp (-(c / 2 * mu i)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have h0 := hmu i hi
  have h1 : c / 2 * mu i ≤ Real.exp (c / 2 * mu i) := by
    have := Real.add_one_le_exp (c / 2 * mu i); linarith
  have h2 : Real.exp (-(c * mu i)) = Real.exp (-(c / 2 * mu i)) * Real.exp (-(c / 2 * mu i)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (c / 2 * mu i) * Real.exp (-(c / 2 * mu i)) = 1 := by
    rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-(c / 2 * mu i))
  have h4 : mu i * Real.exp (-(c / 2 * mu i)) ≤ 2 / c := by
    have : c / 2 * mu i * Real.exp (-(c / 2 * mu i)) ≤ 1 := by
      calc c / 2 * mu i * Real.exp (-(c / 2 * mu i))
          ≤ Real.exp (c / 2 * mu i) * Real.exp (-(c / 2 * mu i)) := mul_le_mul_of_nonneg_right h1 hp.le
        _ = 1 := h3
    rw [le_div_iff₀ hc]; nlinarith
  rw [h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right h4 hp.le

/-- Rayleigh bound: if `x · S x ≤ x · x` for all `x`, every eigenvalue of the real symmetric
    matrix `S` is at most one. -/
theorem eigenvalues_le_one {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ) (hS : S.IsHermitian)
    (hq : ∀ x : n → ℝ, x ⬝ᵥ (S *ᵥ x) ≤ x ⬝ᵥ x) (i : n) : hS.eigenvalues i ≤ 1 := by
  have h := hS.eigenvalues_eq i
  have hv := hq (⇑(hS.eigenvectorBasis i))
  have hnorm : (⇑(hS.eigenvectorBasis i) : n → ℝ) ⬝ᵥ ⇑(hS.eigenvectorBasis i) = 1 := by
    have := hS.eigenvectorBasis.orthonormal.1 i
    have h2 : ‖hS.eigenvectorBasis i‖ ^ 2 = 1 := by rw [this]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simpa [dotProduct, _root_.sq, Real.norm_eq_abs] using h2
  simp only [RCLike.re_to_real, star_trivial] at h
  rw [h]; linarith

/-- Rayleigh bound from below. -/
theorem eigenvalues_ge_neg_one {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ) (hS : S.IsHermitian)
    (hq : ∀ x : n → ℝ, -(x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x)) (i : n) : -1 ≤ hS.eigenvalues i := by
  have h := hS.eigenvalues_eq i
  have hv := hq (⇑(hS.eigenvectorBasis i))
  have hnorm : (⇑(hS.eigenvectorBasis i) : n → ℝ) ⬝ᵥ ⇑(hS.eigenvectorBasis i) = 1 := by
    have := hS.eigenvectorBasis.orthonormal.1 i
    have h2 : ‖hS.eigenvectorBasis i‖ ^ 2 = 1 := by rw [this]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simpa [dotProduct, _root_.sq, Real.norm_eq_abs] using h2
  simp only [RCLike.re_to_real, star_trivial] at h
  rw [h]; linarith

/-- The quadratic form of a graph with symmetric nonnegative weights:
    `|sum_ij W_ij y_i y_j| ≤ sum_i D_i y_i^2` with the degrees `D_i = sum_j W_ij`. -/
theorem graph_quad_form {n : Type} [Fintype n] (W : n → n → ℝ) (hsymm : ∀ i j, W i j = W j i)
    (hnn : ∀ i j, 0 ≤ W i j) (y : n → ℝ) :
    |∑ i, ∑ j, W i j * y i * y j| ≤ ∑ i, (∑ j, W i j) * y i ^ 2 := by
  have hswap : ∑ i, ∑ j, W i j * y j ^ 2 = ∑ i, ∑ j, W i j * y i ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hsymm j i]))
  have hd : ∑ i, (∑ j, W i j) * y i ^ 2 = ∑ i, ∑ j, W i j * y i ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
  have h1 : 0 ≤ ∑ i, ∑ j, W i j * (y i - y j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hnn i j) (sq_nonneg _)))
  have h2 : 0 ≤ ∑ i, ∑ j, W i j * (y i + y j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (hnn i j) (sq_nonneg _)))
  have e1 : ∑ i, ∑ j, W i j * (y i - y j) ^ 2
      = ∑ i, ∑ j, W i j * y i ^ 2 + ∑ i, ∑ j, W i j * y j ^ 2 - 2 * ∑ i, ∑ j, W i j * y i * y j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have e2 : ∑ i, ∑ j, W i j * (y i + y j) ^ 2
      = ∑ i, ∑ j, W i j * y i ^ 2 + ∑ i, ∑ j, W i j * y j ^ 2 + 2 * ∑ i, ∑ j, W i j * y i * y j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hd, abs_le]
  constructor <;> linarith

/-- **The spectrum of the normalised graph matrix lies in `[-1, 1]`.** For symmetric nonnegative
    weights `W` with positive degrees `D_i`, every eigenvalue of `S = D^{-1/2} W D^{-1/2}` lies in
    `[-1, 1]`. In the paper this is the statement `s_a ∈ [-1, 1]` at the beginning of the proof of
    Theorem 3.12. -/
theorem normalised_eigenvalues_mem {n : Type} [Fintype n] [DecidableEq n] (W : n → n → ℝ)
    (hsymm : ∀ i j, W i j = W j i) (hnn : ∀ i j, 0 ≤ W i j) (hd : ∀ i, 0 < ∑ j, W i j)
    (S : Matrix n n ℝ) (hSdef : ∀ i j, S i j = W i j / (Real.sqrt (∑ l, W i l) * Real.sqrt (∑ l, W j l)))
    (hS : S.IsHermitian) (i : n) : -1 ≤ hS.eigenvalues i ∧ hS.eigenvalues i ≤ 1 := by
  have key : ∀ x : n → ℝ, |x ⬝ᵥ (S *ᵥ x)| ≤ x ⬝ᵥ x := by
    intro x
    set y : n → ℝ := fun i => x i / Real.sqrt (∑ l, W i l) with hy
    have hsq : ∀ i, Real.sqrt (∑ l, W i l) ^ 2 = ∑ l, W i l := fun i => Real.sq_sqrt (hd i).le
    have hpos : ∀ i, 0 < Real.sqrt (∑ l, W i l) := fun i => Real.sqrt_pos.mpr (hd i)
    have e1 : x ⬝ᵥ (S *ᵥ x) = ∑ i, ∑ j, W i j * y i * y j := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [hSdef i j, hy]
      have := (hpos i).ne'; have := (hpos j).ne'
      field_simp
    have e2 : x ⬝ᵥ x = ∑ i, (∑ j, W i j) * y i ^ 2 := by
      simp only [dotProduct]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hy]
      have := (hpos i).ne'
      rw [← hsq i]; field_simp
    rw [e1, e2]
    exact graph_quad_form W hsymm hnn y
  exact ⟨eigenvalues_ge_neg_one S hS (fun x => (abs_le.mp (key x)).1) i,
    eigenvalues_le_one S hS (fun x => (abs_le.mp (key x)).2) i⟩

/-- Upper bound of Theorem "Poisson representation" for matrices: if all eigenvalues of `S` are at
    most one and `tau ≥ 0`, then `Tr e^{-tL} ≤ N`. -/
theorem heat_upper_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {tau : ℝ} (ht : 0 ≤ tau) (h1 : ∀ i, hS.eigenvalues i ≤ 1) :
    (NormedSpace.exp (tau • (S - 1))).trace ≤ (Fintype.card n : ℝ) := by
  rw [trace_exp_heat S hS tau]
  have h : ∑ i : n, Real.exp (-(tau * (1 - hS.eigenvalues i))) ≤ ∑ _i : n, (1 : ℝ) :=
    Finset.sum_le_sum (fun i _ => by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg ht (sub_nonneg.mpr (h1 i)); linarith)
  simpa using h

/-- Lemma "traces", deterministic part: for a row-stochastic matrix with entries in `[0, b]`,
    `Tr P ≤ N b` and `Tr P^2 ≤ N b`. In the paper `b = C xi^{-d}/N` on the event of Lemma
    "weights", which gives `Tr P, Tr P^2 ≤ C xi^{-d}`. -/
theorem trace_le_of_entry_le {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) {b : ℝ}
    (hb : ∀ i j, P i j ≤ b) : P.trace ≤ (Fintype.card n : ℝ) * b := by
  have h : ∑ i : n, P i i ≤ ∑ _i : n, b := Finset.sum_le_sum (fun i _ => hb i i)
  simpa [Matrix.trace] using h

theorem trace_sq_le_of_entry_le {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) {b : ℝ}
    (h0 : ∀ i j, 0 ≤ P i j) (hb : ∀ i j, P i j ≤ b) (hrow : ∀ i, ∑ j, P i j = 1) :
    (P * P).trace ≤ (Fintype.card n : ℝ) * b := by
  have h : ∑ i : n, ∑ j : n, P i j * P j i ≤ ∑ _i : n, b := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    calc ∑ j : n, P i j * P j i ≤ ∑ j : n, P i j * b :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hb j i) (h0 i j))
      _ = b := by rw [← Finset.sum_mul, hrow i, one_mul]
  simpa [Matrix.trace, Matrix.mul_apply] using h

/-- Lemma "traces", from the normalisation to the entries of the walk: if the kernel has values
    in `[0, A]` and the estimated normalisation `q_i = (1/N) sum_l K_il` lies in `[qmin, qmax]` with
    `qmin > 0`, then every entry of `P = D^{-1} W`, `W_ij = K_ij/(q_i q_j)`, is at most
    `A qmax / (N qmin^2)`. With `trace_le_of_entry_le` and `trace_sq_le_of_entry_le` this gives
    `Tr P, Tr P^2 ≤ A qmax/qmin^2`, which is of the order `xi^{-d}` in the paper. -/
theorem walk_entry_le {n : Type} [Fintype n] (K : n → n → ℝ) (qv : n → ℝ) {A qmin qmax : ℝ}
    (hK0 : ∀ i j, 0 ≤ K i j) (hKA : ∀ i j, K i j ≤ A)
    (hq : ∀ i, (Fintype.card n : ℝ) * qv i = ∑ l, K i l)
    (hqmin : 0 < qmin) (hlo : ∀ i, qmin ≤ qv i) (hhi : ∀ i, qv i ≤ qmax) (i j : n) :
    (K i j / (qv i * qv j)) / (∑ l, K i l / (qv i * qv l))
      ≤ A * qmax / ((Fintype.card n : ℝ) * qmin ^ 2) := by
  have hqi : ∀ l, 0 < qv l := fun l => lt_of_lt_of_le hqmin (hlo l)
  have hqmax : 0 < qmax := lt_of_lt_of_le (hqi i) (hhi i)
  have hN : 0 < (Fintype.card n : ℝ) := by
    have : Nonempty n := ⟨i⟩
    exact_mod_cast Fintype.card_pos
  have hA : 0 ≤ A := (hK0 i j).trans (hKA i j)
  -- denominator from below
  have hden : (Fintype.card n : ℝ) / qmax ≤ ∑ l, K i l / (qv i * qv l) := by
    have h1 : ∀ l, K i l / (qv i * qmax) ≤ K i l / (qv i * qv l) := fun l =>
      div_le_div_of_nonneg_left (hK0 i l) (mul_pos (hqi i) (hqi l))
        (mul_le_mul_of_nonneg_left (hhi l) (hqi i).le)
    calc (Fintype.card n : ℝ) / qmax = ∑ l, K i l / (qv i * qmax) := by
          rw [← Finset.sum_div, ← hq i]
          have := (hqi i).ne'
          field_simp
      _ ≤ ∑ l, K i l / (qv i * qv l) := Finset.sum_le_sum (fun l _ => h1 l)
  have hdenpos : 0 < (Fintype.card n : ℝ) / qmax := div_pos hN hqmax
  -- numerator from above
  have hnum : K i j / (qv i * qv j) ≤ A / (qmin * qmin) :=
    div_le_div₀ hA (hKA i j) (mul_pos hqmin hqmin) (mul_le_mul (hlo i) (hlo j) hqmin.le (hqi i).le)
  have hnum0 : 0 ≤ K i j / (qv i * qv j) := div_nonneg (hK0 i j) (mul_pos (hqi i) (hqi j)).le
  calc (K i j / (qv i * qv j)) / (∑ l, K i l / (qv i * qv l))
      ≤ (A / (qmin * qmin)) / ((Fintype.card n : ℝ) / qmax) :=
        div_le_div₀ (div_nonneg hA (mul_pos hqmin hqmin).le) hnum hdenpos hden
    _ = A * qmax / ((Fintype.card n : ℝ) * qmin ^ 2) := by field_simp

/-- The walk matrix `P = D^{-1} W`, `W_ij = K_ij/(q_i q_j)`, written out for a kernel matrix `K`
    and a normalisation `q`. -/
noncomputable def walkMatrix {n : Type} [Fintype n] (K : n → n → ℝ) (qv : n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => (K i j / (qv i * qv j)) / (∑ l, K i l / (qv i * qv l))

/-- The entries of the walk matrix: the normalisation of the row cancels. -/
theorem walkMatrix_apply' {n : Type} [Fintype n] (K : n → n → ℝ) (qv : n → ℝ) (b j : n)
    (hb : qv b ≠ 0) :
    walkMatrix K qv b j = (K b j / qv j) / ∑ l, K b l / qv l := by
  have e : ∀ l, K b l / (qv b * qv l) = (K b l / qv l) / qv b := fun l => by
    rw [div_div, mul_comm]
  simp only [walkMatrix, Matrix.of_apply, e]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ hb]

/-- Lemma "traces", deterministic assembly: if the kernel has values in `[0, A]` and the estimated
    normalisation `q_i = (1/N) sum_l K_il` lies in `[q0/2, 3 q0/2]` with `q0 > 0`, then
    `Tr P ≤ 6A/q0` and `Tr P^2 ≤ 6A/q0`. -/
theorem traces_of_normalisation {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (K : n → n → ℝ)
    (qv : n → ℝ) {A q0 : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hKA : ∀ i j, K i j ≤ A)
    (hq : ∀ i, (Fintype.card n : ℝ) * qv i = ∑ l, K i l) (hq0 : 0 < q0)
    (hlo : ∀ i, q0 / 2 ≤ qv i) (hhi : ∀ i, qv i ≤ 3 * q0 / 2) :
    (walkMatrix K qv).trace ≤ 6 * A / q0
      ∧ (walkMatrix K qv * walkMatrix K qv).trace ≤ 6 * A / q0 := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hqi : ∀ l, 0 < qv l := fun l => lt_of_lt_of_le (by linarith) (hlo l)
  have hentry : ∀ i j, walkMatrix K qv i j ≤ A * (3 * q0 / 2) / ((Fintype.card n : ℝ) * (q0 / 2) ^ 2) :=
    fun i j => walk_entry_le K qv hK0 hKA hq (by linarith) hlo hhi i j
  have hD : ∀ i, 0 < ∑ l, K i l / (qv i * qv l) := by
    intro i
    have h1 : ∀ l, K i l / (qv i * (3 * q0 / 2)) ≤ K i l / (qv i * qv l) := fun l =>
      div_le_div_of_nonneg_left (hK0 i l) (mul_pos (hqi i) (hqi l))
        (mul_le_mul_of_nonneg_left (hhi l) (hqi i).le)
    have h2 : (Fintype.card n : ℝ) / (3 * q0 / 2) = ∑ l, K i l / (qv i * (3 * q0 / 2)) := by
      rw [← Finset.sum_div, ← hq i]
      have := (hqi i).ne'
      field_simp
    have h3 : 0 < (Fintype.card n : ℝ) / (3 * q0 / 2) := div_pos hN (by linarith)
    calc 0 < (Fintype.card n : ℝ) / (3 * q0 / 2) := h3
      _ = ∑ l, K i l / (qv i * (3 * q0 / 2)) := h2
      _ ≤ ∑ l, K i l / (qv i * qv l) := Finset.sum_le_sum (fun l _ => h1 l)
  have h0 : ∀ i j, 0 ≤ walkMatrix K qv i j := fun i j =>
    div_nonneg (div_nonneg (hK0 i j) (mul_pos (hqi i) (hqi j)).le) (hD i).le
  have hrow : ∀ i, ∑ j, walkMatrix K qv i j = 1 := by
    intro i
    simp only [walkMatrix, Matrix.of_apply]
    rw [← Finset.sum_div]
    exact div_self (hD i).ne'
  have hb : (Fintype.card n : ℝ) * (A * (3 * q0 / 2) / ((Fintype.card n : ℝ) * (q0 / 2) ^ 2))
      = 6 * A / q0 := by
    have := hN.ne'; have := hq0.ne'
    field_simp; ring
  constructor
  · have := trace_le_of_entry_le (walkMatrix K qv) hentry
    rwa [hb] at this
  · have := trace_sq_le_of_entry_le (walkMatrix K qv) h0 hentry hrow
    rwa [hb] at this

/-- Weyl's law on the flat torus, upper bound, as a count of lattice points: every finite set of
    points `n ∈ ℤ^d` with `|n|^2 ≤ m^2` has at most `(2m+1)^d` elements. The eigenvalues of
    `-Δ` on `(ℝ/ℤ)^d` are `4 π^2 |n|^2`, so at most `(2m+1)^d` of them are `≤ 4 π^2 m^2`; that
    these are the eigenvalues is not formalised. -/
theorem lattice_count_le (d m : ℕ) (S : Finset (Fin d → ℤ))
    (hS : ∀ n ∈ S, ∑ i, (n i) ^ 2 ≤ (m : ℤ) ^ 2) : S.card ≤ (2 * m + 1) ^ d := by
  have hsub : S ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m) := by
    intro n hn
    rw [Fintype.mem_piFinset]
    intro i
    have h1 : (n i) ^ 2 ≤ ∑ j, (n j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (n j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : (n i) ^ 2 ≤ (m : ℤ) ^ 2 := h1.trans (hS n hn)
    have h3 : |n i| ≤ (m : ℤ) := abs_le_of_sq_le_sq h2 (Int.natCast_nonneg m)
    rw [Finset.mem_Icc]
    exact abs_le.mp h3
  calc S.card ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m)).card :=
        Finset.card_le_card hsub
    _ = (2 * m + 1) ^ d := by
        rw [Fintype.card_piFinset]
        simp
        congr 1; omega

/-- The continuum modes beyond the low ones: if `lam_i ≥ b` for all `i` of a finite set, then
    `sum e^{-t lam_i} ≤ e^{-t b/2} sum e^{-t lam_i/2}`. In the proof of Theorem 3.12 `b = c xi^{-2}`,
    and the sum on the right is at most the heat trace at the time `t/2`. -/
theorem tail_modes {ι : Type} (s : Finset ι) (lam : ι → ℝ) {t b : ℝ} (ht : 0 ≤ t)
    (hb : ∀ i ∈ s, b ≤ lam i) :
    ∑ i ∈ s, Real.exp (-(t * lam i))
      ≤ Real.exp (-(t * b / 2)) * ∑ i ∈ s, Real.exp (-(t * lam i / 2)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left (hb i hi) ht
  linarith

/-! ### Theorem "kernel" (uniform comparison of the sampled walk with the heat kernel):
     the deterministic core for matrices -/

/-- Stability: a row-stochastic matrix with nonnegative entries does not increase the supremum
    norm. -/
theorem sup_mulVec_le {n : Type} [Fintype n] (P : Matrix n n ℝ) (h0 : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = 1) (v : n → ℝ) {c : ℝ} (hv : ∀ b, |v b| ≤ c) (a : n) :
    |(P *ᵥ v) a| ≤ c := by
  calc |(P *ᵥ v) a| = |∑ b, P a b * v b| := rfl
    _ ≤ ∑ b, |P a b * v b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, P a b * c := Finset.sum_le_sum (fun b _ => by
        rw [abs_mul, abs_of_nonneg (h0 a b)]
        exact mul_le_mul_of_nonneg_left (hv b) (h0 a b))
    _ = c := by rw [← Finset.sum_mul, hrow a, one_mul]

/-- Stability of the powers. -/
theorem sup_pow_mulVec_le {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (k : ℕ) (v : n → ℝ) {c : ℝ}
    (hv : ∀ b, |v b| ≤ c) (a : n) : |((P ^ k) *ᵥ v) a| ≤ c := by
  induction k generalizing v a with
  | zero => simpa using hv a
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec]
    exact ih (P *ᵥ v) (fun b => sup_mulVec_le P h0 hrow v hv b) a

/-- Step 1 of the proof of Theorem "kernel": `P^k g_1 - g_{k+1}` is the telescoping sum of the
    one-step defects `h_m = P g_m - g_{m+1}`, transported by powers of `P`. In the paper
    `g_m(b) = p_m(x_b - x_i)`. -/
theorem lax_telescope {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) (g : ℕ → n → ℝ)
    (k : ℕ) :
    (P ^ k) *ᵥ g 1 - g (k + 1)
      = ∑ m ∈ Finset.range k, (P ^ (k - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have e1 : ∀ m ∈ Finset.range k, (P ^ (k + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))
        = P *ᵥ ((P ^ (k - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) := by
      intro m hm
      have hm' : m < k := Finset.mem_range.mp hm
      have : k + 1 - 1 - m = (k - 1 - m) + 1 := by omega
      rw [this, pow_succ', ← mulVec_mulVec]
    rw [Finset.sum_congr rfl e1, ← mulVec_sum, ← ih]
    have e2 : k + 1 - 1 - k = 0 := by omega
    rw [e2, pow_zero, one_mulVec, mulVec_sub, mulVec_mulVec, ← pow_succ']
    abel

/-- Stability plus consistency in the supremum norm (the argument of Theorem "kernel" in its
    simplest form): if the defects satisfy `|h_m| ≤ eta_m` at every point, then
    `|P^k g_1 - g_{k+1}| ≤ sum_{m ≤ k} eta_m` at every point. -/
theorem lax_kernel_bound {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (g : ℕ → n → ℝ) (eta : ℕ → ℝ) (k : ℕ)
    (hcons : ∀ m < k, ∀ b, |(P *ᵥ g (m + 1) - g (m + 2)) b| ≤ eta (m + 1)) (a : n) :
    |((P ^ k) *ᵥ g 1 - g (k + 1)) a| ≤ ∑ m ∈ Finset.range k, eta (m + 1) := by
  rw [lax_telescope P g k, Finset.sum_apply]
  calc |∑ m ∈ Finset.range k, ((P ^ (k - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a|
      ≤ ∑ m ∈ Finset.range k, |((P ^ (k - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.range k, eta (m + 1) := Finset.sum_le_sum (fun m hm =>
        sup_pow_mulVec_le P h0 hrow _ _ (hcons m (Finset.mem_range.mp hm)) a)

/-- The powers of a matrix with nonnegative entries have nonnegative entries. -/
theorem pow_entries_nonneg {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (k : ℕ) : ∀ i j, 0 ≤ (P ^ k) i j := by
  induction k with
  | zero => intro i j; simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (h0 l j))

/-- Step 2 of the proof of Theorem "kernel", the last step of the walk: if `|c - g| ≤ theta g`
    pointwise and `B` has nonnegative entries, then `|B c - B g| ≤ theta B g` pointwise. In the
    paper `c_b = N P_{bi}`, `g_b = p(x_b - x_i)`, `theta = 4 delta`, `B = P^k`. -/
theorem last_step {n : Type} [Fintype n] (B : Matrix n n ℝ) (hB : ∀ i j, 0 ≤ B i j)
    (c g : n → ℝ) {theta : ℝ} (hc : ∀ b, |c b - g b| ≤ theta * g b) (a : n) :
    |(B *ᵥ c) a - (B *ᵥ g) a| ≤ theta * (B *ᵥ g) a := by
  have e : (B *ᵥ c) a - (B *ᵥ g) a = ∑ b, B a b * (c b - g b) := by
    simp only [mulVec, dotProduct, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [e]
  calc |∑ b, B a b * (c b - g b)| ≤ ∑ b, |B a b * (c b - g b)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, B a b * (theta * g b) := Finset.sum_le_sum (fun b _ => by
        rw [abs_mul, abs_of_nonneg (hB a b)]
        exact mul_le_mul_of_nonneg_left (hc b) (hB a b))
    _ = theta * (B *ᵥ g) a := by
        simp only [mulVec, dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun b _ => by ring)

/-- The weighted form used in Step 3: `|(B v)_a| ≤ (max |B_ab|) sum_b |v_b|`. -/
theorem weighted_mulVec_le {n : Type} [Fintype n] (B : Matrix n n ℝ) (v : n → ℝ) {w : ℝ}
    (hB : ∀ a b, |B a b| ≤ w) (a : n) : |(B *ᵥ v) a| ≤ w * ∑ b, |v b| := by
  calc |(B *ᵥ v) a| = |∑ b, B a b * v b| := rfl
    _ ≤ ∑ b, |B a b * v b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, w * |v b| := Finset.sum_le_sum (fun b _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB a b) (abs_nonneg _))
    _ = w * ∑ b, |v b| := by rw [Finset.mul_sum]

/-- **Theorem "kernel", conditional form for matrices.** `P` row-stochastic with nonnegative
    entries; `g_m` arbitrary vectors (in the paper the heat kernel `p_m(· - x_i)` at the sample
    points); `c` with `|c - g_1| ≤ theta g_1` (in the paper the column `N P_{·i}`).
    HYPOTHESIS `hcons` (the consistency lemma, which is probabilistic and NOT formalised):
    `|P g_m - g_{m+1}| ≤ eta_m` pointwise for `m ≤ k`. Conclusion:
    `|P^k c - g_{k+1}| ≤ theta (g_{k+1} + sum eta_m) + sum eta_m` pointwise, that is, the entries
    `N (P^{k+1})_{ai}` follow the heat kernel. This is the unweighted form; the paper's sharper
    bound uses the mean of `|h_m|` (see `weighted_mulVec_le`) and the induction `kernel_induction`
    of the core file. -/
theorem kernel_theorem_conditional {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (g : ℕ → n → ℝ) (c : n → ℝ)
    {theta : ℝ} (hth : 0 ≤ theta) (hc : ∀ b, |c b - g 1 b| ≤ theta * g 1 b)
    (eta : ℕ → ℝ) (k : ℕ)
    (hcons : ∀ m < k, ∀ b, |(P *ᵥ g (m + 1) - g (m + 2)) b| ≤ eta (m + 1)) (a : n) :
    |((P ^ k) *ᵥ c) a - g (k + 1) a|
      ≤ theta * (g (k + 1) a + ∑ m ∈ Finset.range k, eta (m + 1))
        + ∑ m ∈ Finset.range k, eta (m + 1) := by
  have h1 := last_step (P ^ k) (pow_entries_nonneg P h0 k) c (g 1) hc a
  have h2 := lax_kernel_bound P h0 hrow g eta k hcons a
  have h2' : |((P ^ k) *ᵥ g 1) a - g (k + 1) a| ≤ ∑ m ∈ Finset.range k, eta (m + 1) := by
    simpa using h2
  have h3 : ((P ^ k) *ᵥ g 1) a ≤ g (k + 1) a + ∑ m ∈ Finset.range k, eta (m + 1) := by
    linarith [(abs_le.mp h2').2]
  have h4 : theta * ((P ^ k) *ᵥ g 1) a
      ≤ theta * (g (k + 1) a + ∑ m ∈ Finset.range k, eta (m + 1)) :=
    mul_le_mul_of_nonneg_left h3 hth
  rw [abs_le] at h1 h2' ⊢
  constructor <;> linarith [h1.1, h1.2, h2'.1, h2'.2]

/-- Step 3 of the proof of Theorem "kernel" in the weighted form: the defect `h_m` transported by
    `P^l`, `l ≥ 1`, is bounded by the largest entry of `P^l` times the sum of `|h_m|`, and the last
    defect by its supremum. In the paper `w_l = (m_l + D_l)/N` and `hb_m = N` times the mean of
    `|h_m|`. -/
theorem lax_kernel_bound_weighted {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (g : ℕ → n → ℝ) (w hb : ℕ → ℝ) (hs : ℝ) (j : ℕ)
    (hent : ∀ m < j, ∀ a b, |(P ^ (j - m)) a b| ≤ w (j - m))
    (hbar : ∀ m < j, ∑ b, |(P *ᵥ g (m + 1) - g (m + 2)) b| ≤ hb (m + 1))
    (hw : ∀ m < j, 0 ≤ w (j - m))
    (hsup : ∀ b, |(P *ᵥ g (j + 1) - g (j + 2)) b| ≤ hs) (a : n) :
    |((P ^ (j + 1)) *ᵥ g 1 - g (j + 2)) a|
      ≤ ∑ m ∈ Finset.range j, w (j - m) * hb (m + 1) + hs := by
  rw [lax_telescope P g (j + 1), Finset.sum_apply, Finset.sum_range_succ]
  have hlast : |((P ^ (j + 1 - 1 - j)) *ᵥ (P *ᵥ g (j + 1) - g (j + 2))) a| ≤ hs := by
    have e : j + 1 - 1 - j = 0 := by omega
    rw [e, pow_zero, one_mulVec]; exact hsup a
  have hterm : ∀ m ∈ Finset.range j,
      |((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a| ≤ w (j - m) * hb (m + 1) := by
    intro m hm
    have hm' : m < j := Finset.mem_range.mp hm
    have e : j + 1 - 1 - m = j - m := by omega
    rw [e]
    exact (weighted_mulVec_le (P ^ (j - m)) _ (hent m hm') a).trans
      (mul_le_mul_of_nonneg_left (hbar m hm') (hw m hm'))
  calc |∑ m ∈ Finset.range j, ((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a
          + ((P ^ (j + 1 - 1 - j)) *ᵥ (P *ᵥ g (j + 1) - g (j + 2))) a|
      ≤ |∑ m ∈ Finset.range j, ((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a|
          + |((P ^ (j + 1 - 1 - j)) *ᵥ (P *ᵥ g (j + 1) - g (j + 2))) a| := abs_add_le _ _
    _ ≤ ∑ m ∈ Finset.range j, w (j - m) * hb (m + 1) + hs :=
        add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)) hlast

/-- **The recursion `eq:kernel-rec` of Theorem "kernel" for matrices.** With the last step of the
    walk (`|c - g_1| ≤ theta g_1`, in the paper `theta = 4 delta`):
    `|P^{j+1} c - g_{j+2}| ≤ theta g_{j+2} + (1 + theta) S_j` pointwise, where
    `S_j = sum_{m<j} w_{j-m} hb_{m+1} + hs`. HYPOTHESES: the bounds on the entries of the powers
    (the induction hypothesis on `D_l`), on the sums of the defects and on the last defect (the
    consistency lemma). The induction that turns this recursion into `D_k ≤ C delta' sqrt(k) m_k`
    is `kernel_induction` in the core file. -/
theorem kernel_recursion_matrix {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (g : ℕ → n → ℝ) (c : n → ℝ) {theta : ℝ} (hth : 0 ≤ theta)
    (hc : ∀ b, |c b - g 1 b| ≤ theta * g 1 b) (w hb : ℕ → ℝ) (hs : ℝ) (j : ℕ)
    (hent : ∀ m < j, ∀ a b, |(P ^ (j - m)) a b| ≤ w (j - m))
    (hbar : ∀ m < j, ∑ b, |(P *ᵥ g (m + 1) - g (m + 2)) b| ≤ hb (m + 1))
    (hw : ∀ m < j, 0 ≤ w (j - m))
    (hsup : ∀ b, |(P *ᵥ g (j + 1) - g (j + 2)) b| ≤ hs) (a : n) :
    |((P ^ (j + 1)) *ᵥ c) a - g (j + 2) a|
      ≤ theta * g (j + 2) a
        + (1 + theta) * (∑ m ∈ Finset.range j, w (j - m) * hb (m + 1) + hs) := by
  have h1 := last_step (P ^ (j + 1)) (pow_entries_nonneg P h0 (j + 1)) c (g 1) hc a
  have h2 := lax_kernel_bound_weighted P g w hb hs j hent hbar hw hsup a
  have h2' : |((P ^ (j + 1)) *ᵥ g 1) a - g (j + 2) a|
      ≤ ∑ m ∈ Finset.range j, w (j - m) * hb (m + 1) + hs := by simpa using h2
  have h3 : ((P ^ (j + 1)) *ᵥ g 1) a
      ≤ g (j + 2) a + (∑ m ∈ Finset.range j, w (j - m) * hb (m + 1) + hs) := by
    linarith [(abs_le.mp h2').2]
  have h4 := mul_le_mul_of_nonneg_left h3 hth
  rw [abs_le] at h1 h2' ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2'.1, h2'.2]

/-- The quantity `D_k` of Theorem "kernel": the largest entry of `N P^k - p_k`, where `p_k` is an
    arbitrary family of kernels on the index set (in the paper `p_k(x_a - x_i)`). -/
noncomputable def kernelDist {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (P : Matrix n n ℝ)
    (p : ℕ → n → n → ℝ) (k : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x : n × n => |(Fintype.card n : ℝ) * (P ^ k) x.1 x.2 - p k x.1 x.2|)

/-- `D_k ≤ c` means that every entry is at most `c`. -/
theorem kernelDist_le_iff {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (P : Matrix n n ℝ)
    (p : ℕ → n → n → ℝ) (k : ℕ) (c : ℝ) :
    kernelDist P p k ≤ c ↔ ∀ a i, |(Fintype.card n : ℝ) * (P ^ k) a i - p k a i| ≤ c := by
  unfold kernelDist
  rw [Finset.sup'_le_iff]
  constructor
  · intro h a i; exact h (a, i) (Finset.mem_univ _)
  · intro h x _; exact h x.1 x.2

/-- **Theorem "kernel" for matrices: the whole deterministic argument.** `P` a matrix with
    nonnegative entries, `p_k` kernels with `0 ≤ p_k ≤ mu_k`. HYPOTHESES, all of which are
    statements of the paper that are not formalised here: the last step of the walk,
    `|N P_bi - p_1| ≤ 4 d p_1` (`hlast`, with `d` the size of the normalisation errors); the
    consistency lemma in the mean and in the supremum (`hbar`, `hsup`); the summation over the
    defects (`hsum`, where the facts on the heat kernel enter) and `4d + (1 + 4d) W ≤ 1` (`hW`).
    CONCLUSION: `D_l ≤ mu_l` for all `1 ≤ l ≤ K`, and `D_{j+2} ≤ (4d + (1+4d) W_{j+1}) mu_{j+2}`.
    In the paper `W_k = C delta' sqrt k`, which gives `D_k ≤ C delta' sqrt k m_k`. -/
theorem kernel_theorem_matrix {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (h0 : ∀ i j, 0 ≤ P i j) (p : ℕ → n → n → ℝ) (mu etabar etasup W : ℕ → ℝ)
    {d : ℝ} (K : ℕ) (hd0 : 0 ≤ d) (hd1 : 4 * d ≤ 1)
    (hmu : ∀ k, 0 ≤ mu k) (hp0 : ∀ k a i, 0 ≤ p k a i) (hpmu : ∀ k a i, p k a i ≤ mu k)
    (hlast : ∀ b i, |(Fintype.card n : ℝ) * P b i - p 1 b i| ≤ 4 * d * p 1 b i)
    (hbar : ∀ m i, 1 ≤ m → m < K → ∑ b, |(P *ᵥ (fun b' => p m b' i)) b - p (m + 1) b i|
        ≤ (Fintype.card n : ℝ) * etabar m)
    (hsup : ∀ m i b, 1 ≤ m → m < K →
      |(P *ᵥ (fun b' => p m b' i)) b - p (m + 1) b i| ≤ etasup m)
    (hsum : ∀ j, j + 1 < K → ∑ m ∈ Finset.range j,
        (2 * mu (j - m) / (Fintype.card n : ℝ)) * ((Fintype.card n : ℝ) * etabar (m + 1))
          + etasup (j + 1) ≤ W (j + 1) * mu (j + 2))
    (hW : ∀ j, j + 1 < K → 0 ≤ W (j + 1) ∧ 4 * d + (1 + 4 * d) * W (j + 1) ≤ 1) :
    (∀ l, 1 ≤ l → l ≤ K → kernelDist P p l ≤ mu l)
      ∧ (∀ j, j + 1 < K →
          kernelDist P p (j + 2) ≤ (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2)) := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  -- one step, given the induction hypothesis up to j+1
  have step : ∀ j, j + 1 < K → (∀ l, 1 ≤ l → l ≤ j + 1 → kernelDist P p l ≤ mu l) →
      kernelDist P p (j + 2) ≤ (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2) := by
    intro j hj ih
    rw [kernelDist_le_iff]
    intro a i
    have hent : ∀ m < j, ∀ a b, |(P ^ (j - m)) a b| ≤ 2 * mu (j - m) / (Fintype.card n : ℝ) := by
      intro m hm a b
      rw [abs_of_nonneg (pow_entries_nonneg P h0 _ a b), le_div_iff₀ hN]
      have h1 := (kernelDist_le_iff P p (j - m) (mu (j - m))).mp (ih (j - m) (by omega) (by omega)) a b
      have h2 := hpmu (j - m) a b
      have h3 := (abs_le.mp h1).2
      linarith
    have hw : ∀ m < j, 0 ≤ 2 * mu (j - m) / (Fintype.card n : ℝ) := fun m _ =>
      div_nonneg (mul_nonneg (by norm_num) (hmu _)) hN.le
    have key := kernel_recursion_matrix P h0 (fun m b => p m b i)
      (fun b => (Fintype.card n : ℝ) * P b i) (theta := 4 * d) (by linarith)
      (fun b => hlast b i) (fun l => 2 * mu l / (Fintype.card n : ℝ))
      (fun m => (Fintype.card n : ℝ) * etabar m) (etasup (j + 1)) j hent
      (fun m hm => by simpa using hbar (m + 1) i (by omega) (by omega)) hw
      (fun b => by simpa using hsup (j + 1) i b (by omega) hj) a
    have e : ((P ^ (j + 1)) *ᵥ fun b => (Fintype.card n : ℝ) * P b i) a
        = (Fintype.card n : ℝ) * (P ^ (j + 2)) a i := by
      have hpow : (P ^ (j + 2)) a i = ∑ b, (P ^ (j + 1)) a b * P b i := by
        rw [show j + 2 = (j + 1) + 1 from rfl, pow_succ, Matrix.mul_apply]
      rw [hpow, Finset.mul_sum]
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e] at key
    have hs := hsum j hj
    have hWj := hW j hj
    have hpm := hpmu (j + 2) a i
    have hp0' := hp0 (j + 2) a i
    have hm2 := hmu (j + 2)
    calc |(Fintype.card n : ℝ) * (P ^ (j + 2)) a i - p (j + 2) a i|
        ≤ 4 * d * p (j + 2) a i + (1 + 4 * d) * (∑ m ∈ Finset.range j,
            (2 * mu (j - m) / (Fintype.card n : ℝ)) * ((Fintype.card n : ℝ) * etabar (m + 1))
              + etasup (j + 1)) := key
      _ ≤ 4 * d * mu (j + 2) + (1 + 4 * d) * (W (j + 1) * mu (j + 2)) := by
          have h1 : 4 * d * p (j + 2) a i ≤ 4 * d * mu (j + 2) :=
            mul_le_mul_of_nonneg_left hpm (by linarith)
          have h2 := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 1 + 4 * d by linarith)
          linarith
      _ = (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2) := by ring
  have base : kernelDist P p 1 ≤ mu 1 := by
    rw [kernelDist_le_iff]
    intro a i
    have h1 := hlast a i
    rw [pow_one]
    have h2 : 4 * d * p 1 a i ≤ 1 * mu 1 :=
      mul_le_mul hd1 (hpmu 1 a i) (hp0 1 a i) (by norm_num)
    linarith
  have all : ∀ k, ∀ l, 1 ≤ l → l ≤ k → l ≤ K → kernelDist P p l ≤ mu l := by
    intro k
    induction k with
    | zero => intro l h1 h2; omega
    | succ k ih =>
      intro l hl1 hlk hlK
      by_cases hle : l ≤ k
      · exact ih l hl1 hle hlK
      · have hl : l = k + 1 := by omega
        subst hl
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; exact base
        · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          have hj : j + 1 < K := by omega
          have hstep := step j hj (fun l h1 h2 => ih l h1 h2 (by omega))
          have hWj := hW j hj
          have hm2 := hmu (j + 2)
          calc kernelDist P p (j + 1 + 1) ≤ (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2) := hstep
            _ ≤ 1 * mu (j + 2) := mul_le_mul_of_nonneg_right hWj.2 hm2
            _ = mu (j + 1 + 1) := by ring_nf
  exact ⟨fun l h1 hK => all l l h1 le_rfl hK,
    fun j hj => step j hj (fun l h1 h2 => all l l h1 le_rfl (by omega))⟩

/-! ### Weyl's inequality for the eigenvalues of real symmetric matrices -/

/-- The quadratic form and the norm in the coordinates of the eigenvectors: with `y = U^T x`,
    `x · A x = sum_i a_i y_i^2` and `x · x = sum_i y_i^2`. -/
theorem quad_form_eig {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (x : n → ℝ) :
    x ⬝ᵥ (A *ᵥ x)
      = ∑ i, hA.eigenvalues i * ((star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ x) i ^ 2
    ∧ x ⬝ᵥ x = ∑ i, ((star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ x) i ^ 2 := by
  set U : Matrix n n ℝ := (↑hA.eigenvectorUnitary : Matrix n n ℝ) with hU
  have h1 : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : A = U * diagonal hA.eigenvalues * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa using h
  have hvec : ∀ w : n → ℝ, x ⬝ᵥ (U *ᵥ w) = (star U *ᵥ x) ⬝ᵥ w := by
    intro w
    rw [dotProduct_mulVec, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      mulVec_transpose]
  constructor
  · have e : A *ᵥ x = U *ᵥ (diagonal hA.eigenvalues *ᵥ (star U *ᵥ x)) := by
      conv_lhs => rw [hspec]
      simp [mulVec_mulVec, Matrix.mul_assoc]
    rw [e, hvec]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  · have e : x = U *ᵥ (star U *ᵥ x) := by rw [mulVec_mulVec, h1, one_mulVec]
    have h2 := hvec (star U *ᵥ x)
    rw [← e] at h2
    rw [h2]
    simp only [dotProduct]
    exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **Weyl's inequality, one side** (proven here because the library has none; search of
    18 November 2026): if `x · A x ≤ x · B x + eps (x · x)` for all `x`, then the eigenvalues in
    decreasing order satisfy `a_j ≤ b_j + eps` for every `j`. Proof: a vector orthogonal to the
    eigenvectors of `A` after the `j`-th and to those of `B` before the `j`-th exists by a count of
    dimensions. -/
theorem weyl_le {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) {ε : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x) + ε * (x ⬝ᵥ x))
    (j : Fin (Fintype.card n)) : hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j + ε := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with he
  set UA : Matrix n n ℝ := (↑hA.eigenvectorUnitary : Matrix n n ℝ) with hUA
  set UB : Matrix n n ℝ := (↑hB.eigenvectorUnitary : Matrix n n ℝ) with hUB
  set sA : Finset n := Finset.univ.filter (fun i => j < e.symm i) with hsA
  set sB : Finset n := Finset.univ.filter (fun i => e.symm i < j) with hsB
  -- the linear map whose kernel we need
  let fA : (n → ℝ) →ₗ[ℝ] (sA → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (Subtype.val : sA → n)) ∘ₗ Matrix.mulVecLin (star UA)
  let fB : (n → ℝ) →ₗ[ℝ] (sB → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (Subtype.val : sB → n)) ∘ₗ Matrix.mulVecLin (star UB)
  let f : (n → ℝ) →ₗ[ℝ] (sA → ℝ) × (sB → ℝ) := fA.prod fB
  have hcard : sA.card + sB.card < Fintype.card n := by
    have hdisj : Disjoint sA sB := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have h1 := (Finset.mem_filter.mp hi1).2
      have h2 := (Finset.mem_filter.mp hi2).2
      exact absurd h1 (not_lt.mpr h2.le)
    have hsub : sA ∪ sB ⊆ Finset.univ.erase (e j) := by
      intro i hi
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro hij
      rcases Finset.mem_union.mp hi with h1 | h1
      · have := (Finset.mem_filter.mp h1).2; rw [hij] at this; simp at this
      · have := (Finset.mem_filter.mp h1).2; rw [hij] at this; simp at this
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ] at h1
    have hpos : 0 < Fintype.card n := Fintype.card_pos_iff.mpr ⟨e j⟩
    omega
  have hrank : Module.finrank ℝ ((sA → ℝ) × (sB → ℝ)) < Module.finrank ℝ (n → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe]
    exact hcard
  obtain ⟨x, hxker, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hrank)
  have hfx : f x = 0 := LinearMap.mem_ker.mp hxker
  have hyA : ∀ i, j < e.symm i → (star UA *ᵥ x) i = 0 := by
    intro i hi
    have h1 : fA x = 0 := congrArg Prod.fst hfx
    have h2 := congrFun h1 ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simpa [fA] using h2
  have hyB : ∀ i, e.symm i < j → (star UB *ᵥ x) i = 0 := by
    intro i hi
    have h1 : fB x = 0 := congrArg Prod.snd hfx
    have h2 := congrFun h1 ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simpa [fB] using h2
  obtain ⟨hqA, hnA⟩ := quad_form_eig A hA x
  obtain ⟨hqB, hnB⟩ := quad_form_eig B hB x
  have hlow : hA.eigenvalues₀ j * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
    rw [hqA, hnA, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hi : j < e.symm i
    · rw [hyA i hi]; simp
    · have hle : e.symm i ≤ j := not_lt.mp hi
      have hant : hA.eigenvalues₀ j ≤ hA.eigenvalues i := hA.eigenvalues₀_antitone hle
      exact mul_le_mul_of_nonneg_right hant (_root_.sq_nonneg _)
  have hupp : x ⬝ᵥ (B *ᵥ x) ≤ hB.eigenvalues₀ j * (x ⬝ᵥ x) := by
    rw [hqB, hnB, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    by_cases hi : e.symm i < j
    · rw [hyB i hi]; simp
    · have hle : j ≤ e.symm i := not_lt.mp hi
      have hant : hB.eigenvalues i ≤ hB.eigenvalues₀ j := hB.eigenvalues₀_antitone hle
      exact mul_le_mul_of_nonneg_right hant (_root_.sq_nonneg _)
  have hpos : 0 < x ⬝ᵥ x := by
    have h0 : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]; exact Finset.sum_nonneg (fun i _ => _root_.mul_self_nonneg _)
    rcases h0.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (dotProduct_self_eq_zero.mp heq.symm) hx0
  have hx := h x
  by_contra hcon
  push Not at hcon
  nlinarith [mul_pos (sub_pos.mpr hcon) hpos]

/-- Weyl's inequality: if `|x · (A - B) x| ≤ eps (x · x)` for all `x`, then
    `|a_j - b_j| ≤ eps` for the eigenvalues in decreasing order. -/
theorem weyl_abs {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) {ε : ℝ}
    (h : ∀ x : n → ℝ, |x ⬝ᵥ (A *ᵥ x) - x ⬝ᵥ (B *ᵥ x)| ≤ ε * (x ⬝ᵥ x))
    (j : Fin (Fintype.card n)) : |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤ ε := by
  have h1 := weyl_le A B hA hB (ε := ε) (fun x => by linarith [(abs_le.mp (h x)).2]) j
  have h2 := weyl_le B A hB hA (ε := ε) (fun x => by linarith [(abs_le.mp (h x)).1]) j
  rw [abs_le]; constructor <;> linarith

/-- Schur's test for a symmetric matrix: if every absolute row sum is at most `eps`, then
    `|x · M x| ≤ eps (x · x)`. -/
theorem quad_form_le_of_row_sums {n : Type} [Fintype n] (M : Matrix n n ℝ)
    (hsymm : ∀ i j, M i j = M j i) {ε : ℝ} (hrow : ∀ i, ∑ j, |M i j| ≤ ε) (x : n → ℝ) :
    |x ⬝ᵥ (M *ᵥ x)| ≤ ε * (x ⬝ᵥ x) := by
  have e : x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, M i j * x i * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hterm : ∀ i j, |M i j * x i * x j| ≤ |M i j| * (x i ^ 2 + x j ^ 2) / 2 := by
    intro i j
    rw [mul_assoc, abs_mul]
    have h1 : |x i * x j| ≤ (x i ^ 2 + x j ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [_root_.sq_nonneg (x i - x j), _root_.sq_nonneg (x i + x j)]
    calc |M i j| * |x i * x j| ≤ |M i j| * ((x i ^ 2 + x j ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |M i j| * (x i ^ 2 + x j ^ 2) / 2 := by ring
  have hswap : ∑ i, ∑ j, |M i j| * x j ^ 2 = ∑ i, ∑ j, |M i j| * x i ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hsymm j i]))
  have hd : ∑ i, ∑ j, |M i j| * x i ^ 2 ≤ ε * (x ⬝ᵥ x) := by
    simp only [dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [← Finset.sum_mul]
    calc (∑ j, |M i j|) * x i ^ 2 ≤ ε * x i ^ 2 := mul_le_mul_of_nonneg_right (hrow i) (_root_.sq_nonneg _)
      _ = ε * (x i * x i) := by ring
  rw [e]
  calc |∑ i, ∑ j, M i j * x i * x j| ≤ ∑ i, |∑ j, M i j * x i * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |M i j * x i * x j| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |M i j| * (x i ^ 2 + x j ^ 2) / 2 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = (∑ i, ∑ j, |M i j| * x i ^ 2 + ∑ i, ∑ j, |M i j| * x j ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ ε * (x ⬝ᵥ x) := by rw [hswap]; linarith

/-- **Weyl's inequality with the maximal absolute row sum**, the form used in the proof of Theorem
    "eigenvalues on the torus": `|a_j - b_j| ≤ max_i sum_j |A_ij - B_ij|`. -/
theorem weyl_row_sums {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) {ε : ℝ} (hrow : ∀ i, ∑ j, |A i j - B i j| ≤ ε)
    (j : Fin (Fintype.card n)) : |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤ ε := by
  apply weyl_abs A B hA hB
  intro x
  have hsymm : ∀ i j, (A - B) i j = (A - B) j i := by
    intro i j
    have h1 : A i j = A j i := by have := congrFun (congrFun hA j) i; simpa using this
    have h2 : B i j = B j i := by have := congrFun (congrFun hB j) i; simpa using this
    simp [h1, h2]
  have h := quad_form_le_of_row_sums (A - B) hsymm (ε := ε) (fun i => by simpa using hrow i) x
  rwa [sub_mulVec, dotProduct_sub] at h

/-! ### Eigenvalues of powers and the deterministic part of Theorem "eigenvalues on the torus" -/

section Powers
open Polynomial

/-- The characteristic polynomial of a power of a real symmetric matrix. -/
theorem charpoly_pow_eq {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (k : ℕ) :
    (S ^ k).charpoly = ∏ i, (X - C (hS.eigenvalues i ^ k)) := by
  have hk : S ^ k = Unitary.conjStarAlgAut ℝ _ hS.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ hS.eigenvalues) ^ k) := by
    conv_lhs => rw [hS.spectral_theorem]
    rw [map_pow]
  rw [hk, diagonal_pow, Unitary.conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

/-- Its roots are the powers of the eigenvalues. -/
theorem roots_charpoly_pow {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (k : ℕ) :
    (S ^ k).charpoly.roots
      = Multiset.map (fun j => hS.eigenvalues₀ j ^ k) Finset.univ.val := by
  rw [charpoly_pow_eq S hS k, Polynomial.roots_prod]
  · simp only [roots_X_sub_C, Multiset.bind_singleton]
    have e : (fun i => hS.eigenvalues i ^ k)
        = (fun j => hS.eigenvalues₀ j ^ k) ∘ (Fintype.equivOfCardEq (Fintype.card_fin _)).symm := by
      funext i; rfl
    rw [e, ← Multiset.map_map]
    simp
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact Polynomial.X_sub_C_ne_zero _

/-- For a real symmetric matrix with nonnegative eigenvalues, the eigenvalues of `S^k` in
    decreasing order are the `k`-th powers of the eigenvalues of `S` in decreasing order. -/
theorem eigenvalues₀_pow {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (hnn : ∀ j, 0 ≤ hS.eigenvalues₀ j) (k : ℕ) (hSk : (S ^ k).IsHermitian)
    (j : Fin (Fintype.card n)) : hSk.eigenvalues₀ j = hS.eigenvalues₀ j ^ k := by
  have hanti : Antitone (fun j => hS.eigenvalues₀ j ^ k) := fun a b hab =>
    pow_le_pow_left₀ (hnn b) (hS.eigenvalues₀_antitone hab) k
  have h1 := hSk.sort_roots_charpoly_eq_eigenvalues₀
  have h2 : ((S ^ k).charpoly.roots.map RCLike.re).sort (· ≥ ·)
      = List.ofFn (fun j => hS.eigenvalues₀ j ^ k) := by
    simp_rw [roots_charpoly_pow S hS k, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.re_to_real, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hanti.sortedGE_ofFn
  have h3 : List.ofFn hSk.eigenvalues₀ = List.ofFn (fun j => hS.eigenvalues₀ j ^ k) := by
    rw [← h1, h2]
  exact congrFun (List.ofFn_injective h3) j

/-- **Theorem "eigenvalues on the torus", the deterministic part for matrices.** `S` real symmetric
    with eigenvalues `s_j ∈ [0, 1]` in decreasing order, `Q` real symmetric with eigenvalues `q_j`.
    HYPOTHESES (in the paper: Theorem "kernel" for the first, Lemma "kernel matrix" for the
    second): every absolute row sum of `S^{k+1} - Q` is at most `eps`, and `|q_j - a^{k+1}| ≤ eps'`
    for a number `a ∈ [0, 1]` with `2 (eps + eps') ≤ a^{k+1}` (in the paper `a = e^{-sigma lambda_j}`).
    CONCLUSION: `|s_j^{k+1} - a^{k+1}| ≤ eps + eps'` (part (i)) and
    `(k+1) a^{k+1} |s_j - a| ≤ 2 (eps + eps')` (part (ii)). -/
theorem eigtorus_matrix {n : Type} [Fintype n] [DecidableEq n] (S Q : Matrix n n ℝ)
    (hS : S.IsHermitian) (hQ : Q.IsHermitian) (hnn : ∀ j, 0 ≤ hS.eigenvalues₀ j)
    (hle1 : ∀ j, hS.eigenvalues₀ j ≤ 1) (k : ℕ) {eps eps' a : ℝ}
    (hrow : ∀ i, ∑ l, |(S ^ (k + 1)) i l - Q i l| ≤ eps)
    (j : Fin (Fintype.card n)) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hQj : |hQ.eigenvalues₀ j - a ^ (k + 1)| ≤ eps')
    (h3 : 2 * (eps + eps') ≤ a ^ (k + 1)) :
    |hS.eigenvalues₀ j ^ (k + 1) - a ^ (k + 1)| ≤ eps + eps'
      ∧ ((k + 1 : ℕ) : ℝ) * (a ^ (k + 1) * |hS.eigenvalues₀ j - a|) ≤ 2 * (eps + eps') := by
  have hSk : (S ^ (k + 1)).IsHermitian := hS.pow (k + 1)
  have hw := weyl_row_sums (S ^ (k + 1)) Q hSk hQ hrow j
  rw [eigenvalues₀_pow S hS hnn (k + 1) hSk j] at hw
  have hi : |hS.eigenvalues₀ j ^ (k + 1) - a ^ (k + 1)| ≤ eps + eps' := by
    have h1 := abs_le.mp hw
    have h2 := abs_le.mp hQj
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨hi, ?_⟩
  have hb := abs_le.mp hi
  have r := eigenvalue_from_power (α := ℝ) (hnn j) (hle1 j) ha0 ha1 k
    (eta := eps + eps') (by rw [pw_eq, pw_eq]; linarith [hb.2])
    (by rw [pw_eq, pw_eq]; linarith [hb.1]) (by rw [pw_eq]; exact h3)
  rw [pw_eq, ncast_eq] at r
  rcases le_total a (hS.eigenvalues₀ j) with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]; exact r.1
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]; exact r.2

/-- The eigenvalues in decreasing order are determined by the characteristic polynomial. -/
theorem eigenvalues₀_eq_of_charpoly_eq {n : Type} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly) :
    hA.eigenvalues₀ = hB.eigenvalues₀ := by
  have h1 := hA.sort_roots_charpoly_eq_eigenvalues₀
  have h2 := hB.sort_roots_charpoly_eq_eigenvalues₀
  rw [h] at h1
  exact List.ofFn_injective (h1.symm.trans h2)

/-- `X Xᵀ` and `Xᵀ X`, each padded with a zero block to the size `n ⊕ F`, have the same eigenvalues
    in decreasing order. -/
theorem eigenvalues₀_gram_swap {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    (X : Matrix n F ℝ)
    (h1 : (fromBlocks (X * Xᵀ) 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (h2 : (fromBlocks (0 : Matrix n n ℝ) 0 0 (Xᵀ * X)).IsHermitian) :
    h1.eigenvalues₀ = h2.eigenvalues₀ := by
  apply eigenvalues₀_eq_of_charpoly_eq
  have e1 : fromBlocks (X * Xᵀ) 0 0 (0 : Matrix F F ℝ)
      = fromBlocks (0 : Matrix n n ℝ) X 0 (0 : Matrix F F ℝ)
        * fromBlocks (0 : Matrix n n ℝ) 0 Xᵀ (0 : Matrix F F ℝ) := by
    rw [fromBlocks_multiply]; simp
  have e2 : fromBlocks (0 : Matrix n n ℝ) 0 0 (Xᵀ * X)
      = fromBlocks (0 : Matrix n n ℝ) 0 Xᵀ (0 : Matrix F F ℝ)
        * fromBlocks (0 : Matrix n n ℝ) X 0 (0 : Matrix F F ℝ) := by
    rw [fromBlocks_multiply]; simp
  rw [e1, e2, charpoly_mul_comm]

/-- **Lemma "kernel matrix", the deterministic core.** `Q = X Xᵀ` with `X` of size `n × F` (in the
    paper `X = V A^{1/2}`, `V` the sampled Fourier modes and `A` the diagonal matrix of the
    Fourier coefficients of the kernel, so that `Xᵀ X = A^{1/2} G A^{1/2}` with the Gram matrix
    `G`). If every absolute row sum of `Xᵀ X - diag(a)` is at most `eps`, then the eigenvalues of
    `Q` in decreasing order, padded with zeros to the size `n ⊕ F`, are within `eps` of the numbers
    `a_f` padded with zeros and arranged in decreasing order (the eigenvalues of the padded
    diagonal matrix). HYPOTHESES `h1`, `hD`: symmetry of the two padded matrices. -/
theorem kernel_matrix_spectrum_det {n F : Type} [Fintype n] [Fintype F] [DecidableEq n]
    [DecidableEq F] (X : Matrix n F ℝ) (a : F → ℝ) {eps : ℝ}
    (hrow : ∀ f, ∑ g, |(Xᵀ * X) f g - diagonal a f g| ≤ eps) (heps : 0 ≤ eps)
    (h1 : (fromBlocks (X * Xᵀ) 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (hD : (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian)
    (j : Fin (Fintype.card (n ⊕ F))) : |h1.eigenvalues₀ j - hD.eigenvalues₀ j| ≤ eps := by
  have h2 : (fromBlocks (0 : Matrix n n ℝ) 0 0 (Xᵀ * X)).IsHermitian := by
    have hXX : (Xᵀ * X).IsHermitian := by
      have := isHermitian_conjTranspose_mul_self X
      simpa [conjTranspose_eq_transpose_of_trivial] using this
    exact IsHermitian.fromBlocks (by simp [IsHermitian]) (by simp) hXX
  rw [eigenvalues₀_gram_swap X h1 h2]
  apply weyl_row_sums _ _ h2 hD
  intro i
  rw [Fintype.sum_sum_type]
  cases i with
  | inl i => simpa using heps
  | inr f => simpa using hrow f

/-- The roots of the characteristic polynomial of a symmetric matrix padded with a zero block:
    the eigenvalues and as many zeros as the block has rows. -/
theorem roots_charpoly_pad {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (fromBlocks A 0 0 (0 : Matrix F F ℝ)).charpoly.roots
      = ((List.ofFn hA.eigenvalues₀ ++ List.replicate (Fintype.card F) (0 : ℝ) : List ℝ) : Multiset ℝ) := by
  rw [charpoly_fromBlocks_zero₁₂, charpoly_zero, Polynomial.roots_mul, roots_X_pow,
    hA.roots_charpoly_eq_eigenvalues₀]
  · simp [Fin.univ_val_map, ← Multiset.coe_add, Multiset.nsmul_singleton]
    exact (Multiset.coe_replicate _ _).symm
  · exact mul_ne_zero (charpoly_monic A).ne_zero (pow_ne_zero _ X_ne_zero)

/-- For nonnegative eigenvalues, the eigenvalues of the padded matrix in decreasing order are
    those of the matrix followed by zeros. -/
theorem eigenvalues₀_pad {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (hnn : ∀ j, 0 ≤ hA.eigenvalues₀ j)
    (hB : (fromBlocks A 0 0 (0 : Matrix F F ℝ)).IsHermitian) :
    List.ofFn hB.eigenvalues₀
      = List.ofFn hA.eigenvalues₀ ++ List.replicate (Fintype.card F) (0 : ℝ) := by
  rw [← hB.sort_roots_charpoly_eq_eigenvalues₀, roots_charpoly_pad A hA]
  simp only [Multiset.map_coe, RCLike.re_to_real, List.map_id', Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq]
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.sortedGE_iff_pairwise]
    exact hA.eigenvalues₀_antitone.sortedGE_ofFn
  · rw [List.pairwise_replicate]; exact Or.inr (le_refl _)
  · intro x hx y hy
    rw [List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [List.mem_replicate] at hy
    rw [hy.2]
    exact hnn j

/-- Pointwise form: the first eigenvalues of the padded matrix are those of the matrix. -/
theorem eigenvalues₀_pad_apply {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (hnn : ∀ j, 0 ≤ hA.eigenvalues₀ j)
    (hB : (fromBlocks A 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (j : Fin (Fintype.card n)) (hj : j.val < Fintype.card (n ⊕ F)) :
    hB.eigenvalues₀ ⟨j.val, hj⟩ = hA.eigenvalues₀ j := by
  have h := eigenvalues₀_pad A hA hnn hB
  have h2 := congrArg (fun l : List ℝ => l[j.val]?) h
  have hlen : j.val < (List.ofFn hA.eigenvalues₀).length := by simp
  simp only [List.getElem?_append_left hlen] at h2
  rw [List.getElem?_ofFn, List.getElem?_ofFn] at h2
  have h3 : ∃ (h : j.val < Fintype.card n + Fintype.card F),
      hB.eigenvalues₀ ⟨j.val, by simpa using h⟩ = hA.eigenvalues₀ j := by simpa [hj, j.isLt] using h2
  obtain ⟨_, h4⟩ := h3
  exact h4

/-- **Lemma "kernel matrix", deterministic part, for the eigenvalues of `Q` itself.** `Q = X Xᵀ`
    with `X` of size `n × F`. If every absolute row sum of `Xᵀ X - diag(a)` is at most `eps`,
    then for every `j` the `j`-th eigenvalue of `Q` in decreasing order is within `eps` of the
    `j`-th of the numbers `a_f`, padded with zeros and arranged in decreasing order. HYPOTHESES
    `h1`, `hD`: symmetry of the two padded matrices (immediate, kept as hypotheses for brevity). -/
theorem kernel_matrix_spectrum {n F : Type} [Fintype n] [Fintype F] [DecidableEq n]
    [DecidableEq F] (X : Matrix n F ℝ) (a : F → ℝ) {eps : ℝ}
    (hrow : ∀ f, ∑ g, |(Xᵀ * X) f g - diagonal a f g| ≤ eps) (heps : 0 ≤ eps)
    (hQ : (X * Xᵀ).IsHermitian)
    (h1 : (fromBlocks (X * Xᵀ) 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (hD : (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian)
    (j : Fin (Fintype.card n)) (hj : j.val < Fintype.card (n ⊕ F)) :
    |hQ.eigenvalues₀ j - hD.eigenvalues₀ ⟨j.val, hj⟩| ≤ eps := by
  have hpsd : Matrix.PosSemidef (X * Xᵀ) := by
    have := Matrix.posSemidef_self_mul_conjTranspose X
    simpa [conjTranspose_eq_transpose_of_trivial] using this
  have hnn : ∀ i, 0 ≤ hQ.eigenvalues₀ i := by
    intro i
    have h := hpsd.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
    simpa [IsHermitian.eigenvalues] using h
  rw [← eigenvalues₀_pad_apply (X * Xᵀ) hQ hnn h1 j hj]
  exact kernel_matrix_spectrum_det X a hrow heps h1 hD ⟨j.val, hj⟩

/-- Row sums from the Gram matrix of the sampled modes. `X i f = √(a f) · v i f`; if the Gram
    matrix `vᵀ v` is within `eta` of the identity entrywise, every absolute row sum of
    `Xᵀ X - diag(a)` is at most `eta · √(a f) · ∑_g √(a g)`. -/
theorem gram_row_sums {n F : Type} [Fintype n] [Fintype F] [DecidableEq F]
    (v : Matrix n F ℝ) (a : F → ℝ) (ha : ∀ f, 0 ≤ a f) {eta : ℝ}
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta) (f : F) :
    ∑ g, |((Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)) f g - diagonal a f g|
      ≤ eta * Real.sqrt (a f) * ∑ g, Real.sqrt (a g) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun g _ => ?_
  have hent : ((Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)) f g - diagonal a f g
      = Real.sqrt (a f) * Real.sqrt (a g) * (∑ i, v i f * v i g - (if f = g then 1 else 0)) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, diagonal_apply]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · by_cases h : f = g
      · subst h; simp [Real.mul_self_sqrt (ha f)]
      · simp [h]
  rw [hent, abs_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have := mul_le_mul_of_nonneg_left (hG f g)
    (mul_nonneg (Real.sqrt_nonneg (a f)) (Real.sqrt_nonneg (a g)))
  nlinarith [this]

/-- Entries of the finite-rank kernel matrix: for `X i f = √(a f) · v i f` with `a ≥ 0`,
    `(X Xᵀ) i j = ∑_f a_f v_{if} v_{jf}`. With `v i f = φ_f(x_i)/√N` this is the matrix
    `K(x_i, x_j)/N` of the truncated kernel `K(x, y) = ∑_f a_f φ_f(x) φ_f(y)`. -/
theorem finite_rank_kernel_entry {n F : Type} [Fintype n] [Fintype F]
    (v : Matrix n F ℝ) (a : F → ℝ) (ha : ∀ f, 0 ≤ a f) (i j : n) :
    ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i j = ∑ f, a f * v i f * v j f := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun f _ => ?_
  have := Real.mul_self_sqrt (ha f)
  calc Real.sqrt (a f) * v i f * (Real.sqrt (a f) * v j f)
      = (Real.sqrt (a f) * Real.sqrt (a f)) * v i f * v j f := by ring
    _ = a f * v i f * v j f := by rw [this]

/-- **Spectrum of a finite-rank kernel matrix from the Gram matrix of the sampled modes
    (Lemma "kernel matrix" for a truncated kernel, deterministic).** If the Gram matrix `vᵀ v` is
    within `eta` of the identity entrywise and `√(a f) ≤ s` for all `f`, every eigenvalue of
    `Q = X Xᵀ`, `X i f = √(a f) v i f`, in decreasing order is within `eta · s · ∑_g √(a g)` of the
    corresponding one of the numbers `a_f`, padded with zeros and arranged in decreasing order. -/
theorem finite_rank_kernel_spectrum {n F : Type} [Fintype n] [Fintype F] [DecidableEq n]
    [DecidableEq F] (v : Matrix n F ℝ) (a : F → ℝ) (ha : ∀ f, 0 ≤ a f) {eta s : ℝ}
    (heta : 0 ≤ eta) (hs0 : 0 ≤ s) (hs : ∀ f, Real.sqrt (a f) ≤ s)
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta)
    (hQ : ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ).IsHermitian)
    (h1 : (fromBlocks ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (hD : (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian)
    (j : Fin (Fintype.card n)) (hj : j.val < Fintype.card (n ⊕ F)) :
    |hQ.eigenvalues₀ j - hD.eigenvalues₀ ⟨j.val, hj⟩| ≤ eta * s * ∑ g, Real.sqrt (a g) := by
  have hsum : 0 ≤ ∑ g, Real.sqrt (a g) := Finset.sum_nonneg fun g _ => Real.sqrt_nonneg _
  refine kernel_matrix_spectrum _ a (fun f => ?_) (mul_nonneg (mul_nonneg heta hs0) hsum)
    hQ h1 hD j hj
  refine (gram_row_sums v a ha hG f).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hs f) heta) hsum

/-- **Eigenvalues of the sampled graph from the Gram matrix of the sampled modes (Theorem
    "eigenvalues on the torus", parts (i) and (ii), deterministic assembly).** `S` symmetric with
    eigenvalues in `[0, 1]`; `X i f = √(a f) v i f` is the truncated kernel matrix factor.
    HYPOTHESES: `hrow`, the row sums of `S^(k+1) - X Xᵀ` are at most `eps` (kernel theorem,
    normalisation and the tail of the Fourier series); `hG`, the Gram matrix of the sampled modes
    is within `eta` of the identity; `hDj`, the `j`-th of the numbers `a_f` in decreasing order is
    `α^(k+1)`. Then `|s_j^(k+1) - α^(k+1)| ≤ eps + eps'` and
    `(k+1) α^(k+1) |s_j - α| ≤ 2 (eps + eps')` with `eps' = eta · s · ∑_g √(a g)`. -/
theorem eigtorus_from_gram {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    (S : Matrix n n ℝ) (hS : S.IsHermitian) (hnn : ∀ j, 0 ≤ hS.eigenvalues₀ j)
    (hle1 : ∀ j, hS.eigenvalues₀ j ≤ 1) (k : ℕ)
    (v : Matrix n F ℝ) (a : F → ℝ) (ha : ∀ f, 0 ≤ a f) {eta s eps α : ℝ}
    (heta : 0 ≤ eta) (hs0 : 0 ≤ s) (hs : ∀ f, Real.sqrt (a f) ≤ s)
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta)
    (hQ : ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ).IsHermitian)
    (h1 : (fromBlocks ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (hD : (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian)
    (hrow : ∀ i, ∑ l, |(S ^ (k + 1)) i l - ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ eps)
    (j : Fin (Fintype.card n)) (hj : j.val < Fintype.card (n ⊕ F))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hDj : hD.eigenvalues₀ ⟨j.val, hj⟩ = α ^ (k + 1))
    (h3 : 2 * (eps + eta * s * ∑ g, Real.sqrt (a g)) ≤ α ^ (k + 1)) :
    |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)| ≤ eps + eta * s * ∑ g, Real.sqrt (a g)
      ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
          ≤ 2 * (eps + eta * s * ∑ g, Real.sqrt (a g)) := by
  have hsp := finite_rank_kernel_spectrum v a ha heta hs0 hs hG hQ h1 hD j hj
  rw [hDj] at hsp
  exact eigtorus_matrix S _ hS hQ hnn hle1 k hrow j hα0 hα1 hsp h3

/-- `∑_{m=1}^{k} m^{-1/2} ≤ 2 √k`: the summation that turns the factor `m^{-1/2}` of the
    consistency lemma into the factor `√k` of the kernel theorem. -/
theorem sum_inv_sqrt_le (k : ℕ) :
    ∑ m ∈ Finset.range k, 1 / Real.sqrt ((m : ℝ) + 1) ≤ 2 * Real.sqrt k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hpos : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    have h1 : Real.sqrt ((k : ℝ) + 1) ^ 2 = k + 1 := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt hk
    have h3 : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have step : 1 / Real.sqrt ((k : ℝ) + 1)
        ≤ 2 * Real.sqrt ((k : ℝ) + 1) - 2 * Real.sqrt k := by
      rw [div_le_iff₀ hpos]
      nlinarith [Real.sqrt_nonneg (k : ℝ)]
    push_cast
    linarith

/-- A decreasing finite sequence takes the value `c` at position `j` if at most `j` of its
    values exceed `c` and more than `j` are at least `c`. -/
theorem antitone_value_of_counts {M : ℕ} (e : Fin M → ℝ) (he : Antitone e) (c : ℝ) (j : Fin M)
    (h1 : (Finset.univ.filter fun i => c < e i).card ≤ j.val)
    (h2 : j.val < (Finset.univ.filter fun i => c ≤ e i).card) : e j = c := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hsub : (Finset.univ.filter fun i => c ≤ e i) ⊆ Finset.Iio j := by
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_Iio]
      by_contra hij
      have := he (not_lt.mp hij)
      linarith [hi.2]
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega
  · have hsub : Finset.Iic j ⊆ (Finset.univ.filter fun i => c < e i) := by
      intro i hi
      rw [Finset.mem_Iic] at hi
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le h (he hi)⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega

/-- Counting eigenvalues with a property is counting roots of the characteristic polynomial. -/
theorem eig_count {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (p : ℝ → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i => p (hA.eigenvalues₀ i)).card = A.charpoly.roots.countP p := by
  rw [hA.roots_charpoly_eq_eigenvalues₀, Multiset.countP_map, Finset.card_def, Finset.filter_val]
  simp

/-- Roots of the characteristic polynomial of `diag(a)` padded with a zero block. -/
theorem roots_diag_pad {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    (a : F → ℝ) :
    (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).charpoly.roots
      = Multiset.replicate (Fintype.card n) (0 : ℝ) + Finset.univ.val.map a := by
  have hprod : (∏ i, (X - C (a i)) : ℝ[X])
      = ((Finset.univ.val.map a).map fun t => X - C t).prod := by
    rw [Multiset.map_map]; rfl
  rw [charpoly_fromBlocks_zero₁₂, charpoly_zero, charpoly_diagonal, Polynomial.roots_mul,
    roots_X_pow, hprod, Polynomial.roots_multiset_prod_X_sub_C]
  · simp [Multiset.nsmul_singleton]
  · refine mul_ne_zero (pow_ne_zero _ X_ne_zero) ?_
    exact (Polynomial.monic_prod_of_monic _ _ fun f _ => monic_X_sub_C (a f)).ne_zero

/-- **Position of a value among the coefficients in decreasing order (hypothesis `hDj` of
    `eigtorus_from_gram` from counting).** If at most `j` of the `a_f` exceed `c > 0` and more than
    `j` are at least `c`, the `j`-th of the `a_f`, padded with zeros, in decreasing order is `c`. -/
theorem diag_pad_eigenvalue {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    (a : F → ℝ) (hD : (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian)
    {c : ℝ} (hc : 0 < c) (j : Fin (Fintype.card (n ⊕ F)))
    (h1 : (Finset.univ.filter fun f => c < a f).card ≤ j.val)
    (h2 : j.val < (Finset.univ.filter fun f => c ≤ a f).card) :
    hD.eigenvalues₀ j = c := by
  have cnt : ∀ (p : ℝ → Prop) [DecidablePred p], ¬ p 0 →
      (Finset.univ.filter fun i => p (hD.eigenvalues₀ i)).card
        = (Finset.univ.filter fun f => p (a f)).card := by
    intro p _ hp0
    rw [eig_count _ hD p, roots_diag_pad, Multiset.countP_add, Multiset.countP_map]
    have : Multiset.countP p (Multiset.replicate (Fintype.card n) (0 : ℝ)) = 0 := by
      rw [Multiset.countP_eq_zero]
      intro x hx
      rw [Multiset.eq_of_mem_replicate hx]; exact hp0
    rw [this, zero_add, Finset.card_def, Finset.filter_val]
  refine antitone_value_of_counts _ hD.eigenvalues₀_antitone c j ?_ ?_
  · rw [cnt (fun t => c < t) (by simp; exact hc.le)]; exact h1
  · rw [cnt (fun t => c ≤ t) (by simp; exact hc)]; exact h2

/-- Powers of a conjugated matrix: if `S i l = r i * P i l / r l` with `r > 0`, then
    `(S^k) i l = r i * (P^k) i l / r l`. For the walk, `r = √(degree)`. -/
theorem conj_pow_entry {n : Type} [Fintype n] [DecidableEq n] (S P : Matrix n n ℝ) (r : n → ℝ)
    (hr : ∀ i, 0 < r i) (hSP : ∀ i l, S i l = r i * P i l / r l) (k : ℕ) (i l : n) :
    (S ^ k) i l = r i * (P ^ k) i l / r l := by
  induction k generalizing i l with
  | zero =>
    by_cases h : i = l
    · subst h; simp [(hr i).ne']
    · simp [Matrix.one_apply_ne h]
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ih, hSP]
    have := (hr j).ne'
    field_simp

/-- **Row sums for the eigenvalue theorem from the kernel bound (deterministic).** `N` points.
    If `S i l = ρ i l · P i l` with `|ρ i l - 1| ≤ θ` (normalisation), `|N P i l - g i l| ≤ D` (kernel
    theorem), `0 ≤ g i l ≤ mu` and `|g i l - N Q i l| ≤ t` (tail of the Fourier series), then every
    absolute row sum of `S - Q` is at most `θ (mu + D) + D + t`. -/
theorem row_sums_from_kernel {n : Type} [Fintype n] (S P Q g : Matrix n n ℝ) (ρ : n → n → ℝ)
    {N θ D mu t : ℝ} (hN : 0 < N) (hcard : (Fintype.card n : ℝ) = N) (hθ : 0 ≤ θ)
    (hS : ∀ i l, S i l = ρ i l * P i l) (hρ : ∀ i l, |ρ i l - 1| ≤ θ)
    (hP : ∀ i l, |N * P i l - g i l| ≤ D) (hg : ∀ i l, |g i l| ≤ mu)
    (hQ : ∀ i l, |g i l - N * Q i l| ≤ t) (i : n) :
    ∑ l, |S i l - Q i l| ≤ θ * (mu + D) + D + t := by
  have hterm : ∀ l, |S i l - Q i l| ≤ (θ * (mu + D) + D + t) / N := by
    intro l
    rw [le_div_iff₀ hN]
    have e : (S i l - Q i l) * N = (ρ i l - 1) * (N * P i l) + (N * P i l - g i l)
        + (g i l - N * Q i l) := by rw [hS]; ring
    have hNP : |N * P i l| ≤ mu + D := by
      have := abs_add_le (N * P i l - g i l) (g i l)
      rw [sub_add_cancel] at this
      linarith [hP i l, hg i l]
    calc |S i l - Q i l| * N = |(S i l - Q i l) * N| := by rw [abs_mul, abs_of_pos hN]
      _ ≤ |(ρ i l - 1) * (N * P i l)| + |N * P i l - g i l| + |g i l - N * Q i l| := by
        rw [e]; exact abs_add_three _ _ _
      _ ≤ θ * (mu + D) + D + t := by
        rw [abs_mul]
        have := mul_le_mul (hρ i l) hNP (abs_nonneg _) hθ
        linarith [hP i l, hQ i l]
  calc ∑ l, |S i l - Q i l| ≤ ∑ _l : n, (θ * (mu + D) + D + t) / N :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = θ * (mu + D) + D + t := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
        field_simp

/-! ### Pointwise Gaussian inequalities behind Lemma "facts on the periodised Gaussian" -/

/-- Core of (P1): for `0 < a ≤ t`, `e^{-v²/(2a)} ≤ e^{-v²/(2t)}`; with the prefactors,
    `γ_a ≤ (t/a)^{1/2} γ_t` in each coordinate. -/
theorem gauss_scale_mono {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) (v : ℝ) :
    Real.exp (-(v ^ 2) / (2 * a)) ≤ Real.exp (-(v ^ 2) / (2 * t)) := by
  apply Real.exp_le_exp.mpr
  have ht : 0 < t := lt_of_lt_of_le ha hat
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (_root_.sq_nonneg v) (by positivity) (by linarith)

/-- Core of (P3): `r e^{-r²/2} ≤ e^{-r²/4}` for `r ≥ 0`. -/
theorem gauss_gradient_core {r : ℝ} (hr : 0 ≤ r) :
    r * Real.exp (-(r ^ 2) / 2) ≤ Real.exp (-(r ^ 2) / 4) := by
  have h1 : r ≤ Real.exp (r ^ 2 / 4) := by
    have := Real.add_one_le_exp (r ^ 2 / 4)
    nlinarith [_root_.sq_nonneg (r / 2 - 1)]
  have h2 : Real.exp (-(r ^ 2) / 2) = Real.exp (-(r ^ 2) / 4) * Real.exp (-(r ^ 2) / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (r ^ 2 / 4) * Real.exp (-(r ^ 2) / 4) = 1 := by
    rw [← Real.exp_add]; simp [neg_div]
  have hpos := Real.exp_pos (-(r ^ 2) / 4)
  calc r * Real.exp (-(r ^ 2) / 2)
      = (r * Real.exp (-(r ^ 2) / 4)) * Real.exp (-(r ^ 2) / 4) := by rw [h2]; ring
    _ ≤ (Real.exp (r ^ 2 / 4) * Real.exp (-(r ^ 2) / 4)) * Real.exp (-(r ^ 2) / 4) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hpos.le) hpos.le
    _ = Real.exp (-(r ^ 2) / 4) := by rw [h3, one_mul]

/-- Core of (P4): for `a, t > 0`,
    `v²/(2a) + w²/(2t) ≥ v²/(4a) + (v + w)²/(2(t + 2a))`. -/
theorem gauss_product_core {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (v w : ℝ) :
    v ^ 2 / (4 * a) + (v + w) ^ 2 / (2 * (t + 2 * a)) ≤ v ^ 2 / (2 * a) + w ^ 2 / (2 * t) := by
  have key : (v + w) ^ 2 / (2 * (t + 2 * a)) ≤ v ^ 2 / (4 * a) + w ^ 2 / (2 * t) := by
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [_root_.sq_nonneg (2 * t * v - 4 * a * w), mul_pos ha ht]
  have e : v ^ 2 / (2 * a) = v ^ 2 / (4 * a) + v ^ 2 / (4 * a) := by field_simp; ring
  linarith

end Powers

/-- **Lemma "consistency", from the walk with the exact normalisation to the sampled walk, in a
    weak form.** One row of the sampled walk is `P_bj = Pt_j u_j / sum_l Pt_l u_l`, where `Pt_j`
    is the row of the walk with the exact normalisation and `u_j = 1/(1 + eps_j)`. If
    `|u_j - 1| ≤ 2 delta`, `|sum_j Pt_j - 1| ≤ delta`, `delta ≤ 1/8` and the main term satisfies
    `|sum_j Pt_j g_j - c| ≤ dev`, then the defect of the sampled walk satisfies
    `|sum_j P_bj g_j - c| ≤ 3 dev + 11 delta c`. In the paper `g_j = p_m(x_j - x_i)` and
    `c = p_{m+1}(x_b - x_i)`. The paper's lemma is sharper: its second term carries a factor
    `m^{-1/2}`, which comes from the Poincaré inequality for the Gaussian measure and is NOT
    obtained here. -/
theorem defect_decomposition {n : Type} [Fintype n] (Pt u g : n → ℝ) {c δ dev : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hPt : ∀ j, 0 ≤ Pt j) (hg : ∀ j, 0 ≤ g j) (hc : 0 ≤ c)
    (hu : ∀ j, |u j - 1| ≤ 2 * δ) (hrow : |∑ j, Pt j - 1| ≤ δ)
    (hdev : |∑ j, Pt j * g j - c| ≤ dev) :
    |(∑ j, Pt j * u j * g j) / (∑ j, Pt j * u j) - c| ≤ 3 * dev + 11 * δ * c := by
  have hdev0 : 0 ≤ dev := (abs_nonneg _).trans hdev
  set R := ∑ j, Pt j with hR
  set G := ∑ j, Pt j * g j with hG
  have hRb := abs_le.mp hrow
  have hGb := abs_le.mp hdev
  -- r from below
  have hr : (1 / 2 : ℝ) ≤ ∑ j, Pt j * u j := by
    have h1 : ∑ j, Pt j * (3 / 4) ≤ ∑ j, Pt j * u j := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hu j)).1]) (hPt j))
    rw [← Finset.sum_mul] at h1
    nlinarith
  have hrpos : 0 < ∑ j, Pt j * u j := by linarith
  -- numerator
  have e : ∑ j, Pt j * u j * g j - c * ∑ j, Pt j * u j
      = (G - c) - c * (R - 1) + ∑ j, Pt j * (u j - 1) * (g j - c) := by
    rw [hG, hR, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have : ∑ j, Pt j * (u j - 1) * (g j - c)
        = ∑ j, (Pt j * u j * g j - c * (Pt j * u j)) - ∑ j, Pt j * g j + c * ∑ j, Pt j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; ring
  have hthird : |∑ j, Pt j * (u j - 1) * (g j - c)| ≤ 2 * δ * (G + c * R) := by
    calc |∑ j, Pt j * (u j - 1) * (g j - c)| ≤ ∑ j, |Pt j * (u j - 1) * (g j - c)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, 2 * δ * (Pt j * g j + c * Pt j) := Finset.sum_le_sum (fun j _ => by
          rw [abs_mul, abs_mul, abs_of_nonneg (hPt j)]
          have h1 : |g j - c| ≤ g j + c := by
            rw [abs_le]; constructor <;> linarith [hg j]
          have h2 := hu j
          have h3 : |u j - 1| * |g j - c| ≤ 2 * δ * (g j + c) :=
            mul_le_mul h2 h1 (abs_nonneg _) (by linarith)
          calc Pt j * |u j - 1| * |g j - c| = Pt j * (|u j - 1| * |g j - c|) := by ring
            _ ≤ Pt j * (2 * δ * (g j + c)) := mul_le_mul_of_nonneg_left h3 (hPt j)
            _ = 2 * δ * (Pt j * g j + c * Pt j) := by ring)
      _ = 2 * δ * (G + c * R) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hnum : |∑ j, Pt j * u j * g j - c * ∑ j, Pt j * u j| ≤ (3 / 2) * dev + (11 / 2) * δ * c := by
    rw [e]
    have h3 := abs_le.mp hthird
    have hGle : G ≤ c + dev := by linarith [hGb.2]
    have hRle : R ≤ 1 + δ := by linarith [hRb.2]
    have hb : 2 * δ * (G + c * R) ≤ 2 * δ * (c + dev + c * (1 + δ)) := by
      have : G + c * R ≤ c + dev + c * (1 + δ) := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by linarith)
    have hcR : |c * (R - 1)| ≤ c * δ := by
      rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hrow hc
    have hcR' := abs_le.mp hcR
    rw [abs_le]
    constructor <;> nlinarith [hGb.1, hGb.2, h3.1, h3.2, hcR'.1, hcR'.2, mul_nonneg hδ0 hdev0,
      mul_nonneg hδ0 hc, mul_nonneg (mul_nonneg hδ0 hδ0) hc]
  have e2 : (∑ j, Pt j * u j * g j) / (∑ j, Pt j * u j) - c
      = (∑ j, Pt j * u j * g j - c * ∑ j, Pt j * u j) / (∑ j, Pt j * u j) := by
    field_simp
  rw [e2, abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
  have : (3 / 2) * dev + (11 / 2) * δ * c ≤ (3 * dev + 11 * δ * c) * (1 / 2) := by ring_nf; linarith
  calc |∑ j, Pt j * u j * g j - c * ∑ j, Pt j * u j| ≤ (3 / 2) * dev + (11 / 2) * δ * c := hnum
    _ ≤ (3 * dev + 11 * δ * c) * (1 / 2) := this
    _ ≤ (3 * dev + 11 * δ * c) * ∑ j, Pt j * u j :=
        mul_le_mul_of_nonneg_left hr (by positivity)

/-- **The kernel theorem for the sampled walk, deterministic assembly.** Index set `n` with `N`
    elements (the sample points); `pk m b i` stands for `p^{*m}(x_b - x_i)`, `m ≥ 1`, with
    `0 ≤ pk m ≤ mu m`; `rho_b = (1/N) sum_l pk 1 b l` is the estimated normalisation relative to
    the true one, and the sampled walk is `P_bj = (pk 1 b j / rho_j) / sum_l (pk 1 b l / rho_l)`.
    HYPOTHESES: `|rho_b - 1| ≤ delta ≤ 1/8` (normalisation errors) and the consistency of the walk
    with the EXACT normalisation, `|(1/N) sum_j pk 1 b j * pk m j i - pk (m+1) b i| ≤ dev m`.
    CONCLUSION: for all `k` and all entries,
    `|N (P^{k+1})_{ai} - pk (k+1) a i| ≤ 10 delta (pk (k+1) a i + E_k) + E_k` with
    `E_k = sum_{m ≤ k} (3 dev m + 11 delta mu (m+1))`. This is the unweighted form: it gives no
    factor `sqrt k`, and it is the form available with the weak consistency bound. -/
theorem kernel_fixed_scale_det {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (pk : ℕ → n → n → ℝ) (mu dev : ℕ → ℝ) (rho : n → ℝ) (P : Matrix n n ℝ) {delta : ℝ}
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 8)
    (hp0 : ∀ m b i, 0 ≤ pk m b i) (hpmu : ∀ m b i, pk m b i ≤ mu m)
    (hrho : ∀ b, (Fintype.card n : ℝ) * rho b = ∑ l, pk 1 b l)
    (hrho1 : ∀ b, |rho b - 1| ≤ delta)
    (hP : ∀ b j, P b j = (pk 1 b j / rho j) / ∑ l, pk 1 b l / rho l)
    (k : ℕ)
    (hcons : ∀ m b i, 1 ≤ m → m ≤ k →
      |∑ j, pk 1 b j / (Fintype.card n : ℝ) * pk m j i - pk (m + 1) b i| ≤ dev m)
    (a i : n) :
    |(Fintype.card n : ℝ) * (P ^ (k + 1)) a i - pk (k + 1) a i|
      ≤ 10 * delta * (pk (k + 1) a i
          + ∑ m ∈ Finset.range k, (3 * dev (m + 1) + 11 * delta * mu (m + 2)))
        + ∑ m ∈ Finset.range k, (3 * dev (m + 1) + 11 * delta * mu (m + 2)) := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hrpos : ∀ b, 0 < rho b := fun b => by linarith [(abs_le.mp (hrho1 b)).1]
  -- the exact-normalisation row and the factors u
  set Pt : n → n → ℝ := fun b j => pk 1 b j / (Fintype.card n : ℝ) with hPt
  set u : n → ℝ := fun j => 1 / rho j with hu
  have hu1 : ∀ j, |u j - 1| ≤ 2 * delta := by
    intro j
    have h1 := abs_le.mp (hrho1 j)
    have hr := hrpos j
    have e : u j - 1 = (1 - rho j) / rho j := by rw [hu]; field_simp
    rw [e, abs_div, abs_of_pos hr, div_le_iff₀ hr]
    have : |1 - rho j| ≤ delta := by rw [abs_sub_comm]; exact hrho1 j
    nlinarith [this]
  have hPtrow : ∀ b, |∑ j, Pt b j - 1| ≤ delta := by
    intro b
    have e : ∑ j, Pt b j = rho b := by
      rw [hPt]; simp only; rw [← Finset.sum_div, ← hrho b]; field_simp
    rw [e]; exact hrho1 b
  have hPtu : ∀ b j, pk 1 b j / rho j = (Fintype.card n : ℝ) * (Pt b j * u j) := by
    intro b j; rw [hPt, hu]; field_simp
  have hden : ∀ b, ∑ l, pk 1 b l / rho l = (Fintype.card n : ℝ) * ∑ l, Pt b l * u l := by
    intro b; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun l _ => hPtu b l)
  have hsumpos : ∀ b, 0 < ∑ l, Pt b l * u l := by
    intro b
    have h1 : ∑ l, Pt b l * (3 / 4) ≤ ∑ l, Pt b l * u l := Finset.sum_le_sum (fun l _ =>
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hu1 l)).1])
        (div_nonneg (hp0 1 b l) hN.le))
    rw [← Finset.sum_mul] at h1
    have h2 := (abs_le.mp (hPtrow b)).1
    nlinarith
  have hPform : ∀ b j, P b j = Pt b j * u j / ∑ l, Pt b l * u l := by
    intro b j
    rw [hP b j, hPtu b j, hden b]
    have := (hsumpos b).ne'; have := hN.ne'
    field_simp
  have hP0 : ∀ b j, 0 ≤ P b j := by
    intro b j
    rw [hPform b j]
    exact div_nonneg (mul_nonneg (div_nonneg (hp0 1 b j) hN.le)
      (by rw [hu]; exact (one_div_pos.mpr (hrpos j)).le)) (hsumpos b).le
  have hProw : ∀ b, ∑ j, P b j = 1 := by
    intro b
    simp_rw [hPform b]
    rw [← Finset.sum_div]
    exact div_self (hsumpos b).ne'
  -- consistency of the sampled walk
  have hdefect : ∀ m, m < k → ∀ b,
      |(P *ᵥ (fun b' => pk (m + 1) b' i) - fun b' => pk (m + 2) b' i) b|
        ≤ 3 * dev (m + 1) + 11 * delta * mu (m + 2) := by
    intro m hmk b
    have hdd := defect_decomposition (Pt b) u (fun j => pk (m + 1) j i) (c := pk (m + 2) b i)
      hd0 hd (fun j => div_nonneg (hp0 1 b j) hN.le) (fun j => hp0 (m + 1) j i) (hp0 (m + 2) b i)
      hu1 (hPtrow b) (hcons (m + 1) b i (by omega) (by omega))
    have e : (P *ᵥ (fun b' => pk (m + 1) b' i)) b
        = (∑ j, Pt b j * u j * pk (m + 1) j i) / ∑ j, Pt b j * u j := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun j _ => by rw [hPform b j]; ring)
    have hb : 11 * delta * pk (m + 2) b i ≤ 11 * delta * mu (m + 2) :=
      mul_le_mul_of_nonneg_left (hpmu (m + 2) b i) (by linarith)
    simp only [Pi.sub_apply]
    rw [e]
    linarith
  -- the last step of the walk
  have hlast : ∀ b, |(Fintype.card n : ℝ) * P b i - pk 1 b i| ≤ 10 * delta * pk 1 b i := by
    intro b
    have hS := hsumpos b
    have e : (Fintype.card n : ℝ) * P b i - pk 1 b i
        = pk 1 b i * (u i / (∑ l, Pt b l * u l) - 1) := by
      rw [hPform b i, hPt]; field_simp
    rw [e, abs_mul, abs_of_nonneg (hp0 1 b i), mul_comm (10 * delta)]
    refine mul_le_mul_of_nonneg_left ?_ (hp0 1 b i)
    -- bounds for u_i and for the sum
    have hui := abs_le.mp (hu1 i)
    have hrow := abs_le.mp (hPtrow b)
    have hlo : ∑ l, Pt b l * (1 - 2 * delta) ≤ ∑ l, Pt b l * u l := Finset.sum_le_sum (fun l _ =>
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hu1 l)).1])
        (div_nonneg (hp0 1 b l) hN.le))
    have hhi : ∑ l, Pt b l * u l ≤ ∑ l, Pt b l * (1 + 2 * delta) := Finset.sum_le_sum (fun l _ =>
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hu1 l)).2])
        (div_nonneg (hp0 1 b l) hN.le))
    rw [← Finset.sum_mul] at hlo hhi
    have e2 : u i / (∑ l, Pt b l * u l) - 1 = (u i - ∑ l, Pt b l * u l) / ∑ l, Pt b l * u l := by
      field_simp
    have hR1 : (1 - delta) * (1 - 2 * delta) ≤ (∑ l, Pt b l) * (1 - 2 * delta) :=
      mul_le_mul_of_nonneg_right (by linarith [hrow.1]) (by linarith)
    have hR2 : (∑ l, Pt b l) * (1 + 2 * delta) ≤ (1 + delta) * (1 + 2 * delta) :=
      mul_le_mul_of_nonneg_right (by linarith [hrow.2]) (by linarith)
    have hdd : delta * delta ≤ delta / 8 := by nlinarith
    have hSlo : 1 - 3 * delta ≤ ∑ l, Pt b l * u l := by nlinarith
    have hShi : ∑ l, Pt b l * u l ≤ 1 + 3 * delta + delta / 4 := by nlinarith
    have hdS : delta * (5 / 8) ≤ delta * ∑ l, Pt b l * u l :=
      mul_le_mul_of_nonneg_left (by linarith) hd0
    rw [e2, abs_div, abs_of_pos hS, div_le_iff₀ hS, abs_le]
    constructor <;> linarith [hui.1, hui.2]
  have key := kernel_theorem_conditional P hP0 hProw (fun m b' => pk m b' i)
    (fun b => (Fintype.card n : ℝ) * P b i) (theta := 10 * delta) (by linarith) hlast
    (fun m => 3 * dev m + 11 * delta * mu (m + 1)) k
    (fun m hm b => by simpa using hdefect m hm b) a
  have e3 : ((P ^ k) *ᵥ fun b => (Fintype.card n : ℝ) * P b i) a
      = (Fintype.card n : ℝ) * (P ^ (k + 1)) a i := by
    have hpow : (P ^ (k + 1)) a i = ∑ b, (P ^ k) a b * P b i := by
      rw [pow_succ, Matrix.mul_apply]
    rw [hpow, Finset.mul_sum]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  rw [e3] at key
  simpa using key

end Spectral


/-! ### Concentration of the normalisation (first step of Lemma "weights")

  With the probability theory of Mathlib. `Y j` stands for `k(x, X_j)` at a FIXED point `x`, with
  mean `m = q(x)`. Not formalised: the same statement at the sample points themselves (which needs
  conditioning on `X_i`), the union over the points, and everything after it. -/

section Probability
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Hoeffding's inequality for the normalisation: for independent random variables `Y j` with
    values in `[0, A]` and common mean `m`, the probability that `sum_{j<N} Y j - N m ≥ eps` is at
    most `exp(-eps^2 / (2 N (A/2)^2))`. With `eps = N s`: `P(q_N - q ≥ s) ≤ exp(-2 N s^2 / A^2)`. -/
theorem normalisation_concentration {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (h_indep : iIndepFun Y μ)
    (hm : ∀ j, AEMeasurable (Y j) μ) {A m : ℝ} (hA : 0 ≤ A)
    (hb : ∀ j, ∀ᵐ ω ∂μ, Y j ω ∈ Set.Icc 0 A) (hmean : ∀ j, μ[Y j] = m)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ j ∈ Finset.range N, Y j ω - N * m}
      ≤ Real.exp (-ε ^ 2 / (2 * N * (A / 2) ^ 2)) := by
  have hZ : iIndepFun (fun j ω => Y j ω - m) μ :=
    h_indep.comp (fun _ x => x - m) (fun _ => measurable_id.sub_const m)
  have hsub : ∀ j < N, HasSubgaussianMGF (fun ω => Y j ω - m) ((‖A - 0‖₊ / 2) ^ 2) μ := by
    intro j _
    have h := hasSubgaussianMGF_of_mem_Icc (hm j) (hb j)
    rwa [hmean j] at h
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun hZ hsub hε
  have hset : {ω | ε ≤ ∑ j ∈ Finset.range N, (Y j ω - m)}
      = {ω | ε ≤ ∑ j ∈ Finset.range N, Y j ω - N * m} := by
    ext ω; simp [Finset.sum_sub_distrib]
  rw [hset] at h
  have hc : (((‖A - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (A / 2) ^ 2 := by
    simp [abs_of_nonneg hA]
  rwa [hc] at h

/-- Two-sided form: `P(|sum_{j<N} Y j - N m| ≥ eps) ≤ 2 exp(-eps^2 / (2 N (A/2)^2))`. -/
theorem normalisation_two_sided {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (h_indep : iIndepFun Y μ)
    (hm : ∀ j, AEMeasurable (Y j) μ) {A m : ℝ} (hA : 0 ≤ A)
    (hb : ∀ j, ∀ᵐ ω ∂μ, Y j ω ∈ Set.Icc 0 A) (hmean : ∀ j, μ[Y j] = m)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, Y j ω - N * m|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * N * (A / 2) ^ 2)) := by
  have h1 := normalisation_concentration Y h_indep hm hA hb hmean N hε
  have hZ : iIndepFun (fun j ω => A - Y j ω) μ :=
    h_indep.comp (fun _ x => A - x) (fun _ => measurable_const.sub measurable_id)
  have hm' : ∀ j, AEMeasurable (fun ω => A - Y j ω) μ := fun j => (hm j).const_sub A
  have hb' : ∀ j, ∀ᵐ ω ∂μ, A - Y j ω ∈ Set.Icc 0 A := fun j => by
    filter_upwards [hb j] with ω h
    exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hint : ∀ j, Integrable (Y j) μ := fun j => Integrable.of_mem_Icc 0 A (hm j) (hb j)
  have hmean' : ∀ j, μ[fun ω => A - Y j ω] = A - m := fun j => by
    rw [integral_sub (integrable_const A) (hint j), hmean j]; simp
  have h2 := normalisation_concentration (fun j ω => A - Y j ω) hZ hm' hA hb' hmean' N hε
  have hsub : {ω | ε ≤ |∑ j ∈ Finset.range N, Y j ω - N * m|}
      ⊆ {ω | ε ≤ ∑ j ∈ Finset.range N, Y j ω - N * m}
        ∪ {ω | ε ≤ ∑ j ∈ Finset.range N, (A - Y j ω) - N * (A - m)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have e : ∑ j ∈ Finset.range N, (A - Y j ω) - N * (A - m)
        = -(∑ j ∈ Finset.range N, Y j ω - N * m) := by
      rw [Finset.sum_sub_distrib]; simp; ring
    rw [e]
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, Y j ω - N * m|}
      ≤ μ.real ({ω | ε ≤ ∑ j ∈ Finset.range N, Y j ω - N * m}
        ∪ {ω | ε ≤ ∑ j ∈ Finset.range N, (A - Y j ω) - N * (A - m)}) := measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

/-- Union bound over a finite set of points (a net): the two-sided estimate holds simultaneously
    for all `a ∈ s` except on an event of probability at most `|s|` times the single bound. -/
theorem net_concentration {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) (Y : ι → ℕ → Ω → ℝ)
    (h_indep : ∀ a ∈ s, iIndepFun (Y a) μ) (hm : ∀ a ∈ s, ∀ j, AEMeasurable (Y a j) μ)
    {A : ℝ} (m : ι → ℝ) (hA : 0 ≤ A)
    (hb : ∀ a ∈ s, ∀ j, ∀ᵐ ω ∂μ, Y a j ω ∈ Set.Icc 0 A) (hmean : ∀ a ∈ s, ∀ j, μ[Y a j] = m a)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ a ∈ s, ε ≤ |∑ j ∈ Finset.range N, Y a j ω - N * m a|}
      ≤ s.card * (2 * Real.exp (-ε ^ 2 / (2 * N * (A / 2) ^ 2))) := by
  have hset : {ω | ∃ a ∈ s, ε ≤ |∑ j ∈ Finset.range N, Y a j ω - N * m a|}
      = ⋃ a ∈ s, {ω | ε ≤ |∑ j ∈ Finset.range N, Y a j ω - N * m a|} := by
    ext ω; simp
  rw [hset]
  calc μ.real (⋃ a ∈ s, {ω | ε ≤ |∑ j ∈ Finset.range N, Y a j ω - N * m a|})
      ≤ ∑ a ∈ s, μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, Y a j ω - N * m a|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ s, 2 * Real.exp (-ε ^ 2 / (2 * N * (A / 2) ^ 2)) :=
        Finset.sum_le_sum (fun a ha =>
          normalisation_two_sided (Y a) (h_indep a ha) (hm a ha) hA (hb a ha) (hmean a ha) N hε)
    _ = _ := by simp

/-- From a net to all points: if two `L`-Lipschitz functions are within `s` of each other on an
    `r`-net, they are within `s + 2 L r` everywhere. -/
theorem sup_from_net {E : Type*} [PseudoMetricSpace E] (f g : E → ℝ) {L r s : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * dist x y) (hg : ∀ x y, |g x - g y| ≤ L * dist x y)
    (net : Finset E) (hnet : ∀ x, ∃ a ∈ net, dist x a ≤ r)
    (hs : ∀ a ∈ net, |f a - g a| ≤ s) (x : E) : |f x - g x| ≤ s + 2 * L * r := by
  obtain ⟨a, ha, hd⟩ := hnet x
  have h1 := hf x a
  have h2 := hg x a
  have h3 := hs a ha
  have h4 : L * dist x a ≤ L * r := mul_le_mul_of_nonneg_left hd hL
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- **Uniform concentration of the normalisation (Lemma "weights", Proposition "rate in N",
    Step 1).** `X j` independent random points of a metric space `E`; `k` a kernel with values in
    `[0, A]`, measurable in the second and `L`-Lipschitz in the first argument;
    `q x = E k(x, X_j)` for every `j` (HYPOTHESIS `hq`: this is where identical distribution
    enters), `q` being `L`-Lipschitz (HYPOTHESIS `hqlip`, a consequence not derived here); a finite
    `r`-net of `E` (HYPOTHESIS `hnet`: its existence and size are geometry). Conclusion: the
    probability that `|sum_{j<N} k(x, X_j) - N q(x)|` exceeds `eps + 2 N L r` for SOME point `x`,
    in particular for some sample point, is at most `2 |net| exp(-eps^2 / (2 N (A/2)^2))`. No
    conditioning is needed, because the estimate is uniform in `x`. -/
theorem uniform_normalisation {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (k : E → E → ℝ) (hk : ∀ x, Measurable (k x)) {A L r : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hbound : ∀ x y, k x y ∈ Set.Icc 0 A)
    (hlip : ∀ x x' y, |k x y - k x' y| ≤ L * dist x x')
    (q : E → ℝ) (hq : ∀ x j, μ[fun ω => k x (X j ω)] = q x)
    (hqlip : ∀ x x', |q x - q x'| ≤ L * dist x x')
    (net : Finset E) (hnet : ∀ x, ∃ a ∈ net, dist x a ≤ r)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ x, ε + 2 * (N * L) * r < |∑ j ∈ Finset.range N, k x (X j ω) - N * q x|}
      ≤ net.card * (2 * Real.exp (-ε ^ 2 / (2 * N * (A / 2) ^ 2))) := by
  have hnetbound := net_concentration (μ := μ) net (fun a j ω => k a (X j ω))
    (fun a _ => h_indep.comp (fun _ y => k a y) (fun _ => hk a))
    (fun a _ j => ((hk a).comp (hX j)).aemeasurable) q hA
    (fun a _ j => Filter.Eventually.of_forall (fun ω => hbound a (X j ω)))
    (fun a _ j => hq a j) N hε
  refine (measureReal_mono ?_).trans hnetbound
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hω
  have hNL : 0 ≤ (N : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  have hf : ∀ x y : E, |∑ j ∈ Finset.range N, k x (X j ω) - ∑ j ∈ Finset.range N, k y (X j ω)|
      ≤ (N * L) * dist x y := by
    intro x y
    rw [← Finset.sum_sub_distrib]
    calc |∑ j ∈ Finset.range N, (k x (X j ω) - k y (X j ω))|
        ≤ ∑ j ∈ Finset.range N, |k x (X j ω) - k y (X j ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range N, L * dist x y := Finset.sum_le_sum (fun j _ => hlip x y (X j ω))
      _ = (N * L) * dist x y := by simp; ring
  have hg : ∀ x y : E, |(N : ℝ) * q x - N * q y| ≤ (N * L) * dist x y := by
    intro x y
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hqlip x y) (Nat.cast_nonneg N)
  have := sup_from_net (fun x => ∑ j ∈ Finset.range N, k x (X j ω)) (fun x => (N : ℝ) * q x)
    hNL hf hg net hnet (fun a ha => (hcon a ha).le) x
  linarith

/-- The same uniform concentration for a family of functions indexed by a metric parameter space
    `T` (for the transported kernel `T = G × G` with the parameter `(x, y)`): `k t` has values in
    `[0, A]` and is `L`-Lipschitz in `t`; `q t = E k(t, X_j)` is `L`-Lipschitz; a finite `r`-net of
    `T`. Then the probability that `|sum_{j<N} k(t, X_j) - N q(t)|` exceeds `eps + 2 N L r` for
    some `t` is at most `2 |net| exp(-eps^2 / (2 N (A/2)^2))`. -/
theorem uniform_concentration_param {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T : Type*} [PseudoMetricSpace T] {E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (k : T → E → ℝ) (hk : ∀ x, Measurable (k x)) {A L r : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hbound : ∀ x y, k x y ∈ Set.Icc 0 A)
    (hlip : ∀ x x' y, |k x y - k x' y| ≤ L * dist x x')
    (q : T → ℝ) (hq : ∀ x j, μ[fun ω => k x (X j ω)] = q x)
    (hqlip : ∀ x x', |q x - q x'| ≤ L * dist x x')
    (net : Finset T) (hnet : ∀ x, ∃ a ∈ net, dist x a ≤ r)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ x, ε + 2 * (N * L) * r < |∑ j ∈ Finset.range N, k x (X j ω) - N * q x|}
      ≤ net.card * (2 * Real.exp (-ε ^ 2 / (2 * N * (A / 2) ^ 2))) := by
  have hnetbound := net_concentration (μ := μ) net (fun a j ω => k a (X j ω))
    (fun a _ => h_indep.comp (fun _ y => k a y) (fun _ => hk a))
    (fun a _ j => ((hk a).comp (hX j)).aemeasurable) q hA
    (fun a _ j => Filter.Eventually.of_forall (fun ω => hbound a (X j ω)))
    (fun a _ j => hq a j) N hε
  refine (measureReal_mono ?_).trans hnetbound
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hω
  have hNL : 0 ≤ (N : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  have hf : ∀ x y : T, |∑ j ∈ Finset.range N, k x (X j ω) - ∑ j ∈ Finset.range N, k y (X j ω)|
      ≤ (N * L) * dist x y := by
    intro x y
    rw [← Finset.sum_sub_distrib]
    calc |∑ j ∈ Finset.range N, (k x (X j ω) - k y (X j ω))|
        ≤ ∑ j ∈ Finset.range N, |k x (X j ω) - k y (X j ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range N, L * dist x y := Finset.sum_le_sum (fun j _ => hlip x y (X j ω))
      _ = (N * L) * dist x y := by simp; ring
  have hg : ∀ x y : T, |(N : ℝ) * q x - N * q y| ≤ (N * L) * dist x y := by
    intro x y
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hqlip x y) (Nat.cast_nonneg N)
  have := sup_from_net (fun x => ∑ j ∈ Finset.range N, k x (X j ω)) (fun x => (N : ℝ) * q x)
    hNL hf hg net hnet (fun a ha => (hcon a ha).le) x
  linarith

/-- **Lemma "traces" with its probability, for a constant normalisation.** Independent points `X j`
    of a metric space; a kernel with values in `[0, A]`, measurable in the second and
    `L`-Lipschitz in the first argument; `E k(x, X_j) = q0 > 0` for every point `x` and every `j`
    (HYPOTHESIS `hq`: identical distribution and a normalisation that does not depend on the
    point, as on a torus with a translation-invariant kernel); a finite `r`-net (HYPOTHESIS
    `hnet`); `s + 2 L r ≤ q0/2`. Then, for the walk matrix `P` built from the first `N` points,
    the probability that `Tr P ≤ 6A/q0` and `Tr P^2 ≤ 6A/q0` FAIL is at most
    `2 |net| exp(-(N s)^2 / (2 N (A/2)^2)) = 2 |net| exp(-2 N s^2/A^2)`. -/
theorem traces_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (k : E → E → ℝ) (hk : ∀ x, Measurable (k x)) {A L r q0 s : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hbound : ∀ x y, k x y ∈ Set.Icc 0 A)
    (hlip : ∀ x x' y, |k x y - k x' y| ≤ L * dist x x')
    (hq : ∀ x j, μ[fun ω => k x (X j ω)] = q0) (hq0 : 0 < q0)
    (net : Finset E) (hnet : ∀ x, ∃ a ∈ net, dist x a ≤ r)
    (N : ℕ) [NeZero N] (hs : 0 ≤ s) (hsmall : s + 2 * L * r ≤ q0 / 2) :
    μ.real {ω | ¬ ((walkMatrix (fun i j : Fin N => k (X i ω) (X j ω))
            (fun i : Fin N => (∑ l : Fin N, k (X i ω) (X l ω)) / N)).trace ≤ 6 * A / q0
        ∧ (walkMatrix (fun i j : Fin N => k (X i ω) (X j ω))
            (fun i : Fin N => (∑ l : Fin N, k (X i ω) (X l ω)) / N)
          * walkMatrix (fun i j : Fin N => k (X i ω) (X j ω))
            (fun i : Fin N => (∑ l : Fin N, k (X i ω) (X l ω)) / N)).trace ≤ 6 * A / q0)}
      ≤ net.card * (2 * Real.exp (-(N * s) ^ 2 / (2 * N * (A / 2) ^ 2))) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hu := uniform_normalisation (μ := μ) X h_indep hX k hk hA hL hbound hlip (fun _ => q0)
    hq (fun x x' => by simpa using mul_nonneg hL dist_nonneg) net hnet N
    (mul_nonneg hNpos.le hs)
  refine (measureReal_mono ?_).trans hu
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  apply hω
  have hsum : ∀ i : Fin N, ∑ l : Fin N, k (X i ω) (X l ω)
      = ∑ j ∈ Finset.range N, k (X i ω) (X j ω) := fun i =>
    Fin.sum_univ_eq_sum_range (fun j => k (X i ω) (X j ω)) N
  have hbd : ∀ i : Fin N, |∑ l : Fin N, k (X i ω) (X l ω) - N * q0| ≤ N * (q0 / 2) := by
    intro i
    rw [hsum i]
    have h1 := hcon (X i ω)
    have h2 : (N : ℝ) * s + 2 * (N * L) * r = N * (s + 2 * L * r) := by ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left hsmall hNpos.le)
  refine traces_of_normalisation (fun i j : Fin N => k (X i ω) (X j ω))
    (fun i : Fin N => (∑ l : Fin N, k (X i ω) (X l ω)) / N)
    (fun i j => (hbound _ _).1) (fun i j => (hbound _ _).2) ?_ hq0 ?_ ?_
  · intro i
    simp only [Fintype.card_fin]
    field_simp
  · intro i
    have h := (abs_le.mp (hbd i)).1
    rw [le_div_iff₀ hNpos]; nlinarith
  · intro i
    have h := (abs_le.mp (hbd i)).2
    rw [div_le_iff₀ hNpos]; nlinarith

/-- **The trace bounds on a torus, with their probability.** `G` a compact abelian group with a
    translation-invariant metric (for instance a flat torus), `ν` its invariant probability
    measure, `X j` independent with law `ν`, and the kernel `k(x, y) = h(x - y)` with `h`
    measurable, with values in `[0, A]` and `L`-Lipschitz, `q0 = ∫ h dν > 0`. For every `r > 0`
    there is a number `M` (the size of an `r`-net of `G`; it is not quantified here) such that for
    all `N ≥ 1` and all `s ≥ 0` with `s + 2 L r ≤ q0/2` the probability that `Tr P ≤ 6A/q0` and
    `Tr P^2 ≤ 6A/q0` FAIL for the walk matrix of the first `N` points is at most
    `2 M exp(-(N s)^2 / (2 N (A/2)^2))`. No hypothesis on the normalisation or on a net remains. -/
theorem torus_traces_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [MetricSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν)
    (h : G → ℝ) (hh : Measurable h) {A L r : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hbound : ∀ u, h u ∈ Set.Icc 0 A) (hlip : ∀ u u', |h u - h u'| ≤ L * dist u u')
    (hq0 : 0 < ∫ u, h u ∂ν) (hr : 0 < r) :
    ∃ M : ℕ, ∀ (N : ℕ) [NeZero N] (s : ℝ), 0 ≤ s → s + 2 * L * r ≤ (∫ u, h u ∂ν) / 2 →
      μ.real {ω | ¬ ((walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)).trace
                ≤ 6 * A / (∫ u, h u ∂ν)
          ∧ (walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)
            * walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)).trace
                ≤ 6 * A / (∫ u, h u ∂ν))}
        ≤ M * (2 * Real.exp (-(N * s) ^ 2 / (2 * N * (A / 2) ^ 2))) := by
  -- a finite r-net from compactness
  obtain ⟨t, -, htfin, htcover⟩ := finite_cover_balls_of_compact (isCompact_univ (X := G)) hr
  have hnet : ∀ x : G, ∃ a ∈ htfin.toFinset, dist x a ≤ r := by
    intro x
    have hx := htcover (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨a, ha, hd⟩ := hx
    exact ⟨a, htfin.mem_toFinset.mpr ha, hd.le⟩
  -- the normalisation does not depend on the point
  have hq : ∀ (x : G) (j : ℕ), μ[fun ω => h (x - X j ω)] = ∫ u, h u ∂ν := by
    intro x j
    have h1 : ∫ ω, h (x - X j ω) ∂μ = ∫ y, h (x - y) ∂(μ.map (X j)) :=
      (integral_map (hX j).aemeasurable
        ((hh.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).symm
    rw [h1, hlaw j]
    exact integral_sub_left_eq_self h ν x
  refine ⟨htfin.toFinset.card, fun N _ s hs hsmall => ?_⟩
  exact traces_whp (μ := μ) X h_indep hX (fun x y => h (x - y))
    (fun x => hh.comp (measurable_const.sub measurable_id)) hA hL
    (fun x y => hbound (x - y))
    (fun x x' y => by rw [← hdist x x' y]; exact hlip (x - y) (x' - y))
    hq hq0 htfin.toFinset hnet N hs hsmall

/-- The same on the circle `ℝ/ℤ` with its Haar probability measure: all hypotheses on the space
    are discharged (compactness, invariance of the metric and of the measure). This shows in
    particular that the hypotheses of `torus_traces_whp` can be satisfied. -/
theorem circle_traces_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → UnitAddCircle) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = AddCircle.haarAddCircle)
    (h : UnitAddCircle → ℝ) (hh : Measurable h) {A L r : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hbound : ∀ u, h u ∈ Set.Icc 0 A) (hlip : ∀ u u', |h u - h u'| ≤ L * dist u u')
    (hq0 : 0 < ∫ u, h u ∂AddCircle.haarAddCircle) (hr : 0 < r) :
    ∃ M : ℕ, ∀ (N : ℕ) [NeZero N] (s : ℝ), 0 ≤ s →
      s + 2 * L * r ≤ (∫ u, h u ∂AddCircle.haarAddCircle) / 2 →
      μ.real {ω | ¬ ((walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)).trace
                ≤ 6 * A / (∫ u, h u ∂AddCircle.haarAddCircle)
          ∧ (walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)
            * walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)).trace
                ≤ 6 * A / (∫ u, h u ∂AddCircle.haarAddCircle))}
        ≤ M * (2 * Real.exp (-(N * s) ^ 2 / (2 * N * (A / 2) ^ 2))) :=
  torus_traces_whp (μ := μ) (G := UnitAddCircle) AddCircle.haarAddCircle
    (fun x x' y => dist_sub_right x x' y) X h_indep hX hlaw h hh hA hL hbound hlip hq0 hr

/-- The flat torus of dimension `d`, `(ℝ/ℤ)^d`, and its invariant probability measure. -/
abbrev FlatTorus (d : ℕ) := Fin d → UnitAddCircle

noncomputable abbrev flatTorusMeasure (d : ℕ) : Measure (FlatTorus d) :=
  Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))

/-- **The trace bounds on the flat torus of dimension `d`, with their probability.** As
    `torus_traces_whp`, for `(ℝ/ℤ)^d` with the product of the Haar measures; all hypotheses on the
    space are discharged. The metric is the supremum metric of the coordinates. -/
theorem flatTorus_traces_whp (d : ℕ) {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (h : FlatTorus d → ℝ) (hh : Measurable h) {A L r : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hbound : ∀ u, h u ∈ Set.Icc 0 A) (hlip : ∀ u u', |h u - h u'| ≤ L * dist u u')
    (hq0 : 0 < ∫ u, h u ∂flatTorusMeasure d) (hr : 0 < r) :
    ∃ M : ℕ, ∀ (N : ℕ) [NeZero N] (s : ℝ), 0 ≤ s →
      s + 2 * L * r ≤ (∫ u, h u ∂flatTorusMeasure d) / 2 →
      μ.real {ω | ¬ ((walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)).trace
                ≤ 6 * A / (∫ u, h u ∂flatTorusMeasure d)
          ∧ (walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)
            * walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)).trace
                ≤ 6 * A / (∫ u, h u ∂flatTorusMeasure d))}
        ≤ M * (2 * Real.exp (-(N * s) ^ 2 / (2 * N * (A / 2) ^ 2))) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  exact torus_traces_whp (μ := μ) (G := FlatTorus d) (flatTorusMeasure d)
    (fun x x' y => dist_sub_right x x' y) X h_indep hX hlaw h hh hA hL hbound hlip hq0 hr

/-- Borel–Cantelli for exponentially small probabilities: if `P(B_N) ≤ C e^{-c N}` with `c > 0`,
    then almost surely `B_N` occurs for only finitely many `N`. -/
theorem ae_eventually_of_exp_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hB : ∀ N, μ.real (B N) ≤ C * Real.exp (-(c * N))) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in Filter.atTop, ω ∉ B N := by
  apply ae_eventually_notMem
  have hsum : Summable (fun N : ℕ => C * Real.exp (-(c * N))) := by
    have h1 : Summable (fun N : ℕ => Real.exp (-c) ^ N) :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (by have := Real.exp_lt_exp.mpr (show -c < 0 by linarith); rwa [Real.exp_zero] at this)
    have h2 : (fun N : ℕ => C * Real.exp (-(c * N))) = fun N : ℕ => C * Real.exp (-c) ^ N := by
      funext N; rw [← Real.exp_nat_mul]; congr 2; ring
    rw [h2]; exact h1.mul_left C
  have hle : ∀ N, μ (B N) ≤ ENNReal.ofReal (C * Real.exp (-(c * N))) := by
    intro N
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hB N)
  have hfin : ∑' N : ℕ, ENNReal.ofReal (C * Real.exp (-(c * N))) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => mul_nonneg hC (Real.exp_pos _).le) hsum]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum hle)

/-- The walk matrix of the first `N` sample points for the kernel `k(x, y) = h(x - y)` on the flat
    torus, with the estimated normalisation. -/
noncomputable def sampleWalk {d : ℕ} {Ω : Type*} (h : FlatTorus d → ℝ) (X : ℕ → Ω → FlatTorus d)
    (N : ℕ) (ω : Ω) : Matrix (Fin N) (Fin N) ℝ :=
  walkMatrix (fun i j : Fin N => h (X i ω - X j ω))
    (fun i : Fin N => (∑ l : Fin N, h (X i ω - X l ω)) / N)

/-- **Lemma "traces" on the flat torus, almost surely.** Independent points with the invariant
    law on `(ℝ/ℤ)^d`, a kernel `k(x, y) = h(x - y)` with `h` measurable, `L`-Lipschitz, with
    values in `[0, A]`, `A > 0`, and `q0 = ∫ h > 0`: almost surely, for all large `N`,
    `Tr P ≤ 6A/q0` and `Tr P^2 ≤ 6A/q0` for the walk matrix of the first `N` points. No rate in
    the kernel scale is claimed; the kernel is fixed. -/
theorem flatTorus_traces_ae (d : ℕ) {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (h : FlatTorus d → ℝ) (hh : Measurable h) {A L : ℝ} (hA : 0 < A) (hL : 0 ≤ L)
    (hbound : ∀ u, h u ∈ Set.Icc 0 A) (hlip : ∀ u u', |h u - h u'| ≤ L * dist u u')
    (hq0 : 0 < ∫ u, h u ∂flatTorusMeasure d) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in Filter.atTop,
      (sampleWalk h X (N + 1) ω).trace ≤ 6 * A / (∫ u, h u ∂flatTorusMeasure d)
      ∧ (sampleWalk h X (N + 1) ω * sampleWalk h X (N + 1) ω).trace
          ≤ 6 * A / (∫ u, h u ∂flatTorusMeasure d) := by
  set q0 := ∫ u, h u ∂flatTorusMeasure d with hq0def
  -- choose s = q0/4 and r with 2 L r ≤ q0/4
  have hr : 0 < q0 / (8 * (L + 1)) := by positivity
  obtain ⟨M, hM⟩ := flatTorus_traces_whp d (μ := μ) X h_indep hX hlaw h hh hA.le hL hbound hlip
    hq0 hr
  have hsmall : q0 / 4 + 2 * L * (q0 / (8 * (L + 1))) ≤ q0 / 2 := by
    have h1 : L / (L + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : 2 * L * (q0 / (8 * (L + 1))) = q0 / 4 * (L / (L + 1)) := by field_simp; ring
    rw [h2]; nlinarith
  have hbad := ae_eventually_of_exp_bound (μ := μ)
    (fun N => {ω | ¬ ((sampleWalk h X (N + 1) ω).trace ≤ 6 * A / q0
      ∧ (sampleWalk h X (N + 1) ω * sampleWalk h X (N + 1) ω).trace ≤ 6 * A / q0)})
    (C := M * 2) (c := 2 * (q0 / 4) ^ 2 / A ^ 2) (by positivity) (by positivity) ?_
  · filter_upwards [hbad] with ω hω
    filter_upwards [hω] with N hN
    simpa using hN
  · intro N
    have h1 := hM (N + 1) (q0 / 4) (by positivity) hsmall
    have hexp : -(((N + 1 : ℕ) : ℝ) * (q0 / 4)) ^ 2 / (2 * ((N + 1 : ℕ) : ℝ) * (A / 2) ^ 2)
        ≤ -(2 * (q0 / 4) ^ 2 / A ^ 2 * N) := by
      have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      have e : -(((N + 1 : ℕ) : ℝ) * (q0 / 4)) ^ 2 / (2 * ((N + 1 : ℕ) : ℝ) * (A / 2) ^ 2)
          = -(2 * (q0 / 4) ^ 2 / A ^ 2 * ((N + 1 : ℕ) : ℝ)) := by
        field_simp
      rw [e]
      have : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
      have hc : 0 ≤ 2 * (q0 / 4) ^ 2 / A ^ 2 := by positivity
      nlinarith
    calc μ.real {ω | ¬ ((sampleWalk h X (N + 1) ω).trace ≤ 6 * A / q0
          ∧ (sampleWalk h X (N + 1) ω * sampleWalk h X (N + 1) ω).trace ≤ 6 * A / q0)}
        ≤ M * (2 * Real.exp (-(((N + 1 : ℕ) : ℝ) * (q0 / 4)) ^ 2
            / (2 * ((N + 1 : ℕ) : ℝ) * (A / 2) ^ 2))) := h1
      _ ≤ M * 2 * Real.exp (-(2 * (q0 / 4) ^ 2 / A ^ 2 * N)) := by
          have := Real.exp_le_exp.mpr hexp
          have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
          nlinarith [Real.exp_pos (-(2 * (q0 / 4) ^ 2 / A ^ 2 * (N : ℝ)))]

/-- **Empirical means of finitely many bounded functions (the probabilistic input of Lemma
    "kernel matrix").** Independent points `X_j`, functions `phi_a` with values in `[-1, 1]` and
    `E phi_a(X_j) = m_a` (HYPOTHESIS `hmean`; for the real and imaginary parts of the characters of
    a torus and the invariant law, `m_a = 0` for nonzero frequencies, which is not formalised).
    Then, simultaneously for all `a` in a finite set,
    `P(∃ a, |sum_{j<N} phi_a(X_j) - N m_a| ≥ eps) ≤ 2 |s| exp(-eps^2 / (2N))`. -/
theorem bounded_functions_concentration {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [MeasurableSpace E] {ι : Type*} (s : Finset ι)
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (phi : ι → E → ℝ) (hphi : ∀ a, Measurable (phi a)) (hb : ∀ a x, |phi a x| ≤ 1)
    (m : ι → ℝ) (hmean : ∀ a j, μ[fun ω => phi a (X j ω)] = m a)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ a ∈ s, ε ≤ |∑ j ∈ Finset.range N, phi a (X j ω) - N * m a|}
      ≤ s.card * (2 * Real.exp (-ε ^ 2 / (2 * N * (2 / 2) ^ 2))) := by
  have hint : ∀ a j, Integrable (fun ω => phi a (X j ω)) μ := fun a j =>
    Integrable.of_bound ((hphi a).comp (hX j)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => by simpa using hb a (X j ω)))
  have h := net_concentration (μ := μ) s (fun a j ω => phi a (X j ω) + 1)
    (fun a _ => h_indep.comp (fun _ x => phi a x + 1) (fun _ => (hphi a).add_const 1))
    (fun a _ j => (((hphi a).comp (hX j)).add_const 1).aemeasurable) (A := 2)
    (fun a => m a + 1) (by norm_num)
    (fun a _ j => Filter.Eventually.of_forall (fun ω => by
      have := abs_le.mp (hb a (X j ω))
      constructor <;> linarith [this.1, this.2]))
    (fun a _ j => by
      rw [integral_add (hint a j) (integrable_const 1), hmean a j]; simp) N hε
  have hset : {ω | ∃ a ∈ s, ε ≤ |∑ j ∈ Finset.range N, (phi a (X j ω) + 1) - N * (m a + 1)|}
      = {ω | ∃ a ∈ s, ε ≤ |∑ j ∈ Finset.range N, phi a (X j ω) - N * m a|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    refine exists_congr (fun a => and_congr_right (fun _ => ?_))
    have e : ∑ j ∈ Finset.range N, (phi a (X j ω) + 1) - N * (m a + 1)
        = ∑ j ∈ Finset.range N, phi a (X j ω) - N * m a := by
      rw [Finset.sum_add_distrib]; simp; ring
    rw [e]
  rwa [hset] at h

/-- **Gram matrix of sampled modes (probabilistic input of Lemma "kernel matrix").** Finitely many
    measurable functions `phi_f` with `|phi_f| ≤ B`, orthonormal under the law of the points
    (HYPOTHESIS `horth`: `E phi_f(X_j) phi_g(X_j) = δ_fg`; for the real Fourier modes of a torus
    this is not formalised). Then, simultaneously for all pairs,
    `P(∃ f g, |sum_{j<N} phi_f(X_j) phi_g(X_j) - N δ_fg| ≥ eps) ≤ 2 |F|^2 exp(-(eps/B^2)^2 / (2N))`. -/
theorem gram_concentration {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [MeasurableSpace E] {F : Type*} [Fintype F]
    [DecidableEq F] (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (phi : F → E → ℝ) (hphi : ∀ f, Measurable (phi f)) {B : ℝ} (hB : 0 < B)
    (hb : ∀ f x, |phi f x| ≤ B)
    (horth : ∀ f g j, μ[fun ω => phi f (X j ω) * phi g (X j ω)] = if f = g then 1 else 0)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ f g, ε ≤ |∑ j ∈ Finset.range N, phi f (X j ω) * phi g (X j ω)
        - N * (if f = g then (1 : ℝ) else 0)|}
      ≤ (Fintype.card F) ^ 2 * (2 * Real.exp (-(ε / B ^ 2) ^ 2 / (2 * N))) := by
  have hB2 : 0 < B ^ 2 := by positivity
  have h := bounded_functions_concentration (μ := μ) (Finset.univ : Finset (F × F)) X h_indep hX
    (fun p x => phi p.1 x * phi p.2 x / B ^ 2)
    (fun p => ((hphi p.1).mul (hphi p.2)).div_const _)
    (fun p x => by
      rw [abs_div, abs_mul, abs_of_pos hB2, div_le_one hB2]
      have h1 := hb p.1 x
      have h2 := hb p.2 x
      nlinarith [abs_nonneg (phi p.1 x), abs_nonneg (phi p.2 x)])
    (fun p => (if p.1 = p.2 then (1 : ℝ) else 0) / B ^ 2)
    (fun p j => by
      have := horth p.1 p.2 j
      simp only [div_eq_mul_inv]
      rw [integral_mul_const, this])
    N (ε := ε / B ^ 2) (by positivity)
  have hcard : ((Finset.univ : Finset (F × F)).card : ℝ) = (Fintype.card F : ℝ) ^ 2 := by
    simp [Fintype.card_prod, pow_two]
  rw [hcard] at h
  have hexp : -(ε / B ^ 2) ^ 2 / (2 * (N : ℝ) * (2 / 2) ^ 2) = -(ε / B ^ 2) ^ 2 / (2 * N) := by
    norm_num
  rw [hexp] at h
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  rintro ω ⟨f, g, hfg⟩
  refine ⟨(f, g), Finset.mem_univ _, ?_⟩
  have e : ∑ j ∈ Finset.range N, phi f (X j ω) * phi g (X j ω) / B ^ 2
        - N * ((if f = g then (1 : ℝ) else 0) / B ^ 2)
      = (∑ j ∈ Finset.range N, phi f (X j ω) * phi g (X j ω)
        - N * (if f = g then (1 : ℝ) else 0)) / B ^ 2 := by
    rw [← Finset.sum_div]; ring
  show ε / B ^ 2 ≤ |∑ j ∈ Finset.range N, phi f (X j ω) * phi g (X j ω) / B ^ 2
        - N * ((if f = g then (1 : ℝ) else 0) / B ^ 2)|
  rw [e, abs_div, abs_of_pos hB2]
  exact div_le_div_of_nonneg_right hfg hB2.le

/-- **A nontrivial character has mean zero.** `c`, `s` are the real and imaginary part of a
    character of an additive group (addition formulas `hc`, `hs`), bounded and measurable, and the
    probability measure `ν` is translation invariant. If the character is not `1` at some point
    `a`, both integrals vanish. This gives mean zero for the real Fourier modes of a torus with
    nonzero frequency. -/
theorem character_mean_zero {G : Type*} [MeasurableSpace G] [AddGroup G] [MeasurableAdd G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddRightInvariant]
    (c s : G → ℝ) (hcm : Measurable c) (hsm : Measurable s)
    (hcb : ∀ x, |c x| ≤ 1) (hsb : ∀ x, |s x| ≤ 1)
    (hc : ∀ x a, c (x + a) = c x * c a - s x * s a)
    (hs : ∀ x a, s (x + a) = s x * c a + c x * s a)
    (a : G) (ha : c a ≠ 1 ∨ s a ≠ 0) :
    ∫ x, c x ∂ν = 0 ∧ ∫ x, s x ∂ν = 0 := by
  have hci : Integrable c ν := Integrable.of_bound hcm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by simpa using hcb x))
  have hsi : Integrable s ν := Integrable.of_bound hsm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by simpa using hsb x))
  have e1 : ∫ x, c x ∂ν = (∫ x, c x ∂ν) * c a - (∫ x, s x ∂ν) * s a := by
    calc ∫ x, c x ∂ν = ∫ x, c (x + a) ∂ν := (integral_add_right_eq_self (μ := ν) c a).symm
      _ = ∫ x, (c x * c a - s x * s a) ∂ν := by simp_rw [hc _ a]
      _ = (∫ x, c x ∂ν) * c a - (∫ x, s x ∂ν) * s a := by
        rw [integral_sub (hci.mul_const _) (hsi.mul_const _), integral_mul_const,
          integral_mul_const]
  have e2 : ∫ x, s x ∂ν = (∫ x, s x ∂ν) * c a + (∫ x, c x ∂ν) * s a := by
    calc ∫ x, s x ∂ν = ∫ x, s (x + a) ∂ν := (integral_add_right_eq_self (μ := ν) s a).symm
      _ = ∫ x, (s x * c a + c x * s a) ∂ν := by simp_rw [hs _ a]
      _ = (∫ x, s x ∂ν) * c a + (∫ x, c x ∂ν) * s a := by
        rw [integral_add (hsi.mul_const _) (hci.mul_const _), integral_mul_const,
          integral_mul_const]
  set Ic := ∫ x, c x ∂ν
  set Is := ∫ x, s x ∂ν
  have hdet : 0 < (1 - c a) ^ 2 + s a ^ 2 := by
    rcases ha with h | h
    · have : 0 < (1 - c a) ^ 2 := by
        have : 1 - c a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
        positivity
      nlinarith [_root_.sq_nonneg (s a)]
    · have : 0 < s a ^ 2 := by positivity
      nlinarith [_root_.sq_nonneg (1 - c a)]
  have k1 : ((1 - c a) ^ 2 + s a ^ 2) * Ic = 0 := by
    have : ((1 - c a) ^ 2 + s a ^ 2) * Ic
        = (1 - c a) * (Ic - (Ic * c a - Is * s a)) - s a * (Is - (Is * c a + Ic * s a)) := by ring
    rw [this]
    have a1 : Ic - (Ic * c a - Is * s a) = 0 := by linarith [e1]
    have a2 : Is - (Is * c a + Ic * s a) = 0 := by linarith [e2]
    rw [a1, a2]; ring
  have k2 : ((1 - c a) ^ 2 + s a ^ 2) * Is = 0 := by
    have : ((1 - c a) ^ 2 + s a ^ 2) * Is
        = (1 - c a) * (Is - (Is * c a + Ic * s a)) + s a * (Ic - (Ic * c a - Is * s a)) := by ring
    rw [this]
    have a1 : Ic - (Ic * c a - Is * s a) = 0 := by linarith [e1]
    have a2 : Is - (Is * c a + Ic * s a) = 0 := by linarith [e2]
    rw [a1, a2]; ring
  exact ⟨(mul_eq_zero.mp k1).resolve_left hdet.ne', (mul_eq_zero.mp k2).resolve_left hdet.ne'⟩

/-- **Products of Fourier modes.** `C k`, `S k` are the real and imaginary parts of a family of
    characters indexed by an additive group of frequencies (product formulas `hC`, `hS`, symmetry
    `hCn`, `hSn`), bounded and measurable, with `∫ C k = δ_{k,0}` and `∫ S k = 0` (which follows from
    `character_mean_zero` for a translation-invariant measure). Then
    `∫ C_m C_n = (δ_{m-n,0} + δ_{m+n,0})/2`, `∫ S_m S_n = (δ_{m-n,0} - δ_{m+n,0})/2`, `∫ C_m S_n = 0`:
    the orthogonality relations behind the Gram matrix of the sampled modes. -/
theorem mode_products {G : Type*} [MeasurableSpace G] (ν : Measure G) [IsProbabilityMeasure ν]
    {Λ : Type*} [AddGroup Λ] [DecidableEq Λ] (C S : Λ → G → ℝ)
    (hCm : ∀ k, Measurable (C k)) (hSm : ∀ k, Measurable (S k))
    (hCb : ∀ k x, |C k x| ≤ 1) (hSb : ∀ k x, |S k x| ≤ 1)
    (hC : ∀ m n x, C (m + n) x = C m x * C n x - S m x * S n x)
    (hS : ∀ m n x, S (m + n) x = S m x * C n x + C m x * S n x)
    (hCn : ∀ n x, C (-n) x = C n x) (hSn : ∀ n x, S (-n) x = -S n x)
    (hCmean : ∀ k, ∫ x, C k x ∂ν = if k = 0 then 1 else 0)
    (hSmean : ∀ k, ∫ x, S k x ∂ν = 0) (m n : Λ) :
    ∫ x, C m x * C n x ∂ν
        = ((if m - n = 0 then (1 : ℝ) else 0) + (if m + n = 0 then 1 else 0)) / 2 ∧
    ∫ x, S m x * S n x ∂ν
        = ((if m - n = 0 then (1 : ℝ) else 0) - (if m + n = 0 then 1 else 0)) / 2 ∧
    ∫ x, C m x * S n x ∂ν = 0 := by
  have hCi : ∀ k, Integrable (C k) ν := fun k =>
    Integrable.of_bound (hCm k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by simpa using hCb k x))
  have hSi : ∀ k, Integrable (S k) ν := fun k =>
    Integrable.of_bound (hSm k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by simpa using hSb k x))
  have hCsub : ∀ x, C (m - n) x = C m x * C n x + S m x * S n x := by
    intro x; rw [sub_eq_add_neg, hC, hCn, hSn]; ring
  have hSsub : ∀ x, S (m - n) x = -(C m x * S n x) + S m x * C n x := by
    intro x; rw [sub_eq_add_neg, hS, hCn, hSn]; ring
  refine ⟨?_, ?_, ?_⟩
  · have e : (fun x => C m x * C n x) = fun x => (C (m - n) x + C (m + n) x) / 2 := by
      funext x; rw [hCsub, hC]; ring
    rw [e, integral_div, integral_add (hCi _) (hCi _), hCmean, hCmean]
  · have e : (fun x => S m x * S n x) = fun x => (C (m - n) x - C (m + n) x) / 2 := by
      funext x; rw [hCsub, hC]; ring
    rw [e, integral_div, integral_sub (hCi _) (hCi _), hCmean, hCmean]
  · have e : (fun x => C m x * S n x) = fun x => (S (m + n) x - S (m - n) x) / 2 := by
      funext x; rw [hSsub, hS]; ring
    rw [e, integral_div, integral_sub (hSi _) (hSi _), hSmean, hSmean]; simp

/-- **Orthogonality of the real Fourier modes of the circle, without hypotheses.** For
    `C_k = Re e^{2πikx}`, `S_k = Im e^{2πikx}` on `UnitAddCircle` with its Haar probability measure:
    `∫ C_m C_n = (δ_{m,n} + δ_{m,-n})/2`, `∫ S_m S_n = (δ_{m,n} - δ_{m,-n})/2`, `∫ C_m S_n = 0`.
    Instance of `mode_products` and `character_mean_zero`. -/
theorem circle_mode_products (m n : ℤ) :
    ∫ x : UnitAddCircle, (fourier m x).re * (fourier n x).re ∂AddCircle.haarAddCircle
        = ((if m - n = 0 then (1 : ℝ) else 0) + (if m + n = 0 then 1 else 0)) / 2 ∧
    ∫ x : UnitAddCircle, (fourier m x).im * (fourier n x).im ∂AddCircle.haarAddCircle
        = ((if m - n = 0 then (1 : ℝ) else 0) - (if m + n = 0 then 1 else 0)) / 2 ∧
    ∫ x : UnitAddCircle, (fourier m x).re * (fourier n x).im ∂AddCircle.haarAddCircle = 0 := by
  have hnorm : ∀ (k : ℤ) (x : UnitAddCircle), ‖(fourier k x : ℂ)‖ = 1 := fun k x => by
    rw [fourier_apply]; exact Circle.norm_coe _
  have hCm : ∀ k : ℤ, Measurable fun x : UnitAddCircle => (fourier k x).re := fun k =>
    (Complex.continuous_re.comp (fourier k).continuous).measurable
  have hSm : ∀ k : ℤ, Measurable fun x : UnitAddCircle => (fourier k x).im := fun k =>
    (Complex.continuous_im.comp (fourier k).continuous).measurable
  have hCb : ∀ (k : ℤ) (x : UnitAddCircle), |(fourier k x).re| ≤ 1 := fun k x =>
    (Complex.abs_re_le_norm _).trans (hnorm k x).le
  have hSb : ∀ (k : ℤ) (x : UnitAddCircle), |(fourier k x).im| ≤ 1 := fun k x =>
    (Complex.abs_im_le_norm _).trans (hnorm k x).le
  have hadd : ∀ (k : ℤ) (x a : UnitAddCircle), fourier k (x + a) = fourier k x * fourier k a := by
    intro k x a
    simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  have hmean : ∀ k : ℤ, k ≠ 0 →
      ∫ x : UnitAddCircle, (fourier k x).re ∂AddCircle.haarAddCircle = 0 ∧
      ∫ x : UnitAddCircle, (fourier k x).im ∂AddCircle.haarAddCircle = 0 := by
    intro k hk
    refine character_mean_zero AddCircle.haarAddCircle _ _ (hCm k) (hSm k) (hCb k) (hSb k)
      (fun x a => by rw [hadd, Complex.mul_re]) (fun x a => by rw [hadd, Complex.mul_im]; ring)
      (((1 : ℝ) / 2 / k : ℝ) : UnitAddCircle) (Or.inl ?_)
    have h := fourier_add_half_inv_index (T := 1) hk one_pos (0 : UnitAddCircle)
    rw [zero_add, fourier_eval_zero] at h
    rw [h]; norm_num
  refine mode_products AddCircle.haarAddCircle (fun k x => (fourier k x).re)
    (fun k x => (fourier k x).im) hCm hSm hCb hSb
    (fun a b x => by beta_reduce; rw [fourier_add, Complex.mul_re])
    (fun a b x => by beta_reduce; rw [fourier_add, Complex.mul_im]; ring)
    (fun k x => by beta_reduce; rw [fourier_neg, Complex.conj_re])
    (fun k x => by beta_reduce; rw [fourier_neg, Complex.conj_im])
    (fun k => ?_) (fun k => ?_) m n
  · by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk]; exact (hmean k hk).1
  · by_cases hk : k = 0
    · subst hk; simp
    · exact (hmean k hk).2

/-- The character of the flat torus with frequency `n ∈ ℤ^d`: `x ↦ ∏_i e^{2πi n_i x_i}`. -/
noncomputable def torusChar (d : ℕ) (n : Fin d → ℤ) (x : FlatTorus d) : ℂ :=
  ∏ i, fourier (n i) (x i)

theorem torusChar_norm (d : ℕ) (n : Fin d → ℤ) (x : FlatTorus d) : ‖torusChar d n x‖ = 1 := by
  unfold torusChar
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => by rw [fourier_apply]; exact Circle.norm_coe _

theorem torusChar_add_freq (d : ℕ) (m n : Fin d → ℤ) (x : FlatTorus d) :
    torusChar d (m + n) x = torusChar d m x * torusChar d n x := by
  unfold torusChar
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, fourier_add]

theorem torusChar_neg_freq (d : ℕ) (n : Fin d → ℤ) (x : FlatTorus d) :
    torusChar d (-n) x = (starRingEnd ℂ) (torusChar d n x) := by
  unfold torusChar
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.neg_apply, fourier_neg]

theorem torusChar_add (d : ℕ) (n : Fin d → ℤ) (x a : FlatTorus d) :
    torusChar d n (x + a) = torusChar d n x * torusChar d n a := by
  unfold torusChar
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by
    simp only [Pi.add_apply, fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem torusChar_continuous (d : ℕ) (n : Fin d → ℤ) : Continuous (torusChar d n) := by
  unfold torusChar
  exact continuous_finset_prod _ fun i _ => (fourier (n i)).continuous.comp (continuous_apply i)

/-- **Orthogonality of the real Fourier modes of the flat torus of dimension `d`, without
    hypotheses.** For `C_n = Re χ_n`, `S_n = Im χ_n`, `χ_n(x) = ∏_i e^{2πi n_i x_i}`, under the product
    of the Haar measures: `∫ C_m C_n = (δ_{m,n} + δ_{m,-n})/2`, `∫ S_m S_n = (δ_{m,n} - δ_{m,-n})/2`,
    `∫ C_m S_n = 0`. -/
theorem flatTorus_mode_products (d : ℕ) (m n : Fin d → ℤ) :
    ∫ x, (torusChar d m x).re * (torusChar d n x).re ∂flatTorusMeasure d
        = ((if m - n = 0 then (1 : ℝ) else 0) + (if m + n = 0 then 1 else 0)) / 2 ∧
    ∫ x, (torusChar d m x).im * (torusChar d n x).im ∂flatTorusMeasure d
        = ((if m - n = 0 then (1 : ℝ) else 0) - (if m + n = 0 then 1 else 0)) / 2 ∧
    ∫ x, (torusChar d m x).re * (torusChar d n x).im ∂flatTorusMeasure d = 0 := by
  have hCm : ∀ k : Fin d → ℤ, Measurable fun x : FlatTorus d => (torusChar d k x).re := fun k =>
    (Complex.continuous_re.comp (torusChar_continuous d k)).measurable
  have hSm : ∀ k : Fin d → ℤ, Measurable fun x : FlatTorus d => (torusChar d k x).im := fun k =>
    (Complex.continuous_im.comp (torusChar_continuous d k)).measurable
  have hCb : ∀ (k : Fin d → ℤ) (x : FlatTorus d), |(torusChar d k x).re| ≤ 1 := fun k x =>
    (Complex.abs_re_le_norm _).trans (torusChar_norm d k x).le
  have hSb : ∀ (k : Fin d → ℤ) (x : FlatTorus d), |(torusChar d k x).im| ≤ 1 := fun k x =>
    (Complex.abs_im_le_norm _).trans (torusChar_norm d k x).le
  have hmean : ∀ k : Fin d → ℤ, k ≠ 0 →
      ∫ x, (torusChar d k x).re ∂flatTorusMeasure d = 0 ∧
      ∫ x, (torusChar d k x).im ∂flatTorusMeasure d = 0 := by
    intro k hk
    obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      exact hk (funext fun i => by simpa using not_exists.mp h i)
    refine character_mean_zero (flatTorusMeasure d) _ _ (hCm k) (hSm k) (hCb k) (hSb k)
      (fun x a => by rw [torusChar_add, Complex.mul_re])
      (fun x a => by rw [torusChar_add, Complex.mul_im]; ring)
      (Pi.single i (((1 : ℝ) / 2 / k i : ℝ) : UnitAddCircle)) (Or.inl ?_)
    have hval : torusChar d k (Pi.single i (((1 : ℝ) / 2 / k i : ℝ) : UnitAddCircle)) = -1 := by
      unfold torusChar
      rw [Finset.prod_eq_single i]
      · rw [Pi.single_eq_same]
        have h := fourier_add_half_inv_index (T := 1) hi one_pos (0 : UnitAddCircle)
        rwa [zero_add, fourier_eval_zero] at h
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, fourier_eval_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hval]; norm_num
  refine mode_products (flatTorusMeasure d) (fun k x => (torusChar d k x).re)
    (fun k x => (torusChar d k x).im) hCm hSm hCb hSb
    (fun a b x => by beta_reduce; rw [torusChar_add_freq, Complex.mul_re])
    (fun a b x => by beta_reduce; rw [torusChar_add_freq, Complex.mul_im]; ring)
    (fun k x => by beta_reduce; rw [torusChar_neg_freq, Complex.conj_re])
    (fun k x => by beta_reduce; rw [torusChar_neg_freq, Complex.conj_im])
    (fun k => ?_) (fun k => ?_) m n
  · by_cases hk : k = 0
    · subst hk; simp [torusChar]
    · rw [if_neg hk]; exact (hmean k hk).1
  · by_cases hk : k = 0
    · subst hk; simp [torusChar]
    · exact (hmean k hk).2

theorem torusChar_zero (d : ℕ) (x : FlatTorus d) : torusChar d 0 x = 1 := by
  simp [torusChar]

/-- Mean zero of the real and imaginary parts of a nontrivial character of the flat torus. -/
theorem torusChar_mean (d : ℕ) (n : Fin d → ℤ) (hn : n ≠ 0) :
    ∫ x, (torusChar d n x).re ∂flatTorusMeasure d = 0 ∧
    ∫ x, (torusChar d n x).im ∂flatTorusMeasure d = 0 := by
  have h := flatTorus_mode_products d 0 n
  simp only [torusChar_zero, Complex.one_re, one_mul, zero_sub, zero_add, neg_eq_zero, if_neg hn,
    add_zero, zero_div] at h
  exact ⟨h.1, h.2.2⟩

/-- The real Fourier modes of the flat torus, normalised in `L²`: the constant `1`,
    `√2 Re χ_n` (index `(n, false)`) and `√2 Im χ_n` (index `(n, true)`). -/
noncomputable def torusMode (d : ℕ) : Option ((Fin d → ℤ) × Bool) → FlatTorus d → ℝ
  | none => fun _ => 1
  | some (n, false) => fun x => Real.sqrt 2 * (torusChar d n x).re
  | some (n, true) => fun x => Real.sqrt 2 * (torusChar d n x).im

theorem torusMode_measurable (d : ℕ) (f : Option ((Fin d → ℤ) × Bool)) :
    Measurable (torusMode d f) := by
  rcases f with _ | ⟨n, b⟩
  · exact measurable_const
  · cases b
    · exact (Complex.continuous_re.comp (torusChar_continuous d n)).measurable.const_mul _
    · exact (Complex.continuous_im.comp (torusChar_continuous d n)).measurable.const_mul _

theorem torusMode_bound (d : ℕ) (f : Option ((Fin d → ℤ) × Bool)) (x : FlatTorus d) :
    |torusMode d f x| ≤ Real.sqrt 2 := by
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  rcases f with _ | ⟨n, b⟩
  · show |(1 : ℝ)| ≤ Real.sqrt 2
    rw [abs_one]; exact h2
  · cases b
    · simp only [torusMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
      have := (Complex.abs_re_le_norm (torusChar d n x)).trans (torusChar_norm d n x).le
      nlinarith [Real.sqrt_nonneg 2]
    · simp only [torusMode, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
      have := (Complex.abs_im_le_norm (torusChar d n x)).trans (torusChar_norm d n x).le
      nlinarith [Real.sqrt_nonneg 2]

/-- **Orthonormality of the real Fourier modes of the flat torus, without hypotheses on the
    measure.** For two indices whose frequencies are nonzero and do not add up to zero (a set of
    frequencies containing no pair `n, -n`), `∫ φ_f φ_g = δ_fg`. -/
theorem torusMode_orthonormal (d : ℕ) (f g : Option ((Fin d → ℤ) × Bool))
    (hf : ∀ n b, f = some (n, b) → n ≠ 0) (hg : ∀ n b, g = some (n, b) → n ≠ 0)
    (hfg : ∀ m b n b', f = some (m, b) → g = some (n, b') → m + n ≠ 0) :
    ∫ x, torusMode d f x * torusMode d g x ∂flatTorusMeasure d = if f = g then 1 else 0 := by
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases f with _ | ⟨m, b⟩ <;> rcases g with _ | ⟨n, b'⟩
  · simp [torusMode]
  · have hn := hg n b' rfl
    cases b' <;> simp only [torusMode, one_mul, integral_const_mul, (torusChar_mean d n hn).1,
      (torusChar_mean d n hn).2, mul_zero] <;> simp
  · have hm := hf m b rfl
    cases b <;> simp only [torusMode, mul_one, integral_const_mul, (torusChar_mean d m hm).1,
      (torusChar_mean d m hm).2, mul_zero] <;> simp
  · have hmn := hfg m b n b' rfl rfl
    have hP := flatTorus_mode_products d m n
    have hP' := flatTorus_mode_products d n m
    have hnm : n + m ≠ 0 := by rwa [add_comm]
    simp only [if_neg hmn, add_zero, sub_zero] at hP
    simp only [if_neg hnm, add_zero, sub_zero] at hP'
    have key : ∀ (u w : FlatTorus d → ℝ),
        ∫ x, (Real.sqrt 2 * u x) * (Real.sqrt 2 * w x) ∂flatTorusMeasure d
          = 2 * ∫ x, u x * w x ∂flatTorusMeasure d := by
      intro u w
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show Real.sqrt 2 * u x * (Real.sqrt 2 * w x) = 2 * (u x * w x)
      linear_combination (u x * w x) * h22
    have hiff : (some (m, b) = some (n, b')) ↔ (m = n ∧ b = b') := by
      simp [Prod.ext_iff]
    cases b <;> cases b'
    · simp only [torusMode]
      rw [key, hP.1]
      by_cases h : m = n
      · simp [h]
      · have : m - n ≠ 0 := sub_ne_zero.mpr h
        simp [h, this]
    · simp only [torusMode]
      rw [key, hP.2.2]; simp
    · simp only [torusMode]
      rw [key]
      have : ∫ x, (torusChar d m x).im * (torusChar d n x).re ∂flatTorusMeasure d = 0 := by
        rw [← hP'.2.2]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      rw [this]; simp
    · simp only [torusMode]
      rw [key, hP.2.1]
      by_cases h : m = n
      · simp [h]
      · have : m - n ≠ 0 := sub_ne_zero.mpr h
        simp [h, this]

/-- **Gram matrix of the sampled Fourier modes on the flat torus, with its probability and
    without hypotheses on the modes.** Independent points with the uniform law on the flat torus
    of dimension `d`; `F` a finite set of mode indices whose frequencies are nonzero and contain no
    pair `n, -n`. Then
    `P(∃ f g ∈ F, |∑_{j<N} φ_f(X_j) φ_g(X_j) - N δ_fg| ≥ eps) ≤ 2 |F|^2 exp(-(eps/2)^2 / (2N))`. -/
theorem flatTorus_gram_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (F : Finset (Option ((Fin d → ℤ) × Bool)))
    (hF : ∀ n b, some (n, b) ∈ F → n ≠ 0)
    (hF2 : ∀ m b n b', some (m, b) ∈ F → some (n, b') ∈ F → m + n ≠ 0)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ f g : F, ε ≤ |∑ j ∈ Finset.range N,
        torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
        - N * (if f = g then (1 : ℝ) else 0)|}
      ≤ (Fintype.card F) ^ 2 * (2 * Real.exp (-(ε / 2) ^ 2 / (2 * N))) := by
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h := gram_concentration (μ := μ) (F := F) X h_indep hX (fun f => torusMode d f.1)
    (fun f => torusMode_measurable d f.1) (B := Real.sqrt 2) (by positivity)
    (fun f x => torusMode_bound d f.1 x)
    (fun f g j => by
      have hm : Measurable fun x => torusMode d f.1 x * torusMode d g.1 x :=
        (torusMode_measurable d f.1).mul (torusMode_measurable d g.1)
      have e : μ[fun ω => torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)]
          = ∫ x, torusMode d f.1 x * torusMode d g.1 x ∂flatTorusMeasure d := by
        rw [← hlaw j, integral_map (hX j).aemeasurable hm.aestronglyMeasurable]
      rw [e, torusMode_orthonormal d f.1 g.1
        (fun n b hfe => hF n b (hfe ▸ f.2)) (fun n b hge => hF n b (hge ▸ g.2))
        (fun m b n b' hfe hge => hF2 m b n b' (hfe ▸ f.2) (hge ▸ g.2))]
      simp only [Subtype.ext_iff])
    N hε
  rwa [h22] at h

/-- **The pair of real modes of a frequency reproduces the translation-invariant kernel.**
    `φ_{n,c}(x) φ_{n,c}(y) + φ_{n,s}(x) φ_{n,s}(y) = 2 Re χ_n(x - y)`. Hence a kernel
    `∑_n â_n χ_n(x - y)` with real symmetric coefficients is `∑_f a_f φ_f(x) φ_f(y)` over the real
    modes, the form required by `finite_rank_kernel_entry`. -/
theorem torusMode_kernel (d : ℕ) (n : Fin d → ℤ) (x y : FlatTorus d) :
    torusMode d (some (n, false)) x * torusMode d (some (n, false)) y
      + torusMode d (some (n, true)) x * torusMode d (some (n, true)) y
      = 2 * (torusChar d n (x - y)).re := by
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hx : torusChar d n x = torusChar d n (x - y) * torusChar d n y := by
    rw [← torusChar_add, sub_add_cancel]
  have hw : (torusChar d n y).re * (torusChar d n y).re
      + (torusChar d n y).im * (torusChar d n y).im = 1 := by
    have h := torusChar_norm d n y
    have h2 : Complex.normSq (torusChar d n y) = 1 := by
      rw [Complex.normSq_eq_norm_sq, h]; norm_num
    rwa [Complex.normSq_apply] at h2
  simp only [torusMode]
  rw [hx, Complex.mul_re, Complex.mul_im]
  linear_combination ((torusChar d n (x - y)).re * ((torusChar d n y).re * (torusChar d n y).re
      + (torusChar d n y).im * (torusChar d n y).im)) * h22
    + 2 * (torusChar d n (x - y)).re * hw

section GaussSums
open Set

/-- `∑_{j=1}^{n} e^{-c j²} ≤ √(π/c)/2`. -/
theorem gauss_sum_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∑ i ∈ Finset.range n, Real.exp (-c * (((i + 1 : ℕ) : ℝ)) ^ 2) ≤ Real.sqrt (Real.pi / c) / 2 := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-c * x ^ 2)) (Icc (0 : ℝ) (0 + n)) := by
    intro x hx y hy hxy
    apply Real.exp_le_exp.mpr
    have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
    nlinarith
  have h1 := hanti.sum_le_integral
  simp only [zero_add] at h1
  refine h1.trans ?_
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_gaussian_Ioi c]
  refine setIntegral_mono_set ((integrable_exp_neg_mul_sq hc).integrableOn) ?_ ?_
  · exact Filter.Eventually.of_forall fun x => (Real.exp_pos _).le
  · exact (Filter.Eventually.of_forall fun x hx => hx.1 : ∀ᵐ x, x ∈ Ioc (0:ℝ) n → x ∈ Ioi (0:ℝ))

/-- The symmetric sum in terms of the one-sided sum. -/
theorem gauss_sum_int_eq (c : ℝ) (m : ℕ) :
    ∑ j ∈ Finset.Icc (-(m : ℤ)) m, Real.exp (-c * (j : ℝ) ^ 2)
      = 1 + 2 * ∑ i ∈ Finset.range m, Real.exp (-c * (((i + 1 : ℕ) : ℝ)) ^ 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hset : Finset.Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ)
        = insert (-((m + 1 : ℕ) : ℤ)) (insert (((m + 1 : ℕ) : ℤ)) (Finset.Icc (-(m : ℤ)) m)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hset, Finset.sum_insert, Finset.sum_insert, ih, Finset.sum_range_succ]
    · push_cast; ring_nf
    · simp only [Finset.mem_Icc]; push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega

/-- `∑_{|j| ≤ m} e^{-c j²} ≤ 1 + √(π/c)`. -/
theorem gauss_sum_int_le {c : ℝ} (hc : 0 < c) (m : ℕ) :
    ∑ j ∈ Finset.Icc (-(m : ℤ)) m, Real.exp (-c * (j : ℝ) ^ 2) ≤ 1 + Real.sqrt (Real.pi / c) := by
  rw [gauss_sum_int_eq]
  linarith [gauss_sum_le hc m]

/-- **Quantitative core of (P2) in Fourier form.** Box sums in dimension `d`: `∑_{n ∈ [-m,m]^d} e^{-c |n|²} ≤ (1 + √(π/c))^d`.
    With `c = 2π² t` these are the partial sums of `p^{(t)}(0) = ∑_n e^{-2π²|n|² t}`, and
    `√(π/c) = (2π t)^{-1/2}`: the on-diagonal bound `C_d t^{-d/2}` for bounded `t`. -/
theorem gauss_box_sum_le {c : ℝ} (hc : 0 < c) (d m : ℕ) :
    ∑ n ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m),
        Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ≤ (1 + Real.sqrt (Real.pi / c)) ^ d := by
  have h := Finset.prod_univ_sum (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m)
    (fun (_ : Fin d) (j : ℤ) => Real.exp (-c * (j : ℝ) ^ 2))
  have e : ∀ n : Fin d → ℤ, Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      = ∏ i, Real.exp (-c * ((n i : ℤ) : ℝ) ^ 2) := by
    intro n; rw [← Real.exp_sum, Finset.mul_sum]
  simp_rw [e]
  rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => (Real.exp_pos _).le) (gauss_sum_int_le hc m) d

/-- Every finite set of frequencies lies in a box. -/
theorem finset_subset_box (d : ℕ) (T : Finset (Fin d → ℤ)) :
    ∃ m : ℕ, T ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m) := by
  refine ⟨T.sup fun n => Finset.univ.sup fun i => (n i).natAbs, fun n hn => ?_⟩
  rw [Fintype.mem_piFinset]
  intro i
  have h1 : (n i).natAbs ≤ Finset.univ.sup fun i => (n i).natAbs :=
    Finset.le_sup (f := fun i => (n i).natAbs) (Finset.mem_univ i)
  have h2 : (Finset.univ.sup fun i => (n i).natAbs)
      ≤ T.sup fun n => Finset.univ.sup fun i => (n i).natAbs :=
    Finset.le_sup (f := fun n : Fin d → ℤ => Finset.univ.sup fun i => (n i).natAbs) hn
  rw [Finset.mem_Icc]
  omega

/-- Sums over arbitrary finite sets of frequencies: `∑_{n ∈ T} e^{-c|n|²} ≤ (1 + √(π/c))^d`. -/
theorem gauss_finset_sum_le {c : ℝ} (hc : 0 < c) (d : ℕ) (T : Finset (Fin d → ℤ)) :
    ∑ n ∈ T, Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ≤ (1 + Real.sqrt (Real.pi / c)) ^ d := by
  obtain ⟨m, hm⟩ := finset_subset_box d T
  exact (Finset.sum_le_sum_of_subset_of_nonneg hm fun n _ _ => (Real.exp_pos _).le).trans
    (gauss_box_sum_le hc d m)

/-- **Tail of the Fourier series of the heat kernel of the torus.** For a finite set `T` of
    frequencies with `|n|² ≥ R`,
    `∑_{n ∈ T} e^{-c|n|²} ≤ e^{-cR/2} (1 + √(2π/c))^d`. With `c = 2π² t` this bounds the error of
    truncating `p^{(t)}(x) = ∑_n e^{-2π²|n|² t} χ_n(x)` uniformly in `x`. -/
theorem gauss_tail_sum_le {c : ℝ} (hc : 0 < c) (d : ℕ) (T : Finset (Fin d → ℤ)) {R : ℝ}
    (hT : ∀ n ∈ T, R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) :
    ∑ n ∈ T, Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ≤ Real.exp (-c * R / 2) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d := by
  have hc2 : 0 < c / 2 := by positivity
  have h := gauss_finset_sum_le hc2 d T
  have e : Real.pi / (c / 2) = 2 * Real.pi / c := by field_simp
  rw [e] at h
  calc ∑ n ∈ T, Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ≤ ∑ n ∈ T, Real.exp (-c * R / 2) * Real.exp (-(c / 2) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hT n hn]
    _ = Real.exp (-c * R / 2) * ∑ n ∈ T, Real.exp (-(c / 2) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

/-- The Fourier coefficients of the heat kernel of the torus are summable. -/
theorem gauss_summable {c : ℝ} (hc : 0 < c) (d : ℕ) :
    Summable fun n : Fin d → ℤ => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) :=
  summable_of_sum_le (fun n => (Real.exp_pos _).le) (fun T => gauss_finset_sum_le hc d T)

/-- **On-diagonal bound of the heat kernel of the torus, as a series (quantitative part of
    (P2)).** `∑_{n ∈ ℤ^d} e^{-c|n|²} ≤ (1 + √(π/c))^d`; with `c = 2π² t` the left side is
    `p^{(t)}(0)` in its Fourier form and the right side is `(1 + (2π t)^{-1/2})^d`. -/
theorem gauss_tsum_le {c : ℝ} (hc : 0 < c) (d : ℕ) :
    ∑' n : Fin d → ℤ, Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ≤ (1 + Real.sqrt (Real.pi / c)) ^ d :=
  (gauss_summable hc d).tsum_le_of_sum_le (fun T => gauss_finset_sum_le hc d T)

end GaussSums

/-! ### The heat kernel of the flat torus as a Fourier series -/

/-- Integral of a series of bounded functions against a bounded function, term by term. -/
theorem series_kernel_integral {G : Type*} [MeasurableSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] {ι : Type*} [Countable ι] (a : ι → ℝ) (ha : Summable fun n => |a n|)
    (u : ι → G → ℝ) (hum : ∀ n, Measurable (u n)) (hub : ∀ n z, |u n z| ≤ 1)
    (q : G → ℝ) (hqm : Measurable q) {B : ℝ} (hqb : ∀ z, |q z| ≤ B) :
    ∫ z, (∑' n, a n * u n z) * q z ∂ν = ∑' n, a n * ∫ z, u n z * q z ∂ν := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hqb (Classical.choice (by
    haveI : NeZero ν := inferInstance
    exact (MeasureTheory.Measure.nonempty_of_neZero ν))))
  have hint : ∀ n, Integrable (fun z => a n * u n z * q z) ν := fun n =>
    Integrable.of_bound (((hum n).const_mul _).mul hqm).aestronglyMeasurable (|a n| * B)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := hub n z
        have h2 := hqb z
        have : |a n| * |u n z| ≤ |a n| := by nlinarith [abs_nonneg (a n)]
        nlinarith [abs_nonneg (a n), abs_nonneg (u n z), abs_nonneg (q z)])
  have hsum : Summable fun n => ∫ z, ‖a n * u n z * q z‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun z => norm_nonneg _) (fun n => ?_)
      (ha.mul_right B)
    have : ∫ z, ‖a n * u n z * q z‖ ∂ν ≤ ∫ _z, |a n| * B ∂ν := by
      refine integral_mono (hint n).norm (integrable_const _) fun z => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have h1 := hub n z
      have h2 := hqb z
      have : |a n| * |u n z| ≤ |a n| := by nlinarith [abs_nonneg (a n)]
      nlinarith [abs_nonneg (a n), abs_nonneg (u n z), abs_nonneg (q z)]
    simpa using this
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have e1 : ∀ z, ∑' n, a n * u n z * q z = (∑' n, a n * u n z) * q z := fun z => tsum_mul_right
  simp_rw [e1] at h
  rw [← h]
  refine tsum_congr fun n => ?_
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

/-- `Re χ_n(x - z) = C_n(x) C_n(z) + S_n(x) S_n(z)`. -/
theorem torusChar_sub_re (d : ℕ) (n : Fin d → ℤ) (x z : FlatTorus d) :
    (torusChar d n (x - z)).re
      = (torusChar d n x).re * (torusChar d n z).re + (torusChar d n x).im * (torusChar d n z).im := by
  have h := torusMode_kernel d n x z
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  simp only [torusMode] at h
  linear_combination (-1 / 2 : ℝ) * h + (1 / 2 : ℝ) * ((torusChar d n x).re * (torusChar d n z).re
    + (torusChar d n x).im * (torusChar d n z).im) * h22

/-- A cosine series on the flat torus with absolutely summable coefficients. -/
noncomputable def cosSeries (d : ℕ) (a : (Fin d → ℤ) → ℝ) (x : FlatTorus d) : ℝ :=
  ∑' n, a n * (torusChar d n x).re

/-- A cosine series with absolutely summable coefficients is continuous. -/
theorem cosSeries_continuous (d : ℕ) (a : (Fin d → ℤ) → ℝ) (ha : Summable fun n => |a n|) :
    Continuous (cosSeries d a) := by
  unfold cosSeries
  refine continuous_tsum (fun n => continuous_const.mul
    (Complex.continuous_re.comp (torusChar_continuous d n))) ha fun n x => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have := (Complex.abs_re_le_norm (torusChar d n x)).trans (torusChar_norm d n x).le
  nlinarith [abs_nonneg (a n)]

/-- Its supremum is at most the sum of the absolute coefficients. -/
theorem cosSeries_abs_le (d : ℕ) (a : (Fin d → ℤ) → ℝ) (ha : Summable fun n => |a n|)
    (x : FlatTorus d) : |cosSeries d a x| ≤ ∑' n, |a n| := by
  unfold cosSeries
  have hb : ∀ n, |a n * (torusChar d n x).re| ≤ |a n| := fun n => by
    rw [abs_mul]
    have := (Complex.abs_re_le_norm (torusChar d n x)).trans (torusChar_norm d n x).le
    nlinarith [abs_nonneg (a n)]
  have hs : Summable fun n => |a n * (torusChar d n x).re| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hb ha
  have h1 : |∑' n, a n * (torusChar d n x).re| ≤ ∑' n, |a n * (torusChar d n x).re| := by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun n => a n * (torusChar d n x).re)
      (by simpa [Real.norm_eq_abs] using hs)
  exact h1.trans (hs.tsum_le_tsum hb ha)


/-- Fourier coefficients of a cosine series with symmetric coefficients. -/
theorem cosSeries_coeff (d : ℕ) (b : (Fin d → ℤ) → ℝ) (hb : Summable fun n => |b n|)
    (hsym : ∀ n, b (-n) = b n) (n : Fin d → ℤ) :
    ∫ z, (torusChar d n z).re * cosSeries d b z ∂flatTorusMeasure d = b n ∧
    ∫ z, (torusChar d n z).im * cosSeries d b z ∂flatTorusMeasure d = 0 := by
  have hCm : ∀ k : Fin d → ℤ, Measurable fun x : FlatTorus d => (torusChar d k x).re := fun k =>
    (Complex.continuous_re.comp (torusChar_continuous d k)).measurable
  have hSm : ∀ k : Fin d → ℤ, Measurable fun x : FlatTorus d => (torusChar d k x).im := fun k =>
    (Complex.continuous_im.comp (torusChar_continuous d k)).measurable
  have hCb : ∀ (k : Fin d → ℤ) (x : FlatTorus d), |(torusChar d k x).re| ≤ 1 := fun k x =>
    (Complex.abs_re_le_norm _).trans (torusChar_norm d k x).le
  have hSb : ∀ (k : Fin d → ℤ) (x : FlatTorus d), |(torusChar d k x).im| ≤ 1 := fun k x =>
    (Complex.abs_im_le_norm _).trans (torusChar_norm d k x).le
  constructor
  · have h := series_kernel_integral (flatTorusMeasure d) b hb (fun m z => (torusChar d m z).re)
      hCm hCb (fun z => (torusChar d n z).re) (hCm n) (B := 1) (hCb n)
    have e : (fun z => (torusChar d n z).re * cosSeries d b z)
        = fun z => (∑' m, b m * (torusChar d m z).re) * (torusChar d n z).re := by
      funext z; unfold cosSeries; ring
    rw [e, h]
    have hterm : ∀ m, b m * ∫ z, (torusChar d m z).re * (torusChar d n z).re ∂flatTorusMeasure d
        = (if m = n then b n / 2 else 0) + (if m = -n then b n / 2 else 0) := by
      intro m
      rw [(flatTorus_mode_products d m n).1]
      by_cases h1 : m = n <;> by_cases h2 : m = -n
      · subst h1; simp [h2.symm ▸ (by simp : m + -m = 0)]; rw [← h2] ; ring_nf; simp; ring
      · subst h1
        have : m + m ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
        simp [this, h2]; ring
      · subst h2
        have : -n - n ≠ 0 := fun h => h1 (sub_eq_zero.mp h)
        simp [this, h1, hsym]; ring
      · have a1 : m - n ≠ 0 := sub_ne_zero.mpr h1
        have a2 : m + n ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
        simp [a1, a2, h1, h2]
    simp_rw [hterm]
    rw [Summable.tsum_add (summable_of_ne_finset_zero (s := {n}) (fun m hm => by simp at hm; simp [hm]))
      (summable_of_ne_finset_zero (s := {-n}) (fun m hm => by simp at hm; simp [hm])),
      tsum_ite_eq, tsum_ite_eq]
    ring
  · have h := series_kernel_integral (flatTorusMeasure d) b hb (fun m z => (torusChar d m z).re)
      hCm hCb (fun z => (torusChar d n z).im) (hSm n) (B := 1) (hSb n)
    have e : (fun z => (torusChar d n z).im * cosSeries d b z)
        = fun z => (∑' m, b m * (torusChar d m z).re) * (torusChar d n z).im := by
      funext z; unfold cosSeries; ring
    rw [e, h]
    simp [(flatTorus_mode_products d _ n).2.2]


/-- **Convolution of cosine series on the flat torus multiplies the coefficients.** -/
theorem cosSeries_conv (d : ℕ) (a b : (Fin d → ℤ) → ℝ) (ha : Summable fun n => |a n|)
    (hb : Summable fun n => |b n|) (hsym : ∀ n, b (-n) = b n) (x : FlatTorus d) :
    ∫ z, cosSeries d a (x - z) * cosSeries d b z ∂flatTorusMeasure d
      = cosSeries d (fun n => a n * b n) x := by
  have hqc := cosSeries_continuous d b hb
  have hCc : ∀ k : Fin d → ℤ, Continuous fun z : FlatTorus d => (torusChar d k z).re := fun k =>
    Complex.continuous_re.comp (torusChar_continuous d k)
  have hSc : ∀ k : Fin d → ℤ, Continuous fun z : FlatTorus d => (torusChar d k z).im := fun k =>
    Complex.continuous_im.comp (torusChar_continuous d k)
  have h := series_kernel_integral (flatTorusMeasure d) a ha
    (fun n z => (torusChar d n (x - z)).re)
    (fun n => ((hCc n).comp (continuous_const.sub continuous_id)).measurable)
    (fun n z => (Complex.abs_re_le_norm _).trans (torusChar_norm d n _).le)
    (cosSeries d b) hqc.measurable (B := ∑' n, |b n|) (cosSeries_abs_le d b hb)
  have e : (fun z => cosSeries d a (x - z) * cosSeries d b z)
      = fun z => (∑' n, a n * (torusChar d n (x - z)).re) * cosSeries d b z := rfl
  rw [e, h]
  unfold cosSeries
  refine tsum_congr fun n => ?_
  have hint : ∀ (f : FlatTorus d → ℝ), Continuous f →
      Integrable (fun z => f z * cosSeries d b z) (flatTorusMeasure d) := fun f hf =>
    (hf.mul hqc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have e2 : (fun z => (torusChar d n (x - z)).re * cosSeries d b z)
      = fun z => (torusChar d n x).re * ((torusChar d n z).re * cosSeries d b z)
          + (torusChar d n x).im * ((torusChar d n z).im * cosSeries d b z) := by
    funext z; rw [torusChar_sub_re]; ring
  have hc := cosSeries_coeff d b hb hsym n
  unfold cosSeries at hc hint e2
  rw [e2, integral_add ((hint _ (hCc n)).const_mul _) ((hint _ (hSc n)).const_mul _),
    integral_const_mul, integral_const_mul, hc.1, hc.2]
  ring

/-- Value at the origin. -/
theorem cosSeries_zero (d : ℕ) (a : (Fin d → ℤ) → ℝ) : cosSeries d a 0 = ∑' n, a n := by
  unfold cosSeries
  refine tsum_congr fun n => ?_
  have : torusChar d n 0 = 1 := by simp [torusChar]
  rw [this]; simp

/-- The heat kernel of the flat torus in its Fourier form, `p(x) = ∑_n e^{-c|n|²} Re χ_n(x)`
    (`c = 2π² t` for the time `t` of the paper). -/
noncomputable def heatTorus (d : ℕ) (c : ℝ) : FlatTorus d → ℝ :=
  cosSeries d fun n => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)

/-! ### Bernstein's inequality -/

/-- Moment generating function of a bounded centred variable: if `|X| ≤ b`, `E X = 0` and
    `0 ≤ t ≤ 1/b`, then `E e^{tX} ≤ exp(t^2 E X^2)`. Uses `|e^x - 1 - x| ≤ x^2` for `|x| ≤ 1`. -/
theorem bernstein_mgf_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hm : Measurable X) {b t : ℝ}
    (hX : ∀ ω, |X ω| ≤ b) (hmean : μ[X] = 0) (ht0 : 0 ≤ t) (ht : t * b ≤ 1) :
    mgf X μ t ≤ Real.exp (t ^ 2 * ∫ ω, X ω ^ 2 ∂μ) := by
  have hintX : Integrable X μ :=
    Integrable.of_bound hm.aestronglyMeasurable b (Filter.Eventually.of_forall (fun ω => by simpa using hX ω))
  have hintX2 : Integrable (fun ω => X ω ^ 2) μ :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (b ^ 2)
      (Filter.Eventually.of_forall (fun ω => by
        simp only [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hX ω) 2))
  have hpt : ∀ ω, Real.exp (t * X ω) ≤ 1 + t * X ω + t ^ 2 * X ω ^ 2 := by
    intro ω
    have h1 : |t * X ω| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht0]
      exact (mul_le_mul_of_nonneg_left (hX ω) ht0).trans ht
    have h2 := Real.abs_exp_sub_one_sub_id_le h1
    have h3 := (abs_le.mp h2).2
    nlinarith [h3]
  have hintE : Integrable (fun ω => Real.exp (t * X ω)) μ :=
    Integrable.of_bound ((hm.const_mul t).exp).aestronglyMeasurable (Real.exp 1)
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have h1 : |t * X ω| ≤ 1 := by
          rw [abs_mul, abs_of_nonneg ht0]
          exact (mul_le_mul_of_nonneg_left (hX ω) ht0).trans ht
        exact (le_abs_self _).trans h1))
  have hintR : Integrable (fun ω => 1 + t * X ω + t ^ 2 * X ω ^ 2) μ :=
    ((integrable_const 1).add (hintX.const_mul t)).add (hintX2.const_mul (t ^ 2))
  calc mgf X μ t = ∫ ω, Real.exp (t * X ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 + t * X ω + t ^ 2 * X ω ^ 2) ∂μ := integral_mono hintE hintR hpt
    _ = 1 + t ^ 2 * ∫ ω, X ω ^ 2 ∂μ := by
        have e1 : ∫ ω, (1 + t * X ω + t ^ 2 * X ω ^ 2) ∂μ
            = ∫ ω, (1 + t * X ω) ∂μ + ∫ ω, t ^ 2 * X ω ^ 2 ∂μ :=
          integral_add (f := fun ω => 1 + t * X ω) (g := fun ω => t ^ 2 * X ω ^ 2)
            ((integrable_const 1).add (hintX.const_mul t)) (hintX2.const_mul (t ^ 2))
        have e2 : ∫ ω, (1 + t * X ω) ∂μ = ∫ _ω, (1 : ℝ) ∂μ + ∫ ω, t * X ω ∂μ :=
          integral_add (f := fun _ => (1 : ℝ)) (g := fun ω => t * X ω)
            (integrable_const 1) (hintX.const_mul t)
        rw [e1, e2, integral_const_mul, integral_const_mul, hmean]
        simp
    _ ≤ Real.exp (t ^ 2 * ∫ ω, X ω ^ 2 ∂μ) := by
        have := Real.add_one_le_exp (t ^ 2 * ∫ ω, X ω ^ 2 ∂μ); linarith

/-- **An inequality of Bernstein type**, proven here because the library has none (search of
    18 November 2026): for independent centred random variables with `|X_i| ≤ b` and
    `sum E X_i^2 ≤ V`, and `eps > 0`,
    `P(sum X_i ≥ eps) ≤ exp(-eps^2 / (4V + 2 b eps))`.
    The classical inequality has `2V + (2/3) b eps` in the denominator; the constants here are
    weaker by a factor of at most three, the dependence on the variance and on `b` is the same.
    This is what Lemma "consistency" uses. -/
theorem bernstein_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} (X : ι → Ω → ℝ) (h_indep : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (s : Finset ι) {b V ε : ℝ} (hb : 0 < b)
    (hX : ∀ i ∈ s, ∀ ω, |X i ω| ≤ b) (hmean : ∀ i ∈ s, μ[X i] = 0)
    (hV : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ ≤ V) (hε : 0 < ε) :
    μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-ε ^ 2 / (4 * V + 2 * b * ε)) := by
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg (fun i _ => integral_nonneg (fun ω => _root_.sq_nonneg _))) hV
  set D := 2 * V + b * ε with hD
  have hDpos : 0 < D := by positivity
  set t := ε / D with ht
  have ht0 : 0 ≤ t := by positivity
  have htb : t * b ≤ 1 := by
    rw [ht, div_mul_eq_mul_div, div_le_one hDpos]; nlinarith
  -- mgf of the sum
  have hmgf : mgf (∑ i ∈ s, X i) μ t ≤ Real.exp (t ^ 2 * V) := by
    rw [h_indep.mgf_sum hm s]
    calc ∏ i ∈ s, mgf (X i) μ t ≤ ∏ i ∈ s, Real.exp (t ^ 2 * ∫ ω, X i ω ^ 2 ∂μ) :=
          Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i hi =>
            bernstein_mgf_le (X i) (hm i) (hX i hi) (hmean i hi) ht0 htb)
      _ = Real.exp (t ^ 2 * ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ) := by
          rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (t ^ 2 * V) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hV (_root_.sq_nonneg t))
  -- integrability of exp (t * sum)
  have hbound : ∀ ω, |t * (∑ i ∈ s, X i) ω| ≤ t * (s.card * b) := by
    intro ω
    rw [abs_mul, abs_of_nonneg ht0, Finset.sum_apply]
    refine mul_le_mul_of_nonneg_left ?_ ht0
    calc |∑ i ∈ s, X i ω| ≤ ∑ i ∈ s, |X i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, b := Finset.sum_le_sum (fun i hi => hX i hi ω)
      _ = s.card * b := by simp
  have hmeas : Measurable (∑ i ∈ s, X i) := by
    have h := Finset.measurable_sum s (fun i (_ : i ∈ s) => hm i)
    have e : (∑ i ∈ s, X i) = fun a => ∑ i ∈ s, X i a := by ext a; simp
    rw [e]; exact h
  have hint : Integrable (fun ω => Real.exp (t * (∑ i ∈ s, X i) ω)) μ :=
    Integrable.of_bound ((hmeas.const_mul t).exp).aestronglyMeasurable
      (Real.exp (t * (s.card * b))) (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hbound ω))))
  have hch := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i ∈ s, X i) ε ht0 hint
  have hset : {ω | ε ≤ (∑ i ∈ s, X i) ω} = {ω | ε ≤ ∑ i ∈ s, X i ω} := by
    ext ω; simp
  rw [hset] at hch
  calc μ.real {ω | ε ≤ ∑ i ∈ s, X i ω} ≤ Real.exp (-t * ε) * mgf (∑ i ∈ s, X i) μ t := hch
    _ ≤ Real.exp (-t * ε) * Real.exp (t ^ 2 * V) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-t * ε + t ^ 2 * V) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-ε ^ 2 / (4 * V + 2 * b * ε)) := by
        apply Real.exp_le_exp.mpr
        have e1 : -t * ε + t ^ 2 * V = -(ε ^ 2 / D) + ε ^ 2 * V / D ^ 2 := by
          rw [ht]; field_simp
        have e2 : -ε ^ 2 / (4 * V + 2 * b * ε) = -(ε ^ 2 / (2 * D)) := by
          rw [hD]; ring_nf
        rw [e1, e2]
        have h1 : ε ^ 2 * V / D ^ 2 ≤ ε ^ 2 / (2 * D) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : 2 * V ≤ D := by rw [hD]; nlinarith
          nlinarith [mul_nonneg (mul_nonneg (_root_.sq_nonneg ε) hDpos.le) (sub_nonneg.mpr this)]
        have h2 : ε ^ 2 / D = 2 * (ε ^ 2 / (2 * D)) := by field_simp
        linarith

/-- Bernstein for independent variables with values in `[0, b]` and a common mean `m`, two-sided:
    `P(|sum_{j<N} Y_j - N m| ≥ eps) ≤ 2 exp(-eps^2 / (4 N b m + 2 b eps))`. The variance of each
    variable is at most `b m`, which is what makes the bound depend on the mean. -/
theorem bernstein_bounded_mean {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℝ) (h_indep : iIndepFun Y μ)
    (hm : ∀ j, Measurable (Y j)) {b m ε : ℝ} (hb : 0 < b)
    (h0 : ∀ j ω, 0 ≤ Y j ω) (hYb : ∀ j ω, Y j ω ≤ b) (hmean : ∀ j, μ[Y j] = m)
    (N : ℕ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, Y j ω - N * m|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (N * (b * m)) + 2 * b * ε)) := by
  have hintY : ∀ j, Integrable (Y j) μ := fun j =>
    Integrable.of_bound (hm j).aestronglyMeasurable b (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 j ω)]; exact hYb j ω))
  have hm0 : 0 ≤ m := by rw [← hmean 0]; exact integral_nonneg (h0 0)
  have hmb : m ≤ b := by
    rw [← hmean 0]
    calc ∫ ω, Y 0 ω ∂μ ≤ ∫ _ω, b ∂μ := integral_mono (hintY 0) (integrable_const b) (hYb 0)
      _ = b := by simp
  -- centred variables
  have habs : ∀ j ω, |Y j ω - m| ≤ b := by
    intro j ω
    rw [abs_le]; constructor <;> linarith [h0 j ω, hYb j ω]
  have hvar : ∀ j, ∫ ω, (Y j ω - m) ^ 2 ∂μ ≤ b * m := by
    intro j
    have hpt : ∀ ω, (Y j ω - m) ^ 2 ≤ (b - 2 * m) * Y j ω + m ^ 2 := by
      intro ω
      nlinarith [mul_nonneg (h0 j ω) (sub_nonneg.mpr (hYb j ω))]
    have hint2 : Integrable (fun ω => (Y j ω - m) ^ 2) μ :=
      Integrable.of_bound (((hm j).sub_const m).pow_const 2).aestronglyMeasurable (b ^ 2)
        (Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (habs j ω) 2))
    have hint3 : Integrable (fun ω => (b - 2 * m) * Y j ω + m ^ 2) μ :=
      ((hintY j).const_mul _).add (integrable_const _)
    calc ∫ ω, (Y j ω - m) ^ 2 ∂μ ≤ ∫ ω, ((b - 2 * m) * Y j ω + m ^ 2) ∂μ :=
          integral_mono hint2 hint3 hpt
      _ = (b - 2 * m) * m + m ^ 2 := by
          rw [integral_add (f := fun ω => (b - 2 * m) * Y j ω) (g := fun _ => m ^ 2)
            ((hintY j).const_mul _) (integrable_const _), integral_const_mul, hmean j]
          simp
      _ ≤ b * m := by nlinarith
  have hV : ∀ (sgn : ℝ), sgn ^ 2 = 1 →
      ∑ j ∈ Finset.range N, ∫ ω, (sgn * (Y j ω - m)) ^ 2 ∂μ ≤ N * (b * m) := by
    intro sgn hs
    calc ∑ j ∈ Finset.range N, ∫ ω, (sgn * (Y j ω - m)) ^ 2 ∂μ
        = ∑ j ∈ Finset.range N, ∫ ω, (Y j ω - m) ^ 2 ∂μ :=
          Finset.sum_congr rfl (fun j _ => by
            congr 1; funext ω; rw [mul_pow, hs, one_mul])
      _ ≤ ∑ _j ∈ Finset.range N, b * m := Finset.sum_le_sum (fun j _ => hvar j)
      _ = N * (b * m) := by simp
  have side : ∀ (sgn : ℝ), sgn ^ 2 = 1 → |sgn| = 1 →
      μ.real {ω | ε ≤ ∑ j ∈ Finset.range N, sgn * (Y j ω - m)}
        ≤ Real.exp (-ε ^ 2 / (4 * (N * (b * m)) + 2 * b * ε)) := by
    intro sgn hs habs1
    have hind : iIndepFun (fun j ω => sgn * (Y j ω - m)) μ :=
      h_indep.comp (fun _ y => sgn * (y - m)) (fun _ => (measurable_id.sub_const m).const_mul sgn)
    exact bernstein_inequality (μ := μ) (fun j ω => sgn * (Y j ω - m)) hind
      (fun j => ((hm j).sub_const m).const_mul sgn) (Finset.range N) hb
      (fun j _ ω => by rw [abs_mul, habs1, one_mul]; exact habs j ω)
      (fun j _ => by
        rw [integral_const_mul, integral_sub (hintY j) (integrable_const m), hmean j]; simp)
      (hV sgn hs) hε
  have h1 := side 1 (by norm_num) (by norm_num)
  have h2 := side (-1) (by norm_num) (by norm_num)
  have hsub : {ω | ε ≤ |∑ j ∈ Finset.range N, Y j ω - N * m|}
      ⊆ {ω | ε ≤ ∑ j ∈ Finset.range N, (1 : ℝ) * (Y j ω - m)}
        ∪ {ω | ε ≤ ∑ j ∈ Finset.range N, (-1 : ℝ) * (Y j ω - m)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have e1 : ∑ j ∈ Finset.range N, (1 : ℝ) * (Y j ω - m) = ∑ j ∈ Finset.range N, Y j ω - N * m := by
      simp [Finset.sum_sub_distrib]
    have e2 : ∑ j ∈ Finset.range N, (-1 : ℝ) * (Y j ω - m)
        = -(∑ j ∈ Finset.range N, Y j ω - N * m) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]; simp
    rw [e1, e2]
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, Y j ω - N * m|}
      ≤ μ.real ({ω | ε ≤ ∑ j ∈ Finset.range N, (1 : ℝ) * (Y j ω - m)}
        ∪ {ω | ε ≤ ∑ j ∈ Finset.range N, (-1 : ℝ) * (Y j ω - m)}) := measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

/-- **Lemma "consistency", the main term at fixed points.** For independent points `X_j` of a group
    and kernels `0 ≤ f ≤ bf`, `0 ≤ g ≤ bg`, the sum `sum_{j<N} f(x - X_j) g(X_j - y)` deviates from
    `N c` by `eps` or more with probability at most `2 exp(-eps^2 / (4 N bf bg c + 2 bf bg eps))`,
    where `c = E f(x - X_j) g(X_j - y)` (HYPOTHESIS `hmean`; for the heat kernel on a torus
    `f = p`, `g = p_m` and `c = p_{m+1}(x - y)` by the semigroup property, which is not
    formalised). With `bf = M`, `bg = m_m` this is the bound of the paper for the walk with the
    exact normalisation at fixed `(b, i, m)`. NOT covered: the normalisation errors (the part with
    the Poincaré inequality), the sample points in place of fixed points, and the union over
    `(b, i, m)`. -/
theorem transported_kernel_concentration {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddGroup G] [MeasurableSpace G]
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (f g : G → ℝ) (x y : G) (hF : Measurable (fun z : G => f (x - z) * g (z - y)))
    {bf bg c ε : ℝ} (hbf : 0 < bf) (hbg : 0 < bg)
    (hf0 : ∀ u, 0 ≤ f u) (hfb : ∀ u, f u ≤ bf) (hg0 : ∀ u, 0 ≤ g u) (hgb : ∀ u, g u ≤ bg)
    (hmean : ∀ j, μ[fun ω => f (x - X j ω) * g (X j ω - y)] = c) (N : ℕ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, f (x - X j ω) * g (X j ω - y) - N * c|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (N * (bf * bg * c)) + 2 * (bf * bg) * ε)) :=
  bernstein_bounded_mean (μ := μ) (fun j ω => f (x - X j ω) * g (X j ω - y))
    (h_indep.comp (fun _ z => f (x - z) * g (z - y)) (fun _ => hF))
    (fun j => hF.comp (hX j)) (mul_pos hbf hbg)
    (fun j ω => mul_nonneg (hf0 _) (hg0 _))
    (fun j ω => mul_le_mul (hfb _) (hgb _) (hg0 _) hbf.le) hmean N hε

/-- Convolution powers of a kernel `p` on a group with respect to a measure `ν`:
    `convPow ν p m = p^{*(m+1)}`. For the heat kernel at time `sigma` on a torus this is the heat
    kernel at time `(m+1) sigma`; the semigroup property then holds by definition. -/
noncomputable def convPow {G : Type*} [AddCommGroup G] [MeasurableSpace G] (ν : Measure G)
    (p : G → ℝ) : ℕ → G → ℝ
  | 0 => p
  | m + 1 => fun u => ∫ w, p (u - w) * convPow ν p m w ∂ν

/-- The convolution powers of a nonnegative kernel are nonnegative. -/
theorem convPow_nonneg {G : Type*} [AddCommGroup G] [MeasurableSpace G] (ν : Measure G)
    (p : G → ℝ) (hp0 : ∀ u, 0 ≤ p u) : ∀ m u, 0 ≤ convPow ν p m u
  | 0, u => hp0 u
  | m + 1, u => integral_nonneg (fun w => mul_nonneg (hp0 _) (convPow_nonneg ν p hp0 m w))

/-- The supremum of the convolution powers does not increase (fact (P1) of Lemma "periodised
    Gaussian" in its qualitative form, `m_{k+1} ≤ m_k`): for a nonnegative kernel of mass one with
    respect to an invariant finite measure, `p^{*(m+1)} ≤ B` implies `p^{*(m+2)} ≤ B`.
    HYPOTHESIS `hqmeas`: measurability of `p^{*(m+1)}` (true for continuous kernels). -/
theorem convPow_succ_le {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableNeg G] (ν : Measure G) [IsFiniteMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (p : G → ℝ) (hp0 : ∀ u, 0 ≤ p u) (hpint : Integrable p ν) (hmass : ∫ u, p u ∂ν = 1)
    (m : ℕ) {B : ℝ} (hqB : ∀ u, convPow ν p m u ≤ B)
    (hqmeas : AEStronglyMeasurable (convPow ν p m) ν) (u : G) :
    convPow ν p (m + 1) u ≤ B := by
  have hq0 := convPow_nonneg ν p hp0 m
  have hB0 : 0 ≤ B := (hq0 u).trans (hqB u)
  have hpu : Integrable (fun w => p (u - w)) ν := hpint.comp_sub_left u
  have hI : Integrable (fun w => convPow ν p m w * p (u - w)) ν :=
    hpu.bdd_mul (c := B) hqmeas (Filter.Eventually.of_forall (fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 w)]; exact hqB w))
  have hI' : Integrable (fun w => p (u - w) * convPow ν p m w) ν := by
    simpa [mul_comm] using hI
  calc convPow ν p (m + 1) u = ∫ w, p (u - w) * convPow ν p m w ∂ν := rfl
    _ ≤ ∫ w, p (u - w) * B ∂ν := integral_mono hI' (hpu.mul_const B)
        (fun w => mul_le_mul_of_nonneg_left (hqB w) (hp0 _))
    _ = B := by
        rw [integral_mul_const, integral_sub_left_eq_self p ν u, hmass, one_mul]

/-- The convolution powers of a Lipschitz kernel are Lipschitz: if `p` is `L`-Lipschitz for a
    translation-invariant metric and `p^{*(m+1)} ≤ B`, then `p^{*(m+2)}` is `L B`-Lipschitz.
    HYPOTHESIS `hqmeas`: measurability of `p^{*(m+1)}`. -/
theorem convPow_succ_lipschitz {G : Type*} [AddCommGroup G] [PseudoMetricSpace G]
    [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G] (ν : Measure G)
    [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (p : G → ℝ) (hp0 : ∀ u, 0 ≤ p u) (hpint : Integrable p ν) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ u u', |p u - p u'| ≤ L * dist u u')
    (m : ℕ) {B : ℝ} (hqB : ∀ u, convPow ν p m u ≤ B)
    (hqmeas : AEStronglyMeasurable (convPow ν p m) ν) (u u' : G) :
    |convPow ν p (m + 1) u - convPow ν p (m + 1) u'| ≤ L * B * dist u u' := by
  have hq0 := convPow_nonneg ν p hp0 m
  have hB0 : 0 ≤ B := (hq0 u).trans (hqB u)
  have hI : ∀ v : G, Integrable (fun w => p (v - w) * convPow ν p m w) ν := by
    intro v
    have h1 : Integrable (fun w => convPow ν p m w * p (v - w)) ν :=
      (hpint.comp_sub_left v).bdd_mul (c := B) hqmeas (Filter.Eventually.of_forall (fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hq0 w)]; exact hqB w))
    simpa [mul_comm] using h1
  have e : convPow ν p (m + 1) u - convPow ν p (m + 1) u'
      = ∫ w, (p (u - w) - p (u' - w)) * convPow ν p m w ∂ν := by
    show ∫ w, p (u - w) * convPow ν p m w ∂ν - ∫ w, p (u' - w) * convPow ν p m w ∂ν = _
    rw [← integral_sub (hI u) (hI u')]
    congr 1; funext w; ring
  rw [e]
  have hbound : ∀ w, ‖(p (u - w) - p (u' - w)) * convPow ν p m w‖ ≤ L * B * dist u u' := by
    intro w
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 w)]
    have h1 := hlip (u - w) (u' - w)
    rw [hdist u u' w] at h1
    calc |p (u - w) - p (u' - w)| * convPow ν p m w ≤ (L * dist u u') * B :=
          mul_le_mul h1 (hqB w) (hq0 w) (mul_nonneg hL dist_nonneg)
      _ = L * B * dist u u' := by ring
  have h := norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall hbound)
  simpa [Real.norm_eq_abs] using h

/-- All convolution powers of a measurable kernel are measurable. -/
theorem convPow_measurable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G]
    (ν : Measure G) [SFinite ν] (p : G → ℝ) (hp : Measurable p) :
    ∀ m, Measurable (convPow ν p m)
  | 0 => hp
  | m + 1 => by
    have ih := convPow_measurable ν p hp m
    have hF : Measurable (fun z : G × G => p (z.1 - z.2) * convPow ν p m z.2) :=
      (hp.comp (measurable_fst.sub measurable_snd)).mul (ih.comp measurable_snd)
    exact (hF.stronglyMeasurable.integral_prod_right').measurable

/-- All convolution powers of a kernel of mass one with `0 ≤ p ≤ M` are at most `M`
    (fact (P1) in its qualitative form, without the decay in `m`). -/
theorem convPow_le_all {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    [MeasurableSub₂ G] [MeasurableNeg G] (ν : Measure G) [IsFiniteMeasure ν]
    [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (p : G → ℝ) (hp : Measurable p) (hp0 : ∀ u, 0 ≤ p u) {M : ℝ} (hpM : ∀ u, p u ≤ M)
    (hpint : Integrable p ν) (hmass : ∫ u, p u ∂ν = 1) : ∀ m u, convPow ν p m u ≤ M
  | 0, u => hpM u
  | m + 1, u => convPow_succ_le ν p hp0 hpint hmass m (convPow_le_all ν p hp hp0 hpM hpint hmass m)
      (convPow_measurable ν p hp m).aestronglyMeasurable u

/-- All convolution powers of an `L`-Lipschitz kernel of mass one with `0 ≤ p ≤ M` are
    `L max(1, M)`-Lipschitz. -/
theorem convPow_lipschitz_all {G : Type*} [AddCommGroup G] [PseudoMetricSpace G]
    [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableSub₂ G] [MeasurableNeg G] (ν : Measure G)
    [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (p : G → ℝ) (hp : Measurable p) (hp0 : ∀ u, 0 ≤ p u) {M L : ℝ} (hpM : ∀ u, p u ≤ M)
    (hpint : Integrable p ν) (hmass : ∫ u, p u ∂ν = 1) (hL : 0 ≤ L)
    (hlip : ∀ u u', |p u - p u'| ≤ L * dist u u') (m : ℕ) (u u' : G) :
    |convPow ν p m u - convPow ν p m u'| ≤ L * max 1 M * dist u u' := by
  have hd : 0 ≤ dist u u' := dist_nonneg
  cases m with
  | zero =>
    calc |convPow ν p 0 u - convPow ν p 0 u'| = |p u - p u'| := rfl
      _ ≤ L * dist u u' := hlip u u'
      _ = L * 1 * dist u u' := by ring
      _ ≤ L * max 1 M * dist u u' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) hL) hd
  | succ m =>
    calc |convPow ν p (m + 1) u - convPow ν p (m + 1) u'| ≤ L * M * dist u u' :=
          convPow_succ_lipschitz ν hdist p hp0 hpint hL hlip m
            (convPow_le_all ν p hp hp0 hpM hpint hmass m)
            (convPow_measurable ν p hp m).aestronglyMeasurable u u'
      _ ≤ L * max 1 M * dist u u' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right _ _) hL) hd

/-- The semigroup property in the form used by Lemma "consistency": for a point `X` with law `ν`
    (translation invariant), `E p(x - X) p^{*(m+1)}(X - y) = p^{*(m+2)}(x - y)`. -/
theorem transported_mean {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (ν : Measure G) [ν.IsAddRightInvariant]
    (X : Ω → G) (hX : Measurable X) (hlaw : μ.map X = ν) (p : G → ℝ) (m : ℕ) (x y : G)
    (hF : Measurable (fun z : G => p (x - z) * convPow ν p m (z - y))) :
    μ[fun ω => p (x - X ω) * convPow ν p m (X ω - y)] = convPow ν p (m + 1) (x - y) := by
  have h1 : ∫ ω, p (x - X ω) * convPow ν p m (X ω - y) ∂μ
      = ∫ z, p (x - z) * convPow ν p m (z - y) ∂(μ.map X) :=
    (integral_map hX.aemeasurable hF.aestronglyMeasurable).symm
  rw [h1, hlaw]
  have h2 := integral_add_right_eq_self (μ := ν) (fun z => p (x - z) * convPow ν p m (z - y)) y
  rw [← h2]
  show ∫ w, p (x - (w + y)) * convPow ν p m (w + y - y) ∂ν = ∫ w, p (x - y - w) * convPow ν p m w ∂ν
  congr 1
  funext w
  rw [add_sub_cancel_right, sub_add_eq_sub_sub, sub_right_comm]

/-- **Lemma "consistency", the main term at fixed points, without a hypothesis on the mean.**
    Independent points with a translation-invariant law `ν` on a commutative group; a kernel
    `0 ≤ p ≤ M` and `0 ≤ p^{*(m+1)} ≤ B`. Then for fixed `x`, `y`
    `P(|sum_{j<N} p(x - X_j) p^{*(m+1)}(X_j - y) - N p^{*(m+2)}(x - y)| ≥ eps)
       ≤ 2 exp(-eps^2 / (4 N M B p^{*(m+2)}(x - y) + 2 M B eps))`.
    This is the deviation of the walk with the EXACT normalisation from the next heat kernel, at
    fixed points. HYPOTHESIS `hF`: measurability of the integrand (true for continuous kernels,
    not derived here). -/
theorem consistency_main_term {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (ν : Measure G) [ν.IsAddRightInvariant]
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (p : G → ℝ) (m : ℕ) (x y : G)
    (hF : Measurable (fun z : G => p (x - z) * convPow ν p m (z - y)))
    {M B ε : ℝ} (hM : 0 < M) (hB : 0 < B) (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M)
    (hq0 : ∀ u, 0 ≤ convPow ν p m u) (hqB : ∀ u, convPow ν p m u ≤ B) (N : ℕ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, p (x - X j ω) * convPow ν p m (X j ω - y)
        - N * convPow ν p (m + 1) (x - y)|}
      ≤ 2 * Real.exp (-ε ^ 2
          / (4 * (N * (M * B * convPow ν p (m + 1) (x - y))) + 2 * (M * B) * ε)) :=
  transported_kernel_concentration (μ := μ) X h_indep hX p (convPow ν p m) x y hF hM hB hp0 hpM
    hq0 hqB (fun j => transported_mean ν (X j) (hX j) (hlaw j) p m x y hF) N hε

/-- **Lemma "consistency" for the walk with the exact normalisation, uniformly in both points.**
    On a commutative group with a translation-invariant metric and law `ν`: for the kernel `p`
    (values in `[0, M]`, `L`-Lipschitz) and its convolution power `q = p^{*(m+1)}` (values in
    `[0, B]`, `Lq`-Lipschitz; the next power `Lq'`-Lipschitz), and a finite `r`-net of `G × G`,
    the probability that
    `|sum_{j<N} p(x - X_j) q(X_j - y) - N p^{*(m+2)}(x - y)| > eps + 2 N Lstar r` for SOME pair
    `(x, y)` is at most `2 |net| exp(-eps^2 / (2 N (M B/2)^2))`, where
    `Lstar ≥ L B + M Lq` and `Lstar ≥ 2 Lq'`. The pairs include all pairs of sample points.
    HYPOTHESES: measurability of the integrand (`hF`), the Lipschitz constants of the convolution
    powers (see `convPow_succ_lipschitz`), the net. This is a bound of Hoeffding type; it does not
    carry the variance factor of the paper's lemma. -/
theorem consistency_uniform_exact {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [PseudoMetricSpace G]
    [MeasurableSpace G] [MeasurableAdd₂ G] (ν : Measure G) [ν.IsAddRightInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (hdist2 : ∀ x y y' : G, dist (x - y) (x - y') = dist y y')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (p : G → ℝ) (m : ℕ)
    (hF : ∀ x y : G, Measurable (fun z : G => p (x - z) * convPow ν p m (z - y)))
    {M B L Lq Lq' Lstar r : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hL : 0 ≤ L) (hLq : 0 ≤ Lq)
    (hLq' : 0 ≤ Lq') (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M)
    (hq0 : ∀ u, 0 ≤ convPow ν p m u) (hqB : ∀ u, convPow ν p m u ≤ B)
    (hplip : ∀ u u', |p u - p u'| ≤ L * dist u u')
    (hqlip : ∀ u u', |convPow ν p m u - convPow ν p m u'| ≤ Lq * dist u u')
    (hq'lip : ∀ u u', |convPow ν p (m + 1) u - convPow ν p (m + 1) u'| ≤ Lq' * dist u u')
    (hL1 : L * B + M * Lq ≤ Lstar) (hL2 : 2 * Lq' ≤ Lstar)
    (net : Finset (G × G)) (hnet : ∀ t : G × G, ∃ a ∈ net, dist t a ≤ r)
    (N : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ t : G × G, ε + 2 * (N * Lstar) * r
        < |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
            - N * convPow ν p (m + 1) (t.1 - t.2)|}
      ≤ net.card * (2 * Real.exp (-ε ^ 2 / (2 * N * (M * B / 2) ^ 2))) := by
  have hLs : 0 ≤ Lstar := le_trans (by positivity) hL2
  refine uniform_concentration_param (μ := μ) (T := G × G) X h_indep hX
    (fun t z => p (t.1 - z) * convPow ν p m (z - t.2)) (fun t => hF t.1 t.2)
    (mul_nonneg hM hB) hLs
    (fun t z => ⟨mul_nonneg (hp0 _) (hq0 _), mul_le_mul (hpM _) (hqB _) (hq0 _) hM⟩)
    ?_ (fun t => convPow ν p (m + 1) (t.1 - t.2))
    (fun t j => transported_mean ν (X j) (hX j) (hlaw j) p m t.1 t.2 (hF t.1 t.2))
    ?_ net hnet N hε
  · -- Lipschitz in the parameter
    intro t t' z
    have h1 := hplip (t.1 - z) (t'.1 - z)
    rw [hdist t.1 t'.1 z] at h1
    have h2 := hqlip (z - t.2) (z - t'.2)
    rw [hdist2 z t.2 t'.2] at h2
    have hd1 : dist t.1 t'.1 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hd2 : dist t.2 t'.2 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_right _ _
    have e : p (t.1 - z) * convPow ν p m (z - t.2) - p (t'.1 - z) * convPow ν p m (z - t'.2)
        = (p (t.1 - z) - p (t'.1 - z)) * convPow ν p m (z - t.2)
          + p (t'.1 - z) * (convPow ν p m (z - t.2) - convPow ν p m (z - t'.2)) := by ring
    rw [e]
    have a1 : |(p (t.1 - z) - p (t'.1 - z)) * convPow ν p m (z - t.2)| ≤ L * dist t t' * B := by
      rw [abs_mul, abs_of_nonneg (hq0 _)]
      exact mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left hd1 hL)) (hqB _) (hq0 _)
        (mul_nonneg hL dist_nonneg)
    have a2 : |p (t'.1 - z) * (convPow ν p m (z - t.2) - convPow ν p m (z - t'.2))|
        ≤ M * (Lq * dist t t') := by
      rw [abs_mul, abs_of_nonneg (hp0 _)]
      exact mul_le_mul (hpM _) (h2.trans (mul_le_mul_of_nonneg_left hd2 hLq)) (abs_nonneg _) hM
    have a3 : (L * B + M * Lq) * dist t t' ≤ Lstar * dist t t' :=
      mul_le_mul_of_nonneg_right hL1 dist_nonneg
    calc |(p (t.1 - z) - p (t'.1 - z)) * convPow ν p m (z - t.2)
            + p (t'.1 - z) * (convPow ν p m (z - t.2) - convPow ν p m (z - t'.2))|
        ≤ L * dist t t' * B + M * (Lq * dist t t') := (abs_add_le _ _).trans (add_le_add a1 a2)
      _ = (L * B + M * Lq) * dist t t' := by ring
      _ ≤ Lstar * dist t t' := a3
  · -- Lipschitz of the mean
    intro t t'
    have hd1 : dist t.1 t'.1 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hd2 : dist t.2 t'.2 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_right _ _
    have h1 := hq'lip (t.1 - t.2) (t'.1 - t'.2)
    have htri : dist (t.1 - t.2) (t'.1 - t'.2) ≤ dist t.1 t'.1 + dist t.2 t'.2 := by
      calc dist (t.1 - t.2) (t'.1 - t'.2)
          ≤ dist (t.1 - t.2) (t'.1 - t.2) + dist (t'.1 - t.2) (t'.1 - t'.2) := dist_triangle _ _ _
        _ = dist t.1 t'.1 + dist t.2 t'.2 := by rw [hdist, hdist2]
    calc |convPow ν p (m + 1) (t.1 - t.2) - convPow ν p (m + 1) (t'.1 - t'.2)|
        ≤ Lq' * dist (t.1 - t.2) (t'.1 - t'.2) := h1
      _ ≤ Lq' * (2 * dist t t') := mul_le_mul_of_nonneg_left (by linarith) hLq'
      _ = 2 * Lq' * dist t t' := by ring
      _ ≤ Lstar * dist t t' := mul_le_mul_of_nonneg_right hL2 dist_nonneg

/-- **The kernel theorem at a fixed kernel scale, with its probability.** Points `X_j` of a
    commutative group; a kernel `p` with convolution powers `0 ≤ p^{*(m+1)} ≤ Bf m`. Let `P` be the
    walk matrix of the first `N` points with the estimated normalisation (HYPOTHESIS `hP`: its
    entries are given by the formula of the paper). Bad events: the normalisation,
    `Bn = {∃ x, |sum_j p(x - X_j) - N| > epsn}`, and for each `m < k` the consistency of the walk
    with the exact normalisation, `Bc m = {∃ (x, y), |sum_j p(x - X_j) p^{*(m+1)}(X_j - y)
    - N p^{*(m+2)}(x - y)| > epsc}`. HYPOTHESES `hBn`, `hBc`: bounds on their probabilities (these
    are the conclusions of `uniform_normalisation` and `consistency_uniform_exact`). CONCLUSION:
    with `delta = epsn/N ≤ 1/8` and `E = sum_{m<k} (3 epsc/N + 11 delta Bf (m+1))`, the probability
    that some entry violates
    `|N (P^{k+1})_{ai} - p^{*(k+1)}(X_a - X_i)| ≤ 10 delta (p^{*(k+1)}(X_a - X_i) + E) + E`
    is at most `pn + sum_{m<k} pc m`. -/
theorem kernel_fixed_scale_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {G : Type*} [AddCommGroup G] [MeasurableSpace G] (ν : Measure G)
    (X : ℕ → Ω → G) (p : G → ℝ) (Bf : ℕ → ℝ) (N : ℕ) [NeZero N] (k : ℕ)
    (hq0 : ∀ m u, 0 ≤ convPow ν p m u) (hqB : ∀ m u, convPow ν p m u ≤ Bf m)
    (P : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hP : ∀ ω b j, P ω b j
      = (p (X b ω - X j ω) / ((∑ l : Fin N, p (X j ω - X l ω)) / N))
        / ∑ l : Fin N, p (X b ω - X l ω) / ((∑ l' : Fin N, p (X l ω - X l' ω)) / N))
    {epsn epsc pn : ℝ} (pc : ℕ → ℝ) (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 8)
    (hBn : μ.real {ω | ∃ x : G, epsn < |∑ j ∈ Finset.range N, p (x - X j ω) - N|} ≤ pn)
    (hBc : ∀ m < k, μ.real {ω | ∃ t : G × G, epsc
        < |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
            - N * convPow ν p (m + 1) (t.1 - t.2)|} ≤ pc m) :
    μ.real {ω | ∃ a i : Fin N,
        10 * (epsn / N) * (convPow ν p k (X a ω - X i ω)
            + ∑ m ∈ Finset.range k, (3 * (epsc / N) + 11 * (epsn / N) * Bf (m + 1)))
          + ∑ m ∈ Finset.range k, (3 * (epsc / N) + 11 * (epsn / N) * Bf (m + 1))
        < |(N : ℝ) * (P ω ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)|}
      ≤ pn + ∑ m ∈ Finset.range k, pc m := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set Bn : Set Ω := {ω | ∃ x : G, epsn < |∑ j ∈ Finset.range N, p (x - X j ω) - N|} with hBn_def
  set Bc : ℕ → Set Ω := fun m => {ω | ∃ t : G × G, epsc
      < |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
          - N * convPow ν p (m + 1) (t.1 - t.2)|} with hBc_def
  have hsub : {ω | ∃ a i : Fin N,
        10 * (epsn / N) * (convPow ν p k (X a ω - X i ω)
            + ∑ m ∈ Finset.range k, (3 * (epsc / N) + 11 * (epsn / N) * Bf (m + 1)))
          + ∑ m ∈ Finset.range k, (3 * (epsc / N) + 11 * (epsn / N) * Bf (m + 1))
        < |(N : ℝ) * (P ω ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)|}
      ⊆ Bn ∪ ⋃ m ∈ Finset.range k, Bc m := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
    obtain ⟨hn, hc⟩ := hcon
    have hn' : ∀ x : G, |∑ j ∈ Finset.range N, p (x - X j ω) - N| ≤ epsn := by
      intro x
      by_contra h
      exact hn ⟨x, not_le.mp h⟩
    have hc' : ∀ m, m < k → ∀ t : G × G,
        |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
          - N * convPow ν p (m + 1) (t.1 - t.2)| ≤ epsc := by
      intro m hm t
      by_contra h
      exact hc m hm ⟨t, not_le.mp h⟩
    obtain ⟨a, i, hai⟩ := hω
    have key := kernel_fixed_scale_det (n := Fin N)
      (fun m b i' => convPow ν p (m - 1) (X b ω - X i' ω)) (fun m => Bf (m - 1))
      (fun _ => epsc / N) (fun b => (∑ l : Fin N, p (X b ω - X l ω)) / N) (P ω)
      (delta := epsn / N) (div_nonneg hepsn0 hNpos.le)
      (by rw [div_le_iff₀ hNpos]; linarith)
      (fun m b i' => hq0 _ _) (fun m b i' => hqB _ _)
      (fun b => by
        simp only [Fintype.card_fin]
        have : (fun l : Fin N => convPow ν p (1 - 1) (X b ω - X l ω))
            = fun l : Fin N => p (X b ω - X l ω) := rfl
        rw [this]; field_simp)
      (fun b => by
        have h := hn' (X b ω)
        rw [← Fin.sum_univ_eq_sum_range (fun j => p (X b ω - X j ω)) N] at h
        have e : (∑ l : Fin N, p (X b ω - X l ω)) / N - 1
            = (∑ l : Fin N, p (X b ω - X l ω) - N) / N := by field_simp
        rw [e, abs_div, abs_of_pos hNpos]
        exact div_le_div_of_nonneg_right h hNpos.le)
      (fun b j => hP ω b j) k
      (fun m b i' hm1 hmk => by
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have h := hc' m' (by omega) (X b ω, X i' ω)
        simp only at h
        rw [← Fin.sum_univ_eq_sum_range
          (fun j => p (X b ω - X j ω) * convPow ν p m' (X j ω - X i' ω)) N] at h
        simp only [Fintype.card_fin, Nat.add_sub_cancel]
        have e : ∑ j : Fin N, convPow ν p (1 - 1) (X b ω - X j ω) / (N : ℝ)
              * convPow ν p m' (X j ω - X i' ω) - convPow ν p (m' + 1) (X b ω - X i' ω)
            = (∑ j : Fin N, p (X b ω - X j ω) * convPow ν p m' (X j ω - X i' ω)
                - N * convPow ν p (m' + 1) (X b ω - X i' ω)) / N := by
          have : ∀ j : Fin N, convPow ν p (1 - 1) (X b ω - X j ω) = p (X b ω - X j ω) :=
            fun j => rfl
          simp_rw [this]
          rw [sub_div, Finset.sum_div]
          congr 1
          · exact Finset.sum_congr rfl (fun j _ => by ring)
          · field_simp
        rw [e, abs_div, abs_of_pos hNpos]
        exact div_le_div_of_nonneg_right h hNpos.le) a i
    simp only [Fintype.card_fin, Nat.add_sub_cancel] at key
    exact absurd hai (not_lt.mpr key)
  calc μ.real _ ≤ μ.real (Bn ∪ ⋃ m ∈ Finset.range k, Bc m) := measureReal_mono hsub
    _ ≤ μ.real Bn + μ.real (⋃ m ∈ Finset.range k, Bc m) := measureReal_union_le _ _
    _ ≤ pn + ∑ m ∈ Finset.range k, pc m := by
        refine add_le_add hBn ((measureReal_biUnion_finset_le _ _).trans ?_)
        exact Finset.sum_le_sum (fun m hm => hBc m (Finset.mem_range.mp hm))

/-- **The kernel theorem at a fixed kernel scale on a torus, without intermediate hypotheses.**
    `G` a compact abelian group with a translation-invariant metric and its invariant probability
    measure `ν`; `X_j` independent with law `ν`; `p` a measurable `L`-Lipschitz probability density
    with `0 ≤ p ≤ M`; `P` the walk matrix of the first `N` points with the estimated normalisation
    (HYPOTHESIS `hP`: the formula for its entries). For every `r > 0` and `k` there are numbers
    `M1`, `M2` (sizes of `r`-nets of `G` and of `G × G`, not quantified) such that for all `N ≥ 1`
    and `epsn, epsc ≥ 0` with `epsn + 2 N L r ≤ N/8`: with `en = epsn + 2 N L r`,
    `ec = epsc + 2 N Lstar r`, `delta = en/N` and `E = sum_{m<k} (3 ec/N + 11 delta M)`, the
    probability that some entry violates
    `|N (P^{k+1})_{ai} - p^{*(k+1)}(X_a - X_i)| ≤ 10 delta (p^{*(k+1)}(X_a - X_i) + E) + E`
    is at most `2 M1 exp(-epsn^2/(2N(M/2)^2)) + sum_{m<k} 2 M2 exp(-epsc^2/(2N(M^2/2)^2))`.
    No rate in the kernel scale is claimed, and the bound is of the weak form (see
    `defect_decomposition`). -/
theorem kernel_fixed_scale_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [MetricSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (hdist2 : ∀ x y y' : G, dist (x - y) (x - y') = dist y y')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν)
    (p : G → ℝ) (hp : Measurable p) {M L r : ℝ} (hM1 : 1 ≤ M) (hL : 0 ≤ L)
    (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (hlip : ∀ u u', |p u - p u'| ≤ L * dist u u') (hr : 0 < r) (k : ℕ) :
    ∃ M1 M2 : ℕ, ∀ (N : ℕ) [NeZero N] (P : Ω → Matrix (Fin N) (Fin N) ℝ),
      (∀ ω b j, P ω b j
        = (p (X b ω - X j ω) / ((∑ l : Fin N, p (X j ω - X l ω)) / N))
          / ∑ l : Fin N, p (X b ω - X l ω) / ((∑ l' : Fin N, p (X l ω - X l' ω)) / N)) →
      ∀ (epsn epsc : ℝ), 0 ≤ epsn → 0 ≤ epsc → epsn + 2 * (N * L) * r ≤ N / 8 →
      μ.real {ω | ∃ a i : Fin N,
          10 * ((epsn + 2 * (N * L) * r) / N) * (convPow ν p k (X a ω - X i ω)
              + ∑ m ∈ Finset.range k,
                  (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                    + 11 * ((epsn + 2 * (N * L) * r) / N) * M))
            + ∑ m ∈ Finset.range k,
                (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                  + 11 * ((epsn + 2 * (N * L) * r) / N) * M)
          < |(N : ℝ) * (P ω ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)|}
        ≤ M1 * (2 * Real.exp (-epsn ^ 2 / (2 * N * (M / 2) ^ 2)))
          + ∑ _m ∈ Finset.range k, M2 * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
  have hM0 : 0 ≤ M := by linarith
  have hpint : Integrable p ν :=
    Integrable.of_bound hp.aestronglyMeasurable M (Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 u)]; exact hpM u))
  have hq0 := convPow_nonneg ν p hp0
  have hqB := convPow_le_all ν p hp hp0 hpM hpint hmass
  have hqlip := convPow_lipschitz_all ν hdist p hp hp0 hpM hpint hmass hL hlip
  have hLq : 0 ≤ L * max 1 M := mul_nonneg hL (le_trans zero_le_one (le_max_left _ _))
  -- nets
  obtain ⟨t1, -, ht1fin, ht1cover⟩ := finite_cover_balls_of_compact (isCompact_univ (X := G)) hr
  have hnet1 : ∀ x : G, ∃ a ∈ ht1fin.toFinset, dist x a ≤ r := by
    intro x
    have hx := ht1cover (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨a, ha, hd⟩ := hx
    exact ⟨a, ht1fin.mem_toFinset.mpr ha, hd.le⟩
  obtain ⟨t2, -, ht2fin, ht2cover⟩ :=
    finite_cover_balls_of_compact (isCompact_univ (X := G × G)) hr
  have hnet2 : ∀ x : G × G, ∃ a ∈ ht2fin.toFinset, dist x a ≤ r := by
    intro x
    have hx := ht2cover (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hx
    obtain ⟨a, ha, hd⟩ := hx
    exact ⟨a, ht2fin.mem_toFinset.mpr ha, hd.le⟩
  refine ⟨ht1fin.toFinset.card, ht2fin.toFinset.card, fun N _ P hP epsn epsc hn hc hsmall => ?_⟩
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- the normalisation event
  have hBn := uniform_normalisation (μ := μ) X h_indep hX (fun x y => p (x - y))
    (fun x => hp.comp (measurable_const.sub measurable_id)) hM0 hL
    (fun x y => ⟨hp0 _, hpM _⟩)
    (fun x x' y => by rw [← hdist x x' y]; exact hlip (x - y) (x' - y))
    (fun _ => 1)
    (fun x j => by
      have h1 : ∫ ω, p (x - X j ω) ∂μ = ∫ y, p (x - y) ∂(μ.map (X j)) :=
        (integral_map (hX j).aemeasurable
          ((hp.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).symm
      rw [h1, hlaw j, integral_sub_left_eq_self p ν x, hmass])
    (fun x x' => by simpa using mul_nonneg hL dist_nonneg)
    ht1fin.toFinset hnet1 N hn
  simp only [mul_one] at hBn
  -- the consistency events
  have hBc : ∀ m < k, μ.real {ω | ∃ t : G × G,
        epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r
        < |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
            - N * convPow ν p (m + 1) (t.1 - t.2)|}
      ≤ ht2fin.toFinset.card * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
    intro m _
    exact consistency_uniform_exact (μ := μ) ν hdist hdist2 X h_indep hX hlaw p m
      (fun x y => (hp.comp (measurable_const.sub measurable_id)).mul
        ((convPow_measurable ν p hp m).comp (measurable_id.sub measurable_const)))
      hM0 hM0 hL hLq hLq hp0 hpM (hq0 m) (hqB m) hlip (hqlip m) (hqlip (m + 1))
      (by nlinarith [hLq]) (by nlinarith [mul_nonneg hL hM0, mul_nonneg hM0 hLq])
      ht2fin.toFinset hnet2 N hc
  exact kernel_fixed_scale_whp (μ := μ) ν X p (fun _ => M) N k hq0 hqB P hP
    (fun _ => ht2fin.toFinset.card * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))))
    (by positivity) hsmall hBn hBc

/-- **The kernel theorem at a fixed kernel scale on a torus for the walk matrix itself.** As
    `kernel_fixed_scale_torus`, with `P` the matrix `walkMatrix` of the first `N` points with the
    estimated normalisation; the formula for its entries is derived, using `p(0) > 0` (self-loops),
    so that no hypothesis on the walk remains. -/
theorem kernel_fixed_scale_torus_walk {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [MetricSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (hdist2 : ∀ x y y' : G, dist (x - y) (x - y') = dist y y')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν)
    (p : G → ℝ) (hp : Measurable p) {M L r : ℝ} (hM1 : 1 ≤ M) (hL : 0 ≤ L)
    (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (hlip : ∀ u u', |p u - p u'| ≤ L * dist u u') (hpzero : 0 < p 0) (hr : 0 < r) (k : ℕ) :
    ∃ M1 M2 : ℕ, ∀ (N : ℕ) [NeZero N],
      ∀ (epsn epsc : ℝ), 0 ≤ epsn → 0 ≤ epsc → epsn + 2 * (N * L) * r ≤ N / 8 →
      μ.real {ω | ∃ a i : Fin N,
          10 * ((epsn + 2 * (N * L) * r) / N) * (convPow ν p k (X a ω - X i ω)
              + ∑ m ∈ Finset.range k,
                  (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                    + 11 * ((epsn + 2 * (N * L) * r) / N) * M))
            + ∑ m ∈ Finset.range k,
                (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                  + 11 * ((epsn + 2 * (N * L) * r) / N) * M)
          < |(N : ℝ) * (walkMatrix (fun i j : Fin N => p (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, p (X i ω - X l ω)) / N) ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)|}
        ≤ M1 * (2 * Real.exp (-epsn ^ 2 / (2 * N * (M / 2) ^ 2)))
          + ∑ _m ∈ Finset.range k, M2 * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
  obtain ⟨M1, M2, h⟩ := kernel_fixed_scale_torus (μ := μ) ν hdist hdist2 X h_indep hX hlaw p hp
    hM1 hL hp0 hpM hmass hlip hr k
  refine ⟨M1, M2, fun N _ => ?_⟩
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine h N (fun ω => walkMatrix (fun i j : Fin N => p (X i ω - X j ω))
    (fun i : Fin N => (∑ l : Fin N, p (X i ω - X l ω)) / N)) (fun ω b j => ?_)
  refine walkMatrix_apply' _ _ b j ?_
  have hpos : 0 < ∑ l : Fin N, p (X b ω - X l ω) := by
    have h1 : p (X b ω - X b ω) ≤ ∑ l : Fin N, p (X b ω - X l ω) :=
      Finset.single_le_sum (f := fun l : Fin N => p (X b ω - X l ω)) (fun l _ => hp0 _)
        (Finset.mem_univ b)
    rw [sub_self] at h1
    linarith
  exact (div_pos hpos hNpos).ne'

/-- Two elementary inequalities for the exponents in `kernel_fixed_scale_ae`. -/
theorem exponent_aux1 {s M : ℝ} (hM1 : 1 ≤ M) (n : ℕ) :
    -(((n + 1 : ℕ) : ℝ) * s) ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * (M / 2) ^ 2)
      ≤ -(2 * s ^ 2 / M ^ 4 * n) := by
  have hM0 : 0 < M := by linarith
  have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have e : -(((n + 1 : ℕ) : ℝ) * s) ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * (M / 2) ^ 2)
      = -(2 * s ^ 2 / M ^ 2 * ((n + 1 : ℕ) : ℝ)) := by field_simp
  rw [e]
  have h1 : 2 * s ^ 2 / M ^ 4 ≤ 2 * s ^ 2 / M ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_right₀ hM1 (show 2 ≤ 4 by norm_num))
  have h2 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h4 := mul_le_mul h1 h2 (Nat.cast_nonneg n) (by positivity : (0 : ℝ) ≤ 2 * s ^ 2 / M ^ 2)
  linarith

theorem exponent_aux2 {s M : ℝ} (hM1 : 1 ≤ M) (n : ℕ) :
    -(((n + 1 : ℕ) : ℝ) * s) ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * (M * M / 2) ^ 2)
      ≤ -(2 * s ^ 2 / M ^ 4 * n) := by
  have hM0 : 0 < M := by linarith
  have hx : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have e : -(((n + 1 : ℕ) : ℝ) * s) ^ 2 / (2 * ((n + 1 : ℕ) : ℝ) * (M * M / 2) ^ 2)
      = -(2 * s ^ 2 / M ^ 4 * ((n + 1 : ℕ) : ℝ)) := by field_simp
  rw [e]
  have h2 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * s ^ 2 / M ^ 4)
  linarith

/-- An elementary inequality used for the choice of the tolerance in `kernel_fixed_scale_ae`. -/
theorem tolerance_aux {s A1 M e q : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hA : 0 ≤ A1) (he : 0 ≤ e)
    (hq : q ≤ M) :
    10 * (s * A1) * (q + s * e) + s * e ≤ s * (10 * A1 * (M + e) + e) := by
  have hse : s * e ≤ e := by nlinarith
  have h2 : 10 * (s * A1) * (q + s * e) ≤ 10 * (s * A1) * (M + e) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e3 : s * (10 * A1 * (M + e) + e) = 10 * (s * A1) * (M + e) + s * e := by ring
  rw [e3]; linarith

/-- **The kernel of the sampled walk at a fixed kernel scale converges almost surely.** `G` a
    compact abelian group with a translation-invariant metric and its invariant probability
    measure; independent points with this law; `p` a measurable Lipschitz probability density with
    `0 ≤ p ≤ M` and `p(0) > 0`. For every fixed `k` and every `eta > 0`, almost surely, for all
    large `N`, every entry of the walk matrix of the first `N + 1` points satisfies
    `|(N+1) (P^{k+1})_{ai} - p^{*(k+1)}(X_a - X_i)| ≤ eta`. This is the entrywise analogue of
    Theorem "fixed kernel scale" of the paper; the kernel scale is fixed, no rate is claimed. -/
theorem kernel_fixed_scale_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [MetricSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (hdist2 : ∀ x y y' : G, dist (x - y) (x - y') = dist y y')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν)
    (p : G → ℝ) (hp : Measurable p) {M L : ℝ} (hM1 : 1 ≤ M) (hL : 0 ≤ L)
    (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (hlip : ∀ u u', |p u - p u'| ≤ L * dist u u') (hpzero : 0 < p 0) (k : ℕ)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in Filter.atTop, ∀ a i : Fin (N + 1),
      |((N + 1 : ℕ) : ℝ) * (walkMatrix (fun i j : Fin (N + 1) => p (X i ω - X j ω))
            (fun i : Fin (N + 1) => (∑ l : Fin (N + 1), p (X i ω - X l ω)) / (N + 1 : ℕ))
              ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)| ≤ eta := by
  have hM0 : 0 < M := by linarith
  set Ls := L * M + M * (L * max 1 M) + 2 * (L * max 1 M) with hLs
  have hLs0 : 0 ≤ Ls := by
    have h1 : 0 ≤ L * max 1 M := mul_nonneg hL (le_trans zero_le_one (le_max_left _ _))
    rw [hLs]; nlinarith [mul_nonneg hL hM0.le, mul_nonneg hM0.le h1]
  set A1 := 1 + 2 * L with hA1
  set A2 := 1 + 2 * Ls with hA2
  have hA1pos : 0 < A1 := by rw [hA1]; linarith
  have hA2pos : 0 < A2 := by rw [hA2]; linarith
  set e := (k : ℝ) * (3 * A2 + 11 * A1 * M) with he
  have he0 : 0 ≤ e := by rw [he]; positivity
  set D := 10 * A1 * (M + e) + e with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  set s := min 1 (min (1 / (8 * A1)) (eta / D)) with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs2 : s * A1 ≤ 1 / 8 := by
    have h := (min_le_right 1 (min (1 / (8 * A1)) (eta / D))).trans (min_le_left _ _)
    calc s * A1 ≤ 1 / (8 * A1) * A1 := mul_le_mul_of_nonneg_right h hA1pos.le
      _ = 1 / 8 := by field_simp
  have hs3 : s * D ≤ eta := by
    have h := (min_le_right 1 (min (1 / (8 * A1)) (eta / D))).trans (min_le_right _ _)
    calc s * D ≤ eta / D * D := mul_le_mul_of_nonneg_right h hDpos.le
      _ = eta := by field_simp
  obtain ⟨M1, M2, hM⟩ := kernel_fixed_scale_torus_walk (μ := μ) ν hdist hdist2 X h_indep hX hlaw
    p hp hM1 hL hp0 hpM hmass hlip hpzero hspos k
  have hqB := convPow_le_all ν p hp hp0 hpM
    (Integrable.of_bound hp.aestronglyMeasurable M (Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 u)]; exact hpM u))) hmass
  have hbad := ae_eventually_of_exp_bound (μ := μ)
    (fun N => {ω | ¬ ∀ a i : Fin (N + 1),
      |((N + 1 : ℕ) : ℝ) * (walkMatrix (fun i j : Fin (N + 1) => p (X i ω - X j ω))
            (fun i : Fin (N + 1) => (∑ l : Fin (N + 1), p (X i ω - X l ω)) / (N + 1 : ℕ))
              ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)| ≤ eta})
    (C := 2 * M1 + k * (2 * M2)) (c := 2 * s ^ 2 / M ^ 4) (by positivity) (by positivity) ?_
  · filter_upwards [hbad] with ω hω
    filter_upwards [hω] with N hN
    simpa using hN
  · intro N
    have hN1 : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hcond : ((N + 1 : ℕ) : ℝ) * s + 2 * (((N + 1 : ℕ) : ℝ) * L) * s
        ≤ ((N + 1 : ℕ) : ℝ) / 8 := by
      have : ((N + 1 : ℕ) : ℝ) * s + 2 * (((N + 1 : ℕ) : ℝ) * L) * s
          = ((N + 1 : ℕ) : ℝ) * (s * A1) := by rw [hA1]; ring
      rw [this]; nlinarith
    have h := hM (N + 1) (((N + 1 : ℕ) : ℝ) * s) (((N + 1 : ℕ) : ℝ) * s)
      (by positivity) (by positivity) hcond
    -- the two normalised tolerances
    have e1 : (((N + 1 : ℕ) : ℝ) * s + 2 * (((N + 1 : ℕ) : ℝ) * L) * s) / ((N + 1 : ℕ) : ℝ)
        = s * A1 := by rw [hA1]; field_simp
    have e2 : (((N + 1 : ℕ) : ℝ) * s + 2 * (((N + 1 : ℕ) : ℝ) * Ls) * s) / ((N + 1 : ℕ) : ℝ)
        = s * A2 := by rw [hA2]; field_simp
    rw [e1, e2] at h
    -- the bound of the theorem is at most eta
    have hsum : ∑ _m ∈ Finset.range k, (3 * (s * A2) + 11 * (s * A1) * M) = s * e := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, he]; ring
    rw [hsum] at h
    have hbound : ∀ q : ℝ, q ≤ M → 10 * (s * A1) * (q + s * e) + s * e ≤ eta := by
      intro q hq
      exact (tolerance_aux hspos.le hs1 hA1pos.le he0 hq).trans hs3
    have hsub : {ω | ¬ ∀ a i : Fin (N + 1),
          |((N + 1 : ℕ) : ℝ) * (walkMatrix (fun i j : Fin (N + 1) => p (X i ω - X j ω))
                (fun i : Fin (N + 1) => (∑ l : Fin (N + 1), p (X i ω - X l ω)) / (N + 1 : ℕ))
                  ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)| ≤ eta}
        ⊆ {ω | ∃ a i : Fin (N + 1),
          10 * (s * A1) * (convPow ν p k (X a ω - X i ω) + s * e) + s * e
            < |((N + 1 : ℕ) : ℝ) * (walkMatrix (fun i j : Fin (N + 1) => p (X i ω - X j ω))
                (fun i : Fin (N + 1) => (∑ l : Fin (N + 1), p (X i ω - X l ω)) / (N + 1 : ℕ))
                  ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, not_forall, not_le] at hω ⊢
      obtain ⟨a, i, hai⟩ := hω
      exact ⟨a, i, lt_of_le_of_lt (hbound _ (hqB k _)) hai⟩
    refine (measureReal_mono hsub).trans (h.trans ?_)
    -- the exponentials
    have hexp1 := exponent_aux1 (s := s) hM1 N
    have hexp2 := exponent_aux2 (s := s) hM1 N
    have hE1 := Real.exp_le_exp.mpr hexp1
    have hE2 := Real.exp_le_exp.mpr hexp2
    have hM1' : (0 : ℝ) ≤ M1 := Nat.cast_nonneg M1
    have hM2' : (0 : ℝ) ≤ M2 := Nat.cast_nonneg M2
    calc (M1 : ℝ) * (2 * Real.exp (-(((N + 1 : ℕ) : ℝ) * s) ^ 2
              / (2 * ((N + 1 : ℕ) : ℝ) * (M / 2) ^ 2)))
          + ∑ _m ∈ Finset.range k, (M2 : ℝ) * (2 * Real.exp (-(((N + 1 : ℕ) : ℝ) * s) ^ 2
              / (2 * ((N + 1 : ℕ) : ℝ) * (M * M / 2) ^ 2)))
        ≤ (M1 : ℝ) * (2 * Real.exp (-(2 * s ^ 2 / M ^ 4 * N)))
          + ∑ _m ∈ Finset.range k, (M2 : ℝ) * (2 * Real.exp (-(2 * s ^ 2 / M ^ 4 * N))) := by
          refine add_le_add (mul_le_mul_of_nonneg_left (by linarith) hM1') ?_
          exact Finset.sum_le_sum (fun _ _ => mul_le_mul_of_nonneg_left (by linarith) hM2')
      _ = (2 * M1 + k * (2 * M2)) * Real.exp (-(2 * s ^ 2 / M ^ 4 * N)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Convolution powers of a cosine series: powers of the coefficients.** -/
theorem cosSeries_convPow (d : ℕ) (a : (Fin d → ℤ) → ℝ) (ha : Summable fun n => |a n|)
    (ha0 : ∀ n, 0 ≤ a n) (ha1 : ∀ n, a n ≤ 1) (hsym : ∀ n, a (-n) = a n) (m : ℕ) :
    convPow (flatTorusMeasure d) (cosSeries d a) m = cosSeries d (fun n => a n ^ (m + 1)) := by
  induction m with
  | zero => simp [convPow]
  | succ m ih =>
    funext x
    have hpow : Summable fun n => |a n ^ (m + 1)| :=
      Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => by
        rw [abs_of_nonneg (pow_nonneg (ha0 n) _), abs_of_nonneg (ha0 n)]
        exact pow_le_of_le_one (ha0 n) (ha1 n) (Nat.succ_ne_zero m)) ha
    show ∫ w, cosSeries d a (x - w) * convPow (flatTorusMeasure d) (cosSeries d a) m w
        ∂flatTorusMeasure d = _
    rw [ih, cosSeries_conv d a _ ha hpow (fun n => by simp only [hsym]) x]
    unfold cosSeries
    exact tsum_congr fun n => by ring

/-- **Convolution powers of the heat kernel of the torus and their on-diagonal bound, with the
    rate.** `p^{*(m+1)}` is the heat kernel with `c` replaced by `(m+1)c`, and
    `|p^{*(m+1)}(x)| ≤ (1 + √(π/((m+1)c)))^d`. -/
theorem heatTorus_convPow {c : ℝ} (hc : 0 < c) (d m : ℕ) :
    convPow (flatTorusMeasure d) (heatTorus d c) m = heatTorus d ((m + 1 : ℕ) * c) ∧
    ∀ x, |convPow (flatTorusMeasure d) (heatTorus d c) m x|
      ≤ (1 + Real.sqrt (Real.pi / ((m + 1 : ℕ) * c))) ^ d := by
  have habs : ∀ {c' : ℝ}, 0 < c' →
      Summable fun n : Fin d → ℤ => |Real.exp (-c' * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := fun hc' => by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc' d
  have h1 : convPow (flatTorusMeasure d) (heatTorus d c) m = heatTorus d ((m + 1 : ℕ) * c) := by
    unfold heatTorus
    rw [cosSeries_convPow d _ (habs hc) (fun n => (Real.exp_pos _).le)
      (fun n => Real.exp_le_one_iff.mpr (by
        have : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
        nlinarith))
      (fun n => by simp) m]
    congr 1
    funext n
    rw [← Real.exp_nat_mul]; congr 1; ring
  refine ⟨h1, fun x => ?_⟩
  have hc' : 0 < ((m + 1 : ℕ) : ℝ) * c := by positivity
  rw [h1]
  unfold heatTorus
  refine (cosSeries_abs_le d _ (habs hc') x).trans ?_
  simp_rw [abs_of_pos (Real.exp_pos _)]
  exact gauss_tsum_le hc' d

/-! ### Nonnegativity of the heat kernel of the flat torus (Poisson summation) -/

section HeatPositivity
open Complex

/-- **One-variable factor, by Poisson summation.** `∑_j e^{-c j²} e^{2πi j t}` is a nonnegative real
    number (Jacobi's transformation formula from Mathlib: it equals a positive multiple of
    `∑_n e^{-(π²/c)(n - t)²}`). -/
theorem theta_factor_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧
      ∑' j : ℤ, ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j ((t : ℝ) : UnitAddCircle)
        = (r : ℂ) := by
  have ha : 0 < c / Real.pi := div_pos hc Real.pi_pos
  have hP := Complex.tsum_exp_neg_quadratic (a := ((c / Real.pi : ℝ) : ℂ))
    (by rwa [ofReal_re]) (I * t)
  have hL : ∀ j : ℤ, ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j ((t : ℝ) : UnitAddCircle)
      = cexp (-Real.pi * ((c / Real.pi : ℝ) : ℂ) * j ^ 2 + 2 * Real.pi * (I * t) * j) := by
    intro j
    rw [fourier_coe_apply, ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have hR : ∀ n : ℤ, cexp (-Real.pi / ((c / Real.pi : ℝ) : ℂ) * (n + I * (I * t)) ^ 2)
      = ((Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [ofReal_exp]
    congr 1
    have : (n : ℂ) + I * (I * t) = ((n : ℝ) - t : ℝ) := by
      rw [← mul_assoc, I_mul_I]; push_cast; ring
    rw [this]; push_cast; ring
  refine ⟨1 / (c / Real.pi) ^ (1 / 2 : ℝ)
      * ∑' n : ℤ, Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2),
    mul_nonneg (by positivity) (tsum_nonneg fun n => (Real.exp_pos _).le), ?_⟩
  simp_rw [hL]
  rw [hP]
  simp_rw [hR]
  rw [← ofReal_tsum]
  push_cast
  rw [ofReal_cpow ha.le]
  push_cast
  ring


open Filter Topology in
/-- Boxes exhaust the lattice. -/
theorem tendsto_box (d : ℕ) :
    Tendsto (fun m : ℕ => Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m))
      atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun m m' h n hn => ?_) (fun n => ?_)
  · rw [Fintype.mem_piFinset] at hn ⊢
    intro i
    have := hn i
    rw [Finset.mem_Icc] at this ⊢
    have : (m : ℤ) ≤ m' := by exact_mod_cast h
    omega
  · obtain ⟨m, hm⟩ := finset_subset_box d {n}
    exact ⟨m, hm (Finset.mem_singleton_self n)⟩

open Filter Topology in
/-- **Series over `ℤ^d` of a product of one-variable terms.** If the one-variable families are
    absolutely summable, the product family is summable over `ℤ^d` and its sum is the product of
    the one-variable sums. -/
theorem hasSum_pi_prod (d : ℕ) (f : Fin d → ℤ → ℂ) (hf : ∀ i, Summable fun j => ‖f i j‖) :
    HasSum (fun n : Fin d → ℤ => ∏ i, f i (n i)) (∏ i, ∑' j, f i j) := by
  have hsumm : Summable fun n : Fin d → ℤ => ‖∏ i, f i (n i)‖ := by
    refine summable_of_sum_le (fun n => norm_nonneg _) (c := ∏ i, ∑' j, ‖f i j‖) (fun T => ?_)
    obtain ⟨m, hm⟩ := finset_subset_box d T
    refine (Finset.sum_le_sum_of_subset_of_nonneg hm fun n _ _ => norm_nonneg _).trans ?_
    simp_rw [norm_prod]
    rw [← Finset.prod_univ_sum (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m)
      (fun (i : Fin d) (j : ℤ) => ‖f i j‖)]
    exact Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
      (fun i _ => (hf i).sum_le_tsum _ fun j _ => norm_nonneg _)
  have hs : Summable fun n : Fin d → ℤ => ∏ i, f i (n i) := hsumm.of_norm
  have h1 : Tendsto (fun m : ℕ => ∑ n ∈ Fintype.piFinset
      (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m), ∏ i, f i (n i)) atTop
      (𝓝 (∑' n : Fin d → ℤ, ∏ i, f i (n i))) := hs.hasSum.comp (tendsto_box d)
  have hI : Tendsto (fun m : ℕ => Finset.Icc (-(m : ℤ)) m) atTop atTop := by
    refine tendsto_atTop_finset_of_monotone (fun m m' h j hj => ?_) (fun j => ⟨j.natAbs, ?_⟩)
    · rw [Finset.mem_Icc] at hj ⊢
      have : (m : ℤ) ≤ m' := by exact_mod_cast h
      omega
    · rw [Finset.mem_Icc]; omega
  have h2 : Tendsto (fun m : ℕ => ∏ i : Fin d, ∑ j ∈ Finset.Icc (-(m : ℤ)) m, f i j) atTop
      (𝓝 (∏ i, ∑' j, f i j)) :=
    tendsto_finset_prod _ fun i _ => ((hf i).of_norm.hasSum.comp hI)
  have e : (fun m : ℕ => ∑ n ∈ Fintype.piFinset
      (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m), ∏ i, f i (n i))
      = fun m : ℕ => ∏ i : Fin d, ∑ j ∈ Finset.Icc (-(m : ℤ)) m, f i j := by
    funext m
    exact (Finset.prod_univ_sum (fun _ : Fin d => Finset.Icc (-(m : ℤ)) m) (fun i j => f i j)).symm
  rw [e] at h1
  rw [← tendsto_nhds_unique h1 h2]
  exact hs.hasSum

/-- Summability of the Gaussian over the integers. -/
theorem gauss_summable_int {c : ℝ} (hc : 0 < c) :
    Summable fun j : ℤ => Real.exp (-c * (j : ℝ) ^ 2) := by
  refine summable_of_sum_le (fun j => (Real.exp_pos _).le) (c := 1 + Real.sqrt (Real.pi / c))
    (fun T => ?_)
  have hsub : T ⊆ Finset.Icc (-((T.sup Int.natAbs : ℕ) : ℤ)) (T.sup Int.natAbs : ℕ) := by
    intro j hj
    have : j.natAbs ≤ T.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hj
    rw [Finset.mem_Icc]; omega
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (Real.exp_pos _).le).trans
    (gauss_sum_int_le hc _)

/-- **The heat kernel of the flat torus, defined by its Fourier series, is nonnegative.** -/
theorem heatTorus_nonneg {c : ℝ} (hc : 0 < c) (d : ℕ) (x : FlatTorus d) : 0 ≤ heatTorus d c x := by
  have hnorm : ∀ (i : Fin d) (j : ℤ),
      ‖((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j (x i)‖ = Real.exp (-c * (j : ℝ) ^ 2) := by
    intro i j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), fourier_apply,
      Circle.norm_coe, mul_one]
  have hS := hasSum_pi_prod d (fun i j => ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j (x i))
    (fun i => by simp_rw [hnorm]; exact gauss_summable_int hc)
  have hr : ∀ i : Fin d, ∃ r : ℝ, 0 ≤ r ∧
      ∑' j : ℤ, ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j (x i) = (r : ℂ) := by
    intro i
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (x i)
    rw [← ht]
    exact theta_factor_nonneg hc t
  choose r hr0 hreq using hr
  simp_rw [hreq] at hS
  have hG : ∀ n : Fin d → ℤ,
      (∏ i, ((Real.exp (-c * ((n i : ℤ) : ℝ) ^ 2) : ℝ) : ℂ) * fourier (n i) (x i)).re
        = Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) * (torusChar d n x).re := by
    intro n
    rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum]
    unfold torusChar
    rw [Complex.re_ofReal_mul]
  have hre := Complex.hasSum_re hS
  simp_rw [hG] at hre
  have hval : heatTorus d c x = (∏ i, (r i : ℂ)).re := hre.tsum_eq
  rw [hval, ← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_nonneg fun i _ => hr0 i

end HeatPositivity

/-! ### The sampled walk with the heat kernel of the torus, at a fixed scale -/

section HeatWalk
open Complex

/-- `|e^{2πi n u} - 1| ≤ 2π |n| ‖u‖` on the circle. -/
theorem fourier_sub_one_le (n : ℤ) (u : UnitAddCircle) :
    ‖(fourier n u : ℂ) - 1‖ ≤ 2 * Real.pi * |(n : ℝ)| * ‖u‖ := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective u
  have hn : ‖((s : ℝ) : UnitAddCircle)‖ = |s - round s| := UnitAddCircle.norm_eq
  have e : (fourier n ((s : ℝ) : UnitAddCircle) : ℂ)
      = cexp (I * ((2 * Real.pi * n * (s - round s) : ℝ) : ℂ)) := by
    rw [fourier_coe_apply]
    have h1 : (2 * Real.pi * I * n * s / (1 : ℝ) : ℂ)
        = I * ((2 * Real.pi * n * (s - round s) : ℝ) : ℂ) + ((n * round s : ℤ) : ℂ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e, hn]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]

/-- Lipschitz bound for a character of the circle. -/
theorem fourier_lipschitz (n : ℤ) (x y : UnitAddCircle) :
    ‖(fourier n x : ℂ) - fourier n y‖ ≤ 2 * Real.pi * |(n : ℝ)| * dist x y := by
  have hadd : (fourier n x : ℂ) = fourier n (x - y) * fourier n y := by
    have : x = (x - y) + y := by abel
    conv_lhs => rw [this]
    simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
  have h1 : ‖(fourier n y : ℂ)‖ = 1 := by rw [fourier_apply]; exact Circle.norm_coe _
  have : (fourier n x : ℂ) - fourier n y = (fourier n (x - y) - 1) * fourier n y := by
    rw [hadd]; ring
  rw [this, norm_mul, h1, mul_one, dist_eq_norm]
  exact fourier_sub_one_le n (x - y)

/-- `‖∏ z_i - 1‖ ≤ ∑ ‖z_i - 1‖` for factors of norm at most one. -/
theorem norm_prod_sub_one_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ‖∏ i ∈ s, z i - 1‖ ≤ ∑ i ∈ s, ‖z i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have e : z a * ∏ i ∈ s, z i - 1 = z a * (∏ i ∈ s, z i - 1) + (z a - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [hz a, norm_nonneg (z a), norm_nonneg (∏ i ∈ s, z i - 1), norm_nonneg (z a - 1)]

/-- Lipschitz bound for a character of the flat torus. -/
theorem torusChar_lipschitz (d : ℕ) (n : Fin d → ℤ) (x y : FlatTorus d) :
    ‖torusChar d n x - torusChar d n y‖ ≤ 2 * Real.pi * (∑ i, |((n i : ℤ) : ℝ)|) * dist x y := by
  have hadd : torusChar d n x = torusChar d n (x - y) * torusChar d n y := by
    rw [← torusChar_add, sub_add_cancel]
  have e : torusChar d n x - torusChar d n y = (torusChar d n (x - y) - 1) * torusChar d n y := by
    rw [hadd]; ring
  rw [e, norm_mul, torusChar_norm, mul_one]
  unfold torusChar
  refine (norm_prod_sub_one_le _ _ fun i => by
    rw [fourier_apply]; exact (Circle.norm_coe _).le).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := fourier_sub_one_le (n i) ((x - y) i)
  have h2 : ‖(x - y) i‖ ≤ dist x y := by
    rw [Pi.sub_apply, ← dist_eq_norm]; exact dist_le_pi_dist x y i
  have h3 : 0 ≤ 2 * Real.pi * |((n i : ℤ) : ℝ)| := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_left h2 h3)

/-- `|k| ≤ k²` for integers. -/
theorem int_abs_le_sq (k : ℤ) : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
  rw [← sq_abs]
  by_cases h : k = 0
  · simp [h]
  · have : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
    nlinarith

/-- `s e^{-cs} ≤ (2/c) e^{-cs/2}`. -/
theorem mul_exp_neg_le {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s) :
    s * Real.exp (-c * s) ≤ 2 / c * Real.exp (-(c / 2) * s) := by
  have h1 : Real.exp (-c * s) = Real.exp (-(c / 2) * s) * Real.exp (-(c / 2) * s) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : c / 2 * s * Real.exp (-(c / 2) * s) ≤ 1 := by
    have ha := Real.add_one_le_exp (c / 2 * s)
    have hpos := Real.exp_pos (-(c / 2) * s)
    have hinv : Real.exp (c / 2 * s) * Real.exp (-(c / 2) * s) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [mul_nonneg (mul_nonneg hc.le hs) hpos.le]
  have hpos := Real.exp_pos (-(c / 2) * s)
  rw [h1]
  have : s * Real.exp (-(c / 2) * s) ≤ 2 / c := by
    rw [le_div_iff₀ hc]; nlinarith
  nlinarith

/-- **Lipschitz constant of the heat kernel of the flat torus.** -/
theorem heatTorus_lipschitz {c : ℝ} (hc : 0 < c) (d : ℕ) (x y : FlatTorus d) :
    |heatTorus d c x - heatTorus d c y|
      ≤ 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d * dist x y := by
  set a : (Fin d → ℤ) → ℝ := fun n => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) with ha
  have ha0 : ∀ n, 0 < a n := fun n => Real.exp_pos _
  have hsa : Summable a := gauss_summable hc d
  have hF : ∀ z : FlatTorus d, Summable fun n => a n * (torusChar d n z).re := fun z =>
    Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (ha0 n)]
      have := (Complex.abs_re_le_norm (torusChar d n z)).trans (torusChar_norm d n z).le
      nlinarith [ha0 n]) hsa)
  have hc2 : 0 < c / 2 := by positivity
  set g : (Fin d → ℤ) → ℝ := fun n =>
    2 * Real.pi * (2 / c) * dist x y * Real.exp (-(c / 2) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) with hg
  have hsg : Summable g := (gauss_summable hc2 d).mul_left _
  have hterm : ∀ n, |a n * (torusChar d n x).re - a n * (torusChar d n y).re| ≤ g n := by
    intro n
    have h1 : |(torusChar d n x).re - (torusChar d n y).re|
        ≤ 2 * Real.pi * (∑ i, |((n i : ℤ) : ℝ)|) * dist x y := by
      rw [← Complex.sub_re]
      exact (Complex.abs_re_le_norm _).trans (torusChar_lipschitz d n x y)
    have h2 : ∑ i, |((n i : ℤ) : ℝ)| ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun i _ => int_abs_le_sq (n i)
    have hs0 : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
    have h3 := mul_exp_neg_le hc hs0
    have hd : 0 ≤ dist x y := dist_nonneg
    rw [← mul_sub, abs_mul, abs_of_pos (ha0 n)]
    have h4 : a n * |(torusChar d n x).re - (torusChar d n y).re|
        ≤ a n * (2 * Real.pi * (∑ i, ((n i : ℤ) : ℝ) ^ 2) * dist x y) := by
      refine mul_le_mul_of_nonneg_left (h1.trans ?_) (ha0 n).le
      have : 0 ≤ 2 * Real.pi := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 this) hd
    refine h4.trans ?_
    have h5 : a n * (2 * Real.pi * (∑ i, ((n i : ℤ) : ℝ) ^ 2) * dist x y)
        = 2 * Real.pi * dist x y * ((∑ i, ((n i : ℤ) : ℝ) ^ 2) * a n) := by ring
    rw [h5, hg]
    have : 0 ≤ 2 * Real.pi * dist x y := by positivity
    calc 2 * Real.pi * dist x y * ((∑ i, ((n i : ℤ) : ℝ) ^ 2) * a n)
        ≤ 2 * Real.pi * dist x y * (2 / c * Real.exp (-(c / 2) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 this
      _ = _ := by ring
  have hdiff : heatTorus d c x - heatTorus d c y
      = ∑' n, (a n * (torusChar d n x).re - a n * (torusChar d n y).re) := by
    unfold heatTorus cosSeries
    exact ((hF x).tsum_sub (hF y)).symm
  have hsabs : Summable fun n => |a n * (torusChar d n x).re - a n * (torusChar d n y).re| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm hsg
  rw [hdiff]
  have h1 : |∑' n, (a n * (torusChar d n x).re - a n * (torusChar d n y).re)|
      ≤ ∑' n, |a n * (torusChar d n x).re - a n * (torusChar d n y).re| := by
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
      (f := fun n => a n * (torusChar d n x).re - a n * (torusChar d n y).re)
      (by simpa [Real.norm_eq_abs] using hsabs)
  refine h1.trans ((hsabs.tsum_le_tsum hterm hsg).trans ?_)
  rw [hg, tsum_mul_left]
  have h6 := gauss_tsum_le hc2 d
  have e : Real.pi / (c / 2) = 2 * Real.pi / c := by field_simp
  rw [e] at h6
  have : 0 ≤ 2 * Real.pi * (2 / c) * dist x y := by positivity
  calc 2 * Real.pi * (2 / c) * dist x y * ∑' n : Fin d → ℤ, Real.exp (-(c / 2) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ≤ 2 * Real.pi * (2 / c) * dist x y * (1 + Real.sqrt (2 * Real.pi / c)) ^ d :=
        mul_le_mul_of_nonneg_left h6 this
    _ = _ := by ring

/-- The heat kernel of the torus has mass one. -/
theorem heatTorus_mass {c : ℝ} (hc : 0 < c) (d : ℕ) :
    ∫ u, heatTorus d c u ∂flatTorusMeasure d = 1 := by
  have habs : Summable fun n : Fin d → ℤ => |Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc d
  have h := (cosSeries_coeff d (fun n => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) habs
    (fun n => by simp) 0).1
  simp only [torusChar_zero, Complex.one_re, one_mul, Pi.zero_apply, Int.cast_zero] at h
  unfold heatTorus
  rw [h]; simp

/-- It is positive at the origin. -/
theorem heatTorus_zero_pos {c : ℝ} (hc : 0 < c) (d : ℕ) : 0 < heatTorus d c 0 := by
  unfold heatTorus
  rw [cosSeries_zero]
  exact (gauss_summable hc d).tsum_pos (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- **The kernel of the sampled walk with the heat kernel of the torus, at a fixed scale, almost
    surely, without hypotheses.** Independent uniform points on the flat torus of
    dimension `d`, kernel `p(x) = ∑_n e^{-c|n|²} Re χ_n(x)` (`c = 2π²σ`), self-loops kept: for every `k`
    and `eta > 0`, almost surely for all large `N`,
    `max_{a,i} |(N+1) P^{k+1}(a,i) - p_{(k+1)c}(X_a - X_i)| ≤ eta`. This is the entrywise limit at a
    FIXED scale; it carries no rate in the scale and is not Theorem "kernel". -/
theorem heatTorus_walk_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {c : ℝ} (hc : 0 < c) (k : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in Filter.atTop, ∀ a i : Fin (N + 1),
      |((N + 1 : ℕ) : ℝ) * (walkMatrix (fun i j : Fin (N + 1) => heatTorus d c (X i ω - X j ω))
            (fun i : Fin (N + 1) => (∑ l : Fin (N + 1), heatTorus d c (X i ω - X l ω)) / (N + 1 : ℕ))
              ^ (k + 1)) a i - heatTorus d ((k + 1 : ℕ) * c) (X a ω - X i ω)| ≤ eta := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have habs : Summable fun n : Fin d → ℤ => |Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc d
  have hM : ∀ u, heatTorus d c u ≤ (1 + Real.sqrt (Real.pi / c)) ^ d := fun u => by
    have h1 := cosSeries_abs_le d (fun n => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) habs u
    simp_rw [abs_of_pos (Real.exp_pos _)] at h1
    exact (le_abs_self _).trans (h1.trans (gauss_tsum_le hc d))
  have h := kernel_fixed_scale_ae (μ := μ) (G := FlatTorus d) (flatTorusMeasure d)
    (fun x x' y => dist_sub_right x x' y) (fun x y y' => dist_sub_left x y y') X h_indep hX hlaw
    (heatTorus d c) (cosSeries_continuous d _ habs).measurable
    (M := (1 + Real.sqrt (Real.pi / c)) ^ d)
    (L := 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d)
    (one_le_pow₀ (by linarith [Real.sqrt_nonneg (Real.pi / c)])) (by positivity)
    (heatTorus_nonneg hc d) hM (heatTorus_mass hc d) (heatTorus_lipschitz hc d)
    (heatTorus_zero_pos hc d) k heta
  rw [(heatTorus_convPow hc d k).1] at h
  exact h

end HeatWalk

/-! ### Explicit nets on the torus and the quantitative kernel bound (weak form) -/

/-- The grid `{j/m : j < m}` on the circle. -/
noncomputable def circleNet (m : ℕ) : Finset UnitAddCircle :=
  (Finset.range m).image fun j : ℕ => (((j : ℝ) / (m : ℝ) : ℝ) : UnitAddCircle)

/-- It has at most `m` points. -/
theorem circleNet_card (m : ℕ) : (circleNet m).card ≤ m :=
  Finset.card_image_le.trans (by simp)

/-- Every point of the circle is within `1/m` of the grid. -/
theorem circleNet_dense {m : ℕ} (hm : 0 < m) (x : UnitAddCircle) :
    ∃ a ∈ circleNet m, dist x a ≤ 1 / m := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set j' : ℤ := ⌊s * m⌋ with hj'
  set j : ℕ := (j' % (m : ℤ)).toNat with hj
  have hmz : (0 : ℤ) < m := by exact_mod_cast hm
  have hjlt : j < m := by
    have h1 := Int.emod_lt_of_pos j' hmz
    have h2 := Int.emod_nonneg j' hmz.ne'
    omega
  have hjz : (j : ℤ) = j' % m := Int.toNat_of_nonneg (Int.emod_nonneg j' hmz.ne')
  refine ⟨_, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjlt, rfl⟩, ?_⟩
  rw [dist_eq_norm]
  have hcoe : ((s : ℝ) : UnitAddCircle) - (((j : ℝ) / m : ℝ) : UnitAddCircle)
      = ((s - (j : ℝ) / m : ℝ) : UnitAddCircle) := rfl
  rw [hcoe, UnitAddCircle.norm_eq]
  refine (round_le _ (j' / (m : ℤ))).trans ?_
  have hdecomp : (j' : ℝ) = m * ((j' / (m : ℤ) : ℤ) : ℝ) + (j : ℝ) := by
    have := Int.mul_ediv_add_emod j' m
    have h2 : ((m : ℤ) * (j' / m) + j' % m : ℤ) = j' := this
    rw [← hjz] at h2
    exact_mod_cast h2.symm
  have e : s - (j : ℝ) / m - ((j' / (m : ℤ) : ℤ) : ℝ) = (s * m - j') / m := by
    rw [hdecomp]; field_simp; ring
  rw [e, abs_div, abs_of_pos hm']
  apply div_le_div_of_nonneg_right _ hm'.le
  have h1 := Int.floor_le (s * m)
  have h2 := Int.lt_floor_add_one (s * m)
  rw [abs_le]; constructor <;> linarith

/-- The product grid on the flat torus. -/
noncomputable def torusNet (d m : ℕ) : Finset (FlatTorus d) :=
  Fintype.piFinset fun _ => circleNet m

/-- It has at most `m^d` points. -/
theorem torusNet_card (d m : ℕ) : (torusNet d m).card ≤ m ^ d := by
  unfold torusNet
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Nat.pow_le_pow_left (circleNet_card m) d

/-- Every point of the torus is within `1/m` of the grid (supremum metric). -/
theorem torusNet_dense (d : ℕ) {m : ℕ} (hm : 0 < m) (x : FlatTorus d) :
    ∃ a ∈ torusNet d m, dist x a ≤ 1 / m := by
  choose a ha hd using fun i => circleNet_dense hm (x i)
  refine ⟨a, Fintype.mem_piFinset.mpr ha, ?_⟩
  exact (dist_pi_le_iff (by positivity)).mpr hd

/-- The same for pairs of points. -/
theorem torusNet2_dense (d : ℕ) {m : ℕ} (hm : 0 < m) (t : FlatTorus d × FlatTorus d) :
    ∃ a ∈ torusNet d m ×ˢ torusNet d m, dist t a ≤ 1 / m := by
  obtain ⟨a, ha, hda⟩ := torusNet_dense d hm t.1
  obtain ⟨b, hb, hdb⟩ := torusNet_dense d hm t.2
  exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, max_le hda hdb⟩

/-- The grid of pairs has at most `m^{2d}` points. -/
theorem torusNet2_card (d m : ℕ) : (torusNet d m ×ˢ torusNet d m).card ≤ m ^ (2 * d) := by
  rw [Finset.card_product, two_mul, pow_add]
  exact Nat.mul_le_mul (torusNet_card d m) (torusNet_card d m)


/-- `kernel_fixed_scale_torus` with the two nets given instead of obtained from compactness, so
    that their cardinalities appear in the bound. -/
theorem kernel_fixed_scale_nets {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [MetricSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (hdist2 : ∀ x y y' : G, dist (x - y) (x - y') = dist y y')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν)
    (p : G → ℝ) (hp : Measurable p) {M L r : ℝ} (hM1 : 1 ≤ M) (hL : 0 ≤ L)
    (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (hlip : ∀ u u', |p u - p u'| ≤ L * dist u u') (hr : 0 ≤ r) (k : ℕ)
    (net1 : Finset G) (hnet1 : ∀ x : G, ∃ a ∈ net1, dist x a ≤ r)
    (net2 : Finset (G × G)) (hnet2 : ∀ x : G × G, ∃ a ∈ net2, dist x a ≤ r) :
    ∀ (N : ℕ) [NeZero N] (P : Ω → Matrix (Fin N) (Fin N) ℝ),
      (∀ ω b j, P ω b j
        = (p (X b ω - X j ω) / ((∑ l : Fin N, p (X j ω - X l ω)) / N))
          / ∑ l : Fin N, p (X b ω - X l ω) / ((∑ l' : Fin N, p (X l ω - X l' ω)) / N)) →
      ∀ (epsn epsc : ℝ), 0 ≤ epsn → 0 ≤ epsc → epsn + 2 * (N * L) * r ≤ N / 8 →
      μ.real {ω | ∃ a i : Fin N,
          10 * ((epsn + 2 * (N * L) * r) / N) * (convPow ν p k (X a ω - X i ω)
              + ∑ m ∈ Finset.range k,
                  (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                    + 11 * ((epsn + 2 * (N * L) * r) / N) * M))
            + ∑ m ∈ Finset.range k,
                (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                  + 11 * ((epsn + 2 * (N * L) * r) / N) * M)
          < |(N : ℝ) * (P ω ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)|}
        ≤ net1.card * (2 * Real.exp (-epsn ^ 2 / (2 * N * (M / 2) ^ 2)))
          + ∑ _m ∈ Finset.range k, net2.card * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
  have hM0 : 0 ≤ M := by linarith
  have hpint : Integrable p ν :=
    Integrable.of_bound hp.aestronglyMeasurable M (Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hp0 u)]; exact hpM u))
  have hq0 := convPow_nonneg ν p hp0
  have hqB := convPow_le_all ν p hp hp0 hpM hpint hmass
  have hqlip := convPow_lipschitz_all ν hdist p hp hp0 hpM hpint hmass hL hlip
  have hLq : 0 ≤ L * max 1 M := mul_nonneg hL (le_trans zero_le_one (le_max_left _ _))
  intro N _ P hP epsn epsc hn hc hsmall
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  -- the normalisation event
  have hBn := uniform_normalisation (μ := μ) X h_indep hX (fun x y => p (x - y))
    (fun x => hp.comp (measurable_const.sub measurable_id)) hM0 hL
    (fun x y => ⟨hp0 _, hpM _⟩)
    (fun x x' y => by rw [← hdist x x' y]; exact hlip (x - y) (x' - y))
    (fun _ => 1)
    (fun x j => by
      have h1 : ∫ ω, p (x - X j ω) ∂μ = ∫ y, p (x - y) ∂(μ.map (X j)) :=
        (integral_map (hX j).aemeasurable
          ((hp.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).symm
      rw [h1, hlaw j, integral_sub_left_eq_self p ν x, hmass])
    (fun x x' => by simpa using mul_nonneg hL dist_nonneg)
    net1 hnet1 N hn
  simp only [mul_one] at hBn
  -- the consistency events
  have hBc : ∀ m < k, μ.real {ω | ∃ t : G × G,
        epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r
        < |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
            - N * convPow ν p (m + 1) (t.1 - t.2)|}
      ≤ net2.card * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
    intro m _
    exact consistency_uniform_exact (μ := μ) ν hdist hdist2 X h_indep hX hlaw p m
      (fun x y => (hp.comp (measurable_const.sub measurable_id)).mul
        ((convPow_measurable ν p hp m).comp (measurable_id.sub measurable_const)))
      hM0 hM0 hL hLq hLq hp0 hpM (hq0 m) (hqB m) hlip (hqlip m) (hqlip (m + 1))
      (by nlinarith [hLq]) (by nlinarith [mul_nonneg hL hM0, mul_nonneg hM0 hLq])
      net2 hnet2 N hc
  exact kernel_fixed_scale_whp (μ := μ) ν X p (fun _ => M) N k hq0 hqB P hP
    (fun _ => net2.card * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))))
    (by positivity) hsmall hBn hBc

/-- `kernel_fixed_scale_torus_walk` with given nets. -/
theorem kernel_fixed_scale_nets_walk {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [MetricSpace G]
    [MeasurableSpace G] [BorelSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (hdist2 : ∀ x y y' : G, dist (x - y) (x - y') = dist y y')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν)
    (p : G → ℝ) (hp : Measurable p) {M L r : ℝ} (hM1 : 1 ≤ M) (hL : 0 ≤ L)
    (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (hlip : ∀ u u', |p u - p u'| ≤ L * dist u u') (hpzero : 0 < p 0) (hr : 0 ≤ r) (k : ℕ)
    (net1 : Finset G) (hnet1 : ∀ x : G, ∃ a ∈ net1, dist x a ≤ r)
    (net2 : Finset (G × G)) (hnet2 : ∀ x : G × G, ∃ a ∈ net2, dist x a ≤ r) :
    ∀ (N : ℕ) [NeZero N],
      ∀ (epsn epsc : ℝ), 0 ≤ epsn → 0 ≤ epsc → epsn + 2 * (N * L) * r ≤ N / 8 →
      μ.real {ω | ∃ a i : Fin N,
          10 * ((epsn + 2 * (N * L) * r) / N) * (convPow ν p k (X a ω - X i ω)
              + ∑ m ∈ Finset.range k,
                  (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                    + 11 * ((epsn + 2 * (N * L) * r) / N) * M))
            + ∑ m ∈ Finset.range k,
                (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * r) / N)
                  + 11 * ((epsn + 2 * (N * L) * r) / N) * M)
          < |(N : ℝ) * (walkMatrix (fun i j : Fin N => p (X i ω - X j ω))
              (fun i : Fin N => (∑ l : Fin N, p (X i ω - X l ω)) / N) ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)|}
        ≤ net1.card * (2 * Real.exp (-epsn ^ 2 / (2 * N * (M / 2) ^ 2)))
          + ∑ _m ∈ Finset.range k, net2.card * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
  have h := kernel_fixed_scale_nets (μ := μ) ν hdist hdist2 X h_indep hX hlaw p hp
    hM1 hL hp0 hpM hmass hlip hr k net1 hnet1 net2 hnet2
  intro N _
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine h N (fun ω => walkMatrix (fun i j : Fin N => p (X i ω - X j ω))
    (fun i : Fin N => (∑ l : Fin N, p (X i ω - X l ω)) / N)) (fun ω b j => ?_)
  refine walkMatrix_apply' _ _ b j ?_
  have hpos : 0 < ∑ l : Fin N, p (X b ω - X l ω) := by
    have h1 : p (X b ω - X b ω) ≤ ∑ l : Fin N, p (X b ω - X l ω) :=
      Finset.single_le_sum (f := fun l : Fin N => p (X b ω - X l ω)) (fun l _ => hp0 _)
        (Finset.mem_univ b)
    rw [sub_self] at h1
    linarith
  exact (div_pos hpos hNpos).ne'

/-- **The kernel of the sampled walk with the heat kernel of the torus: quantitative bound with
    explicit constants (weak form of Theorem "kernel").** Independent uniform points on the flat
    torus of dimension `d`, kernel `heatTorus d c` (`c = 2π²σ`), `M = (1 + √(π/c))^d`,
    `L = 2π(2/c)(1 + √(2π/c))^d`, grid parameter `m`. With `δ = (epsn + 2NL/m)/N` and
    `e = 3 (epsc + 2 N L* /m)/N + 11 δ M`, the probability that some entry violates
    `|N P^{k+1}(a,i) - p_{(k+1)c}(X_a - X_i)| ≤ 10 δ (p_{(k+1)c} + k e) + k e` is at most
    `2 m^d exp(-epsn²/(2N(M/2)²)) + 2 k m^{2d} exp(-epsc²/(2N(M²/2)²))`. Every constant is explicit
    in `c`, `d`, `N`, `k`. Compared with the theorem of the paper: Hoeffding instead of Bernstein
    (`M` in place of `√M` in the deviation), uniform bound `M` for all convolution powers, error
    linear in `k` instead of `√k m_k`; the regime in which the bound is small is therefore
    smaller than that of the paper. -/
theorem heatTorus_walk_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {c : ℝ} (hc : 0 < c) (k : ℕ) {m : ℕ} (hm : 0 < m) (N : ℕ) [NeZero N]
    {M L : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / c)) ^ d)
    (hLdef : L = 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d)
    (epsn epsc : ℝ) (hn : 0 ≤ epsn) (hcc : 0 ≤ epsc)
    (hsmall : epsn + 2 * (N * L) * (1 / m) ≤ N / 8) :
    μ.real {ω | ∃ a i : Fin N,
        10 * ((epsn + 2 * (N * L) * (1 / m)) / N) * (heatTorus d ((k + 1 : ℕ) * c) (X a ω - X i ω)
            + ∑ _j ∈ Finset.range k,
                (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * (1 / m)) / N)
                  + 11 * ((epsn + 2 * (N * L) * (1 / m)) / N) * M))
          + ∑ _j ∈ Finset.range k,
              (3 * ((epsc + 2 * (N * (L * M + M * (L * max 1 M) + 2 * (L * max 1 M))) * (1 / m)) / N)
                + 11 * ((epsn + 2 * (N * L) * (1 / m)) / N) * M)
        < |(N : ℝ) * (walkMatrix (fun i j : Fin N => heatTorus d c (X i ω - X j ω))
            (fun i : Fin N => (∑ l : Fin N, heatTorus d c (X i ω - X l ω)) / N) ^ (k + 1)) a i
            - heatTorus d ((k + 1 : ℕ) * c) (X a ω - X i ω)|}
      ≤ (m : ℝ) ^ d * (2 * Real.exp (-epsn ^ 2 / (2 * N * (M / 2) ^ 2)))
        + ∑ _j ∈ Finset.range k,
            (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have habs : Summable fun n : Fin d → ℤ => |Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc d
  have hM : ∀ u, heatTorus d c u ≤ M := fun u => by
    have h1 := cosSeries_abs_le d (fun n => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) habs u
    simp_rw [abs_of_pos (Real.exp_pos _)] at h1
    rw [hMdef]
    exact (le_abs_self _).trans (h1.trans (gauss_tsum_le hc d))
  have hM1 : 1 ≤ M := by
    rw [hMdef]; exact one_le_pow₀ (by linarith [Real.sqrt_nonneg (Real.pi / c)])
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have h := kernel_fixed_scale_nets_walk (μ := μ) (G := FlatTorus d) (flatTorusMeasure d)
    (fun x x' y => dist_sub_right x x' y) (fun x y y' => dist_sub_left x y y') X h_indep hX hlaw
    (heatTorus d c) (cosSeries_continuous d _ habs).measurable (M := M) (L := L) (r := 1 / m)
    hM1 hL0 (heatTorus_nonneg hc d) hM (heatTorus_mass hc d)
    (fun u u' => by rw [hLdef]; exact heatTorus_lipschitz hc d u u')
    (heatTorus_zero_pos hc d) (by positivity) k
    (torusNet d m) (torusNet_dense d hm) (torusNet d m ×ˢ torusNet d m) (torusNet2_dense d hm)
    N epsn epsc hn hcc hsmall
  rw [(heatTorus_convPow hc d k).1] at h
  refine h.trans ?_
  have c1 : ((torusNet d m).card : ℝ) ≤ (m : ℝ) ^ d := by exact_mod_cast torusNet_card d m
  have c2 : ((torusNet d m ×ˢ torusNet d m).card : ℝ) ≤ (m : ℝ) ^ (2 * d) := by
    exact_mod_cast torusNet2_card d m
  refine add_le_add (mul_le_mul_of_nonneg_right c1 (by positivity))
    (Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_right c2 (by positivity))

/-! ### The heat-kernel matrix: positive semidefiniteness and truncation -/

/-- The matrix of the heat kernel of the torus at arbitrary points is positive semidefinite. -/
theorem heatTorus_quadform_nonneg {c : ℝ} (hc : 0 < c) (d : ℕ) {n : Type*} [Fintype n]
    (x : n → FlatTorus d) (y : n → ℝ) :
    0 ≤ ∑ i, ∑ j, y i * y j * heatTorus d c (x i - x j) := by
  set a : (Fin d → ℤ) → ℝ := fun k => Real.exp (-c * ∑ i, ((k i : ℤ) : ℝ) ^ 2) with ha
  have hF : ∀ z : FlatTorus d, HasSum (fun k => a k * (torusChar d k z).re) (heatTorus d c z) :=
    fun z => (Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := (Complex.abs_re_le_norm (torusChar d k z)).trans (torusChar_norm d k z).le
      nlinarith [Real.exp_pos (-c * ∑ i, ((k i : ℤ) : ℝ) ^ 2)]) (gauss_summable hc d))).hasSum
  have hS : HasSum (fun k => ∑ i, ∑ j, y i * y j * (a k * (torusChar d k (x i - x j)).re))
      (∑ i, ∑ j, y i * y j * heatTorus d c (x i - x j)) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ => (hF (x i - x j)).mul_left (y i * y j)
  refine HasSum.nonneg (fun k => ?_) hS
  have e : ∑ i, ∑ j, y i * y j * (a k * (torusChar d k (x i - x j)).re)
      = a k * ((∑ i, y i * (torusChar d k (x i)).re) ^ 2
          + (∑ i, y i * (torusChar d k (x i)).im) ^ 2) := by
    rw [_root_.sq, _root_.sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [torusChar_sub_re]; ring
  rw [e]
  exact mul_nonneg (Real.exp_pos _).le (add_nonneg (_root_.sq_nonneg _) (_root_.sq_nonneg _))

open Filter Topology in
/-- **Truncation of the Fourier series of the heat kernel of the torus.** If every frequency
    outside the finite set `T` has `|n|² ≥ R`, the partial sum over `T` is within
    `e^{-cR/2} (1 + √(2π/c))^d` of the kernel, uniformly on the torus. -/
theorem heatTorus_truncation {c : ℝ} (hc : 0 < c) (d : ℕ) (T : Finset (Fin d → ℤ)) {R : ℝ}
    (hT : ∀ n, n ∉ T → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) (u : FlatTorus d) :
    |heatTorus d c u - ∑ n ∈ T, Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) * (torusChar d n u).re|
      ≤ Real.exp (-c * R / 2) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d := by
  classical
  set F : (Fin d → ℤ) → ℝ := fun k =>
    Real.exp (-c * ∑ i, ((k i : ℤ) : ℝ) ^ 2) * (torusChar d k u).re with hFdef
  have hFabs : ∀ k, |F k| ≤ Real.exp (-c * ∑ i, ((k i : ℤ) : ℝ) ^ 2) := fun k => by
    rw [hFdef]; simp only
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have := (Complex.abs_re_le_norm (torusChar d k u)).trans (torusChar_norm d k u).le
    nlinarith [Real.exp_pos (-c * ∑ i, ((k i : ℤ) : ℝ) ^ 2)]
  have hF : HasSum F (heatTorus d c u) :=
    (Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact hFabs k) (gauss_summable hc d))).hasSum
  have hlim : Tendsto (fun U : Finset (Fin d → ℤ) => |∑ n ∈ U, F n - ∑ n ∈ T, F n|) atTop
      (𝓝 |heatTorus d c u - ∑ n ∈ T, F n|) := (hF.sub_const _).abs
  refine le_of_tendsto hlim ((eventually_ge_atTop T).mono fun U hU => ?_)
  have hsplit : ∑ n ∈ U, F n - ∑ n ∈ T, F n = ∑ n ∈ U \ T, F n := by
    rw [← Finset.sum_sdiff hU]; ring
  rw [hsplit]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun n _ => hFabs n).trans ?_)
  exact gauss_tail_sum_le hc d (U \ T) fun n hn => hT n (Finset.mem_sdiff.mp hn).2

/-- Truncation over a half-set of frequencies `H` (nonzero, no pair `n, -n`):
    `1 + ∑_{n ∈ H} 2 e^{-c|n|²} Re χ_n(u)` approximates the heat kernel up to the tail. -/
theorem heatTorus_truncation_half {c : ℝ} (hc : 0 < c) (d : ℕ) (H : Finset (Fin d → ℤ))
    (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0) {R : ℝ}
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (u : FlatTorus d) :
    |heatTorus d c u - (1 + ∑ n ∈ H, 2 * Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
        * (torusChar d n u).re)|
      ≤ Real.exp (-c * R / 2) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d := by
  classical
  set F : (Fin d → ℤ) → ℝ := fun k =>
    Real.exp (-c * ∑ i, ((k i : ℤ) : ℝ) ^ 2) * (torusChar d k u).re with hFdef
  have hneg : ∀ n, F (-n) = F n := fun n => by
    simp only [hFdef, Pi.neg_apply, Int.cast_neg, neg_sq, torusChar_neg_freq, Complex.conj_re]
  have hdisj : Disjoint H (H.image fun n => -n) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn'
    exact hH2 m hm (-m) hn (by simp)
  have h0 : (0 : Fin d → ℤ) ∉ H ∪ H.image fun n => -n := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hH0 0 h rfl
    · obtain ⟨m, hm, hm0⟩ := Finset.mem_image.mp h
      exact hH0 m hm (neg_eq_zero.mp hm0)
  have hsum : ∑ n ∈ insert (0 : Fin d → ℤ) (H ∪ H.image fun n => -n), F n
      = 1 + ∑ n ∈ H, 2 * Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) * (torusChar d n u).re := by
    rw [Finset.sum_insert h0, Finset.sum_union hdisj,
      Finset.sum_image (fun a _ b _ h => neg_injective h)]
    simp_rw [hneg]
    rw [← Finset.sum_add_distrib]
    congr 1
    · simp [hFdef, torusChar_zero]
    · exact Finset.sum_congr rfl fun n _ => by simp only [hFdef]; ring
  rw [← hsum]
  refine heatTorus_truncation hc d _ (fun n hn => ?_) u
  have hn' : n ≠ 0 ∧ n ∉ H ∧ -n ∉ H := by
    refine ⟨fun h => hn (h ▸ Finset.mem_insert_self _ _), fun h => hn ?_, fun h => hn ?_⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨-n, h, neg_neg n⟩))
  exact hR n hn'.1 hn'.2.1 hn'.2.2

/-! ### Real modes of a half-set of frequencies and the deterministic eigenvalue assembly -/

/-- The index set of real modes belonging to a half-set `H` of frequencies. -/
noncomputable def modeSet (d : ℕ) (H : Finset (Fin d → ℤ)) :
    Finset (Option ((Fin d → ℤ) × Bool)) := by
  classical
  exact insert none ((H.image fun n => some (n, false)) ∪ (H.image fun n => some (n, true)))

/-- The coefficient of a real mode in the heat kernel: `1` for the constant, `e^{-c|n|²}` else. -/
noncomputable def modeCoeff (d : ℕ) (c : ℝ) : Option ((Fin d → ℤ) × Bool) → ℝ
  | none => 1
  | some (n, _) => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)

/-- Membership of a nonconstant mode. -/
theorem mem_modeSet (d : ℕ) (H : Finset (Fin d → ℤ)) (n : Fin d → ℤ) (b : Bool) :
    some (n, b) ∈ modeSet d H ↔ n ∈ H := by
  classical
  unfold modeSet
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Option.some.injEq,
    Prod.mk.injEq, reduceCtorEq, false_or]
  constructor
  · rintro (⟨m, hm, rfl, -⟩ | ⟨m, hm, rfl, -⟩) <;> exact hm
  · intro h
    cases b
    · exact Or.inl ⟨n, h, rfl, rfl⟩
    · exact Or.inr ⟨n, h, rfl, rfl⟩

/-- The coefficients are nonnegative. -/
theorem modeCoeff_nonneg (d : ℕ) (c : ℝ) (f : Option ((Fin d → ℤ) × Bool)) :
    0 ≤ modeCoeff d c f := by
  rcases f with _ | ⟨n, b⟩
  · simp [modeCoeff]
  · exact (Real.exp_pos _).le

/-- The truncated kernel as a sum over the real modes. -/
theorem modeSet_kernel (d : ℕ) (c : ℝ) (H : Finset (Fin d → ℤ)) (x y : FlatTorus d) :
    ∑ f ∈ modeSet d H, modeCoeff d c f * torusMode d f x * torusMode d f y
      = 1 + ∑ n ∈ H, 2 * Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) * (torusChar d n (x - y)).re := by
  classical
  unfold modeSet
  have hnone : (none : Option ((Fin d → ℤ) × Bool))
      ∉ (H.image fun n => some (n, false)) ∪ (H.image fun n => some (n, true)) := by
    simp
  have hdisj : Disjoint (H.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
      (H.image fun n => some (n, true)) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨m', -, h⟩ := Finset.mem_image.mp hf'
    simp at h
  rw [Finset.sum_insert hnone, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => by simpa using h),
    Finset.sum_image (fun a _ b _ h => by simpa using h), ← Finset.sum_add_distrib]
  congr 1
  · simp [modeCoeff, torusMode]
  · refine Finset.sum_congr rfl fun n _ => ?_
    have h := torusMode_kernel d n x y
    simp only [modeCoeff]
    linear_combination (Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) * h

open Matrix in
/-- **Eigenvalues of the sampled graph: deterministic assembly on the good event.** Composition
    of `kernel_fixed_scale_det` (entries of `P^{k+1}`), `conj_pow_entry` and `row_sums_from_kernel`
    (row sums of `S^{k+1} - X Xᵀ`) and `eigtorus_from_gram`. HYPOTHESES, all of them facts on the
    event where normalisation, consistency and Gram matrix are controlled: `hrho1`, `hcons`, `hθ`,
    `hG`, `htail`; `hnn`, `hle1` (eigenvalues of `S` in `[0, 1]`); `hDj` (position of `α^{k+1}` among
    the coefficients). -/
theorem eig_sample_det {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    [Nonempty n]
    (pk : ℕ → n → n → ℝ) (mu dev : ℕ → ℝ) (rho : n → ℝ) (P : Matrix n n ℝ) {delta : ℝ}
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 8)
    (hp0 : ∀ m b i, 0 ≤ pk m b i) (hpmu : ∀ m b i, pk m b i ≤ mu m)
    (hrho : ∀ b, (Fintype.card n : ℝ) * rho b = ∑ l, pk 1 b l)
    (hrho1 : ∀ b, |rho b - 1| ≤ delta)
    (hP : ∀ b j, P b j = (pk 1 b j / rho j) / ∑ l, pk 1 b l / rho l)
    (k : ℕ)
    (hcons : ∀ m b i, 1 ≤ m → m ≤ k →
      |∑ j, pk 1 b j / (Fintype.card n : ℝ) * pk m j i - pk (m + 1) b i| ≤ dev m)
    (S : Matrix n n ℝ) (hS : S.IsHermitian) (hnn : ∀ j, 0 ≤ hS.eigenvalues₀ j)
    (hle1 : ∀ j, hS.eigenvalues₀ j ≤ 1)
    (r : n → ℝ) (hr : ∀ i, 0 < r i) (hSP : ∀ i l, S i l = r i * P i l / r l)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ i l, |r i / r l - 1| ≤ θ)
    (v : Matrix n F ℝ) (a : F → ℝ) (ha : ∀ f, 0 ≤ a f) {eta s t E Dk eps α : ℝ}
    (heta : 0 ≤ eta) (hs0 : 0 ≤ s) (hs : ∀ f, Real.sqrt (a f) ≤ s)
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta)
    (hQ : ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ).IsHermitian)
    (h1 : (fromBlocks ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (hD : (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian)
    (htail : ∀ i l, |pk (k + 1) i l - (Fintype.card n : ℝ) *
        ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
          (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t)
    (hE : ∑ m ∈ Finset.range k, (3 * dev (m + 1) + 11 * delta * mu (m + 2)) ≤ E)
    (hDk : 10 * delta * (mu (k + 1) + E) + E ≤ Dk)
    (heps : θ * (mu (k + 1) + Dk) + Dk + t ≤ eps)
    (j : Fin (Fintype.card n)) (hj : j.val < Fintype.card (n ⊕ F))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hDj : hD.eigenvalues₀ ⟨j.val, hj⟩ = α ^ (k + 1))
    (h3 : 2 * (eps + eta * s * ∑ g, Real.sqrt (a g)) ≤ α ^ (k + 1)) :
    |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)| ≤ eps + eta * s * ∑ g, Real.sqrt (a g)
      ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
          ≤ 2 * (eps + eta * s * ∑ g, Real.sqrt (a g)) := by
  have hNpos : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hkern : ∀ a' i, |(Fintype.card n : ℝ) * (P ^ (k + 1)) a' i - pk (k + 1) a' i| ≤ Dk := by
    intro a' i
    have h := kernel_fixed_scale_det pk mu dev rho P hd0 hd hp0 hpmu hrho hrho1 hP k hcons a' i
    have hmu := hpmu (k + 1) a' i
    have h10 : 0 ≤ 10 * delta := by linarith
    have : 10 * delta * (pk (k + 1) a' i
        + ∑ m ∈ Finset.range k, (3 * dev (m + 1) + 11 * delta * mu (m + 2)))
        ≤ 10 * delta * (mu (k + 1) + E) := mul_le_mul_of_nonneg_left (by linarith) h10
    linarith
  have hrow : ∀ i, ∑ l, |(S ^ (k + 1)) i l - ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ eps := by
    intro i
    refine (row_sums_from_kernel (S ^ (k + 1)) (P ^ (k + 1)) _ (Matrix.of fun i l => pk (k + 1) i l)
      (fun i l => r i / r l) hNpos rfl hθ0 (fun i l => ?_) hθ (fun i l => hkern i l)
      (fun i l => ?_) (fun i l => htail i l) i).trans heps
    · rw [conj_pow_entry S P r hr hSP (k + 1) i l]; ring
    · show |pk (k + 1) i l| ≤ mu (k + 1)
      rw [abs_of_nonneg (hp0 _ _ _)]; exact hpmu _ _ _
  exact eigtorus_from_gram S hS hnn hle1 k v a ha heta hs0 hs hG hQ h1 hD hrow j hj hα0 hα1 hDj h3

/-! ### The symmetric matrix of the sampled graph -/

section SymGraph
open Matrix

/-- Degrees of the normalised graph. -/
theorem graph_degree_bounds {n : Type} [Fintype n] [Nonempty n] (K : n → n → ℝ)
    (hK0 : ∀ i j, 0 ≤ K i j) (rho : n → ℝ) {delta : ℝ} (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 8)
    (hrho : ∀ b, (Fintype.card n : ℝ) * rho b = ∑ l, K b l)
    (hrho1 : ∀ b, |rho b - 1| ≤ delta) (i : n) :
    (Fintype.card n : ℝ) / (1 + delta) ≤ ∑ l, K i l / (rho i * rho l) ∧
    ∑ l, K i l / (rho i * rho l) ≤ (Fintype.card n : ℝ) / (1 - delta) := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hr : ∀ b, 1 - delta ≤ rho b ∧ rho b ≤ 1 + delta := fun b => by
    have := abs_le.mp (hrho1 b); constructor <;> linarith [this.1, this.2]
  have hrpos : ∀ b, 0 < rho b := fun b => by linarith [(hr b).1]
  have h1 : 0 < 1 - delta := by linarith
  have h2 : 0 < 1 + delta := by linarith
  have e : ∑ l, K i l / (rho i * rho l) = (∑ l, K i l / rho l) / rho i := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by
      have := (hrpos i).ne'; have := (hrpos l).ne'; field_simp
  have lo : (∑ l, K i l) / (1 + delta) ≤ ∑ l, K i l / rho l := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun l _ =>
      div_le_div_of_nonneg_left (hK0 i l) (hrpos l) (hr l).2
  have hi : ∑ l, K i l / rho l ≤ (∑ l, K i l) / (1 - delta) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun l _ =>
      div_le_div_of_nonneg_left (hK0 i l) h1 (hr l).1
  rw [e, ← hrho i] at *
  constructor
  · rw [div_le_div_iff₀ h2 (hrpos i)]
    have := (div_le_iff₀ h2).mp lo
    nlinarith [hrpos i]
  · rw [div_le_div_iff₀ (hrpos i) h1]
    have := (le_div_iff₀ h1).mp hi
    nlinarith [hrpos i]

/-- Ratio of square roots of two numbers in `[N/(1+δ), N/(1-δ)]`. -/
theorem sqrt_ratio_bound {N delta x y : ℝ} (hN : 0 < N) (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 8)
    (hx : N / (1 + delta) ≤ x ∧ x ≤ N / (1 - delta))
    (hy : N / (1 + delta) ≤ y ∧ y ≤ N / (1 - delta)) :
    |Real.sqrt x / Real.sqrt y - 1| ≤ 3 * delta := by
  have h1 : 0 < 1 - delta := by linarith
  have h2 : 0 < 1 + delta := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (div_pos hN h2) hx.1
  have hy0 : 0 < y := lt_of_lt_of_le (div_pos hN h2) hy.1
  set u := Real.sqrt x / Real.sqrt y with hu
  have hu0 : 0 < u := div_pos (Real.sqrt_pos.mpr hx0) (Real.sqrt_pos.mpr hy0)
  have husq : u ^ 2 = x / y := by
    rw [hu, div_pow, Real.sq_sqrt hx0.le, Real.sq_sqrt hy0.le]
  have hxy1 : x / y ≤ (1 + delta) / (1 - delta) := by
    rw [div_le_div_iff₀ hy0 h1]
    have a1 := (le_div_iff₀ h1).mp hx.2
    have a2 := (div_le_iff₀ h2).mp hy.1
    nlinarith
  have hxy2 : (1 - delta) / (1 + delta) ≤ x / y := by
    rw [div_le_div_iff₀ h2 hy0]
    have a1 := (div_le_iff₀ h2).mp hx.1
    have a2 := (le_div_iff₀ h1).mp hy.2
    nlinarith
  have hup : u ^ 2 ≤ 1 + 6 * delta := by
    rw [husq]; refine hxy1.trans ?_
    rw [div_le_iff₀ h1]; nlinarith
  have hlo : 1 - 2 * delta ≤ u ^ 2 := by
    rw [husq]; refine le_trans ?_ hxy2
    rw [le_div_iff₀ h2]; nlinarith
  rw [abs_le]
  constructor
  · by_contra hcon
    push Not at hcon
    have h3 : u < 1 - 3 * delta := by linarith
    have h4 : u ^ 2 < (1 - 3 * delta) ^ 2 := by nlinarith
    nlinarith
  · by_contra hcon
    push Not at hcon
    have h3 : 1 + 3 * delta < u := by linarith
    have h4 : (1 + 3 * delta) ^ 2 < u ^ 2 := by nlinarith
    nlinarith

/-- The symmetric normalised matrix `S = D^{-1/2} W D^{-1/2}` of the graph with weights
    `W i j = K i j / (rho i rho j)`. -/
noncomputable def symGraph {n : Type} [Fintype n] (K : n → n → ℝ) (rho : n → ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j => (K i j / (rho i * rho j))
    / (Real.sqrt (∑ l, K i l / (rho i * rho l)) * Real.sqrt (∑ l, K j l / (rho j * rho l)))

/-- `S` is symmetric. -/
theorem symGraph_isHermitian {n : Type} [Fintype n] (K : n → n → ℝ) (rho : n → ℝ)
    (hK : ∀ i j, K i j = K j i) : (symGraph K rho).IsHermitian := by
  ext i j
  simp only [symGraph, conjTranspose_apply, of_apply, star_trivial]
  rw [hK j i, mul_comm (rho j), mul_comm (Real.sqrt _)]

/-- `S = D^{1/2} P D^{-1/2}` entrywise. -/
theorem symGraph_conj {n : Type} [Fintype n] (K : n → n → ℝ) (rho : n → ℝ)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) (i l : n) :
    symGraph K rho i l = Real.sqrt (∑ j, K i j / (rho i * rho j)) * walkMatrix K rho i l
      / Real.sqrt (∑ j, K l j / (rho l * rho j)) := by
  simp only [symGraph, walkMatrix, of_apply]
  have h1 := Real.sqrt_pos.mpr (hD i)
  have h2 := Real.sqrt_pos.mpr (hD l)
  have h3 : Real.sqrt (∑ j, K i j / (rho i * rho j)) * Real.sqrt (∑ j, K i j / (rho i * rho j))
      = ∑ j, K i j / (rho i * rho j) := Real.mul_self_sqrt (hD i).le
  rw [div_eq_div_iff (mul_pos h1 h2).ne' h2.ne']
  have hDi := (hD i).ne'
  have h3' : Real.sqrt (∑ j, K i j / (rho i * rho j)) ^ 2 = ∑ j, K i j / (rho i * rho j) :=
    Real.sq_sqrt (hD i).le
  field_simp
  rw [h3']


/-- Eigenvalues of `S` in decreasing order are at most one. -/
theorem symGraph_eig_le_one {n : Type} [Fintype n] [DecidableEq n] (K : n → n → ℝ) (rho : n → ℝ)
    (hK : ∀ i j, K i j = K j i) (hK0 : ∀ i j, 0 ≤ K i j) (hrho : ∀ i, 0 < rho i)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l))
    (hS : (symGraph K rho).IsHermitian) (j : Fin (Fintype.card n)) :
    hS.eigenvalues₀ j ≤ 1 := by
  have h := (normalised_eigenvalues_mem (fun i j => K i j / (rho i * rho j))
    (fun i j => by beta_reduce; rw [hK i j, mul_comm])
    (fun i j => div_nonneg (hK0 i j) (mul_pos (hrho i) (hrho j)).le) hD
    (symGraph K rho) (fun i j => rfl) hS ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)).2
  simpa [IsHermitian.eigenvalues] using h

/-- If the kernel matrix is positive semidefinite, the eigenvalues of `S` are nonnegative. -/
theorem symGraph_eig_nonneg {n : Type} [Fintype n] [DecidableEq n] (K : n → n → ℝ) (rho : n → ℝ)
    (hpsd : ∀ y : n → ℝ, 0 ≤ ∑ i, ∑ j, y i * y j * K i j)
    (hS : (symGraph K rho).IsHermitian) (j : Fin (Fintype.card n)) :
    0 ≤ hS.eigenvalues₀ j := by
  have hps : (symGraph K rho).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hS fun y => ?_
    have e : star y ⬝ᵥ (symGraph K rho *ᵥ y)
        = ∑ i, ∑ l, (y i / (rho i * Real.sqrt (∑ m, K i m / (rho i * rho m))))
            * (y l / (rho l * Real.sqrt (∑ m, K l m / (rho l * rho m)))) * K i l := by
      simp only [dotProduct, mulVec, star_trivial, symGraph, of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      simp only [div_eq_mul_inv, mul_inv]
      ring
    rw [e]
    exact hpsd _
  have h := hps.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  simpa [IsHermitian.eigenvalues] using h

end SymGraph

/-! ### Eigenvalues of the sampled graph on the torus, deterministic part -/

section TorusEig
open Matrix

/-- The heat kernel of the torus is even. -/
theorem heatTorus_even (d : ℕ) (c : ℝ) (u : FlatTorus d) : heatTorus d c (-u) = heatTorus d c u := by
  unfold heatTorus cosSeries
  refine tsum_congr fun n => ?_
  have h := torusChar_sub_re d n 0 u
  rw [zero_sub] at h
  have h0 : torusChar d n 0 = 1 := by simp [torusChar]
  rw [h, h0]; simp

/-- `X Xᵀ` is symmetric. -/
theorem gram_hermitian {n F : Type} [Fintype n] [Fintype F] (X : Matrix n F ℝ) :
    (X * Xᵀ).IsHermitian := by
  have := isHermitian_mul_conjTranspose_self X
  simpa [conjTranspose_eq_transpose_of_trivial] using this

/-- A symmetric matrix padded with a zero block is symmetric. -/
theorem pad_hermitian₁ {n F : Type} [Fintype n] [Fintype F] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) : (fromBlocks A 0 0 (0 : Matrix F F ℝ)).IsHermitian :=
  hA.fromBlocks (by simp) isHermitian_zero

/-- A diagonal matrix padded with a zero block is symmetric. -/
theorem pad_hermitian₂ {n F : Type} [Fintype n] [Fintype F] [DecidableEq F] (a : F → ℝ) :
    (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian :=
  isHermitian_zero.fromBlocks (by simp) (isHermitian_diagonal a)

/-- Upper bound for the heat kernel of the torus. -/
theorem heatTorus_le {c : ℝ} (hc : 0 < c) (d : ℕ) (u : FlatTorus d) :
    heatTorus d c u ≤ (1 + Real.sqrt (Real.pi / c)) ^ d := by
  have habs : Summable fun n : Fin d → ℤ => |Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc d
  have h1 := cosSeries_abs_le d (fun n => Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) habs u
  simp_rw [abs_of_pos (Real.exp_pos _)] at h1
  exact (le_abs_self _).trans (h1.trans (gauss_tsum_le hc d))

/-- **Eigenvalues of the sampled graph on the torus: deterministic statement on the good event.**
    Points `x_1, …, x_N` on the flat torus, kernel `heatTorus d c`, `S` the symmetric normalised matrix
    of the graph with self-loops, `H` a set of nonzero frequencies without a pair `n, -n` such that
    all other nonzero frequencies have `|n|² ≥ R`. HYPOTHESES on the points (the good event):
    `hnorm` (normalisation within `delta ≤ 1/8`), `hcons` (consistency with exact normalisation, errors
    `dev m`), `hgram` (Gram matrix of the sampled modes within `N eta` of `N` times the identity).
    `hc1`, `hc2` say that `α^{k+1}` is the `j`-th largest coefficient `e^{-(k+1)c|n|²}` of the modes,
    counted with multiplicity (each nonzero frequency of `H` twice). Conclusion: parts (i) and (ii)
    of Theorem "eigenvalues on the torus" for the `j`-th eigenvalue of `S`, with
    `eps = 3 delta (mu + Dk) + Dk + t`. No hypothesis on eigenvalues, symmetry or positivity remains. -/
theorem heatTorus_eig_det {c : ℝ} (hc : 0 < c) (d N : ℕ) [NeZero N] (x : Fin N → FlatTorus d)
    (k : ℕ) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {R delta eta t E Dk eps α : ℝ}
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 8) (heta : 0 ≤ eta) (dev : ℕ → ℝ)
    (hnorm : ∀ b, |(∑ l, heatTorus d c (x b - x l)) / N - 1| ≤ delta)
    (hcons : ∀ m b i, 1 ≤ m → m ≤ k →
      |∑ j, heatTorus d c (x b - x j) / N * heatTorus d ((m : ℕ) * c) (x j - x i)
        - heatTorus d ((m + 1 : ℕ) * c) (x b - x i)| ≤ dev m)
    (hgram : ∀ f g : modeSet d H, |∑ i, torusMode d f.1 (x i) * torusMode d g.1 (x i)
        - N * (if f = g then (1 : ℝ) else 0)| ≤ N * eta)
    (ht : Real.exp (-((k + 1 : ℕ) * c) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k + 1 : ℕ) * c))) ^ d ≤ t)
    (hE : ∑ m ∈ Finset.range k,
        (3 * dev (m + 1) + 11 * delta * (1 + Real.sqrt (Real.pi / ((m + 2 : ℕ) * c))) ^ d) ≤ E)
    (hDk : 10 * delta * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + E) + E ≤ Dk)
    (heps : 3 * delta * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + Dk) + Dk + t ≤ eps)
    (hS : (symGraph (fun i j : Fin N => heatTorus d c (x i - x j))
      (fun i => (∑ l, heatTorus d c (x i - x l)) / N)).IsHermitian)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) < modeCoeff d ((k + 1 : ℕ) * c) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) ≤ modeCoeff d ((k + 1 : ℕ) * c) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)) ≤ α ^ (k + 1)) :
    |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)|
        ≤ eps + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)
      ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
          ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
              Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)) := by
  classical
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp
  set K : Fin N → Fin N → ℝ := fun i j => heatTorus d c (x i - x j) with hKdef
  set rho : Fin N → ℝ := fun i => (∑ l, heatTorus d c (x i - x l)) / N with hrhodef
  set pk : ℕ → Fin N → Fin N → ℝ := fun m b i =>
    if m = 0 then 0 else heatTorus d ((m : ℕ) * c) (x b - x i) with hpkdef
  set mu : ℕ → ℝ := fun m => if m = 0 then 0 else (1 + Real.sqrt (Real.pi / ((m : ℕ) * c))) ^ d
    with hmudef
  have hmc : ∀ m : ℕ, m ≠ 0 → 0 < (m : ℝ) * c := fun m hm =>
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hc
  have hpk1 : ∀ b i, pk 1 b i = K b i := fun b i => by simp [hpkdef, hKdef]
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => heatTorus_nonneg hc d _
  have hKsym : ∀ i j, K i j = K j i := fun i j => by
    simp only [hKdef]; rw [← heatTorus_even, neg_sub]
  have hrho1 : ∀ b, |rho b - 1| ≤ delta := hnorm
  have hrhopos : ∀ b, 0 < rho b := fun b => by
    have := abs_le.mp (hrho1 b); linarith [this.1]
  have hrhoeq : ∀ b, (Fintype.card (Fin N) : ℝ) * rho b = ∑ l, K b l := fun b => by
    rw [hcard]; simp only [hrhodef, hKdef]; field_simp
  have hDb := fun i => graph_degree_bounds K hK0 rho hd0 hd hrhoeq hrho1 i
  have hDpos : ∀ i, 0 < ∑ l, K i l / (rho i * rho l) := fun i =>
    lt_of_lt_of_le (div_pos (by rw [hcard]; exact hNpos) (by linarith)) (hDb i).1
  -- kernel-matrix factor
  set a : modeSet d H → ℝ := fun f => modeCoeff d ((k + 1 : ℕ) * c) f.1 with hadef
  set v : Matrix (Fin N) (modeSet d H) ℝ :=
    Matrix.of fun i f => torusMode d f.1 (x i) / Real.sqrt N with hvdef
  have ha : ∀ f, 0 ≤ a f := fun f => modeCoeff_nonneg d _ f.1
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hsqpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hs : ∀ f, Real.sqrt (a f) ≤ 1 := fun f => by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    rcases f with ⟨_ | ⟨n, b⟩, hf⟩
    · simp [hadef, modeCoeff]
    · simp only [hadef, modeCoeff]
      apply Real.exp_le_one_iff.mpr
      have h1 : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
      have := (hmc (k + 1) (Nat.succ_ne_zero k)).le
      nlinarith
  have hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta := by
    intro f g
    have e : ∑ i, v i f * v i g - (if f = g then (1 : ℝ) else 0)
        = (∑ i, torusMode d f.1 (x i) * torusMode d g.1 (x i)
            - N * (if f = g then (1 : ℝ) else 0)) / N := by
      simp only [hvdef, of_apply]
      rw [sub_div, Finset.sum_div, mul_div_cancel_left₀ _ hNpos.ne']
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_mul_div_comm, hsqN]
    rw [e, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    linarith [hgram f g]
  have hQ := gram_hermitian (Matrix.of fun i f => Real.sqrt (a f) * v i f)
  have h1 := pad_hermitian₁ (F := modeSet d H) _ hQ
  have hD := pad_hermitian₂ (n := Fin N) a
  have htail : ∀ i l, |pk (k + 1) i l - (Fintype.card (Fin N) : ℝ) *
      ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t := by
    intro i l
    rw [finite_rank_kernel_entry v a ha i l, hcard]
    have e : (N : ℝ) * ∑ f, a f * v i f * v l f
        = 1 + ∑ n ∈ H, 2 * Real.exp (-((k + 1 : ℕ) * c) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
            * (torusChar d n (x i - x l)).re := by
      rw [← modeSet_kernel d ((k + 1 : ℕ) * c) H (x i) (x l),
        ← Finset.sum_coe_sort (modeSet d H), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [hvdef, hadef, of_apply]
      field_simp
      rw [Real.sq_sqrt hNpos.le]; ring
    rw [e]
    have hp : pk (k + 1) i l = heatTorus d ((k + 1 : ℕ) * c) (x i - x l) := by
      simp [hpkdef]
    rw [hp]
    exact (heatTorus_truncation_half (hmc (k + 1) (Nat.succ_ne_zero k)) d H hH0 hH2 hR _).trans ht
  have hj : j.val < Fintype.card (Fin N ⊕ modeSet d H) := by
    rw [Fintype.card_sum]; exact lt_of_lt_of_le j.2 (Nat.le_add_right _ _)
  have hDj : hD.eigenvalues₀ ⟨j.val, hj⟩ = α ^ (k + 1) :=
    diag_pad_eigenvalue a hD (pow_pos hα0 _) ⟨j.val, hj⟩ hc1 hc2
  refine eig_sample_det pk mu dev rho (walkMatrix K rho) hd0 hd
    (fun m b i => ?_) (fun m b i => ?_) (fun b => by simp_rw [hpk1]; exact hrhoeq b) hrho1
    (fun b j' => by simp_rw [hpk1]; exact walkMatrix_apply' K rho b j' (hrhopos b).ne')
    k (fun m b i h1m hmk => ?_)
    (symGraph K rho) hS (symGraph_eig_nonneg K rho (fun y => heatTorus_quadform_nonneg hc d x y) hS)
    (symGraph_eig_le_one K rho hKsym hK0 hrhopos hDpos hS)
    (fun i => Real.sqrt (∑ l, K i l / (rho i * rho l))) (fun i => Real.sqrt_pos.mpr (hDpos i))
    (symGraph_conj K rho hDpos) (θ := 3 * delta) (by linarith)
    (fun i l => sqrt_ratio_bound (by rw [hcard]; exact hNpos) hd0 hd (hDb i) (hDb l))
    v a ha (E := E) (Dk := Dk) (eps := eps) (t := t) heta zero_le_one hs hG hQ h1 hD htail ?_ ?_ ?_
    j hj hα0.le hα1 hDj h3
  · simp only [hpkdef]; split_ifs with h
    · exact le_rfl
    · exact heatTorus_nonneg (hmc m h) d _
  · simp only [hpkdef, hmudef]; split_ifs with h
    · exact le_rfl
    · exact heatTorus_le (hmc m h) d _
  · have hm0 : m ≠ 0 := by omega
    have := hcons m b i h1m hmk
    simp only [hpkdef, hcard, hm0, Nat.succ_ne_zero, if_false, one_ne_zero, Nat.cast_one, one_mul]
    simpa using this
  · simpa [hmudef] using hE
  · simpa [hmudef] using hDk
  · simpa [hmudef] using heps

end TorusEig

section TorusEigProb
open Matrix

/-- **Eigenvalues of the sampled graph on the torus, with probability (weak form of Theorem
    "eigenvalues on the torus").** The set of samples for which the conclusion of
    `heatTorus_eig_det` fails is contained in the union of three bad events: normalisation (`hBn`),
    consistency for the times `(m+1)c`, `m < k` (`hBc`), Gram matrix of the sampled modes (`hBg`).
    HYPOTHESES: the probabilities `pn`, `pc m`, `pg` of these events; they are the conclusions of
    `uniform_normalisation`, `consistency_uniform_exact` and `flatTorus_gram_whp`. -/
theorem heatTorus_eig_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 < c) (d N : ℕ) [NeZero N] (X : ℕ → Ω → FlatTorus d)
    (k : ℕ) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {R eta t E Dk eps α epsn epsc pn pg : ℝ} (pc : ℕ → ℝ)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 8) (heta : 0 ≤ eta)
    (hBn : μ.real {ω | ∃ x : FlatTorus d,
        epsn < |∑ j ∈ Finset.range N, heatTorus d c (x - X j ω) - N|} ≤ pn)
    (hBc : ∀ m < k, μ.real {ω | ∃ u : FlatTorus d × FlatTorus d, epsc
        < |∑ j ∈ Finset.range N, heatTorus d c (u.1 - X j ω)
              * heatTorus d ((m + 1 : ℕ) * c) (X j ω - u.2)
            - N * heatTorus d ((m + 1 + 1 : ℕ) * c) (u.1 - u.2)|} ≤ pc m)
    (hBg : μ.real {ω | ∃ f g : modeSet d H, N * eta ≤ |∑ j ∈ Finset.range N,
        torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
        - N * (if f = g then (1 : ℝ) else 0)|} ≤ pg)
    (ht : Real.exp (-((k + 1 : ℕ) * c) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k + 1 : ℕ) * c))) ^ d ≤ t)
    (hE : ∑ m ∈ Finset.range k, (3 * (epsc / N)
        + 11 * (epsn / N) * (1 + Real.sqrt (Real.pi / ((m + 2 : ℕ) * c))) ^ d) ≤ E)
    (hDk : 10 * (epsn / N) * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + E) + E ≤ Dk)
    (heps : 3 * (epsn / N) * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + Dk) + Dk + t
        ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) < modeCoeff d ((k + 1 : ℕ) * c) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) ≤ modeCoeff d ((k + 1 : ℕ) * c) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)) ≤ α ^ (k + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph (fun i j : Fin N => heatTorus d c (X i ω - X j ω))
          (fun i : Fin N => (∑ l : Fin N, heatTorus d c (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)
          ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1))}
      ≤ pn + ∑ m ∈ Finset.range k, pc m + pg := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set Bn : Set Ω := {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d c (x - X j ω) - N|} with hBn_def
  set Bc : ℕ → Set Ω := fun m => {ω | ∃ u : FlatTorus d × FlatTorus d, epsc
      < |∑ j ∈ Finset.range N, heatTorus d c (u.1 - X j ω)
            * heatTorus d ((m + 1 : ℕ) * c) (X j ω - u.2)
          - N * heatTorus d ((m + 1 + 1 : ℕ) * c) (u.1 - u.2)|} with hBc_def
  set Bg : Set Ω := {ω | ∃ f g : modeSet d H, N * eta ≤ |∑ j ∈ Finset.range N,
      torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
      - N * (if f = g then (1 : ℝ) else 0)|} with hBg_def
  have hsub : {ω | ¬ ∀ hS : (symGraph (fun i j : Fin N => heatTorus d c (X i ω - X j ω))
          (fun i : Fin N => (∑ l : Fin N, heatTorus d c (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)
          ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1))}
      ⊆ (Bn ∪ ⋃ m ∈ Finset.range k, Bc m) ∪ Bg := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_range, not_or, not_exists] at hcon
    obtain ⟨⟨hn, hcc⟩, hg⟩ := hcon
    apply hω
    intro hS
    refine heatTorus_eig_det hc d N (fun i => X i ω) k H hH0 hH2 hR
      (div_nonneg hepsn0 hNpos.le) (by rw [div_le_iff₀ hNpos]; linarith) heta
      (fun _ => epsc / N) (fun b => ?_) (fun m b i hm1 hmk => ?_) (fun f g => ?_)
      ht hE hDk heps hS j hα0 hα1 hc1 hc2 h3
    · have h : |∑ j ∈ Finset.range N, heatTorus d c (X b ω - X j ω) - N| ≤ epsn := by
        by_contra h; exact hn ⟨X b ω, not_le.mp h⟩
      rw [← Fin.sum_univ_eq_sum_range (fun j => heatTorus d c (X b ω - X j ω)) N] at h
      have e : (∑ l : Fin N, heatTorus d c (X b ω - X l ω)) / N - 1
          = (∑ l : Fin N, heatTorus d c (X b ω - X l ω) - N) / N := by field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h : |∑ j ∈ Finset.range N, heatTorus d c (X b ω - X j ω)
            * heatTorus d ((m' + 1 : ℕ) * c) (X j ω - X i ω)
          - N * heatTorus d ((m' + 1 + 1 : ℕ) * c) (X b ω - X i ω)| ≤ epsc := by
        by_contra h; exact hcc m' (by omega) ⟨(X b ω, X i ω), not_le.mp h⟩
      rw [← Fin.sum_univ_eq_sum_range (fun j => heatTorus d c (X b ω - X j ω)
            * heatTorus d ((m' + 1 : ℕ) * c) (X j ω - X i ω)) N] at h
      have e : ∑ j : Fin N, heatTorus d c (X b ω - X j ω) / N
            * heatTorus d ((m' + 1 : ℕ) * c) (X j ω - X i ω)
            - heatTorus d ((m' + 1 + 1 : ℕ) * c) (X b ω - X i ω)
          = (∑ j : Fin N, heatTorus d c (X b ω - X j ω)
                * heatTorus d ((m' + 1 : ℕ) * c) (X j ω - X i ω)
              - N * heatTorus d ((m' + 1 + 1 : ℕ) * c) (X b ω - X i ω)) / N := by
        rw [sub_div, Finset.sum_div]
        congr 1
        · exact Finset.sum_congr rfl (fun j _ => by ring)
        · field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    · have h : |∑ j ∈ Finset.range N, torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
          - N * (if f = g then (1 : ℝ) else 0)| < N * eta := by
        by_contra h; exact hg ⟨f, g, not_lt.mp h⟩
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)) N] at h
      exact h.le
  calc μ.real _ ≤ μ.real ((Bn ∪ ⋃ m ∈ Finset.range k, Bc m) ∪ Bg) := measureReal_mono hsub
    _ ≤ μ.real (Bn ∪ ⋃ m ∈ Finset.range k, Bc m) + μ.real Bg := measureReal_union_le _ _
    _ ≤ (μ.real Bn + μ.real (⋃ m ∈ Finset.range k, Bc m)) + μ.real Bg := by
        gcongr; exact measureReal_union_le _ _
    _ ≤ pn + ∑ m ∈ Finset.range k, pc m + pg := by
        refine add_le_add (add_le_add hBn ((measureReal_biUnion_finset_le _ _).trans ?_)) hBg
        exact Finset.sum_le_sum (fun m hm => hBc m (Finset.mem_range.mp hm))

end TorusEigProb

section TorusEigSample
open Matrix

/-- The bound for the heat kernel decreases in time. -/
theorem heatBound_anti {c : ℝ} (hc : 0 < c) (d m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    (1 + Real.sqrt (a / ((m + 1 : ℕ) * c))) ^ d ≤ (1 + Real.sqrt (a / c)) ^ d := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have h1 : a / ((m + 1 : ℕ) * c) ≤ a / c :=
    div_le_div_of_nonneg_left ha hc (by nlinarith)
  exact pow_le_pow_left₀ (by positivity) (by linarith [Real.sqrt_le_sqrt h1]) d

/-- The Lipschitz constant of the heat kernel decreases in time. -/
theorem heatLip_anti {c : ℝ} (hc : 0 < c) (d m : ℕ) :
    2 * Real.pi * (2 / ((m + 1 : ℕ) * c)) * (1 + Real.sqrt (2 * Real.pi / ((m + 1 : ℕ) * c))) ^ d
      ≤ 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d := by
  have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have h1 : 2 / (((m + 1 : ℕ) : ℝ) * c) ≤ 2 / c :=
    div_le_div_of_nonneg_left (by norm_num) hc (by nlinarith)
  have h2 := heatBound_anti hc d m (2 * Real.pi) (by positivity)
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hpi) h2 (by positivity) (by positivity)

/-- **Eigenvalues of the sampled graph on the flat torus for random samples: explicit bound
    (weak form of Theorem "eigenvalues on the torus").** Independent uniform points `X_1, …, X_N` on the
    flat torus of dimension `d`; graph with the heat kernel `heatTorus d c` (`c = 2π²σ`) and
    self-loops; `S` its symmetric normalised matrix. `M`, `L` the explicit bound and Lipschitz
    constant of the kernel; `m` a grid parameter; `H` a finite set of nonzero frequencies without a
    pair `n, -n` outside of which `|n|² ≥ R`. If `α^{k+1}` is the `j`-th largest of the coefficients
    `e^{-(k+1)c|n|²}` of the real modes of `H` (counts `hc1`, `hc2`) and the explicit error `eps`
    (built from `epsn0`, `epsc0`, the tail `t` and the grid) and `eta` satisfy `h3`, then the
    probability that `|s_j^{k+1} - α^{k+1}| ≤ eps + eta ∑ √a_f` or
    `(k+1) α^{k+1} |s_j - α| ≤ 2 (eps + eta ∑ √a_f)` fails is at most
    `2 m^d e^{-epsn0²/(2N(M/2)²)} + 2 k m^{2d} e^{-epsc0²/(2N(M²/2)²)} + 2 |modes|² e^{-(N eta/2)²/(2N)}`.
    The only hypotheses are on the sample (independence, measurability, law) and inequalities
    between explicit numbers. This is weaker than the theorem of the paper: the consistency step
    uses Hoeffding's inequality and the uniform bound `M`, the error is linear in `k`, and the
    regime of `(N, c)` in which the inequalities can be satisfied has not been worked out. -/
theorem heatTorus_eig_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c) (d N : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (k : ℕ) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {m : ℕ} (hm : 0 < m) {M L R eta t E Dk eps α epsn0 epsc0 : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / c)) ^ d)
    (hLdef : L = 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hn0 : 0 ≤ epsn0) (hc0 : 0 ≤ epsc0) (heta : 0 ≤ eta)
    (hsmall : epsn0 + 2 * (N * L) * (1 / m) ≤ N / 8)
    (ht : Real.exp (-((k + 1 : ℕ) * c) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k + 1 : ℕ) * c))) ^ d ≤ t)
    (hE : ∑ m' ∈ Finset.range k,
        (3 * ((epsc0 + 2 * (N * (L * M + M * L + 2 * L)) * (1 / m)) / N)
          + 11 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
              * (1 + Real.sqrt (Real.pi / ((m' + 2 : ℕ) * c))) ^ d) ≤ E)
    (hDk : 10 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
        * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + E) + E ≤ Dk)
    (heps : 3 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
        * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + Dk) + Dk + t ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) < modeCoeff d ((k + 1 : ℕ) * c) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) ≤ modeCoeff d ((k + 1 : ℕ) * c) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)) ≤ α ^ (k + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph (fun i j : Fin N => heatTorus d c (X i ω - X j ω))
          (fun i : Fin N => (∑ l : Fin N, heatTorus d c (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)
          ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1))}
      ≤ (m : ℝ) ^ d * (2 * Real.exp (-epsn0 ^ 2 / (2 * N * (M / 2) ^ 2)))
        + ∑ _m' ∈ Finset.range k,
            (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2 / (2 * N * (M * M / 2) ^ 2)))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2
            * (2 * Real.exp (-(N * eta / 2) ^ 2 / (2 * N))) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have habs : ∀ {c' : ℝ}, 0 < c' →
      Summable fun n : Fin d → ℤ => |Real.exp (-c' * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := fun hc' => by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc' d
  have hcont : ∀ {c' : ℝ}, 0 < c' → Continuous (heatTorus d c') := fun hc' =>
    cosSeries_continuous d _ (habs hc')
  have hmc : ∀ m' : ℕ, 0 < ((m' + 1 : ℕ) : ℝ) * c := fun m' => by positivity
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hpM : ∀ u, heatTorus d c u ≤ M := fun u => by rw [hMdef]; exact heatTorus_le hc d u
  have hplip : ∀ u u', |heatTorus d c u - heatTorus d c u'| ≤ L * dist u u' := fun u u' => by
    rw [hLdef]; exact heatTorus_lipschitz hc d u u'
  have hlipm : ∀ (m' : ℕ) (u u' : FlatTorus d),
      |heatTorus d ((m' + 1 : ℕ) * c) u - heatTorus d ((m' + 1 : ℕ) * c) u'| ≤ L * dist u u' :=
    fun m' u u' => (heatTorus_lipschitz (hmc m') d u u').trans
      (mul_le_mul_of_nonneg_right (by rw [hLdef]; exact heatLip_anti hc d m') dist_nonneg)
  have hr : (0 : ℝ) ≤ 1 / m := by positivity
  -- normalisation
  have hBn := uniform_normalisation (μ := μ) X h_indep hX (fun x y => heatTorus d c (x - y))
    (fun x => (hcont hc).measurable.comp (measurable_const.sub measurable_id)) hM0 hL0
    (fun x y => ⟨heatTorus_nonneg hc d _, hpM _⟩)
    (fun x x' y => by
      have := hplip (x - y) (x' - y); rwa [dist_sub_right] at this)
    (fun _ => 1)
    (fun x j => by
      have h1 : ∫ ω, heatTorus d c (x - X j ω) ∂μ
          = ∫ y, heatTorus d c (x - y) ∂(μ.map (X j)) :=
        (integral_map (hX j).aemeasurable
          (((hcont hc).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).symm
      rw [h1, hlaw j, integral_sub_left_eq_self (heatTorus d c) (flatTorusMeasure d) x,
        heatTorus_mass hc d])
    (fun x x' => by simpa using mul_nonneg hL0 dist_nonneg)
    (torusNet d m) (torusNet_dense d hm) N hn0
  simp only [mul_one] at hBn
  -- consistency
  have hBc : ∀ m' < k, μ.real {ω | ∃ u : FlatTorus d × FlatTorus d,
        epsc0 + 2 * (N * (L * M + M * L + 2 * L)) * (1 / m)
        < |∑ j ∈ Finset.range N, heatTorus d c (u.1 - X j ω)
              * heatTorus d ((m' + 1 : ℕ) * c) (X j ω - u.2)
            - N * heatTorus d ((m' + 1 + 1 : ℕ) * c) (u.1 - u.2)|}
      ≤ (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2 / (2 * N * (M * M / 2) ^ 2))) := by
    intro m' _
    have h := consistency_uniform_exact (μ := μ) (flatTorusMeasure d)
      (fun x x' y => dist_sub_right x x' y) (fun x y y' => dist_sub_left x y y')
      X h_indep hX hlaw (heatTorus d c) m'
      (fun x y => by
        rw [(heatTorus_convPow hc d m').1]
        exact ((hcont hc).measurable.comp (measurable_const.sub measurable_id)).mul
          ((hcont (hmc m')).measurable.comp (measurable_id.sub measurable_const)))
      (M := M) (B := M) (L := L) (Lq := L) (Lq' := L) (Lstar := L * M + M * L + 2 * L)
      (r := 1 / m) hM0 hM0 hL0 hL0 hL0 (heatTorus_nonneg hc d) hpM
      (fun u => by rw [(heatTorus_convPow hc d m').1]; exact heatTorus_nonneg (hmc m') d u)
      (fun u => by
        rw [(heatTorus_convPow hc d m').1]
        exact (heatTorus_le (hmc m') d u).trans
          (by rw [hMdef]; exact heatBound_anti hc d m' Real.pi Real.pi_pos.le))
      hplip
      (fun u u' => by rw [(heatTorus_convPow hc d m').1]; exact hlipm m' u u')
      (fun u u' => by rw [(heatTorus_convPow hc d (m' + 1)).1]; exact hlipm (m' + 1) u u')
      (by nlinarith [mul_nonneg hL0 hM0]) (by nlinarith [mul_nonneg hL0 hM0])
      (torusNet d m ×ˢ torusNet d m) (torusNet2_dense d hm) N hc0
    rw [(heatTorus_convPow hc d m').1, (heatTorus_convPow hc d (m' + 1)).1] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast torusNet2_card d m
  -- Gram matrix
  have hBg := flatTorus_gram_whp (μ := μ) d X h_indep hX hlaw (modeSet d H)
    (fun n b h => hH0 n ((mem_modeSet d H n b).mp h))
    (fun n b n' b' h h' => hH2 n ((mem_modeSet d H n b).mp h) n' ((mem_modeSet d H n' b').mp h'))
    N (ε := N * eta) (by positivity)
  have hc1' : ((torusNet d m).card : ℝ) ≤ (m : ℝ) ^ d := by exact_mod_cast torusNet_card d m
  exact heatTorus_eig_whp hc d N X k H hH0 hH2
    (fun _ => (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2 / (2 * N * (M * M / 2) ^ 2))))
    hR (by positivity) hsmall heta
    (hBn.trans (mul_le_mul_of_nonneg_right hc1' (by positivity))) hBc hBg
    ht hE hDk heps j hα0 hα1 hc1 hc2 h3

end TorusEigSample

/-! ### Bernstein's inequality in the uniform steps -/

/-- **Uniform concentration with Bernstein's inequality.** As `uniform_concentration_param`, with
    the variance proxy `A · qmax` in place of `A²`: for a family `k x` with values in `[0, A]`,
    means `q x ≤ qmax`, Lipschitz in the parameter, and a net of the parameter space,
    `P(∃ x, |∑_{j<N} k x (X_j) - N q x| > eps + 2 N L r) ≤ 2 |net| exp(-eps²/(4 N A qmax + 2 A eps))`. -/
theorem uniform_concentration_bernstein {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T : Type*} [PseudoMetricSpace T] {E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (k : T → E → ℝ) (hk : ∀ x, Measurable (k x)) {A L r qmax : ℝ} (hA : 0 < A) (hL : 0 ≤ L)
    (hbound : ∀ x y, k x y ∈ Set.Icc 0 A)
    (hlip : ∀ x x' y, |k x y - k x' y| ≤ L * dist x x')
    (q : T → ℝ) (hq : ∀ x j, μ[fun ω => k x (X j ω)] = q x) (hqmax : ∀ x, q x ≤ qmax)
    (hqlip : ∀ x x', |q x - q x'| ≤ L * dist x x')
    (net : Finset T) (hnet : ∀ x, ∃ a ∈ net, dist x a ≤ r)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ x, ε + 2 * (N * L) * r < |∑ j ∈ Finset.range N, k x (X j ω) - N * q x|}
      ≤ net.card * (2 * Real.exp (-ε ^ 2 / (4 * (N * (A * qmax)) + 2 * A * ε))) := by
  classical
  have hq0 : ∀ x, 0 ≤ q x := fun x => by
    rw [← hq x 0]; exact integral_nonneg fun ω => (hbound x (X 0 ω)).1
  have hone : ∀ a ∈ net, μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, k a (X j ω) - N * q a|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (N * (A * qmax)) + 2 * A * ε)) := by
    intro a _
    have h := bernstein_bounded_mean (μ := μ) (fun j ω => k a (X j ω))
      (h_indep.comp (fun _ y => k a y) (fun _ => hk a)) (fun j => (hk a).comp (hX j)) hA
      (fun j ω => (hbound a (X j ω)).1) (fun j ω => (hbound a (X j ω)).2) (fun j => hq a j) N hε
    refine h.trans ?_
    have hden1 : 0 < 4 * (N * (A * q a)) + 2 * A * ε := by
      have : 0 ≤ (N : ℝ) * (A * q a) := by have := hq0 a; positivity
      nlinarith [mul_pos hA hε]
    have hden : 4 * (N * (A * q a)) + 2 * A * ε ≤ 4 * (N * (A * qmax)) + 2 * A * ε := by
      have : (N : ℝ) * (A * q a) ≤ N * (A * qmax) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hqmax a) hA.le) (Nat.cast_nonneg N)
      linarith
    have : -ε ^ 2 / (4 * (N * (A * q a)) + 2 * A * ε)
        ≤ -ε ^ 2 / (4 * (N * (A * qmax)) + 2 * A * ε) := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (_root_.sq_nonneg ε) hden1 hden
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr this) (by norm_num)
  have hnetbound : μ.real {ω | ∃ a ∈ net, ε ≤ |∑ j ∈ Finset.range N, k a (X j ω) - N * q a|}
      ≤ net.card * (2 * Real.exp (-ε ^ 2 / (4 * (N * (A * qmax)) + 2 * A * ε))) := by
    have hset : {ω | ∃ a ∈ net, ε ≤ |∑ j ∈ Finset.range N, k a (X j ω) - N * q a|}
        = ⋃ a ∈ net, {ω | ε ≤ |∑ j ∈ Finset.range N, k a (X j ω) - N * q a|} := by
      ext ω; simp
    rw [hset]
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ a ∈ net, μ.real {ω | ε ≤ |∑ j ∈ Finset.range N, k a (X j ω) - N * q a|}
        ≤ ∑ _a ∈ net, 2 * Real.exp (-ε ^ 2 / (4 * (N * (A * qmax)) + 2 * A * ε)) :=
          Finset.sum_le_sum hone
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  refine (measureReal_mono ?_).trans hnetbound
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hω
  have hNL : 0 ≤ (N : ℝ) * L := mul_nonneg (Nat.cast_nonneg _) hL
  have hf : ∀ x y : T, |∑ j ∈ Finset.range N, k x (X j ω) - ∑ j ∈ Finset.range N, k y (X j ω)|
      ≤ (N * L) * dist x y := by
    intro x y
    rw [← Finset.sum_sub_distrib]
    calc |∑ j ∈ Finset.range N, (k x (X j ω) - k y (X j ω))|
        ≤ ∑ j ∈ Finset.range N, |k x (X j ω) - k y (X j ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range N, L * dist x y := Finset.sum_le_sum (fun j _ => hlip x y (X j ω))
      _ = (N * L) * dist x y := by simp; ring
  have hg : ∀ x y : T, |(N : ℝ) * q x - N * q y| ≤ (N * L) * dist x y := by
    intro x y
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hqlip x y) (Nat.cast_nonneg N)
  have := sup_from_net (fun x => ∑ j ∈ Finset.range N, k x (X j ω)) (fun x => (N : ℝ) * q x)
    hNL hf hg net hnet (fun a ha => (hcon a ha).le) x
  linarith


/-- `consistency_uniform_exact` with Bernstein's inequality: the variance proxy is
    `M B Bq` (bounds of `p`, `p^{*(m+1)}`, `p^{*(m+2)}`) in place of `(M B)²`. -/
theorem consistency_uniform_bernstein {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {G : Type*} [AddCommGroup G] [PseudoMetricSpace G]
    [MeasurableSpace G] [MeasurableAdd₂ G] (ν : Measure G) [ν.IsAddRightInvariant]
    (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (hdist2 : ∀ x y y' : G, dist (x - y) (x - y') = dist y y')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (p : G → ℝ) (m : ℕ)
    (hF : ∀ x y : G, Measurable (fun z : G => p (x - z) * convPow ν p m (z - y)))
    {M B Bq L Lq Lq' Lstar r : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B) (hMB : 0 < M * B)
    (hqmax : ∀ u, convPow ν p (m + 1) u ≤ Bq) (hL : 0 ≤ L) (hLq : 0 ≤ Lq)
    (hLq' : 0 ≤ Lq') (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M)
    (hq0 : ∀ u, 0 ≤ convPow ν p m u) (hqB : ∀ u, convPow ν p m u ≤ B)
    (hplip : ∀ u u', |p u - p u'| ≤ L * dist u u')
    (hqlip : ∀ u u', |convPow ν p m u - convPow ν p m u'| ≤ Lq * dist u u')
    (hq'lip : ∀ u u', |convPow ν p (m + 1) u - convPow ν p (m + 1) u'| ≤ Lq' * dist u u')
    (hL1 : L * B + M * Lq ≤ Lstar) (hL2 : 2 * Lq' ≤ Lstar)
    (net : Finset (G × G)) (hnet : ∀ t : G × G, ∃ a ∈ net, dist t a ≤ r)
    (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ t : G × G, ε + 2 * (N * Lstar) * r
        < |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
            - N * convPow ν p (m + 1) (t.1 - t.2)|}
      ≤ net.card * (2 * Real.exp (-ε ^ 2 / (4 * (N * (M * B * Bq)) + 2 * (M * B) * ε))) := by
  have hLs : 0 ≤ Lstar := le_trans (by positivity) hL2
  refine uniform_concentration_bernstein (μ := μ) (T := G × G) X h_indep hX
    (fun t z => p (t.1 - z) * convPow ν p m (z - t.2)) (fun t => hF t.1 t.2)
    hMB hLs
    (fun t z => ⟨mul_nonneg (hp0 _) (hq0 _), mul_le_mul (hpM _) (hqB _) (hq0 _) hM⟩)
    ?_ (fun t => convPow ν p (m + 1) (t.1 - t.2))
    (fun t j => transported_mean ν (X j) (hX j) (hlaw j) p m t.1 t.2 (hF t.1 t.2))
    (fun t => hqmax _) ?_ net hnet N hε
  · -- Lipschitz in the parameter
    intro t t' z
    have h1 := hplip (t.1 - z) (t'.1 - z)
    rw [hdist t.1 t'.1 z] at h1
    have h2 := hqlip (z - t.2) (z - t'.2)
    rw [hdist2 z t.2 t'.2] at h2
    have hd1 : dist t.1 t'.1 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hd2 : dist t.2 t'.2 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_right _ _
    have e : p (t.1 - z) * convPow ν p m (z - t.2) - p (t'.1 - z) * convPow ν p m (z - t'.2)
        = (p (t.1 - z) - p (t'.1 - z)) * convPow ν p m (z - t.2)
          + p (t'.1 - z) * (convPow ν p m (z - t.2) - convPow ν p m (z - t'.2)) := by ring
    rw [e]
    have a1 : |(p (t.1 - z) - p (t'.1 - z)) * convPow ν p m (z - t.2)| ≤ L * dist t t' * B := by
      rw [abs_mul, abs_of_nonneg (hq0 _)]
      exact mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left hd1 hL)) (hqB _) (hq0 _)
        (mul_nonneg hL dist_nonneg)
    have a2 : |p (t'.1 - z) * (convPow ν p m (z - t.2) - convPow ν p m (z - t'.2))|
        ≤ M * (Lq * dist t t') := by
      rw [abs_mul, abs_of_nonneg (hp0 _)]
      exact mul_le_mul (hpM _) (h2.trans (mul_le_mul_of_nonneg_left hd2 hLq)) (abs_nonneg _) hM
    have a3 : (L * B + M * Lq) * dist t t' ≤ Lstar * dist t t' :=
      mul_le_mul_of_nonneg_right hL1 dist_nonneg
    calc |(p (t.1 - z) - p (t'.1 - z)) * convPow ν p m (z - t.2)
            + p (t'.1 - z) * (convPow ν p m (z - t.2) - convPow ν p m (z - t'.2))|
        ≤ L * dist t t' * B + M * (Lq * dist t t') := (abs_add_le _ _).trans (add_le_add a1 a2)
      _ = (L * B + M * Lq) * dist t t' := by ring
      _ ≤ Lstar * dist t t' := a3
  · -- Lipschitz of the mean
    intro t t'
    have hd1 : dist t.1 t'.1 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_left _ _
    have hd2 : dist t.2 t'.2 ≤ dist t t' := by rw [Prod.dist_eq]; exact le_max_right _ _
    have h1 := hq'lip (t.1 - t.2) (t'.1 - t'.2)
    have htri : dist (t.1 - t.2) (t'.1 - t'.2) ≤ dist t.1 t'.1 + dist t.2 t'.2 := by
      calc dist (t.1 - t.2) (t'.1 - t'.2)
          ≤ dist (t.1 - t.2) (t'.1 - t.2) + dist (t'.1 - t.2) (t'.1 - t'.2) := dist_triangle _ _ _
        _ = dist t.1 t'.1 + dist t.2 t'.2 := by rw [hdist, hdist2]
    calc |convPow ν p (m + 1) (t.1 - t.2) - convPow ν p (m + 1) (t'.1 - t'.2)|
        ≤ Lq' * dist (t.1 - t.2) (t'.1 - t'.2) := h1
      _ ≤ Lq' * (2 * dist t t') := mul_le_mul_of_nonneg_left (by linarith) hLq'
      _ = 2 * Lq' * dist t t' := by ring
      _ ≤ Lstar * dist t t' := mul_le_mul_of_nonneg_right hL2 dist_nonneg

/-- **The kernel of the sampled walk with the heat kernel of the torus: quantitative bound with
    Bernstein's inequality and the decaying bounds of the convolution powers.** As
    `heatTorus_walk_whp`, with `B_j = (1 + √(π/((j+1)c)))^d` in place of `M` for the `j`-th convolution
    power, both in the error term and in the exponents: the probability is at most
    `2 m^d exp(-epsn0²/(4NM + 2M epsn0)) + ∑_{j<k} 2 m^{2d} exp(-epsc0²/(4N M B_j B_{j+1} + 2 M B_j epsc0))`.
    Still weaker than the theorem of the paper: the consistency error enters without the factor
    `m^{-1/2}` and without the Gaussian weight, so the error is a sum over `j < k` of terms of the
    size of the deviation and not `√k m_k` times it. -/
theorem heatTorus_walk_bernstein {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {c : ℝ} (hc : 0 < c) (k : ℕ) {m : ℕ} (hm : 0 < m) (N : ℕ) [NeZero N]
    {M L : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / c)) ^ d)
    (hLdef : L = 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d)
    (epsn0 epsc0 : ℝ) (hn : 0 < epsn0) (hcc : 0 < epsc0)
    (hsmall : epsn0 + 2 * (N * L) * (1 / m) ≤ N / 8) :
    μ.real {ω | ∃ a i : Fin N,
        10 * ((epsn0 + 2 * (N * L) * (1 / m)) / N) * (heatTorus d ((k + 1 : ℕ) * c) (X a ω - X i ω)
            + ∑ j ∈ Finset.range k,
                (3 * ((epsc0 + 2 * (N * (L * M + M * L + 2 * L)) * (1 / m)) / N)
                  + 11 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
                      * (1 + Real.sqrt (Real.pi / ((j + 1 + 1 : ℕ) * c))) ^ d))
          + ∑ j ∈ Finset.range k,
              (3 * ((epsc0 + 2 * (N * (L * M + M * L + 2 * L)) * (1 / m)) / N)
                + 11 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
                    * (1 + Real.sqrt (Real.pi / ((j + 1 + 1 : ℕ) * c))) ^ d)
        < |(N : ℝ) * (walkMatrix (fun i j : Fin N => heatTorus d c (X i ω - X j ω))
            (fun i : Fin N => (∑ l : Fin N, heatTorus d c (X i ω - X l ω)) / N) ^ (k + 1)) a i
            - heatTorus d ((k + 1 : ℕ) * c) (X a ω - X i ω)|}
      ≤ (m : ℝ) ^ d * (2 * Real.exp (-epsn0 ^ 2 / (4 * (N * M) + 2 * M * epsn0)))
        + ∑ j ∈ Finset.range k, (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2
            / (4 * (N * (M * (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d
                  * (1 + Real.sqrt (Real.pi / ((j + 1 + 1 : ℕ) * c))) ^ d))
              + 2 * (M * (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d) * epsc0))) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have habs : ∀ {c' : ℝ}, 0 < c' →
      Summable fun n : Fin d → ℤ => |Real.exp (-c' * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := fun hc' => by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc' d
  have hcont : ∀ {c' : ℝ}, 0 < c' → Continuous (heatTorus d c') := fun hc' =>
    cosSeries_continuous d _ (habs hc')
  have hmc : ∀ m' : ℕ, 0 < ((m' + 1 : ℕ) : ℝ) * c := fun m' => by positivity
  have hM1 : 1 ≤ M := by
    rw [hMdef]; exact one_le_pow₀ (by linarith [Real.sqrt_nonneg (Real.pi / c)])
  have hM0 : 0 < M := by linarith
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hp0 := heatTorus_nonneg hc d
  have hpM : ∀ u, heatTorus d c u ≤ M := fun u => by rw [hMdef]; exact heatTorus_le hc d u
  have hplip : ∀ u u', |heatTorus d c u - heatTorus d c u'| ≤ L * dist u u' := fun u u' => by
    rw [hLdef]; exact heatTorus_lipschitz hc d u u'
  have hlipm : ∀ (m' : ℕ) (u u' : FlatTorus d),
      |heatTorus d ((m' + 1 : ℕ) * c) u - heatTorus d ((m' + 1 : ℕ) * c) u'| ≤ L * dist u u' :=
    fun m' u u' => (heatTorus_lipschitz (hmc m') d u u').trans
      (mul_le_mul_of_nonneg_right (by rw [hLdef]; exact heatLip_anti hc d m') dist_nonneg)
  have hconv := fun j => (heatTorus_convPow hc d j).1
  have hBfM : ∀ j : ℕ, (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d ≤ M := fun j => by
    rw [hMdef]; exact heatBound_anti hc d j Real.pi Real.pi_pos.le
  have hBfpos : ∀ j : ℕ, 0 < (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d := fun j => by
    positivity
  -- normalisation
  have hBn := uniform_concentration_bernstein (μ := μ) (T := FlatTorus d) X h_indep hX
    (fun x y => heatTorus d c (x - y))
    (fun x => (hcont hc).measurable.comp (measurable_const.sub measurable_id)) hM0 hL0
    (fun x y => ⟨hp0 _, hpM _⟩)
    (fun x x' y => by have := hplip (x - y) (x' - y); rwa [dist_sub_right] at this)
    (fun _ => 1)
    (fun x j => by
      have h1 : ∫ ω, heatTorus d c (x - X j ω) ∂μ
          = ∫ y, heatTorus d c (x - y) ∂(μ.map (X j)) :=
        (integral_map (hX j).aemeasurable
          (((hcont hc).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).symm
      rw [h1, hlaw j, integral_sub_left_eq_self (heatTorus d c) (flatTorusMeasure d) x,
        heatTorus_mass hc d])
    (qmax := 1) (fun _ => le_rfl)
    (fun x x' => by simpa using mul_nonneg hL0 dist_nonneg)
    (torusNet d m) (torusNet_dense d hm) N hn
  simp only [mul_one] at hBn
  -- consistency
  have hBc : ∀ j < k, μ.real {ω | ∃ u : FlatTorus d × FlatTorus d,
        epsc0 + 2 * (N * (L * M + M * L + 2 * L)) * (1 / m)
        < |∑ l ∈ Finset.range N, heatTorus d c (u.1 - X l ω)
              * convPow (flatTorusMeasure d) (heatTorus d c) j (X l ω - u.2)
            - N * convPow (flatTorusMeasure d) (heatTorus d c) (j + 1) (u.1 - u.2)|}
      ≤ (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2
            / (4 * (N * (M * (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d
                  * (1 + Real.sqrt (Real.pi / ((j + 1 + 1 : ℕ) * c))) ^ d))
              + 2 * (M * (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d) * epsc0))) := by
    intro j _
    have h := consistency_uniform_bernstein (μ := μ) (flatTorusMeasure d)
      (fun x x' y => dist_sub_right x x' y) (fun x y y' => dist_sub_left x y y')
      X h_indep hX hlaw (heatTorus d c) j
      (fun x y => by
        rw [hconv j]
        exact ((hcont hc).measurable.comp (measurable_const.sub measurable_id)).mul
          ((hcont (hmc j)).measurable.comp (measurable_id.sub measurable_const)))
      (M := M) (B := (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d)
      (Bq := (1 + Real.sqrt (Real.pi / ((j + 1 + 1 : ℕ) * c))) ^ d)
      (L := L) (Lq := L) (Lq' := L) (Lstar := L * M + M * L + 2 * L) (r := 1 / m)
      hM0.le (hBfpos j).le (mul_pos hM0 (hBfpos j))
      (fun u => by rw [hconv (j + 1)]; exact heatTorus_le (hmc (j + 1)) d u)
      hL0 hL0 hL0 hp0 hpM
      (fun u => by rw [hconv j]; exact heatTorus_nonneg (hmc j) d u)
      (fun u => by rw [hconv j]; exact heatTorus_le (hmc j) d u)
      hplip
      (fun u u' => by rw [hconv j]; exact hlipm j u u')
      (fun u u' => by rw [hconv (j + 1)]; exact hlipm (j + 1) u u')
      (by nlinarith [mul_le_mul_of_nonneg_left (hBfM j) hL0, mul_nonneg hL0 hM0.le])
      (by nlinarith [mul_nonneg hL0 hM0.le])
      (torusNet d m ×ˢ torusNet d m) (torusNet2_dense d hm) N hcc
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast torusNet2_card d m
  have hc1' : ((torusNet d m).card : ℝ) ≤ (m : ℝ) ^ d := by exact_mod_cast torusNet_card d m
  have key := kernel_fixed_scale_whp (μ := μ) (flatTorusMeasure d) X (heatTorus d c)
    (fun j => (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d) N k
    (fun j u => by rw [hconv j]; exact heatTorus_nonneg (hmc j) d u)
    (fun j u => by rw [hconv j]; exact heatTorus_le (hmc j) d u)
    (fun ω => walkMatrix (fun i j : Fin N => heatTorus d c (X i ω - X j ω))
      (fun i : Fin N => (∑ l : Fin N, heatTorus d c (X i ω - X l ω)) / N))
    (fun ω b j => by
      refine walkMatrix_apply' _ _ b j ?_
      have hpos : 0 < ∑ l : Fin N, heatTorus d c (X b ω - X l ω) := by
        have h1 : heatTorus d c (X b ω - X b ω) ≤ ∑ l : Fin N, heatTorus d c (X b ω - X l ω) :=
          Finset.single_le_sum (f := fun l : Fin N => heatTorus d c (X b ω - X l ω))
            (fun l _ => hp0 _) (Finset.mem_univ b)
        rw [sub_self] at h1
        linarith [heatTorus_zero_pos hc d]
      exact (div_pos hpos hNpos).ne')
    (fun j => (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2
            / (4 * (N * (M * (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d
                  * (1 + Real.sqrt (Real.pi / ((j + 1 + 1 : ℕ) * c))) ^ d))
              + 2 * (M * (1 + Real.sqrt (Real.pi / ((j + 1 : ℕ) * c))) ^ d) * epsc0))))
    (by positivity) hsmall
    (hBn.trans (mul_le_mul_of_nonneg_right hc1' (by positivity))) hBc
  rw [hconv k] at key
  exact key

section TorusEigSampleB
open Matrix

/-- **Eigenvalues of the sampled graph on the flat torus for random samples, with Bernstein's
    inequality.** As `heatTorus_eig_sample`, with the probabilities of `heatTorus_walk_bernstein`:
    `2 m^d exp(-epsn0²/(4NM + 2M epsn0)) + ∑_{j<k} 2 m^{2d} exp(-epsc0²/(4N M B_j B_{j+1} + 2 M B_j epsc0))
    + 2 |modes|² exp(-(N eta/2)²/(2N))`. Still a weak form of the theorem of the paper. -/
theorem heatTorus_eig_sample_bernstein {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : ℝ} (hc : 0 < c) (d N : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (k : ℕ) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {m : ℕ} (hm : 0 < m) {M L R eta t E Dk eps α epsn0 epsc0 : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / c)) ^ d)
    (hLdef : L = 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hn0 : 0 < epsn0) (hc0 : 0 < epsc0) (heta : 0 ≤ eta)
    (hsmall : epsn0 + 2 * (N * L) * (1 / m) ≤ N / 8)
    (ht : Real.exp (-((k + 1 : ℕ) * c) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k + 1 : ℕ) * c))) ^ d ≤ t)
    (hE : ∑ m' ∈ Finset.range k,
        (3 * ((epsc0 + 2 * (N * (L * M + M * L + 2 * L)) * (1 / m)) / N)
          + 11 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
              * (1 + Real.sqrt (Real.pi / ((m' + 2 : ℕ) * c))) ^ d) ≤ E)
    (hDk : 10 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
        * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + E) + E ≤ Dk)
    (heps : 3 * ((epsn0 + 2 * (N * L) * (1 / m)) / N)
        * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + Dk) + Dk + t ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) < modeCoeff d ((k + 1 : ℕ) * c) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) ≤ modeCoeff d ((k + 1 : ℕ) * c) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)) ≤ α ^ (k + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph (fun i j : Fin N => heatTorus d c (X i ω - X j ω))
          (fun i : Fin N => (∑ l : Fin N, heatTorus d c (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)
          ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1))}
      ≤ (m : ℝ) ^ d * (2 * Real.exp (-epsn0 ^ 2 / (4 * (N * M) + 2 * M * epsn0)))
        + ∑ j' ∈ Finset.range k, (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2
            / (4 * (N * (M * (1 + Real.sqrt (Real.pi / ((j' + 1 : ℕ) * c))) ^ d
                  * (1 + Real.sqrt (Real.pi / ((j' + 1 + 1 : ℕ) * c))) ^ d))
              + 2 * (M * (1 + Real.sqrt (Real.pi / ((j' + 1 : ℕ) * c))) ^ d) * epsc0)))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2
            * (2 * Real.exp (-(N * eta / 2) ^ 2 / (2 * N))) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have habs : ∀ {c' : ℝ}, 0 < c' →
      Summable fun n : Fin d → ℤ => |Real.exp (-c' * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := fun hc' => by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc' d
  have hcont : ∀ {c' : ℝ}, 0 < c' → Continuous (heatTorus d c') := fun hc' =>
    cosSeries_continuous d _ (habs hc')
  have hmc : ∀ m' : ℕ, 0 < ((m' + 1 : ℕ) : ℝ) * c := fun m' => by positivity
  have hM0' : 0 < M := by rw [hMdef]; positivity
  have hM0 : 0 ≤ M := hM0'.le
  have hBfpos : ∀ j' : ℕ, 0 < (1 + Real.sqrt (Real.pi / ((j' + 1 : ℕ) * c))) ^ d := fun j' => by
    positivity
  have hBfM : ∀ j' : ℕ, (1 + Real.sqrt (Real.pi / ((j' + 1 : ℕ) * c))) ^ d ≤ M := fun j' => by
    rw [hMdef]; exact heatBound_anti hc d j' Real.pi Real.pi_pos.le
  have hL0 : 0 ≤ L := by rw [hLdef]; positivity
  have hpM : ∀ u, heatTorus d c u ≤ M := fun u => by rw [hMdef]; exact heatTorus_le hc d u
  have hplip : ∀ u u', |heatTorus d c u - heatTorus d c u'| ≤ L * dist u u' := fun u u' => by
    rw [hLdef]; exact heatTorus_lipschitz hc d u u'
  have hlipm : ∀ (m' : ℕ) (u u' : FlatTorus d),
      |heatTorus d ((m' + 1 : ℕ) * c) u - heatTorus d ((m' + 1 : ℕ) * c) u'| ≤ L * dist u u' :=
    fun m' u u' => (heatTorus_lipschitz (hmc m') d u u').trans
      (mul_le_mul_of_nonneg_right (by rw [hLdef]; exact heatLip_anti hc d m') dist_nonneg)
  have hr : (0 : ℝ) ≤ 1 / m := by positivity
  -- normalisation
  have hBn := uniform_concentration_bernstein (μ := μ) (T := FlatTorus d) X h_indep hX
    (fun x y => heatTorus d c (x - y))
    (fun x => (hcont hc).measurable.comp (measurable_const.sub measurable_id)) hM0' hL0
    (fun x y => ⟨heatTorus_nonneg hc d _, hpM _⟩)
    (fun x x' y => by
      have := hplip (x - y) (x' - y); rwa [dist_sub_right] at this)
    (fun _ => 1)
    (fun x j => by
      have h1 : ∫ ω, heatTorus d c (x - X j ω) ∂μ
          = ∫ y, heatTorus d c (x - y) ∂(μ.map (X j)) :=
        (integral_map (hX j).aemeasurable
          (((hcont hc).measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).symm
      rw [h1, hlaw j, integral_sub_left_eq_self (heatTorus d c) (flatTorusMeasure d) x,
        heatTorus_mass hc d])
    (qmax := 1) (fun _ => le_rfl)
    (fun x x' => by simpa using mul_nonneg hL0 dist_nonneg)
    (torusNet d m) (torusNet_dense d hm) N hn0
  simp only [mul_one] at hBn
  -- consistency
  have hBc : ∀ m' < k, μ.real {ω | ∃ u : FlatTorus d × FlatTorus d,
        epsc0 + 2 * (N * (L * M + M * L + 2 * L)) * (1 / m)
        < |∑ j ∈ Finset.range N, heatTorus d c (u.1 - X j ω)
              * heatTorus d ((m' + 1 : ℕ) * c) (X j ω - u.2)
            - N * heatTorus d ((m' + 1 + 1 : ℕ) * c) (u.1 - u.2)|}
      ≤ (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2
            / (4 * (N * (M * (1 + Real.sqrt (Real.pi / ((m' + 1 : ℕ) * c))) ^ d
                  * (1 + Real.sqrt (Real.pi / ((m' + 1 + 1 : ℕ) * c))) ^ d))
              + 2 * (M * (1 + Real.sqrt (Real.pi / ((m' + 1 : ℕ) * c))) ^ d) * epsc0))) := by
    intro m' _
    have h := consistency_uniform_bernstein (μ := μ) (flatTorusMeasure d)
      (fun x x' y => dist_sub_right x x' y) (fun x y y' => dist_sub_left x y y')
      X h_indep hX hlaw (heatTorus d c) m'
      (fun x y => by
        rw [(heatTorus_convPow hc d m').1]
        exact ((hcont hc).measurable.comp (measurable_const.sub measurable_id)).mul
          ((hcont (hmc m')).measurable.comp (measurable_id.sub measurable_const)))
      (M := M) (B := (1 + Real.sqrt (Real.pi / ((m' + 1 : ℕ) * c))) ^ d)
      (Bq := (1 + Real.sqrt (Real.pi / ((m' + 1 + 1 : ℕ) * c))) ^ d)
      (L := L) (Lq := L) (Lq' := L) (Lstar := L * M + M * L + 2 * L)
      (r := 1 / m) hM0 (hBfpos m').le (mul_pos hM0' (hBfpos m'))
      (fun u => by rw [(heatTorus_convPow hc d (m' + 1)).1]; exact heatTorus_le (hmc (m' + 1)) d u)
      hL0 hL0 hL0 (heatTorus_nonneg hc d) hpM
      (fun u => by rw [(heatTorus_convPow hc d m').1]; exact heatTorus_nonneg (hmc m') d u)
      (fun u => by
        rw [(heatTorus_convPow hc d m').1]
        exact heatTorus_le (hmc m') d u)
      hplip
      (fun u u' => by rw [(heatTorus_convPow hc d m').1]; exact hlipm m' u u')
      (fun u u' => by rw [(heatTorus_convPow hc d (m' + 1)).1]; exact hlipm (m' + 1) u u')
      (by nlinarith [mul_le_mul_of_nonneg_left (hBfM m') hL0, mul_nonneg hL0 hM0])
      (by nlinarith [mul_nonneg hL0 hM0])
      (torusNet d m ×ˢ torusNet d m) (torusNet2_dense d hm) N hc0
    rw [(heatTorus_convPow hc d m').1, (heatTorus_convPow hc d (m' + 1)).1] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact_mod_cast torusNet2_card d m
  -- Gram matrix
  have hBg := flatTorus_gram_whp (μ := μ) d X h_indep hX hlaw (modeSet d H)
    (fun n b h => hH0 n ((mem_modeSet d H n b).mp h))
    (fun n b n' b' h h' => hH2 n ((mem_modeSet d H n b).mp h) n' ((mem_modeSet d H n' b').mp h'))
    N (ε := N * eta) (by positivity)
  have hc1' : ((torusNet d m).card : ℝ) ≤ (m : ℝ) ^ d := by exact_mod_cast torusNet_card d m
  exact heatTorus_eig_whp hc d N X k H hH0 hH2
    (fun j' => (m : ℝ) ^ (2 * d) * (2 * Real.exp (-epsc0 ^ 2
            / (4 * (N * (M * (1 + Real.sqrt (Real.pi / ((j' + 1 : ℕ) * c))) ^ d
                  * (1 + Real.sqrt (Real.pi / ((j' + 1 + 1 : ℕ) * c))) ^ d))
              + 2 * (M * (1 + Real.sqrt (Real.pi / ((j' + 1 : ℕ) * c))) ^ d) * epsc0))))
    hR (by positivity) hsmall heta
    (hBn.trans (mul_le_mul_of_nonneg_right hc1' (by positivity))) hBc hBg
    ht hE hDk heps j hα0 hα1 hc1 hc2 h3

end TorusEigSampleB

/-! ### The heat kernel of the torus as a periodised Gaussian; (P1) -/

section PerGauss
open Complex

/-- Summability of a shifted Gaussian over the integers. -/
theorem gauss_shift_summable {b : ℝ} (hb : 0 < b) (t : ℝ) :
    Summable fun n : ℤ => Real.exp (-b * ((n : ℝ) - t) ^ 2) := by
  have hb2 : 0 < b / 2 := by positivity
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    ((gauss_summable_int hb2).mul_left (Real.exp (b * t ^ 2)))
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [_root_.sq_nonneg ((n : ℝ) - 2 * t), _root_.sq_nonneg ((n : ℝ)), _root_.sq_nonneg t]

/-- The one-dimensional periodised Gaussian in the variable of the Fourier form:
    `perGauss c t = (π/c)^{1/2} ∑_n e^{-(π²/c)(n - t)²}`; with `c = 2π²τ` this is
    `∑_n (2πτ)^{-1/2} e^{-(t - n)²/(2τ)}`. -/
noncomputable def perGauss (c t : ℝ) : ℝ :=
  1 / (c / Real.pi) ^ (1 / 2 : ℝ) * ∑' n : ℤ, Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2)

/-- **Poisson summation, one variable:** the Fourier series equals the periodised Gaussian. -/
theorem theta_factor_eq {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∑' j : ℤ, ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j ((t : ℝ) : UnitAddCircle)
      = (perGauss c t : ℂ) := by
  have ha : 0 < c / Real.pi := div_pos hc Real.pi_pos
  have hP := Complex.tsum_exp_neg_quadratic (a := ((c / Real.pi : ℝ) : ℂ))
    (by rwa [ofReal_re]) (I * t)
  have hL : ∀ j : ℤ, ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j ((t : ℝ) : UnitAddCircle)
      = cexp (-Real.pi * ((c / Real.pi : ℝ) : ℂ) * j ^ 2 + 2 * Real.pi * (I * t) * j) := by
    intro j
    rw [fourier_coe_apply, ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
  have hR : ∀ n : ℤ, cexp (-Real.pi / ((c / Real.pi : ℝ) : ℂ) * (n + I * (I * t)) ^ 2)
      = ((Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2) : ℝ) : ℂ) := by
    intro n
    rw [ofReal_exp]
    congr 1
    have : (n : ℂ) + I * (I * t) = ((n : ℝ) - t : ℝ) := by
      rw [← mul_assoc, I_mul_I]; push_cast; ring
    rw [this]; push_cast; ring
  simp_rw [hL]
  rw [hP]
  simp_rw [hR]
  rw [← ofReal_tsum]
  unfold perGauss
  push_cast
  rw [ofReal_cpow ha.le]
  push_cast
  ring

/-- The periodised Gaussian is nonnegative. -/
theorem perGauss_nonneg {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 ≤ perGauss c t := by
  have ha : 0 < c / Real.pi := div_pos hc Real.pi_pos
  unfold perGauss
  exact mul_nonneg (by positivity) (tsum_nonneg fun n => (Real.exp_pos _).le)

/-- **The heat kernel of the flat torus is the product of one-dimensional periodised Gaussians.** -/
theorem heatTorus_eq_prod {c : ℝ} (hc : 0 < c) (d : ℕ) (t : Fin d → ℝ) :
    heatTorus d c (fun i => ((t i : ℝ) : UnitAddCircle)) = ∏ i, perGauss c (t i) := by
  set x : FlatTorus d := fun i => ((t i : ℝ) : UnitAddCircle) with hx
  have hnorm : ∀ (i : Fin d) (j : ℤ),
      ‖((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j (x i)‖ = Real.exp (-c * (j : ℝ) ^ 2) := by
    intro i j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), fourier_apply,
      Circle.norm_coe, mul_one]
  have hS := hasSum_pi_prod d (fun i j => ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j (x i))
    (fun i => by simp_rw [hnorm]; exact gauss_summable_int hc)
  have hreq : ∀ i, ∑' j : ℤ, ((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j (x i)
      = (perGauss c (t i) : ℂ) := fun i => theta_factor_eq hc (t i)
  simp_rw [hreq] at hS
  have hG : ∀ n : Fin d → ℤ,
      (∏ i, ((Real.exp (-c * ((n i : ℤ) : ℝ) ^ 2) : ℝ) : ℂ) * fourier (n i) (x i)).re
        = Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2) * (torusChar d n x).re := by
    intro n
    rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum]
    unfold torusChar
    rw [Complex.re_ofReal_mul]
  have hre := Complex.hasSum_re hS
  simp_rw [hG] at hre
  have hval : heatTorus d c x = (∏ i, (perGauss c (t i) : ℂ)).re := hre.tsum_eq
  rw [hval, ← Complex.ofReal_prod, Complex.ofReal_re]

/-- (P1) in one variable: for `c_a ≤ c_t`, `perGauss c_a ≤ (c_t/c_a)^{1/2} perGauss c_t`. -/
theorem perGauss_P1 {ca ct : ℝ} (ha : 0 < ca) (hat : ca ≤ ct) (t : ℝ) :
    perGauss ca t ≤ (ct / ca) ^ (1 / 2 : ℝ) * perGauss ct t := by
  have ht : 0 < ct := lt_of_lt_of_le ha hat
  have h1 : 0 < ca / Real.pi := div_pos ha Real.pi_pos
  have h2 : 0 < ct / Real.pi := div_pos ht Real.pi_pos
  unfold perGauss
  have hsum : ∑' n : ℤ, Real.exp (-Real.pi / (ca / Real.pi) * ((n : ℝ) - t) ^ 2)
      ≤ ∑' n : ℤ, Real.exp (-Real.pi / (ct / Real.pi) * ((n : ℝ) - t) ^ 2) := by
    have e1 : ∀ c' : ℝ, 0 < c' → (fun n : ℤ => Real.exp (-Real.pi / (c' / Real.pi) * ((n : ℝ) - t) ^ 2))
        = fun n : ℤ => Real.exp (-(Real.pi / (c' / Real.pi)) * ((n : ℝ) - t) ^ 2) := fun c' _ => by
      funext n; rw [neg_div]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ ?_
    · apply Real.exp_le_exp.mpr
      have : Real.pi / (ct / Real.pi) ≤ Real.pi / (ca / Real.pi) :=
        div_le_div_of_nonneg_left Real.pi_pos.le h1 (div_le_div_of_nonneg_right hat Real.pi_pos.le)
      rw [neg_div, neg_div]
      nlinarith [_root_.sq_nonneg ((n : ℝ) - t)]
    · rw [e1 ca ha]; exact gauss_shift_summable (by positivity) t
    · rw [e1 ct ht]; exact gauss_shift_summable (by positivity) t
  have hpre : 1 / (ca / Real.pi) ^ (1 / 2 : ℝ)
      = (ct / ca) ^ (1 / 2 : ℝ) * (1 / (ct / Real.pi) ^ (1 / 2 : ℝ)) := by
    have : ct / ca = (ct / Real.pi) / (ca / Real.pi) := by field_simp
    rw [this, Real.div_rpow h2.le h1.le]
    have h3 : 0 < (ct / Real.pi) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h2 _
    have h4 : 0 < (ca / Real.pi) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h1 _
    field_simp
  rw [hpre, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)

/-- Every point of the flat torus has real coordinates. -/
theorem flatTorus_lift (d : ℕ) (x : FlatTorus d) :
    ∃ t : Fin d → ℝ, x = fun i => ((t i : ℝ) : UnitAddCircle) := by
  choose t ht using fun i => QuotientAddGroup.mk_surjective (x i)
  exact ⟨t, funext fun i => (ht i).symm⟩

/-- **(P1) for the heat kernel of the torus:** for `c_a ≤ c_t`,
    `p_{c_a} ≤ (c_t/c_a)^{d/2} p_{c_t}` pointwise. -/
theorem heatTorus_P1 {ca ct : ℝ} (ha : 0 < ca) (hat : ca ≤ ct) (d : ℕ) (x : FlatTorus d) :
    heatTorus d ca x ≤ ((ct / ca) ^ (1 / 2 : ℝ)) ^ d * heatTorus d ct x := by
  obtain ⟨t, rfl⟩ := flatTorus_lift d x
  have ht : 0 < ct := lt_of_lt_of_le ha hat
  rw [heatTorus_eq_prod ha, heatTorus_eq_prod ht]
  calc ∏ i, perGauss ca (t i) ≤ ∏ i : Fin d, (ct / ca) ^ (1 / 2 : ℝ) * perGauss ct (t i) :=
        Finset.prod_le_prod (fun i _ => perGauss_nonneg ha _) (fun i _ => perGauss_P1 ha hat _)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PerGauss

/-! ### Core of (P5) -/

/-- `√(∑ a_i) ≤ ∑ √a_i` for finite sums of nonnegative numbers. -/
theorem sqrt_finset_sum_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Real.sqrt (∑ i ∈ s, a i) ≤ ∑ i ∈ s, Real.sqrt (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have h1 : Real.sqrt (a j + ∑ i ∈ s, a i) ≤ Real.sqrt (a j) + Real.sqrt (∑ i ∈ s, a i) := by
      rw [Real.sqrt_le_left (by positivity)]
      have e1 := Real.sq_sqrt (ha j)
      have e2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => ha i : (0:ℝ) ≤ ∑ i ∈ s, a i)
      nlinarith [Real.sqrt_nonneg (a j), Real.sqrt_nonneg (∑ i ∈ s, a i)]
    linarith

open Filter Topology in
/-- The square root of a series of nonnegative terms is at most the series of the square roots. -/
theorem sqrt_tsum_le {ι : Type*} (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hs : Summable a)
    (hs' : Summable fun i => Real.sqrt (a i)) :
    Real.sqrt (∑' i, a i) ≤ ∑' i, Real.sqrt (a i) := by
  have h1 : Tendsto (fun s : Finset ι => Real.sqrt (∑ i ∈ s, a i)) atTop
      (𝓝 (Real.sqrt (∑' i, a i))) :=
    (Real.continuous_sqrt.tendsto _).comp hs.hasSum
  refine le_of_tendsto h1 (Eventually.of_forall fun s => ?_)
  exact (sqrt_finset_sum_le s a ha).trans (hs'.sum_le_tsum s fun i _ => Real.sqrt_nonneg _)

/-- **Core of (P5) in one variable:** `√(perGauss c t) · pre(2c) ≤ √(pre(c)) · perGauss (2c) t`, where
    `pre(c) = 1/(c/π)^{1/2}` is the prefactor of the periodised Gaussian. -/
theorem perGauss_sqrt {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Real.sqrt (perGauss c t) * (1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ))
      ≤ Real.sqrt (1 / (c / Real.pi) ^ (1 / 2 : ℝ)) * perGauss (2 * c) t := by
  have ha : 0 < c / Real.pi := div_pos hc Real.pi_pos
  have ha2 : 0 < 2 * c / Real.pi := div_pos (by positivity) Real.pi_pos
  have hpre : 0 ≤ 1 / (c / Real.pi) ^ (1 / 2 : ℝ) := by positivity
  have hpre2 : 0 ≤ 1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ) := by positivity
  have hb : 0 < Real.pi / (c / Real.pi) := div_pos Real.pi_pos ha
  have e1 : (fun n : ℤ => Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2))
      = fun n : ℤ => Real.exp (-(Real.pi / (c / Real.pi)) * ((n : ℝ) - t) ^ 2) := by
    funext n; rw [neg_div]
  have hsqrt : ∀ n : ℤ, Real.sqrt (Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2))
      = Real.exp (-Real.pi / (2 * c / Real.pi) * ((n : ℝ) - t) ^ 2) := by
    intro n
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hs1 : Summable fun n : ℤ => Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2) := by
    rw [e1]; exact gauss_shift_summable hb t
  have hs2 : Summable fun n : ℤ =>
      Real.sqrt (Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2)) := by
    simp_rw [hsqrt]
    have : (fun n : ℤ => Real.exp (-Real.pi / (2 * c / Real.pi) * ((n : ℝ) - t) ^ 2))
        = fun n : ℤ => Real.exp (-(Real.pi / (2 * c / Real.pi)) * ((n : ℝ) - t) ^ 2) := by
      funext n; rw [neg_div]
    rw [this]; exact gauss_shift_summable (div_pos Real.pi_pos ha2) t
  have h := sqrt_tsum_le _ (fun n => (Real.exp_pos _).le) hs1 hs2
  simp_rw [hsqrt] at h
  unfold perGauss
  rw [Real.sqrt_mul hpre]
  calc Real.sqrt (1 / (c / Real.pi) ^ (1 / 2 : ℝ))
        * Real.sqrt (∑' n : ℤ, Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2))
        * (1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ))
      ≤ Real.sqrt (1 / (c / Real.pi) ^ (1 / 2 : ℝ))
        * (∑' n : ℤ, Real.exp (-Real.pi / (2 * c / Real.pi) * ((n : ℝ) - t) ^ 2))
        * (1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring

/-! ### (P4) in one variable -/

section P4
open Complex

/-- `∑_{j ∈ ℤ} e^{-c j²} ≤ 1 + √(π/c)`. -/
theorem gauss_tsum_int_le {c : ℝ} (hc : 0 < c) :
    ∑' j : ℤ, Real.exp (-c * (j : ℝ) ^ 2) ≤ 1 + Real.sqrt (Real.pi / c) := by
  refine (gauss_summable_int hc).tsum_le_of_sum_le fun T => ?_
  have hsub : T ⊆ Finset.Icc (-((T.sup Int.natAbs : ℕ) : ℤ)) (T.sup Int.natAbs : ℕ) := by
    intro j hj
    have : j.natAbs ≤ T.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hj
    rw [Finset.mem_Icc]; omega
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => (Real.exp_pos _).le).trans
    (gauss_sum_int_le hc _)

/-- **Uniform bound for the periodised Gaussian (one variable):** `perGauss c t ≤ 1 + √(π/c)`.
    Equivalently `∑_n e^{-b(n-t)²} ≤ √(π/b) + 1` for every shift `t`. -/
theorem perGauss_le {c : ℝ} (hc : 0 < c) (t : ℝ) : perGauss c t ≤ 1 + Real.sqrt (Real.pi / c) := by
  have h := theta_factor_eq hc t
  have hn : ∀ j : ℤ, ‖((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j ((t : ℝ) : UnitAddCircle)‖
      = Real.exp (-c * (j : ℝ) ^ 2) := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), fourier_apply,
      Circle.norm_coe, mul_one]
  have hs : Summable fun j : ℤ =>
      ‖((Real.exp (-c * (j : ℝ) ^ 2) : ℝ) : ℂ) * fourier j ((t : ℝ) : UnitAddCircle)‖ := by
    simp_rw [hn]; exact gauss_summable_int hc
  have h1 := norm_tsum_le_tsum_norm hs
  rw [h] at h1
  simp_rw [hn] at h1
  rw [Complex.norm_real, Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans (h1.trans (gauss_tsum_int_le hc))

/-- Shifted Gaussian sums are bounded uniformly in the shift. -/
theorem gauss_shift_tsum_le {b : ℝ} (hb : 0 < b) (t : ℝ) :
    ∑' n : ℤ, Real.exp (-b * ((n : ℝ) - t) ^ 2) ≤ Real.sqrt (Real.pi / b) + 1 := by
  have hc : 0 < Real.pi ^ 2 / b := by positivity
  have h := perGauss_le hc t
  unfold perGauss at h
  have e1 : Real.pi ^ 2 / b / Real.pi = Real.pi / b := by field_simp
  have e2 : -Real.pi / (Real.pi / b) = -b := by field_simp
  rw [e1, e2] at h
  have hpos : 0 < (Real.pi / b) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hsq : (Real.pi / b) ^ (1 / 2 : ℝ) = Real.sqrt (Real.pi / b) := (Real.sqrt_eq_rpow _).symm
  have e3 : Real.pi / (Real.pi ^ 2 / b) = b / Real.pi := by field_simp
  rw [e3] at h
  have hsb : Real.sqrt (b / Real.pi) * Real.sqrt (Real.pi / b) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    have : b / Real.pi * (Real.pi / b) = 1 := by field_simp
    rw [this, Real.sqrt_one]
  rw [hsq] at h hpos
  have h2 : ∑' n : ℤ, Real.exp (-b * ((n : ℝ) - t) ^ 2)
      ≤ Real.sqrt (Real.pi / b) * (1 + Real.sqrt (b / Real.pi)) := by
    have := mul_le_mul_of_nonneg_left h hpos.le
    rwa [← mul_assoc, mul_one_div_cancel hpos.ne', one_mul] at this
  nlinarith [h2, hsb]

/-- **Double-sum step of (P4), one variable.** For `a, t > 0` and all real `u, z`,
    `(∑_n e^{-(n-u)²/(2a)}) (∑_{n'} e^{-(n'-(z-u))²/(2t)})
      ≤ (∑_n e^{-(n-u)²/(4a)}) (∑_n e^{-(n-z)²/(2(t+2a))})`. -/
theorem gauss_double_sum {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (u z : ℝ) :
    (∑' n : ℤ, Real.exp (-(1 / (2 * a)) * ((n : ℝ) - u) ^ 2))
        * (∑' n : ℤ, Real.exp (-(1 / (2 * t)) * ((n : ℝ) - (z - u)) ^ 2))
      ≤ (∑' n : ℤ, Real.exp (-(1 / (4 * a)) * ((n : ℝ) - u) ^ 2))
        * (∑' n : ℤ, Real.exp (-(1 / (2 * (t + 2 * a))) * ((n : ℝ) - z) ^ 2)) := by
  have hf := gauss_shift_summable (b := 1 / (2 * a)) (by positivity) u
  have hg := gauss_shift_summable (b := 1 / (2 * t)) (by positivity) (z - u)
  have hF := gauss_shift_summable (b := 1 / (4 * a)) (by positivity) u
  have hG := gauss_shift_summable (b := 1 / (2 * (t + 2 * a))) (by positivity) z
  have hfg := Summable.mul_of_nonneg hf hg (fun n => (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le)
  have hFG := Summable.mul_of_nonneg hF hG (fun n => (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le)
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1, p.1 + p.2), invFun := fun p => (p.1, p.2 - p.1),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  have hFG' : Summable fun p : ℤ × ℤ =>
      Real.exp (-(1 / (4 * a)) * ((p.1 : ℝ) - u) ^ 2)
        * Real.exp (-(1 / (2 * (t + 2 * a))) * (((p.1 + p.2 : ℤ) : ℝ) - z) ^ 2) :=
    (Equiv.summable_iff e).mpr hFG
  have hR : ∑' p : ℤ × ℤ, Real.exp (-(1 / (4 * a)) * ((p.1 : ℝ) - u) ^ 2)
        * Real.exp (-(1 / (2 * (t + 2 * a))) * ((p.2 : ℝ) - z) ^ 2)
      = ∑' p : ℤ × ℤ, Real.exp (-(1 / (4 * a)) * ((p.1 : ℝ) - u) ^ 2)
        * Real.exp (-(1 / (2 * (t + 2 * a))) * (((p.1 + p.2 : ℤ) : ℝ) - z) ^ 2) :=
    (Equiv.tsum_eq e (fun p : ℤ × ℤ => Real.exp (-(1 / (4 * a)) * ((p.1 : ℝ) - u) ^ 2)
        * Real.exp (-(1 / (2 * (t + 2 * a))) * ((p.2 : ℝ) - z) ^ 2))).symm
  rw [hf.tsum_mul_tsum hg hfg, hF.tsum_mul_tsum hG hFG, hR]
  refine hfg.tsum_le_tsum (fun p => ?_) hFG'
  show Real.exp (-(1 / (2 * a)) * ((p.1 : ℝ) - u) ^ 2)
      * Real.exp (-(1 / (2 * t)) * ((p.2 : ℝ) - (z - u)) ^ 2)
    ≤ Real.exp (-(1 / (4 * a)) * ((p.1 : ℝ) - u) ^ 2)
      * Real.exp (-(1 / (2 * (t + 2 * a))) * (((p.1 + p.2 : ℤ) : ℝ) - z) ^ 2)
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := gauss_product_core ha ht ((p.1 : ℝ) - u) ((p.2 : ℝ) - (z - u))
  have e1 : ((p.1 : ℝ) - u) + ((p.2 : ℝ) - (z - u)) = ((p.1 + p.2 : ℤ) : ℝ) - z := by
    push_cast; ring
  rw [e1] at h
  have r1 : (1 / (2 * a)) * ((p.1 : ℝ) - u) ^ 2 = ((p.1 : ℝ) - u) ^ 2 / (2 * a) := by ring
  have r2 : (1 / (2 * t)) * ((p.2 : ℝ) - (z - u)) ^ 2 = ((p.2 : ℝ) - (z - u)) ^ 2 / (2 * t) := by ring
  have r3 : (1 / (4 * a)) * ((p.1 : ℝ) - u) ^ 2 = ((p.1 : ℝ) - u) ^ 2 / (4 * a) := by ring
  have r4 : (1 / (2 * (t + 2 * a))) * (((p.1 + p.2 : ℤ) : ℝ) - z) ^ 2
      = (((p.1 + p.2 : ℤ) : ℝ) - z) ^ 2 / (2 * (t + 2 * a)) := by ring
  linarith

/-- The periodised Gaussian in the time variable `τ` (`c = 2π²τ`):
    `perGauss (2π²τ) x = (2πτ)^{-1/2} ∑_n e^{-(n-x)²/(2τ)}`. -/
theorem perGauss_time {τ : ℝ} (hτ : 0 < τ) (x : ℝ) :
    perGauss (2 * Real.pi ^ 2 * τ) x
      = 1 / (2 * Real.pi * τ) ^ (1 / 2 : ℝ)
        * ∑' n : ℤ, Real.exp (-(1 / (2 * τ)) * ((n : ℝ) - x) ^ 2) := by
  unfold perGauss
  have e1 : 2 * Real.pi ^ 2 * τ / Real.pi = 2 * Real.pi * τ := by
    field_simp
  have e2 : -Real.pi / (2 * Real.pi * τ) = -(1 / (2 * τ)) := by
    field_simp
  rw [e1, e2]

/-- **(P4) in one variable.** For `a, t > 0` and all real `u, z`, with `pre(τ) = (2πτ)^{-1/2}`,
    `p_a(u) p_t(z - u) · pre(t + 2a) ≤ pre(a) pre(t) (√(4πa) + 1) · p_{t+2a}(z)`. -/
theorem perGauss_P4 {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (u z : ℝ) :
    perGauss (2 * Real.pi ^ 2 * a) u * perGauss (2 * Real.pi ^ 2 * t) (z - u)
        * (1 / (2 * Real.pi * (t + 2 * a)) ^ (1 / 2 : ℝ))
      ≤ 1 / (2 * Real.pi * a) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * t) ^ (1 / 2 : ℝ))
        * (Real.sqrt (Real.pi / (1 / (4 * a))) + 1)
        * perGauss (2 * Real.pi ^ 2 * (t + 2 * a)) z := by
  have hta : 0 < t + 2 * a := by positivity
  rw [perGauss_time ha, perGauss_time ht, perGauss_time hta]
  have hd := gauss_double_sum ha ht u z
  have hs := gauss_shift_tsum_le (b := 1 / (4 * a)) (by positivity) u
  have hpa : 0 ≤ 1 / (2 * Real.pi * a) ^ (1 / 2 : ℝ) := by positivity
  have hpt : 0 ≤ 1 / (2 * Real.pi * t) ^ (1 / 2 : ℝ) := by positivity
  have hpta : 0 ≤ 1 / (2 * Real.pi * (t + 2 * a)) ^ (1 / 2 : ℝ) := by positivity
  have hG : 0 ≤ ∑' n : ℤ, Real.exp (-(1 / (2 * (t + 2 * a))) * ((n : ℝ) - z) ^ 2) :=
    tsum_nonneg fun n => (Real.exp_pos _).le
  have h1 : (∑' n : ℤ, Real.exp (-(1 / (2 * a)) * ((n : ℝ) - u) ^ 2))
        * (∑' n : ℤ, Real.exp (-(1 / (2 * t)) * ((n : ℝ) - (z - u)) ^ 2))
      ≤ (Real.sqrt (Real.pi / (1 / (4 * a))) + 1)
        * (∑' n : ℤ, Real.exp (-(1 / (2 * (t + 2 * a))) * ((n : ℝ) - z) ^ 2)) :=
    hd.trans (mul_le_mul_of_nonneg_right hs hG)
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg hpa hpt) hpta)
  calc _ = 1 / (2 * Real.pi * a) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * t) ^ (1 / 2 : ℝ))
        * (1 / (2 * Real.pi * (t + 2 * a)) ^ (1 / 2 : ℝ))
        * ((∑' n : ℤ, Real.exp (-(1 / (2 * a)) * ((n : ℝ) - u) ^ 2))
          * (∑' n : ℤ, Real.exp (-(1 / (2 * t)) * ((n : ℝ) - (z - u)) ^ 2))) := by ring
    _ ≤ _ := h2
    _ = _ := by ring

end P4

/-! ### (P4) and (P5) on the torus -/

/-- **(P4) for the heat kernel of the flat torus** (time variables, `c = 2π²τ`): for `a, t > 0`,
    `p_a(u) p_t(z - u) · pre(t+2a)^d ≤ (pre(a) pre(t) (√(4πa) + 1))^d · p_{t+2a}(z)`,
    `pre(τ) = (2πτ)^{-1/2}`. -/
theorem heatTorus_P4 {a t : ℝ} (ha : 0 < a) (ht : 0 < t) (d : ℕ) (u z : FlatTorus d) :
    heatTorus d (2 * Real.pi ^ 2 * a) u * heatTorus d (2 * Real.pi ^ 2 * t) (z - u)
        * (1 / (2 * Real.pi * (t + 2 * a)) ^ (1 / 2 : ℝ)) ^ d
      ≤ (1 / (2 * Real.pi * a) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * t) ^ (1 / 2 : ℝ))
          * (Real.sqrt (Real.pi / (1 / (4 * a))) + 1)) ^ d
        * heatTorus d (2 * Real.pi ^ 2 * (t + 2 * a)) z := by
  obtain ⟨tu, rfl⟩ := flatTorus_lift d u
  obtain ⟨tz, rfl⟩ := flatTorus_lift d z
  have hca : 0 < 2 * Real.pi ^ 2 * a := by positivity
  have hct : 0 < 2 * Real.pi ^ 2 * t := by positivity
  have hcta : 0 < 2 * Real.pi ^ 2 * (t + 2 * a) := by positivity
  have hsub : ((fun i => ((tz i : ℝ) : UnitAddCircle)) - fun i => ((tu i : ℝ) : UnitAddCircle))
      = fun i => (((tz i - tu i : ℝ)) : UnitAddCircle) := by
    funext i; simp
  rw [hsub, heatTorus_eq_prod hca, heatTorus_eq_prod hct, heatTorus_eq_prod hcta,
    ← Finset.prod_mul_distrib]
  have hcard : ∀ x : ℝ, x ^ d = ∏ _i : Fin d, x := fun x => by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hcard, hcard, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => perGauss_P4 ha ht (tu i) (tz i))
  exact mul_nonneg (mul_nonneg (perGauss_nonneg hca _) (perGauss_nonneg hct _)) (by positivity)

/-- **Core of (P5) on the torus:** `√(p_c(z)) · pre(2c)^d ≤ √(pre(c))^d · p_{2c}(z)`. -/
theorem heatTorus_sqrt {c : ℝ} (hc : 0 < c) (d : ℕ) (z : FlatTorus d) :
    Real.sqrt (heatTorus d c z) * (1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ)) ^ d
      ≤ (Real.sqrt (1 / (c / Real.pi) ^ (1 / 2 : ℝ))) ^ d * heatTorus d (2 * c) z := by
  obtain ⟨tz, rfl⟩ := flatTorus_lift d z
  have hc2 : 0 < 2 * c := by positivity
  rw [heatTorus_eq_prod hc, heatTorus_eq_prod hc2]
  have hsq : Real.sqrt (∏ i, perGauss c (tz i)) = ∏ i, Real.sqrt (perGauss c (tz i)) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Finset.prod_nonneg fun i _ => perGauss_nonneg hc _)
      (Finset.prod_nonneg fun i _ => Real.sqrt_nonneg _), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (Real.mul_self_sqrt (perGauss_nonneg hc _)).symm
  have hcard : ∀ x : ℝ, x ^ d = ∏ _i : Fin d, x := fun x => by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsq, hcard, hcard, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => perGauss_sqrt hc (tz i))
  exact mul_nonneg (Real.sqrt_nonneg _) (by positivity)

/-- **(P5) for the heat kernel of the flat torus, with an explicit factor:**
    `(p_{c'}(0) p_c(z))^{1/2} · pre(2c)^d ≤ (1 + √(π/c'))^{d/2} √(pre(c))^d · p_{2c}(z)`; in the lemma
    of the paper `c' = 2c/3` (times `2t` and `3t`) and `2c` is the time `6t`. -/
theorem heatTorus_P5 {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') (d : ℕ) (z : FlatTorus d) :
    Real.sqrt (heatTorus d c' 0 * heatTorus d c z) * (1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ)) ^ d
      ≤ Real.sqrt ((1 + Real.sqrt (Real.pi / c')) ^ d)
        * ((Real.sqrt (1 / (c / Real.pi) ^ (1 / 2 : ℝ))) ^ d * heatTorus d (2 * c) z) := by
  have h0 := heatTorus_nonneg hc' d 0
  rw [Real.sqrt_mul h0, mul_assoc]
  exact mul_le_mul (Real.sqrt_le_sqrt (heatTorus_le hc' d 0)) (heatTorus_sqrt hc d z)
    (mul_nonneg (Real.sqrt_nonneg _) (by positivity)) (Real.sqrt_nonneg _)

/-! ### Explicit variance of a Gaussian under a Gaussian -/

/-- Algebra for `gauss_variance_core`. -/
theorem vc_aux1 {s : ℝ} (hs : 0 < s) (σ e : ℝ) :
    1 / (2 * Real.pi * s) * (σ / s ^ 2 * (6 * s * e)) = σ / s * (3 / (Real.pi * s)) * e := by
  have := Real.pi_pos
  field_simp; ring

/-- Algebra for `gauss_variance_core`. -/
theorem vc_aux2 {s : ℝ} (hs : 0 < s) (σ e : ℝ) :
    σ / s * (1 / (4 * Real.pi * s)) * e + σ / s * (3 / (Real.pi * s)) * e
      = σ / s * ((13 / 4) / (Real.pi * s)) * e := by
  have := Real.pi_pos
  field_simp; ring

/-- Algebra for `gauss_variance_core`. -/
theorem vc_aux3 {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hσs : σ ≤ s) :
    σ ^ 2 / (4 * Real.pi * s ^ 3) ≤ σ / s * (1 / (4 * Real.pi * s)) := by
  have hpi := Real.pi_pos
  have e : σ / s * (1 / (4 * Real.pi * s)) = σ * s / (4 * Real.pi * s ^ 3) := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- Assembly step of `gauss_variance_core`, with free variables. -/
theorem vc_assemble {s σ z A1 A2 E1 E2 E6 : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hσs : σ ≤ s)
    (hE1pos : 0 < E1) (hE6pos : 0 < E6) (hA2n : 0 ≤ A2)
    (hA : A1 - A2 ≤ σ ^ 2 / (4 * Real.pi * s ^ 3)) (h16 : E1 ≤ E6)
    (hE12 : E1 - E2 ≤ E1 * (z ^ 2 * σ / s ^ 2)) (hzE : z ^ 2 * E1 ≤ 6 * s * E6)
    (hA2 : A2 ≤ 1 / (2 * Real.pi * s)) :
    A1 * E1 - A2 * E2 ≤ σ / s * (4 / (Real.pi * s)) * E6 := by
  have hpi := Real.pi_pos
  have hsplit : A1 * E1 - A2 * E2 = (A1 - A2) * E1 + A2 * (E1 - E2) := by ring
  rw [hsplit]
  have hterm1 : (A1 - A2) * E1 ≤ σ / s * (1 / (4 * Real.pi * s)) * E6 := by
    have hpre := vc_aux3 hs hσ hσs
    have h0 : 0 ≤ σ / s * (1 / (4 * Real.pi * s)) := by positivity
    calc _ ≤ σ ^ 2 / (4 * Real.pi * s ^ 3) * E1 := mul_le_mul_of_nonneg_right hA hE1pos.le
      _ ≤ σ / s * (1 / (4 * Real.pi * s)) * E6 := mul_le_mul hpre h16 hE1pos.le h0
  have hterm2 : A2 * (E1 - E2) ≤ σ / s * (3 / (Real.pi * s)) * E6 := by
    have hq : 0 ≤ σ / s ^ 2 := by positivity
    have h1 : E1 - E2 ≤ σ / s ^ 2 * (6 * s * E6) := by
      calc E1 - E2 ≤ E1 * (z ^ 2 * σ / s ^ 2) := hE12
        _ = σ / s ^ 2 * (z ^ 2 * E1) := by ring
        _ ≤ σ / s ^ 2 * (6 * s * E6) := mul_le_mul_of_nonneg_left hzE hq
    have h0 : 0 ≤ σ / s ^ 2 * (6 * s * E6) := by positivity
    calc A2 * (E1 - E2) ≤ A2 * (σ / s ^ 2 * (6 * s * E6)) := mul_le_mul_of_nonneg_left h1 hA2n
      _ ≤ 1 / (2 * Real.pi * s) * (σ / s ^ 2 * (6 * s * E6)) := mul_le_mul_of_nonneg_right hA2 h0
      _ = σ / s * (3 / (Real.pi * s)) * E6 := vc_aux1 hs σ E6
  have hfin : σ / s * (1 / (4 * Real.pi * s)) * E6 + σ / s * (3 / (Real.pi * s)) * E6
      ≤ σ / s * (4 / (Real.pi * s)) * E6 := by
    rw [vc_aux2 hs σ E6]
    have h1 : (13 / 4 : ℝ) / (Real.pi * s) ≤ 4 / (Real.pi * s) :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    have h2 : 0 ≤ σ / s := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) hE6pos.le
  linarith

/-- **Explicit variance of a Gaussian under a Gaussian, the inequality replacing the Gaussian
    Poincaré inequality.** For `0 < σ ≤ s`,
    `(E γ_s(z + √σ Z)²) - (E γ_s(z + √σ Z))²
      = e^{-z²/(s+2σ)} / (2π √(s(s+2σ))) - e^{-z²/(s+σ)} / (2π (s+σ))`
    (the identity itself is not formalised here), and this difference is at most
    `(σ/s) · 4/(π s) · e^{-z²/(6s)}`: the factor `σ/s = 1/m` of the consistency lemma. -/
theorem gauss_variance_core {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hσs : σ ≤ s) (z : ℝ) :
    1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ))) * Real.exp (-(z ^ 2) / (s + 2 * σ))
        - 1 / (2 * Real.pi * (s + σ)) * Real.exp (-(z ^ 2) / (s + σ))
      ≤ σ / s * (4 / (Real.pi * s)) * Real.exp (-(z ^ 2) / (6 * s)) := by
  have hpi := Real.pi_pos
  set r := Real.sqrt (s * (s + 2 * σ)) with hr
  have hr2 : r ^ 2 = s * (s + 2 * σ) := Real.sq_sqrt (by positivity)
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hrs : s ≤ r := by
    by_contra h; push Not at h
    nlinarith
  have hrs2 : r ≤ s + σ := by
    by_contra h; push Not at h
    nlinarith
  set E1 := Real.exp (-(z ^ 2) / (s + 2 * σ)) with hE1
  set E2 := Real.exp (-(z ^ 2) / (s + σ)) with hE2
  set E6 := Real.exp (-(z ^ 2) / (6 * s)) with hE6
  have hE1pos : 0 < E1 := Real.exp_pos _
  have hE6pos : 0 < E6 := Real.exp_pos _
  have hz : 0 ≤ z ^ 2 := _root_.sq_nonneg z
  -- E1 ≤ E6
  have h16 : E1 ≤ E6 := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hz (by positivity) (by linarith)
  -- (i) prefactors
  have hA : 1 / (2 * Real.pi * r) - 1 / (2 * Real.pi * (s + σ)) ≤ σ ^ 2 / (4 * Real.pi * s ^ 3) := by
    have hdiff : (s + σ) - r ≤ σ ^ 2 / (2 * s) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hdiff0 : 0 ≤ (s + σ) - r := by linarith
    have e : 1 / (2 * Real.pi * r) - 1 / (2 * Real.pi * (s + σ))
        = ((s + σ) - r) / (2 * Real.pi * r * (s + σ)) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((s + σ) - r) * (4 * Real.pi * s ^ 3) ≤ σ ^ 2 / (2 * s) * (4 * Real.pi * s ^ 3) :=
      mul_le_mul_of_nonneg_right hdiff (by positivity)
    have h2 : σ ^ 2 / (2 * s) * (4 * Real.pi * s ^ 3) = 2 * Real.pi * σ ^ 2 * s ^ 2 := by
      field_simp; ring
    have h3 : s ^ 2 ≤ r * (s + σ) := by nlinarith
    have h4 : 2 * Real.pi * σ ^ 2 * s ^ 2 ≤ σ ^ 2 * (2 * Real.pi * r * (s + σ)) := by
      have : 0 ≤ 2 * Real.pi * σ ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h3 this]
    linarith
  -- (iii) difference of exponentials
  have hE12 : E1 - E2 ≤ E1 * (z ^ 2 * σ / s ^ 2) := by
    have hx : 0 ≤ z ^ 2 / (s + σ) - z ^ 2 / (s + 2 * σ) := by
      rw [sub_nonneg]; exact div_le_div_of_nonneg_left hz (by positivity) (by linarith)
    have hE2' : E2 = E1 * Real.exp (-(z ^ 2 / (s + σ) - z ^ 2 / (s + 2 * σ))) := by
      rw [hE1, hE2, ← Real.exp_add]; congr 1; ring
    have h1 : 1 - (z ^ 2 / (s + σ) - z ^ 2 / (s + 2 * σ))
        ≤ Real.exp (-(z ^ 2 / (s + σ) - z ^ 2 / (s + 2 * σ))) := by
      have := Real.add_one_le_exp (-(z ^ 2 / (s + σ) - z ^ 2 / (s + 2 * σ)))
      linarith
    have h2 : z ^ 2 / (s + σ) - z ^ 2 / (s + 2 * σ) ≤ z ^ 2 * σ / s ^ 2 := by
      have e : z ^ 2 / (s + σ) - z ^ 2 / (s + 2 * σ) = z ^ 2 * σ / ((s + σ) * (s + 2 * σ)) := by
        field_simp; ring
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    rw [hE2']
    nlinarith [mul_le_mul_of_nonneg_left h1 hE1pos.le, mul_le_mul_of_nonneg_left h2 hE1pos.le]
  -- (iv) z² E1 ≤ 6 s E6
  have hzE : z ^ 2 * E1 ≤ 6 * s * E6 := by
    set x := z ^ 2 / (s + 2 * σ) with hx
    have hx0 : 0 ≤ x := by positivity
    have hE1x : E1 = Real.exp (-x) := by rw [hE1, hx, neg_div]
    have hhalf : Real.exp (-(x / 2)) ≤ E6 := by
      apply Real.exp_le_exp.mpr
      rw [hx, neg_div, neg_le_neg_iff, div_div]
      exact div_le_div_of_nonneg_left hz (by positivity) (by linarith)
    have hxe : x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
      have h1 := Real.add_one_le_exp (x / 2)
      have h2 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
        rw [← Real.exp_add]; simp
      have hp := Real.exp_pos (-(x / 2))
      rw [h2]
      have h4 : x * Real.exp (-(x / 2)) ≤ 2 := by nlinarith
      nlinarith
    have hz2 : z ^ 2 = (s + 2 * σ) * x := by rw [hx]; field_simp
    rw [hz2, hE1x]
    have h5 : (s + 2 * σ) * x * Real.exp (-x) ≤ (s + 2 * σ) * (2 * Real.exp (-(x / 2))) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hxe (by positivity)
    have h6 : (s + 2 * σ) * (2 * Real.exp (-(x / 2))) ≤ 3 * s * (2 * E6) := by
      have hp := Real.exp_pos (-(x / 2))
      nlinarith
    linarith
  have hA2 : 1 / (2 * Real.pi * (s + σ)) ≤ 1 / (2 * Real.pi * s) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hA2n : 0 ≤ 1 / (2 * Real.pi * (s + σ)) := by positivity
  exact vc_assemble hs hσ hσs hE1pos hE6pos hA2n hA h16 hE12 hzE hA2

/-! ### Moments of a Gaussian under a Gaussian on the line -/

/-- Completing the square for a product of two Gaussians. -/
theorem gauss_square_complete {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (z y : ℝ) :
    -((z - y) ^ 2) / (2 * σ) + -(y ^ 2) / (2 * τ)
      = -(z ^ 2) / (2 * (σ + τ))
        + -((σ + τ) / (2 * σ * τ)) * (y - z * τ / (σ + τ)) ^ 2 := by
  have h : 0 < σ + τ := by positivity
  field_simp
  ring

/-- **Convolution of two Gaussians on the line (exponent form):**
    `∫ e^{-(z-y)²/(2σ)} e^{-y²/(2τ)} dy = e^{-z²/(2(σ+τ))} √(π / ((σ+τ)/(2στ)))`. -/
theorem gauss_conv_core {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (z : ℝ) :
    ∫ y : ℝ, Real.exp (-((z - y) ^ 2) / (2 * σ)) * Real.exp (-(y ^ 2) / (2 * τ))
      = Real.exp (-(z ^ 2) / (2 * (σ + τ))) * Real.sqrt (Real.pi / ((σ + τ) / (2 * σ * τ))) := by
  have e : ∀ y : ℝ, Real.exp (-((z - y) ^ 2) / (2 * σ)) * Real.exp (-(y ^ 2) / (2 * τ))
      = Real.exp (-(z ^ 2) / (2 * (σ + τ)))
        * Real.exp (-((σ + τ) / (2 * σ * τ)) * (y - z * τ / (σ + τ)) ^ 2) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add, gauss_square_complete hσ hτ]
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  have h := integral_sub_right_eq_self
    (fun y : ℝ => Real.exp (-((σ + τ) / (2 * σ * τ)) * y ^ 2)) (z * τ / (σ + τ)) (μ := volume)
  rw [h, integral_gaussian]

/-- Prefactor identity for the first moment. -/
theorem sqrt_pref_first {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) :
    1 / Real.sqrt (2 * Real.pi * σ) * (1 / Real.sqrt (2 * Real.pi * s))
        * Real.sqrt (Real.pi / ((σ + s) / (2 * σ * s)))
      = 1 / Real.sqrt (2 * Real.pi * (σ + s)) := by
  have hpi := Real.pi_pos
  have h1 : 0 < Real.sqrt (2 * Real.pi * σ) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < Real.sqrt (2 * Real.pi * (σ + s)) := Real.sqrt_pos.mpr (by positivity)
  have a1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * Real.pi * σ by positivity)
  have a2 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * Real.pi * s by positivity)
  have a3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * Real.pi * (σ + s) by positivity)
  have hR : Real.sqrt (Real.pi / ((σ + s) / (2 * σ * s)))
      = Real.sqrt (2 * Real.pi * σ) * Real.sqrt (2 * Real.pi * s)
        / Real.sqrt (2 * Real.pi * (σ + s)) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    rw [div_mul_div_comm, mul_mul_mul_comm, a1, a2, a3]
    field_simp
  rw [hR]
  field_simp

/-- First moment: `∫ γ_σ(z - y) γ_s(y) dy = γ_{σ+s}(z)`. -/
theorem gauss_first_moment {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (z : ℝ) :
    ∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((z - y) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(y ^ 2) / (2 * s)))
      = 1 / Real.sqrt (2 * Real.pi * (σ + s)) * Real.exp (-(z ^ 2) / (2 * (σ + s))) := by
  have e : ∀ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((z - y) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(y ^ 2) / (2 * s)))
      = (1 / Real.sqrt (2 * Real.pi * σ) * (1 / Real.sqrt (2 * Real.pi * s)))
        * (Real.exp (-((z - y) ^ 2) / (2 * σ)) * Real.exp (-(y ^ 2) / (2 * s))) := fun y => by ring
  simp_rw [e]
  rw [integral_const_mul, gauss_conv_core hσ hs, ← sqrt_pref_first hσ hs]
  ring

/-- Prefactor identity for the second moment. -/
theorem sqrt_pref_second {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) :
    1 / Real.sqrt (2 * Real.pi * σ) * (1 / (2 * Real.pi * s))
        * Real.sqrt (Real.pi / ((σ + s / 2) / (2 * σ * (s / 2))))
      = 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ))) := by
  have hpi := Real.pi_pos
  have h1 : 0 < Real.sqrt (2 * Real.pi * σ) := Real.sqrt_pos.mpr (by positivity)
  have h3 : 0 < Real.sqrt (s * (s + 2 * σ)) := Real.sqrt_pos.mpr (by positivity)
  have a1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * Real.pi * σ by positivity)
  have a3 := Real.mul_self_sqrt (show (0 : ℝ) ≤ s * (s + 2 * σ) by positivity)
  have hR : Real.sqrt (Real.pi / ((σ + s / 2) / (2 * σ * (s / 2))))
      = Real.sqrt (2 * Real.pi * σ) * s / Real.sqrt (s * (s + 2 * σ)) := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)]
    rw [div_mul_div_comm, mul_mul_mul_comm, a1, a3]
    field_simp
    ring
  rw [hR]
  field_simp

/-- Second moment: `∫ γ_σ(z - y) γ_s(y)² dy = e^{-z²/(s+2σ)} / (2π √(s(s+2σ)))`. -/
theorem gauss_second_moment {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (z : ℝ) :
    ∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((z - y) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(y ^ 2) / (2 * s))) ^ 2
      = 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ))) * Real.exp (-(z ^ 2) / (s + 2 * σ)) := by
  have hpi := Real.pi_pos
  have hsq : (1 / Real.sqrt (2 * Real.pi * s)) ^ 2 = 1 / (2 * Real.pi * s) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have e : ∀ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((z - y) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(y ^ 2) / (2 * s))) ^ 2
      = (1 / Real.sqrt (2 * Real.pi * σ) * (1 / (2 * Real.pi * s)))
        * (Real.exp (-((z - y) ^ 2) / (2 * σ)) * Real.exp (-(y ^ 2) / (2 * (s / 2)))) := fun y => by
    rw [mul_pow, hsq, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(y ^ 2) / (2 * s)) = -(y ^ 2) / (2 * (s / 2)) := by
      push_cast; field_simp
    rw [this]; ring
  simp_rw [e]
  rw [integral_const_mul, gauss_conv_core hσ (by positivity : (0 : ℝ) < s / 2),
    ← sqrt_pref_second hσ hs]
  have : (2 : ℝ) * (σ + s / 2) = s + 2 * σ := by ring
  rw [this]
  ring

/-- **Variance of a Gaussian under a Gaussian on the line, as integrals, with the factor `σ/s`:**
    for `0 < σ ≤ s`,
    `∫ γ_σ(z - y) γ_s(y)² dy - (∫ γ_σ(z - y) γ_s(y) dy)² ≤ (σ/s) · 4/(π s) · e^{-z²/(6s)}`. -/
theorem gauss_variance_line {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (z : ℝ) :
    (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((z - y) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(y ^ 2) / (2 * s))) ^ 2)
      - (∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((z - y) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(y ^ 2) / (2 * s)))) ^ 2
      ≤ σ / s * (4 / (Real.pi * s)) * Real.exp (-(z ^ 2) / (6 * s)) := by
  have hpi := Real.pi_pos
  rw [gauss_second_moment hσ hs, gauss_first_moment hσ hs]
  have h := gauss_variance_core hs hσ hσs z
  have e : (1 / Real.sqrt (2 * Real.pi * (σ + s)) * Real.exp (-(z ^ 2) / (2 * (σ + s)))) ^ 2
      = 1 / (2 * Real.pi * (s + σ)) * Real.exp (-(z ^ 2) / (s + σ)) := by
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity), ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(z ^ 2) / (2 * (σ + s))) = -(z ^ 2) / (s + σ) := by
      push_cast; field_simp; ring
    rw [this, add_comm σ s]
  rw [e]
  exact h

/-! ### Lattice-pair terms of the periodised variance -/

/-- Shifting the centre of a Gaussian by `k/2` at the cost of a factor in `k`:
    `e^{-(v - k/2)²/(6s)} ≤ e^{-v²/(12s)} e^{k²/(24s)}`. -/
theorem gauss_shift_cost {s : ℝ} (hs : 0 < s) (v k : ℝ) :
    Real.exp (-((v - k / 2) ^ 2) / (6 * s))
      ≤ Real.exp (-(v ^ 2) / (12 * s)) * Real.exp (k ^ 2 / (24 * s)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h : v ^ 2 ≤ 2 * (v - k / 2) ^ 2 + 2 * (k / 2) ^ 2 := by nlinarith [_root_.sq_nonneg (v - k)]
  have e : -((v - k / 2) ^ 2) / (6 * s) = -(2 * (v - k / 2) ^ 2) / (12 * s) := by
    field_simp; ring
  have e2 : -(v ^ 2) / (12 * s) + k ^ 2 / (24 * s) = -(v ^ 2 - k ^ 2 / 2) / (12 * s) := by
    field_simp; ring
  rw [e, e2]
  exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- **One lattice-pair term of the periodised variance.** For `0 < σ ≤ s`, with `w = v - k/2`
    (`v = x + n`, `k = n - n'`), the term
    `e^{-k²/(4s)} M₂(w) - e^{-k²/(4(s+σ))} M₁²(w)` of
    `∫ γ_σ(x - y) g(y)² dy - (∫ γ_σ(x - y) g(y) dy)²`, `g = ∑_n γ_s(· + n)`, is at most
    `(σ/s) · 4/(π s) · e^{-k²/(12s)} e^{-v²/(12s)}`. -/
theorem pair_variance_term {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hσs : σ ≤ s) (v k : ℝ) :
    Real.exp (-(k ^ 2) / (4 * s))
        * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
            * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ)))
      - Real.exp (-(k ^ 2) / (4 * (s + σ)))
        * (1 / (2 * Real.pi * (s + σ)) * Real.exp (-((v - k / 2) ^ 2) / (s + σ)))
      ≤ σ / s * (4 / (Real.pi * s))
        * (Real.exp (-(k ^ 2) / (12 * s)) * Real.exp (-(v ^ 2) / (12 * s))) := by
  have hpi := Real.pi_pos
  have hcore := gauss_variance_core hs hσ hσs (v - k / 2)
  have hM2 : 0 ≤ 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
      * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ)) := by positivity
  have hk : Real.exp (-(k ^ 2) / (4 * s)) ≤ Real.exp (-(k ^ 2) / (4 * (s + σ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (_root_.sq_nonneg k) (by positivity) (by linarith)
  have hk2 : Real.exp (-(k ^ 2) / (4 * (s + σ))) ≤ Real.exp (-(k ^ 2) / (8 * s)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (_root_.sq_nonneg k) (by positivity) (by linarith)
  have hshift := gauss_shift_cost hs v k
  have hcomb : Real.exp (-(k ^ 2) / (8 * s)) * Real.exp (k ^ 2 / (24 * s))
      = Real.exp (-(k ^ 2) / (12 * s)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hE := Real.exp_pos (-(k ^ 2) / (4 * (s + σ)))
  have hc0 : 0 ≤ σ / s * (4 / (Real.pi * s)) := by positivity
  calc _ ≤ Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
              * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ)))
        - Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * (s + σ)) * Real.exp (-((v - k / 2) ^ 2) / (s + σ))) := by
        have := mul_le_mul_of_nonneg_right hk hM2
        linarith
    _ = Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
              * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ))
            - 1 / (2 * Real.pi * (s + σ)) * Real.exp (-((v - k / 2) ^ 2) / (s + σ))) := by ring
    _ ≤ Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (σ / s * (4 / (Real.pi * s)) * Real.exp (-((v - k / 2) ^ 2) / (6 * s))) :=
        mul_le_mul_of_nonneg_left hcore hE.le
    _ ≤ Real.exp (-(k ^ 2) / (8 * s))
          * (σ / s * (4 / (Real.pi * s))
            * (Real.exp (-(v ^ 2) / (12 * s)) * Real.exp (k ^ 2 / (24 * s)))) := by
        refine mul_le_mul hk2 (mul_le_mul_of_nonneg_left hshift hc0) (by positivity) (by positivity)
    _ = σ / s * (4 / (Real.pi * s))
          * (Real.exp (-(k ^ 2) / (12 * s)) * Real.exp (-(v ^ 2) / (12 * s))) := by
        rw [← hcomb]; ring

/-- **Sum over the lattice pairs of the bounds of `pair_variance_term`.** The double series
    factorises, and
    `∑_{n,k} e^{-k²/(12s)} e^{-(n+x)²/(12s)} ≤ (1 + √(12πs)) ∑_n e^{-(n+x)²/(12s)}`:
    up to the factor `(σ/s) · 4/(πs) · (1 + √(12πs)) · √(12πs)` the periodised variance is at most
    the periodised Gaussian at time `6s`. -/
theorem pair_variance_sum {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Summable (fun p : ℤ × ℤ => Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-(1 / (12 * s)) * (p.2 : ℝ) ^ 2)) ∧
    ∑' p : ℤ × ℤ, Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-(1 / (12 * s)) * (p.2 : ℝ) ^ 2)
      ≤ (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ∑' n : ℤ, Real.exp (-(1 / (12 * s)) * ((n : ℝ) - (-x)) ^ 2) := by
  have hb : 0 < 1 / (12 * s) := by positivity
  have hf := gauss_shift_summable hb (-x)
  have hg := gauss_summable_int hb
  have hfg := Summable.mul_of_nonneg hf hg (fun n => (Real.exp_pos _).le) (fun n => (Real.exp_pos _).le)
  refine ⟨hfg, ?_⟩
  rw [← hf.tsum_mul_tsum hg hfg, mul_comm]
  exact mul_le_mul_of_nonneg_right (gauss_tsum_int_le hb) (tsum_nonneg fun n => (Real.exp_pos _).le)

/-! ### Integrals of the lattice pairs -/

/-- Product of two shifted Gaussians of the same variance: centre at the midpoint. -/
theorem gauss_prod_shift {s : ℝ} (hs : 0 < s) (y a b : ℝ) :
    Real.exp (-((y + a) ^ 2) / (2 * s)) * Real.exp (-((y + b) ^ 2) / (2 * s))
      = Real.exp (-((a - b) ^ 2) / (4 * s)) * Real.exp (-((y + (a + b) / 2) ^ 2) / (2 * s)) ^ 2 := by
  rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- **Integral of one lattice pair:** for `σ, s > 0` and real shifts `a, b`,
    `∫ γ_σ(x - y) γ_s(y + a) γ_s(y + b) dy
      = e^{-(a-b)²/(4s)} · e^{-(x + (a+b)/2)²/(s+2σ)} / (2π √(s(s+2σ)))`. -/
theorem gauss_pair_integral {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x a b : ℝ) :
    ∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((x - y) ^ 2) / (2 * σ)))
        * ((1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-((y + a) ^ 2) / (2 * s)))
          * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-((y + b) ^ 2) / (2 * s))))
      = Real.exp (-((a - b) ^ 2) / (4 * s))
        * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
          * Real.exp (-((x + (a + b) / 2) ^ 2) / (s + 2 * σ))) := by
  have e : ∀ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((x - y) ^ 2) / (2 * σ)))
        * ((1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-((y + a) ^ 2) / (2 * s)))
          * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-((y + b) ^ 2) / (2 * s))))
      = Real.exp (-((a - b) ^ 2) / (4 * s))
        * ((1 / Real.sqrt (2 * Real.pi * σ)
              * Real.exp (-(((x + (a + b) / 2) - (y + (a + b) / 2)) ^ 2) / (2 * σ)))
          * (1 / Real.sqrt (2 * Real.pi * s)
              * Real.exp (-((y + (a + b) / 2) ^ 2) / (2 * s))) ^ 2) := by
    intro y
    have h := gauss_prod_shift hs y a b
    have hx : (x + (a + b) / 2) - (y + (a + b) / 2) = x - y := by ring
    rw [hx, mul_pow]
    calc _ = 1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((x - y) ^ 2) / (2 * σ))
          * ((1 / Real.sqrt (2 * Real.pi * s)) ^ 2
            * (Real.exp (-((y + a) ^ 2) / (2 * s)) * Real.exp (-((y + b) ^ 2) / (2 * s)))) := by
          ring
      _ = _ := by rw [h]; ring
  simp_rw [e]
  rw [integral_const_mul]
  congr 1
  have h := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi * σ)
          * Real.exp (-(((x + (a + b) / 2) - u) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(u ^ 2) / (2 * s))) ^ 2) ((a + b) / 2)
  rw [h]
  exact gauss_second_moment hσ hs (x + (a + b) / 2)

/-- First moment with a shift: `∫ γ_σ(x - y) γ_s(y + a) dy = γ_{σ+s}(x + a)`. -/
theorem gauss_first_moment_shift {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x a : ℝ) :
    ∫ y : ℝ, (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-((x - y) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-((y + a) ^ 2) / (2 * s)))
      = 1 / Real.sqrt (2 * Real.pi * (σ + s)) * Real.exp (-((x + a) ^ 2) / (2 * (σ + s))) := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ => (1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-(((x + a) - u) ^ 2) / (2 * σ)))
        * (1 / Real.sqrt (2 * Real.pi * s) * Real.exp (-(u ^ 2) / (2 * s)))) a
  have e : ∀ y : ℝ, (x + a) - (y + a) = x - y := fun y => by ring
  simp only [e] at h
  rw [h]
  exact gauss_first_moment hσ hs (x + a)

/-- Product of two values of a Gaussian of variance `τ` at shifted points. -/
theorem gauss_first_pair {τ : ℝ} (hτ : 0 < τ) (x a b : ℝ) :
    (1 / Real.sqrt (2 * Real.pi * τ) * Real.exp (-((x + a) ^ 2) / (2 * τ)))
        * (1 / Real.sqrt (2 * Real.pi * τ) * Real.exp (-((x + b) ^ 2) / (2 * τ)))
      = Real.exp (-((a - b) ^ 2) / (4 * τ))
        * (1 / (2 * Real.pi * τ) * Real.exp (-((x + (a + b) / 2) ^ 2) / τ)) := by
  have hpi := Real.pi_pos
  have h := gauss_prod_shift hτ x a b
  have hsq : 1 / Real.sqrt (2 * Real.pi * τ) * (1 / Real.sqrt (2 * Real.pi * τ))
      = 1 / (2 * Real.pi * τ) := by
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by positivity)]
  have he : Real.exp (-((x + (a + b) / 2) ^ 2) / (2 * τ)) ^ 2
      = Real.exp (-((x + (a + b) / 2) ^ 2) / τ) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; field_simp
  calc _ = (1 / Real.sqrt (2 * Real.pi * τ) * (1 / Real.sqrt (2 * Real.pi * τ)))
        * (Real.exp (-((x + a) ^ 2) / (2 * τ)) * Real.exp (-((x + b) ^ 2) / (2 * τ))) := by ring
    _ = _ := by rw [hsq, h, he]; ring

/-! ### Variance of the periodised Gaussian under a Gaussian, one variable -/

/-- The Gaussian density of variance `τ` on the line. -/
noncomputable def gaussR (τ u : ℝ) : ℝ :=
  1 / Real.sqrt (2 * Real.pi * τ) * Real.exp (-(u ^ 2) / (2 * τ))

/-- Nonnegativity. -/
theorem gaussR_nonneg (τ u : ℝ) : 0 ≤ gaussR τ u := by
  unfold gaussR; positivity

/-- Upper bound by the value at the origin. -/
theorem gaussR_le {τ : ℝ} (u : ℝ) (hτ : 0 < τ) : gaussR τ u ≤ 1 / Real.sqrt (2 * Real.pi * τ) := by
  unfold gaussR
  have h : Real.exp (-(u ^ 2) / (2 * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div]
    exact neg_nonpos.mpr (div_nonneg (_root_.sq_nonneg u) (by positivity))
  have h0 : 0 ≤ 1 / Real.sqrt (2 * Real.pi * τ) := by positivity
  nlinarith

/-- Continuity. -/
theorem gaussR_continuous (τ : ℝ) : Continuous (gaussR τ) := by
  unfold gaussR; fun_prop

/-- Integrability of the reflected and translated density. -/
theorem gaussR_integrable_sub {σ : ℝ} (hσ : 0 < σ) (x : ℝ) :
    Integrable fun y : ℝ => gaussR σ (x - y) := by
  have h := (integrable_exp_neg_mul_sq (b := 1 / (2 * σ)) (by positivity)).comp_sub_left x
  have e : (fun y : ℝ => gaussR σ (x - y))
      = fun y : ℝ => 1 / Real.sqrt (2 * Real.pi * σ) * Real.exp (-(1 / (2 * σ)) * (x - y) ^ 2) := by
    funext y; unfold gaussR; congr 2; ring
  rw [e]
  exact h.const_mul _

/-- Summability over integer shifts. -/
theorem gaussR_shift_summable {s : ℝ} (hs : 0 < s) (y : ℝ) :
    Summable fun n : ℤ => gaussR s (y + n) := by
  have h := gauss_shift_summable (b := 1 / (2 * s)) (by positivity) (-y)
  have e : (fun n : ℤ => gaussR s (y + n))
      = fun n : ℤ => 1 / Real.sqrt (2 * Real.pi * s)
          * Real.exp (-(1 / (2 * s)) * ((n : ℝ) - (-y)) ^ 2) := by
    funext n; unfold gaussR; congr 2; ring
  rw [e]
  exact h.mul_left _

/-- The pair integral in the short notation. -/
theorem gaussR_pair_integral {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x a b : ℝ) :
    ∫ y : ℝ, gaussR σ (x - y) * (gaussR s (y + a) * gaussR s (y + b))
      = Real.exp (-((a - b) ^ 2) / (4 * s))
        * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
          * Real.exp (-((x + (a + b) / 2) ^ 2) / (s + 2 * σ))) :=
  gauss_pair_integral hσ hs x a b

/-- The shifted first moment in the short notation. -/
theorem gaussR_first_integral {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x a : ℝ) :
    ∫ y : ℝ, gaussR σ (x - y) * gaussR s (y + a) = gaussR (σ + s) (x + a) :=
  gauss_first_moment_shift hσ hs x a

/-- Integrability of a product of the Gaussian weight with bounded continuous factors. -/
theorem gaussR_weight_integrable {σ : ℝ} (hσ : 0 < σ) (x : ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    {B : ℝ} (hB : ∀ y, |f y| ≤ B) : Integrable fun y : ℝ => gaussR σ (x - y) * f y := by
  have h := (gaussR_integrable_sub hσ x).bdd_mul (c := B) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa using hB y)
  simpa [mul_comm] using h

/-- Integrability of weight times a shifted density. -/
theorem gaussR_shift_integrable {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x a : ℝ) :
    Integrable fun y : ℝ => gaussR σ (x - y) * gaussR s (y + a) :=
  gaussR_weight_integrable hσ x (fun y => gaussR s (y + a))
    ((gaussR_continuous s).comp (continuous_id.add continuous_const))
    (fun y => by rw [abs_of_nonneg (gaussR_nonneg _ _)]; exact gaussR_le _ hs)

/-- **First moment of the periodised Gaussian under a Gaussian:**
    `∫ γ_σ(x - y) ∑_n γ_s(y + n) dy = ∑_n γ_{σ+s}(x + n)`. -/
theorem per_first_moment {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x : ℝ) :
    ∫ y : ℝ, gaussR σ (x - y) * ∑' n : ℤ, gaussR s (y + n) = ∑' n : ℤ, gaussR (σ + s) (x + n) := by
  have hint : ∀ n : ℤ, Integrable fun y : ℝ => gaussR σ (x - y) * gaussR s (y + n) :=
    fun n => gaussR_shift_integrable hσ hs x n
  have hval : ∀ n : ℤ, ∫ y : ℝ, ‖gaussR σ (x - y) * gaussR s (y + n)‖ = gaussR (σ + s) (x + n) := by
    intro n
    have : ∀ y : ℝ, ‖gaussR σ (x - y) * gaussR s (y + n)‖ = gaussR σ (x - y) * gaussR s (y + n) :=
      fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussR_nonneg _ _) (gaussR_nonneg _ _))]
    simp_rw [this]
    exact gaussR_first_integral hσ hs x n
  have hsum : Summable fun n : ℤ => ∫ y : ℝ, ‖gaussR σ (x - y) * gaussR s (y + n)‖ := by
    simp_rw [hval]; exact gaussR_shift_summable (by positivity) x
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have e : ∀ y : ℝ, ∑' n : ℤ, gaussR σ (x - y) * gaussR s (y + n)
      = gaussR σ (x - y) * ∑' n : ℤ, gaussR s (y + n) := fun y => tsum_mul_left
  simp_rw [e] at h
  rw [← h]
  exact tsum_congr fun n => gaussR_first_integral hσ hs x n

/-- The bounding double series in the coordinates `(n, n')`. -/
theorem pair_bound_summable {s : ℝ} (hs : 0 < s) (x : ℝ) :
    Summable (fun p : ℤ × ℤ => Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) ∧
    ∑' p : ℤ × ℤ, Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)
      ≤ (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ∑' n : ℤ, Real.exp (-(1 / (12 * s)) * ((n : ℝ) - (-x)) ^ 2) := by
  obtain ⟨hsum, hle⟩ := pair_variance_sum hs x
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1, p.1 - p.2), invFun := fun p => (p.1, p.1 - p.2),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  refine ⟨(Equiv.summable_iff e).mpr hsum, ?_⟩
  have h := Equiv.tsum_eq e (fun p : ℤ × ℤ => Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-(1 / (12 * s)) * (p.2 : ℝ) ^ 2))
  exact (le_of_eq h).trans hle

/-- The value of the pair integral for the lattice pair `p = (n, n')`. -/
noncomputable def pairVal (σ s x : ℝ) (p : ℤ × ℤ) : ℝ :=
  Real.exp (-(((p.1 : ℝ) - p.2) ^ 2) / (4 * s))
    * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
      * Real.exp (-((x + ((p.1 : ℝ) + p.2) / 2) ^ 2) / (s + 2 * σ)))

/-- Nonnegativity of the pair values. -/
theorem pairVal_nonneg (σ s x : ℝ) (p : ℤ × ℤ) : 0 ≤ pairVal σ s x p := by
  unfold pairVal; positivity

/-- Each pair value is bounded by a term of the factorising double series. -/
theorem pairVal_le {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x : ℝ) (p : ℤ × ℤ) :
    pairVal σ s x p ≤ 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
      * (Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) := by
  unfold pairVal
  set v : ℝ := x + p.1 with hv
  set k : ℝ := (p.1 : ℝ) - p.2 with hk
  have hpi := Real.pi_pos
  have hc : 0 ≤ 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ))) := by positivity
  have e1 : x + ((p.1 : ℝ) + p.2) / 2 = v - k / 2 := by rw [hv, hk]; ring
  have e2 : (p.1 : ℝ) - (-x) = v := by rw [hv]; ring
  have e3 : (((p.1 - p.2 : ℤ) : ℝ)) = k := by rw [hk]; push_cast; ring
  rw [e1, e2, e3]
  have h1 : Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ)) ≤ Real.exp (-((v - k / 2) ^ 2) / (6 * s)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (_root_.sq_nonneg _) (by positivity) (by linarith)
  have h2 := gauss_shift_cost hs v k
  have h3 : Real.exp (-(k ^ 2) / (4 * s)) ≤ Real.exp (-(k ^ 2) / (8 * s)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (_root_.sq_nonneg _) (by positivity) (by linarith)
  have hcomb : Real.exp (-(k ^ 2) / (8 * s)) * Real.exp (k ^ 2 / (24 * s))
      = Real.exp (-(1 / (12 * s)) * k ^ 2) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have e4 : Real.exp (-(1 / (12 * s)) * v ^ 2) = Real.exp (-(v ^ 2) / (12 * s)) := by
    congr 1; ring
  rw [e4, ← hcomb]
  have hA := Real.exp_pos (-(k ^ 2) / (4 * s))
  have hB := Real.exp_pos (-(k ^ 2) / (8 * s))
  have hC := Real.exp_pos (-((v - k / 2) ^ 2) / (s + 2 * σ))
  have hD := Real.exp_pos (-(v ^ 2) / (12 * s))
  have hE := Real.exp_pos (k ^ 2 / (24 * s))
  have h4 : Real.exp (-(k ^ 2) / (4 * s)) * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ))
      ≤ Real.exp (-(k ^ 2) / (8 * s))
        * (Real.exp (-(v ^ 2) / (12 * s)) * Real.exp (k ^ 2 / (24 * s))) :=
    mul_le_mul h3 (h1.trans h2) hC.le hB.le
  calc _ = 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
        * (Real.exp (-(k ^ 2) / (4 * s)) * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ))) := by ring
    _ ≤ 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
        * (Real.exp (-(k ^ 2) / (8 * s))
          * (Real.exp (-(v ^ 2) / (12 * s)) * Real.exp (k ^ 2 / (24 * s)))) :=
        mul_le_mul_of_nonneg_left h4 hc
    _ = _ := by ring

/-- Summability of the pair values. -/
theorem pairVal_summable {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x : ℝ) :
    Summable (pairVal σ s x) :=
  Summable.of_nonneg_of_le (pairVal_nonneg σ s x) (pairVal_le hσ hs hσs x)
    ((pair_bound_summable hs x).1.mul_left _)

/-- **Second moment of the periodised Gaussian under a Gaussian, as a sum over lattice pairs.** -/
theorem per_second_moment {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x : ℝ) :
    ∫ y : ℝ, gaussR σ (x - y) * (∑' n : ℤ, gaussR s (y + n)) ^ 2 = ∑' p : ℤ × ℤ, pairVal σ s x p := by
  have hpi := Real.pi_pos
  have hint : ∀ p : ℤ × ℤ,
      Integrable fun y : ℝ => gaussR σ (x - y) * (gaussR s (y + p.1) * gaussR s (y + p.2)) := by
    intro p
    refine gaussR_weight_integrable hσ x (fun y => gaussR s (y + p.1) * gaussR s (y + p.2))
      (((gaussR_continuous s).comp (continuous_id.add continuous_const)).mul
        ((gaussR_continuous s).comp (continuous_id.add continuous_const)))
      (B := 1 / Real.sqrt (2 * Real.pi * s) * (1 / Real.sqrt (2 * Real.pi * s))) (fun y => ?_)
    rw [abs_of_nonneg (mul_nonneg (gaussR_nonneg _ _) (gaussR_nonneg _ _))]
    exact mul_le_mul (gaussR_le _ hs) (gaussR_le _ hs) (gaussR_nonneg _ _) (by positivity)
  have hpv : ∀ p : ℤ × ℤ,
      ∫ y : ℝ, gaussR σ (x - y) * (gaussR s (y + p.1) * gaussR s (y + p.2)) = pairVal σ s x p :=
    fun p => gaussR_pair_integral hσ hs x p.1 p.2
  have hval : ∀ p : ℤ × ℤ,
      ∫ y : ℝ, ‖gaussR σ (x - y) * (gaussR s (y + p.1) * gaussR s (y + p.2))‖
        = pairVal σ s x p := by
    intro p
    have : ∀ y : ℝ, ‖gaussR σ (x - y) * (gaussR s (y + p.1) * gaussR s (y + p.2))‖
        = gaussR σ (x - y) * (gaussR s (y + p.1) * gaussR s (y + p.2)) := fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (gaussR_nonneg _ _)
        (mul_nonneg (gaussR_nonneg _ _) (gaussR_nonneg _ _)))]
    simp_rw [this]
    exact hpv p
  have hsum : Summable fun p : ℤ × ℤ =>
      ∫ y : ℝ, ‖gaussR σ (x - y) * (gaussR s (y + p.1) * gaussR s (y + p.2))‖ := by
    simp_rw [hval]; exact pairVal_summable hσ hs hσs x
  have h := integral_tsum_of_summable_integral_norm hint hsum
  have hsq : ∀ y : ℝ, (∑' n : ℤ, gaussR s (y + n)) ^ 2
      = ∑' p : ℤ × ℤ, gaussR s (y + p.1) * gaussR s (y + p.2) := by
    intro y
    have hf := gaussR_shift_summable hs y
    rw [_root_.sq, hf.tsum_mul_tsum hf (Summable.mul_of_nonneg hf hf (fun n => gaussR_nonneg _ _)
      (fun n => gaussR_nonneg _ _))]
  have e : ∀ y : ℝ, ∑' p : ℤ × ℤ, gaussR σ (x - y) * (gaussR s (y + p.1) * gaussR s (y + p.2))
      = gaussR σ (x - y) * (∑' n : ℤ, gaussR s (y + n)) ^ 2 := fun y => by
    rw [hsq y, tsum_mul_left]
  simp_rw [e] at h
  rw [← h]
  exact tsum_congr hpv

/-- **Variance of the periodised Gaussian under a Gaussian, one variable, with the factor
    `σ/s`:** for `0 < σ ≤ s` and `g = ∑_n γ_s(· + n)`,
    `∫ γ_σ(x - y) g(y)² dy - (∫ γ_σ(x - y) g(y) dy)²
      ≤ (σ/s) · 4/(πs) · (1 + √(12πs)) · ∑_n e^{-(x+n)²/(12s)}`.
    This is the variance bound of the consistency lemma in one variable, without the Gaussian
    Poincaré inequality; the right-hand side is a multiple of the periodised Gaussian at time `6s`. -/
theorem per_variance_line {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x : ℝ) :
    (∫ y : ℝ, gaussR σ (x - y) * (∑' n : ℤ, gaussR s (y + n)) ^ 2)
      - (∫ y : ℝ, gaussR σ (x - y) * ∑' n : ℤ, gaussR s (y + n)) ^ 2
      ≤ σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ∑' n : ℤ, Real.exp (-(1 / (12 * s)) * ((n : ℝ) - (-x)) ^ 2)) := by
  have hpi := Real.pi_pos
  have hτ : 0 < σ + s := by positivity
  rw [per_second_moment hσ hs hσs, per_first_moment hσ hs]
  have hf := gaussR_shift_summable hτ x
  have hprod := Summable.mul_of_nonneg hf hf (fun n => gaussR_nonneg _ _) (fun n => gaussR_nonneg _ _)
  rw [_root_.sq, hf.tsum_mul_tsum hf hprod, ← (pairVal_summable hσ hs hσs x).tsum_sub hprod]
  obtain ⟨hbs, hble⟩ := pair_bound_summable hs x
  have hc0 : 0 ≤ σ / s * (4 / (Real.pi * s)) := by positivity
  have hterm : ∀ p : ℤ × ℤ, pairVal σ s x p - gaussR (σ + s) (x + p.1) * gaussR (σ + s) (x + p.2)
      ≤ σ / s * (4 / (Real.pi * s))
        * (Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
          * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) := by
    intro p
    have h := pair_variance_term hs hσ hσs (x + p.1) ((p.1 : ℝ) - p.2)
    have e1 : x + (p.1 : ℝ) - ((p.1 : ℝ) - p.2) / 2 = x + ((p.1 : ℝ) + p.2) / 2 := by ring
    have hQ : gaussR (σ + s) (x + p.1) * gaussR (σ + s) (x + p.2)
        = Real.exp (-(((p.1 : ℝ) - p.2) ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * (s + σ))
            * Real.exp (-((x + ((p.1 : ℝ) + p.2) / 2) ^ 2) / (s + σ))) := by
      have := gauss_first_pair hτ x (p.1 : ℝ) (p.2 : ℝ)
      unfold gaussR
      rw [this, add_comm σ s]
    rw [e1] at h
    rw [hQ]
    unfold pairVal
    have e2 : Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        = Real.exp (-((x + (p.1 : ℝ)) ^ 2) / (12 * s)) := by congr 1; ring
    have e3 : Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)
        = Real.exp (-(((p.1 : ℝ) - p.2) ^ 2) / (12 * s)) := by
      congr 1; push_cast; ring
    rw [e2, e3]
    calc _ ≤ σ / s * (4 / (Real.pi * s))
          * (Real.exp (-(((p.1 : ℝ) - p.2) ^ 2) / (12 * s))
            * Real.exp (-((x + (p.1 : ℝ)) ^ 2) / (12 * s))) := h
      _ = _ := by ring
  have hdiffsum : Summable fun p : ℤ × ℤ =>
      pairVal σ s x p - gaussR (σ + s) (x + p.1) * gaussR (σ + s) (x + p.2) :=
    (pairVal_summable hσ hs hσs x).sub hprod
  calc _ ≤ ∑' p : ℤ × ℤ, σ / s * (4 / (Real.pi * s))
          * (Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
            * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) :=
        hdiffsum.tsum_le_tsum hterm (hbs.mul_left _)
    _ = σ / s * (4 / (Real.pi * s))
          * ∑' p : ℤ × ℤ, Real.exp (-(1 / (12 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
            * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hble hc0

/-! ### Unfolding integrals over the circle -/

/-- Integer translations act trivially on the unit circle. -/
theorem coe_add_int_unit (x : ℝ) (n : ℤ) :
    (((x + n : ℝ)) : UnitAddCircle) = ((x : ℝ) : UnitAddCircle) := by
  have h : (((n : ℝ)) : UnitAddCircle) = 0 := by
    have := AddCircle.coe_period (1 : ℝ)
    rw [show (n : ℝ) = n • (1 : ℝ) by simp, AddCircle.coe_zsmul, this, smul_zero]
  rw [AddCircle.coe_add, h, add_zero]

/-- **Unfolding.** For an integrable `γ` on the line and a bounded measurable function `F` on the
    circle, `∫_ℝ γ(y) F(y mod 1) dy = ∫_0^1 (∑_n γ(x + n)) F(x mod 1) dx`. -/
theorem line_unfold (γ : ℝ → ℝ) (hγ : Integrable γ) (F : UnitAddCircle → ℝ) (hF : Measurable F)
    {B : ℝ} (hFb : ∀ u, |F u| ≤ B) :
    ∫ y : ℝ, γ y * F (y : UnitAddCircle)
      = ∫ x in (0 : ℝ)..1, (∑' n : ℤ, γ (x + n)) * F (x : UnitAddCircle) := by
  have hFm : Measurable fun y : ℝ => F (y : UnitAddCircle) :=
    hF.comp (AddCircle.measurable_mk')
  have hint : Integrable fun y : ℝ => γ y * F (y : UnitAddCircle) := by
    have h := hγ.bdd_mul (c := B) hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hFb (y : UnitAddCircle))
    simpa [mul_comm] using h
  have h1 := hint.hasSum_intervalIntegral_comp_add_int
  simp_rw [coe_add_int_unit] at h1
  -- exchange on (0, 1]
  have hterm : ∀ n : ℤ, Integrable (fun x : ℝ => γ (x + n) * F (x : UnitAddCircle))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro n
    have hg : Integrable fun x : ℝ => γ (x + n) := hγ.comp_add_right (n : ℝ)
    have h := hg.bdd_mul (c := B) hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hFb (y : UnitAddCircle))
    have h' : Integrable fun x : ℝ => γ (x + n) * F (x : UnitAddCircle) := by
      simpa [mul_comm] using h
    exact h'.restrict
  have habs := hγ.norm.hasSum_intervalIntegral_comp_add_int
  have hsum : Summable fun n : ℤ =>
      ∫ x, ‖γ (x + n) * F (x : UnitAddCircle)‖ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFb 0)
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) (fun n => ?_)
      (habs.summable.mul_left B)
    have hg : Integrable (fun x : ℝ => ‖γ (x + n)‖) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      ((hγ.comp_add_right (n : ℝ)).norm).restrict
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    refine integral_mono (hterm n).norm (hg.const_mul B) fun x => ?_
    show ‖γ (x + n) * F (x : UnitAddCircle)‖ ≤ B * ‖γ (x + n)‖
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa using hFb (x : UnitAddCircle)) (norm_nonneg _)
  have h2 := integral_tsum_of_summable_integral_norm hterm hsum
  have e : ∀ x : ℝ, ∑' n : ℤ, γ (x + n) * F (x : UnitAddCircle)
      = (∑' n : ℤ, γ (x + n)) * F (x : UnitAddCircle) := fun x => tsum_mul_right
  simp_rw [e] at h2
  rw [intervalIntegral.integral_of_le zero_le_one, ← h2, ← h1.tsum_eq]
  exact tsum_congr fun n => intervalIntegral.integral_of_le zero_le_one

/-- **Unfolding on the circle.** If `Γ` is the function on the circle with
    `Γ(x mod 1) = ∑_n γ(x + n)`, then `∫_circle Γ F = ∫_ℝ γ(y) F(y mod 1) dy` (Haar probability
    measure on the circle). -/
theorem circle_unfold (γ : ℝ → ℝ) (hγ : Integrable γ) (Γ : UnitAddCircle → ℝ)
    (hΓ : ∀ x : ℝ, Γ (x : UnitAddCircle) = ∑' n : ℤ, γ (x + n))
    (F : UnitAddCircle → ℝ) (hF : Measurable F) {B : ℝ} (hFb : ∀ u, |F u| ≤ B) :
    ∫ u, Γ u * F u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
      = ∫ y : ℝ, γ y * F (y : UnitAddCircle) := by
  rw [AddCircle.integral_haarAddCircle, inv_one, one_smul,
    ← UnitAddCircle.intervalIntegral_preimage 0 (fun u => Γ u * F u), line_unfold γ hγ F hF hFb]
  simp only [zero_add, hΓ]

/-! ### The variance bound on the circle -/

/-- The periodised Gaussian in time variables as a sum of Gaussian densities. -/
theorem perGauss_eq_tsum_gaussR {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    perGauss (2 * Real.pi ^ 2 * τ) t = ∑' n : ℤ, gaussR τ (t + n) := by
  rw [perGauss_time hτ, ← tsum_mul_left, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  unfold gaussR
  rw [Real.sqrt_eq_rpow]
  congr 2
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

/-- The heat kernel of the circle as a function on the circle. -/
noncomputable def pC (c : ℝ) (u : UnitAddCircle) : ℝ := heatTorus 1 c (fun _ => u)

/-- Its value at a real point is the periodised Gaussian. -/
theorem pC_coe {c : ℝ} (hc : 0 < c) (t : ℝ) : pC c (t : UnitAddCircle) = perGauss c t := by
  unfold pC
  rw [heatTorus_eq_prod hc 1 (fun _ => t)]
  simp

/-- Continuity. -/
theorem pC_continuous {c : ℝ} (hc : 0 < c) : Continuous (pC c) := by
  have habs : Summable fun n : Fin 1 → ℤ => |Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc 1
  unfold pC
  exact (cosSeries_continuous 1 _ habs).comp (continuous_pi fun _ => continuous_id)

/-- Nonnegativity. -/
theorem pC_nonneg {c : ℝ} (hc : 0 < c) (u : UnitAddCircle) : 0 ≤ pC c u :=
  heatTorus_nonneg hc 1 _

/-- Upper bound. -/
theorem pC_le {c : ℝ} (hc : 0 < c) (u : UnitAddCircle) :
    pC c u ≤ (1 + Real.sqrt (Real.pi / c)) ^ 1 := heatTorus_le hc 1 _

/-- Integration against the heat kernel of the circle is integration against the Gaussian on
    the line. -/
theorem circle_gauss_integral {σ : ℝ} (hσ : 0 < σ) (x : ℝ) (F : UnitAddCircle → ℝ)
    (hF : Measurable F) {B : ℝ} (hFb : ∀ u, |F u| ≤ B) :
    ∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u) * F u
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
      = ∫ y : ℝ, gaussR σ (x - y) * F (y : UnitAddCircle) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  refine circle_unfold (fun y => gaussR σ (x - y)) (gaussR_integrable_sub hσ x)
    (fun u => pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)) (fun y => ?_) F hF hFb
  show pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - (y : UnitAddCircle))
    = ∑' n : ℤ, gaussR σ (x - (y + n))
  rw [← AddCircle.coe_sub, pC_coe hc, perGauss_eq_tsum_gaussR hσ, ← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  congr 1; ring

/-- **Variance bound on the circle, with the factor `σ/s`.** For `0 < σ ≤ s`, with `P_σ`, `P_s`
    the heat kernels of the circle at times `σ`, `s` (`c = 2π²τ`) and real `x, w`,
    `∫ P_σ(x - u) P_s(u - w)² du - (∫ P_σ(x - u) P_s(u - w) du)²
      ≤ (σ/s) · 4/(πs) · (1 + √(12πs)) · ∑_n e^{-(x - w + n)²/(12s)}`. -/
theorem circle_variance {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x w : ℝ) :
    (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
      - (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) ^ 2
      ≤ σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ∑' n : ℤ, Real.exp (-(1 / (12 * s)) * ((n : ℝ) - (-(x - w))) ^ 2)) := by
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hG : Continuous fun u : UnitAddCircle => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) :=
    (pC_continuous hcs).comp (continuous_id.sub continuous_const)
  have hGb : ∀ u : UnitAddCircle, |pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))|
      ≤ (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1 := fun u => by
    rw [abs_of_nonneg (pC_nonneg hcs _)]; exact pC_le hcs _
  have hval : ∀ y : ℝ, pC (2 * Real.pi ^ 2 * s) ((y : UnitAddCircle) - (w : UnitAddCircle))
      = ∑' n : ℤ, gaussR s (y - w + n) := fun y => by
    rw [← AddCircle.coe_sub, pC_coe hcs, perGauss_eq_tsum_gaussR hs]
  have h2 := circle_gauss_integral hσ x
    (fun u => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2) (hG.pow 2).measurable
    (B := ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1) ^ 2) (fun u => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hGb u) 2)
  have h1 := circle_gauss_integral hσ x
    (fun u => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))) hG.measurable hGb
  simp only [hval] at h1 h2
  rw [h1, h2]
  have t2 := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => gaussR σ (x - y) * (∑' n : ℤ, gaussR s (y - w + n)) ^ 2) w
  have t1 := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => gaussR σ (x - y) * ∑' n : ℤ, gaussR s (y - w + n)) w
  have e : ∀ y : ℝ, x - (y + w) = (x - w) - y := fun y => by ring
  have e' : ∀ y : ℝ, y + w - w = y := fun y => by ring
  simp only [e, e'] at t1 t2
  rw [← t1, ← t2]
  exact per_variance_line hσ hs hσs (x - w)

/-! ### The variance bound on the circle with the kernel weight -/

/-- The Gaussian lattice sum is a multiple of the heat kernel of the circle:
    `∑_n e^{-(n - t)²/(2τ)} = (2πτ)^{1/2} P_τ(t)`. -/
theorem gauss_sum_eq_pC {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    ∑' n : ℤ, Real.exp (-(1 / (2 * τ)) * ((n : ℝ) - t) ^ 2)
      = (2 * Real.pi * τ) ^ (1 / 2 : ℝ) * pC (2 * Real.pi ^ 2 * τ) (t : UnitAddCircle) := by
  have hc : 0 < 2 * Real.pi ^ 2 * τ := by positivity
  have hpos : 0 < (2 * Real.pi * τ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  rw [pC_coe hc, perGauss_time hτ, ← mul_assoc, mul_one_div_cancel hpos.ne', one_mul]

/-- The heat kernel of the circle is even. -/
theorem pC_even (c : ℝ) (u : UnitAddCircle) : pC c (-u) = pC c u := by
  unfold pC
  have := heatTorus_even 1 c (fun _ => u)
  simpa using this

/-- **Variance bound on the circle in the form of the consistency lemma:** for `0 < σ ≤ s`,
    `∫ P_σ(x - u) P_s(u - w)² du - (∫ P_σ(x - u) P_s(u - w) du)²
      ≤ (σ/s) · 4/(πs) · (1 + √(12πs)) · (12πs)^{1/2} · P_{6s}(x - w)`. -/
theorem circle_variance_weight {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x w : ℝ) :
    (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
      - (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) ^ 2
      ≤ σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ((2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ)
          * pC (2 * Real.pi ^ 2 * (6 * s)) ((x : UnitAddCircle) - (w : UnitAddCircle)))) := by
  have h := circle_variance hσ hs hσs x w
  have h6 : (0 : ℝ) < 6 * s := by positivity
  have e := gauss_sum_eq_pC h6 (-(x - w))
  have e1 : (1 : ℝ) / (2 * (6 * s)) = 1 / (12 * s) := by ring_nf
  rw [e1] at e
  rw [e] at h
  have e2 : (((-(x - w) : ℝ)) : UnitAddCircle) = -((x : UnitAddCircle) - (w : UnitAddCircle)) := by
    rw [AddCircle.coe_neg, AddCircle.coe_sub]
  rw [e2, pC_even] at h
  exact h

/-! ### Difference of two products -/

/-- **Difference of two products.** If `0 ≤ a i ≤ α w i`, `0 ≤ b i ≤ α w i` and `a i - b i ≤ ε w i` with
    `w i ≥ 0`, then `∏ a - ∏ b ≤ |s| · ε · α^{|s|-1} · ∏ w`. -/
theorem prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b w : ι → ℝ) {α ε : ℝ}
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hbw : ∀ i, b i ≤ α * w i) (haw : ∀ i, a i ≤ α * w i) (hd : ∀ i, a i - b i ≤ ε * w i) (hw : ∀ i, 0 ≤ w i) :
    ∏ i ∈ s, a i - ∏ i ∈ s, b i ≤ s.card * ε * α ^ (s.card - 1) * ∏ i ∈ s, w i := by
  classical
  have hprodb : ∀ t : Finset ι, ∏ i ∈ t, b i ≤ α ^ t.card * ∏ i ∈ t, w i := by
    intro t
    calc ∏ i ∈ t, b i ≤ ∏ i ∈ t, α * w i :=
          Finset.prod_le_prod (fun i _ => hb i) (fun i _ => hbw i)
      _ = α ^ t.card * ∏ i ∈ t, w i := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.prod_insert hk,
      Finset.card_insert_of_notMem hk]
    have hW : 0 ≤ ∏ i ∈ s, w i := Finset.prod_nonneg fun i _ => hw i
    have hB : 0 ≤ ∏ i ∈ s, b i := Finset.prod_nonneg fun i _ => hb i
    have e : a k * ∏ i ∈ s, a i - b k * ∏ i ∈ s, b i
        = a k * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a k - b k) * ∏ i ∈ s, b i := by ring
    rw [e]
    have hnn : 0 ≤ (s.card : ℝ) * ε * α ^ (s.card - 1) * ∏ i ∈ s, w i := by positivity
    have h1 : a k * (∏ i ∈ s, a i - ∏ i ∈ s, b i)
        ≤ (α * w k) * (s.card * ε * α ^ (s.card - 1) * ∏ i ∈ s, w i) :=
      (mul_le_mul_of_nonneg_left ih (ha k)).trans (mul_le_mul_of_nonneg_right (haw k) hnn)
    have h2 : (a k - b k) * ∏ i ∈ s, b i ≤ (ε * w k) * (α ^ s.card * ∏ i ∈ s, w i) :=
      mul_le_mul (hd k) (hprodb s) hB (mul_nonneg hε (hw k))
    have hpow : (s.card : ℝ) * α ^ (s.card - 1) * α = s.card * α ^ s.card := by
      rcases Nat.eq_zero_or_pos s.card with h0 | hpos
      · simp [h0]
      · rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hpos]
    have hfin : (α * w k) * (s.card * ε * α ^ (s.card - 1) * ∏ i ∈ s, w i)
        + (ε * w k) * (α ^ s.card * ∏ i ∈ s, w i)
        = ((s.card + 1 : ℕ) : ℝ) * ε * α ^ (s.card + 1 - 1) * (w k * ∏ i ∈ s, w i) := by
      rw [Nat.add_sub_cancel]
      push_cast
      have h3 : (α * w k) * (s.card * ε * α ^ (s.card - 1) * ∏ i ∈ s, w i)
          = ((s.card : ℝ) * α ^ (s.card - 1) * α) * ε * (w k * ∏ i ∈ s, w i) := by ring
      rw [h3, hpow]; ring
    linarith

/-! ### The variance bound on the torus of dimension `d` -/

/-- The heat kernel of the torus is the product of the heat kernels of the circle. -/
theorem heatTorus_eq_prod_pC {c : ℝ} (hc : 0 < c) (d : ℕ) (x : FlatTorus d) :
    heatTorus d c x = ∏ i, pC c (x i) := by
  obtain ⟨t, rfl⟩ := flatTorus_lift d x
  rw [heatTorus_eq_prod hc]
  exact Finset.prod_congr rfl fun i _ => (pC_coe hc (t i)).symm

/-- Integral of a product over the coordinates of the flat torus. -/
theorem flatTorus_integral_prod (d : ℕ) (f : Fin d → UnitAddCircle → ℝ) :
    ∫ x, ∏ i, f i (x i) ∂flatTorusMeasure d
      = ∏ i, ∫ u, f i u ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  integral_fintype_prod_eq_prod (𝕜 := ℝ) f

/-- Semigroup on the circle: `∫ P_σ(x - u) P_s(u - w) du = P_{σ+s}(x - w)`. -/
theorem circle_first_moment {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x w : ℝ) :
    ∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
      = pC (2 * Real.pi ^ 2 * (σ + s)) ((x : UnitAddCircle) - (w : UnitAddCircle)) := by
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hcτ : 0 < 2 * Real.pi ^ 2 * (σ + s) := by positivity
  have hG : Continuous fun u : UnitAddCircle => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) :=
    (pC_continuous hcs).comp (continuous_id.sub continuous_const)
  have hGb : ∀ u : UnitAddCircle, |pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))|
      ≤ (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1 := fun u => by
    rw [abs_of_nonneg (pC_nonneg hcs _)]; exact pC_le hcs _
  have hval : ∀ y : ℝ, pC (2 * Real.pi ^ 2 * s) ((y : UnitAddCircle) - (w : UnitAddCircle))
      = ∑' n : ℤ, gaussR s (y - w + n) := fun y => by
    rw [← AddCircle.coe_sub, pC_coe hcs, perGauss_eq_tsum_gaussR hs]
  have h1 := circle_gauss_integral hσ x
    (fun u => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))) hG.measurable hGb
  simp only [hval] at h1
  rw [h1]
  have t1 := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => gaussR σ (x - y) * ∑' n : ℤ, gaussR s (y - w + n)) w
  have e : ∀ y : ℝ, x - (y + w) = (x - w) - y := fun y => by ring
  have e' : ∀ y : ℝ, y + w - w = y := fun y => by ring
  simp only [e, e'] at t1
  rw [← t1, per_first_moment hσ hs, ← AddCircle.coe_sub, pC_coe hcτ,
    perGauss_eq_tsum_gaussR (by positivity : (0 : ℝ) < σ + s)]

/-- Second moment on the circle against the first: `∫ P_σ(x-u) P_s(u-w)² du ≤ S · P_{σ+s}(x-w)` with
    `S = 1 + √(π/c_s)` the bound of `P_s`. -/
theorem circle_second_le {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (x w : ℝ) :
    ∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
      ≤ (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
        * pC (2 * Real.pi ^ 2 * (σ + s)) ((x : UnitAddCircle) - (w : UnitAddCircle)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hK : Continuous fun u : UnitAddCircle => pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u) :=
    (pC_continuous hcσ).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun u : UnitAddCircle => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) :=
    (pC_continuous hcs).comp (continuous_id.sub continuous_const)
  rw [← circle_first_moment hσ hs x w, ← integral_const_mul]
  refine integral_mono
    ((hK.mul (hG.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (((hK.mul hG).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun u => ?_)
  have h0 := pC_nonneg hcσ ((x : UnitAddCircle) - u)
  have h1 := pC_nonneg hcs (u - (w : UnitAddCircle))
  have h2 := pC_le hcs (u - (w : UnitAddCircle))
  show pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2
      ≤ (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
        * (pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)))
  nlinarith [mul_nonneg h0 h1, mul_le_mul_of_nonneg_left h2 (mul_nonneg h0 h1)]

/-- (P1) for the heat kernel of the circle. -/
theorem pC_P1 {ca ct : ℝ} (ha : 0 < ca) (hat : ca ≤ ct) (u : UnitAddCircle) :
    pC ca u ≤ (ct / ca) ^ (1 / 2 : ℝ) * pC ct u := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective u
  have ht : 0 < ct := lt_of_lt_of_le ha hat
  rw [pC_coe ha, pC_coe ht]
  exact perGauss_P1 ha hat t

/-- **Variance bound on the flat torus of dimension `d`, with the factor `σ/s` and the weight of
    the consistency lemma.** For `0 < σ ≤ s`, with `p_τ` the heat kernel of the torus at time `τ`
    (`c = 2π²τ`) and points `X, W` of the torus,
    `∫ p_σ(X - y) p_s(y - W)² dy - (∫ p_σ(X - y) p_s(y - W) dy)² ≤ d · ε · α^{d-1} · p_{6s}(X - W)`,
    where `ε = (σ/s) · 4/(πs) · (1 + √(12πs)) · (12πs)^{1/2}` carries the factor `σ/s = 1/m` and
    `α = (1 + √(π/c_s)) · (6s/(σ+s))^{1/2}`. This is the variance bound of the consistency lemma in
    every dimension, without the Gaussian Poincaré inequality; the constants depend on `s`. -/
theorem torus_variance {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : Fin d → ℝ) :
    (∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle)) ^ 2
        ∂flatTorusMeasure d)
      - (∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
        ∂flatTorusMeasure d) ^ 2
      ≤ (d : ℝ) * (σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
            * (2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ)))
          * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
            * ((2 * Real.pi ^ 2 * (6 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)) ^ (d - 1)
          * heatTorus d (2 * Real.pi ^ 2 * (6 * s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)) := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hcτ : 0 < 2 * Real.pi ^ 2 * (σ + s) := by positivity
  have hc6 : 0 < 2 * Real.pi ^ 2 * (6 * s) := by positivity
  have hτ6 : 2 * Real.pi ^ 2 * (σ + s) ≤ 2 * Real.pi ^ 2 * (6 * s) := by
    have : 0 ≤ 2 * Real.pi ^ 2 := by positivity
    nlinarith
  set S : ℝ := (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1 with hS
  set ρ : ℝ := ((2 * Real.pi ^ 2 * (6 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ) with hρ
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have e2 : ∀ y : FlatTorus d,
      heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle)) ^ 2
        = ∏ i, (pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - y i)
            * pC (2 * Real.pi ^ 2 * s) (y i - ((w i : ℝ) : UnitAddCircle)) ^ 2) := by
    intro y
    rw [heatTorus_eq_prod_pC hcσ, heatTorus_eq_prod_pC hcs, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    rfl
  have e1 : ∀ y : FlatTorus d,
      heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
        = ∏ i, (pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - y i)
            * pC (2 * Real.pi ^ 2 * s) (y i - ((w i : ℝ) : UnitAddCircle))) := by
    intro y
    rw [heatTorus_eq_prod_pC hcσ, heatTorus_eq_prod_pC hcs, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [e2, e1]
  rw [flatTorus_integral_prod d (fun i u => pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle)) ^ 2),
    flatTorus_integral_prod d (fun i u => pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle))),
    ← Finset.prod_pow, heatTorus_eq_prod_pC hc6]
  have hfirst : ∀ i : Fin d, ∫ u, pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
      = pC (2 * Real.pi ^ 2 * (σ + s)) (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)) :=
    fun i => circle_first_moment hσ hs (x i) (w i)
  have hτle : ∀ z : UnitAddCircle, pC (2 * Real.pi ^ 2 * (σ + s)) z
      ≤ ρ * pC (2 * Real.pi ^ 2 * (6 * s)) z := fun z => pC_P1 hcτ hτ6 z
  have hτS : ∀ z : UnitAddCircle, pC (2 * Real.pi ^ 2 * (σ + s)) z ≤ S := by
    intro z
    refine (pC_le hcτ z).trans ?_
    rw [hS, pow_one, pow_one]
    have : Real.pi / (2 * Real.pi ^ 2 * (σ + s)) ≤ Real.pi / (2 * Real.pi ^ 2 * s) :=
      div_le_div_of_nonneg_left hpi.le hcs (by nlinarith [_root_.sq_nonneg Real.pi])
    linarith [Real.sqrt_le_sqrt this]
  have h := prod_sub_prod_le (Finset.univ : Finset (Fin d))
    (fun i => ∫ u, pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle)) ^ 2
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
    (fun i => (∫ u, pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) ^ 2)
    (fun i => pC (2 * Real.pi ^ 2 * (6 * s))
        (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)))
    (α := S * ρ)
    (ε := σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
            * (2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ)))
    (mul_nonneg hS0 hρ0) (by positivity)
    (fun i => integral_nonneg fun u => mul_nonneg (pC_nonneg hcσ _) (_root_.sq_nonneg _))
    (fun i => _root_.sq_nonneg _)
    (fun i => by
      beta_reduce
      rw [hfirst i]
      have a1 := hτS (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      have a2 := hτle (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      have a0 := pC_nonneg hcτ (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      calc _ = pC (2 * Real.pi ^ 2 * (σ + s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
            * pC (2 * Real.pi ^ 2 * (σ + s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)) := _root_.sq _
        _ ≤ S * (ρ * pC (2 * Real.pi ^ 2 * (6 * s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))) :=
            mul_le_mul a1 a2 a0 hS0
        _ = _ := by ring)
    (fun i => by
      have a2 := hτle (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      calc _ ≤ S * pC (2 * Real.pi ^ 2 * (σ + s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)) :=
            circle_second_le hσ hs (x i) (w i)
        _ ≤ S * (ρ * pC (2 * Real.pi ^ 2 * (6 * s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))) :=
            mul_le_mul_of_nonneg_left a2 hS0
        _ = _ := by ring)
    (fun i => by
      have := circle_variance_weight hσ hs hσs (x i) (w i)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (fun i => pC_nonneg hc6 _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

/-! ### Conditioning by independence -/

section Conditioning
open scoped ENNReal

/-- **Conditioning by independence.** `U`, `V` independent and measurable, `S` a measurable set of
    pairs. If for every fixed value `u` the probability that `(u, V) ∈ S` is at most `q`, then the
    probability that `(U, V) ∈ S` is at most `q`. This replaces "given `x_b` and `x_i`" in the proof
    of the consistency lemma. -/
theorem indep_cond_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (U : Ω → α) (V : Ω → β) (hU : Measurable U) (hV : Measurable V) (hind : IndepFun U V μ)
    (S : Set (α × β)) (hS : MeasurableSet S) {q : ℝ≥0∞}
    (hq : ∀ u : α, μ {ω | (u, V ω) ∈ S} ≤ q) :
    μ {ω | (U ω, V ω) ∈ S} ≤ q := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).mp hind
  have hUV : Measurable fun ω => (U ω, V ω) := hU.prodMk hV
  have h1 : μ {ω | (U ω, V ω) ∈ S} = (μ.map fun ω => (U ω, V ω)) S := by
    rw [Measure.map_apply hUV hS]; rfl
  haveI : IsProbabilityMeasure (μ.map U) := Measure.isProbabilityMeasure_map hU.aemeasurable
  haveI : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  rw [h1, hmap, Measure.prod_apply hS]
  calc ∫⁻ u, (μ.map V) (Prod.mk u ⁻¹' S) ∂(μ.map U)
      ≤ ∫⁻ _u, q ∂(μ.map U) := by
        refine lintegral_mono fun u => ?_
        rw [Measure.map_apply hV (measurable_prodMk_left hS)]
        exact hq u
    _ = q := by simp

/-- The same with real-valued probabilities. -/
theorem indep_cond_bound_real {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (U : Ω → α) (V : Ω → β) (hU : Measurable U) (hV : Measurable V) (hind : IndepFun U V μ)
    (S : Set (α × β)) (hS : MeasurableSet S) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ u : α, μ.real {ω | (u, V ω) ∈ S} ≤ q) :
    μ.real {ω | (U ω, V ω) ∈ S} ≤ q := by
  have h := indep_cond_bound U V hU hV hind S hS (q := ENNReal.ofReal q) (fun u => by
    have := hq u
    rw [Measure.real] at this
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hq0).mpr this)
  rw [Measure.real]
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hq0).mp h

/-- **Conditioning on part of an independent sample.** For independent `X_j`, disjoint finite index
    sets `S`, `T` and a measurable set `A` of pairs of tuples: if for every fixed tuple `u` over `S`
    the probability that `(u, (X_j)_{j ∈ T}) ∈ A` is at most `q`, then the probability that
    `((X_i)_{i ∈ S}, (X_j)_{j ∈ T}) ∈ A` is at most `q`. -/
theorem sample_cond_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j)) (S T : Finset ℕ) (hST : Disjoint S T)
    (A : Set ((S → E) × (T → E))) (hA : MeasurableSet A) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ∀ u : S → E, μ.real {ω | (u, fun j : T => X j ω) ∈ A} ≤ q) :
    μ.real {ω | ((fun i : S => X i ω), (fun j : T => X j ω)) ∈ A} ≤ q :=
  indep_cond_bound_real (fun ω (i : S) => X i ω) (fun ω (j : T) => X j ω)
    (measurable_pi_lambda _ fun i => hX i) (measurable_pi_lambda _ fun j => hX j)
    (h_indep.indepFun_finset S T hST hX) A hA hq0 hq

end Conditioning

/-! ### Bernstein two-sided, the semigroup on the torus and the centred second moment -/

/-- **Bernstein's inequality, two-sided, for a function of independent points over a finite index
    set.** `f` measurable with `|f| ≤ b`, `E f(X_j) = 0` and `E f(X_j)² ≤ v` for `j ∈ T`:
    `P(|∑_{j ∈ T} f(X_j)| ≥ eps) ≤ 2 exp(-eps² / (4 |T| v + 2 b eps))`. -/
theorem bernstein_two_sided_fn {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j)) (f : E → ℝ) (hf : Measurable f)
    (T : Finset ℕ) {b v ε : ℝ} (hb : 0 < b) (hfb : ∀ z, |f z| ≤ b)
    (hmean : ∀ j ∈ T, μ[fun ω => f (X j ω)] = 0)
    (hvar : ∀ j ∈ T, ∫ ω, f (X j ω) ^ 2 ∂μ ≤ v) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T, f (X j ω)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * v) + 2 * b * ε)) := by
  have hV : ∑ j ∈ T, ∫ ω, f (X j ω) ^ 2 ∂μ ≤ T.card * v := by
    calc ∑ j ∈ T, ∫ ω, f (X j ω) ^ 2 ∂μ ≤ ∑ _j ∈ T, v := Finset.sum_le_sum hvar
      _ = T.card * v := by rw [Finset.sum_const, nsmul_eq_mul]
  have hint : ∀ j, Integrable (fun ω => f (X j ω)) μ := fun j =>
    Integrable.of_bound (hf.comp (hX j)).aestronglyMeasurable b
      (Filter.Eventually.of_forall fun ω => by simpa using hfb (X j ω))
  have h1 := bernstein_inequality (μ := μ) (fun j ω => f (X j ω))
    (h_indep.comp (fun _ z => f z) (fun _ => hf)) (fun j => hf.comp (hX j)) T hb
    (fun j _ ω => hfb (X j ω)) hmean hV hε
  have h2 := bernstein_inequality (μ := μ) (fun j ω => -f (X j ω))
    (h_indep.comp (fun _ z => -f z) (fun _ => hf.neg)) (fun j => (hf.comp (hX j)).neg) T hb
    (fun j _ ω => by rw [abs_neg]; exact hfb (X j ω))
    (fun j hj => by
      have : (fun ω => -f (X j ω)) = fun ω => -(f (X j ω)) := rfl
      rw [integral_neg, hmean j hj, neg_zero])
    (by simpa using hV) hε
  have hsub : {ω | ε ≤ |∑ j ∈ T, f (X j ω)|}
      ⊆ {ω | ε ≤ ∑ j ∈ T, f (X j ω)} ∪ {ω | ε ≤ ∑ j ∈ T, -f (X j ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Finset.sum_neg_distrib] at hω ⊢
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc μ.real {ω | ε ≤ |∑ j ∈ T, f (X j ω)|}
      ≤ μ.real ({ω | ε ≤ ∑ j ∈ T, f (X j ω)} ∪ {ω | ε ≤ ∑ j ∈ T, -f (X j ω)}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ ∑ j ∈ T, f (X j ω)} + μ.real {ω | ε ≤ ∑ j ∈ T, -f (X j ω)} :=
        measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * v) + 2 * b * ε)) := by linarith

/-- Continuity of the heat kernel of the torus. -/
theorem heatTorus_continuous {c : ℝ} (hc : 0 < c) (d : ℕ) : Continuous (heatTorus d c) := by
  have habs : Summable fun n : Fin d → ℤ => |Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)| := by
    simpa [abs_of_pos (Real.exp_pos _)] using gauss_summable hc d
  exact cosSeries_continuous d _ habs

/-- **Semigroup on the flat torus:** `∫ p_σ(X - y) p_s(y - W) dy = p_{σ+s}(X - W)`. -/
theorem torus_first_moment {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (x w : Fin d → ℝ) :
    ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
        * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
        ∂flatTorusMeasure d
      = heatTorus d (2 * Real.pi ^ 2 * (σ + s))
          ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hcτ : 0 < 2 * Real.pi ^ 2 * (σ + s) := by positivity
  have e1 : ∀ y : FlatTorus d,
      heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
        = ∏ i, (pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - y i)
            * pC (2 * Real.pi ^ 2 * s) (y i - ((w i : ℝ) : UnitAddCircle))) := by
    intro y
    rw [heatTorus_eq_prod_pC hcσ, heatTorus_eq_prod_pC hcs, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [e1]
  rw [flatTorus_integral_prod d (fun i u => pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle))),
    heatTorus_eq_prod_pC hcτ]
  exact Finset.prod_congr rfl fun i _ => circle_first_moment hσ hs (x i) (w i)

/-- **Centred second moment on the torus:**
    `∫ p_σ(X - y) (p_s(y - W) - c)² dy = ∫ p_σ(X - y) p_s(y - W)² dy - c²` for `c = p_{σ+s}(X - W)`. -/
theorem torus_centered_second {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (x w : Fin d → ℝ) :
    ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
          - heatTorus d (2 * Real.pi ^ 2 * (σ + s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle))) ^ 2
        ∂flatTorusMeasure d
      = (∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle)) ^ 2
          ∂flatTorusMeasure d)
        - heatTorus d (2 * Real.pi ^ 2 * (σ + s))
            ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)) ^ 2 := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  set X : FlatTorus d := fun i => ((x i : ℝ) : UnitAddCircle) with hX
  set W : FlatTorus d := fun i => ((w i : ℝ) : UnitAddCircle) with hW
  set c : ℝ := heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X - W) with hc
  have hK : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X - y) :=
    (heatTorus_continuous hcσ d).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * s) (y - W) :=
    (heatTorus_continuous hcs d).comp (continuous_id.sub continuous_const)
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass : ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) (X - y) ∂flatTorusMeasure d = 1 := by
    rw [integral_sub_left_eq_self (heatTorus d (2 * Real.pi ^ 2 * σ)) (flatTorusMeasure d) X]
    exact heatTorus_mass hcσ d
  have hfirst : ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) (X - y)
      * heatTorus d (2 * Real.pi ^ 2 * s) (y - W) ∂flatTorusMeasure d = c :=
    torus_first_moment hσ hs d x w
  have e : ∀ y : FlatTorus d, heatTorus d (2 * Real.pi ^ 2 * σ) (X - y)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (y - W) - c) ^ 2
      = heatTorus d (2 * Real.pi ^ 2 * σ) (X - y) * heatTorus d (2 * Real.pi ^ 2 * s) (y - W) ^ 2
        - 2 * c * (heatTorus d (2 * Real.pi ^ 2 * σ) (X - y)
            * heatTorus d (2 * Real.pi ^ 2 * s) (y - W))
        + c ^ 2 * heatTorus d (2 * Real.pi ^ 2 * σ) (X - y) := fun y => by ring
  simp_rw [e]
  have I1 : Integrable (fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X - y)
      * heatTorus d (2 * Real.pi ^ 2 * s) (y - W) ^ 2) (flatTorusMeasure d) :=
    hint _ (hK.mul (hG.pow 2))
  have I2 : Integrable (fun y : FlatTorus d => 2 * c * (heatTorus d (2 * Real.pi ^ 2 * σ) (X - y)
      * heatTorus d (2 * Real.pi ^ 2 * s) (y - W))) (flatTorusMeasure d) :=
    (hint _ (hK.mul hG)).const_mul _
  have I3 : Integrable (fun y : FlatTorus d => c ^ 2 * heatTorus d (2 * Real.pi ^ 2 * σ) (X - y))
      (flatTorusMeasure d) := (hint _ hK).const_mul _
  have I12 : Integrable (fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X - y)
      * heatTorus d (2 * Real.pi ^ 2 * s) (y - W) ^ 2
      - 2 * c * (heatTorus d (2 * Real.pi ^ 2 * σ) (X - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - W))) (flatTorusMeasure d) := I1.sub I2
  rw [integral_add I12 I3, integral_sub I1 I2, integral_const_mul, integral_const_mul, hfirst,
    hmass]
  ring

/-! ### Consistency at fixed points with the sharp variance -/

/-- **Consistency at fixed points with the sharp variance (Bernstein step of the consistency
    lemma).** Independent uniform points `X_j` on the flat torus; fixed points `x, w` (real
    coordinates), times `0 < σ ≤ s`; `Y(z) = p_σ(x - z) (p_s(z - w) - p_{σ+s}(x - w))`. If
    `|Y| ≤ Bb` (HYPOTHESIS, to be supplied by (P4)) and `p_σ ≤ Mσ`, then for every finite index set
    `T`,
    `P(|∑_{j ∈ T} Y(X_j)| ≥ eps) ≤ 2 exp(-eps² / (4 |T| Mσ V + 2 Bb eps))`,
    where `V = d ε α^{d-1} p_{6s}(x - w)` is the bound of `torus_variance`, which carries the
    factor `σ/s = 1/m` and the weight `p_{6s}`. -/
theorem heat_consistency_fixed {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : Fin d → ℝ) (T : Finset ℕ)
    {Bb Mσ ε : ℝ} (hBb : 0 < Bb)
    (hY : ∀ z : FlatTorus d,
      |heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - z)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (z - fun i => ((w i : ℝ) : UnitAddCircle))
          - heatTorus d (2 * Real.pi ^ 2 * (σ + s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)))| ≤ Bb)
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T,
        heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - X j ω)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (X j ω - fun i => ((w i : ℝ) : UnitAddCircle))
          - heatTorus d (2 * Real.pi ^ 2 * (σ + s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)))|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * (Mσ
          * ((d : ℝ) * (σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
                * (2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ)))
              * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
                * ((2 * Real.pi ^ 2 * (6 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)) ^ (d - 1)
              * heatTorus d (2 * Real.pi ^ 2 * (6 * s))
                  ((fun i => ((x i : ℝ) : UnitAddCircle))
                    - fun i => ((w i : ℝ) : UnitAddCircle))))) + 2 * Bb * ε)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  set X0 : FlatTorus d := fun i => ((x i : ℝ) : UnitAddCircle) with hX0
  set W0 : FlatTorus d := fun i => ((w i : ℝ) : UnitAddCircle) with hW0
  set c : ℝ := heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) with hc
  have hK : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) :=
    (heatTorus_continuous hcσ d).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) :=
    (heatTorus_continuous hcs d).comp (continuous_id.sub continuous_const)
  have hYc : Continuous fun z : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) := hK.mul (hG.sub continuous_const)
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass : ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) ∂flatTorusMeasure d = 1 := by
    rw [integral_sub_left_eq_self (heatTorus d (2 * Real.pi ^ 2 * σ)) (flatTorusMeasure d) X0]
    exact heatTorus_mass hcσ d
  have hfirst : ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y)
      * heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) ∂flatTorusMeasure d = c :=
    torus_first_moment hσ hs d x w
  -- transfer of integrals to the law
  have htr : ∀ (j : ℕ) (f : FlatTorus d → ℝ), Continuous f →
      ∫ ω, f (X j ω) ∂μ = ∫ z, f z ∂flatTorusMeasure d := fun j f hf => by
    rw [← hlaw j, integral_map (hX j).aemeasurable hf.measurable.aestronglyMeasurable]
  refine bernstein_two_sided_fn (μ := μ) X h_indep hX
    (fun z => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) hYc.measurable T hBb hY
    (fun j _ => ?_) (fun j _ => ?_) hε
  · -- mean zero
    rw [htr j _ hYc]
    have e : ∀ z : FlatTorus d, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)
        = heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) * heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
          - c * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) := fun z => by ring
    simp_rw [e]
    have I1 : Integrable (fun z : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)) (flatTorusMeasure d) := hint _ (hK.mul hG)
    have I2 : Integrable (fun z : FlatTorus d => c * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))
        (flatTorusMeasure d) := (hint _ hK).const_mul _
    rw [integral_sub I1 I2, integral_const_mul, hfirst, hmass]
    ring
  · -- variance
    rw [htr j (fun z => (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) ^ 2) (hYc.pow 2)]
    have hle : ∫ z, (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) ^ 2 ∂flatTorusMeasure d
        ≤ ∫ z, Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2) ∂flatTorusMeasure d := by
      refine integral_mono (hint _ (hYc.pow 2))
        ((hint _ (hK.mul ((hG.sub continuous_const).pow 2))).const_mul _) (fun z => ?_)
      have h0 := heatTorus_nonneg hcσ d (X0 - z)
      have h1 := hMσ (X0 - z)
      have h2 : 0 ≤ (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2 := _root_.sq_nonneg _
      show (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
            * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) ^ 2
          ≤ Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
            * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2)
      rw [mul_pow, _root_.sq (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))]
      nlinarith [mul_nonneg h0 h2, mul_le_mul_of_nonneg_right h1 (mul_nonneg h0 h2)]
    have hM0 : 0 ≤ Mσ := (heatTorus_nonneg hcσ d 0).trans (hMσ 0)
    have hvar := torus_variance hσ hs hσs d x w
    rw [torus_first_moment hσ hs d x w] at hvar
    refine hle.trans ?_
    rw [integral_const_mul, torus_centered_second hσ hs d x w]
    exact mul_le_mul_of_nonneg_left hvar hM0

/-! ### Positivity of the kernel and the bound `B` from (P4) -/

/-- The periodised Gaussian is strictly positive. -/
theorem perGauss_pos {c : ℝ} (hc : 0 < c) (t : ℝ) : 0 < perGauss c t := by
  have ha : 0 < c / Real.pi := div_pos hc Real.pi_pos
  have hb : 0 < Real.pi / (c / Real.pi) := div_pos Real.pi_pos ha
  unfold perGauss
  refine mul_pos (by positivity) ?_
  have e : (fun n : ℤ => Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - t) ^ 2))
      = fun n : ℤ => Real.exp (-(Real.pi / (c / Real.pi)) * ((n : ℝ) - t) ^ 2) := by
    funext n; rw [neg_div]
  rw [e]
  exact (gauss_shift_summable hb t).tsum_pos (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- The heat kernel of the torus is strictly positive. -/
theorem heatTorus_pos {c : ℝ} (hc : 0 < c) (d : ℕ) (x : FlatTorus d) : 0 < heatTorus d c x := by
  obtain ⟨t, rfl⟩ := flatTorus_lift d x
  rw [heatTorus_eq_prod hc]
  exact Finset.prod_pos fun i _ => perGauss_pos hc (t i)

/-- **The bound `B` of the consistency lemma from (P4).** For `σ, s > 0`, points `X, W` of the
    torus and `Y(z) = p_σ(X - z) (p_s(z - W) - c)`, `c = p_{σ+s}(X - W)`, with `p_σ ≤ Mσ`:
    `|Y(z)| ≤ K^d p_{s+2σ}(X - W) / pre(s+2σ)^d + Mσ c`, where `K = pre(σ) pre(s) (√(4πσ) + 1)` and
    `pre(τ) = (2πτ)^{-1/2}`. -/
theorem heat_Y_bound {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (X0 W0 z : FlatTorus d) {Mσ : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) :
    |heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
          - heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0))|
      ≤ (1 / (2 * Real.pi * σ) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * s) ^ (1 / 2 : ℝ))
            * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)) ^ d
          * heatTorus d (2 * Real.pi ^ 2 * (s + 2 * σ)) (X0 - W0)
          / (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d
        + Mσ * heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hcτ : 0 < 2 * Real.pi ^ 2 * (σ + s) := by positivity
  have hK := heatTorus_nonneg hcσ d (X0 - z)
  have hG := heatTorus_nonneg hcs d (z - W0)
  have hc := heatTorus_nonneg hcτ d (X0 - W0)
  have hpre : 0 < (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d := by positivity
  have hP4 := heatTorus_P4 hσ hs d (X0 - z) (X0 - W0)
  have e : X0 - W0 - (X0 - z) = z - W0 := by abel
  rw [e] at hP4
  have h1 : heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) * heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
      ≤ (1 / (2 * Real.pi * σ) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * s) ^ (1 / 2 : ℝ))
            * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)) ^ d
          * heatTorus d (2 * Real.pi ^ 2 * (s + 2 * σ)) (X0 - W0)
          / (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d := by
    rw [le_div_iff₀ hpre]; exact hP4
  have h2 : heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0)
      ≤ Mσ * heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) :=
    mul_le_mul_of_nonneg_right (hMσ _) hc
  have h3 : |heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
        - heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0)|
      ≤ heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
        + heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) := by
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_of_nonneg hK]
  calc heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * |heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
          - heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0)|
      ≤ heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
          + heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0)) :=
        mul_le_mul_of_nonneg_left h3 hK
    _ = heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) * heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
        + heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) := by ring
    _ ≤ _ := add_le_add h1 h2

/-! ### From fixed points to two sample points -/

/-- **From fixed points to two sample points.** `X_j` independent; `b ≠ i` two indices and `T` a
    finite index set containing neither. `Y x w z` and the threshold `thr x w` are jointly
    measurable. If for all fixed `x, w` the probability that
    `thr x w ≤ |∑_{j ∈ T} Y x w (X_j)|` is at most `q`, then the same holds with `x = X_b`,
    `w = X_i`. This is the step "given `x_b` and `x_i`, the remaining points are independent" of
    the consistency lemma. -/
theorem cond_pair_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [MeasurableSpace E] (X : ℕ → Ω → E)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j)) (b i : ℕ) (T : Finset ℕ)
    (hbT : b ∉ T) (hiT : i ∉ T)
    (Y : E → E → E → ℝ) (hY : Measurable fun p : E × E × E => Y p.1 p.2.1 p.2.2)
    (thr : E → E → ℝ) (hthr : Measurable fun p : E × E => thr p.1 p.2) {q : ℝ} (hq0 : 0 ≤ q)
    (hfix : ∀ x w : E, μ.real {ω | thr x w ≤ |∑ j ∈ T, Y x w (X j ω)|} ≤ q) :
    μ.real {ω | thr (X b ω) (X i ω) ≤ |∑ j ∈ T, Y (X b ω) (X i ω) (X j ω)|} ≤ q := by
  classical
  set S : Finset ℕ := {b, i} with hS
  have hbS : b ∈ S := by simp [hS]
  have hiS : i ∈ S := by simp [hS]
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro j hj hjT
    rcases Finset.mem_insert.mp hj with rfl | hj'
    · exact hbT hjT
    · rw [Finset.mem_singleton] at hj'; subst hj'; exact hiT hjT
  set A : Set ((S → E) × (T → E)) :=
    {p | thr (p.1 ⟨b, hbS⟩) (p.1 ⟨i, hiS⟩)
      ≤ |∑ j : T, Y (p.1 ⟨b, hbS⟩) (p.1 ⟨i, hiS⟩) (p.2 j)|} with hA
  have hub : Measurable fun p : (S → E) × (T → E) => p.1 ⟨b, hbS⟩ :=
    (measurable_pi_apply _).comp measurable_fst
  have hui : Measurable fun p : (S → E) × (T → E) => p.1 ⟨i, hiS⟩ :=
    (measurable_pi_apply _).comp measurable_fst
  have hAm : MeasurableSet A := by
    refine measurableSet_le (hthr.comp (hub.prodMk hui)) ?_
    refine Measurable.abs (Finset.measurable_sum _ fun j _ => ?_)
    exact hY.comp (hub.prodMk (hui.prodMk ((measurable_pi_apply j).comp measurable_snd)))
  have hsum : ∀ (x w : E) (f : ℕ → E), ∑ j : T, Y x w (f j) = ∑ j ∈ T, Y x w (f j) :=
    fun x w f => Finset.sum_coe_sort T (fun j => Y x w (f j))
  have h := sample_cond_bound (μ := μ) X h_indep hX S T hST A hAm hq0 (fun u => by
    have := hfix (u ⟨b, hbS⟩) (u ⟨i, hiS⟩)
    refine le_trans (le_of_eq ?_) this
    congr 1
    ext ω
    simp only [hA, Set.mem_setOf_eq]
    rw [hsum (u ⟨b, hbS⟩) (u ⟨i, hiS⟩) (fun j => X j ω)])
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [hA, Set.mem_setOf_eq]
  rw [hsum (X b ω) (X i ω) (fun j => X j ω)]

/-! ### Weighted consistency at a pair of sample points -/

/-- The centred summand of the consistency lemma:
    `Y(x, w, z) = p_σ(x - z) (p_s(z - w) - p_{σ+s}(x - w))`. -/
noncomputable def heatY (d : ℕ) (σ s : ℝ) (x w z : FlatTorus d) : ℝ :=
  heatTorus d (2 * Real.pi ^ 2 * σ) (x - z)
    * (heatTorus d (2 * Real.pi ^ 2 * s) (z - w) - heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (x - w))

/-- The variance bound of `torus_variance` as a function of `u = x - w`. -/
noncomputable def heatV (d : ℕ) (σ s : ℝ) (u : FlatTorus d) : ℝ :=
  (d : ℝ) * (σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * (2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ)))
    * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
      * ((2 * Real.pi ^ 2 * (6 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)) ^ (d - 1)
    * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u

/-- The bound `B` of `heat_Y_bound` as a function of `u = x - w`. -/
noncomputable def heatB (d : ℕ) (σ s Mσ : ℝ) (u : FlatTorus d) : ℝ :=
  (1 / (2 * Real.pi * σ) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * s) ^ (1 / 2 : ℝ))
        * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)) ^ d
      * heatTorus d (2 * Real.pi ^ 2 * (s + 2 * σ)) u
      / (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d
    + Mσ * heatTorus d (2 * Real.pi ^ 2 * (σ + s)) u

/-- The variance bound is nonnegative. -/
theorem heatV_nonneg {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (u : FlatTorus d) :
    0 ≤ heatV d σ s u := by
  unfold heatV
  have h := heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * s)) d u
  have hpi := Real.pi_pos
  positivity

/-- The bound `B` is positive. -/
theorem heatB_pos {σ s Mσ : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hM : 0 < Mσ) (d : ℕ)
    (u : FlatTorus d) : 0 < heatB d σ s Mσ u := by
  unfold heatB
  have h1 := heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (s + 2 * σ)) d u
  have h2 := heatTorus_pos (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (σ + s)) d u
  have hpi := Real.pi_pos
  have : 0 ≤ (1 / (2 * Real.pi * σ) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * s) ^ (1 / 2 : ℝ))
        * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)) ^ d
      * heatTorus d (2 * Real.pi ^ 2 * (s + 2 * σ)) u
      / (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d := by positivity
  have h3 : 0 < Mσ * heatTorus d (2 * Real.pi ^ 2 * (σ + s)) u := mul_pos hM h2
  linarith

/-- The Bernstein step at arbitrary fixed points of the torus, with the bound `B` from (P4). -/
theorem heat_consistency_fixed_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : FlatTorus d) (T : Finset ℕ)
    {Mσ ε : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T, heatY d σ s x w (X j ω)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * (Mσ * heatV d σ s (x - w)))
          + 2 * heatB d σ s Mσ (x - w) * ε)) := by
  obtain ⟨tx, rfl⟩ := flatTorus_lift d x
  obtain ⟨tw, rfl⟩ := flatTorus_lift d w
  have hM : 0 < Mσ :=
    lt_of_lt_of_le (heatTorus_pos (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * σ) d 0) (hMσ 0)
  exact heat_consistency_fixed hσ hs hσs d X h_indep hX hlaw tx tw T
    (heatB_pos hσ hs hM d _) (fun z => heat_Y_bound hσ hs d _ _ z hMσ) hMσ hε

/-- **Choice of the threshold in Bernstein's inequality.** For `B > 0`, `A ≥ 0`, `L > 0` and
    `eps = 2 B L + 2 √(A L)`: `L ≤ eps² / (4 A + 2 B eps)`, so that
    `exp(-eps²/(4A + 2B eps)) ≤ exp(-L)`. -/
theorem bern_threshold {B A L : ℝ} (hB : 0 < B) (hA : 0 ≤ A) (hL : 0 < L) :
    0 < 2 * B * L + 2 * Real.sqrt (A * L) ∧
    Real.exp (-(2 * B * L + 2 * Real.sqrt (A * L)) ^ 2
        / (4 * A + 2 * B * (2 * B * L + 2 * Real.sqrt (A * L)))) ≤ Real.exp (-L) := by
  set r := Real.sqrt (A * L) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = A * L := Real.sq_sqrt (mul_nonneg hA hL.le)
  have hBL : 0 < B * L := mul_pos hB hL
  have hε : 0 < 2 * B * L + 2 * r := by nlinarith
  refine ⟨hε, ?_⟩
  apply Real.exp_le_exp.mpr
  have hden : 0 < 4 * A + 2 * B * (2 * B * L + 2 * r) := by nlinarith
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hden]
  nlinarith [mul_nonneg hBL.le hr0]

/-- **Weighted consistency at a pair of sample points (estimate (ii) of the consistency lemma for
    one pair and one index set, without the exceptional terms).** Independent uniform points on
    the flat torus, indices `b, i` outside the finite index set `T`, `0 < σ ≤ s`, `p_σ ≤ Mσ`,
    `L > 0`. With the threshold
    `θ(x, w) = 2 B(x - w) L + 2 √(|T| Mσ V(x - w) L)`,
    where `V` carries the factor `σ/s` and the weight `p_{6s}` and `B` is the bound from (P4),
    `P(θ(X_b, X_i) ≤ |∑_{j ∈ T} Y(X_b, X_i, X_j)|) ≤ 2 e^{-L}`. -/
theorem heat_consistency_pair {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (b i : ℕ) (T : Finset ℕ)
    (hbT : b ∉ T) (hiT : i ∉ T) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | 2 * heatB d σ s Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (T.card * (Mσ * heatV d σ s (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ T, heatY d σ s (X b ω) (X i ω) (X j ω)|}
      ≤ 2 * Real.exp (-L) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hcτ : 0 < 2 * Real.pi ^ 2 * (σ + s) := by positivity
  have hc6 : 0 < 2 * Real.pi ^ 2 * (6 * s) := by positivity
  have hc2 : 0 < 2 * Real.pi ^ 2 * (s + 2 * σ) := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  have hYc : Continuous fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
      heatY d σ s p.1 p.2.1 p.2.2 := by
    unfold heatY
    exact ((heatTorus_continuous hcσ d).comp (continuous_fst.sub (continuous_snd.comp continuous_snd))).mul
      (((heatTorus_continuous hcs d).comp
          ((continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd))).sub
        ((heatTorus_continuous hcτ d).comp (continuous_fst.sub (continuous_fst.comp continuous_snd))))
  have hVc : Continuous fun u : FlatTorus d => heatV d σ s u := by
    unfold heatV
    exact continuous_const.mul (heatTorus_continuous hc6 d)
  have hBc : Continuous fun u : FlatTorus d => heatB d σ s Mσ u := by
    unfold heatB
    exact ((continuous_const.mul (heatTorus_continuous hc2 d)).div_const _).add
      (continuous_const.mul (heatTorus_continuous hcτ d))
  have hsub : Continuous fun p : FlatTorus d × FlatTorus d => p.1 - p.2 :=
    continuous_fst.sub continuous_snd
  have hthr : Continuous fun p : FlatTorus d × FlatTorus d =>
      2 * heatB d σ s Mσ (p.1 - p.2) * L
        + 2 * Real.sqrt (T.card * (Mσ * heatV d σ s (p.1 - p.2)) * L) :=
    ((continuous_const.mul (hBc.comp hsub)).mul continuous_const).add
      (continuous_const.mul (Real.continuous_sqrt.comp
        ((continuous_const.mul (continuous_const.mul (hVc.comp hsub))).mul continuous_const)))
  refine cond_pair_bound (μ := μ) X h_indep hX b i T hbT hiT (heatY d σ s) hYc.measurable
    (fun x w => 2 * heatB d σ s Mσ (x - w) * L
      + 2 * Real.sqrt (T.card * (Mσ * heatV d σ s (x - w)) * L)) hthr.measurable
    (by positivity) (fun x w => ?_)
  have hA : 0 ≤ (T.card : ℝ) * (Mσ * heatV d σ s (x - w)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hM.le (heatV_nonneg hσ hs d _))
  obtain ⟨hε, hexp⟩ := bern_threshold (heatB_pos hσ hs hM d (x - w)) hA hL
  have h := heat_consistency_fixed_all hσ hs hσs d X h_indep hX hlaw x w T hMσ hε
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left hexp (by norm_num)

/-! ### Weighted consistency for all pairs of sample points -/

/-- **Weighted consistency simultaneously for all pairs of sample points.** Independent uniform
    points on the flat torus, `0 < σ ≤ s`, `p_σ ≤ Mσ`, `L > 0`. With probability at least
    `1 - 2 N² e^{-L}`, for all `b, i < N`, the sum of `Y(X_b, X_i, X_j)` over the other indices
    `j < N`, `j ∉ {b, i}`, is smaller in absolute value than
    `2 B(X_b - X_i) L + 2 √(N Mσ V(X_b - X_i) L)`. -/
theorem heat_consistency_all_pairs {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ s Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV d σ s (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ s (X b ω) (X i ω) (X j ω)|}
      ≤ (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  set E : ℕ × ℕ → Set Ω := fun p => {ω |
      2 * heatB d σ s Mσ (X p.1 ω - X p.2 ω) * L
        + 2 * Real.sqrt ((((Finset.range N).erase p.1).erase p.2).card
            * (Mσ * heatV d σ s (X p.1 ω - X p.2 ω)) * L)
      ≤ |∑ j ∈ ((Finset.range N).erase p.1).erase p.2,
          heatY d σ s (X p.1 ω) (X p.2 ω) (X j ω)|} with hE
  have hsub : {ω | ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ s Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV d σ s (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ s (X b ω) (X i ω) (X j ω)|}
      ⊆ ⋃ p ∈ Finset.range N ×ˢ Finset.range N, E p := by
    rintro ω ⟨b, hb, i, hi, h⟩
    simp only [Set.mem_iUnion, Finset.mem_product]
    refine ⟨(b, i), ⟨hb, hi⟩, ?_⟩
    simp only [hE, Set.mem_setOf_eq]
    refine le_trans ?_ h
    have hcard : ((((Finset.range N).erase b).erase i).card : ℝ) ≤ N := by
      have h1 := Finset.card_erase_le (s := (Finset.range N).erase b) (a := i)
      have h2 := Finset.card_erase_le (s := Finset.range N) (a := b)
      rw [Finset.card_range] at h2
      exact_mod_cast h1.trans h2
    have hV := heatV_nonneg hσ hs d (X b ω - X i ω)
    have hmono : ((((Finset.range N).erase b).erase i).card : ℝ)
          * (Mσ * heatV d σ s (X b ω - X i ω)) * L
        ≤ N * (Mσ * heatV d σ s (X b ω - X i ω)) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (mul_nonneg hM.le hV)) hL.le
    linarith [Real.sqrt_le_sqrt hmono]
  have hone : ∀ p ∈ Finset.range N ×ˢ Finset.range N, μ.real (E p) ≤ 2 * Real.exp (-L) := by
    intro p _
    exact heat_consistency_pair hσ hs hσs d X h_indep hX hlaw p.1 p.2
      (((Finset.range N).erase p.1).erase p.2)
      (fun h => Finset.notMem_erase p.1 _ (Finset.mem_of_mem_erase h))
      (Finset.notMem_erase p.2 _) hMσ hL
  calc μ.real _ ≤ μ.real (⋃ p ∈ Finset.range N ×ˢ Finset.range N, E p) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, μ.real (E p) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ Finset.range N ×ˢ Finset.range N, 2 * Real.exp (-L) := Finset.sum_le_sum hone
    _ = (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/-! ### Weighted consistency for all pairs and all numbers of steps -/

/-- **Weighted consistency simultaneously for all pairs of sample points and all numbers of steps
    `1 ≤ m ≤ K`.** Kernel time `σ`, times `s = m σ`. With probability at least
    `1 - 2 K N² e^{-L}`, for all `1 ≤ m ≤ K` and all `b, i < N`, the sum of
    `Y_m(X_b, X_i, X_j)` over `j < N`, `j ∉ {b, i}`, is smaller in absolute value than
    `2 B_m(X_b - X_i) L + 2 √(N Mσ V_m(X_b - X_i) L)`. -/
theorem heat_consistency_all_steps {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
  set E : ℕ → Set Ω := fun m => {ω | ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} with hE
  have hsub : {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ⊆ ⋃ m ∈ Finset.Icc 1 K, E m := by
    rintro ω ⟨m, hm, h⟩
    simp only [Set.mem_iUnion]
    exact ⟨m, hm, h⟩
  have hone : ∀ m ∈ Finset.Icc 1 K, μ.real (E m) ≤ (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hs : 0 < (m : ℝ) * σ := by positivity
    have hσs : σ ≤ (m : ℝ) * σ := by nlinarith
    exact heat_consistency_all_pairs hσ hs hσs d X h_indep hX hlaw N hMσ hL
  calc μ.real _ ≤ μ.real (⋃ m ∈ Finset.Icc 1 K, E m) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ m ∈ Finset.Icc 1 K, μ.real (E m) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 K, (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := Finset.sum_le_sum hone
    _ = (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp

/-! ### Moments of the summand and the Bernstein step for its absolute value -/

/-- Continuity of the summand `Y` in its last variable. -/
theorem heatY_continuous {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (x w : FlatTorus d) :
    Continuous fun z : FlatTorus d => heatY d σ s x w z := by
  unfold heatY
  exact ((heatTorus_continuous (by positivity) d).comp (continuous_const.sub continuous_id)).mul
    (((heatTorus_continuous (by positivity) d).comp (continuous_id.sub continuous_const)).sub
      continuous_const)

/-- **Second moment of the summand `Y` under the uniform law:**
    `∫ Y(x, w, z)² dz ≤ Mσ V(x - w)`. -/
theorem heatY_sq_integral_le {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : FlatTorus d) {Mσ : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) :
    ∫ z, heatY d σ s x w z ^ 2 ∂flatTorusMeasure d ≤ Mσ * heatV d σ s (x - w) := by
  obtain ⟨tx, rfl⟩ := flatTorus_lift d x
  obtain ⟨tw, rfl⟩ := flatTorus_lift d w
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  set X0 : FlatTorus d := fun i => ((tx i : ℝ) : UnitAddCircle) with hX0
  set W0 : FlatTorus d := fun i => ((tw i : ℝ) : UnitAddCircle) with hW0
  set c : ℝ := heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) with hc
  have hK : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) :=
    (heatTorus_continuous hcσ d).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) :=
    (heatTorus_continuous hcs d).comp (continuous_id.sub continuous_const)
  have hYc := heatY_continuous hσ hs d X0 W0
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : ∫ z, heatY d σ s X0 W0 z ^ 2 ∂flatTorusMeasure d
      ≤ ∫ z, Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2) ∂flatTorusMeasure d := by
    refine integral_mono (hint _ (hYc.pow 2))
      ((hint _ (hK.mul ((hG.sub continuous_const).pow 2))).const_mul _) (fun z => ?_)
    have h0 := heatTorus_nonneg hcσ d (X0 - z)
    have h1 := hMσ (X0 - z)
    have h2 : 0 ≤ (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2 := _root_.sq_nonneg _
    show heatY d σ s X0 W0 z ^ 2
        ≤ Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2)
    unfold heatY
    rw [mul_pow, _root_.sq (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))]
    nlinarith [mul_nonneg h0 h2, mul_le_mul_of_nonneg_right h1 (mul_nonneg h0 h2)]
  have hM0 : 0 ≤ Mσ := (heatTorus_nonneg hcσ d 0).trans (hMσ 0)
  have hvar := torus_variance hσ hs hσs d tx tw
  rw [torus_first_moment hσ hs d tx tw] at hvar
  refine hle.trans ?_
  rw [integral_const_mul, torus_centered_second hσ hs d tx tw]
  unfold heatV
  exact mul_le_mul_of_nonneg_left hvar hM0

/-- **First absolute moment of `Y`:** `∫ |Y(x, w, z)| dz ≤ √(Mσ V(x - w))` (Cauchy–Schwarz). -/
theorem heatY_abs_integral_le {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : FlatTorus d) {Mσ : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) :
    ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d ≤ Real.sqrt (Mσ * heatV d σ s (x - w)) := by
  have hYc := heatY_continuous hσ hs d x w
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set e : ℝ := ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d with he
  have he0 : 0 ≤ e := integral_nonneg fun z => abs_nonneg _
  have hsq : e ^ 2 ≤ ∫ z, heatY d σ s x w z ^ 2 ∂flatTorusMeasure d := by
    have hnn : 0 ≤ ∫ z, (|heatY d σ s x w z| - e) ^ 2 ∂flatTorusMeasure d :=
      integral_nonneg fun z => _root_.sq_nonneg _
    have hexp : ∀ z, (|heatY d σ s x w z| - e) ^ 2
        = heatY d σ s x w z ^ 2 - 2 * e * |heatY d σ s x w z| + e ^ 2 := fun z => by
      rw [sub_sq, sq_abs]; ring
    simp_rw [hexp] at hnn
    have I1 : Integrable (fun z => heatY d σ s x w z ^ 2) (flatTorusMeasure d) := hint _ (hYc.pow 2)
    have I2 : Integrable (fun z => 2 * e * |heatY d σ s x w z|) (flatTorusMeasure d) :=
      (hint _ hYc.abs).const_mul _
    have I12 : Integrable (fun z => heatY d σ s x w z ^ 2 - 2 * e * |heatY d σ s x w z|)
        (flatTorusMeasure d) := I1.sub I2
    rw [integral_add I12 (integrable_const _), integral_sub I1 I2, integral_const_mul,
      integral_const] at hnn
    simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul] at hnn
    nlinarith
  have h2 := heatY_sq_integral_le hσ hs hσs d x w hMσ
  calc e = Real.sqrt (e ^ 2) := (Real.sqrt_sq he0).symm
    _ ≤ Real.sqrt (Mσ * heatV d σ s (x - w)) := Real.sqrt_le_sqrt (hsq.trans h2)

/-- **First absolute moment of `Y`, sharp form:** `∫ |Y(x, w, z)| dz ≤ √(V(x - w))`, without the
    factor `Mσ` (Cauchy–Schwarz with respect to the probability density `p_σ(x - ·)`). -/
theorem heatY_abs_integral_sharp {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : FlatTorus d) :
    ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d ≤ Real.sqrt (heatV d σ s (x - w)) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  obtain ⟨tx, rfl⟩ := flatTorus_lift d x
  obtain ⟨tw, rfl⟩ := flatTorus_lift d w
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  set X0 : FlatTorus d := fun i => ((tx i : ℝ) : UnitAddCircle) with hX0
  set W0 : FlatTorus d := fun i => ((tw i : ℝ) : UnitAddCircle) with hW0
  set c : ℝ := heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) with hc
  have hK : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) :=
    (heatTorus_continuous hcσ d).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) :=
    (heatTorus_continuous hcs d).comp (continuous_id.sub continuous_const)
  have hYc := heatY_continuous hσ hs d X0 W0
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ∫ z, |heatY d σ s X0 W0 z| ∂flatTorusMeasure d := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; exact integral_nonneg fun z => abs_nonneg _
  have hYabs : ∀ z, |heatY d σ s X0 W0 z|
      = heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * |heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c| := fun z => by
    unfold heatY
    rw [abs_mul, abs_of_nonneg (heatTorus_nonneg hcσ d _)]
  have hnn : 0 ≤ ∫ z, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (|heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c| - e) ^ 2 ∂flatTorusMeasure d :=
    integral_nonneg fun z => mul_nonneg (heatTorus_nonneg hcσ d _) (_root_.sq_nonneg _)
  have hexp : ∀ z, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * (|heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c| - e) ^ 2
      = heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2
        - 2 * e * |heatY d σ s X0 W0 z|
        + e ^ 2 * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) := fun z => by
    rw [hYabs z, sub_sq, sq_abs]; ring
  simp_rw [hexp] at hnn
  have I1 : Integrable (fun z => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2) (flatTorusMeasure d) :=
    hint _ (hK.mul ((hG.sub continuous_const).pow 2))
  have I2 : Integrable (fun z => 2 * e * |heatY d σ s X0 W0 z|) (flatTorusMeasure d) :=
    (hint _ hYc.abs).const_mul _
  have I3 : Integrable (fun z => e ^ 2 * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))
      (flatTorusMeasure d) := (hint _ hK).const_mul _
  have hmass : ∫ z, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) ∂flatTorusMeasure d = 1 := by
    rw [integral_sub_left_eq_self (heatTorus d (2 * Real.pi ^ 2 * σ)) (flatTorusMeasure d) X0,
      heatTorus_mass hcσ d]
  have I12 : Integrable (fun z => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2 - 2 * e * |heatY d σ s X0 W0 z|)
      (flatTorusMeasure d) := I1.sub I2
  rw [integral_add I12 I3, integral_sub I1 I2, integral_const_mul, integral_const_mul,
    hmass, torus_centered_second hσ hs d tx tw, ← he] at hnn
  have hvar := torus_variance hσ hs hσs d tx tw
  rw [torus_first_moment hσ hs d tx tw] at hvar
  have hsq : e ^ 2 ≤ heatV d σ s (X0 - W0) := by
    unfold heatV
    nlinarith
  rw [← he]
  calc e = Real.sqrt (e ^ 2) := (Real.sqrt_sq he0).symm
    _ ≤ Real.sqrt (heatV d σ s (X0 - W0)) := Real.sqrt_le_sqrt hsq

/-- The summand `Y` is bounded by `B` at arbitrary points. -/
theorem heatY_abs_le {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (x w z : FlatTorus d) {Mσ : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) :
    |heatY d σ s x w z| ≤ heatB d σ s Mσ (x - w) := by
  have h := heat_Y_bound hσ hs d x w z hMσ
  unfold heatY heatB
  exact h

/-- **Bernstein step for `|Y| - E|Y|` at fixed points.** With `e = ∫ |Y(x, w, z)| dz`,
    `P(|∑_{j ∈ T} (|Y(x, w, X_j)| - e)| ≥ eps) ≤ 2 exp(-eps² / (4 |T| Mσ V + 2 B eps))`. -/
theorem heat_abs_consistency_fixed_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : FlatTorus d) (T : Finset ℕ)
    {Mσ ε : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T, (|heatY d σ s x w (X j ω)|
        - ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * (Mσ * heatV d σ s (x - w)))
          + 2 * heatB d σ s Mσ (x - w) * ε)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  have hYc := heatY_continuous hσ hs d x w
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set e : ℝ := ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d with he
  have he0 : 0 ≤ e := integral_nonneg fun z => abs_nonneg _
  have hB := heatB_pos hσ hs hM d (x - w)
  have hYB : ∀ z, |heatY d σ s x w z| ≤ heatB d σ s Mσ (x - w) :=
    fun z => heatY_abs_le hσ hs d x w z hMσ
  have heB : e ≤ heatB d σ s Mσ (x - w) := by
    have h := integral_mono (hint _ hYc.abs) (integrable_const (heatB d σ s Mσ (x - w))) hYB
    simpa using h
  have hfc : Continuous fun z : FlatTorus d => |heatY d σ s x w z| - e :=
    hYc.abs.sub continuous_const
  have htr : ∀ (j : ℕ) (f : FlatTorus d → ℝ), Continuous f →
      ∫ ω, f (X j ω) ∂μ = ∫ z, f z ∂flatTorusMeasure d := fun j f hf => by
    rw [← hlaw j, integral_map (hX j).aemeasurable hf.measurable.aestronglyMeasurable]
  refine bernstein_two_sided_fn (μ := μ) X h_indep hX
    (fun z => |heatY d σ s x w z| - e) hfc.measurable T hB (fun z => ?_)
    (fun j _ => ?_) (fun j _ => ?_) hε
  · rw [abs_le]
    constructor <;> linarith [hYB z, abs_nonneg (heatY d σ s x w z)]
  · rw [htr j _ hfc, integral_sub (hint _ hYc.abs) (integrable_const _), integral_const]
    simp [he]
  · rw [htr j (fun z => (|heatY d σ s x w z| - e) ^ 2) (hfc.pow 2)]
    have hexp : ∀ z, (|heatY d σ s x w z| - e) ^ 2
        = heatY d σ s x w z ^ 2 - 2 * e * |heatY d σ s x w z| + e ^ 2 := fun z => by
      rw [sub_sq, sq_abs]; ring
    simp_rw [hexp]
    have I1 : Integrable (fun z => heatY d σ s x w z ^ 2) (flatTorusMeasure d) := hint _ (hYc.pow 2)
    have I2 : Integrable (fun z => 2 * e * |heatY d σ s x w z|) (flatTorusMeasure d) :=
      (hint _ hYc.abs).const_mul _
    have I12 : Integrable (fun z => heatY d σ s x w z ^ 2 - 2 * e * |heatY d σ s x w z|)
        (flatTorusMeasure d) := I1.sub I2
    rw [integral_add I12 (integrable_const _), integral_sub I1 I2, integral_const_mul,
      integral_const]
    simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
    have h2 := heatY_sq_integral_le hσ hs hσs d x w hMσ
    nlinarith [_root_.sq_nonneg e]

/-! ### The centred absolute summand at a pair of sample points -/

/-- Joint continuity of the summand `Y`. -/
theorem heatY_joint_continuous {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) :
    Continuous fun p : FlatTorus d × FlatTorus d × FlatTorus d => heatY d σ s p.1 p.2.1 p.2.2 := by
  unfold heatY
  exact ((heatTorus_continuous (by positivity) d).comp
      (continuous_fst.sub (continuous_snd.comp continuous_snd))).mul
    (((heatTorus_continuous (by positivity) d).comp
        ((continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd))).sub
      ((heatTorus_continuous (by positivity) d).comp
        (continuous_fst.sub (continuous_fst.comp continuous_snd))))

set_option maxHeartbeats 1600000 in
/-- Continuity of the first absolute moment of `Y` in the two points. -/
theorem heatY_absmean_continuous {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) :
    Continuous fun p : FlatTorus d × FlatTorus d =>
      ∫ z, |heatY d σ s p.1 p.2 z| ∂flatTorusMeasure d := by
  have hj := heatY_joint_continuous hσ hs d
  have hu : Continuous (Function.uncurry fun (p : FlatTorus d × FlatTorus d) (z : FlatTorus d) =>
      |heatY d σ s p.1 p.2 z|) := by
    have hmap : Continuous fun q : (FlatTorus d × FlatTorus d) × FlatTorus d =>
        ((q.1.1, (q.1.2, q.2)) : FlatTorus d × FlatTorus d × FlatTorus d) :=
      (continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
    exact (hj.comp hmap).abs
  have h := continuous_parametric_integral_of_continuous (μ := flatTorusMeasure d) hu
    (isCompact_univ (X := FlatTorus d))
  simp only [Measure.restrict_univ] at h
  exact h

/-- The first absolute moment of the summand: `e(x, w) = ∫ |Y(x, w, z)| dz`. -/
noncomputable def heatYmean (d : ℕ) (σ s : ℝ) (x w : FlatTorus d) : ℝ :=
  ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d

/-- Continuity of the mean in the two points. -/
theorem heatYmean_continuous {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) :
    Continuous fun p : FlatTorus d × FlatTorus d => heatYmean d σ s p.1 p.2 :=
  heatY_absmean_continuous hσ hs d

/-- Unfolding of the mean (the definition is made irreducible below). -/
theorem heatYmean_eq (d : ℕ) (σ s : ℝ) (x w : FlatTorus d) :
    heatYmean d σ s x w = ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d := rfl

attribute [irreducible] heatYmean

/-- The centred absolute summand: `|Y(x, w, z)| - e(x, w)`. -/
noncomputable def heatYc (d : ℕ) (σ s : ℝ) (x w z : FlatTorus d) : ℝ :=
  |heatY d σ s x w z| - heatYmean d σ s x w

/-- Joint continuity of the centred absolute summand. -/
theorem heatYc_joint_continuous {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) :
    Continuous fun p : FlatTorus d × FlatTorus d × FlatTorus d => heatYc d σ s p.1 p.2.1 p.2.2 := by
  have h1 : Continuous fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
      |heatY d σ s p.1 p.2.1 p.2.2| := (heatY_joint_continuous hσ hs d).abs
  have hg : Continuous fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
      ((p.1, p.2.1) : FlatTorus d × FlatTorus d) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have h2 : Continuous fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
      heatYmean d σ s p.1 p.2.1 := (heatYmean_continuous hσ hs d).comp hg
  exact h1.sub h2

/-- The threshold of the weighted consistency estimates. -/
noncomputable def heatThr (d : ℕ) (σ s Mσ L A : ℝ) (u : FlatTorus d) : ℝ :=
  2 * heatB d σ s Mσ u * L + 2 * Real.sqrt (A * (Mσ * heatV d σ s u) * L)

/-- Continuity of the threshold in the two points. -/
theorem heatThr_continuous {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (Mσ L A : ℝ) :
    Continuous fun p : FlatTorus d × FlatTorus d => heatThr d σ s Mσ L A (p.1 - p.2) := by
  have hVc : Continuous fun u : FlatTorus d => heatV d σ s u := by
    unfold heatV
    exact continuous_const.mul (heatTorus_continuous (by positivity) d)
  have hBc : Continuous fun u : FlatTorus d => heatB d σ s Mσ u := by
    unfold heatB
    exact ((continuous_const.mul (heatTorus_continuous (by positivity) d)).div_const _).add
      (continuous_const.mul (heatTorus_continuous (by positivity) d))
  have hsub : Continuous fun p : FlatTorus d × FlatTorus d => p.1 - p.2 :=
    continuous_fst.sub continuous_snd
  unfold heatThr
  exact ((continuous_const.mul (hBc.comp hsub)).mul continuous_const).add
    (continuous_const.mul (Real.continuous_sqrt.comp
      ((continuous_const.mul (continuous_const.mul (hVc.comp hsub))).mul continuous_const)))

/-- The Bernstein step for the centred absolute summand at fixed points, with the threshold. -/
theorem heatYc_fixed {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : FlatTorus d) (T : Finset ℕ)
    {Mσ L : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | heatThr d σ s Mσ L T.card (x - w) ≤ |∑ j ∈ T, heatYc d σ s x w (X j ω)|}
      ≤ 2 * Real.exp (-L) := by
  have hM : 0 < Mσ :=
    lt_of_lt_of_le (heatTorus_pos (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * σ) d 0) (hMσ 0)
  have hA : 0 ≤ (T.card : ℝ) * (Mσ * heatV d σ s (x - w)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hM.le (heatV_nonneg hσ hs d _))
  obtain ⟨hε, hexp⟩ := bern_threshold (heatB_pos hσ hs hM d (x - w)) hA hL
  have h := heat_abs_consistency_fixed_all hσ hs hσs d X h_indep hX hlaw x w T hMσ hε
  unfold heatThr heatYc
  simp only [heatYmean_eq]
  exact h.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))

/-- **Weighted bound for the absolute summand at a pair of sample points.** As
    `heat_consistency_pair`, for the centred absolute summand `|Y| - E|Y|`. -/
theorem heat_abs_consistency_pair {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (b i : ℕ) (T : Finset ℕ)
    (hbT : b ∉ T) (hiT : i ∉ T) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | heatThr d σ s Mσ L T.card (X b ω - X i ω)
        ≤ |∑ j ∈ T, heatYc d σ s (X b ω) (X i ω) (X j ω)|}
      ≤ 2 * Real.exp (-L) :=
  cond_pair_bound (μ := μ) X h_indep hX b i T hbT hiT (heatYc d σ s)
    (heatYc_joint_continuous hσ hs d).measurable
    (fun x w => heatThr d σ s Mσ L T.card (x - w))
    (heatThr_continuous hσ hs d Mσ L T.card).measurable (by positivity)
    (fun x w => heatYc_fixed hσ hs hσs d X h_indep hX hlaw x w T hMσ hL)

/-! ### The centred absolute summand for all pairs and all numbers of steps -/

/-- The threshold is monotone in the size parameter. -/
theorem heatThr_mono {σ s Mσ L A A' : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hM : 0 ≤ Mσ) (hL : 0 ≤ L)
    (hAA : A ≤ A') (d : ℕ) (u : FlatTorus d) :
    heatThr d σ s Mσ L A u ≤ heatThr d σ s Mσ L A' u := by
  unfold heatThr
  have hV := heatV_nonneg hσ hs d u
  have h : A * (Mσ * heatV d σ s u) * L ≤ A' * (Mσ * heatV d σ s u) * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA (mul_nonneg hM hV)) hL
  linarith [Real.sqrt_le_sqrt h]

/-- **The centred absolute summand, simultaneously for all pairs of sample points and all numbers
    of steps `1 ≤ m ≤ K`.** With probability at least `1 - 2 K N² e^{-L}`, for all `1 ≤ m ≤ K` and
    `b, i < N`, the sum of `|Y_m(X_b, X_i, X_j)| - E|Y_m|` over `j < N`, `j ∉ {b, i}`, is smaller in
    absolute value than the threshold `2 B_m L + 2 √(N Mσ V_m L)` at `X_b - X_i`. -/
theorem heat_abs_consistency_all_steps {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatThr d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  set I : Finset (ℕ × ℕ × ℕ) := Finset.Icc 1 K ×ˢ (Finset.range N ×ˢ Finset.range N) with hI
  set E : ℕ × ℕ × ℕ → Set Ω := fun q => {ω |
      heatThr d σ ((q.1 : ℝ) * σ) Mσ L
          ((((Finset.range N).erase q.2.1).erase q.2.2).card : ℝ) (X q.2.1 ω - X q.2.2 ω)
        ≤ |∑ j ∈ ((Finset.range N).erase q.2.1).erase q.2.2,
            heatYc d σ ((q.1 : ℝ) * σ) (X q.2.1 ω) (X q.2.2 ω) (X j ω)|} with hE
  have hsub : {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatThr d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ⊆ ⋃ q ∈ I, E q := by
    rintro ω ⟨m, hm, b, hb, i, hi, h⟩
    simp only [Set.mem_iUnion]
    refine ⟨(m, b, i), by simp [hI, Finset.mem_product, hm, hb, hi], ?_⟩
    simp only [hE, Set.mem_setOf_eq]
    refine le_trans ?_ h
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hcard : ((((Finset.range N).erase b).erase i).card : ℝ) ≤ N := by
      have h1 := Finset.card_erase_le (s := (Finset.range N).erase b) (a := i)
      have h2 := Finset.card_erase_le (s := Finset.range N) (a := b)
      rw [Finset.card_range] at h2
      exact_mod_cast h1.trans h2
    exact heatThr_mono hσ (by positivity) hM.le hL.le hcard d _
  have hone : ∀ q ∈ I, μ.real (E q) ≤ 2 * Real.exp (-L) := by
    intro q hq
    have hm := (Finset.mem_product.mp hq).1
    have hm1 : (1 : ℝ) ≤ q.1 := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hs : 0 < (q.1 : ℝ) * σ := by positivity
    have hσs : σ ≤ (q.1 : ℝ) * σ := by nlinarith
    exact heat_abs_consistency_pair hσ hs hσs d X h_indep hX hlaw q.2.1 q.2.2
      (((Finset.range N).erase q.2.1).erase q.2.2)
      (fun h => Finset.notMem_erase q.2.1 _ (Finset.mem_of_mem_erase h))
      (Finset.notMem_erase q.2.2 _) hMσ hL
  calc μ.real _ ≤ μ.real (⋃ q ∈ I, E q) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ q ∈ I, μ.real (E q) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ I, 2 * Real.exp (-L) := Finset.sum_le_sum hone
    _ = (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
        rw [Finset.sum_const, hI, Finset.card_product, Finset.card_product, Nat.card_Icc,
          Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### Splitting of the defect and the exceptional terms (deterministic) -/

/-- **Splitting of the one-step defect (the identity `h = (S₁ + S₂)/r` of the consistency lemma,
    as an estimate).** Weights `Pt j ≥ 0`, normalisation factors `u j` with `|u j - 1| ≤ η`,
    `r = ∑ Pt j u j > 0`. For the row `P j = Pt j u j / r` of the normalised walk and any numbers
    `g j`, `c`:
    `|∑ P j g j - c| ≤ (|∑ Pt j (g j - c)| + η ∑ Pt j |g j - c|) / r`. -/
theorem defect_split {n : Type*} [Fintype n] (Pt u g : n → ℝ) (c η : ℝ)
    (hPt : ∀ j, 0 ≤ Pt j) (hu : ∀ j, |u j - 1| ≤ η) (hr : 0 < ∑ l, Pt l * u l) :
    |∑ j, Pt j * u j / (∑ l, Pt l * u l) * g j - c|
      ≤ (|∑ j, Pt j * (g j - c)| + η * ∑ j, Pt j * |g j - c|) / (∑ l, Pt l * u l) := by
  set r := ∑ l, Pt l * u l with hrdef
  have e1 : ∑ j, Pt j * u j / r * g j - c = (∑ j, Pt j * u j * (g j - c)) / r := by
    have hsum : ∑ j, Pt j * u j * (g j - c) = ∑ j, Pt j * u j * g j - c * r := by
      rw [hrdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, sub_div, mul_div_cancel_right₀ _ hr.ne', Finset.sum_div]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, Pt j * u j * (g j - c)
      = ∑ j, Pt j * (g j - c) + ∑ j, Pt j * ((u j - 1) * (g j - c)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : |∑ j, Pt j * ((u j - 1) * (g j - c))| ≤ η * ∑ j, Pt j * |g j - c| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (hPt j)]
    have := mul_le_mul_of_nonneg_right (hu j) (abs_nonneg (g j - c))
    nlinarith [hPt j, mul_le_mul_of_nonneg_left this (hPt j)]
  rw [e1, abs_div, abs_of_pos hr, e2]
  exact div_le_div_of_nonneg_right ((abs_add_le _ _).trans (add_le_add le_rfl h2)) hr.le

/-- Removing two indices from a sum costs at most the two terms. -/
theorem abs_sum_le_erase2 (s : Finset ℕ) (y : ℕ → ℝ) (b i : ℕ) :
    |∑ j ∈ s, y j| ≤ |∑ j ∈ (s.erase b).erase i, y j| + |y b| + |y i| := by
  have h1 : |∑ j ∈ s, y j| ≤ |∑ j ∈ s.erase b, y j| + |y b| := by
    by_cases hb : b ∈ s
    · have e : ∑ j ∈ s, y j = ∑ j ∈ s.erase b, y j + y b := by
        rw [Finset.sum_erase_eq_sub hb]; ring
      rw [e]; exact abs_add_le _ _
    · rw [Finset.erase_eq_of_notMem hb]; linarith [abs_nonneg (y b)]
  have h2 : |∑ j ∈ s.erase b, y j| ≤ |∑ j ∈ (s.erase b).erase i, y j| + |y i| := by
    by_cases hi : i ∈ s.erase b
    · have e : ∑ j ∈ s.erase b, y j = ∑ j ∈ (s.erase b).erase i, y j + y i := by
        rw [Finset.sum_erase_eq_sub hi]; ring
      rw [e]; exact abs_add_le _ _
    · rw [Finset.erase_eq_of_notMem hi]; linarith [abs_nonneg (y i)]
  linarith

/-- The sum of the absolute values against the centred sum without two indices: for `e ≥ 0`,
    `∑_{j ∈ s} |y j| ≤ |∑_{j ∈ s ∖ {b, i}} (|y j| - e)| + |s| e + |y b| + |y i|`. -/
theorem sum_abs_le_erase2 (s : Finset ℕ) (y : ℕ → ℝ) (b i : ℕ) {e : ℝ} (he : 0 ≤ e) :
    ∑ j ∈ s, |y j| ≤ |∑ j ∈ (s.erase b).erase i, (|y j| - e)| + s.card * e + |y b| + |y i| := by
  have h0 := abs_sum_le_erase2 s (fun j => |y j|) b i
  simp only [abs_abs] at h0
  have hnn : 0 ≤ ∑ j ∈ s, |y j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  rw [abs_of_nonneg hnn] at h0
  have hnn2 : 0 ≤ ∑ j ∈ (s.erase b).erase i, |y j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  rw [abs_of_nonneg hnn2] at h0
  have hsplit : ∑ j ∈ (s.erase b).erase i, |y j|
      = ∑ j ∈ (s.erase b).erase i, (|y j| - e) + ((s.erase b).erase i).card * e := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  have hcard : (((s.erase b).erase i).card : ℝ) ≤ s.card := by
    exact_mod_cast (Finset.card_erase_le).trans Finset.card_erase_le
  have h3 : (((s.erase b).erase i).card : ℝ) * e ≤ s.card * e :=
    mul_le_mul_of_nonneg_right hcard he
  linarith [le_abs_self (∑ j ∈ (s.erase b).erase i, (|y j| - e))]

/-! ### The defect from the two Bernstein bounds (deterministic) -/

/-- `defect_split` for sums over `Finset.range N`. -/
theorem defect_split_range (N : ℕ) (Pt u g : ℕ → ℝ) (c η : ℝ)
    (hPt : ∀ j, 0 ≤ Pt j) (hu : ∀ j, |u j - 1| ≤ η)
    (hr : 0 < ∑ l ∈ Finset.range N, Pt l * u l) :
    |∑ j ∈ Finset.range N, Pt j * u j / (∑ l ∈ Finset.range N, Pt l * u l) * g j - c|
      ≤ (|∑ j ∈ Finset.range N, Pt j * (g j - c)|
          + η * ∑ j ∈ Finset.range N, Pt j * |g j - c|)
        / (∑ l ∈ Finset.range N, Pt l * u l) := by
  have h := defect_split (n := Fin N) (fun j => Pt j) (fun j => u j) (fun j => g j) c η
    (fun j => hPt j) (fun j => hu j)
    (by rw [Fin.sum_univ_eq_sum_range (fun l => Pt l * u l) N]; exact hr)
  simp only [Fin.sum_univ_eq_sum_range (fun l => Pt l * u l) N] at h
  rw [Fin.sum_univ_eq_sum_range
      (fun j => Pt j * u j / (∑ l ∈ Finset.range N, Pt l * u l) * g j) N,
    Fin.sum_univ_eq_sum_range (fun j => Pt j * (g j - c)) N,
    Fin.sum_univ_eq_sum_range (fun j => Pt j * |g j - c|) N] at h
  exact h

/-- **The defect from the two Bernstein bounds (deterministic assembly).** `N` points; weights
    `Pt j ≥ 0`, normalisation factors with `|u j - 1| ≤ η`, `r₀ ≤ ∑ Pt j u j`; `y j = N Pt j (g j - c)`.
    If the sum of `y j` and the centred sum of `|y j| - e` over `j < N`, `j ∉ {b, i}`, are at most
    `thr` in absolute value, and `|y b|, |y i| ≤ B`, then
    `|∑ P j g j - c| ≤ ((thr + 2B) + η (N e + thr + 2B)) / (N r₀)`. -/
theorem defect_from_bounds (N : ℕ) (hN : 0 < N) (Pt u g y : ℕ → ℝ) (c η r₀ thr B e : ℝ)
    (hPt : ∀ j, 0 ≤ Pt j) (hu : ∀ j, |u j - 1| ≤ η) (hη : 0 ≤ η) (hr₀ : 0 < r₀)
    (hr : r₀ ≤ ∑ l ∈ Finset.range N, Pt l * u l)
    (hy : ∀ j, y j = N * (Pt j * (g j - c))) (b i : ℕ) (he : 0 ≤ e)
    (H1 : |∑ j ∈ ((Finset.range N).erase b).erase i, y j| ≤ thr)
    (H2 : |∑ j ∈ ((Finset.range N).erase b).erase i, (|y j| - e)| ≤ thr)
    (hBb : |y b| ≤ B) (hBi : |y i| ≤ B) :
    |∑ j ∈ Finset.range N, Pt j * u j / (∑ l ∈ Finset.range N, Pt l * u l) * g j - c|
      ≤ ((thr + 2 * B) + η * (N * e + thr + 2 * B)) / (N * r₀) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrpos : 0 < ∑ l ∈ Finset.range N, Pt l * u l := lt_of_lt_of_le hr₀ hr
  have h := defect_split_range N Pt u g c η hPt hu hrpos
  have hS1 : |∑ j ∈ Finset.range N, Pt j * (g j - c)| ≤ (thr + 2 * B) / N := by
    have e1 : ∑ j ∈ Finset.range N, Pt j * (g j - c) = (∑ j ∈ Finset.range N, y j) / N := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hy j]; field_simp
    rw [e1, abs_div, abs_of_pos hNpos]
    apply div_le_div_of_nonneg_right _ hNpos.le
    have := abs_sum_le_erase2 (Finset.range N) y b i
    linarith
  have hA : ∑ j ∈ Finset.range N, Pt j * |g j - c| ≤ (N * e + thr + 2 * B) / N := by
    have e2 : ∑ j ∈ Finset.range N, Pt j * |g j - c| = (∑ j ∈ Finset.range N, |y j|) / N := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hy j, abs_mul, abs_mul, abs_of_pos hNpos, abs_of_nonneg (hPt j)]; field_simp
    rw [e2]
    apply div_le_div_of_nonneg_right _ hNpos.le
    have := sum_abs_le_erase2 (Finset.range N) y b i he
    rw [Finset.card_range] at this
    linarith
  have hthr : 0 ≤ thr := (abs_nonneg _).trans H1
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hBb
  have hnum : |∑ j ∈ Finset.range N, Pt j * (g j - c)|
        + η * ∑ j ∈ Finset.range N, Pt j * |g j - c|
      ≤ ((thr + 2 * B) + η * (N * e + thr + 2 * B)) / N := by
    have h1 := mul_le_mul_of_nonneg_left hA hη
    have e3 : ((thr + 2 * B) + η * (N * e + thr + 2 * B)) / N
        = (thr + 2 * B) / N + η * ((N * e + thr + 2 * B) / N) := by ring
    rw [e3]; linarith
  have hnum0 : 0 ≤ ((thr + 2 * B) + η * (N * e + thr + 2 * B)) / N := by positivity
  calc _ ≤ (|∑ j ∈ Finset.range N, Pt j * (g j - c)|
          + η * ∑ j ∈ Finset.range N, Pt j * |g j - c|)
        / (∑ l ∈ Finset.range N, Pt l * u l) := h
    _ ≤ (((thr + 2 * B) + η * (N * e + thr + 2 * B)) / N)
        / (∑ l ∈ Finset.range N, Pt l * u l) := div_le_div_of_nonneg_right hnum hrpos.le
    _ ≤ (((thr + 2 * B) + η * (N * e + thr + 2 * B)) / N) / r₀ :=
        div_le_div_of_nonneg_left hnum0 hr₀ hr
    _ = _ := by rw [div_div]

/-! ### The defect of the sampled walk on the good event -/

/-- The estimated normalisation at the `j`-th point: `ρ_j = (1/N) ∑_{l<N} p_σ(x_j - x_l)`. -/
noncomputable def heatRho (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (j : ℕ) : ℝ :=
  (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x l)) / N

/-- The one-step defect of the sampled walk: `h_m^{(i)}(b) = ∑_j P_{bj} p_m(x_j - x_i) - p_{m+1}(x_b - x_i)`,
    with the row `P_{bj} = (p_σ(x_b - x_j)/N)(1/ρ_j) / ∑_l (p_σ(x_b - x_l)/N)(1/ρ_l)` of the walk. -/
noncomputable def heatDefect (d : ℕ) (σ : ℝ) (N m : ℕ) (x : ℕ → FlatTorus d) (b i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N,
      (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / N) * (1 / heatRho d σ N x j)
        / (∑ l ∈ Finset.range N,
            (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (1 / heatRho d σ N x l))
        * heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (x j - x i)
    - heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)

/-- The bound for the defect on the good event, as a function of `u = x_b - x_i`. -/
noncomputable def heatDefBound (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ : ℝ) (u : FlatTorus d) : ℝ :=
  ((heatThr d σ ((m : ℝ) * σ) Mσ L N u + 2 * heatB d σ ((m : ℝ) * σ) Mσ u)
      + 2 * δ * (N * Real.sqrt (heatV d σ ((m : ℝ) * σ) u)
          + heatThr d σ ((m : ℝ) * σ) Mσ L N u + 2 * heatB d σ ((m : ℝ) * σ) Mσ u))
    / (N * (1 / 3))

/-- Inverse of a number close to one. -/
theorem inv_near_one {ρ δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hρ : |ρ - 1| ≤ δ) :
    |1 / ρ - 1| ≤ 2 * δ ∧ 2 / 3 ≤ 1 / ρ := by
  have h := abs_le.mp hρ
  have hρpos : 0 < ρ := by linarith [h.1]
  have e : 1 / ρ - 1 = (1 - ρ) / ρ := by field_simp
  constructor
  · rw [e, abs_div, abs_of_pos hρpos, div_le_iff₀ hρpos]
    have : |1 - ρ| ≤ δ := by rw [abs_sub_comm]; exact hρ
    nlinarith [h.1]
  · rw [le_div_iff₀ hρpos]; nlinarith [h.2]

/-- **The defect of the sampled walk on the good event (deterministic).** Points `x_0, …, x_{N-1}`
    of the flat torus, `m ≥ 1`. If the estimated normalisations are within `δ ≤ 1/2` of one and the
    two Bernstein bounds hold for the pair `(b, i)`, then
    `|h_m^{(i)}(b)| ≤ heatDefBound(x_b - x_i)`. -/
theorem heat_defect_det {σ : ℝ} (hσ : 0 < σ) (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m)
    (x : ℕ → FlatTorus d) (b i : ℕ) (hb : b ∈ Finset.range N) {Mσ L δ : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hρ : ∀ j, |heatRho d σ N x j - 1| ≤ δ)
    (H1 : |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
      ≤ heatThr d σ ((m : ℝ) * σ) Mσ L N (x b - x i))
    (H2 : |∑ j ∈ ((Finset.range N).erase b).erase i, heatYc d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
      ≤ heatThr d σ ((m : ℝ) * σ) Mσ L N (x b - x i)) :
    |heatDefect d σ N m x b i| ≤ heatDefBound d σ N m Mσ L δ (x b - x i) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hσs : σ ≤ (m : ℝ) * σ := by nlinarith
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  have hinv := fun j => inv_near_one hδ0 hδ (hρ j)
  have hPt : ∀ j, 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / N :=
    fun j => div_nonneg (heatTorus_nonneg hcσ d _) hNpos.le
  -- lower bound for the row normalisation
  have hr : (1 : ℝ) / 3 ≤ ∑ l ∈ Finset.range N,
      (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (1 / heatRho d σ N x l) := by
    have h1 : ∑ l ∈ Finset.range N, (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (2 / 3)
        ≤ ∑ l ∈ Finset.range N,
          (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (1 / heatRho d σ N x l) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hinv l).2 (hPt l)
    have h2 : ∑ l ∈ Finset.range N, (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (2 / 3)
        = heatRho d σ N x b * (2 / 3) := by
      unfold heatRho
      rw [← Finset.sum_mul, Finset.sum_div]
    have h3 := abs_le.mp (hρ b)
    nlinarith [h3.1]
  have hB := fun z => heatY_abs_le hσ hs d (x b) (x i) z hMσ
  have he := heatY_abs_integral_sharp hσ hs hσs d (x b) (x i)
  have he0 : 0 ≤ heatYmean d σ ((m : ℝ) * σ) (x b) (x i) := by
    rw [heatYmean_eq]; exact integral_nonneg fun z => abs_nonneg _
  have H2' : |∑ j ∈ ((Finset.range N).erase b).erase i,
      (|heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j)| - heatYmean d σ ((m : ℝ) * σ) (x b) (x i))|
      ≤ heatThr d σ ((m : ℝ) * σ) Mσ L N (x b - x i) := H2
  have key := defect_from_bounds N hN
    (fun j => heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / N)
    (fun j => 1 / heatRho d σ N x j)
    (fun j => heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (x j - x i))
    (fun j => heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j))
    (heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)) (2 * δ) (1 / 3)
    (heatThr d σ ((m : ℝ) * σ) Mσ L N (x b - x i)) (heatB d σ ((m : ℝ) * σ) Mσ (x b - x i))
    (heatYmean d σ ((m : ℝ) * σ) (x b) (x i))
    hPt (fun j => (hinv j).1) (by positivity) (by norm_num) hr
    (fun j => by unfold heatY; field_simp) b i he0 H1 H2' (hB _) (hB _)
  have hthr0 : 0 ≤ heatThr d σ ((m : ℝ) * σ) Mσ L N (x b - x i) := (abs_nonneg _).trans H1
  have hB0 : 0 ≤ heatB d σ ((m : ℝ) * σ) Mσ (x b - x i) :=
    (heatB_pos hσ hs hM d _).le
  rw [heatYmean_eq] at he0
  unfold heatDefect heatDefBound
  refine key.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmono : (N : ℝ) * heatYmean d σ ((m : ℝ) * σ) (x b) (x i)
      ≤ N * Real.sqrt (heatV d σ ((m : ℝ) * σ) (x b - x i)) := by
    rw [heatYmean_eq]; exact mul_le_mul_of_nonneg_left he hNpos.le
  nlinarith [mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 2 * δ)]

/-! ### The defect of the sampled walk with its probability -/

/-- **The one-step defect of the sampled walk on the torus, with its probability (estimate (ii) of
    the consistency lemma with explicit, time-dependent constants).** Independent uniform points
    on the flat torus; kernel time `σ`, `p_σ ≤ Mσ`, `L > 0`, `N > 0`. HYPOTHESIS `hBn`: the
    probability `pn` of the normalisation event (a conclusion of
    `uniform_concentration_bernstein`), with `epsn ≤ N/2`. Then, except on an event of probability
    at most `pn + 4 K N² e^{-L}`, for all `1 ≤ m ≤ K` and all `b, i < N`,
    `|h_m^{(i)}(b)| ≤ heatDefBound(X_b - X_i)` with `δ = epsn/N`. -/
theorem heat_defect_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {Mσ L epsn pn : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L)
    (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 2)
    (hBn : μ.real {ω | ∃ x : FlatTorus d,
        epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} ≤ pn) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatDefBound d σ N m Mσ L (epsn / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|}
      ≤ pn + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  set Bn : Set Ω := {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} with hBnd
  set E1 : Set Ω := {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
      2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
        + 2 * Real.sqrt (N * (Mσ * heatV d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
      ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} with hE1
  set E2 : Set Ω := {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
      heatThr d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω)
      ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} with hE2
  have hP1 : μ.real E1 ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) :=
    heat_consistency_all_steps hσ d X h_indep hX hlaw N K hMσ hL
  have hP2 : μ.real E2 ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) :=
    heat_abs_consistency_all_steps hσ d X h_indep hX hlaw N K hMσ hL
  have hsub : {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatDefBound d σ N m Mσ L (epsn / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|}
      ⊆ Bn ∪ (E1 ∪ E2) := by
    rintro ω ⟨m, hm, b, hb, i, hi, hbad⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hn, h1, h2⟩ := hcon
    have hρ : ∀ j, |heatRho d σ N (fun j => X j ω) j - 1| ≤ epsn / N := by
      intro j
      have h : |∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N|
          ≤ epsn := by
        by_contra h; exact hn ⟨X j ω, not_le.mp h⟩
      have e : heatRho d σ N (fun j => X j ω) j - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    have H1 : |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|
        ≤ heatThr d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω) := by
      by_contra h
      exact h1 ⟨m, hm, b, hb, i, hi, (not_le.mp h).le⟩
    have H2 : |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|
        ≤ heatThr d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω) := by
      by_contra h
      exact h2 ⟨m, hm, b, hb, i, hi, (not_le.mp h).le⟩
    have hdet := heat_defect_det hσ d N m hN (Finset.mem_Icc.mp hm).1 (fun j => X j ω) b i hb hMσ hL
      (div_nonneg hepsn0 hNpos.le) (by rw [div_le_iff₀ hNpos]; linarith) hρ H1 H2
    exact absurd hbad (not_lt.mpr hdet)
  calc μ.real _ ≤ μ.real (Bn ∪ (E1 ∪ E2)) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real Bn + μ.real (E1 ∪ E2) := measureReal_union_le _ _
    _ ≤ μ.real Bn + (μ.real E1 + μ.real E2) := by
        have := measureReal_union_le (μ := μ) E1 E2
        linarith
    _ ≤ _ := by linarith

/-! ### Estimate (ii) of the consistency lemma for random samples -/

/-- **The normalisation event on the torus, with its probability.** Independent uniform points,
    kernel `p_σ ≤ M` with Lipschitz constant `Lip`, grid parameter `g > 0`:
    `P(∃ x, |∑_{j<N} p_σ(x - X_j) - N| > eps + 2 N Lip / g) ≤ 2 g^d exp(-eps² / (4 N M + 2 M eps))`. -/
theorem heat_normalisation_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ) {g : ℕ} (hg : 0 < g) {M Lip ε : ℝ}
    (hM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M)
    (hLip : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u - heatTorus d (2 * Real.pi ^ 2 * σ) u'|
      ≤ Lip * dist u u') (hLip0 : 0 ≤ Lip) (hε : 0 < ε) :
    μ.real {ω | ∃ x : FlatTorus d, ε + 2 * (N * Lip) * (1 / g)
        < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM0 : 0 < M := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hM 0)
  have hcont := heatTorus_continuous hcσ d
  have h := uniform_concentration_bernstein (μ := μ) (T := FlatTorus d) X h_indep hX
    (fun x y => heatTorus d (2 * Real.pi ^ 2 * σ) (x - y))
    (fun x => hcont.measurable.comp (measurable_const.sub measurable_id)) hM0 hLip0
    (fun x y => ⟨heatTorus_nonneg hcσ d _, hM _⟩)
    (fun x x' y => by have := hLip (x - y) (x' - y); rwa [dist_sub_right] at this)
    (fun _ => 1)
    (fun x j => by
      have h1 : ∫ ω, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) ∂μ
          = ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) (x - y) ∂(μ.map (X j)) :=
        (integral_map (hX j).aemeasurable
          ((hcont.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)).symm
      rw [h1, hlaw j, integral_sub_left_eq_self (heatTorus d (2 * Real.pi ^ 2 * σ))
        (flatTorusMeasure d) x, heatTorus_mass hcσ d])
    (qmax := 1) (fun _ => le_rfl)
    (fun x x' => by simpa using mul_nonneg hLip0 dist_nonneg)
    (torusNet d g) (torusNet_dense d hg) N hε
  simp only [mul_one] at h
  have hc : ((torusNet d g).card : ℝ) ≤ (g : ℝ) ^ d := by exact_mod_cast torusNet_card d g
  exact h.trans (mul_le_mul_of_nonneg_right hc (by positivity))

/-- **Estimate (ii) of the consistency lemma for random samples on the torus, with explicit
    time-dependent constants and no hypothesis beyond those on the sample.** With
    `M = (1 + √(π/c_σ))^d`, the Lipschitz constant `Lip` of the kernel and a grid parameter `g`:
    except on an event of probability at most
    `2 g^d exp(-eps²/(4NM + 2M eps)) + 4 K N² e^{-L}`, for all `1 ≤ m ≤ K` and `b, i < N`,
    `|h_m^{(i)}(b)| ≤ heatDefBound(X_b - X_i)` with `δ = (eps + 2 N Lip / g)/N`. -/
theorem heat_defect_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 2) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatDefBound d σ N m M L ((ε + 2 * (N * Lip) * (1 / g)) / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M := fun u => by
    rw [hMdef]; exact heatTorus_le hcσ d u
  have hLip : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u
      - heatTorus d (2 * Real.pi ^ 2 * σ) u'| ≤ Lip * dist u u' := fun u u' => by
    rw [hLipdef]; exact heatTorus_lipschitz hcσ d u u'
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hBn := heat_normalisation_whp hσ d X h_indep hX hlaw N hg hM hLip hLip0 hε
  exact heat_defect_whp hσ d X h_indep hX hlaw N K hN hM hL (by positivity) hsmall hBn

/-! ### The defect in matrix form -/

section WalkDefect
open Matrix

/-- **The defect in matrix form.** For points `x_0, …, x_{N-1}` with nonzero estimated
    normalisations, the walk matrix `P` of the sampled graph applied to the kernel vector
    `b' ↦ p_m(x_{b'} - x_i)`, minus `p_{m+1}(x_b - x_i)`, is the defect `heatDefect`. -/
theorem walk_defect_eq (d : ℕ) (σ : ℝ) (N m : ℕ) (hN : 0 < N) (x : ℕ → FlatTorus d)
    (hρ : ∀ j, heatRho d σ N x j ≠ 0) (b i : Fin N) :
    ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
          (fun a : Fin N => heatRho d σ N x a))
        *ᵥ (fun b' : Fin N => heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (x b' - x i))) b
      - heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
      = heatDefect d σ N m x b i := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold heatDefect
  congr 1
  simp only [mulVec, dotProduct]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / N * (1 / heatRho d σ N x j)
      / (∑ l ∈ Finset.range N,
          heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N * (1 / heatRho d σ N x l))
      * heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (x j - x i)) N]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [walkMatrix_apply' _ _ b j (hρ b)]
  congr 1
  have hsum : ∑ l ∈ Finset.range N,
        heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N * (1 / heatRho d σ N x l)
      = (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / heatRho d σ N x l) / N := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N * (1 / heatRho d σ N x l)) N,
      Finset.sum_div]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hsum]
  have hj := hρ j
  field_simp

end WalkDefect

/-! ### The defect bound in the supremum -/

/-- The uniform bound of the heat kernel of the torus at parameter `c`. -/
noncomputable def heatM (d : ℕ) (c : ℝ) : ℝ := (1 + Real.sqrt (Real.pi / c)) ^ d

/-- Nonnegativity of the uniform bound. -/
theorem heatM_nonneg (d : ℕ) (c : ℝ) : 0 ≤ heatM d c := by unfold heatM; positivity

/-- The kernel is at most its uniform bound. -/
theorem heatTorus_le_heatM {c : ℝ} (hc : 0 < c) (d : ℕ) (u : FlatTorus d) :
    heatTorus d c u ≤ heatM d c := heatTorus_le hc d u

/-- Supremum version of the bound `B`. -/
noncomputable def heatBsup (d : ℕ) (σ s Mσ : ℝ) : ℝ :=
  (1 / (2 * Real.pi * σ) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * s) ^ (1 / 2 : ℝ))
        * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)) ^ d
      * heatM d (2 * Real.pi ^ 2 * (s + 2 * σ))
      / (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d
    + Mσ * heatM d (2 * Real.pi ^ 2 * (σ + s))

/-- Supremum version of the variance bound `V`. -/
noncomputable def heatVsup (d : ℕ) (σ s : ℝ) : ℝ :=
  (d : ℝ) * (σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * (2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ)))
    * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
      * ((2 * Real.pi ^ 2 * (6 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)) ^ (d - 1)
    * heatM d (2 * Real.pi ^ 2 * (6 * s))

/-- `B(u)` is at most its supremum version. -/
theorem heatB_le_sup {σ s Mσ : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hM : 0 ≤ Mσ) (d : ℕ)
    (u : FlatTorus d) : heatB d σ s Mσ u ≤ heatBsup d σ s Mσ := by
  unfold heatB heatBsup
  have hpi := Real.pi_pos
  have h1 := heatTorus_le_heatM (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (s + 2 * σ)) d u
  have h2 := heatTorus_le_heatM (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (σ + s)) d u
  have hK : 0 ≤ (1 / (2 * Real.pi * σ) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * s) ^ (1 / 2 : ℝ))
        * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)) ^ d := by positivity
  have hpre : 0 < (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d := by positivity
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 hM)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hK) hpre.le

/-- `V(u)` is at most its supremum version. -/
theorem heatV_le_sup {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (u : FlatTorus d) :
    heatV d σ s u ≤ heatVsup d σ s := by
  unfold heatV heatVsup
  have hpi := Real.pi_pos
  have h1 := heatTorus_le_heatM (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * s)) d u
  refine mul_le_mul_of_nonneg_left h1 ?_
  positivity

/-- Nonnegativity of the supremum version of `V`. -/
theorem heatVsup_nonneg {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) : 0 ≤ heatVsup d σ s := by
  unfold heatVsup
  have hpi := Real.pi_pos
  have := heatM_nonneg d (2 * Real.pi ^ 2 * (6 * s))
  positivity

/-- Supremum version of the threshold. -/
noncomputable def heatThrSup (d : ℕ) (σ s Mσ L A : ℝ) : ℝ :=
  2 * heatBsup d σ s Mσ * L + 2 * Real.sqrt (A * (Mσ * heatVsup d σ s) * L)

/-- The threshold is at most its supremum version. -/
theorem heatThr_le_sup {σ s Mσ L A : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hM : 0 ≤ Mσ) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (d : ℕ) (u : FlatTorus d) :
    heatThr d σ s Mσ L A u ≤ heatThrSup d σ s Mσ L A := by
  unfold heatThr heatThrSup
  have h1 := heatB_le_sup hσ hs hM d u
  have h2 := heatV_le_sup hσ hs d u
  have h3 : A * (Mσ * heatV d σ s u) * L ≤ A * (Mσ * heatVsup d σ s) * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hM) hA) hL
  have h4 := Real.sqrt_le_sqrt h3
  nlinarith [mul_le_mul_of_nonneg_right h1 hL]

/-- Supremum version of the bound for the defect. -/
noncomputable def heatDefSup (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ : ℝ) : ℝ :=
  ((heatThrSup d σ ((m : ℝ) * σ) Mσ L N + 2 * heatBsup d σ ((m : ℝ) * σ) Mσ)
      + 2 * δ * (N * Real.sqrt (heatVsup d σ ((m : ℝ) * σ))
          + heatThrSup d σ ((m : ℝ) * σ) Mσ L N + 2 * heatBsup d σ ((m : ℝ) * σ) Mσ))
    / (N * (1 / 3))

/-- **The defect bound in the supremum.** `heatDefBound(u) ≤ heatDefSup` for all `u`. -/
theorem heatDefBound_le_sup {σ Mσ L δ : ℝ} (hσ : 0 < σ) (hM : 0 ≤ Mσ) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m) (u : FlatTorus d) :
    heatDefBound d σ N m Mσ L δ u ≤ heatDefSup d σ N m Mσ L δ := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < (m : ℝ) * σ := by positivity
  unfold heatDefBound heatDefSup
  have h1 := heatThr_le_sup hσ hs hM hL hNpos.le d u
  have h2 := heatB_le_sup hσ hs hM d u
  have h3 := heatV_le_sup hσ hs d u
  have h4 : Real.sqrt (heatV d σ ((m : ℝ) * σ) u)
      ≤ Real.sqrt (heatVsup d σ ((m : ℝ) * σ)) :=
    Real.sqrt_le_sqrt h3
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h5 : (N : ℝ) * Real.sqrt (heatV d σ ((m : ℝ) * σ) u)
      ≤ N * Real.sqrt (heatVsup d σ ((m : ℝ) * σ)) :=
    mul_le_mul_of_nonneg_left h4 hNpos.le
  have h6 : 2 * δ * (N * Real.sqrt (heatV d σ ((m : ℝ) * σ) u)
        + heatThr d σ ((m : ℝ) * σ) Mσ L N u + 2 * heatB d σ ((m : ℝ) * σ) Mσ u)
      ≤ 2 * δ * (N * Real.sqrt (heatVsup d σ ((m : ℝ) * σ))
        + heatThrSup d σ ((m : ℝ) * σ) Mσ L N + 2 * heatBsup d σ ((m : ℝ) * σ) Mσ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-! ### The defect bound as a linear function of three kernel quantities -/

/-- Coefficient of `p_{s+2σ}` in the bound `B`. -/
noncomputable def heatKB (d : ℕ) (σ s : ℝ) : ℝ :=
  (1 / (2 * Real.pi * σ) ^ (1 / 2 : ℝ) * (1 / (2 * Real.pi * s) ^ (1 / 2 : ℝ))
        * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)) ^ d
    / (1 / (2 * Real.pi * (s + 2 * σ)) ^ (1 / 2 : ℝ)) ^ d

/-- Coefficient of `p_{6s}` in the variance bound `V`. -/
noncomputable def heatCV (d : ℕ) (σ s : ℝ) : ℝ :=
  (d : ℝ) * (σ / s * (4 / (Real.pi * s)) * ((1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * (2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ)))
    * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
      * ((2 * Real.pi ^ 2 * (6 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)) ^ (d - 1)

/-- Nonnegativity of the coefficient. -/
theorem heatKB_nonneg {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) : 0 ≤ heatKB d σ s := by
  unfold heatKB
  have hpi := Real.pi_pos
  positivity

/-- Nonnegativity of the coefficient. -/
theorem heatCV_nonneg {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) : 0 ≤ heatCV d σ s := by
  unfold heatCV
  have hpi := Real.pi_pos
  positivity

/-- `B` in terms of its coefficients. -/
theorem heatB_eq (d : ℕ) (σ s Mσ : ℝ) (u : FlatTorus d) :
    heatB d σ s Mσ u = heatKB d σ s * heatTorus d (2 * Real.pi ^ 2 * (s + 2 * σ)) u
      + Mσ * heatTorus d (2 * Real.pi ^ 2 * (σ + s)) u := by
  unfold heatB heatKB
  ring

/-- `V` in terms of its coefficient. -/
theorem heatV_eq (d : ℕ) (σ s : ℝ) (u : FlatTorus d) :
    heatV d σ s u = heatCV d σ s * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u := by
  unfold heatV heatCV
  ring

/-- The defect bound as a function of three numbers `pa, pb, q` standing for `p_{s+2σ}(u)`,
    `p_{σ+s}(u)` and `√(p_{6s}(u))`; it is linear in them with nonnegative coefficients. -/
noncomputable def heatDefNum (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ pa pb q : ℝ) : ℝ :=
  (((2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb) * L
        + 2 * (Real.sqrt (N * (Mσ * heatCV d σ ((m : ℝ) * σ)) * L) * q))
      + 2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb))
    + 2 * δ * (N * (Real.sqrt (heatCV d σ ((m : ℝ) * σ)) * q)
        + (2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb) * L
          + 2 * (Real.sqrt (N * (Mσ * heatCV d σ ((m : ℝ) * σ)) * L) * q))
        + 2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb)))
    / (N * (1 / 3))

/-- Additivity. -/
theorem heatDefNum_add (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ pa pb q pa' pb' q' : ℝ) :
    heatDefNum d σ N m Mσ L δ (pa + pa') (pb + pb') (q + q')
      = heatDefNum d σ N m Mσ L δ pa pb q + heatDefNum d σ N m Mσ L δ pa' pb' q' := by
  unfold heatDefNum
  ring

/-- Value at zero. -/
theorem heatDefNum_zero (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ : ℝ) :
    heatDefNum d σ N m Mσ L δ 0 0 0 = 0 := by
  unfold heatDefNum
  simp

/-- Nonnegativity for nonnegative arguments. -/
theorem heatDefNum_nonneg {σ Mσ L δ pa pb q : ℝ} (hσ : 0 < σ) (hM : 0 ≤ Mσ) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (d N m : ℕ) (hm : 1 ≤ m) (ha : 0 ≤ pa) (hb : 0 ≤ pb) (hq : 0 ≤ q) :
    0 ≤ heatDefNum d σ N m Mσ L δ pa pb q := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hK := heatKB_nonneg hσ hs d
  unfold heatDefNum
  positivity

/-- Monotonicity in the three arguments. -/
theorem heatDefNum_mono {σ Mσ L δ pa pb q pa' pb' q' : ℝ} (hσ : 0 < σ) (hM : 0 ≤ Mσ)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (d N m : ℕ) (hm : 1 ≤ m) (ha : pa ≤ pa') (hb : pb ≤ pb')
    (hq : q ≤ q') :
    heatDefNum d σ N m Mσ L δ pa pb q ≤ heatDefNum d σ N m Mσ L δ pa' pb' q' := by
  have h := heatDefNum_add d σ N m Mσ L δ pa pb q (pa' - pa) (pb' - pb) (q' - q)
  have e1 : pa + (pa' - pa) = pa' := by ring
  have e2 : pb + (pb' - pb) = pb' := by ring
  have e3 : q + (q' - q) = q' := by ring
  rw [e1, e2, e3] at h
  have := heatDefNum_nonneg hσ hM hL hδ d N m hm (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
    (sub_nonneg.mpr hq)
  linarith

/-- Compatibility with finite sums. -/
theorem heatDefNum_sum (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ : ℝ) {ι : Type*} (S : Finset ι)
    (pa pb q : ι → ℝ) :
    ∑ b ∈ S, heatDefNum d σ N m Mσ L δ (pa b) (pb b) (q b)
      = heatDefNum d σ N m Mσ L δ (∑ b ∈ S, pa b) (∑ b ∈ S, pb b) (∑ b ∈ S, q b) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [heatDefNum_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih,
      ← heatDefNum_add]

/-- The defect bound at a point is the numeric function at the three kernel quantities. -/
theorem heatDefBound_eq_num {σ Mσ L : ℝ} (hσ : 0 < σ) (hM : 0 ≤ Mσ) (hL : 0 ≤ L) (d N m : ℕ)
    (hm : 1 ≤ m) (δ : ℝ) (u : FlatTorus d) :
    heatDefBound d σ N m Mσ L δ u
      = heatDefNum d σ N m Mσ L δ
          (heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) u)
          (heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) u)
          (Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hC := heatCV_nonneg hσ hs d
  have hp6 := heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) d u
  have e1 : Real.sqrt (N * (Mσ * (heatCV d σ ((m : ℝ) * σ)
        * heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u)) * L)
      = Real.sqrt (N * (Mσ * heatCV d σ ((m : ℝ) * σ)) * L)
        * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; ring
  have e2 : Real.sqrt (heatCV d σ ((m : ℝ) * σ)
        * heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u)
      = Real.sqrt (heatCV d σ ((m : ℝ) * σ))
        * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u) :=
    Real.sqrt_mul hC _
  unfold heatDefBound heatThr heatDefNum
  rw [heatB_eq, heatV_eq, e1, e2]

/-- Cauchy–Schwarz for a sum of square roots: `∑_{b ∈ S} √(a b) ≤ √(|S| ∑ a b)` for `a ≥ 0`. -/
theorem sum_sqrt_le {ι : Type*} (S : Finset ι) (a : ι → ℝ) (ha : ∀ b, 0 ≤ a b) :
    ∑ b ∈ S, Real.sqrt (a b) ≤ Real.sqrt (S.card * ∑ b ∈ S, a b) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun b => Real.sqrt (a b))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have h2 : ∑ b ∈ S, Real.sqrt (a b) ^ 2 = ∑ b ∈ S, a b :=
    Finset.sum_congr rfl fun b _ => Real.sq_sqrt (ha b)
  rw [h2] at h
  have hnn : 0 ≤ ∑ b ∈ S, Real.sqrt (a b) := Finset.sum_nonneg fun b _ => Real.sqrt_nonneg _
  calc ∑ b ∈ S, Real.sqrt (a b) = Real.sqrt ((∑ b ∈ S, Real.sqrt (a b)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (S.card * ∑ b ∈ S, a b) := Real.sqrt_le_sqrt h

/-- **The defect bound in the mean over the points (deterministic).** If the sums of the three
    kernels over the points `x_b`, `b < N`, at `x_b - x_i` are at most `N (1 + δ_a)`, `N (1 + δ_b)`,
    `N (1 + δ_c)` (estimate (iii) of the consistency lemma at the three times), then
    `∑_{b<N} heatDefBound(x_b - x_i) ≤ heatDefNum(N(1+δ_a), N(1+δ_b), N √(1+δ_c))`. -/
theorem heat_defect_mean_det {σ Mσ L δ δa δb δc : ℝ} (hσ : 0 < σ) (hM : 0 ≤ Mσ) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (d N m : ℕ) (hm : 1 ≤ m) (x : ℕ → FlatTorus d) (i : ℕ) (hδc : 0 ≤ δc)
    (hA : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) (x b - x i)
      ≤ N * (1 + δa))
    (hB : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
      ≤ N * (1 + δb))
    (hC : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
      ≤ N * (1 + δc)) :
    ∑ b ∈ Finset.range N, heatDefBound d σ N m Mσ L δ (x b - x i)
      ≤ heatDefNum d σ N m Mσ L δ (N * (1 + δa)) (N * (1 + δb)) (N * Real.sqrt (1 + δc)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc6 : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)) := by positivity
  simp_rw [heatDefBound_eq_num hσ hM hL d N m hm δ]
  rw [heatDefNum_sum]
  refine heatDefNum_mono hσ hM hL hδ d N m hm hA hB ?_
  have h1 := sum_sqrt_le (Finset.range N)
    (fun b => heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i))
    (fun b => heatTorus_nonneg hc6 d _)
  rw [Finset.card_range] at h1
  refine h1.trans ?_
  have h2 : (N : ℝ) * ∑ b ∈ Finset.range N,
        heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
      ≤ (N : ℝ) ^ 2 * (1 + δc) := by
    have := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg N)
    nlinarith
  calc Real.sqrt ((N : ℝ) * ∑ b ∈ Finset.range N,
          heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i))
      ≤ Real.sqrt ((N : ℝ) ^ 2 * (1 + δc)) := Real.sqrt_le_sqrt h2
    _ = N * Real.sqrt (1 + δc) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg N)]

/-- The factor in `√(p_c) ≤ heatQ · p_{2c}` (core of (P5)); it is of the order `c^{d/4}`. -/
noncomputable def heatQ (d : ℕ) (c : ℝ) : ℝ :=
  (Real.sqrt (1 / (c / Real.pi) ^ (1 / 2 : ℝ)) / (1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ))) ^ d

theorem heatQ_nonneg {c : ℝ} (hc : 0 < c) (d : ℕ) : 0 ≤ heatQ d c := by
  unfold heatQ
  have hpi := Real.pi_pos
  positivity

/-- Core of (P5) solved for the square root: `√(p_c(z)) ≤ heatQ(c) p_{2c}(z)`. -/
theorem heatTorus_sqrt_le {c : ℝ} (hc : 0 < c) (d : ℕ) (z : FlatTorus d) :
    Real.sqrt (heatTorus d c z) ≤ heatQ d c * heatTorus d (2 * c) z := by
  have h := heatTorus_sqrt hc d z
  have hpi := Real.pi_pos
  have hA : 0 < (1 / (2 * c / Real.pi) ^ (1 / 2 : ℝ)) ^ d := by positivity
  unfold heatQ
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hA]
  exact h

/-- The bound for the mean of the defect at step `m`: the defect bound as a function of the means
    of the three kernel quantities, where the mean of `√(p_{6s})` is bounded both by
    Cauchy–Schwarz and through (P5) by the mean of `p_{12s}`. -/
noncomputable def heatEtaBar (d : ℕ) (σ : ℝ) (N m : ℕ) (M L δ δ3 : ℝ) : ℝ :=
  heatDefNum d σ N m M L δ (N * (1 + δ3)) (N * (1 + δ3))
    (min (N * Real.sqrt (1 + δ3))
      (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ3)))) / N

/-- **The defect bound in the mean over the points, with (P5).** As `heat_defect_mean_det`, with the
    additional estimate (iii) at the time `12mσ`; the sum of the defect bounds is at most
    `N · heatEtaBar`. -/
theorem heat_defect_mean_det_min {σ Mσ L δ δ3 : ℝ} (hσ : 0 < σ) (hM : 0 ≤ Mσ) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m) (x : ℕ → FlatTorus d) (i : ℕ)
    (hδ3 : 0 ≤ δ3)
    (hA : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) (x b - x i)
      ≤ N * (1 + δ3))
    (hB : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
      ≤ N * (1 + δ3))
    (hC : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
      ≤ N * (1 + δ3))
    (hC12 : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i)
      ≤ N * (1 + δ3)) :
    ∑ b ∈ Finset.range N, heatDefBound d σ N m Mσ L δ (x b - x i)
      ≤ N * heatEtaBar d σ N m Mσ L δ δ3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc6 : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)) := by positivity
  unfold heatEtaBar
  rw [mul_div_cancel₀ _ hNpos.ne']
  simp_rw [heatDefBound_eq_num hσ hM hL d N m hm δ]
  rw [heatDefNum_sum]
  refine heatDefNum_mono hσ hM hL hδ d N m hm hA hB (le_min ?_ ?_)
  · have h1 := sum_sqrt_le (Finset.range N)
      (fun b => heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i))
      (fun b => heatTorus_nonneg hc6 d _)
    rw [Finset.card_range] at h1
    refine h1.trans ?_
    have h2 : (N : ℝ) * ∑ b ∈ Finset.range N,
          heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
        ≤ (N : ℝ) ^ 2 * (1 + δ3) := by
      have := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg N)
      nlinarith
    calc Real.sqrt ((N : ℝ) * ∑ b ∈ Finset.range N,
            heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i))
        ≤ Real.sqrt ((N : ℝ) ^ 2 * (1 + δ3)) := Real.sqrt_le_sqrt h2
      _ = N * Real.sqrt (1 + δ3) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Nat.cast_nonneg N)]
  · have e12 : 2 * (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)))
        = 2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ)) := by ring
    calc ∑ b ∈ Finset.range N,
          Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i))
        ≤ ∑ b ∈ Finset.range N, heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)))
            * heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i) :=
          Finset.sum_le_sum fun b _ => by
            have := heatTorus_sqrt_le hc6 d (x b - x i)
            rwa [e12] at this
      _ = heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)))
            * ∑ b ∈ Finset.range N,
              heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hC12 (heatQ_nonneg hc6 d)

/-- **The last step of the walk (Step 2 of the kernel theorem), for the walk matrix itself.**
    If the estimated normalisations `ρ_a = (∑_l K_{al})/N` satisfy `|ρ_a - 1| ≤ δ ≤ 1/8`, then
    `|N P_{bi} - K_{bi}| ≤ 4 δ K_{bi}` for the walk matrix `P` of the kernel matrix `K ≥ 0`. -/
theorem walk_last_step {n : Type} [Fintype n] [Nonempty n] (K : n → n → ℝ) (ρ : n → ℝ) {δ : ℝ}
    (hK : ∀ a j, 0 ≤ K a j) (hsum : ∀ a, ∑ l, K a l = (Fintype.card n : ℝ) * ρ a)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hρ : ∀ a, |ρ a - 1| ≤ δ) (b i : n) :
    |(Fintype.card n : ℝ) * walkMatrix K ρ b i - K b i| ≤ 4 * δ * K b i := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hρb := fun a => abs_le.mp (hρ a)
  have hρpos : ∀ a, 0 < ρ a := fun a => by linarith [(hρb a).1]
  obtain ⟨S, hSdef⟩ : ∃ S, S = ∑ l, K b l / ρ l := ⟨_, rfl⟩
  have hS1 : (Fintype.card n : ℝ) * (1 - δ) ≤ S * (1 + δ) := by
    calc (Fintype.card n : ℝ) * (1 - δ) ≤ (Fintype.card n : ℝ) * ρ b :=
          mul_le_mul_of_nonneg_left (by linarith [(hρb b).1]) hN.le
      _ = ∑ l, K b l := (hsum b).symm
      _ ≤ ∑ l, K b l / ρ l * (1 + δ) := Finset.sum_le_sum fun l _ => by
          rw [div_mul_eq_mul_div, le_div_iff₀ (hρpos l)]
          exact mul_le_mul_of_nonneg_left (by linarith [(hρb l).2]) (hK b l)
      _ = S * (1 + δ) := by rw [hSdef, Finset.sum_mul]
  have hS2 : S * (1 - δ) ≤ (Fintype.card n : ℝ) * (1 + δ) := by
    calc S * (1 - δ) = ∑ l, K b l / ρ l * (1 - δ) := by rw [hSdef, Finset.sum_mul]
      _ ≤ ∑ l, K b l := Finset.sum_le_sum fun l _ => by
          rw [div_mul_eq_mul_div, div_le_iff₀ (hρpos l)]
          exact mul_le_mul_of_nonneg_left (by linarith [(hρb l).1]) (hK b l)
      _ = (Fintype.card n : ℝ) * ρ b := hsum b
      _ ≤ (Fintype.card n : ℝ) * (1 + δ) :=
          mul_le_mul_of_nonneg_left (by linarith [(hρb b).2]) hN.le
  have hSpos : 0 < S := by
    have h1 : 0 < S * (1 + δ) := lt_of_lt_of_le (mul_pos hN (by linarith)) hS1
    exact (mul_pos_iff_of_pos_right (by linarith)).mp h1
  obtain ⟨u, hudef⟩ : ∃ u, u = 1 / ρ i := ⟨_, rfl⟩
  have hu1 : 1 ≤ u * (1 + δ) := by
    rw [hudef, one_div_mul_eq_div, le_div_iff₀ (hρpos i)]; linarith [(hρb i).2]
  have hu2 : u * (1 - δ) ≤ 1 := by
    rw [hudef, one_div_mul_eq_div, div_le_iff₀ (hρpos i)]; linarith [(hρb i).1]
  have hP : (Fintype.card n : ℝ) * walkMatrix K ρ b i - K b i
      = K b i * (((Fintype.card n : ℝ) * u - S) / S) := by
    rw [walkMatrix_apply' K ρ b i (hρpos b).ne', ← hSdef, hudef]
    have := hρpos i
    field_simp
  have hpos2 : 0 < (1 - δ) * (1 + δ) := mul_pos (by linarith) (by linarith)
  -- upper bound: N u ≤ (1 + 4δ) S
  have hup : (Fintype.card n : ℝ) * u ≤ (1 + 4 * δ) * S := by
    refine le_of_mul_le_mul_right ?_ hpos2
    have a1 : (Fintype.card n : ℝ) * u * ((1 - δ) * (1 + δ)) ≤ (Fintype.card n : ℝ) * (1 + δ) := by
      have := mul_le_mul_of_nonneg_left hu2 (mul_nonneg hN.le (by linarith : (0 : ℝ) ≤ 1 + δ))
      nlinarith
    have a2 : (Fintype.card n : ℝ) * (1 + δ)
        ≤ (1 + 4 * δ) * (1 - δ) * ((Fintype.card n : ℝ) * (1 - δ)) := by
      have hpoly : 0 ≤ δ * (1 - 7 * δ + 4 * δ ^ 2) :=
        mul_nonneg hδ0 (by nlinarith [_root_.sq_nonneg δ])
      nlinarith [mul_nonneg hN.le hpoly]
    have a3 : (1 + 4 * δ) * (1 - δ) * ((Fintype.card n : ℝ) * (1 - δ))
        ≤ (1 + 4 * δ) * (1 - δ) * (S * (1 + δ)) :=
      mul_le_mul_of_nonneg_left hS1 (mul_nonneg (by linarith) (by linarith))
    calc (Fintype.card n : ℝ) * u * ((1 - δ) * (1 + δ)) ≤ (Fintype.card n : ℝ) * (1 + δ) := a1
      _ ≤ _ := a2
      _ ≤ _ := a3
      _ = (1 + 4 * δ) * S * ((1 - δ) * (1 + δ)) := by ring
  -- lower bound: (1 - 4δ) S ≤ N u
  have hlow : (1 - 4 * δ) * S ≤ (Fintype.card n : ℝ) * u := by
    refine le_of_mul_le_mul_right ?_ hpos2
    have b1 : (1 - 4 * δ) * (1 + δ) * (S * (1 - δ))
        ≤ (1 - 4 * δ) * (1 + δ) * ((Fintype.card n : ℝ) * (1 + δ)) :=
      mul_le_mul_of_nonneg_left hS2 (mul_nonneg (by linarith) (by linarith))
    have b2 : (1 - 4 * δ) * (1 + δ) * ((Fintype.card n : ℝ) * (1 + δ))
        ≤ (Fintype.card n : ℝ) * (1 - δ) := by
      have hpoly : 0 ≤ δ * (1 + 7 * δ + 4 * δ ^ 2) :=
        mul_nonneg hδ0 (by nlinarith [_root_.sq_nonneg δ])
      nlinarith [mul_nonneg hN.le hpoly]
    have b3 : (Fintype.card n : ℝ) * (1 - δ)
        ≤ (Fintype.card n : ℝ) * u * ((1 - δ) * (1 + δ)) := by
      have := mul_le_mul_of_nonneg_left hu1 (mul_nonneg hN.le (by linarith : (0 : ℝ) ≤ 1 - δ))
      nlinarith
    calc (1 - 4 * δ) * S * ((1 - δ) * (1 + δ)) = (1 - 4 * δ) * (1 + δ) * (S * (1 - δ)) := by ring
      _ ≤ _ := b1
      _ ≤ _ := b2
      _ ≤ _ := b3
  rw [hP, abs_mul, abs_of_nonneg (hK b i), mul_comm (4 * δ)]
  refine mul_le_mul_of_nonneg_left ?_ (hK b i)
  rw [abs_div, abs_of_pos hSpos, div_le_iff₀ hSpos, abs_le]
  constructor <;> linarith

/-- The heat kernel after `k` steps of size `σ` (zero for `k = 0`, a convention). -/
noncomputable def heatP (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : ℝ :=
  if k = 0 then 0 else heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) u

/-- The uniform bound of the heat kernel after `k` steps (zero for `k = 0`). -/
noncomputable def heatMu (d : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else heatM d (2 * Real.pi ^ 2 * ((k : ℝ) * σ))

theorem heatP_of_ne (d : ℕ) (σ : ℝ) {k : ℕ} (hk : k ≠ 0) (u : FlatTorus d) :
    heatP d σ k u = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) u := by
  simp [heatP, hk]

theorem heatP_succ (d : ℕ) (σ : ℝ) (m : ℕ) (u : FlatTorus d) :
    heatP d σ (m + 1) u = heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) u := by
  rw [heatP_of_ne d σ (Nat.succ_ne_zero m)]
  congr 2
  push_cast
  ring

theorem heatP_one (d : ℕ) (σ : ℝ) (u : FlatTorus d) :
    heatP d σ 1 u = heatTorus d (2 * Real.pi ^ 2 * σ) u := by
  rw [heatP_of_ne d σ one_ne_zero]
  simp

theorem heatMu_nonneg (d : ℕ) (σ : ℝ) (k : ℕ) : 0 ≤ heatMu d σ k := by
  unfold heatMu
  split_ifs
  · exact le_rfl
  · exact heatM_nonneg d _

theorem heatP_nonneg {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (u : FlatTorus d) : 0 ≤ heatP d σ k u := by
  unfold heatP
  split_ifs with hk
  · exact le_rfl
  · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    exact heatTorus_nonneg (by positivity) d u

theorem heatP_le_mu {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (u : FlatTorus d) :
    heatP d σ k u ≤ heatMu d σ k := by
  unfold heatP heatMu
  split_ifs with hk
  · exact le_rfl
  · have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    exact heatTorus_le_heatM (by positivity) d u

section KernelMin
open Matrix

/-- Step 3 of the proof of Theorem "kernel" with an arbitrary bound `t m` for each transported
    defect `P^{j-m} h_m`. -/
theorem lax_kernel_bound_terms {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (g : ℕ → n → ℝ) (t : ℕ → ℝ) (hs : ℝ) (j : ℕ)
    (hterm : ∀ m < j, ∀ a, |((P ^ (j - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a| ≤ t m)
    (hsup : ∀ b, |(P *ᵥ g (j + 1) - g (j + 2)) b| ≤ hs) (a : n) :
    |((P ^ (j + 1)) *ᵥ g 1 - g (j + 2)) a| ≤ ∑ m ∈ Finset.range j, t m + hs := by
  rw [lax_telescope P g (j + 1), Finset.sum_apply, Finset.sum_range_succ]
  have hlast : |((P ^ (j + 1 - 1 - j)) *ᵥ (P *ᵥ g (j + 1) - g (j + 2))) a| ≤ hs := by
    have e : j + 1 - 1 - j = 0 := by omega
    rw [e, pow_zero, one_mulVec]; exact hsup a
  have hterm' : ∀ m ∈ Finset.range j,
      |((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a| ≤ t m := by
    intro m hm
    have hm' : m < j := Finset.mem_range.mp hm
    have e : j + 1 - 1 - m = j - m := by omega
    rw [e]
    exact hterm m hm' a
  calc |∑ m ∈ Finset.range j, ((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a
          + ((P ^ (j + 1 - 1 - j)) *ᵥ (P *ᵥ g (j + 1) - g (j + 2))) a|
      ≤ |∑ m ∈ Finset.range j, ((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a|
          + |((P ^ (j + 1 - 1 - j)) *ᵥ (P *ᵥ g (j + 1) - g (j + 2))) a| := abs_add_le _ _
    _ ≤ ∑ m ∈ Finset.range j, t m + hs :=
        add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm')) hlast

/-- The recursion `eq:kernel-rec` with an arbitrary bound for each transported defect. -/
theorem kernel_recursion_terms {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (g : ℕ → n → ℝ) (c : n → ℝ) {theta : ℝ} (hth : 0 ≤ theta)
    (hc : ∀ b, |c b - g 1 b| ≤ theta * g 1 b) (t : ℕ → ℝ) (hs : ℝ) (j : ℕ)
    (hterm : ∀ m < j, ∀ a, |((P ^ (j - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a| ≤ t m)
    (hsup : ∀ b, |(P *ᵥ g (j + 1) - g (j + 2)) b| ≤ hs) (a : n) :
    |((P ^ (j + 1)) *ᵥ c) a - g (j + 2) a|
      ≤ theta * g (j + 2) a + (1 + theta) * (∑ m ∈ Finset.range j, t m + hs) := by
  have h1 := last_step (P ^ (j + 1)) (pow_entries_nonneg P h0 (j + 1)) c (g 1) hc a
  have h2 := lax_kernel_bound_terms P g t hs j hterm hsup a
  have h2' : |((P ^ (j + 1)) *ᵥ g 1) a - g (j + 2) a| ≤ ∑ m ∈ Finset.range j, t m + hs := by
    simpa using h2
  have h3 : ((P ^ (j + 1)) *ᵥ g 1) a ≤ g (j + 2) a + (∑ m ∈ Finset.range j, t m + hs) := by
    linarith [(abs_le.mp h2').2]
  have h4 := mul_le_mul_of_nonneg_left h3 hth
  rw [abs_le] at h1 h2' ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2'.1, h2'.2]

/-- **Theorem "kernel" for matrices with the two bounds of Step 3.** As `kernel_theorem_matrix`,
    for a row-stochastic `P`, but each transported defect `P^{j-m} h_m` is bounded by the smaller of
    `2 mu_{j-m} etabar_{m+1}` (largest entry of the power times the mean of the defect) and
    `etasup_{m+1}` (supremum of the defect; the powers are row-stochastic). This is the form used in
    Step 4 of the proof in the paper, where the first bound is taken for `m ≤ k/2` and the second
    for `m > k/2`. -/
theorem kernel_theorem_matrix_min {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (P : Matrix n n ℝ) (h0 : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1)
    (p : ℕ → n → n → ℝ) (mu etabar etasup W : ℕ → ℝ)
    {d : ℝ} (K : ℕ) (hd0 : 0 ≤ d) (hd1 : 4 * d ≤ 1)
    (hmu : ∀ k, 0 ≤ mu k) (hp0 : ∀ k a i, 0 ≤ p k a i) (hpmu : ∀ k a i, p k a i ≤ mu k)
    (hlast : ∀ b i, |(Fintype.card n : ℝ) * P b i - p 1 b i| ≤ 4 * d * p 1 b i)
    (hbar : ∀ m i, 1 ≤ m → m < K → ∑ b, |(P *ᵥ (fun b' => p m b' i)) b - p (m + 1) b i|
        ≤ (Fintype.card n : ℝ) * etabar m)
    (hsup : ∀ m i b, 1 ≤ m → m < K →
      |(P *ᵥ (fun b' => p m b' i)) b - p (m + 1) b i| ≤ etasup m)
    (hsum : ∀ j, j + 1 < K → ∑ m ∈ Finset.range j,
        min (2 * mu (j - m) * etabar (m + 1)) (etasup (m + 1))
          + etasup (j + 1) ≤ W (j + 1) * mu (j + 2))
    (hW : ∀ j, j + 1 < K → 0 ≤ W (j + 1) ∧ 4 * d + (1 + 4 * d) * W (j + 1) ≤ 1) :
    (∀ l, 1 ≤ l → l ≤ K → kernelDist P p l ≤ mu l)
      ∧ (∀ j, j + 1 < K →
          kernelDist P p (j + 2) ≤ (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2)) := by
  have hN : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have step : ∀ j, j + 1 < K → (∀ l, 1 ≤ l → l ≤ j + 1 → kernelDist P p l ≤ mu l) →
      kernelDist P p (j + 2) ≤ (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2) := by
    intro j hj ih
    rw [kernelDist_le_iff]
    intro a i
    have hent : ∀ m < j, ∀ a b, |(P ^ (j - m)) a b| ≤ 2 * mu (j - m) / (Fintype.card n : ℝ) := by
      intro m hm a b
      rw [abs_of_nonneg (pow_entries_nonneg P h0 _ a b), le_div_iff₀ hN]
      have h1 := (kernelDist_le_iff P p (j - m) (mu (j - m))).mp (ih (j - m) (by omega) (by omega)) a b
      have h2 := hpmu (j - m) a b
      have h3 := (abs_le.mp h1).2
      linarith
    have hw : ∀ m < j, 0 ≤ 2 * mu (j - m) / (Fintype.card n : ℝ) := fun m _ =>
      div_nonneg (mul_nonneg (by norm_num) (hmu _)) hN.le
    have key := kernel_recursion_terms P h0 (fun m b => p m b i)
      (fun b => (Fintype.card n : ℝ) * P b i) (theta := 4 * d) (by linarith)
      (fun b => hlast b i)
      (fun m => min (2 * mu (j - m) * etabar (m + 1)) (etasup (m + 1))) (etasup (j + 1)) j
      (fun m hm a => by
        refine le_min ?_ ?_
        · have hb1 : ∑ b, |(P *ᵥ (fun b => p (m + 1) b i) - fun b => p (m + 2) b i) b|
              ≤ (Fintype.card n : ℝ) * etabar (m + 1) := by
            simpa using hbar (m + 1) i (by omega) (by omega)
          have h1 := (weighted_mulVec_le (P ^ (j - m))
            (P *ᵥ (fun b => p (m + 1) b i) - fun b => p (m + 2) b i) (hent m hm) a).trans
            (mul_le_mul_of_nonneg_left hb1 (hw m hm))
          have e : 2 * mu (j - m) / (Fintype.card n : ℝ) * ((Fintype.card n : ℝ) * etabar (m + 1))
              = 2 * mu (j - m) * etabar (m + 1) := by field_simp
          rw [e] at h1
          exact h1
        · exact sup_pow_mulVec_le P h0 hrow (j - m)
            (P *ᵥ (fun b => p (m + 1) b i) - fun b => p (m + 2) b i)
            (fun b => by simpa using hsup (m + 1) i b (by omega) (by omega)) a)
      (fun b => by simpa using hsup (j + 1) i b (by omega) hj) a
    have e : ((P ^ (j + 1)) *ᵥ fun b => (Fintype.card n : ℝ) * P b i) a
        = (Fintype.card n : ℝ) * (P ^ (j + 2)) a i := by
      have hpow : (P ^ (j + 2)) a i = ∑ b, (P ^ (j + 1)) a b * P b i := by
        rw [show j + 2 = (j + 1) + 1 from rfl, pow_succ, Matrix.mul_apply]
      rw [hpow, Finset.mul_sum]
      simp only [mulVec, dotProduct]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e] at key
    have hs := hsum j hj
    have hWj := hW j hj
    have hpm := hpmu (j + 2) a i
    have hp0' := hp0 (j + 2) a i
    have hm2 := hmu (j + 2)
    calc |(Fintype.card n : ℝ) * (P ^ (j + 2)) a i - p (j + 2) a i|
        ≤ 4 * d * p (j + 2) a i + (1 + 4 * d) * (∑ m ∈ Finset.range j,
            min (2 * mu (j - m) * etabar (m + 1)) (etasup (m + 1)) + etasup (j + 1)) := key
      _ ≤ 4 * d * mu (j + 2) + (1 + 4 * d) * (W (j + 1) * mu (j + 2)) := by
          have h1 : 4 * d * p (j + 2) a i ≤ 4 * d * mu (j + 2) :=
            mul_le_mul_of_nonneg_left hpm (by linarith)
          have h2 := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 1 + 4 * d by linarith)
          linarith
      _ = (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2) := by ring
  have base : kernelDist P p 1 ≤ mu 1 := by
    rw [kernelDist_le_iff]
    intro a i
    have h1 := hlast a i
    rw [pow_one]
    have h2 : 4 * d * p 1 a i ≤ 1 * mu 1 :=
      mul_le_mul hd1 (hpmu 1 a i) (hp0 1 a i) (by norm_num)
    have h3 := abs_le.mp h1
    rw [abs_le]
    constructor <;> linarith [hp0 1 a i, hpmu 1 a i]
  have all : ∀ k, ∀ l, 1 ≤ l → l ≤ k → l ≤ K → kernelDist P p l ≤ mu l := by
    intro k
    induction k with
    | zero => intro l h1 h2; omega
    | succ k ih =>
      intro l hl1 hlk hlK
      by_cases hle : l ≤ k
      · exact ih l hl1 hle hlK
      · have hl : l = k + 1 := by omega
        subst hl
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; exact base
        · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          have hj : j + 1 < K := by omega
          have hstep := step j hj (fun l h1 h2 => ih l h1 h2 (by omega))
          have hWj := hW j hj
          have hm2 := hmu (j + 2)
          calc kernelDist P p (j + 1 + 1) ≤ (4 * d + (1 + 4 * d) * W (j + 1)) * mu (j + 2) := hstep
            _ ≤ 1 * mu (j + 2) := mul_le_mul_of_nonneg_right hWj.2 hm2
            _ = mu (j + 1 + 1) := by ring_nf
  exact ⟨fun l h1 hK => all l l h1 le_rfl hK,
    fun j hj => step j hj (fun l h1 h2 => all l l h1 le_rfl (by omega))⟩

/-- The rows of the walk matrix sum to one when the row normalisation does not vanish. -/
theorem walkMatrix_row_sum {n : Type} [Fintype n] (K : n → n → ℝ) (qv : n → ℝ) (b : n)
    (hS : ∑ l, K b l / (qv b * qv l) ≠ 0) : ∑ j, walkMatrix K qv b j = 1 := by
  simp only [walkMatrix, Matrix.of_apply]
  rw [← Finset.sum_div]
  exact div_self hS

end KernelMin

open Matrix in
/-- **Theorem "kernel" for the sampled walk on the torus, deterministic part, sharp form.**
    Points `x_0, …, x_{N-1}` on the flat torus, walk matrix `P` of the kernel `p_σ` with the
    estimated normalisation. HYPOTHESES on the points (each holds with high probability for a
    random sample): the normalisation `|ρ_j - 1| ≤ δ ≤ 1/8`; estimate (ii) of the consistency lemma,
    `|h_m^{(i)}(b)| ≤ heatDefBound(x_b - x_i)` for `1 ≤ m < K`; estimate (iii) at the three times
    `mσ + 2σ`, `σ + mσ`, `6mσ` with error `δ₃`. HYPOTHESES on numbers: the summation `hsum`, in which each
    transported defect is bounded by the smaller of the mean bound and the supremum bound (Step 3
    of the proof in the paper), and `4δ + (1 + 4δ) W ≤ 1`. CONCLUSION: `D_l ≤ mu_l` for `1 ≤ l ≤ K` and
    `D_{j+2} ≤ (4δ + (1 + 4δ) W_{j+1}) mu_{j+2}`, where `D_k = max |N P^k(a,i) - p_{kσ}(x_a - x_i)|`. -/
theorem heat_kernel_sharp_det {σ M L δ δ3 : ℝ} (hσ : 0 < σ) (d N K : ℕ) (hN : 0 < N)
    (x : ℕ → FlatTorus d) (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hδ3 : 0 ≤ δ3)
    (hρ : ∀ j, |heatRho d σ N x j - 1| ≤ δ)
    (hdef : ∀ m, 1 ≤ m → m < K → ∀ b, b < N → ∀ i, i < N →
      |heatDefect d σ N m x b i| ≤ heatDefBound d σ N m M L δ (x b - x i))
    (hA : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hB : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hC : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    (hC12 : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    (W : ℕ → ℝ)
    (hsum : ∀ j, j + 1 < K → ∑ m ∈ Finset.range j,
        min (2 * heatMu d σ (j - m)
          * heatEtaBar d σ N (m + 1) M L δ δ3) (heatDefSup d σ N (m + 1) M L δ)
          + heatDefSup d σ N (j + 1) M L δ ≤ W (j + 1) * heatMu d σ (j + 2))
    (hW : ∀ j, j + 1 < K → 0 ≤ W (j + 1) ∧ 4 * δ + (1 + 4 * δ) * W (j + 1) ≤ 1) :
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    (∀ l, 1 ≤ l → l ≤ K →
        kernelDist (walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a))
          (fun k (a i : Fin N) => heatP d σ k (x a - x i)) l ≤ heatMu d σ l)
      ∧ (∀ j, j + 1 < K →
        kernelDist (walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a))
          (fun k (a i : Fin N) => heatP d σ k (x a - x i)) (j + 2)
          ≤ (4 * δ + (1 + 4 * δ) * W (j + 1)) * heatMu d σ (j + 2)) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hρb := fun j => abs_le.mp (hρ j)
  have hρpos : ∀ j, 0 < heatRho d σ N x j := fun j => by linarith [(hρb j).1]
  have hK0 : ∀ a j : Fin N, 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j) :=
    fun a j => heatTorus_nonneg hcσ d _
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp
  -- the one-step defect in matrix form
  have hterm : ∀ m, 1 ≤ m → ∀ (i b : Fin N),
      ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a))
          *ᵥ (fun b' : Fin N => heatP d σ m (x b' - x i))) b - heatP d σ (m + 1) (x b - x i)
        = heatDefect d σ N m x b i := by
    intro m hm i b
    have e1 : (fun b' : Fin N => heatP d σ m (x b' - x i))
        = fun b' : Fin N => heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (x b' - x i) :=
      funext fun b' => heatP_of_ne d σ (by omega) _
    rw [e1, heatP_succ]
    exact walk_defect_eq d σ N m hN x (fun j => (hρpos j).ne') b i
  have h := kernel_theorem_matrix_min
    (walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
      (fun a : Fin N => heatRho d σ N x a))
    (fun a j => by
      rw [walkMatrix_apply' _ _ a j (hρpos a).ne']
      exact div_nonneg (div_nonneg (hK0 a j) (hρpos j).le)
        (Finset.sum_nonneg fun l _ => div_nonneg (hK0 a l) (hρpos l).le))
    (fun a => walkMatrix_row_sum _ _ a (ne_of_gt (Finset.sum_pos'
      (fun l _ => div_nonneg (hK0 a l) (mul_pos (hρpos a) (hρpos l)).le)
      ⟨a, Finset.mem_univ a, div_pos (by rw [sub_self]; exact heatTorus_pos hcσ d 0)
        (mul_pos (hρpos a) (hρpos a))⟩)))
    (fun k (a i : Fin N) => heatP d σ k (x a - x i)) (heatMu d σ)
    (fun m => heatEtaBar d σ N m M L δ δ3)
    (fun m => heatDefSup d σ N m M L δ) W K hδ0 (by linarith)
    (heatMu_nonneg d σ) (fun k a i => heatP_nonneg hσ d k _) (fun k a i => heatP_le_mu hσ d k _)
    (fun b i => by
      have h1 := walk_last_step (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
        (fun a : Fin N => heatRho d σ N x a) hK0
        (fun a => by
          rw [hcard]
          unfold heatRho
          rw [mul_div_cancel₀ _ hNpos.ne']
          exact Fin.sum_univ_eq_sum_range
            (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) N)
        hδ0 hδ (fun a => hρ a) b i
      simpa only [heatP_one] using h1)
    (fun m i hm hmK => by
      simp only [hterm m hm i]
      rw [hcard]
      calc ∑ b : Fin N, |heatDefect d σ N m x b i|
          ≤ ∑ b : Fin N, heatDefBound d σ N m M L δ (x b - x i) :=
            Finset.sum_le_sum fun b _ => hdef m hm hmK b b.2 i i.2
        _ = ∑ b ∈ Finset.range N, heatDefBound d σ N m M L δ (x b - x i) :=
            Fin.sum_univ_eq_sum_range (fun b => heatDefBound d σ N m M L δ (x b - x i)) N
        _ ≤ _ := heat_defect_mean_det_min hσ hM hL (by linarith) d N m hN hm x i hδ3
            (hA m hm hmK i i.2) (hB m hm hmK i i.2) (hC m hm hmK i i.2) (hC12 m hm hmK i i.2))
    (fun m i b hm hmK => by
      rw [hterm m hm i b]
      exact (hdef m hm hmK b b.2 i i.2).trans
        (heatDefBound_le_sup hσ hM hL (by linarith) d N m hN hm _))
    (fun j hj => hsum j hj)
    hW
  exact h

/-- The conclusion of the kernel theorem for the sampled walk, entry by entry: for `1 ≤ l ≤ K`,
    `|N P^l(a,i) - p_{lσ}(x_a - x_i)| ≤ mu_l`, and for `j + 1 < K`,
    `|N P^{j+2}(a,i) - p_{(j+2)σ}(x_a - x_i)| ≤ (4δ + (1 + 4δ) W_{j+1}) mu_{j+2}`. -/
def heatKernelSharp (d : ℕ) (σ δ : ℝ) (N K : ℕ) (W : ℕ → ℝ) (x : ℕ → FlatTorus d) : Prop :=
  (∀ l, 1 ≤ l → l ≤ K → ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ l) a i - heatP d σ l (x a - x i)|
        ≤ heatMu d σ l)
    ∧ (∀ j, j + 1 < K → ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ (j + 2)) a i - heatP d σ (j + 2) (x a - x i)|
        ≤ (4 * δ + (1 + 4 * δ) * W (j + 1)) * heatMu d σ (j + 2))

/-- The sharp deterministic kernel theorem, entry by entry. -/
theorem heat_kernel_sharp_entries {σ M L δ δ3 : ℝ} (hσ : 0 < σ) (d N K : ℕ) (hN : 0 < N)
    (x : ℕ → FlatTorus d) (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hδ3 : 0 ≤ δ3)
    (hρ : ∀ j, |heatRho d σ N x j - 1| ≤ δ)
    (hdef : ∀ m, 1 ≤ m → m < K → ∀ b, b < N → ∀ i, i < N →
      |heatDefect d σ N m x b i| ≤ heatDefBound d σ N m M L δ (x b - x i))
    (hA : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hB : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hC : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    (hC12 : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    (W : ℕ → ℝ)
    (hsum : ∀ j, j + 1 < K → ∑ m ∈ Finset.range j,
        min (2 * heatMu d σ (j - m)
          * heatEtaBar d σ N (m + 1) M L δ δ3) (heatDefSup d σ N (m + 1) M L δ)
          + heatDefSup d σ N (j + 1) M L δ ≤ W (j + 1) * heatMu d σ (j + 2))
    (hW : ∀ j, j + 1 < K → 0 ≤ W (j + 1) ∧ 4 * δ + (1 + 4 * δ) * W (j + 1) ≤ 1) :
    heatKernelSharp d σ δ N K W x := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨h1, h2⟩ := heat_kernel_sharp_det hσ d N K hN x hM hL hδ0 hδ hδ3 hρ hdef hA hB hC hC12 W hsum hW
  constructor
  · intro l hl hlK a i
    have := (kernelDist_le_iff _ _ l _).mp (h1 l hl hlK) a i
    simpa using this
  · intro j hj a i
    have := (kernelDist_le_iff _ _ (j + 2) _).mp (h2 j hj) a i
    simpa using this

/-- From the normalisation event at time `τ` to estimate (iii): the sum of the kernel over the
    points, seen from a sample point. -/
theorem norm_event_sum {d N : ℕ} {τ epsn : ℝ} (hN : 0 < N) (x : ℕ → FlatTorus d)
    (h : ∀ y : FlatTorus d,
      |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (y - x j) - N| ≤ epsn) (i : ℕ) :
    ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x b - x i) ≤ N * (1 + epsn / N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := (abs_le.mp (h (x i))).2
  have e : ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x b - x i)
      = ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x i - x b) :=
    Finset.sum_congr rfl fun b _ => by rw [← heatTorus_even, neg_sub]
  have e2 : (N : ℝ) * (1 + epsn / N) = N + epsn := by field_simp
  rw [e, e2]
  linarith

/-- **Theorem "kernel" for a random sample on the torus, sharp form with time-dependent
    constants.** Independent uniform points. HYPOTHESIS `hBn`: the normalisation event at every time
    `τ ≥ σ` has probability at most `pn` (the conclusion of `heat_normalisation_whp`). HYPOTHESES on
    numbers: `hsum`, `hW`. Then the conclusion `heatKernelSharp` of the kernel theorem fails with
    probability at most `(2 + 4K) pn + 4 K N² e^{-L}`. -/
theorem heat_kernel_sharp_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {M L epsn pn : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M) (hL : 0 < L)
    (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 8)
    (hBn : ∀ τ, σ ≤ τ → μ.real {ω | ∃ x : FlatTorus d,
        epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} ≤ pn)
    (W : ℕ → ℝ)
    (hsum : ∀ j, j + 1 < K → ∑ m ∈ Finset.range j,
        min (2 * heatMu d σ (j - m)
          * heatEtaBar d σ N (m + 1) M L (epsn / N) (epsn / N)) (heatDefSup d σ N (m + 1) M L (epsn / N))
          + heatDefSup d σ N (j + 1) M L (epsn / N) ≤ W (j + 1) * heatMu d σ (j + 2))
    (hW : ∀ j, j + 1 < K →
      0 ≤ W (j + 1) ∧ 4 * (epsn / N) + (1 + 4 * (epsn / N)) * W (j + 1) ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ (epsn / N) N K W (fun j => X j ω)}
      ≤ pn + (pn + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))))) + (K : ℝ) * (4 * pn) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM0 : 0 ≤ M := (heatTorus_nonneg hcσ d 0).trans (hMσ 0)
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : ℝ → Set Ω, Bn = fun τ => {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} := ⟨_, rfl⟩
  have hBnP : ∀ τ, σ ≤ τ → μ.real (Bn τ) ≤ pn := fun τ hτ => by rw [hBnd]; exact hBn τ hτ
  have hBnc : ∀ τ ω, ω ∉ Bn τ → ∀ y : FlatTorus d,
      |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (y - X j ω) - N| ≤ epsn := by
    intro τ ω hω y
    by_contra h
    rw [hBnd] at hω
    exact hω ⟨y, not_le.mp h⟩
  obtain ⟨D, hDd⟩ : ∃ D : Set Ω, D = {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N,
      ∃ i ∈ Finset.range N, heatDefBound d σ N m M L (epsn / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|} := ⟨_, rfl⟩
  have hDP : μ.real D ≤ pn + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))) := by
    rw [hDd]
    exact heat_defect_whp hσ d X h_indep hX hlaw N K hN hMσ hL hepsn0 (by linarith) (hBn σ le_rfl)
  obtain ⟨A, hAd⟩ : ∃ A : ℕ → Set Ω, A = fun m : ℕ =>
      Bn ((m : ℝ) * σ + 2 * σ) ∪ (Bn (σ + (m : ℝ) * σ)
        ∪ (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ)))) := ⟨_, rfl⟩
  have hAP : ∀ m ∈ Finset.Icc 1 K, μ.real (A m) ≤ 4 * pn := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have t1 : σ ≤ (m : ℝ) * σ + 2 * σ := by nlinarith
    have t2 : σ ≤ σ + (m : ℝ) * σ := by nlinarith
    have t3 : σ ≤ 6 * ((m : ℝ) * σ) := by nlinarith
    have t4 : σ ≤ 12 * ((m : ℝ) * σ) := by nlinarith
    rw [hAd]
    have u1 := measureReal_union_le (μ := μ) (Bn ((m : ℝ) * σ + 2 * σ))
      (Bn (σ + (m : ℝ) * σ) ∪ (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ))))
    have u2 := measureReal_union_le (μ := μ) (Bn (σ + (m : ℝ) * σ))
      (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ)))
    have u3 := measureReal_union_le (μ := μ) (Bn (6 * ((m : ℝ) * σ))) (Bn (12 * ((m : ℝ) * σ)))
    linarith [hBnP _ t1, hBnP _ t2, hBnP _ t3, hBnP _ t4]
  have hUP : μ.real (⋃ m ∈ Finset.Icc 1 K, A m) ≤ (K : ℝ) * (4 * pn) := by
    calc μ.real (⋃ m ∈ Finset.Icc 1 K, A m) ≤ ∑ m ∈ Finset.Icc 1 K, μ.real (A m) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, 4 * pn := Finset.sum_le_sum hAP
      _ = (K : ℝ) * (4 * pn) := by simp
  have hsub : {ω | ¬ heatKernelSharp d σ (epsn / N) N K W (fun j => X j ω)}
      ⊆ Bn σ ∪ D ∪ ⋃ m ∈ Finset.Icc 1 K, A m := by
    intro ω hbad
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨hn, hD⟩, hAm⟩ := hcon
    apply hbad
    have hδ0 : 0 ≤ epsn / N := div_nonneg hepsn0 hNpos.le
    have hδ8 : epsn / N ≤ 1 / 8 := by rw [div_le_iff₀ hNpos]; linarith
    have hρ : ∀ j, |heatRho d σ N (fun j => X j ω) j - 1| ≤ epsn / N := by
      intro j
      have h := hBnc σ ω hn (X j ω)
      have e : heatRho d σ N (fun j => X j ω) j - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    have hmem : ∀ m, 1 ≤ m → m < K → m ∈ Finset.Icc 1 K := fun m h1 h2 =>
      Finset.mem_Icc.mpr ⟨h1, h2.le⟩
    refine heat_kernel_sharp_entries hσ d N K hN (fun j => X j ω) hM0 hL.le hδ0 hδ8 hδ0 hρ
      ?_ ?_ ?_ ?_ ?_ W hsum hW
    · intro m hm hmK b hb i hi
      by_contra h
      rw [hDd] at hD
      exact hD ⟨m, hmem m hm hmK, b, Finset.mem_range.mpr hb, i, Finset.mem_range.mpr hi,
        not_le.mp h⟩
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.2.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.2.2) i
  calc μ.real _ ≤ μ.real (Bn σ ∪ D ∪ ⋃ m ∈ Finset.Icc 1 K, A m) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real (Bn σ ∪ D) + μ.real (⋃ m ∈ Finset.Icc 1 K, A m) := measureReal_union_le _ _
    _ ≤ (μ.real (Bn σ) + μ.real D) + μ.real (⋃ m ∈ Finset.Icc 1 K, A m) :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := by linarith [hBnP σ le_rfl]

/-- The uniform bound and the Lipschitz constant of the heat kernel decrease in the time. -/
theorem heat_consts_anti {c c' : ℝ} (hc : 0 < c) (hcc : c ≤ c') (d : ℕ) :
    (1 + Real.sqrt (Real.pi / c')) ^ d ≤ (1 + Real.sqrt (Real.pi / c)) ^ d
      ∧ 2 * Real.pi * (2 / c') * (1 + Real.sqrt (2 * Real.pi / c')) ^ d
        ≤ 2 * Real.pi * (2 / c) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d := by
  have hpi := Real.pi_pos
  have h1 : Real.pi / c' ≤ Real.pi / c := div_le_div_of_nonneg_left hpi.le hc hcc
  have h2 : 2 * Real.pi / c' ≤ 2 * Real.pi / c := div_le_div_of_nonneg_left (by positivity) hc hcc
  have h3 : 2 / c' ≤ 2 / c := div_le_div_of_nonneg_left (by norm_num) hc hcc
  have hc' : 0 < c' := lt_of_lt_of_le hc hcc
  constructor
  · exact pow_le_pow_left₀ (by positivity) (by linarith [Real.sqrt_le_sqrt h1]) d
  · have h4 : (1 + Real.sqrt (2 * Real.pi / c')) ^ d ≤ (1 + Real.sqrt (2 * Real.pi / c)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith [Real.sqrt_le_sqrt h2]) d
    exact mul_le_mul (mul_le_mul_of_nonneg_left h3 (by positivity)) h4 (by positivity)
      (by positivity)

/-- **Theorem "kernel" for a random sample on the torus, sharp form with time-dependent
    constants, without hypothesis on events.** Independent uniform points on the flat torus,
    `M = (1 + √(π/c_σ))^d`, `Lip` the Lipschitz constant of `p_σ`, grid parameter `g`,
    `δ = (eps + 2 N Lip / g)/N ≤ 1/8`. HYPOTHESES on numbers only: the summation `hsum` and
    `4δ + (1 + 4δ) W ≤ 1`. The conclusion `heatKernelSharp` fails with probability at most
    `(2 + 4K) · 2 g^d exp(-eps²/(4NM + 2M eps)) + 4 K N² e^{-L}`. -/
theorem heat_kernel_sharp_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (W : ℕ → ℝ)
    (hsum : ∀ j, j + 1 < K → ∑ m ∈ Finset.range j,
        min (2 * heatMu d σ (j - m)
          * heatEtaBar d σ N (m + 1) M L ((ε + 2 * (N * Lip) * (1 / g)) / N) ((ε + 2 * (N * Lip) * (1 / g)) / N))
          (heatDefSup d σ N (m + 1) M L ((ε + 2 * (N * Lip) * (1 / g)) / N))
          + heatDefSup d σ N (j + 1) M L ((ε + 2 * (N * Lip) * (1 / g)) / N)
        ≤ W (j + 1) * heatMu d σ (j + 2))
    (hW : ∀ j, j + 1 < K → 0 ≤ W (j + 1)
      ∧ 4 * ((ε + 2 * (N * Lip) * (1 / g)) / N)
        + (1 + 4 * ((ε + 2 * (N * Lip) * (1 / g)) / N)) * W (j + 1) ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ ((ε + 2 * (N * Lip) * (1 / g)) / N) N K W (fun j => X j ω)}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
            + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
        + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  have hconst : ∀ τ, σ ≤ τ →
      (∀ u, heatTorus d (2 * Real.pi ^ 2 * τ) u ≤ M)
      ∧ (∀ u u', |heatTorus d (2 * Real.pi ^ 2 * τ) u - heatTorus d (2 * Real.pi ^ 2 * τ) u'|
          ≤ Lip * dist u u') := by
    intro τ hτ
    have hcτ : 0 < 2 * Real.pi ^ 2 * τ := by have := lt_of_lt_of_le hσ hτ; positivity
    have hcc : 2 * Real.pi ^ 2 * σ ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    obtain ⟨a1, a2⟩ := heat_consts_anti hcσ hcc d
    constructor
    · intro u; rw [hMdef]; exact (heatTorus_le hcτ d u).trans a1
    · intro u u'; rw [hLipdef]
      exact (heatTorus_lipschitz hcτ d u u').trans (mul_le_mul_of_nonneg_right a2 dist_nonneg)
  have hepsn0 : 0 ≤ ε + 2 * (N * Lip) * (1 / g) := by positivity
  exact heat_kernel_sharp_whp hσ d X h_indep hX hlaw N K hN (hconst σ le_rfl).1 hL hepsn0 hsmall
    (fun τ hτ => heat_normalisation_whp (lt_of_lt_of_le hσ hτ) d X h_indep hX hlaw N hg
      (hconst τ hτ).1 (hconst τ hτ).2 hLip0 hε) W hsum hW

section EigSharp
open Matrix

/-- As `eig_sample_det`, but with a bound `hkern` for the entries of `N P^{k+1} - p_{k+1}` as the
    hypothesis (in place of the consistency hypotheses from which `eig_sample_det` derives one). -/
theorem eig_sample_det_kern {n F : Type} [Fintype n] [Fintype F] [DecidableEq n] [DecidableEq F]
    [Nonempty n]
    (pk : ℕ → n → n → ℝ) (mu : ℕ → ℝ) (P : Matrix n n ℝ)
    (hp0 : ∀ m b i, 0 ≤ pk m b i) (hpmu : ∀ m b i, pk m b i ≤ mu m)
    (k : ℕ)
    (S : Matrix n n ℝ) (hS : S.IsHermitian) (hnn : ∀ j, 0 ≤ hS.eigenvalues₀ j)
    (hle1 : ∀ j, hS.eigenvalues₀ j ≤ 1)
    (r : n → ℝ) (hr : ∀ i, 0 < r i) (hSP : ∀ i l, S i l = r i * P i l / r l)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ i l, |r i / r l - 1| ≤ θ)
    (v : Matrix n F ℝ) (a : F → ℝ) (ha : ∀ f, 0 ≤ a f) {eta s t Dk eps α : ℝ}
    (heta : 0 ≤ eta) (hs0 : 0 ≤ s) (hs : ∀ f, Real.sqrt (a f) ≤ s)
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta)
    (hQ : ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ).IsHermitian)
    (h1 : (fromBlocks ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) 0 0 (0 : Matrix F F ℝ)).IsHermitian)
    (hD : (fromBlocks (0 : Matrix n n ℝ) 0 0 (diagonal a)).IsHermitian)
    (htail : ∀ i l, |pk (k + 1) i l - (Fintype.card n : ℝ) *
        ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
          (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t)
    (hkern : ∀ a' i, |(Fintype.card n : ℝ) * (P ^ (k + 1)) a' i - pk (k + 1) a' i| ≤ Dk)
    (heps : θ * (mu (k + 1) + Dk) + Dk + t ≤ eps)
    (j : Fin (Fintype.card n)) (hj : j.val < Fintype.card (n ⊕ F))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hDj : hD.eigenvalues₀ ⟨j.val, hj⟩ = α ^ (k + 1))
    (h3 : 2 * (eps + eta * s * ∑ g, Real.sqrt (a g)) ≤ α ^ (k + 1)) :
    |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)| ≤ eps + eta * s * ∑ g, Real.sqrt (a g)
      ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
          ≤ 2 * (eps + eta * s * ∑ g, Real.sqrt (a g)) := by
  have hNpos : 0 < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos
  have hrow : ∀ i, ∑ l, |(S ^ (k + 1)) i l - ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ eps := by
    intro i
    refine (row_sums_from_kernel (S ^ (k + 1)) (P ^ (k + 1)) _ (Matrix.of fun i l => pk (k + 1) i l)
      (fun i l => r i / r l) hNpos rfl hθ0 (fun i l => ?_) hθ (fun i l => hkern i l)
      (fun i l => ?_) (fun i l => htail i l) i).trans heps
    · rw [conj_pow_entry S P r hr hSP (k + 1) i l]; ring
    · show |pk (k + 1) i l| ≤ mu (k + 1)
      rw [abs_of_nonneg (hp0 _ _ _)]; exact hpmu _ _ _
  exact eigtorus_from_gram S hS hnn hle1 k v a ha heta hs0 hs hG hQ h1 hD hrow j hj hα0 hα1 hDj h3

/-- **Eigenvalues of the sampled graph on the torus from a bound for the kernel of the walk.** As
    `heatTorus_eig_det`, with the hypothesis `hkern`: `|N P^{k+1}(a,i) - p_{(k+1)c}(x_a - x_i)| ≤ Dk`
    for all entries; this is where the sharp form of the kernel theorem enters. -/
theorem heatTorus_eig_det_kern {c : ℝ} (hc : 0 < c) (d N : ℕ) [NeZero N] (x : Fin N → FlatTorus d)
    (k : ℕ) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {R delta eta t Dk eps α : ℝ}
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hd0 : 0 ≤ delta) (hd : delta ≤ 1 / 8) (heta : 0 ≤ eta)
    (hnorm : ∀ b, |(∑ l, heatTorus d c (x b - x l)) / N - 1| ≤ delta)
    (hgram : ∀ f g : modeSet d H, |∑ i, torusMode d f.1 (x i) * torusMode d g.1 (x i)
        - N * (if f = g then (1 : ℝ) else 0)| ≤ N * eta)
    (ht : Real.exp (-((k + 1 : ℕ) * c) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k + 1 : ℕ) * c))) ^ d ≤ t)
    (hkern : ∀ a i : Fin N, |(N : ℝ) * ((walkMatrix (fun i j : Fin N => heatTorus d c (x i - x j))
        (fun i => (∑ l, heatTorus d c (x i - x l)) / N)) ^ (k + 1)) a i
      - heatTorus d ((k + 1 : ℕ) * c) (x a - x i)| ≤ Dk)
    (heps : 3 * delta * ((1 + Real.sqrt (Real.pi / ((k + 1 : ℕ) * c))) ^ d + Dk) + Dk + t ≤ eps)
    (hS : (symGraph (fun i j : Fin N => heatTorus d c (x i - x j))
      (fun i => (∑ l, heatTorus d c (x i - x l)) / N)).IsHermitian)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) < modeCoeff d ((k + 1 : ℕ) * c) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (k + 1) ≤ modeCoeff d ((k + 1 : ℕ) * c) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)) ≤ α ^ (k + 1)) :
    |hS.eigenvalues₀ j ^ (k + 1) - α ^ (k + 1)|
        ≤ eps + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)
      ∧ ((k + 1 : ℕ) : ℝ) * (α ^ (k + 1) * |hS.eigenvalues₀ j - α|)
          ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
              Real.sqrt (modeCoeff d ((k + 1 : ℕ) * c) g.1)) := by
  classical
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp
  set K : Fin N → Fin N → ℝ := fun i j => heatTorus d c (x i - x j) with hKdef
  set rho : Fin N → ℝ := fun i => (∑ l, heatTorus d c (x i - x l)) / N with hrhodef
  set pk : ℕ → Fin N → Fin N → ℝ := fun m b i =>
    if m = 0 then 0 else heatTorus d ((m : ℕ) * c) (x b - x i) with hpkdef
  set mu : ℕ → ℝ := fun m => if m = 0 then 0 else (1 + Real.sqrt (Real.pi / ((m : ℕ) * c))) ^ d
    with hmudef
  have hmc : ∀ m : ℕ, m ≠ 0 → 0 < (m : ℝ) * c := fun m hm =>
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hc
  have hpk1 : ∀ b i, pk 1 b i = K b i := fun b i => by simp [hpkdef, hKdef]
  have hK0 : ∀ i j, 0 ≤ K i j := fun i j => heatTorus_nonneg hc d _
  have hKsym : ∀ i j, K i j = K j i := fun i j => by
    simp only [hKdef]; rw [← heatTorus_even, neg_sub]
  have hrho1 : ∀ b, |rho b - 1| ≤ delta := hnorm
  have hrhopos : ∀ b, 0 < rho b := fun b => by
    have := abs_le.mp (hrho1 b); linarith [this.1]
  have hrhoeq : ∀ b, (Fintype.card (Fin N) : ℝ) * rho b = ∑ l, K b l := fun b => by
    rw [hcard]; simp only [hrhodef, hKdef]; field_simp
  have hDb := fun i => graph_degree_bounds K hK0 rho hd0 hd hrhoeq hrho1 i
  have hDpos : ∀ i, 0 < ∑ l, K i l / (rho i * rho l) := fun i =>
    lt_of_lt_of_le (div_pos (by rw [hcard]; exact hNpos) (by linarith)) (hDb i).1
  -- kernel-matrix factor
  set a : modeSet d H → ℝ := fun f => modeCoeff d ((k + 1 : ℕ) * c) f.1 with hadef
  set v : Matrix (Fin N) (modeSet d H) ℝ :=
    Matrix.of fun i f => torusMode d f.1 (x i) / Real.sqrt N with hvdef
  have ha : ∀ f, 0 ≤ a f := fun f => modeCoeff_nonneg d _ f.1
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hsqpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hs : ∀ f, Real.sqrt (a f) ≤ 1 := fun f => by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    rcases f with ⟨_ | ⟨n, b⟩, hf⟩
    · simp [hadef, modeCoeff]
    · simp only [hadef, modeCoeff]
      apply Real.exp_le_one_iff.mpr
      have h1 : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
      have := (hmc (k + 1) (Nat.succ_ne_zero k)).le
      nlinarith
  have hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta := by
    intro f g
    have e : ∑ i, v i f * v i g - (if f = g then (1 : ℝ) else 0)
        = (∑ i, torusMode d f.1 (x i) * torusMode d g.1 (x i)
            - N * (if f = g then (1 : ℝ) else 0)) / N := by
      simp only [hvdef, of_apply]
      rw [sub_div, Finset.sum_div, mul_div_cancel_left₀ _ hNpos.ne']
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_mul_div_comm, hsqN]
    rw [e, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    linarith [hgram f g]
  have hQ := gram_hermitian (Matrix.of fun i f => Real.sqrt (a f) * v i f)
  have h1 := pad_hermitian₁ (F := modeSet d H) _ hQ
  have hD := pad_hermitian₂ (n := Fin N) a
  have htail : ∀ i l, |pk (k + 1) i l - (Fintype.card (Fin N) : ℝ) *
      ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t := by
    intro i l
    rw [finite_rank_kernel_entry v a ha i l, hcard]
    have e : (N : ℝ) * ∑ f, a f * v i f * v l f
        = 1 + ∑ n ∈ H, 2 * Real.exp (-((k + 1 : ℕ) * c) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
            * (torusChar d n (x i - x l)).re := by
      rw [← modeSet_kernel d ((k + 1 : ℕ) * c) H (x i) (x l),
        ← Finset.sum_coe_sort (modeSet d H), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [hvdef, hadef, of_apply]
      field_simp
      rw [Real.sq_sqrt hNpos.le]; ring
    rw [e]
    have hp : pk (k + 1) i l = heatTorus d ((k + 1 : ℕ) * c) (x i - x l) := by
      simp [hpkdef]
    rw [hp]
    exact (heatTorus_truncation_half (hmc (k + 1) (Nat.succ_ne_zero k)) d H hH0 hH2 hR _).trans ht
  have hj : j.val < Fintype.card (Fin N ⊕ modeSet d H) := by
    rw [Fintype.card_sum]; exact lt_of_lt_of_le j.2 (Nat.le_add_right _ _)
  have hDj : hD.eigenvalues₀ ⟨j.val, hj⟩ = α ^ (k + 1) :=
    diag_pad_eigenvalue a hD (pow_pos hα0 _) ⟨j.val, hj⟩ hc1 hc2
  refine eig_sample_det_kern pk mu (walkMatrix K rho)
    (fun m b i => ?_) (fun m b i => ?_) k
    (symGraph K rho) hS (symGraph_eig_nonneg K rho (fun y => heatTorus_quadform_nonneg hc d x y) hS)
    (symGraph_eig_le_one K rho hKsym hK0 hrhopos hDpos hS)
    (fun i => Real.sqrt (∑ l, K i l / (rho i * rho l))) (fun i => Real.sqrt_pos.mpr (hDpos i))
    (symGraph_conj K rho hDpos) (θ := 3 * delta) (by linarith)
    (fun i l => sqrt_ratio_bound (by rw [hcard]; exact hNpos) hd0 hd (hDb i) (hDb l))
    v a ha (Dk := Dk) (eps := eps) (t := t) heta zero_le_one hs hG hQ h1 hD htail ?_ ?_
    j hj hα0.le hα1 hDj h3
  · simp only [hpkdef]; split_ifs with h
    · exact le_rfl
    · exact heatTorus_nonneg (hmc m h) d _
  · simp only [hpkdef, hmudef]; split_ifs with h
    · exact le_rfl
    · exact heatTorus_le (hmc m h) d _
  · intro a' i
    have := hkern a' i
    simp only [hpkdef, hcard, Nat.succ_ne_zero, if_false]
    exact this
  · simpa [hmudef] using heps

/-- The conclusion of the sharp kernel theorem in the form used by the eigenvalue theorem: a bound
    for the entries of `N P^{k+1} - p_{(k+1)c}` with `k = j + 1`, `c = 2π²σ`. -/
theorem heatKernelSharp_kern {d N K : ℕ} {σ δ : ℝ} {W : ℕ → ℝ} (hN : 0 < N) (x : ℕ → FlatTorus d)
    (h : heatKernelSharp d σ δ N K W x) (j : ℕ) (hj : j + 1 < K) (a i : Fin N) :
    |(N : ℝ) * ((walkMatrix (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j))
        (fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N))
          ^ (j + 1 + 1)) a i
      - heatTorus d ((j + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) (x a - x i)|
      ≤ (4 * δ + (1 + 4 * δ) * W (j + 1)) * heatMu d σ (j + 2) := by
  have h2 := h.2 j hj a i
  have e1 : (fun a : Fin N => heatRho d σ N x a)
      = fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N := by
    funext a
    unfold heatRho
    rw [Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) N]
  have e2 : heatP d σ (j + 2) (x a - x i)
      = heatTorus d ((j + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) (x a - x i) := by
    rw [heatP_of_ne d σ (by omega)]
    congr 1
    push_cast
    ring
  rw [e1, e2] at h2
  exact h2

/-- **Eigenvalues of the sampled graph on the torus from the sharp kernel theorem, with
    probability.** `c = 2π²σ`, `k = j' + 1` with `j' + 1 < K`, `δ = epsn/N`. The conclusion of
    `heatTorus_eig_det_kern` with `Dk = (4δ + (1 + 4δ) W_{j'+1}) mu_{j'+2}` fails only on the union of
    three events: normalisation (`hBn`), failure of the sharp kernel theorem (`hKS`), Gram matrix of
    the sampled modes (`hBg`). HYPOTHESES: the probabilities of these events; they are the
    conclusions of `heat_normalisation_whp`, `heat_kernel_sharp_sample`, `flatTorus_gram_whp`. -/
theorem heat_eig_sharp_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : 0 < σ) (d N K : ℕ) [NeZero N] (X : ℕ → Ω → FlatTorus d)
    (j' : ℕ) (hj' : j' + 1 < K) (W : ℕ → ℝ)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {R eta t eps α epsn pn pks pg : ℝ}
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 8) (heta : 0 ≤ eta)
    (hBn : μ.real {ω | ∃ x : FlatTorus d,
        epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} ≤ pn)
    (hKS : μ.real {ω | ¬ heatKernelSharp d σ (epsn / N) N K W (fun j => X j ω)} ≤ pks)
    (hBg : μ.real {ω | ∃ f g : modeSet d H, N * eta ≤ |∑ j ∈ Finset.range N,
        torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
        - N * (if f = g then (1 : ℝ) else 0)|} ≤ pg)
    (ht : Real.exp (-((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d ≤ t)
    (heps : 3 * (epsn / N)
          * ((1 + Real.sqrt (Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
            + (4 * (epsn / N) + (1 + 4 * (epsn / N)) * W (j' + 1)) * heatMu d σ (j' + 2))
        + (4 * (epsn / N) + (1 + 4 * (epsn / N)) * W (j' + 1)) * heatMu d σ (j' + 2) + t ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (j' + 1 + 1) < modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (j' + 1 + 1) ≤ modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)) ≤ α ^ (j' + 1 + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph
          (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
          (fun i : Fin N =>
            (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (j' + 1 + 1) - α ^ (j' + 1 + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H,
                Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
          ∧ ((j' + 1 + 1 : ℕ) : ℝ) * (α ^ (j' + 1 + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))}
      ≤ pn + pks + pg := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : Set Ω, Bn = {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} := ⟨_, rfl⟩
  obtain ⟨Bk, hBkd⟩ : ∃ Bk : Set Ω,
      Bk = {ω | ¬ heatKernelSharp d σ (epsn / N) N K W (fun j => X j ω)} := ⟨_, rfl⟩
  obtain ⟨Bg, hBgd⟩ : ∃ Bg : Set Ω, Bg = {ω | ∃ f g : modeSet d H, N * eta ≤ |∑ j ∈ Finset.range N,
      torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
      - N * (if f = g then (1 : ℝ) else 0)|} := ⟨_, rfl⟩
  have hsub : {ω | ¬ ∀ hS : (symGraph
          (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
          (fun i : Fin N =>
            (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (j' + 1 + 1) - α ^ (j' + 1 + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H,
                Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
          ∧ ((j' + 1 + 1 : ℕ) : ℝ) * (α ^ (j' + 1 + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))}
      ⊆ (Bn ∪ Bk) ∪ Bg := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨hn, hk⟩, hg⟩ := hcon
    rw [hBnd] at hn
    rw [hBkd] at hk
    rw [hBgd] at hg
    have hks : heatKernelSharp d σ (epsn / N) N K W (fun j => X j ω) := not_not.mp hk
    apply hω
    intro hS
    refine heatTorus_eig_det_kern hc d N (fun i => X i ω) (j' + 1) H hH0 hH2 hR
      (div_nonneg hepsn0 hNpos.le) (by rw [div_le_iff₀ hNpos]; linarith) heta
      (fun b => ?_) (fun f g => ?_) ht
      (fun a i => heatKernelSharp_kern hN (fun j => X j ω) hks j' hj' a i) heps hS j hα0 hα1
      hc1 hc2 h3
    · have h : |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X j ω) - N|
          ≤ epsn := by
        by_contra h; exact hn ⟨X b ω, not_le.mp h⟩
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X j ω)) N] at h
      have e : (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X l ω)) / N - 1
          = (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X l ω) - N) / N := by
        field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    · have h : |∑ j ∈ Finset.range N, torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
          - N * (if f = g then (1 : ℝ) else 0)| < N * eta := by
        by_contra h; exact hg ⟨f, g, not_lt.mp h⟩
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)) N] at h
      exact h.le
  have hBn' : μ.real Bn ≤ pn := by rw [hBnd]; exact hBn
  have hKS' : μ.real Bk ≤ pks := by rw [hBkd]; exact hKS
  have hBg' : μ.real Bg ≤ pg := by rw [hBgd]; exact hBg
  calc μ.real _ ≤ μ.real ((Bn ∪ Bk) ∪ Bg) := measureReal_mono hsub
    _ ≤ μ.real (Bn ∪ Bk) + μ.real Bg := measureReal_union_le _ _
    _ ≤ (μ.real Bn + μ.real Bk) + μ.real Bg := add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ pn + pks + pg := by linarith

/-- **Eigenvalues of the sampled graph on the torus from the sharp kernel recursion, for random
    samples.** Independent uniform points on the flat torus, kernel time `σ`, `c = 2π²σ`,
    `k = j' + 1 < K` steps, `δ = (ε + 2 N Lip / g)/N ≤ 1/8`. No hypothesis on events. HYPOTHESES on
    numbers: `hsum`, `hW` (the summation of the kernel recursion), `ht` (tail of the Fourier
    series), `heps`, `h3` (size of the error against `α^{k+1}`), and the two counts `hc1`, `hc2`
    that place `α^{k+1}` among the coefficients of the modes. CONCLUSION: parts (i) and (ii) of
    Theorem "eigenvalues on the torus" for the `j`-th eigenvalue of `S` fail with probability at
    most `(3 + 4K) · 2 g^d exp(-ε²/(4NM + 2Mε)) + 4 K N² e^{-L} + 2 |F|² exp(-(Nη/2)²/(2N))`. -/
theorem heat_eig_sharp_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (j' : ℕ) (hj' : j' + 1 < K) (W : ℕ → ℝ)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g) {M Lip L ε δ R eta t eps α : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (heta : 0 ≤ eta)
    (hsum : ∀ j, j + 1 < K → ∑ m ∈ Finset.range j,
        min (2 * heatMu d σ (j - m)
          * heatEtaBar d σ N (m + 1) M L δ δ) (heatDefSup d σ N (m + 1) M L δ)
          + heatDefSup d σ N (j + 1) M L δ ≤ W (j + 1) * heatMu d σ (j + 2))
    (hW : ∀ j, j + 1 < K → 0 ≤ W (j + 1) ∧ 4 * δ + (1 + 4 * δ) * W (j + 1) ≤ 1)
    (ht : Real.exp (-((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d ≤ t)
    (heps : 3 * δ
          * ((1 + Real.sqrt (Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
            + (4 * δ + (1 + 4 * δ) * W (j' + 1)) * heatMu d σ (j' + 2))
        + (4 * δ + (1 + 4 * δ) * W (j' + 1)) * heatMu d σ (j' + 2) + t ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (j' + 1 + 1) < modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (j' + 1 + 1) ≤ modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)) ≤ α ^ (j' + 1 + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph
          (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
          (fun i : Fin N =>
            (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (j' + 1 + 1) - α ^ (j' + 1 + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H,
                Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
          ∧ ((j' + 1 + 1 : ℕ) : ℝ) * (α ^ (j' + 1 + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
            + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
              + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
          + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2
            * (2 * Real.exp (-(N * eta / 2) ^ 2 / (2 * N))) := by
  subst hδ
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M := fun u => by
    rw [hMdef]; exact heatTorus_le hcσ d u
  have hLip : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u
      - heatTorus d (2 * Real.pi ^ 2 * σ) u'| ≤ Lip * dist u u' := fun u u' => by
    rw [hLipdef]; exact heatTorus_lipschitz hcσ d u u'
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hepsn0 : 0 ≤ ε + 2 * (N * Lip) * (1 / g) := by positivity
  have hBn := heat_normalisation_whp hσ d X h_indep hX hlaw N hg hM hLip hLip0 hε
  have hKS := heat_kernel_sharp_sample hσ d X h_indep hX hlaw N K hN hg hMdef hLipdef hL hε hsmall
    W hsum hW
  have hBg := flatTorus_gram_whp (μ := μ) d X h_indep hX hlaw (modeSet d H)
    (fun n b h => hH0 n ((mem_modeSet d H n b).mp h))
    (fun n b n' b' h h' => hH2 n ((mem_modeSet d H n b).mp h) n' ((mem_modeSet d H n' b').mp h'))
    N (ε := N * eta) (mul_nonneg (Nat.cast_nonneg N) heta)
  exact heat_eig_sharp_whp hσ d N K X j' hj' W H hH0 hH2 hR hepsn0 hsmall heta hBn hKS hBg ht heps
    j hα0 hα1 hc1 hc2 h3

end EigSharp

/-- Closed bound for the coefficient `heatKB` for `σ ≤ s`, `σ ≤ 1`:
    `heatKB ≤ ((2πσ)^{-1/2} (√(4π) + 1) √3)^d`. -/
theorem heatKB_le {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hσ1 : σ ≤ 1) (d : ℕ) :
    heatKB d σ s
      ≤ (1 / Real.sqrt (2 * Real.pi * σ) * ((Real.sqrt (4 * Real.pi) + 1) * Real.sqrt 3)) ^ d := by
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  have hpi := Real.pi_pos
  unfold heatKB
  simp only [← Real.sqrt_eq_rpow]
  rw [← div_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have hC : Real.sqrt (Real.pi / (1 / (4 * σ))) ≤ Real.sqrt (4 * Real.pi) := by
    apply Real.sqrt_le_sqrt
    have e : Real.pi / (1 / (4 * σ)) = 4 * Real.pi * σ := by field_simp
    rw [e]
    nlinarith
  have hsa : 0 < Real.sqrt (2 * Real.pi * s) := Real.sqrt_pos.mpr (by positivity)
  have hsb : 0 < Real.sqrt (2 * Real.pi * (s + 2 * σ)) := Real.sqrt_pos.mpr (by positivity)
  have hBD : 1 / Real.sqrt (2 * Real.pi * s) / (1 / Real.sqrt (2 * Real.pi * (s + 2 * σ)))
      ≤ Real.sqrt 3 := by
    have e : 1 / Real.sqrt (2 * Real.pi * s) / (1 / Real.sqrt (2 * Real.pi * (s + 2 * σ)))
        = Real.sqrt (2 * Real.pi * (s + 2 * σ) / (2 * Real.pi * s)) := by
      rw [Real.sqrt_div (by positivity)]
      field_simp
    rw [e]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hA : 0 ≤ 1 / Real.sqrt (2 * Real.pi * σ) := by positivity
  calc 1 / Real.sqrt (2 * Real.pi * σ) * (1 / Real.sqrt (2 * Real.pi * s))
          * (Real.sqrt (Real.pi / (1 / (4 * σ))) + 1) / (1 / Real.sqrt (2 * Real.pi * (s + 2 * σ)))
      = 1 / Real.sqrt (2 * Real.pi * σ) * ((Real.sqrt (Real.pi / (1 / (4 * σ))) + 1)
          * (1 / Real.sqrt (2 * Real.pi * s) / (1 / Real.sqrt (2 * Real.pi * (s + 2 * σ))))) := by
        ring
    _ ≤ 1 / Real.sqrt (2 * Real.pi * σ) * ((Real.sqrt (4 * Real.pi) + 1) * Real.sqrt 3) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (by linarith) hBD (by positivity) (by positivity)) hA

/-- The constant in the closed bound for `heatCV`. -/
noncomputable def cvConst : ℝ :=
  4 / Real.pi * (1 + Real.sqrt (12 * Real.pi)) * Real.sqrt (12 * Real.pi) * Real.sqrt (2 * Real.pi)

theorem cvConst_nonneg : 0 ≤ cvConst := by
  unfold cvConst
  have := Real.pi_pos
  positivity

/-- Closed bound for the coefficient `heatCV` for `σ ≤ s ≤ 1`, with `Y = √(π/(2π²s)) = (2πs)^{-1/2}`:
    `heatCV ≤ d (σ/s) c₁ Y ((1 + Y) √6)^{d-1}`. -/
theorem heatCV_le {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : s ≤ 1) (d : ℕ) :
    heatCV d σ s
      ≤ (d : ℝ) * (σ / s * (cvConst * Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))))
        * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) * Real.sqrt 6) ^ (d - 1) := by
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  have hpi := Real.pi_pos
  unfold heatCV
  simp only [← Real.sqrt_eq_rpow, pow_one]
  have e12 : Real.pi / (1 / (12 * s)) = 12 * Real.pi * s := by field_simp
  have e12' : 2 * Real.pi * (6 * s) = 12 * Real.pi * s := by ring
  rw [e12, e12']
  have hT : Real.sqrt (12 * Real.pi * s) = Real.sqrt (12 * Real.pi) * Real.sqrt s :=
    Real.sqrt_mul (by positivity) s
  have hT1 : Real.sqrt (12 * Real.pi * s) ≤ Real.sqrt (12 * Real.pi) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hY : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)) = 1 / (Real.sqrt (2 * Real.pi) * Real.sqrt s) := by
    have e : Real.pi / (2 * Real.pi ^ 2 * s) = 1 / (2 * Real.pi * s) := by field_simp
    rw [e, Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul (by positivity)]
  have h2pi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h2pisq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  -- the scalar factor
  have hfac : 4 / (Real.pi * s) * ((1 + Real.sqrt (12 * Real.pi * s)) * Real.sqrt (12 * Real.pi * s))
      ≤ cvConst * Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)) := by
    have h1 : 4 / (Real.pi * s) * ((1 + Real.sqrt (12 * Real.pi * s)) * Real.sqrt (12 * Real.pi * s))
        ≤ 4 / (Real.pi * s) * ((1 + Real.sqrt (12 * Real.pi))
            * (Real.sqrt (12 * Real.pi) * Real.sqrt s)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [← hT]
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    have h2 : 4 / (Real.pi * s) * ((1 + Real.sqrt (12 * Real.pi))
            * (Real.sqrt (12 * Real.pi) * Real.sqrt s))
        = cvConst * Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)) := by
      rw [hY]
      unfold cvConst
      have hs' : s = Real.sqrt s * Real.sqrt s := hss.symm
      field_simp
      nlinarith [hss, h2pisq]
    linarith
  -- the last factor
  have hlast : (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)))
        * Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s)))
      ≤ (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) * Real.sqrt 6 := by
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg Real.pi, mul_pos hpi hpi]
  have hpow := pow_le_pow_left₀ (by positivity) hlast (d - 1)
  have hσs0 : 0 ≤ σ / s := by positivity
  calc (d : ℝ) * (σ / s * (4 / (Real.pi * s))
          * ((1 + Real.sqrt (12 * Real.pi * s)) * Real.sqrt (12 * Real.pi * s)))
        * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)))
          * Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s)))) ^ (d - 1)
      = (d : ℝ) * (σ / s * (4 / (Real.pi * s)
          * ((1 + Real.sqrt (12 * Real.pi * s)) * Real.sqrt (12 * Real.pi * s))))
        * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)))
          * Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s)))) ^ (d - 1) := by
        ring
    _ ≤ (d : ℝ) * (σ / s * (cvConst * Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))))
        * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) * Real.sqrt 6) ^ (d - 1) := by
        refine mul_le_mul ?_ hpow (by positivity) ?_
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac hσs0)
            (Nat.cast_nonneg d)
        · have := cvConst_nonneg
          positivity

/-- `heatCV ≤ d c₁ √6^{d-1} (σ/s) · heatM(2π²s)` for `σ ≤ s ≤ 1`. -/
theorem heatCV_le_mu {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : s ≤ 1) (d : ℕ) :
    heatCV d σ s
      ≤ (d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1) * (σ / s) * heatM d (2 * Real.pi ^ 2 * s) := by
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  have h := heatCV_le hσ hσs hs1 d
  have hc := cvConst_nonneg
  obtain ⟨Y, hY⟩ : ∃ Y, Y = Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)) := ⟨_, rfl⟩
  have hY0 : 0 ≤ Y := by rw [hY]; exact Real.sqrt_nonneg _
  unfold heatM
  rw [← hY] at h ⊢
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.cast_zero, zero_mul] at h ⊢
    exact h
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h ⊢
    refine h.trans ?_
    have hσs0 : 0 ≤ σ / s := by positivity
    have h6 : 0 ≤ Real.sqrt 6 ^ n := by positivity
    have key : Y * ((1 + Y) * Real.sqrt 6) ^ n ≤ Real.sqrt 6 ^ n * (1 + Y) ^ (n + 1) := by
      rw [mul_pow, pow_succ]
      have h1 : Y * ((1 + Y) ^ n * Real.sqrt 6 ^ n) ≤ (1 + Y) * ((1 + Y) ^ n * Real.sqrt 6 ^ n) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith
    calc ((n + 1 : ℕ) : ℝ) * (σ / s * (cvConst * Y)) * ((1 + Y) * Real.sqrt 6) ^ n
        = ((n + 1 : ℕ) : ℝ) * cvConst * (σ / s) * (Y * ((1 + Y) * Real.sqrt 6) ^ n) := by ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * cvConst * (σ / s) * (Real.sqrt 6 ^ n * (1 + Y) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring

/-- The square of the base of `heatQ` at `c = 2π²·6s`, in terms of `w = √(2πs)`. -/
theorem heatQ_base_sq {s : ℝ} (hs : 0 < s) :
    (Real.sqrt (1 / Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / Real.pi))
        / (1 / Real.sqrt (2 * (2 * Real.pi ^ 2 * (6 * s)) / Real.pi))) ^ 2
      = 2 * Real.sqrt 6 * Real.sqrt (2 * Real.pi * s) := by
  have hpi := Real.pi_pos
  obtain ⟨w, hw⟩ : ∃ w, w = Real.sqrt (2 * Real.pi * s) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact Real.sqrt_pos.mpr (by positivity)
  have hww : w * w = 2 * Real.pi * s := by rw [hw]; exact Real.mul_self_sqrt (by positivity)
  have e1 : 2 * Real.pi ^ 2 * (6 * s) / Real.pi = 6 * (w * w) := by rw [hww]; field_simp
  have e2 : 2 * (2 * Real.pi ^ 2 * (6 * s)) / Real.pi = 12 * (w * w) := by
    rw [hww]; field_simp; ring
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have h6p : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have s1 : Real.sqrt (6 * (w * w)) = Real.sqrt 6 * w := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul_self hw0.le]
  rw [e1, e2, ← hw, div_pow, Real.sq_sqrt (by positivity), s1, div_pow, one_pow,
    Real.sq_sqrt (by positivity)]
  field_simp
  nlinarith [h6]

/-- `heatCV · heatQ² ≤ d c₁ 2√6 (12 (1 + √(2π)))^{d-1} (σ/s)` for `σ ≤ s ≤ 1`: the factor `s^{-d/2}`
    of the variance bound is cancelled by `heatQ² ∼ s^{d/2}` (this is where (P5) enters). -/
theorem heatCV_heatQ {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : s ≤ 1) (d : ℕ) :
    heatCV d σ s * heatQ d (2 * Real.pi ^ 2 * (6 * s)) ^ 2
      ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (σ / s) := by
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  have hpi := Real.pi_pos
  have h := heatCV_le hσ hσs hs1 d
  have hc := cvConst_nonneg
  obtain ⟨w, hw⟩ : ∃ w, w = Real.sqrt (2 * Real.pi * s) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact Real.sqrt_pos.mpr (by positivity)
  have hw1 : w ≤ Real.sqrt (2 * Real.pi) := by
    rw [hw]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hY : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)) = 1 / w := by
    have e : Real.pi / (2 * Real.pi ^ 2 * s) = 1 / (2 * Real.pi * s) := by field_simp
    rw [e, Real.sqrt_div (by norm_num), Real.sqrt_one, hw]
  have hQ : heatQ d (2 * Real.pi ^ 2 * (6 * s)) ^ 2 = (2 * Real.sqrt 6 * w) ^ d := by
    unfold heatQ
    simp only [← Real.sqrt_eq_rpow]
    rw [← pow_mul, mul_comm d 2, pow_mul, heatQ_base_sq hs, ← hw]
  have h6 : Real.sqrt 6 * Real.sqrt 6 = 6 := Real.mul_self_sqrt (by norm_num)
  have h6p : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  rw [hY] at h
  rw [hQ]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one] at h ⊢
    exact h
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h ⊢
    have hσs0 : 0 ≤ σ / s := by positivity
    have hstep : ((1 + 1 / w) * Real.sqrt 6) * (2 * Real.sqrt 6 * w)
        ≤ 12 * (1 + Real.sqrt (2 * Real.pi)) := by
      have e : ((1 + 1 / w) * Real.sqrt 6) * (2 * Real.sqrt 6 * w)
          = 2 * (Real.sqrt 6 * Real.sqrt 6) * (w + 1) := by field_simp
      rw [e, h6]; linarith
    have hpow := pow_le_pow_left₀ (by positivity) hstep n
    have e2 : (1 / w) * (2 * Real.sqrt 6 * w) = 2 * Real.sqrt 6 := by field_simp
    calc heatCV (n + 1) σ s * (2 * Real.sqrt 6 * w) ^ (n + 1)
        ≤ (((n + 1 : ℕ) : ℝ) * (σ / s * (cvConst * (1 / w)))
            * ((1 + 1 / w) * Real.sqrt 6) ^ n) * (2 * Real.sqrt 6 * w) ^ (n + 1) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = ((n + 1 : ℕ) : ℝ) * cvConst * (σ / s) * ((1 / w) * (2 * Real.sqrt 6 * w))
            * (((1 + 1 / w) * Real.sqrt 6) * (2 * Real.sqrt 6 * w)) ^ n := by
          rw [mul_pow (((1 + 1 / w) * Real.sqrt 6)) (2 * Real.sqrt 6 * w) n, pow_succ]; ring
      _ ≤ ((n + 1 : ℕ) : ℝ) * cvConst * (σ / s) * (2 * Real.sqrt 6)
            * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ n := by
          rw [e2]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring

/-- Algebraic core of the closed bounds for the defect: the defect expression is monotone in the
    three quantities `X` (bound `B`), `T` (Bernstein square-root term) and `Z` (first moment). -/
theorem defect_closed_core {N L δ S X T Z Xb Zb : ℝ} (hN : 0 < N) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hX : X ≤ Xb) (hT : T ≤ S * Zb) (hZ : Z ≤ Zb) :
    ((2 * X * L + 2 * T) + 2 * X + 2 * δ * (N * Z + (2 * X * L + 2 * T) + 2 * X)) / (N * (1 / 3))
      ≤ 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * Xb + 2 * S * Zb) + 2 * δ * N * Zb) := by
  rw [div_le_iff₀ (by positivity)]
  have e : 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * Xb + 2 * S * Zb) + 2 * δ * N * Zb) * (N * (1 / 3))
      = (1 + 2 * δ) * ((2 * L + 2) * Xb + 2 * S * Zb) + 2 * δ * N * Zb := by field_simp
  rw [e]
  have h1 : (2 * L + 2) * X ≤ (2 * L + 2) * Xb := mul_le_mul_of_nonneg_left hX (by linarith)
  have h3 : N * Z ≤ N * Zb := mul_le_mul_of_nonneg_left hZ hN.le
  have h4 : (1 + 2 * δ) * ((2 * L + 2) * X + 2 * T)
      ≤ (1 + 2 * δ) * ((2 * L + 2) * Xb + 2 * S * Zb) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h5 : 2 * δ * (N * Z) ≤ 2 * δ * (N * Zb) := mul_le_mul_of_nonneg_left h3 (by linarith)
  nlinarith

theorem heatBsup_eq (d : ℕ) (σ s M : ℝ) :
    heatBsup d σ s M = heatKB d σ s * heatM d (2 * Real.pi ^ 2 * (s + 2 * σ))
      + M * heatM d (2 * Real.pi ^ 2 * (σ + s)) := by
  unfold heatBsup heatKB
  ring

theorem heatVsup_eq (d : ℕ) (σ s : ℝ) :
    heatVsup d σ s = heatCV d σ s * heatM d (2 * Real.pi ^ 2 * (6 * s)) := by
  unfold heatVsup heatCV
  ring

/-- The uniform bound of the heat kernel decreases in the time. -/
theorem heatM_anti {c c' : ℝ} (hc : 0 < c) (h : c ≤ c') (d : ℕ) : heatM d c' ≤ heatM d c := by
  unfold heatM
  exact (heat_consts_anti hc h d).1

/-- **Closed bound for the mean of the defect bound:** `heatEtaBar ≤ a/√m`. HYPOTHESES: closed
    bounds for the coefficients (`hKB`, `hcq`, supplied by `heatKB_le`, `heatCV_heatQ`) and
    `(2L + 2)(kb + M) √m ≤ θ N` (the range of `m`). -/
theorem heatEtaBar_le {σ M L δ kb θ r : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m) (hkb : 0 ≤ kb) (hr : 0 ≤ r)
    (hKB : heatKB d σ ((m : ℝ) * σ) ≤ kb)
    (hcq : heatCV d σ ((m : ℝ) * σ) * heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) ^ 2
      ≤ r ^ 2 / m)
    (hθ : (2 * L + 2) * (kb + M) * Real.sqrt m ≤ θ * N) :
    heatEtaBar d σ N m M L δ δ
      ≤ 3 * (1 + δ) * ((1 + 2 * δ) * (θ + 2 * (Real.sqrt (N * M * L) / N) * r) + 2 * δ * r)
        / Real.sqrt m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hc6 : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)) := by positivity
  have hCV := heatCV_nonneg hσ hs d
  have hQ := heatQ_nonneg hc6 d
  have hKB0 := heatKB_nonneg hσ hs d
  obtain ⟨q, hq⟩ : ∃ q, q = min ((N : ℝ) * Real.sqrt (1 + δ))
      (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ))) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact le_min (by positivity) (by positivity)
  have hqle : q ≤ heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ)) := by
    rw [hq]; exact min_le_right _ _
  -- √CV · heatQ ≤ r/√m
  have hsq : Real.sqrt (heatCV d σ ((m : ℝ) * σ))
      * heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) ≤ r / Real.sqrt m := by
    have e1 : Real.sqrt (heatCV d σ ((m : ℝ) * σ))
        * heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)))
        = Real.sqrt (heatCV d σ ((m : ℝ) * σ)
          * heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) ^ 2) := by
      rw [Real.sqrt_mul hCV, Real.sqrt_sq hQ]
    rw [e1]
    calc Real.sqrt (heatCV d σ ((m : ℝ) * σ)
          * heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) ^ 2)
        ≤ Real.sqrt (r ^ 2 / m) := Real.sqrt_le_sqrt hcq
      _ = r / Real.sqrt m := by rw [Real.sqrt_div (by positivity), Real.sqrt_sq hr]
  have hZ : Real.sqrt (heatCV d σ ((m : ℝ) * σ)) * q ≤ r / Real.sqrt m * (N * (1 + δ)) := by
    calc Real.sqrt (heatCV d σ ((m : ℝ) * σ)) * q
        ≤ Real.sqrt (heatCV d σ ((m : ℝ) * σ))
          * (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ))) :=
          mul_le_mul_of_nonneg_left hqle (Real.sqrt_nonneg _)
      _ = Real.sqrt (heatCV d σ ((m : ℝ) * σ))
          * heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ)) := by ring
      _ ≤ r / Real.sqrt m * (N * (1 + δ)) := mul_le_mul_of_nonneg_right hsq (by positivity)
  have hT : Real.sqrt (N * (M * heatCV d σ ((m : ℝ) * σ)) * L) * q
      ≤ Real.sqrt (N * M * L) * (r / Real.sqrt m * (N * (1 + δ))) := by
    have e : Real.sqrt (N * (M * heatCV d σ ((m : ℝ) * σ)) * L)
        = Real.sqrt (N * M * L) * Real.sqrt (heatCV d σ ((m : ℝ) * σ)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1; ring
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)
  have hX : heatKB d σ ((m : ℝ) * σ) * (N * (1 + δ)) + M * (N * (1 + δ))
      ≤ (kb + M) * (N * (1 + δ)) := by
    have := mul_le_mul_of_nonneg_right hKB (by positivity : (0 : ℝ) ≤ N * (1 + δ))
    linarith
  have hcore := defect_closed_core (S := Real.sqrt (N * M * L)) hNpos hL hδ hX hT hZ
  have hnum : heatDefNum d σ N m M L δ (N * (1 + δ)) (N * (1 + δ)) q
      ≤ 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * ((kb + M) * (N * (1 + δ)))
          + 2 * Real.sqrt (N * M * L) * (r / Real.sqrt m * (N * (1 + δ))))
        + 2 * δ * N * (r / Real.sqrt m * (N * (1 + δ)))) := by
    refine le_trans (le_of_eq ?_) hcore
    unfold heatDefNum
    ring
  have hu : (2 * L + 2) * (kb + M) / N ≤ θ / Real.sqrt m := by
    rw [div_le_div_iff₀ hNpos hsm]; exact hθ
  unfold heatEtaBar
  rw [← hq]
  calc heatDefNum d σ N m M L δ (N * (1 + δ)) (N * (1 + δ)) q / N
      ≤ 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * ((kb + M) * (N * (1 + δ)))
          + 2 * Real.sqrt (N * M * L) * (r / Real.sqrt m * (N * (1 + δ))))
        + 2 * δ * N * (r / Real.sqrt m * (N * (1 + δ)))) / N :=
        div_le_div_of_nonneg_right hnum hNpos.le
    _ = 3 * (1 + δ) * ((1 + 2 * δ) * ((2 * L + 2) * (kb + M) / N
          + 2 * (Real.sqrt (N * M * L) / N) * (r / Real.sqrt m)) + 2 * δ * (r / Real.sqrt m)) := by
        field_simp
    _ ≤ 3 * (1 + δ) * ((1 + 2 * δ) * (θ / Real.sqrt m
          + 2 * (Real.sqrt (N * M * L) / N) * (r / Real.sqrt m)) + 2 * δ * (r / Real.sqrt m)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ 1 + 2 * δ)
        linarith
    _ = _ := by field_simp

/-- **Closed bound for the supremum of the defect bound:** `heatDefSup ≤ b · mu_m/√m`. HYPOTHESES:
    closed bounds for the coefficients (`hKB`, `hcv`, supplied by `heatKB_le`, `heatCV_le_mu`) and
    `(2L + 2)(kb + M) √m ≤ θ N`. -/
theorem heatDefSup_le {σ M L δ kb θ c2 : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m) (hkb : 0 ≤ kb) (hc2 : 0 ≤ c2)
    (hKB : heatKB d σ ((m : ℝ) * σ) ≤ kb)
    (hcv : heatCV d σ ((m : ℝ) * σ) ≤ c2 / m * heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)))
    (hθ : (2 * L + 2) * (kb + M) * Real.sqrt m ≤ θ * N) :
    heatDefSup d σ N m M L δ
      ≤ 3 * ((1 + 2 * δ) * (θ + 2 * (Real.sqrt (N * M * L) / N) * Real.sqrt c2)
          + 2 * δ * Real.sqrt c2) * heatMu d σ m / Real.sqrt m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hcs : (0 : ℝ) < 2 * Real.pi ^ 2 * ((m : ℝ) * σ) := by positivity
  have hCV := heatCV_nonneg hσ hs d
  have hKB0 := heatKB_nonneg hσ hs d
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact heatM_nonneg d _
  have hmu : heatMu d σ m = μ := by
    unfold heatMu; rw [if_neg (by omega), hμ]
  have a1 : heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) ≤ μ := by
    rw [hμ]; exact heatM_anti hcs (by nlinarith [sq_nonneg Real.pi, Real.pi_pos]) d
  have a2 : heatM d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) ≤ μ := by
    rw [hμ]; exact heatM_anti hcs (by nlinarith [sq_nonneg Real.pi, Real.pi_pos]) d
  have a3 : heatM d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) ≤ μ := by
    rw [hμ]; exact heatM_anti hcs (by nlinarith [sq_nonneg Real.pi, Real.pi_pos]) d
  rw [← hμ] at hcv
  have hX : heatBsup d σ ((m : ℝ) * σ) M ≤ (kb + M) * μ := by
    rw [heatBsup_eq]
    have h1 : heatKB d σ ((m : ℝ) * σ) * heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ))
        ≤ kb * μ := mul_le_mul hKB a1 (heatM_nonneg d _) hkb
    have h2 := mul_le_mul_of_nonneg_left a2 hM
    linarith
  have hV : heatVsup d σ ((m : ℝ) * σ) ≤ c2 / m * μ * μ := by
    rw [heatVsup_eq]
    exact mul_le_mul hcv a3 (heatM_nonneg d _) (by positivity)
  have hV0 : 0 ≤ heatVsup d σ ((m : ℝ) * σ) := heatVsup_nonneg hσ hs d
  have hZ : Real.sqrt (heatVsup d σ ((m : ℝ) * σ)) ≤ Real.sqrt c2 / Real.sqrt m * μ := by
    calc Real.sqrt (heatVsup d σ ((m : ℝ) * σ)) ≤ Real.sqrt (c2 / m * μ * μ) :=
          Real.sqrt_le_sqrt hV
      _ = Real.sqrt c2 / Real.sqrt m * μ := by
          rw [mul_assoc, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hμ0,
            Real.sqrt_div hc2]
  have hT : Real.sqrt (N * (M * heatVsup d σ ((m : ℝ) * σ)) * L)
      ≤ Real.sqrt (N * M * L) * (Real.sqrt c2 / Real.sqrt m * μ) := by
    have e : Real.sqrt (N * (M * heatVsup d σ ((m : ℝ) * σ)) * L)
        = Real.sqrt (N * M * L) * Real.sqrt (heatVsup d σ ((m : ℝ) * σ)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)
  have hcore := defect_closed_core (S := Real.sqrt (N * M * L)) hNpos hL hδ hX hT hZ
  have hu : (2 * L + 2) * (kb + M) / N ≤ θ / Real.sqrt m := by
    rw [div_le_div_iff₀ hNpos hsm]; exact hθ
  rw [hmu]
  calc heatDefSup d σ N m M L δ
      ≤ 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * ((kb + M) * μ)
          + 2 * Real.sqrt (N * M * L) * (Real.sqrt c2 / Real.sqrt m * μ))
        + 2 * δ * N * (Real.sqrt c2 / Real.sqrt m * μ)) := by
        refine le_trans (le_of_eq ?_) hcore
        unfold heatDefSup heatThrSup
        ring
    _ = 3 * ((1 + 2 * δ) * ((2 * L + 2) * (kb + M) / N
          + 2 * (Real.sqrt (N * M * L) / N) * (Real.sqrt c2 / Real.sqrt m))
        + 2 * δ * (Real.sqrt c2 / Real.sqrt m)) * μ := by field_simp
    _ ≤ 3 * ((1 + 2 * δ) * (θ / Real.sqrt m
          + 2 * (Real.sqrt (N * M * L) / N) * (Real.sqrt c2 / Real.sqrt m))
        + 2 * δ * (Real.sqrt c2 / Real.sqrt m)) * μ := by
        refine mul_le_mul_of_nonneg_right ?_ hμ0
        have := mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ 1 + 2 * δ)
        linarith
    _ = _ := by field_simp


/-- **The summation of Step 4 of the kernel theorem, in abstract form.** If `mu_l ≤ c₀ mu_k` whenever
    `k ≤ 4l`, the mean bound satisfies `etabar_m ≤ a/√m` and the supremum bound
    `etasup_m ≤ b mu_m/√m` for `1 ≤ m < K`, then for `j + 1 < K`
    `∑_{m<j} min(2 mu_{j-m} etabar_{m+1}, etasup_{m+1}) + etasup_{j+1}
      ≤ 2 c₀ max(2a, b) √(j+1) · mu_{j+2}`. -/
theorem kernel_sum_bound (mu etabar etasup : ℕ → ℝ) {a b c0 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc0 : 0 ≤ c0) (K : ℕ) (hmu : ∀ k, 0 ≤ mu k)
    (hdoub : ∀ l k, 1 ≤ l → 1 ≤ k → k ≤ 4 * l → mu l ≤ c0 * mu k)
    (hbar : ∀ m, 1 ≤ m → m < K → etabar m ≤ a / Real.sqrt m)
    (hsup : ∀ m, 1 ≤ m → m < K → etasup m ≤ b * mu m / Real.sqrt m)
    (j : ℕ) (hj : j + 1 < K) :
    ∑ m ∈ Finset.range j, min (2 * mu (j - m) * etabar (m + 1)) (etasup (m + 1)) + etasup (j + 1)
      ≤ 2 * c0 * max (2 * a) b * Real.sqrt ((j : ℝ) + 1) * mu (j + 2) := by
  have hmax0 : 0 ≤ max (2 * a) b := le_max_of_le_right hb
  have hC0 : 0 ≤ c0 * max (2 * a) b * mu (j + 2) := mul_nonneg (mul_nonneg hc0 hmax0) (hmu _)
  have hsq : ∀ m : ℕ, 0 < Real.sqrt ((m : ℝ) + 1) := fun m => Real.sqrt_pos.mpr (by positivity)
  have hcast : ∀ m : ℕ, Real.sqrt ((m + 1 : ℕ) : ℝ) = Real.sqrt ((m : ℝ) + 1) := fun m => by
    push_cast; rfl
  -- the supremum bound in terms of mu (j+2)
  have hsupj : ∀ m, m < j + 1 → j + 2 ≤ 4 * (m + 1) →
      etasup (m + 1) ≤ c0 * max (2 * a) b * mu (j + 2) * (1 / Real.sqrt ((m : ℝ) + 1)) := by
    intro m hm h4
    have h1 := hsup (m + 1) (by omega) (by omega)
    rw [hcast] at h1
    have h2 := hdoub (m + 1) (j + 2) (by omega) (by omega) h4
    have h3 : b * mu (m + 1) ≤ max (2 * a) b * (c0 * mu (j + 2)) :=
      mul_le_mul (le_max_right _ _) h2 (hmu _) hmax0
    calc etasup (m + 1) ≤ b * mu (m + 1) / Real.sqrt ((m : ℝ) + 1) := h1
      _ ≤ max (2 * a) b * (c0 * mu (j + 2)) / Real.sqrt ((m : ℝ) + 1) :=
          div_le_div_of_nonneg_right h3 (hsq m).le
      _ = _ := by ring
  have hterm : ∀ m ∈ Finset.range j,
      min (2 * mu (j - m) * etabar (m + 1)) (etasup (m + 1))
        ≤ c0 * max (2 * a) b * mu (j + 2) * (1 / Real.sqrt ((m : ℝ) + 1)) := by
    intro m hm
    have hmj : m < j := Finset.mem_range.mp hm
    by_cases hcase : 2 * (m + 1) ≤ j + 1
    · refine (min_le_left _ _).trans ?_
      have h1 := hbar (m + 1) (by omega) (by omega)
      rw [hcast] at h1
      have h2 := hdoub (j - m) (j + 2) (by omega) (by omega) (by omega)
      have h3 : 2 * mu (j - m) * etabar (m + 1)
          ≤ 2 * mu (j - m) * (a / Real.sqrt ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) (hmu _))
      have h4 : 2 * mu (j - m) * (a / Real.sqrt ((m : ℝ) + 1))
          ≤ 2 * (c0 * mu (j + 2)) * (a / Real.sqrt ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg ha (hsq m).le)
      have h5 : 2 * (c0 * mu (j + 2)) * (a / Real.sqrt ((m : ℝ) + 1))
          = c0 * (2 * a) * mu (j + 2) * (1 / Real.sqrt ((m : ℝ) + 1)) := by ring
      have h6 : c0 * (2 * a) * mu (j + 2) * (1 / Real.sqrt ((m : ℝ) + 1))
          ≤ c0 * max (2 * a) b * mu (j + 2) * (1 / Real.sqrt ((m : ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hc0) (hmu _)
      linarith
    · exact (min_le_right _ _).trans (hsupj m (by omega) (by omega))
  have hlast := hsupj j (by omega) (by omega)
  have hs := sum_inv_sqrt_le (j + 1)
  rw [Finset.sum_range_succ] at hs
  have hs' : ∑ m ∈ Finset.range j, 1 / Real.sqrt ((m : ℝ) + 1) + 1 / Real.sqrt ((j : ℝ) + 1)
      ≤ 2 * Real.sqrt ((j : ℝ) + 1) := by
    have e : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
    rw [e] at hs
    exact hs
  calc ∑ m ∈ Finset.range j, min (2 * mu (j - m) * etabar (m + 1)) (etasup (m + 1))
        + etasup (j + 1)
      ≤ ∑ m ∈ Finset.range j, c0 * max (2 * a) b * mu (j + 2) * (1 / Real.sqrt ((m : ℝ) + 1))
        + c0 * max (2 * a) b * mu (j + 2) * (1 / Real.sqrt ((j : ℝ) + 1)) :=
        add_le_add (Finset.sum_le_sum hterm) hlast
    _ = c0 * max (2 * a) b * mu (j + 2)
          * (∑ m ∈ Finset.range j, 1 / Real.sqrt ((m : ℝ) + 1) + 1 / Real.sqrt ((j : ℝ) + 1)) := by
        rw [mul_add, Finset.mul_sum]
    _ ≤ c0 * max (2 * a) b * mu (j + 2) * (2 * Real.sqrt ((j : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hs' hC0
    _ = _ := by ring

/-- Doubling of the uniform bound of the heat kernel: `mu_l ≤ 2^d mu_k` for `1 ≤ l`, `1 ≤ k ≤ 4l`. -/
theorem heatMu_doubling {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {l k : ℕ} (hl : 1 ≤ l) (hk : 1 ≤ k)
    (hkl : k ≤ 4 * l) : heatMu d σ l ≤ 2 ^ d * heatMu d σ k := by
  have hl0 : l ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hpi := Real.pi_pos
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hklr : (k : ℝ) ≤ 4 * l := by exact_mod_cast hkl
  unfold heatMu heatM
  rw [if_neg hl0, if_neg hk0, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have e : ∀ n : ℝ, 0 < n → Real.pi / (2 * Real.pi ^ 2 * (n * σ)) = 1 / (2 * Real.pi * σ) / n :=
    fun n hn => by field_simp
  have hA : 0 < 1 / (2 * Real.pi * σ) := by positivity
  have h1 : Real.pi / (2 * Real.pi ^ 2 * ((l : ℝ) * σ))
      ≤ 4 * (Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ))) := by
    rw [e l (by linarith), e k (by linarith)]
    have h := div_le_div_of_nonneg_left hA.le (by positivity : (0 : ℝ) < k / 4)
      (by linarith : (k : ℝ) / 4 ≤ l)
    have e2 : 1 / (2 * Real.pi * σ) / ((k : ℝ) / 4) = 4 * (1 / (2 * Real.pi * σ) / k) := by
      field_simp
    linarith
  have h2 : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * ((l : ℝ) * σ)))
      ≤ 2 * Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ))) := by
    calc Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * ((l : ℝ) * σ)))
        ≤ Real.sqrt (4 * (Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ)))) := Real.sqrt_le_sqrt h1
      _ = 2 * Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ))) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]
  nlinarith [Real.sqrt_nonneg (Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ)))]


/-- The closed bound `kb` for `heatKB`. -/
noncomputable def heatKbar (d : ℕ) (σ : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi * σ) * ((Real.sqrt (4 * Real.pi) + 1) * Real.sqrt 3)) ^ d

/-- The constant `a` of the mean bound `heatEtaBar ≤ a/√m`. -/
noncomputable def heatRateA (d N : ℕ) (M L δ θ : ℝ) : ℝ :=
  3 * (1 + δ) * ((1 + 2 * δ) * (θ + 2 * (Real.sqrt (N * M * L) / N)
      * Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)))
    + 2 * δ * Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)))

/-- The constant `b` of the supremum bound `heatDefSup ≤ b mu_m/√m`. -/
noncomputable def heatRateB (d N : ℕ) (M L δ θ : ℝ) : ℝ :=
  3 * ((1 + 2 * δ) * (θ + 2 * (Real.sqrt (N * M * L) / N)
      * Real.sqrt ((d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1)))
    + 2 * δ * Real.sqrt ((d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1)))

/-- The numbers `W_k = 2 · 2^d · max(2a, b) · √k` of the kernel theorem in closed form. -/
noncomputable def heatW (d N : ℕ) (M L δ θ : ℝ) (k : ℕ) : ℝ :=
  2 * 2 ^ d * max (2 * heatRateA d N M L δ θ) (heatRateB d N M L δ θ) * Real.sqrt k

theorem heatRateA_nonneg {M L δ θ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (d N : ℕ) : 0 ≤ heatRateA d N M L δ θ := by
  unfold heatRateA
  have := cvConst_nonneg
  positivity

theorem heatRateB_nonneg {M L δ θ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (d N : ℕ) : 0 ≤ heatRateB d N M L δ θ := by
  unfold heatRateB
  have := cvConst_nonneg
  positivity

/-- **The summation hypothesis of the sharp kernel theorem, proved in closed form.** For kernel time
    `σ ≤ 1`, `K σ ≤ 1` and `(2L + 2)(kb + M) √K ≤ θ N`, the hypothesis `hsum` of
    `heat_kernel_sharp_sample` holds with `W_k = heatW k = 2 · 2^d · max(2a, b) · √k`. -/
theorem heat_hsum_closed {σ M L δ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hθ0 : 0 ≤ θ) (d N K : ℕ) (hN : 0 < N) (hKσ : (K : ℝ) * σ ≤ 1)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N) (j : ℕ) (hj : j + 1 < K) :
    ∑ m ∈ Finset.range j, min (2 * heatMu d σ (j - m) * heatEtaBar d σ N (m + 1) M L δ δ)
        (heatDefSup d σ N (m + 1) M L δ) + heatDefSup d σ N (j + 1) M L δ
      ≤ heatW d N M L δ θ (j + 1) * heatMu d σ (j + 2) := by
  have hc := cvConst_nonneg
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hrange : ∀ m : ℕ, 1 ≤ m → m < K →
      σ ≤ (m : ℝ) * σ ∧ (m : ℝ) * σ ≤ 1
        ∧ (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N := by
    intro m hm hmK
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmK' : (m : ℝ) ≤ K := by exact_mod_cast hmK.le
    refine ⟨by nlinarith, by nlinarith, ?_⟩
    have h1 : Real.sqrt m ≤ Real.sqrt K := Real.sqrt_le_sqrt hmK'
    have h2 : 0 ≤ (2 * L + 2) * (heatKbar d σ + M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hbar : ∀ m, 1 ≤ m → m < K →
      heatEtaBar d σ N m M L δ δ ≤ heatRateA d N M L δ θ / Real.sqrt m := by
    intro m hm hmK
    obtain ⟨r1, r2, r3⟩ := hrange m hm hmK
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hrc : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
        * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
    have hcq := heatCV_heatQ hσ r1 r2 d
    have e : σ / ((m : ℝ) * σ) = 1 / m := by field_simp
    rw [e] at hcq
    unfold heatRateA
    refine heatEtaBar_le hσ hM hL hδ d N m hN hm hkb0 (Real.sqrt_nonneg _)
      (by unfold heatKbar; exact heatKB_le hσ r1 hσ1 d) ?_ r3
    rw [Real.sq_sqrt hrc]
    calc _ ≤ _ := hcq
      _ = _ := by ring
  have hsup : ∀ m, 1 ≤ m → m < K →
      heatDefSup d σ N m M L δ ≤ heatRateB d N M L δ θ * heatMu d σ m / Real.sqrt m := by
    intro m hm hmK
    obtain ⟨r1, r2, r3⟩ := hrange m hm hmK
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hc2 : 0 ≤ (d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1) := by positivity
    have hcv := heatCV_le_mu hσ r1 r2 d
    have e : σ / ((m : ℝ) * σ) = 1 / m := by field_simp
    rw [e] at hcv
    unfold heatRateB
    refine heatDefSup_le hσ hM hL hδ d N m hN hm hkb0 hc2
      (by unfold heatKbar; exact heatKB_le hσ r1 hσ1 d) ?_ r3
    calc _ ≤ _ := hcv
      _ = _ := by ring
  have h := kernel_sum_bound (heatMu d σ) (fun m => heatEtaBar d σ N m M L δ δ)
    (fun m => heatDefSup d σ N m M L δ) (heatRateA_nonneg hM hL hδ hθ0 d N)
    (heatRateB_nonneg hM hL hδ hθ0 d N) (c0 := 2 ^ d) (by positivity) K (heatMu_nonneg d σ)
    (fun l k hl hk hkl => heatMu_doubling hσ d hl hk hkl) hbar hsup j hj
  unfold heatW
  have e : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
  rw [e]
  exact h

/-- The numbers `W_k` are nonnegative and increase with `k`. -/
theorem heatW_mono {M L δ θ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (d N : ℕ)
    {k k' : ℕ} (hk : k ≤ k') :
    0 ≤ heatW d N M L δ θ k ∧ heatW d N M L δ θ k ≤ heatW d N M L δ θ k' := by
  have ha := heatRateA_nonneg hM hL hδ hθ d N
  have hb := heatRateB_nonneg hM hL hδ hθ d N
  have hmax : 0 ≤ max (2 * heatRateA d N M L δ θ) (heatRateB d N M L δ θ) :=
    le_max_of_le_right hb
  unfold heatW
  refine ⟨by positivity, ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hk)) (by positivity)

/-- **Theorem "kernel" for a random sample on the torus with the rate `√k`.** Independent uniform
    points on the flat torus, kernel time `σ ≤ 1`, `K σ ≤ 1`, `δ = (ε + 2 N Lip/g)/N ≤ 1/8`. No
    hypothesis on events and no summation hypothesis. HYPOTHESES on numbers:
    `(2L + 2)(kb + M) √K ≤ θ N` and `4δ + (1 + 4δ) W_K ≤ 1` with `W_k = 2·2^d·max(2a, b)·√k`.
    CONCLUSION: except on an event of probability at most
    `(2 + 4K) · 2 g^d exp(-ε²/(4NM + 2Mε)) + 4 K N² e^{-L}`, for all `1 ≤ l ≤ K` and all entries
    `|N P^l(a,i) - p_{lσ}(x_a - x_i)| ≤ mu_l`, and for `j + 1 < K`
    `|N P^{j+2}(a,i) - p_{(j+2)σ}(x_a - x_i)| ≤ (4δ + (1 + 4δ) W_{j+1}) mu_{j+2}`. -/
theorem heat_kernel_rate_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hKσ : (K : ℝ) * σ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ K ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ δ N K (heatW d N M L δ θ) (fun j => X j ω)}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
            + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
        + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hsum := fun j hj => heat_hsum_closed hσ hσ1 hM0 hL.le hδ0 hθ0 d N K hN hKσ hθ j hj
  have hW : ∀ j, j + 1 < K → 0 ≤ heatW d N M L δ θ (j + 1)
      ∧ 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j + 1) ≤ 1 := by
    intro j hj
    obtain ⟨w0, w1⟩ := heatW_mono hM0 hL.le hδ0 hθ0 d N (by omega : j + 1 ≤ K)
    refine ⟨w0, ?_⟩
    have := mul_le_mul_of_nonneg_left w1 (by linarith : (0 : ℝ) ≤ 1 + 4 * δ)
    linarith
  subst hδ
  exact heat_kernel_sharp_sample hσ d X h_indep hX hlaw N K hN hg hMdef hLipdef hL hε hsmall
    (heatW d N M L ((ε + 2 * (N * Lip) * (1 / g)) / N) θ) hsum hW

section EigRate
open Matrix

/-- **Eigenvalues of the sampled graph on the torus with the rate `√k` of the kernel theorem.** As
    `heat_eig_sharp_sample`, with the numbers `W_k = heatW k` in closed form: no summation hypothesis.
    HYPOTHESES on numbers: `σ ≤ 1`, `K σ ≤ 1`, `(2L + 2)(kb + M) √K ≤ θ N`,
    `4δ + (1 + 4δ) W_K ≤ 1`, the tail `ht`, the size conditions `heps`, `h3`, and the two counts
    `hc1`, `hc2`. -/
theorem heat_eig_rate_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (j' : ℕ) (hj' : j' + 1 < K)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g) {M Lip L ε δ θ R eta t eps α : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (heta : 0 ≤ eta)
    (hKσ : (K : ℝ) * σ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ K ≤ 1)
    (ht : Real.exp (-((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d ≤ t)
    (heps : 3 * δ
          * ((1 + Real.sqrt (Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
            + (4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j' + 1)) * heatMu d σ (j' + 2))
        + (4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j' + 1)) * heatMu d σ (j' + 2) + t ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hc1 : (Finset.univ.filter fun f : modeSet d H =>
        α ^ (j' + 1 + 1) < modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) f.1).card ≤ j.val)
    (hc2 : j.val < (Finset.univ.filter fun f : modeSet d H =>
        α ^ (j' + 1 + 1) ≤ modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) f.1).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)) ≤ α ^ (j' + 1 + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph
          (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
          (fun i : Fin N =>
            (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (j' + 1 + 1) - α ^ (j' + 1 + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H,
                Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
          ∧ ((j' + 1 + 1 : ℕ) : ℝ) * (α ^ (j' + 1 + 1) * |hS.eigenvalues₀ j - α|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
            + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
              + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
          + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2
            * (2 * Real.exp (-(N * eta / 2) ^ 2 / (2 * N))) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hsum := fun j hj => heat_hsum_closed hσ hσ1 hM0 hL.le hδ0 hθ0 d N K hN hKσ hθ j hj
  have hW : ∀ j, j + 1 < K → 0 ≤ heatW d N M L δ θ (j + 1)
      ∧ 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j + 1) ≤ 1 := by
    intro j hj
    obtain ⟨w0, w1⟩ := heatW_mono hM0 hL.le hδ0 hθ0 d N (by omega : j + 1 ≤ K)
    refine ⟨w0, ?_⟩
    have := mul_le_mul_of_nonneg_left w1 (by linarith : (0 : ℝ) ≤ 1 + 4 * δ)
    linarith
  exact heat_eig_sharp_sample hσ d N K X h_indep hX hlaw j' hj' (heatW d N M L δ θ) H hH0 hH2 hg
    hMdef hLipdef hL hε hsmall hδ hR heta hsum hW ht heps j hα0 hα1 hc1 hc2 h3

end EigRate

/-- **Theorem "kernel" with the rate `√k` and failure probability `2/N³`.** As
    `heat_kernel_rate_sample`, with the level `L = log(4 K N⁵)` and a tolerance `ε` large enough
    that `log((2 + 4K) · 2 g^d · N³) · (4NM + 2Mε) ≤ ε²`: the conclusion fails with probability at
    most `2/N³`. -/
theorem heat_kernel_rate_prob {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    {g : ℕ} (hg : 0 < g)
    {M Lip L ε δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLdef : L = Real.log (4 * K * (N : ℝ) ^ 5)) (hε : 0 < ε)
    (hT : Real.log ((2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3) * (4 * (N * M) + 2 * M * ε)
      ≤ ε ^ 2)
    (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hKσ : (K : ℝ) * σ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ K ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ δ N K (heatW d N M L δ θ) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hN5 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ hN1
  have hLarg : (1 : ℝ) < 4 * K * (N : ℝ) ^ 5 := by nlinarith
  have hL : 0 < L := by rw [hLdef]; exact Real.log_pos hLarg
  have h := heat_kernel_rate_sample hσ hσ1 d X h_indep hX hlaw N K hN hg hMdef hLipdef hL hε hsmall
    hδ hKσ hθ0 hθ hWK
  refine h.trans ?_
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3 := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; positivity
  have hD : 0 < 4 * (N * M) + 2 * M * ε := by positivity
  rw [← hA] at hT
  have he1 : Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ 1 / A := by
    have h1 : -ε ^ 2 / (4 * (N * M) + 2 * M * ε) ≤ -Real.log A := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD]; exact hT
    calc Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ Real.exp (-Real.log A) :=
          Real.exp_le_exp.mpr h1
      _ = 1 / A := by rw [Real.exp_neg, Real.exp_log hApos, one_div]
  have he2 : Real.exp (-L) = 1 / (4 * K * (N : ℝ) ^ 5) := by
    rw [hLdef, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hp : (2 + 4 * (K : ℝ)) * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
      ≤ 1 / (N : ℝ) ^ 3 := by
    calc (2 + 4 * (K : ℝ)) * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
        ≤ (2 + 4 * (K : ℝ)) * ((g : ℝ) ^ d * (2 * (1 / A))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1 / (N : ℝ) ^ 3 := by rw [hA]; field_simp
  have hq : (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) = 1 / (2 * (N : ℝ) ^ 3) := by
    rw [he2]; field_simp; ring
  have e3 : 2 / (N : ℝ) ^ 3 = 1 / (N : ℝ) ^ 3 + (1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3)) := by
    field_simp; ring
  rw [hq, e3]
  linarith

/-- The number of elements of a subtype of a finset that satisfy a predicate on the value. -/
theorem card_filter_subtype {α : Type*} [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun f : s => p f.1).card = (s.filter p).card := by
  rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
  congr 1
  ext a
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact ⟨f.2, hf⟩
  · rintro ⟨ha, hp⟩; exact ⟨⟨a, ha⟩, hp, rfl⟩

/-- **The counts for the first shell of modes.** `H` a set of frequencies with `|n|² ≥ r > 0` for all
    `n ∈ H`, `E` the frequencies of `H` with `|n|² = r`, `c > 0`. Then exactly one coefficient of the
    modes exceeds `e^{-cr}` (the constant), and at least `2|E| + 1` coefficients are at least
    `e^{-cr}`. -/
theorem mode_counts_shell (d : ℕ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (H : Finset (Fin d → ℤ))
    (hall : ∀ n ∈ H, r ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) :
    (Finset.univ.filter fun f : modeSet d H => Real.exp (-c * r) < modeCoeff d c f.1).card ≤ 1
      ∧ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r).card + 1
        ≤ (Finset.univ.filter fun f : modeSet d H => Real.exp (-c * r) ≤ modeCoeff d c f.1).card := by
  classical
  rw [card_filter_subtype (modeSet d H) (fun f => Real.exp (-c * r) < modeCoeff d c f),
    card_filter_subtype (modeSet d H) (fun f => Real.exp (-c * r) ≤ modeCoeff d c f)]
  constructor
  · have hsub : (modeSet d H).filter (fun f => Real.exp (-c * r) < modeCoeff d c f) ⊆ {none} := by
      intro f hf
      rw [Finset.mem_filter] at hf
      rcases f with _ | ⟨n, b⟩
      · simp
      · exfalso
        have hn : n ∈ H := (mem_modeSet d H n b).mp hf.1
        have h1 := hall n hn
        have h2 : modeCoeff d c (some (n, b)) ≤ Real.exp (-c * r) := by
          simp only [modeCoeff]
          apply Real.exp_le_exp.mpr
          nlinarith
        exact absurd hf.2 (not_lt.mpr h2)
    exact (Finset.card_le_card hsub).trans (by simp)
  · obtain ⟨E, hE⟩ : ∃ E : Finset (Fin d → ℤ),
        E = H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r := ⟨_, rfl⟩
    rw [← hE]
    have hEH : ∀ n ∈ E, n ∈ H ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r := fun n hn => by
      rw [hE, Finset.mem_filter] at hn; exact hn
    have inj : ∀ b : Bool, Function.Injective fun n : Fin d → ℤ =>
        (some (n, b) : Option ((Fin d → ℤ) × Bool)) := fun b n n' h => by
      simpa using h
    have hsub : insert none ((E.image fun n => some (n, false)) ∪ (E.image fun n => some (n, true)))
        ⊆ (modeSet d H).filter (fun f => Real.exp (-c * r) ≤ modeCoeff d c f) := by
      intro f hf
      rw [Finset.mem_filter]
      rcases f with _ | ⟨n, b⟩
      · refine ⟨by unfold modeSet; simp, ?_⟩
        simp only [modeCoeff]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      · have hn : n ∈ E := by
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Option.some.injEq,
            Prod.mk.injEq, reduceCtorEq, false_or] at hf
          rcases hf with ⟨m, hm, rfl, -⟩ | ⟨m, hm, rfl, -⟩ <;> exact hm
        refine ⟨(mem_modeSet d H n b).mpr (hEH n hn).1, ?_⟩
        simp only [modeCoeff]
        rw [(hEH n hn).2]
    have hdisj : Disjoint (E.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
        (E.image fun n => some (n, true)) := by
      rw [Finset.disjoint_left]
      intro f hf hf'
      simp only [Finset.mem_image] at hf hf'
      obtain ⟨m, -, rfl⟩ := hf
      obtain ⟨m', -, h⟩ := hf'
      simp at h
    have hnone : (none : Option ((Fin d → ℤ) × Bool))
        ∉ (E.image fun n => some (n, false)) ∪ (E.image fun n => some (n, true)) := by
      simp
    have hcard : (insert none ((E.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
        ∪ (E.image fun n => some (n, true)))).card = 2 * E.card + 1 := by
      rw [Finset.card_insert_of_notMem hnone, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (inj false), Finset.card_image_of_injective _ (inj true)]
      ring
    rw [← hcard]
    exact Finset.card_le_card hsub

section EigShell
open Matrix

/-- **The first shell of eigenvalues of the sampled graph on the torus, with the rate `√k`.** As
    `heat_eig_rate_sample` with `α = e^{-cr}`, `c = 2π²σ`, where `r > 0` is a lower bound for `|n|²`
    on `H` and `E` is the set of frequencies of `H` with `|n|² = r`: for `1 ≤ j ≤ 2|E|` the two
    counts are proved (`mode_counts_shell`), so no hypothesis on the position of `α^{k+1}` among the
    coefficients remains. -/
theorem heat_eig_rate_shell {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (j' : ℕ) (hj' : j' + 1 < K)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g) {M Lip L ε δ θ R eta t eps r : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (heta : 0 ≤ eta)
    (hKσ : (K : ℝ) * σ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ K ≤ 1)
    (ht : Real.exp (-((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d ≤ t)
    (heps : 3 * δ
          * ((1 + Real.sqrt (Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
            + (4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j' + 1)) * heatMu d σ (j' + 2))
        + (4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j' + 1)) * heatMu d σ (j' + 2) + t ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hr : 0 < r)
    (hall : ∀ n ∈ H, r ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hj1 : 1 ≤ j.val)
    (hj2 : j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)) ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph
          (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
          (fun i : Fin N =>
            (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (j' + 1 + 1) - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H,
                Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
          ∧ ((j' + 1 + 1 : ℕ) : ℝ) * (Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1) * |hS.eigenvalues₀ j - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
            + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
              + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
          + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2
            * (2 * Real.exp (-(N * eta / 2) ^ 2 / (2 * N))) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hc' : 0 < ((j' + 1 + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ) := by positivity
  have hpow : Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1)
      = Real.exp (-(((j' + 1 + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ)) * r) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨c1, c2⟩ := mode_counts_shell d hc' hr H hall
  refine heat_eig_rate_sample hσ hσ1 d N K X h_indep hX hlaw j' hj' H hH0 hH2 hg hMdef hLipdef hL hε
    hsmall hδ hR heta hKσ hθ0 hθ hWK ht heps j (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hc hr])) ?_ ?_ h3
  · rw [hpow]; exact c1.trans hj1
  · rw [hpow]; exact lt_of_lt_of_le (by omega) c2

end EigShell

/-- The conclusion of the kernel theorem is monotone in the normalisation error and in the
    numbers `W`. -/
theorem heatKernelSharp_mono {d N K : ℕ} {σ δ δ' : ℝ} {W W' : ℕ → ℝ} (x : ℕ → FlatTorus d)
    (h : heatKernelSharp d σ δ N K W x) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ')
    (hW : ∀ j, 0 ≤ W j ∧ W j ≤ W' j) : heatKernelSharp d σ δ' N K W' x := by
  refine ⟨h.1, fun j hj a i => (h.2 j hj a i).trans ?_⟩
  refine mul_le_mul_of_nonneg_right ?_ (heatMu_nonneg d σ _)
  have h1 := (hW (j + 1)).1
  have h2 := (hW (j + 1)).2
  have h3 : (1 + 4 * δ) * W (j + 1) ≤ (1 + 4 * δ') * W' (j + 1) :=
    mul_le_mul (by linarith) h2 h1 (by linarith)
  linarith

/-- The numbers `W_k` increase with the normalisation error `δ`. -/
theorem heatW_mono_delta {M L δ δ' θ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ')
    (hθ : 0 ≤ θ) (d N k : ℕ) : heatW d N M L δ θ k ≤ heatW d N M L δ' θ k := by
  have hc := cvConst_nonneg
  have hδ'0 : 0 ≤ δ' := hδ0.trans hδ
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (N * M * L) / N := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have key : ∀ r : ℝ, 0 ≤ r →
      (1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r ≤ (1 + 2 * δ') * (θ + 2 * S * r) + 2 * δ' * r := by
    intro r hr
    have h1 : 0 ≤ θ + 2 * S * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hδ h1, mul_le_mul_of_nonneg_right hδ hr]
  have key0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ (1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r := by
    intro r hr; positivity
  have hA : heatRateA d N M L δ θ ≤ heatRateA d N M L δ' θ := by
    unfold heatRateA
    rw [← hS]
    have hr : 0 ≤ Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
        * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)) := Real.sqrt_nonneg _
    have h1 := key _ hr
    have h0 := key0 _ hr
    have h2 : 3 * (1 + δ) ≤ 3 * (1 + δ') := by linarith
    exact mul_le_mul h2 h1 h0 (by linarith)
  have hB : heatRateB d N M L δ θ ≤ heatRateB d N M L δ' θ := by
    unfold heatRateB
    rw [← hS]
    have hr : 0 ≤ Real.sqrt ((d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1)) := Real.sqrt_nonneg _
    have h1 := key _ hr
    linarith
  unfold heatW
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left (max_le_max (by linarith) hB) (by positivity)

/-- **Theorem "kernel" with the rate `√k`, all parameters explicit.** Independent uniform points on
    the flat torus, kernel time `σ ≤ 1`, `K σ ≤ 1`, grid parameter `g`. With
    `T = log((2 + 4K) · 2 g^d · N³)`, `L = log(4 K N⁵)`, `δ = 6 √(N M T)/N` and
    `θ = (2L + 2)(kb + M) √K / N`, under the three inequalities
    `2 N Lip/g ≤ 3 √(N M T)`, `6 √(N M T) ≤ N/8` and `4δ + (1 + 4δ) W_K ≤ 1`, the conclusion of
    the kernel theorem with `W_k = 2·2^d·max(2a, b)·√k` fails with probability at most `2/N³`. -/
theorem heat_kernel_rate_explicit {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    {g : ℕ} (hg : 0 < g)
    {M Lip L T δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLdef : L = Real.log (4 * K * (N : ℝ) ^ 5))
    (hTdef : T = Real.log ((2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3))
    (hδdef : δ = 6 * Real.sqrt (N * M * T) / N)
    (hθdef : θ = (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K / N)
    (hgc : 2 * (N * Lip) * (1 / g) ≤ 3 * Real.sqrt (N * M * T))
    (hsm : 6 * Real.sqrt (N * M * T) ≤ N / 8)
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ K ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ δ N K (heatW d N M L δ θ) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hLarg : (1 : ℝ) < 4 * K * (N : ℝ) ^ 5 := by nlinarith [one_le_pow₀ hN1 (n := 5)]
  have hL : 0 < L := by rw [hLdef]; exact Real.log_pos hLarg
  have hTarg : (1 : ℝ) < (2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (g : ℝ) ^ d := one_le_pow₀ hg1
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
    have h3 : (6 : ℝ) ≤ 2 + 4 * K := by linarith
    have h4 : (2 : ℝ) ≤ 2 * (g : ℝ) ^ d := by linarith
    have h5 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * (g : ℝ) ^ d) := by nlinarith
    nlinarith
  have hT : 0 < T := by rw [hTdef]; exact Real.log_pos hTarg
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * M * T) := ⟨_, rfl⟩
  have hsq : 0 < Real.sqrt (N * M * T) := Real.sqrt_pos.mpr (by positivity)
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε2 : ε ^ 2 = 9 * (N * M * T) := by
    rw [hεdef, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hεN : ε ≤ N / 16 := by rw [hεdef]; linarith
  have hTcond : Real.log ((2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3)
      * (4 * (N * M) + 2 * M * ε) ≤ ε ^ 2 := by
    rw [← hTdef, hε2]
    have h1 : 2 * M * ε * T ≤ 5 * (N * M * T) := by
      have : ε ≤ 5 * N / 2 := by linarith
      have hMT : 0 ≤ M * T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hMT]
    nlinarith
  have hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8 := by rw [hεdef]; linarith
  obtain ⟨δ0, hδ0def⟩ : ∃ δ0 : ℝ, δ0 = (ε + 2 * (N * Lip) * (1 / g)) / N := ⟨_, rfl⟩
  have hδ00 : 0 ≤ δ0 := by rw [hδ0def]; positivity
  have hδ0le : δ0 ≤ δ := by
    rw [hδ0def, hδdef]
    apply div_le_div_of_nonneg_right _ hNpos.le
    rw [hεdef]; linarith
  have hδpos : 0 ≤ δ := hδ00.trans hδ0le
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N := by
    rw [hθdef, div_mul_cancel₀ _ hNpos.ne']
  have hWmono := fun k => heatW_mono_delta hMpos.le hL.le hδ00 hδ0le hθ0 d N k
  have hWK0 : 4 * δ0 + (1 + 4 * δ0) * heatW d N M L δ0 θ K ≤ 1 := by
    have w0 := (heatW_mono hMpos.le hL.le hδ00 hθ0 d N (le_refl K)).1
    have h3 : (1 + 4 * δ0) * heatW d N M L δ0 θ K ≤ (1 + 4 * δ) * heatW d N M L δ θ K :=
      mul_le_mul (by linarith) (hWmono K) w0 (by linarith)
    linarith
  have h := heat_kernel_rate_prob hσ hσ1 d X h_indep hX hlaw N K hN hK hg hMdef hLipdef hLdef hε
    hTcond hsmall hδ0def hKσ hθ0 hθ hWK0
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  exact hω (heatKernelSharp_mono (fun j => X j ω) hgood hδ00 hδ0le
    (fun j => ⟨(heatW_mono hMpos.le hL.le hδ00 hθ0 d N (le_refl j)).1, hWmono j⟩))

section EigShells
open Matrix

/-- **The counts for an arbitrary shell of modes.** `H` a set of frequencies, `c, r > 0`. At most
    `1 + 2 #{n ∈ H : |n|² < r}` coefficients of the modes exceed `e^{-cr}`, and at least
    `2 #{n ∈ H : |n|² ≤ r} + 1` coefficients are at least `e^{-cr}`. -/
theorem mode_counts_general (d : ℕ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) (H : Finset (Fin d → ℤ)) :
    (Finset.univ.filter fun f : modeSet d H => Real.exp (-c * r) < modeCoeff d c f.1).card
        ≤ 1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card
      ∧ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card + 1
        ≤ (Finset.univ.filter fun f : modeSet d H => Real.exp (-c * r) ≤ modeCoeff d c f.1).card := by
  classical
  rw [card_filter_subtype (modeSet d H) (fun f => Real.exp (-c * r) < modeCoeff d c f),
    card_filter_subtype (modeSet d H) (fun f => Real.exp (-c * r) ≤ modeCoeff d c f)]
  have inj : ∀ b : Bool, Function.Injective fun n : Fin d → ℤ =>
      (some (n, b) : Option ((Fin d → ℤ) × Bool)) := fun b n n' h => by
    simpa using h
  constructor
  · obtain ⟨A, hA⟩ : ∃ A : Finset (Fin d → ℤ),
        A = H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r := ⟨_, rfl⟩
    rw [← hA]
    have hsub : (modeSet d H).filter (fun f => Real.exp (-c * r) < modeCoeff d c f)
        ⊆ insert none ((A.image fun n => some (n, false)) ∪ (A.image fun n => some (n, true))) := by
      intro f hf
      rw [Finset.mem_filter] at hf
      rcases f with _ | ⟨n, b⟩
      · simp
      · have hn : n ∈ H := (mem_modeSet d H n b).mp hf.1
        have h2 := hf.2
        simp only [modeCoeff] at h2
        have h3 := Real.exp_lt_exp.mp h2
        have hnA : n ∈ A := by
          rw [hA, Finset.mem_filter]; exact ⟨hn, by nlinarith⟩
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Option.some.injEq,
          Prod.mk.injEq, reduceCtorEq, false_or]
        cases b
        · exact Or.inl ⟨n, hnA, rfl, rfl⟩
        · exact Or.inr ⟨n, hnA, rfl, rfl⟩
    refine (Finset.card_le_card hsub).trans ?_
    refine (Finset.card_insert_le _ _).trans ?_
    have h1 := Finset.card_union_le (A.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
      (A.image fun n => some (n, true))
    have h2 := Finset.card_image_le (s := A)
      (f := fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
    have h3 := Finset.card_image_le (s := A)
      (f := fun n => (some (n, true) : Option ((Fin d → ℤ) × Bool)))
    omega
  · obtain ⟨E, hE⟩ : ∃ E : Finset (Fin d → ℤ),
        E = H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r := ⟨_, rfl⟩
    rw [← hE]
    have hEH : ∀ n ∈ E, n ∈ H ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r := fun n hn => by
      rw [hE, Finset.mem_filter] at hn; exact hn
    have hsub : insert none ((E.image fun n => some (n, false)) ∪ (E.image fun n => some (n, true)))
        ⊆ (modeSet d H).filter (fun f => Real.exp (-c * r) ≤ modeCoeff d c f) := by
      intro f hf
      rw [Finset.mem_filter]
      rcases f with _ | ⟨n, b⟩
      · refine ⟨by unfold modeSet; simp, ?_⟩
        simp only [modeCoeff]
        exact Real.exp_le_one_iff.mpr (by nlinarith)
      · have hn : n ∈ E := by
          simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image, Option.some.injEq,
            Prod.mk.injEq, reduceCtorEq, false_or] at hf
          rcases hf with ⟨m, hm, rfl, -⟩ | ⟨m, hm, rfl, -⟩ <;> exact hm
        refine ⟨(mem_modeSet d H n b).mpr (hEH n hn).1, ?_⟩
        simp only [modeCoeff]
        apply Real.exp_le_exp.mpr
        nlinarith [(hEH n hn).2]
    have hdisj : Disjoint (E.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
        (E.image fun n => some (n, true)) := by
      rw [Finset.disjoint_left]
      intro f hf hf'
      simp only [Finset.mem_image] at hf hf'
      obtain ⟨m, -, rfl⟩ := hf
      obtain ⟨m', -, h⟩ := hf'
      simp at h
    have hnone : (none : Option ((Fin d → ℤ) × Bool))
        ∉ (E.image fun n => some (n, false)) ∪ (E.image fun n => some (n, true)) := by
      simp
    have hcard : (insert none ((E.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
        ∪ (E.image fun n => some (n, true)))).card = 2 * E.card + 1 := by
      rw [Finset.card_insert_of_notMem hnone, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (inj false), Finset.card_image_of_injective _ (inj true)]
      ring
    rw [← hcard]
    exact Finset.card_le_card hsub

/-- From the bound for `s - α` to the eigenvalue of the graph Laplacian `(1 - s)/τ`. -/
theorem eig_lambda_form {s α E τ : ℝ} {n : ℕ} (hn : 0 < n) (hτ : 0 < τ) (hα : 0 < α)
    (h : (n : ℝ) * (α ^ n * |s - α|) ≤ E) :
    |(1 - s) / τ - (1 - α) / τ| ≤ E / ((n : ℝ) * α ^ n * τ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hαn : 0 < α ^ n := pow_pos hα n
  have e : (1 - s) / τ - (1 - α) / τ = -(s - α) / τ := by ring
  rw [e, abs_div, abs_neg, abs_of_pos hτ, div_le_div_iff₀ hτ (by positivity)]
  nlinarith [abs_nonneg (s - α), mul_le_mul_of_nonneg_right h hτ.le]

/-- **Every shell of eigenvalues of the sampled graph on the torus below the cut-off of `H`, with
    the rate `√k`.** As `heat_eig_rate_shell`, for an arbitrary `r > 0`: the statement holds for the
    indices `1 + 2 #{n ∈ H : |n|² < r} ≤ j ≤ 2 #{n ∈ H : |n|² ≤ r}`, that is, for the eigenvalues that
    correspond to the shell `|n|² = r` counted with multiplicity (each frequency of the half-set `H`
    twice), with `α = e^{-2π²σ r}`. -/
theorem heat_eig_rate_shells {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (j' : ℕ) (hj' : j' + 1 < K)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g) {M Lip L ε δ θ R eta t eps r : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (heta : 0 ≤ eta)
    (hKσ : (K : ℝ) * σ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ K ≤ 1)
    (ht : Real.exp (-((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d ≤ t)
    (heps : 3 * δ
          * ((1 + Real.sqrt (Real.pi / ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
            + (4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j' + 1)) * heatMu d σ (j' + 2))
        + (4 * δ + (1 + 4 * δ) * heatW d N M L δ θ (j' + 1)) * heatMu d σ (j' + 2) + t ≤ eps)
    (j : Fin (Fintype.card (Fin N))) (hr : 0 < r)
    (hj1 : 1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val)
    (hj2 : j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card)
    (h3 : 2 * (eps + eta * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)) ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1)) :
    μ.real {ω | ¬ ∀ hS : (symGraph
          (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
          (fun i : Fin N =>
            (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian,
        |hS.eigenvalues₀ j ^ (j' + 1 + 1) - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1)|
            ≤ eps + eta * 1 * ∑ g : modeSet d H,
                Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
          ∧ ((j' + 1 + 1 : ℕ) : ℝ) * (Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1) * |hS.eigenvalues₀ j - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)|)
              ≤ 2 * (eps + eta * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((j' + 1 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
            + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
              + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
          + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2
            * (2 * Real.exp (-(N * eta / 2) ^ 2 / (2 * N))) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hc' : 0 < ((j' + 1 + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ) := by positivity
  have hpow : Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (j' + 1 + 1)
      = Real.exp (-(((j' + 1 + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ)) * r) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨c1, c2⟩ := mode_counts_general d hc' hr H
  refine heat_eig_rate_sample hσ hσ1 d N K X h_indep hX hlaw j' hj' H hH0 hH2 hg hMdef hLipdef hL hε
    hsmall hδ hR heta hKσ hθ0 hθ hWK ht heps j (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hc hr])) ?_ ?_ h3
  · rw [hpow]; exact c1.trans hj1
  · rw [hpow]; exact lt_of_lt_of_le (by omega) c2

end EigShells

section RatePaper
open Matrix

/-- Constant in `heatKbar ≤ rateCK · M`. -/
noncomputable def rateCK (d : ℕ) : ℝ := ((Real.sqrt (4 * Real.pi) + 1) * Real.sqrt 3) ^ d

/-- The constant `r` of the mean bound. -/
noncomputable def rateRA (d : ℕ) : ℝ :=
  Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6) * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1))

/-- The constant `r'` of the supremum bound. -/
noncomputable def rateRB (d : ℕ) : ℝ := Real.sqrt ((d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1))

/-- The constant of the kernel theorem in the form `D_k ≤ C δ' √k mu_k`. -/
noncomputable def rateCfin (d : ℕ) : ℝ :=
  48 * Real.sqrt ((d : ℝ) + 5)
    + 3 * 2 ^ d * max
        (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
          + 12 * Real.sqrt ((d : ℝ) + 5) * rateRA d)))
        (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRB d)
          + 12 * Real.sqrt ((d : ℝ) + 5) * rateRB d))

theorem heatKbar_le_M {σ : ℝ} (hσ : 0 < σ) (d : ℕ) :
    heatKbar d σ ≤ rateCK d * (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d := by
  have hpi := Real.pi_pos
  have e : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ)) = 1 / Real.sqrt (2 * Real.pi * σ) := by
    have e1 : Real.pi / (2 * Real.pi ^ 2 * σ) = 1 / (2 * Real.pi * σ) := by field_simp
    rw [e1, Real.sqrt_div (by norm_num), Real.sqrt_one]
  unfold heatKbar rateCK
  rw [e, mul_pow, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by linarith) d

/-- Bounds for the two rate constants in terms of `δ'`. -/
theorem rate_ab_bound {δ θ S r δp θ1 Aa : ℝ} (hδ0 : 0 ≤ δ) (hδ8 : δ ≤ 1 / 8)
    (hδ : δ ≤ 6 * Aa * δp) (hθ0 : 0 ≤ θ) (hθ : θ ≤ θ1 * δp) (hS0 : 0 ≤ S)
    (hS : S ≤ Real.sqrt 7 * δp) (hr : 0 ≤ r) (hδp : 0 ≤ δp) (hθ1 : 0 ≤ θ1) (hAa : 0 ≤ Aa) :
    3 * (1 + δ) * ((1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r)
        ≤ 3 * (9 / 8) * ((5 / 4) * (θ1 + 2 * Real.sqrt 7 * r) + 12 * Aa * r) * δp
      ∧ 3 * ((1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r)
        ≤ 3 * ((5 / 4) * (θ1 + 2 * Real.sqrt 7 * r) + 12 * Aa * r) * δp := by
  have h7 : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _
  have hU : θ + 2 * S * r ≤ (θ1 + 2 * Real.sqrt 7 * r) * δp := by
    have := mul_le_mul_of_nonneg_right hS hr
    nlinarith
  have hU0 : 0 ≤ θ + 2 * S * r := by positivity
  have h1 : (1 + 2 * δ) * (θ + 2 * S * r) ≤ 5 / 4 * ((θ1 + 2 * Real.sqrt 7 * r) * δp) :=
    mul_le_mul (by linarith) hU hU0 (by norm_num)
  have h2 : 2 * δ * r ≤ 12 * Aa * r * δp := by
    have := mul_le_mul_of_nonneg_right hδ hr
    nlinarith
  have hX : (1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r
      ≤ ((5 / 4) * (θ1 + 2 * Real.sqrt 7 * r) + 12 * Aa * r) * δp := by nlinarith
  have hX0 : 0 ≤ (1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r := by positivity
  constructor
  · have := mul_le_mul (by linarith : 1 + δ ≤ 9 / 8) hX hX0 (by norm_num)
    nlinarith
  · nlinarith

set_option maxHeartbeats 1600000 in
/-- **Theorem "kernel" in the form `D_k ≤ C δ' √k mu_k`.** Independent uniform points on the flat
    torus, `σ ≤ 1` the variance of the Gaussian kernel, `K σ ≤ 1`, `1 ≤ K ≤ N`, `N ≥ 12`,
    `δ' = √(M log N / N)`. HYPOTHESES on numbers: `2 Lip ≤ 3 √(N M log N)` and the smallness
    condition `C δ' √K ≤ 1` with the explicit constant `C = rateCfin d` depending only on `d`. Then,
    except on an event of probability at most `2/N³`, for all `2 ≤ k ≤ K` and all entries
    `|N P^k(a,i) - p_{kσ}(x_a - x_i)| ≤ C δ' √k mu_k`. -/
theorem heat_kernel_rate_paper {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ rateCfin d * δp * Real.sqrt k * heatMu d σ k}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hN : 0 < N := by omega
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hpi := Real.pi_pos
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hc := cvConst_nonneg
  -- logarithms
  obtain ⟨lg, hlg⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  rw [← hlg] at hδp hLipc
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log ((2 + 4 * K) * (2 * ((N : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (4 * K * (N : ℝ) ^ 5) := ⟨_, rfl⟩
  have hNd : (1 : ℝ) ≤ (N : ℝ) ^ d := one_le_pow₀ (by linarith)
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hargpos : 0 < (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3 := by positivity
  have hTle : T ≤ ((d : ℝ) + 5) * lg := by
    have h1 : (2 + 4 * (K : ℝ)) * 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (d + 5) := by
      calc (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3
          = ((2 + 4 * (K : ℝ)) * 2) * ((N : ℝ) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (d + 5) := by ring
    rw [hT, hlg]
    calc Real.log ((2 + 4 * (K : ℝ)) * (2 * ((N : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3)
        ≤ Real.log ((N : ℝ) ^ (d + 5)) := Real.log_le_log hargpos h2
      _ = ((d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hTge : lg ≤ T := by
    rw [hT, hlg]
    refine Real.log_le_log hNpos ?_
    have h6 : (6 : ℝ) ≤ 2 + 4 * K := by linarith
    have h2 : (2 : ℝ) ≤ 2 * (N : ℝ) ^ d := by linarith
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (N : ℝ)]
    have h12 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * (N : ℝ) ^ d) := by nlinarith
    have h13 := mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
    linarith
  have hLle : L ≤ 7 * lg := by
    have h1 : 4 * (K : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 7 := by
      calc 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ 7 := by ring
    rw [hL, hlg]
    calc Real.log (4 * (K : ℝ) * (N : ℝ) ^ 5) ≤ Real.log ((N : ℝ) ^ 7) :=
          Real.log_le_log (by positivity) h2
      _ = 7 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos
    have : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hTpos : 0 < T := by linarith
  -- δ' and the square roots
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * M * lg) := ⟨_, rfl⟩
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hQeq : Q = δp * N := by
    have hsq : (δp * N) ^ 2 = N * M * lg := by
      rw [mul_pow, hδp, Real.sq_sqrt (by positivity)]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt ((d : ℝ) + 5) := ⟨_, rfl⟩
  have hAa0 : 0 ≤ Aa := by rw [hAa]; exact Real.sqrt_nonneg _
  have hAa1 : 1 ≤ Aa := by
    rw [hAa, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hsqT : Real.sqrt (N * M * T) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ N * M)
    exact this.trans (le_of_eq (by ring))
  have hsqTge : Q ≤ Real.sqrt (N * M * T) := by
    rw [hQ]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTge (by positivity))
  -- the constant
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = rateCfin d := ⟨_, rfl⟩
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRB d)
        + 12 * Aa * rateRB d)) := ⟨_, rfl⟩
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hRB0 : 0 ≤ rateRB d := Real.sqrt_nonneg _
  have hmx0 : 0 ≤ mx := by rw [hmx]; exact le_max_of_le_right (by positivity)
  have hCfeq : Cf = 48 * Aa + 3 * 2 ^ d * mx := by rw [hCf, hmx, hAa]; unfold rateCfin; rfl
  rw [← hCf] at hsmall
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hCf48 : 48 * Aa ≤ Cf := by
    rw [hCfeq]
    have : 0 ≤ 3 * 2 ^ d * mx := by positivity
    linarith
  have hCf0 : 0 ≤ Cf := by linarith
  have h48 : 48 * Aa * δp ≤ 1 := by
    have h1 : 48 * Aa * δp ≤ Cf * δp := mul_le_mul_of_nonneg_right hCf48 hδp0
    have h2 : Cf * δp ≤ Cf * δp * Real.sqrt K :=
      le_mul_of_one_le_right (mul_nonneg hCf0 hδp0) hsK1
    linarith
  have hδK : δp * Real.sqrt K ≤ 1 := by
    have h1 : 1 * (δp * Real.sqrt K) ≤ Cf * (δp * Real.sqrt K) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : Cf * (δp * Real.sqrt K) = Cf * δp * Real.sqrt K := by ring
    linarith
  -- the parameters of the explicit theorem
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 6 * Real.sqrt (N * M * T) / N := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K / N := ⟨_, rfl⟩
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδle : δ ≤ 6 * Aa * δp := by
    rw [hδ, div_le_iff₀ hNpos]
    calc 6 * Real.sqrt (N * M * T) ≤ 6 * (Aa * Q) := by linarith
      _ = 6 * Aa * δp * N := by rw [hQeq]; ring
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hsm : 6 * Real.sqrt (N * M * T) ≤ N / 8 := by
    have : 6 * Real.sqrt (N * M * T) = δ * N := by rw [hδ]; field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hδ8 hNpos.le
    linarith
  have hgc : 2 * (N * Lip) * (1 / ((N : ℕ) : ℝ)) ≤ 3 * Real.sqrt (N * M * T) := by
    have e : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ)) = 2 * Lip := by field_simp
    rw [e]
    calc 2 * Lip ≤ 3 * Q := by rw [hQ]; exact hLipc
      _ ≤ 3 * Real.sqrt (N * M * T) := by linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθle : θ ≤ 16 * (rateCK d + 1) * δp := by
    have hkb := heatKbar_le_M hσ d
    rw [← hMdef] at hkb
    have h1 : 2 * L + 2 ≤ 16 * lg := by linarith
    have h2 : heatKbar d σ + M ≤ (rateCK d + 1) * M := by linarith
    have h3 : (2 * L + 2) * (heatKbar d σ + M) ≤ 16 * lg * ((rateCK d + 1) * M) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have hδp2 : δp ^ 2 = M * lg / N := by rw [hδp, Real.sq_sqrt (by positivity)]
    rw [hθ, div_le_iff₀ hNpos]
    calc (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K
        ≤ 16 * lg * ((rateCK d + 1) * M) * Real.sqrt K :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = 16 * (rateCK d + 1) * (δp ^ 2 * N) * Real.sqrt K := by rw [hδp2]; field_simp
      _ = 16 * (rateCK d + 1) * δp * N * (δp * Real.sqrt K) := by ring
      _ ≤ 16 * (rateCK d + 1) * δp * N * 1 :=
          mul_le_mul_of_nonneg_left hδK (by positivity)
      _ = 16 * (rateCK d + 1) * δp * N := by ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (N * M * L) / N := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hSle : S ≤ Real.sqrt 7 * δp := by
    rw [hS, div_le_iff₀ hNpos]
    calc Real.sqrt (N * M * L) ≤ Real.sqrt (7 * (N * M * lg)) := by
          apply Real.sqrt_le_sqrt
          have := mul_le_mul_of_nonneg_left hLle (by positivity : (0 : ℝ) ≤ N * M)
          exact this.trans (le_of_eq (by ring))
      _ = Real.sqrt 7 * Q := by rw [hQ, Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 7 * δp * N := by rw [hQeq]; ring
  have habA := (rate_ab_bound hδ0 hδ8 hδle hθ0 hθle hS0 hSle hRA0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).1
  have habB := (rate_ab_bound hδ0 hδ8 hδle hθ0 hθle hS0 hSle hRB0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).2
  have hA : heatRateA d N M L δ θ
      ≤ 3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d) * δp := by
    unfold heatRateA; rw [← hS]; exact habA
  have hB : heatRateB d N M L δ θ
      ≤ 3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRB d)
        + 12 * Aa * rateRB d) * δp := by
    unfold heatRateB; rw [← hS]; exact habB
  have hmaxle : max (2 * heatRateA d N M L δ θ) (heatRateB d N M L δ θ) ≤ mx * δp := by
    rw [hmx, max_mul_of_nonneg _ _ hδp0]
    exact max_le_max (by linarith) hB
  have hWle : ∀ k : ℕ, heatW d N M L δ θ k ≤ 2 * 2 ^ d * (mx * δp) * Real.sqrt k := by
    intro k
    unfold heatW
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmaxle (by positivity)) (Real.sqrt_nonneg _)
  have hW0 : ∀ k : ℕ, 0 ≤ heatW d N M L δ θ k := fun k =>
    (heatW_mono hMpos.le hLpos.le hδ0 hθ0 d N (le_refl k)).1
  have hrel : ∀ k : ℕ, 1 ≤ k →
      4 * δ + (1 + 4 * δ) * heatW d N M L δ θ k ≤ Cf * δp * Real.sqrt k := by
    intro k hk
    have hk1 : 1 ≤ Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
    have h1 : (1 + 4 * δ) * heatW d N M L δ θ k
        ≤ 3 / 2 * (2 * 2 ^ d * (mx * δp) * Real.sqrt k) :=
      mul_le_mul (by linarith) (hWle k) (hW0 k) (by norm_num)
    have h2 : 4 * δ ≤ 24 * Aa * δp * Real.sqrt k := by
      have : 24 * Aa * δp ≤ 24 * Aa * δp * Real.sqrt k :=
        le_mul_of_one_le_right (by positivity) hk1
      linarith
    rw [hCfeq]
    have h3 : 0 ≤ 24 * Aa * δp * Real.sqrt k := by positivity
    have e : (48 * Aa + 3 * 2 ^ d * mx) * δp * Real.sqrt k
        = 2 * (24 * Aa * δp * Real.sqrt k) + 3 / 2 * (2 * 2 ^ d * (mx * δp) * Real.sqrt k) := by
      ring
    rw [e]
    linarith
  have hWK : 4 * δ + (1 + 4 * δ) * heatW d N M L δ θ K ≤ 1 := (hrel K hK).trans hsmall
  have h := heat_kernel_rate_explicit hσ hσ1 d X h_indep hX hlaw N K hN hK hN hMdef hLipdef hL hT
    hδ hθ hgc hsm hKσ hWK
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk2 hkK a i
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h1 := hgood.2 j (by omega) a i
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (heatMu_nonneg d σ _)
  refine (hrel (j + 1) (by omega)).trans ?_
  rw [hCf]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by rw [← hCf]; exact mul_nonneg hCf0 hδp0)
  push_cast; linarith

end RatePaper

section EigUniform
open Matrix

/-- The error of the eigenvalue statement at step `k`: `3δ(M_k + D) + D + t_k`, with the uniform
    bound `M_k` of the kernel after `k` steps, the kernel error `D` and the tail `t_k` of the Fourier
    series beyond `|n|² ≥ R`. -/
noncomputable def heatEigErr (d : ℕ) (σ : ℝ) (k : ℕ) (δ D R : ℝ) : ℝ :=
  3 * δ * ((1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d + D) + D
    + Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
      * (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d

/-- **Eigenvalues of the sampled graph on the torus, uniformly in the step and in the index
    (deterministic statement on the good event).** Points `x_0, …, x_{N-1}`; HYPOTHESES on the
    points: normalisation within `δ ≤ 1/8`, Gram matrix of the sampled modes of `H` within `N η`,
    and a bound `Dk k` for the entries of `N P^k - p_{kσ}` for `2 ≤ k ≤ K`. Then for every such `k`,
    every `r > 0` and every index `j` of the shell `|n|² = r`
    (`1 + 2 #{n ∈ H : |n|² < r} ≤ j ≤ 2 #{n ∈ H : |n|² ≤ r}`), with `α = e^{-2π²σ r}`: if
    `2 (err_k + η Σ_g √a_g) ≤ α^k`, then `|s_j^k - α^k| ≤ err_k + η Σ_g √a_g` and
    `k α^k |s_j - α| ≤ 2 (err_k + η Σ_g √a_g)`. -/
theorem heat_eig_uniform_det {σ δ η R : ℝ} (hσ : 0 < σ) (d N K : ℕ) [NeZero N]
    (x : ℕ → FlatTorus d) (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0)
    (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hδ0 : 0 ≤ δ) (hδ8 : δ ≤ 1 / 8) (hη0 : 0 ≤ η)
    (hnorm : ∀ j, |heatRho d σ N x j - 1| ≤ δ)
    (hgram : ∀ f g : modeSet d H, |∑ i : Fin N, torusMode d f.1 (x i) * torusMode d g.1 (x i)
        - N * (if f = g then (1 : ℝ) else 0)| ≤ N * η)
    (Dk : ℕ → ℝ)
    (hkern : ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ k) a i - heatP d σ k (x a - x i)| ≤ Dk k)
    (k : ℕ) (hk2 : 2 ≤ k) (hkK : k ≤ K) {r : ℝ} (hr : 0 < r)
    (hS : (symGraph (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j))
      (fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N)).IsHermitian)
    (j : Fin (Fintype.card (Fin N)))
    (hj1 : 1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val)
    (hj2 : j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card)
    (h3 : 2 * (heatEigErr d σ k δ (Dk k) R + η * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))
      ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k) :
    |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
        ≤ heatEigErr d σ k δ (Dk k) R + η * 1 * ∑ g : modeSet d H,
            Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
      ∧ (k : ℝ) * (Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k
            * |hS.eigenvalues₀ j - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)|)
          ≤ 2 * (heatEigErr d σ k δ (Dk k) R + η * 1 * ∑ g : modeSet d H,
              Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)) := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hc' : 0 < ((k0 + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ) := by positivity
  have hpow : Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ (k0 + 1)
      = Real.exp (-(((k0 + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ)) * r) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  obtain ⟨c1, c2⟩ := mode_counts_general d hc' hr H
  have e1 : (fun a : Fin N => heatRho d σ N x a)
      = fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N := by
    funext a
    unfold heatRho
    rw [Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) N]
  have hnorm' : ∀ b : Fin N,
      |(∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l)) / N - 1| ≤ δ := by
    intro b
    have h := hnorm b
    have e := congrFun e1 b
    simp only at e
    rw [e] at h
    exact h
  have hkern' : ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j))
          (fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) / N))
            ^ (k0 + 1)) a i
        - heatTorus d ((k0 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) (x a - x i)| ≤ Dk (k0 + 1) := by
    intro a i
    have h := hkern (k0 + 1) hk2 hkK a i
    have e2 : heatP d σ (k0 + 1) (x a - x i)
        = heatTorus d ((k0 + 1 : ℕ) * (2 * Real.pi ^ 2 * σ)) (x a - x i) := by
      rw [heatP_of_ne d σ (by omega)]
      congr 1
      ring
    rw [e1, e2] at h
    exact h
  refine heatTorus_eig_det_kern hc d N (fun i : Fin N => x i) k0 H hH0 hH2 hR hδ0 hδ8 hη0
    hnorm' hgram le_rfl hkern' (by unfold heatEigErr; exact le_rfl) hS j (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hc hr])) ?_ ?_ h3
  · rw [hpow]; exact c1.trans hj1
  · rw [hpow]; exact lt_of_lt_of_le (by omega) c2

set_option maxHeartbeats 1600000 in
/-- **Eigenvalues of the sampled graph on the torus, uniformly in the step and in the index, for
    random samples.** In the situation of `heat_kernel_rate_paper` (kernel error
    `D_k = C δ' √k mu_k`), with a normalisation tolerance `ε`, grid parameter `g`,
    `δ = (ε + 2 N Lip/g)/N ≤ 1/8`, a set `H` of frequencies with cut-off `R` and a Gram tolerance `η`:
    except on an event of probability at most
    `2/N³ + 2 g^d exp(-ε²/(4NM + 2Mε)) + 2 |F|² exp(-(Nη/2)²/(2N))`, simultaneously for all
    `2 ≤ k ≤ K`, all `r > 0` and all indices `j` of the shell `|n|² = r`: if
    `2 (err_k + η Σ_g √a_g) ≤ α^k` with `α = e^{-2π²σ r}`, then
    `|s_j^k - α^k| ≤ err_k + η Σ_g √a_g` and `k α^k |s_j - α| ≤ 2 (err_k + η Σ_g √a_g)`. -/
theorem heat_eig_uniform_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g)
    {M Lip δp ε δ η R : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1)
    (hε : 0 < ε) (hδdef : δ = (ε + 2 * (N * Lip) * (1 / g)) / N) (hδ8 : δ ≤ 1 / 8) (hη0 : 0 ≤ η)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ r : ℝ, 0 < r →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val →
          j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card →
          2 * (heatEigErr d σ k δ (rateCfin d * δp * Real.sqrt k * heatMu d σ k) R
              + η * 1 * ∑ g : modeSet d H,
                Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))
            ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k →
          |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ heatEigErr d σ k δ (rateCfin d * δp * Real.sqrt k * heatMu d σ k) R
                + η * 1 * ∑ g : modeSet d H,
                  Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
            ∧ (k : ℝ) * (Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k
                  * |hS.eigenvalues₀ j - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)|)
                ≤ 2 * (heatEigErr d σ k δ (rateCfin d * δp * Real.sqrt k * heatMu d σ k) R
                  + η * 1 * ∑ g : modeSet d H,
                    Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))}
      ≤ 2 / (N : ℝ) ^ 3 + (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2 * (2 * Real.exp (-(N * η / 2) ^ 2 / (2 * N))) := by
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M := fun u => by
    rw [hMdef]; exact heatTorus_le hcσ d u
  have hLip : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u
      - heatTorus d (2 * Real.pi ^ 2 * σ) u'| ≤ Lip * dist u u' := fun u u' => by
    rw [hLipdef]; exact heatTorus_lipschitz hcσ d u u'
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  obtain ⟨Bk, hBkd⟩ : ∃ Bk : Set Ω, Bk = {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix
            (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
            (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
          - heatP d σ k (X a ω - X i ω)|
        ≤ rateCfin d * δp * Real.sqrt k * heatMu d σ k} := ⟨_, rfl⟩
  have hBk : μ.real Bk ≤ 2 / (N : ℝ) ^ 3 := by
    rw [hBkd]
    exact heat_kernel_rate_paper hσ hσ1 d X h_indep hX hlaw N K hN12 hK hKN hMdef hLipdef hδp hLipc
      hKσ hsmall
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : Set Ω, Bn = {ω | ∃ x : FlatTorus d, ε + 2 * (N * Lip) * (1 / g)
      < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} := ⟨_, rfl⟩
  have hBn : μ.real Bn ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))) := by
    rw [hBnd]
    exact heat_normalisation_whp hσ d X h_indep hX hlaw N hg hM hLip hLip0 hε
  obtain ⟨Bg, hBgd⟩ : ∃ Bg : Set Ω, Bg = {ω | ∃ f g : modeSet d H, N * η ≤ |∑ j ∈ Finset.range N,
      torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
      - N * (if f = g then (1 : ℝ) else 0)|} := ⟨_, rfl⟩
  have hBg : μ.real Bg
      ≤ (Fintype.card (modeSet d H) : ℝ) ^ 2 * (2 * Real.exp (-(N * η / 2) ^ 2 / (2 * N))) := by
    rw [hBgd]
    exact flatTorus_gram_whp (μ := μ) d X h_indep hX hlaw (modeSet d H)
      (fun n b h => hH0 n ((mem_modeSet d H n b).mp h))
      (fun n b n' b' h h' => hH2 n ((mem_modeSet d H n b).mp h) n' ((mem_modeSet d H n' b').mp h'))
      N (ε := N * η) (mul_nonneg (Nat.cast_nonneg N) hη0)
  refine le_trans (measureReal_mono (s₂ := (Bk ∪ Bn) ∪ Bg) ?_ (measure_ne_top μ _)) ?_
  · intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨hk, hn⟩, hgm⟩ := hcon
    rw [hBkd] at hk
    rw [hBnd] at hn
    rw [hBgd] at hgm
    have hkern := not_not.mp hk
    apply hω
    intro k hk2 hkK r hr hS j hj1 hj2 h3
    refine heat_eig_uniform_det hσ d N K (fun j => X j ω) H hH0 hH2 hR hδ0 hδ8 hη0 ?_ ?_
      (fun k => rateCfin d * δp * Real.sqrt k * heatMu d σ k) hkern k hk2 hkK hr hS j hj1 hj2 h3
    · intro b
      have h : |∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X l ω) - N|
          ≤ ε + 2 * (N * Lip) * (1 / g) := by
        by_contra h; exact hn ⟨X b ω, not_le.mp h⟩
      have e : heatRho d σ N (fun j => X j ω) b - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos, hδdef]
      exact div_le_div_of_nonneg_right h hNpos.le
    · intro f g'
      have h : |∑ j ∈ Finset.range N, torusMode d f.1 (X j ω) * torusMode d g'.1 (X j ω)
          - N * (if f = g' then (1 : ℝ) else 0)| < N * η := by
        by_contra h; exact hgm ⟨f, g', not_lt.mp h⟩
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => torusMode d f.1 (X j ω) * torusMode d g'.1 (X j ω)) N] at h
      exact h.le
  · calc μ.real ((Bk ∪ Bn) ∪ Bg) ≤ μ.real (Bk ∪ Bn) + μ.real Bg := measureReal_union_le _ _
      _ ≤ (μ.real Bk + μ.real Bn) + μ.real Bg := add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ _ := by linarith

end EigUniform

section EigLambda
open Matrix

/-- The sum of the square roots of the coefficients of the modes:
    `∑_g √a_g = 1 + 2 ∑_{n ∈ H} e^{-c|n|²/2} ≤ 1 + 2 (1 + √(2π/c))^d`. -/
theorem mode_sqrt_sum_le (d : ℕ) {c : ℝ} (hc : 0 < c) (H : Finset (Fin d → ℤ)) :
    ∑ g : modeSet d H, Real.sqrt (modeCoeff d c g.1)
      ≤ 1 + 2 * (1 + Real.sqrt (Real.pi / (c / 2))) ^ d := by
  classical
  rw [Finset.sum_coe_sort (modeSet d H) (fun g => Real.sqrt (modeCoeff d c g))]
  have hsq : ∀ q : ℝ, Real.sqrt (Real.exp (-c * q)) = Real.exp (-(c / 2) * q) := fun q => by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    congr 1; ring
  have hnone : (none : Option ((Fin d → ℤ) × Bool))
      ∉ (H.image fun n => some (n, false)) ∪ (H.image fun n => some (n, true)) := by
    simp
  have hdisj : Disjoint (H.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
      (H.image fun n => some (n, true)) := by
    rw [Finset.disjoint_left]
    intro f hf hf'
    simp only [Finset.mem_image] at hf hf'
    obtain ⟨m, -, rfl⟩ := hf
    obtain ⟨m', -, h⟩ := hf'
    simp at h
  have inj : ∀ b : Bool, Function.Injective fun n : Fin d → ℤ =>
      (some (n, b) : Option ((Fin d → ℤ) × Bool)) := fun b n n' h => by
    simpa using h
  unfold modeSet
  rw [Finset.sum_insert hnone, Finset.sum_union hdisj,
    Finset.sum_image (fun a _ b _ h => inj false h), Finset.sum_image (fun a _ b _ h => inj true h)]
  simp only [modeCoeff, Real.sqrt_one, hsq]
  have h := gauss_finset_sum_le (by positivity : (0 : ℝ) < c / 2) d H
  linarith

/-- From the bound for the `k`-th power to the eigenvalue of the graph Laplacian, when
    `α^k ≥ e^{-1}`: `|(1 - s)/τ - (1 - α)/τ| ≤ 2 e E / (k τ)`. -/
theorem lambda_from_power {s α E τ : ℝ} {k : ℕ} (hk : 0 < k) (hτ : 0 < τ)
    (hαk : Real.exp (-1) ≤ α ^ k) (h : (k : ℝ) * (α ^ k * |s - α|) ≤ 2 * E) :
    |(1 - s) / τ - (1 - α) / τ| ≤ 2 * Real.exp 1 * E / (k * τ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have he : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have habs := abs_nonneg (s - α)
  have h1 : (k : ℝ) * (Real.exp (-1) * |s - α|) ≤ 2 * E :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαk habs) hkpos.le) h
  have h2 : (k : ℝ) * |s - α| ≤ 2 * Real.exp 1 * E := by
    have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos 1).le
    have e : (k : ℝ) * (Real.exp (-1) * |s - α|) * Real.exp 1
        = (k : ℝ) * |s - α| * (Real.exp (-1) * Real.exp 1) := by ring
    rw [e, he] at this
    linarith
  have e : (1 - s) / τ - (1 - α) / τ = -(s - α) / τ := by ring
  rw [e, abs_div, abs_neg, abs_of_pos hτ, div_le_div_iff₀ hτ (by positivity)]
  have := mul_le_mul_of_nonneg_right h2 hτ.le
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **Eigenvalues of the graph Laplacian of the sampled graph on the torus (form of part (ii) of
    Theorem "eigenvalues on the torus", with explicit error).** In the situation of
    `heat_eig_uniform_sample`, with `τ = σ/2` (the `σ` of the paper) and `λ = 4π² r`, so that
    `e^{-2π²σ r} = e^{-τλ}`: except on the same event, simultaneously for all `2 ≤ k ≤ K`, all
    `r > 0` with `k · 2π²σ · r ≤ 1` and all indices `j` of the shell `|n|² = r`: if
    `2 E_k ≤ e^{-1}`, then `|(1 - s_j)/τ - (1 - e^{-τλ})/τ| ≤ 2 e E_k/(k τ)`, where
    `E_k = err_k + η (1 + 2 (1 + √(2π/(k c)))^d)`. -/
theorem heat_eig_lambda_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g)
    {M Lip δp ε δ η R : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1)
    (hε : 0 < ε) (hδdef : δ = (ε + 2 * (N * Lip) * (1 / g)) / N) (hδ8 : δ ≤ 1 / 8) (hη0 : 0 ≤ η)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ r : ℝ, 0 < r → (k : ℝ) * (2 * Real.pi ^ 2 * σ) * r ≤ 1 →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val →
          j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card →
          2 * (heatEigErr d σ k δ (rateCfin d * δp * Real.sqrt k * heatMu d σ k) R
              + η * (1 + 2 * (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d))
            ≤ Real.exp (-1) →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ 2 * Real.exp 1
              * (heatEigErr d σ k δ (rateCfin d * δp * Real.sqrt k * heatMu d σ k) R
                + η * (1 + 2 * (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d))
              / (k * (σ / 2))}
      ≤ 2 / (N : ℝ) ^ 3 + (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2 * (2 * Real.exp (-(N * η / 2) ^ 2 / (2 * N))) := by
  have h := heat_eig_uniform_sample hσ hσ1 d N K X h_indep hX hlaw hN12 hK hKN H hH0 hH2 hg hMdef
    hLipdef hδp hLipc hKσ hsmall hε hδdef hδ8 hη0 hR
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω huni
  apply hω
  intro k hk2 hkK r hr hkr hS j hj1 hj2 hsize
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkc : 0 < ((k : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ) := by positivity
  have hpow : Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k
      = Real.exp (-(((k : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ) * r)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hαk : Real.exp (-1) ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k := by
    rw [hpow]; exact Real.exp_le_exp.mpr (by linarith)
  have hS1 := mode_sqrt_sum_le d hkc H
  have hηS : η * 1 * ∑ g : modeSet d H,
        Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1)
      ≤ η * (1 + 2 * (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d) := by
    rw [mul_one]; exact mul_le_mul_of_nonneg_left hS1 hη0
  have h3 : 2 * (heatEigErr d σ k δ (rateCfin d * δp * Real.sqrt k * heatMu d σ k) R
        + η * 1 * ∑ g : modeSet d H,
          Real.sqrt (modeCoeff d ((k : ℕ) * (2 * Real.pi ^ 2 * σ)) g.1))
      ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k := by linarith
  obtain ⟨-, h2⟩ := huni k hk2 hkK r hr hS j hj1 hj2 h3
  refine lambda_from_power (by omega) (by positivity) hαk (h2.trans ?_)
  linarith

end EigLambda

section EigClosed
open Matrix

theorem rateCfin_nonneg (d : ℕ) : 0 ≤ rateCfin d := by
  have hc := cvConst_nonneg
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRB0 : 0 ≤ rateRB d := Real.sqrt_nonneg _
  have hmax : 0 ≤ max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt ((d : ℝ) + 5) * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRB d)
        + 12 * Real.sqrt ((d : ℝ) + 5) * rateRB d)) :=
    le_max_of_le_right (by positivity)
  unfold rateCfin
  positivity

/-- **The error of the eigenvalue statement in terms of `δ'`.** If `δ ≤ c₁ δ'`, `η ≤ c₂ δ'`, the
    tail satisfies `t_k ≤ c₃ δ' mu_k` and `C δ' √k ≤ 1`, then
    `E_k ≤ (6c₁ + C + c₃ + c₂ (1 + 2·2^d)) δ' √k mu_k`. -/
theorem eig_err_closed {σ δ η R δp c1 c2 c3 Cf : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ c1 * δp) (hη0 : 0 ≤ η) (hη : η ≤ c2 * δp) (hδp0 : 0 ≤ δp)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hCf : 0 ≤ Cf)
    (hD : Cf * δp * Real.sqrt k ≤ 1)
    (ht : Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
      ≤ c3 * δp * heatMu d σ k) :
    heatEigErr d σ k δ (Cf * δp * Real.sqrt k * heatMu d σ k) R
        + η * (1 + 2 * (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d)
      ≤ (6 * c1 + Cf + c3 + c2 * (1 + 2 * 2 ^ d)) * δp * Real.sqrt k * heatMu d σ k := by
  have hpi := Real.pi_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsk1 : 1 ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ))) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = heatMu d σ k := ⟨_, rfl⟩
  have hμeq : μ = (1 + y) ^ d := by
    rw [hμ, hy]; unfold heatMu heatM
    rw [if_neg (by omega)]
    have e : 2 * Real.pi ^ 2 * ((k : ℝ) * σ) = (k : ℝ) * (2 * Real.pi ^ 2 * σ) := by ring
    rw [e]
  have hμ1 : 1 ≤ μ := by rw [hμeq]; exact one_le_pow₀ (by linarith)
  have hS : (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d ≤ 2 ^ d * μ := by
    rw [hμeq, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have e : Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2)
        = 2 * (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ))) := by field_simp
    have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    rw [e, Real.sqrt_mul (by norm_num), ← hy]
    nlinarith [mul_le_mul_of_nonneg_right h2 hy0]
  rw [← hμ] at ht ⊢
  have hDμ : Cf * δp * Real.sqrt k * μ ≤ μ := by
    have := mul_le_mul_of_nonneg_right hD (by linarith : (0 : ℝ) ≤ μ)
    linarith
  have hD0 : 0 ≤ Cf * δp * Real.sqrt k * μ := by positivity
  have hμ0 : 0 ≤ μ := by linarith
  have hδpμ : 0 ≤ δp * μ := mul_nonneg hδp0 hμ0
  -- the four pieces
  have p1 : 3 * δ * ((1 + y) ^ d + Cf * δp * Real.sqrt k * μ) ≤ 6 * c1 * (δp * μ) := by
    rw [← hμeq]
    have h1 : 3 * δ * (μ + Cf * δp * Real.sqrt k * μ) ≤ 3 * (c1 * δp) * (2 * μ) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    linarith
  have p2 : η * (1 + 2 * (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d)
      ≤ c2 * (1 + 2 * 2 ^ d) * (δp * μ) := by
    have h1 : 1 + 2 * (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d
        ≤ (1 + 2 * 2 ^ d) * μ := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) d]
    have h2 : η * (1 + 2 * (1 + Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ) / 2))) ^ d)
        ≤ c2 * δp * ((1 + 2 * 2 ^ d) * μ) :=
      mul_le_mul hη h1 (by positivity) (by positivity)
    linarith
  have p3 : Cf * δp * Real.sqrt k * μ = Cf * (δp * μ) * Real.sqrt k := by ring
  have hsmallpieces : (6 * c1 + c3 + c2 * (1 + 2 * 2 ^ d)) * (δp * μ)
      ≤ (6 * c1 + c3 + c2 * (1 + 2 * 2 ^ d)) * (δp * μ) * Real.sqrt k :=
    le_mul_of_one_le_right (by positivity) hsk1
  unfold heatEigErr
  rw [← hy]
  have e : (6 * c1 + Cf + c3 + c2 * (1 + 2 * 2 ^ d)) * δp * Real.sqrt k * μ
      = (6 * c1 + c3 + c2 * (1 + 2 * 2 ^ d)) * (δp * μ) * Real.sqrt k
        + Cf * (δp * μ) * Real.sqrt k := by ring
  rw [e]
  have ht' : Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
      ≤ c3 * (δp * μ) := by linarith
  linarith

/-- **From the error `E ≤ C' δ' √k mu_k` to the closed bound of part (ii).** If
    `1/2 ≤ k · 2π²σ · r`, then
    `2 e E/(k σ/2) ≤ 4 e C' δ' √(4π² r/σ) (1 + √(2π r))^d`. -/
theorem eig_closed_bound {σ r δp C' E : ℝ} (hσ : 0 < σ) (hr : 0 < r) (d k : ℕ) (hk : 1 ≤ k)
    (hδp0 : 0 ≤ δp) (hC' : 0 ≤ C')
    (hlo : 1 / 2 ≤ (k : ℝ) * (2 * Real.pi ^ 2 * σ) * r)
    (hE : E ≤ C' * δp * Real.sqrt k * heatMu d σ k) :
    2 * Real.exp 1 * E / (k * (σ / 2))
      ≤ 4 * Real.exp 1 * C' * δp * Real.sqrt (4 * Real.pi ^ 2 * r / σ)
        * (1 + Real.sqrt (2 * Real.pi * r)) ^ d := by
  have hpi := Real.pi_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkpos
  have hsksq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hkpos.le
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  -- mu_k ≤ (1 + √(2π r))^d
  have hμ : heatMu d σ k ≤ (1 + Real.sqrt (2 * Real.pi * r)) ^ d := by
    unfold heatMu heatM
    rw [if_neg (by omega)]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have : Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) ≤ 2 * Real.pi * r := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_pos hpi hpi]
    linarith [Real.sqrt_le_sqrt this]
  have hμ0 : 0 ≤ heatMu d σ k := heatMu_nonneg d σ k
  -- 1/(√k σ) ≤ √(4π² r/σ)
  have h1 : 1 / (Real.sqrt k * σ) ≤ Real.sqrt (4 * Real.pi ^ 2 * r / σ) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hkpos.le, div_le_div_iff₀ (by positivity) hσ]
    nlinarith
  have hsq0 : 0 ≤ Real.sqrt (4 * Real.pi ^ 2 * r / σ) := Real.sqrt_nonneg _
  calc 2 * Real.exp 1 * E / (k * (σ / 2))
      ≤ 2 * Real.exp 1 * (C' * δp * Real.sqrt k * heatMu d σ k) / (k * (σ / 2)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hE (by positivity)
    _ = 4 * Real.exp 1 * C' * δp * heatMu d σ k * (1 / (Real.sqrt k * σ)) := by
        field_simp
        rw [Real.sq_sqrt hkpos.le]
        ring
    _ ≤ 4 * Real.exp 1 * C' * δp * heatMu d σ k * Real.sqrt (4 * Real.pi ^ 2 * r / σ) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 4 * Real.exp 1 * C' * δp * (1 + Real.sqrt (2 * Real.pi * r)) ^ d
          * Real.sqrt (4 * Real.pi ^ 2 * r / σ) := by
        refine mul_le_mul_of_nonneg_right ?_ hsq0
        exact mul_le_mul_of_nonneg_left hμ (by positivity)
    _ = _ := by ring

set_option maxHeartbeats 1600000 in
/-- **Eigenvalues of the graph Laplacian on the torus in the closed form of part (ii) of Theorem
    "eigenvalues on the torus".** In the situation of `heat_eig_lambda_sample`, with numbers
    `c₁, c₂, c₃` such that `δ ≤ c₁ δ'`, `η ≤ c₂ δ'` and the tail of the Fourier series satisfies
    `t_k ≤ c₃ δ' mu_k` for `2 ≤ k ≤ K`, and `C' = 6c₁ + C + c₃ + c₂ (1 + 2·2^d)`: except on the same
    event, simultaneously for all `2 ≤ k ≤ K`, all `r > 0` with `1/2 ≤ k · 2π²σ · r ≤ 1` (that is,
    `1/2 ≤ k τ λ ≤ 1` for `τ = σ/2`, `λ = 4π² r`) and all indices `j` of the shell: if
    `2 C' δ' √k mu_k ≤ e^{-1}`, then
    `|(1 - s_j)/τ - (1 - e^{-τλ})/τ| ≤ 4 e C' δ' √(λ/σ) (1 + √(λ/(2π)))^d`. -/
theorem heat_eig_closed_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g)
    {M Lip δp ε δ η R c1 c2 c3 : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1)
    (hε : 0 < ε) (hδdef : δ = (ε + 2 * (N * Lip) * (1 / g)) / N) (hδ8 : δ ≤ 1 / 8) (hη0 : 0 ≤ η)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hδc : δ ≤ c1 * δp) (hηc : η ≤ c2 * δp)
    (htail : ∀ k : ℕ, 2 ≤ k → k ≤ K →
      Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
          * (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
        ≤ c3 * δp * heatMu d σ k) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ r : ℝ, 0 < r →
        1 / 2 ≤ (k : ℝ) * (2 * Real.pi ^ 2 * σ) * r → (k : ℝ) * (2 * Real.pi ^ 2 * σ) * r ≤ 1 →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val →
          j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card →
          2 * ((6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp * Real.sqrt k * heatMu d σ k)
            ≤ Real.exp (-1) →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ 4 * Real.exp 1 * (6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp
              * Real.sqrt (4 * Real.pi ^ 2 * r / σ) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d}
      ≤ 2 / (N : ℝ) ^ 3 + (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2 * (2 * Real.exp (-(N * η / 2) ^ 2 / (2 * N))) := by
  have h := heat_eig_lambda_sample hσ hσ1 d N K X h_indep hX hlaw hN12 hK hKN H hH0 hH2 hg hMdef
    hLipdef hδp hLipc hKσ hsmall hε hδdef hδ8 hη0 hR
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hlam
  apply hω
  intro k hk2 hkK r hr hlo hhi hS j hj1 hj2 hsize
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδdef]; positivity
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hCf := rateCfin_nonneg d
  have hC' : 0 ≤ 6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d) := by positivity
  have hD : rateCfin d * δp * Real.sqrt k ≤ 1 := by
    have h1 : Real.sqrt k ≤ Real.sqrt K := Real.sqrt_le_sqrt (by exact_mod_cast hkK)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hCf hδp0)
    linarith
  have hE := eig_err_closed hσ d k (by omega) hδ0 hδc hη0 hηc hδp0 hc1 hc2 hc3 hCf hD
    (htail k hk2 hkK)
  have h1 := hlam k hk2 hkK r hr hhi hS j hj1 hj2 (by linarith)
  exact h1.trans (eig_closed_bound hσ hr d k (by omega) hδp0 hC' hlo hE)

end EigClosed

section EigPaper
open Matrix

/-- The choice of the step: for `0 < x ≤ 1/2` there is an integer `k ≥ 2` with `1/2 ≤ k x ≤ 1`
    (namely `k = ⌊1/x⌋`). -/
theorem exists_step {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    ∃ k : ℕ, 2 ≤ k ∧ 1 / 2 ≤ (k : ℝ) * x ∧ (k : ℝ) * x ≤ 1 := by
  refine ⟨⌊1 / x⌋₊, ?_, ?_, ?_⟩
  · apply Nat.le_floor
    rw [le_div_iff₀ hx0]; push_cast; linarith
  · have h2 : 1 / x < (⌊1 / x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hx0] at h2
    linarith
  · have h1 : (⌊1 / x⌋₊ : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
    have := mul_le_mul_of_nonneg_right h1 hx0.le
    rwa [div_mul_cancel₀ _ hx0.ne'] at this

/-- The uniform bound of the kernel at the step chosen for a shell:
    `mu_k ≤ (1 + √(2π r))^d` if `1/2 ≤ k · 2π²σ · r`. -/
theorem heatMu_le_shell {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) (d k : ℕ) (hk : 1 ≤ k)
    (hlo : 1 / 2 ≤ (k : ℝ) * (2 * Real.pi ^ 2 * σ) * r) :
    heatMu d σ k ≤ (1 + Real.sqrt (2 * Real.pi * r)) ^ d := by
  have hpi := Real.pi_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  unfold heatMu heatM
  rw [if_neg (by omega)]
  refine pow_le_pow_left₀ (by positivity) ?_ d
  have : Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) ≤ 2 * Real.pi * r := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hpi hpi]
  linarith [Real.sqrt_le_sqrt this]

/-- **The tail condition from a condition on the cut-off.** If `e^{-2π²σ R} 2^d ≤ c₃ δ'`, then for
    every `k ≥ 2` the tail of the Fourier series beyond `|n|² ≥ R` satisfies
    `t_k ≤ c₃ δ' mu_k`. -/
theorem tail_closed {σ R c3 δp : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 2 ≤ k) (hR0 : 0 ≤ R)
    (hc3 : 0 ≤ c3 * δp) (h : Real.exp (-(2 * Real.pi ^ 2 * σ) * R) * 2 ^ d ≤ c3 * δp) :
    Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
      ≤ c3 * δp * heatMu d σ k := by
  have hpi := Real.pi_pos
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ))) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  have hμeq : heatMu d σ k = (1 + y) ^ d := by
    rw [hy]; unfold heatMu heatM
    rw [if_neg (by omega)]
    have e : 2 * Real.pi ^ 2 * ((k : ℝ) * σ) = (k : ℝ) * (2 * Real.pi ^ 2 * σ) := by ring
    rw [e]
  have hS : (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
      ≤ 2 ^ d * heatMu d σ k := by
    rw [hμeq, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have e : 2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ))
        = 2 * (Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ))) := by ring
    have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    rw [e, Real.sqrt_mul (by norm_num), ← hy]
    nlinarith [mul_le_mul_of_nonneg_right h2 hy0]
  have hexp : Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
      ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * R) := by
    apply Real.exp_le_exp.mpr
    have := mul_nonneg hc.le hR0
    nlinarith
  have hμ0 := heatMu_nonneg d σ k
  calc Real.exp (-((k : ℕ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
        * (1 + Real.sqrt (2 * Real.pi / ((k : ℕ) * (2 * Real.pi ^ 2 * σ)))) ^ d
      ≤ Real.exp (-(2 * Real.pi ^ 2 * σ) * R) * (2 ^ d * heatMu d σ k) :=
        mul_le_mul hexp hS (by positivity) (Real.exp_pos _).le
    _ = Real.exp (-(2 * Real.pi ^ 2 * σ) * R) * 2 ^ d * heatMu d σ k := by ring
    _ ≤ c3 * δp * heatMu d σ k := mul_le_mul_of_nonneg_right h hμ0

/-- **The bias of the eigenvalues of the population walk** (second inequality of part (ii)):
    `0 ≤ λ - (1 - e^{-τλ})/τ ≤ τ λ²/2` for `τ > 0`, `λ ≥ 0`. -/
theorem lambda_bias {τ lam : ℝ} (hτ : 0 < τ) (hl : 0 ≤ lam) :
    0 ≤ lam - (1 - Real.exp (-(τ * lam))) / τ
      ∧ lam - (1 - Real.exp (-(τ * lam))) / τ ≤ τ * lam ^ 2 / 2 := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = τ * lam := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  rw [← hy]
  have h1 : 1 - y ≤ Real.exp (-y) := by have := Real.add_one_le_exp (-y); linarith
  have h2 : Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
    have hq := Real.quadratic_le_exp_of_nonneg hy0
    have hpos : 0 < 1 + y + y ^ 2 / 2 := by positivity
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos y)]
    have h3 : 1 ≤ (1 - y + y ^ 2 / 2) * (1 + y + y ^ 2 / 2) := by nlinarith [sq_nonneg (y ^ 2)]
    have h4 : 0 ≤ 1 - y + y ^ 2 / 2 := by nlinarith [sq_nonneg (y - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hq h4]
  have e : lam = y / τ := by rw [hy]; field_simp
  constructor
  · rw [e, ← sub_div]
    apply div_nonneg _ hτ.le
    linarith
  · rw [e, ← sub_div, div_le_iff₀ hτ]
    have e2 : τ * (y / τ) ^ 2 / 2 * τ = y ^ 2 / 2 := by field_simp
    rw [e2]
    linarith

set_option maxHeartbeats 1600000 in
/-- **Eigenvalues of the graph Laplacian on the torus, part (ii) without a hypothesis on the
    step.** In the situation of `heat_eig_closed_sample`, with the tail condition replaced by the
    condition `e^{-2π²σ R} 2^d ≤ c₃ δ'` on the cut-off `R ≥ 0` of `H`: except on the same event,
    simultaneously for all `r > 0` with `2π²σ r ≤ 1/2` and `1 ≤ K · 2π²σ · r` (that is, `τλ ≤ 1/2` and
    `Kτλ ≥ 1` for `τ = σ/2`, `λ = 4π² r`) and all indices `j` of the shell: if
    `2 C' δ' (1 + √(2π r))^d ≤ e^{-1} √(2π²σ r)`, then
    `|(1 - s_j)/τ - (1 - e^{-τλ})/τ| ≤ 4 e C' δ' √(λ/σ) (1 + √(λ/(2π)))^d`. -/
theorem heat_eig_paper_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {g : ℕ} (hg : 0 < g)
    {M Lip δp ε δ η R c1 c2 c3 : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1)
    (hε : 0 < ε) (hδdef : δ = (ε + 2 * (N * Lip) * (1 / g)) / N) (hδ8 : δ ≤ 1 / 8) (hη0 : 0 ≤ η)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hδc : δ ≤ c1 * δp) (hηc : η ≤ c2 * δp)
    (hR0 : 0 ≤ R) (htail : Real.exp (-(2 * Real.pi ^ 2 * σ) * R) * 2 ^ d ≤ c3 * δp) :
    μ.real {ω | ¬ ∀ r : ℝ, 0 < r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
        1 ≤ (K : ℝ) * ((2 * Real.pi ^ 2 * σ) * r) →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val →
          j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card →
          2 * ((6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp)
              * (1 + Real.sqrt (2 * Real.pi * r)) ^ d
            ≤ Real.exp (-1) * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ 4 * Real.exp 1 * (6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp
              * Real.sqrt (4 * Real.pi ^ 2 * r / σ) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d}
      ≤ 2 / (N : ℝ) ^ 3 + (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + (Fintype.card (modeSet d H) : ℝ) ^ 2 * (2 * Real.exp (-(N * η / 2) ^ 2 / (2 * N))) := by
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have h := heat_eig_closed_sample hσ hσ1 d N K X h_indep hX hlaw hN12 hK hKN H hH0 hH2 hg hMdef
    hLipdef hδp hLipc hKσ hsmall hε hδdef hδ8 hη0 hR hc1 hc2 hc3 hδc hηc
    (fun k hk2 _ => tail_closed hσ d k hk2 hR0 (mul_nonneg hc3 hδp0) htail)
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hclosed
  apply hω
  intro r hr hx hKx hS j hj1 hj2 hsize
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hx0 : 0 < (2 * Real.pi ^ 2 * σ) * r := mul_pos hc hr
  obtain ⟨k, hk2, hlo, hhi⟩ := exists_step hx0 hx
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkK : k ≤ K := by
    have : (k : ℝ) * ((2 * Real.pi ^ 2 * σ) * r) ≤ (K : ℝ) * ((2 * Real.pi ^ 2 * σ) * r) := by
      linarith
    have h2 : (k : ℝ) ≤ K := le_of_mul_le_mul_right this hx0
    exact_mod_cast h2
  have hlo' : 1 / 2 ≤ (k : ℝ) * (2 * Real.pi ^ 2 * σ) * r := by rw [mul_assoc]; exact hlo
  have hhi' : (k : ℝ) * (2 * Real.pi ^ 2 * σ) * r ≤ 1 := by rw [mul_assoc]; exact hhi
  have hCf := rateCfin_nonneg d
  have hC' : 0 ≤ 6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d) := by positivity
  -- the size condition at the chosen step
  have hμ := heatMu_le_shell hσ hr d k (by omega) hlo'
  have hμ0 := heatMu_nonneg d σ k
  have hsx : 0 < Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) := Real.sqrt_pos.mpr hx0
  have hsk : Real.sqrt k * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) ≤ 1 := by
    rw [← Real.sqrt_mul hkpos.le, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hhi
  have hsize' : 2 * ((6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp * Real.sqrt k
      * heatMu d σ k) ≤ Real.exp (-1) := by
    have hA0 : 0 ≤ 2 * ((6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp) := by positivity
    have h1 : 2 * ((6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp) * heatMu d σ k
        ≤ Real.exp (-1) * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) :=
      (mul_le_mul_of_nonneg_left hμ hA0).trans hsize
    have h2 : 2 * ((6 * c1 + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp) * heatMu d σ k
          * Real.sqrt k
        ≤ Real.exp (-1) * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) * Real.sqrt k :=
      mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
    have h3 : Real.exp (-1) * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) * Real.sqrt k
        ≤ Real.exp (-1) * 1 := by
      have hsk' : Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) * Real.sqrt k ≤ 1 := by
        rw [mul_comm]; exact hsk
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hsk' (Real.exp_pos _).le
    linarith
  exact hclosed k hk2 hkK r hr hlo' hhi' hS j hj1 hj2 hsize'

end EigPaper

section KernelM
open Matrix

/-- The periodised Gaussian at the origin is at least its main term. -/
theorem perGauss_zero_ge {c : ℝ} (hc : 0 < c) : 1 / (c / Real.pi) ^ (1 / 2 : ℝ) ≤ perGauss c 0 := by
  have ha : 0 < c / Real.pi := div_pos hc Real.pi_pos
  have hb : 0 < Real.pi / (c / Real.pi) := div_pos Real.pi_pos ha
  unfold perGauss
  have e : (fun n : ℤ => Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - 0) ^ 2))
      = fun n : ℤ => Real.exp (-(Real.pi / (c / Real.pi)) * ((n : ℝ) - 0) ^ 2) := by
    funext n; congr 1; ring
  have hsum : Summable fun n : ℤ => Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - 0) ^ 2) := by
    rw [e]; exact gauss_shift_summable hb 0
  have h1 : (1 : ℝ) ≤ ∑' n : ℤ, Real.exp (-Real.pi / (c / Real.pi) * ((n : ℝ) - 0) ^ 2) := by
    have h := hsum.le_tsum 0 (fun n _ => (Real.exp_pos _).le)
    simpa using h
  exact le_mul_of_one_le_right (by positivity) h1

/-- The heat kernel of the torus at the origin is at least `(c/π)^{-d/2}`. -/
theorem heatTorus_zero_ge {c : ℝ} (hc : 0 < c) (d : ℕ) :
    (1 / (c / Real.pi) ^ (1 / 2 : ℝ)) ^ d ≤ heatTorus d c 0 := by
  have e : (0 : FlatTorus d) = fun i => (((fun _ : Fin d => (0 : ℝ)) i : ℝ) : UnitAddCircle) := by
    funext i; simp
  rw [e, heatTorus_eq_prod hc d (fun _ => 0), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have hpi := Real.pi_pos
  exact pow_le_pow_left₀ (by positivity) (perGauss_zero_ge hc) d

/-- **The uniform bound of the kernel against its value at the origin:** for `k σ ≤ 1`,
    `mu_k ≤ (1 + √(2π))^d p_{kσ}(0)`. -/
theorem heatMu_le_m {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) (hkσ : (k : ℝ) * σ ≤ 1) :
    heatMu d σ k
      ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by
  have hpi := Real.pi_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := by positivity
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = 2 * Real.pi * ((k : ℝ) * σ) := ⟨_, rfl⟩
  have hv0 : 0 < v := by rw [hv]; positivity
  have hv1 : v ≤ 2 * Real.pi := by rw [hv]; nlinarith
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hsv1 : Real.sqrt v ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_le_sqrt hv1
  have e1 : 2 * Real.pi ^ 2 * ((k : ℝ) * σ) / Real.pi = v := by rw [hv]; field_simp
  have e2 : Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) = 1 / v := by rw [hv]; field_simp
  have h0 := heatTorus_zero_ge hc d
  rw [e1, ← Real.sqrt_eq_rpow] at h0
  unfold heatMu heatM
  rw [if_neg (by omega), e2, Real.sqrt_div (by norm_num), Real.sqrt_one]
  have hstep : 1 + 1 / Real.sqrt v ≤ (1 + Real.sqrt (2 * Real.pi)) * (1 / Real.sqrt v) := by
    rw [mul_one_div, le_div_iff₀ hsv]
    have : (1 + 1 / Real.sqrt v) * Real.sqrt v = Real.sqrt v + 1 := by field_simp
    rw [this]; linarith
  calc (1 + 1 / Real.sqrt v) ^ d ≤ ((1 + Real.sqrt (2 * Real.pi)) * (1 / Real.sqrt v)) ^ d :=
        pow_le_pow_left₀ (by positivity) hstep d
    _ = (1 + Real.sqrt (2 * Real.pi)) ^ d * (1 / Real.sqrt v) ^ d := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h0 (by positivity)

set_option maxHeartbeats 1600000 in
/-- **Theorem "kernel" in the form `D_k ≤ C δ' √k m_k` with `m_k = p_{kσ}(0)`.** As
    `heat_kernel_rate_paper`, with the value of the kernel at the origin in place of the uniform
    bound `mu_k`, at the cost of the factor `(1 + √(2π))^d`. -/
theorem heat_kernel_rate_paper_m {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ rateCfin d * (1 + Real.sqrt (2 * Real.pi)) ^ d * δp * Real.sqrt k
            * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have h := heat_kernel_rate_paper hσ hσ1 d X h_indep hX hlaw N K hN12 hK hKN hMdef hLipdef hδp
    hLipc hKσ hsmall
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk2 hkK a i
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hkσ : (k : ℝ) * σ ≤ 1 := by
    have : (k : ℝ) ≤ K := by exact_mod_cast hkK
    nlinarith
  have hμ := heatMu_le_m hσ d k (by omega) hkσ
  have hC0 : 0 ≤ rateCfin d * δp * Real.sqrt k :=
    mul_nonneg (mul_nonneg (rateCfin_nonneg d) hδp0) (Real.sqrt_nonneg _)
  calc _ ≤ rateCfin d * δp * Real.sqrt k * heatMu d σ k := hgood k hk2 hkK a i
    _ ≤ rateCfin d * δp * Real.sqrt k * ((1 + Real.sqrt (2 * Real.pi)) ^ d
          * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0) :=
        mul_le_mul_of_nonneg_left hμ hC0
    _ = _ := by ring

end KernelM

section EigParams
open Matrix

set_option maxHeartbeats 1600000 in
/-- **The choice of the normalisation parameters.** With the grid parameter `g = N`,
    `T = log((2 + 4K) · 2 N^d · N³)` and the tolerance `ε = 3 √(N M T)`: if `12 ≤ N`, `1 ≤ K ≤ N`,
    `2 Lip ≤ 3 √(N M log N)` and `48 √(d+5) δ' ≤ 1`, then `ε > 0`, the normalisation error
    `δ = (ε + 2 N Lip/N)/N` is at most `6 √(d+5) δ'` and at most `1/8`, and the probability term of the
    normalisation event is at most `1/N³`. -/
theorem param_choice (d N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N) {M Lip δp ε : ℝ}
    (hM : 0 < M) (hLip0 : 0 ≤ Lip) (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (h48 : 48 * Real.sqrt ((d : ℝ) + 5) * δp ≤ 1)
    (hε : ε = 3 * Real.sqrt (N * M
      * Real.log ((2 + 4 * K) * (2 * ((N : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3))) :
    0 < ε
      ∧ (ε + 2 * (N * Lip) * (1 / ((N : ℕ) : ℝ))) / N ≤ 6 * Real.sqrt ((d : ℝ) + 5) * δp
      ∧ (ε + 2 * (N * Lip) * (1 / ((N : ℕ) : ℝ))) / N ≤ 1 / 8
      ∧ ((N : ℕ) : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          ≤ 1 / (N : ℝ) ^ 3 := by
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  obtain ⟨lg, hlg⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  rw [← hlg] at hδp hLipc
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log A := ⟨_, rfl⟩
  have hNd : (1 : ℝ) ≤ (N : ℝ) ^ d := one_le_pow₀ (by linarith)
  have hApos : 0 < A := by rw [hA]; positivity
  have hTle : T ≤ ((d : ℝ) + 5) * lg := by
    have h1 : (2 + 4 * (K : ℝ)) * 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : A ≤ (N : ℝ) ^ (d + 5) := by
      rw [hA]
      calc (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3
          = ((2 + 4 * (K : ℝ)) * 2) * ((N : ℝ) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (d + 5) := by ring
    rw [hT, hlg]
    calc Real.log A ≤ Real.log ((N : ℝ) ^ (d + 5)) := Real.log_le_log hApos h2
      _ = ((d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hTge : lg ≤ T := by
    rw [hT, hlg]
    refine Real.log_le_log hNpos ?_
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (N : ℝ)]
    have h12 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * (N : ℝ) ^ d) := by nlinarith
    have h13 := mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
    rw [hA]; linarith
  have hTpos : 0 < T := by linarith
  have hεeq : ε = 3 * Real.sqrt (N * M * T) := by rw [hε, hT, hA]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * M * lg) := ⟨_, rfl⟩
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hQeq : Q = δp * N := by
    have hsq : (δp * N) ^ 2 = N * M * lg := by
      rw [mul_pow, hδp, Real.sq_sqrt (by positivity)]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt ((d : ℝ) + 5) := ⟨_, rfl⟩
  rw [← hAa] at h48 ⊢
  have hAa0 : 0 ≤ Aa := by rw [hAa]; exact Real.sqrt_nonneg _
  have hsqT : Real.sqrt (N * M * T) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ N * M)
    exact this.trans (le_of_eq (by ring))
  have hsqTge : Q ≤ Real.sqrt (N * M * T) := by
    rw [hQ]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTge (by positivity))
  have hsq : 0 < Real.sqrt (N * M * T) := Real.sqrt_pos.mpr (by positivity)
  have hεpos : 0 < ε := by rw [hεeq]; positivity
  have he : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ)) = 2 * Lip := by field_simp
  have hnum : ε + 2 * Lip ≤ 6 * Aa * δp * N := by
    calc ε + 2 * Lip ≤ 3 * Real.sqrt (N * M * T) + 3 * Q := by rw [hεeq, hQ]; linarith
      _ ≤ 6 * Real.sqrt (N * M * T) := by linarith
      _ ≤ 6 * (Aa * Q) := by linarith
      _ = 6 * Aa * δp * N := by rw [hQeq]; ring
  have hδle : (ε + 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ))) / N ≤ 6 * Aa * δp := by
    rw [he, div_le_iff₀ hNpos]; exact hnum
  have hεN : ε ≤ 5 * N / 2 := by
    have h1 : ε ≤ 6 * Aa * δp * N := by linarith
    have h2 : 6 * Aa * δp * N ≤ N / 8 := by
      have := mul_le_mul_of_nonneg_right h48 hNpos.le
      linarith
    linarith
  have hε2 : ε ^ 2 = 9 * (N * M * T) := by
    rw [hεeq, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hD : 0 < 4 * (N * M) + 2 * M * ε := by positivity
  have hTcond : T * (4 * (N * M) + 2 * M * ε) ≤ ε ^ 2 := by
    rw [hε2]
    have hMT : 0 ≤ M * T := by positivity
    have h1 : 2 * M * ε * T ≤ 5 * (N * M * T) := by
      nlinarith [mul_le_mul_of_nonneg_left hεN hMT]
    nlinarith
  have he1 : Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ 1 / A := by
    have h1 : -ε ^ 2 / (4 * (N * M) + 2 * M * ε) ≤ -Real.log A := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD, ← hT]; exact hTcond
    calc Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ Real.exp (-Real.log A) :=
          Real.exp_le_exp.mpr h1
      _ = 1 / A := by rw [Real.exp_neg, Real.exp_log hApos, one_div]
  refine ⟨hεpos, hδle, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left h48 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    linarith
  · calc ((N : ℕ) : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        ≤ (N : ℝ) ^ d * (2 * (1 / A)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
      _ = 1 / ((2 + 4 * (K : ℝ)) * (N : ℝ) ^ 3) := by rw [hA]; field_simp
      _ ≤ 1 / (N : ℝ) ^ 3 := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
          nlinarith

theorem rateCfin_ge (d : ℕ) : 48 * Real.sqrt ((d : ℝ) + 5) ≤ rateCfin d := by
  have hc := cvConst_nonneg
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRB0 : 0 ≤ rateRB d := Real.sqrt_nonneg _
  have hmax : 0 ≤ max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt ((d : ℝ) + 5) * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRB d)
        + 12 * Real.sqrt ((d : ℝ) + 5) * rateRB d)) :=
    le_max_of_le_right (by positivity)
  unfold rateCfin
  have : 0 ≤ 3 * 2 ^ d * max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt ((d : ℝ) + 5) * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRB d)
        + 12 * Real.sqrt ((d : ℝ) + 5) * rateRB d)) := by positivity
  linarith

set_option maxHeartbeats 1600000 in
/-- **Eigenvalues of the graph Laplacian on the torus, part (ii), with the normalisation parameters
    chosen.** As `heat_eig_paper_sample` with the grid parameter `g = N` and the tolerance
    `ε = 3 √(N M T)`: the normalisation error satisfies `δ ≤ 6 √(d+5) δ'` (so `c₁ = 6 √(d+5)` is no
    longer a hypothesis) and the probability of the normalisation event is at most `1/N³`. The
    remaining hypotheses on numbers are `η ≤ c₂ δ'` (tolerance of the Gram matrix) and the condition
    `e^{-2π²σ R} 2^d ≤ c₃ δ'` on the cut-off of `H`. -/
theorem heat_eig_paper_sample_N {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {M Lip δp η R c2 c3 : ℝ}
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1)
    (hη0 : 0 ≤ η)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hηc : η ≤ c2 * δp)
    (hR0 : 0 ≤ R) (htail : Real.exp (-(2 * Real.pi ^ 2 * σ) * R) * 2 ^ d ≤ c3 * δp) :
    μ.real {ω | ¬ ∀ r : ℝ, 0 < r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
        1 ≤ (K : ℝ) * ((2 * Real.pi ^ 2 * σ) * r) →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val →
          j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card →
          2 * ((6 * (6 * Real.sqrt ((d : ℝ) + 5)) + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp)
              * (1 + Real.sqrt (2 * Real.pi * r)) ^ d
            ≤ Real.exp (-1) * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ 4 * Real.exp 1 * (6 * (6 * Real.sqrt ((d : ℝ) + 5)) + rateCfin d + c3 + c2 * (1 + 2 * 2 ^ d)) * δp
              * Real.sqrt (4 * Real.pi ^ 2 * r / σ) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d}
      ≤ 2 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3
        + (Fintype.card (modeSet d H) : ℝ) ^ 2 * (2 * Real.exp (-(N * η / 2) ^ 2 / (2 * N))) := by
  have hN : 0 < N := by omega
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hK)
  have h48 : 48 * Real.sqrt ((d : ℝ) + 5) * δp ≤ 1 := by
    have h1 : 48 * Real.sqrt ((d : ℝ) + 5) * δp ≤ rateCfin d * δp :=
      mul_le_mul_of_nonneg_right (rateCfin_ge d) hδp0
    have h2 : rateCfin d * δp ≤ rateCfin d * δp * Real.sqrt K :=
      le_mul_of_one_le_right (mul_nonneg (rateCfin_nonneg d) hδp0) hsK1
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * M
      * Real.log ((2 + 4 * K) * (2 * ((N : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨p1, p2, p3, p4⟩ := param_choice d N K hN12 hK hKN hMpos hLip0 hδp hLipc h48 hε
  have h := heat_eig_paper_sample hσ hσ1 d N K X h_indep hX hlaw hN12 hK hKN H hH0 hH2 (g := N) hN
    hMdef hLipdef hδp hLipc hKσ hsmall p1 rfl p3 hη0 hR
    (c1 := 6 * Real.sqrt ((d : ℝ) + 5)) (by positivity) hc2 hc3 p2 hηc hR0 htail
  refine h.trans ?_
  linarith

end EigParams

section EigFinal
open Matrix

/-- **The choice of the tolerance of the Gram matrix.** With `η = √(8(3 + 2a)) δ'`,
    `δ' = √(M log N/N)`, `M ≥ 1` and at most `N^a` modes, the term of the Gram matrix in the
    probability is at most `2/N³`. -/
theorem gram_choice {N a F : ℕ} (hN : 2 ≤ N) (hF : F ≤ N ^ a) {M δp : ℝ} (hM : 1 ≤ M)
    (hδp : δp = Real.sqrt (M * Real.log N / N)) :
    (F : ℝ) ^ 2 * (2 * Real.exp (-(N * (Real.sqrt (8 * (3 + 2 * (a : ℝ))) * δp) / 2) ^ 2 / (2 * N)))
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlg : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hFr : (F : ℝ) ≤ (N : ℝ) ^ a := by exact_mod_cast hF
  have hsq : Real.sqrt (8 * (3 + 2 * (a : ℝ))) ^ 2 = 8 * (3 + 2 * (a : ℝ)) :=
    Real.sq_sqrt (by positivity)
  have hδ2 : δp ^ 2 = M * Real.log N / N := by rw [hδp, Real.sq_sqrt (by positivity)]
  have hexpo : -(N * (Real.sqrt (8 * (3 + 2 * (a : ℝ))) * δp) / 2) ^ 2 / (2 * N)
      = -((3 + 2 * (a : ℝ)) * (M * Real.log N)) := by
    have e : (N * (Real.sqrt (8 * (3 + 2 * (a : ℝ))) * δp) / 2) ^ 2
        = (N : ℝ) ^ 2 * (Real.sqrt (8 * (3 + 2 * (a : ℝ))) ^ 2 * δp ^ 2) / 4 := by ring
    rw [e, hsq, hδ2]
    field_simp
    ring
  have hle : Real.exp (-((3 + 2 * (a : ℝ)) * (M * Real.log N)))
      ≤ 1 / (N : ℝ) ^ (3 + 2 * a) := by
    have h1 : ((3 + 2 * a : ℕ) : ℝ) * Real.log N ≤ (3 + 2 * (a : ℝ)) * (M * Real.log N) := by
      push_cast
      have : Real.log N ≤ M * Real.log N := le_mul_of_one_le_left hlg hM
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc Real.exp (-((3 + 2 * (a : ℝ)) * (M * Real.log N)))
        ≤ Real.exp (-(((3 + 2 * a : ℕ) : ℝ) * Real.log N)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / (N : ℝ) ^ (3 + 2 * a) := by
          rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hNpos, one_div]
  rw [hexpo]
  have hF2 : (F : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * a) := by
    calc (F : ℝ) ^ 2 ≤ ((N : ℝ) ^ a) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg F) hFr 2
      _ = (N : ℝ) ^ (2 * a) := by rw [← pow_mul, mul_comm]
  calc (F : ℝ) ^ 2 * (2 * Real.exp (-((3 + 2 * (a : ℝ)) * (M * Real.log N))))
      ≤ (N : ℝ) ^ (2 * a) * (2 * (1 / (N : ℝ) ^ (3 + 2 * a))) :=
        mul_le_mul hF2 (by linarith) (by positivity) (by positivity)
    _ = 2 / (N : ℝ) ^ 3 := by
        rw [pow_add]
        field_simp

set_option maxHeartbeats 1600000 in
/-- **Eigenvalues of the graph Laplacian on the torus, part (ii), all tolerances chosen.** As
    `heat_eig_paper_sample_N` with the tolerance `η = √(8(3 + 2a)) δ'` of the Gram matrix, for a set
    `H` with at most `N^a` modes: the exceptional event has probability at most `5/N³`. The remaining
    hypothesis on `H` is the condition `e^{-2π²σ R} 2^d ≤ c₃ δ'` on its cut-off. -/
theorem heat_eig_paper_sample_final {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {M Lip δp R c3 : ℝ} (a : ℕ)
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1)
    (hF : Fintype.card (modeSet d H) ≤ N ^ a)
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (hc3 : 0 ≤ c3)
    (hR0 : 0 ≤ R) (htail : Real.exp (-(2 * Real.pi ^ 2 * σ) * R) * 2 ^ d ≤ c3 * δp) :
    μ.real {ω | ¬ ∀ r : ℝ, 0 < r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
        1 ≤ (K : ℝ) * ((2 * Real.pi ^ 2 * σ) * r) →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          1 + 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val →
          j.val ≤ 2 * (H.filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card →
          2 * ((6 * (6 * Real.sqrt ((d : ℝ) + 5)) + rateCfin d + c3 + Real.sqrt (8 * (3 + 2 * (a : ℝ))) * (1 + 2 * 2 ^ d)) * δp)
              * (1 + Real.sqrt (2 * Real.pi * r)) ^ d
            ≤ Real.exp (-1) * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ 4 * Real.exp 1 * (6 * (6 * Real.sqrt ((d : ℝ) + 5)) + rateCfin d + c3 + Real.sqrt (8 * (3 + 2 * (a : ℝ))) * (1 + 2 * 2 ^ d)) * δp
              * Real.sqrt (4 * Real.pi ^ 2 * r / σ) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d}
      ≤ 5 / (N : ℝ) ^ 3 := by
  have hsqM : 0 ≤ Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ)) := Real.sqrt_nonneg _
  have hMge : 1 ≤ M := by rw [hMdef]; exact one_le_pow₀ (by linarith)
  have hg := gram_choice (by omega : 2 ≤ N) hF hMge hδp
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have h := heat_eig_paper_sample_N hσ hσ1 d N K X h_indep hX hlaw hN12 hK hKN H hH0 hH2
    hMdef hLipdef hδp hLipc hKσ hsmall
    (η := Real.sqrt (8 * (3 + 2 * (a : ℝ))) * δp) (by positivity) hR
    (c2 := Real.sqrt (8 * (3 + 2 * (a : ℝ)))) (Real.sqrt_nonneg _) hc3 le_rfl hR0 htail
  refine h.trans ?_
  have e : (5 : ℝ) / (N : ℝ) ^ 3 = 2 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3 + 2 / (N : ℝ) ^ 3 := by ring
  rw [e]
  linarith

end EigFinal

section EigTorusFinal
open Matrix

/-- A frequency is lexicographically positive if its first nonzero coordinate is positive. -/
def lexPos (d : ℕ) (n : Fin d → ℤ) : Prop := ∃ i, 0 < n i ∧ ∀ j, j < i → n j = 0

theorem lexPos_ne_zero {d : ℕ} {n : Fin d → ℤ} (h : lexPos d n) : n ≠ 0 := by
  obtain ⟨i, hi, -⟩ := h
  intro h0
  rw [h0] at hi
  simp at hi

theorem lexPos_neg_not {d : ℕ} {n : Fin d → ℤ} (h : lexPos d n) : ¬ lexPos d (-n) := by
  obtain ⟨i, hi, hlt⟩ := h
  rintro ⟨i', hi', hlt'⟩
  simp only [Pi.neg_apply] at hi' hlt'
  rcases lt_trichotomy i i' with h1 | h1 | h1
  · have := hlt' i h1
    omega
  · subst h1; omega
  · have := hlt i' h1
    omega

theorem lexPos_or_neg {d : ℕ} {n : Fin d → ℤ} (h : n ≠ 0) : lexPos d n ∨ lexPos d (-n) := by
  classical
  have hne : (Finset.univ.filter fun i : Fin d => n i ≠ 0).Nonempty := by
    by_contra hcon
    apply h
    funext i
    by_contra hi
    have hi' : n i ≠ 0 := by simpa using hi
    exact hcon ⟨i, by simp [hi']⟩
  obtain ⟨i0, hi0⟩ : ∃ i0, i0 = (Finset.univ.filter fun i : Fin d => n i ≠ 0).min' hne := ⟨_, rfl⟩
  have hmem : i0 ∈ Finset.univ.filter fun i : Fin d => n i ≠ 0 := by
    rw [hi0]; exact Finset.min'_mem _ hne
  have hn0 : n i0 ≠ 0 := (Finset.mem_filter.mp hmem).2
  have hlt : ∀ j, j < i0 → n j = 0 := by
    intro j hj
    by_contra hnj
    have hjm : j ∈ Finset.univ.filter fun i : Fin d => n i ≠ 0 := by simp [hnj]
    have := Finset.min'_le _ j hjm
    rw [← hi0] at this
    exact absurd hj (not_lt.mpr this)
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · right
    exact ⟨i0, by simp only [Pi.neg_apply]; omega, fun j hj => by
      simp only [Pi.neg_apply]; rw [hlt j hj]; simp⟩
  · left
    exact ⟨i0, hpos, hlt⟩

/-- The half of the frequencies with `|n|² < R` inside the cube `[-m, m]^d`: the lexicographically
    positive ones. -/
noncomputable def halfFreq (d m : ℕ) (R : ℝ) : Finset (Fin d → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(m : ℤ)) m).filter
    fun n => lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < R

theorem mem_halfFreq {d m : ℕ} {R : ℝ} (hm : R ≤ (m : ℝ) ^ 2) (n : Fin d → ℤ) :
    n ∈ halfFreq d m R ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < R := by
  classical
  unfold halfFreq
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h1 : ((n i : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((n i : ℤ) : ℝ) ^ 2) (fun j _ => _root_.sq_nonneg _)
      (Finset.mem_univ i)
  have h2 : ((n i : ℤ) : ℝ) ^ 2 < (m : ℝ) ^ 2 := by linarith [h.2]
  have h3 := abs_lt_of_sq_lt_sq' h2 (Nat.cast_nonneg m)
  constructor
  · have : (-(m : ℝ)) ≤ ((n i : ℤ) : ℝ) := h3.1.le
    exact_mod_cast this
  · have : ((n i : ℤ) : ℝ) ≤ (m : ℝ) := h3.2.le
    exact_mod_cast this

/-- **The half-set of frequencies has the properties required of `H`:** no zero frequency, no pair
    `n, -n`, every other nonzero frequency has `|n|² ≥ R`; and it has at most `(2m+1)^d` elements. -/
theorem halfFreq_props (d m : ℕ) {R : ℝ} (hm : R ≤ (m : ℝ) ^ 2) :
    (∀ n ∈ halfFreq d m R, n ≠ 0)
      ∧ (∀ a ∈ halfFreq d m R, ∀ n ∈ halfFreq d m R, a + n ≠ 0)
      ∧ (∀ n : Fin d → ℤ, n ≠ 0 → n ∉ halfFreq d m R → -n ∉ halfFreq d m R →
          R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ∧ (halfFreq d m R).card ≤ (2 * m + 1) ^ d := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    exact lexPos_ne_zero ((mem_halfFreq hm n).mp hn).1
  · intro a ha n hn hsum
    have hna : n = -a := by
      have := eq_neg_of_add_eq_zero_right hsum
      exact this
    rw [hna] at hn
    exact lexPos_neg_not ((mem_halfFreq hm a).mp ha).1 ((mem_halfFreq hm (-a)).mp hn).1
  · intro n hn0 hn hnn
    by_contra hlt
    rw [not_le] at hlt
    have hneg : ∑ i, (((-n) i : ℤ) : ℝ) ^ 2 = ∑ i, ((n i : ℤ) : ℝ) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by simp
    rcases lexPos_or_neg hn0 with h | h
    · exact hn ((mem_halfFreq hm n).mpr ⟨h, hlt⟩)
    · exact hnn ((mem_halfFreq hm (-n)).mpr ⟨h, by rw [hneg]; exact hlt⟩)
  · unfold halfFreq
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Fintype.card_piFinset]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Int.card_Icc]
    apply le_of_eq
    congr 1
    omega

/-- The number of modes of a set of frequencies. -/
theorem modeSet_card_le (d : ℕ) (H : Finset (Fin d → ℤ)) :
    Fintype.card (modeSet d H) ≤ 1 + 2 * H.card := by
  classical
  rw [Fintype.card_coe]
  unfold modeSet
  have h1 := Finset.card_insert_le (none : Option ((Fin d → ℤ) × Bool))
    ((H.image fun n => some (n, false)) ∪ (H.image fun n => some (n, true)))
  have h2 := Finset.card_union_le (H.image fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
    (H.image fun n => some (n, true))
  have h3 := Finset.card_image_le (s := H)
    (f := fun n => (some (n, false) : Option ((Fin d → ℤ) × Bool)))
  have h4 := Finset.card_image_le (s := H)
    (f := fun n => (some (n, true) : Option ((Fin d → ℤ) × Bool)))
  omega

set_option maxHeartbeats 1600000 in
/-- **Eigenvalues of the graph Laplacian on the torus, part (ii), with the set of frequencies
    chosen.** As `heat_eig_paper_sample_final` with `H = halfFreq d m R`, the lexicographically
    positive frequencies with `|n|² < R` (`R ≤ m²`): the properties required of `H` are proved, and
    the number of modes is at most `1 + 2 (2m+1)^d`. HYPOTHESES on numbers that remain: those of the
    kernel theorem, `1 + 2 (2m+1)^d ≤ N^a`, the condition `e^{-2π²σ R} 2^d ≤ c₃ δ'` on the cut-off, and
    the size condition for each shell. The exceptional event has probability at most `5/N³`. -/
theorem heat_eig_torus_final {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N) (hK : 0 < K) (hKN : K ≤ N)
    (m : ℕ)
    {M Lip δp R c3 : ℝ} (a : ℕ)
    (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hKσ : (K : ℝ) * σ ≤ 1)
    (hsmall : rateCfin d * δp * Real.sqrt K ≤ 1)
    (hRm : R ≤ (m : ℝ) ^ 2) (hF : 1 + 2 * (2 * m + 1) ^ d ≤ N ^ a)
    (hc3 : 0 ≤ c3)
    (hR0 : 0 ≤ R) (htail : Real.exp (-(2 * Real.pi ^ 2 * σ) * R) * 2 ^ d ≤ c3 * δp) :
    μ.real {ω | ¬ ∀ r : ℝ, 0 < r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
        1 ≤ (K : ℝ) * ((2 * Real.pi ^ 2 * σ) * r) →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          1 + 2 * ((halfFreq d m R).filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r).card ≤ j.val →
          j.val ≤ 2 * ((halfFreq d m R).filter fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r).card →
          2 * ((6 * (6 * Real.sqrt ((d : ℝ) + 5)) + rateCfin d + c3 + Real.sqrt (8 * (3 + 2 * (a : ℝ))) * (1 + 2 * 2 ^ d)) * δp)
              * (1 + Real.sqrt (2 * Real.pi * r)) ^ d
            ≤ Real.exp (-1) * Real.sqrt ((2 * Real.pi ^ 2 * σ) * r) →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ 4 * Real.exp 1 * (6 * (6 * Real.sqrt ((d : ℝ) + 5)) + rateCfin d + c3 + Real.sqrt (8 * (3 + 2 * (a : ℝ))) * (1 + 2 * 2 ^ d)) * δp
              * Real.sqrt (4 * Real.pi ^ 2 * r / σ) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d}
      ≤ 5 / (N : ℝ) ^ 3 := by
  obtain ⟨p1, p2, p3, p4⟩ := halfFreq_props d m hRm
  have hcard : Fintype.card (modeSet d (halfFreq d m R)) ≤ N ^ a :=
    (modeSet_card_le d (halfFreq d m R)).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_left 2 p4) 1).trans hF)
  exact heat_eig_paper_sample_final hσ hσ1 d N K X h_indep hX hlaw hN12 hK hKN (halfFreq d m R) p1 p2
    a hMdef hLipdef hδp hLipc hKσ hsmall hcard p3 hc3 hR0 htail

end EigTorusFinal

/-! ## The kernel recursion in the mean (`L¹` form), with a stationary weight -/

section KernelL1
open Matrix

/-- One step of the weighted `L¹` contraction: for `P ≥ 0` with a stationary weight `w ≥ 0`
    (`∑_b w_b P_{bj} = w_j`), `∑_b w_b |(P v)_b| ≤ ∑_b w_b |v_b|`. -/
theorem weighted_l1_step {n : Type} [Fintype n] (P : Matrix n n ℝ) (h0 : ∀ i j, 0 ≤ P i j)
    (w : n → ℝ) (hw0 : ∀ b, 0 ≤ w b) (hstat : ∀ j, ∑ b, w b * P b j = w j) (v : n → ℝ) :
    ∑ b, w b * |(P *ᵥ v) b| ≤ ∑ b, w b * |v b| := by
  have h1 : ∀ b, w b * |(P *ᵥ v) b| ≤ ∑ j, w b * P b j * |v j| := by
    intro b
    have : |(P *ᵥ v) b| ≤ ∑ j, P b j * |v j| := by
      calc |(P *ᵥ v) b| = |∑ j, P b j * v j| := rfl
        _ ≤ ∑ j, |P b j * v j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, P b j * |v j| := Finset.sum_congr rfl fun j _ => by
            rw [abs_mul, abs_of_nonneg (h0 b j)]
    calc w b * |(P *ᵥ v) b| ≤ w b * ∑ j, P b j * |v j| := mul_le_mul_of_nonneg_left this (hw0 b)
      _ = ∑ j, w b * P b j * |v j| := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  calc ∑ b, w b * |(P *ᵥ v) b| ≤ ∑ b, ∑ j, w b * P b j * |v j| := Finset.sum_le_sum fun b _ => h1 b
    _ = ∑ j, ∑ b, w b * P b j * |v j| := Finset.sum_comm
    _ = ∑ j, w j * |v j| := Finset.sum_congr rfl fun j _ => by
        rw [← Finset.sum_mul, hstat j]

/-- **Weighted `L¹` contraction of the powers of a walk with a stationary weight.** -/
theorem weighted_l1_pow {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw0 : ∀ b, 0 ≤ w b)
    (hstat : ∀ j, ∑ b, w b * P b j = w j) (k : ℕ) (v : n → ℝ) :
    ∑ b, w b * |((P ^ k) *ᵥ v) b| ≤ ∑ b, w b * |v b| := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    have e : (P ^ (k + 1)) *ᵥ v = (P ^ k) *ᵥ (P *ᵥ v) := by
      rw [pow_succ, ← mulVec_mulVec]
    rw [e]
    exact (ih (P *ᵥ v)).trans (weighted_l1_step P h0 w hw0 hstat v)

/-- The unweighted form: if `wlo ≤ w_b ≤ whi` with `wlo > 0`, then
    `∑_b |(P^k v)_b| ≤ (whi/wlo) ∑_b |v_b|`. -/
theorem l1_pow_le {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (w : n → ℝ) {wlo whi : ℝ} (hlo : 0 < wlo)
    (hw : ∀ b, wlo ≤ w b ∧ w b ≤ whi) (hstat : ∀ j, ∑ b, w b * P b j = w j) (k : ℕ)
    (v : n → ℝ) :
    ∑ b, |((P ^ k) *ᵥ v) b| ≤ whi / wlo * ∑ b, |v b| := by
  have hw0 : ∀ b, 0 ≤ w b := fun b => hlo.le.trans (hw b).1
  have h := weighted_l1_pow P h0 w hw0 hstat k v
  have h1 : wlo * ∑ b, |((P ^ k) *ᵥ v) b| ≤ ∑ b, w b * |((P ^ k) *ᵥ v) b| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hw b).1 (abs_nonneg _)
  have h2 : ∑ b, w b * |v b| ≤ whi * ∑ b, |v b| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hw b).2 (abs_nonneg _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hlo]
  linarith

/-- **The kernel recursion in the mean (`L¹` form).** For a walk `P ≥ 0` with a stationary weight
    between `wlo > 0` and `whi`: if `∑_b |c_b - g_1(b)| ≤ V` (last step) and the defects satisfy
    `∑_b |(P g_{m+1} - g_{m+2})_b| ≤ hb_{m+1}` for `m ≤ j`, then
    `∑_a |(P^{j+1} c)_a - g_{j+2}(a)| ≤ (whi/wlo) (V + ∑_{m ≤ j} hb_{m+1})`.
    No induction on the size of the powers and no smallness condition is needed. -/
theorem l1_kernel_bound {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (P : Matrix n n ℝ)
    (h0 : ∀ i j, 0 ≤ P i j) (w : n → ℝ) {wlo whi : ℝ} (hlo : 0 < wlo)
    (hw : ∀ b, wlo ≤ w b ∧ w b ≤ whi) (hstat : ∀ j, ∑ b, w b * P b j = w j)
    (g : ℕ → n → ℝ) (c : n → ℝ) {V : ℝ} (hc : ∑ b, |c b - g 1 b| ≤ V) (hb : ℕ → ℝ) (j : ℕ)
    (hbar : ∀ m, m < j + 1 → ∑ b, |(P *ᵥ g (m + 1) - g (m + 2)) b| ≤ hb (m + 1)) :
    ∑ a, |((P ^ (j + 1)) *ᵥ c) a - g (j + 2) a|
      ≤ whi / wlo * (V + ∑ m ∈ Finset.range (j + 1), hb (m + 1)) := by
  have hr0 : 0 ≤ whi / wlo := div_nonneg (hlo.le.trans ((hw (Classical.arbitrary n)).1.trans
    (hw (Classical.arbitrary n)).2)) hlo.le
  have hsplit : ∀ a, ((P ^ (j + 1)) *ᵥ c) a - g (j + 2) a
      = ((P ^ (j + 1)) *ᵥ (c - g 1)) a
        + ∑ m ∈ Finset.range (j + 1),
            ((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a := by
    intro a
    have ht := congrFun (lax_telescope P g (j + 1)) a
    rw [Finset.sum_apply] at ht
    rw [← ht, mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  calc ∑ a, |((P ^ (j + 1)) *ᵥ c) a - g (j + 2) a|
      ≤ ∑ a, (|((P ^ (j + 1)) *ᵥ (c - g 1)) a|
          + ∑ m ∈ Finset.range (j + 1),
              |((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a|) :=
        Finset.sum_le_sum fun a _ => by
          rw [hsplit a]
          exact (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ a, |((P ^ (j + 1)) *ᵥ (c - g 1)) a|
          + ∑ m ∈ Finset.range (j + 1),
              ∑ a, |((P ^ (j + 1 - 1 - m)) *ᵥ (P *ᵥ g (m + 1) - g (m + 2))) a| := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ whi / wlo * V + ∑ m ∈ Finset.range (j + 1), whi / wlo * hb (m + 1) := by
        refine add_le_add ?_ (Finset.sum_le_sum fun m hm => ?_)
        · refine (l1_pow_le P h0 w hlo hw hstat (j + 1) (c - g 1)).trans ?_
          exact mul_le_mul_of_nonneg_left (by simpa using hc) hr0
        · refine (l1_pow_le P h0 w hlo hw hstat _ _).trans ?_
          exact mul_le_mul_of_nonneg_left (hbar m (Finset.mem_range.mp hm)) hr0
    _ = whi / wlo * (V + ∑ m ∈ Finset.range (j + 1), hb (m + 1)) := by
        rw [mul_add, Finset.mul_sum]

/-- **The stationary weight of the walk of a symmetric kernel.** For `P = walkMatrix K ρ` with a
    symmetric kernel `K` and `ρ > 0`, the weight `w_b = (∑_l K_{bl}/ρ_l)/ρ_b` satisfies
    `w_b P_{bj} = K_{bj}/(ρ_b ρ_j)`, hence `∑_b w_b P_{bj} = w_j`. -/
theorem walkMatrix_stationary {n : Type} [Fintype n] (K : n → n → ℝ) (ρ : n → ℝ)
    (hsym : ∀ a b, K a b = K b a) (hρ : ∀ a, 0 < ρ a)
    (hS : ∀ b, 0 < ∑ l, K b l / ρ l) (j : n) :
    ∑ b, ((∑ l, K b l / ρ l) / ρ b) * walkMatrix K ρ b j = (∑ l, K j l / ρ l) / ρ j := by
  have e : ∀ b, ((∑ l, K b l / ρ l) / ρ b) * walkMatrix K ρ b j = K j b / ρ b / ρ j := by
    intro b
    rw [walkMatrix_apply' K ρ b j (hρ b).ne', hsym b j]
    have h1 := (hS b).ne'
    have h2 := (hρ b).ne'
    have h3 := (hρ j).ne'
    field_simp
  rw [Finset.sum_congr rfl fun b _ => e b, ← Finset.sum_div]

/-- **The kernel theorem in the mean (`L¹` form) for the sampled walk, deterministic part.**
    On the good event (normalisation `|ρ_j - 1| ≤ δ ≤ 1/8`, estimate (ii) for `1 ≤ m ≤ j+1`, estimate
    (iii) at the four times): for every `i`,
    `∑_a |N P^{j+2}(a,i) - p_{(j+2)σ}(x_a - x_i)| ≤ (9/7) (4δ N(1+δ) + ∑_{m ≤ j} N · heatEtaBar_{m+1})`.
    No smallness condition and no induction on the size of the powers. -/
theorem heat_kernel_l1_det {σ M L δ δ3 : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 0 < N)
    (x : ℕ → FlatTorus d) (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hδ3 : 0 ≤ δ3)
    (hρ : ∀ j, |heatRho d σ N x j - 1| ≤ δ) (j : ℕ)
    (hdef : ∀ m, 1 ≤ m → m ≤ j + 1 → ∀ b, b < N → ∀ i, i < N →
      |heatDefect d σ N m x b i| ≤ heatDefBound d σ N m M L δ (x b - x i))
    (hA : ∀ m, 1 ≤ m → m ≤ j + 1 → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hB : ∀ m, 1 ≤ m → m ≤ j + 1 → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hC : ∀ m, 1 ≤ m → m ≤ j + 1 → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    (hC12 : ∀ m, 1 ≤ m → m ≤ j + 1 → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    (i : Fin N) :
    ∑ a : Fin N,
        |(N : ℝ) * ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ (j + 2)) a i - heatP d σ (j + 2) (x a - x i)|
      ≤ 9 / 7 * (4 * δ * (N * (1 + δ))
          + ∑ m ∈ Finset.range (j + 1), N * heatEtaBar d σ N (m + 1) M L δ δ3) := by
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hρb := fun j => abs_le.mp (hρ j)
  have hρpos : ∀ j, 0 < heatRho d σ N x j := fun j => by linarith [(hρb j).1]
  have h1m : 0 < 1 - δ := by linarith
  have h1p : 0 < 1 + δ := by linarith
  obtain ⟨K, hKdef⟩ : ∃ K : Fin N → Fin N → ℝ,
      K = fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Fin N → ℝ, ρ = fun a : Fin N => heatRho d σ N x a := ⟨_, rfl⟩
  rw [← hKdef, ← hρdef]
  have hK0 : ∀ a j : Fin N, 0 ≤ K a j := fun a j => by
    rw [hKdef]; exact heatTorus_nonneg hcσ d _
  have hKsym : ∀ a b : Fin N, K a b = K b a := fun a b => by
    rw [hKdef]
    show heatTorus d _ (x a - x b) = heatTorus d _ (x b - x a)
    rw [← heatTorus_even, neg_sub]
  have hρp : ∀ a : Fin N, 0 < ρ a := fun a => by rw [hρdef]; exact hρpos a
  have hρlo : ∀ a : Fin N, 1 - δ ≤ ρ a := fun a => by rw [hρdef]; linarith [(hρb a).1]
  have hρhi : ∀ a : Fin N, ρ a ≤ 1 + δ := fun a => by rw [hρdef]; linarith [(hρb a).2]
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp
  have hsumK : ∀ a : Fin N, ∑ l, K a l = (N : ℝ) * ρ a := fun a => by
    rw [hKdef, hρdef]
    show ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l) = (N : ℝ) * heatRho d σ N x a
    unfold heatRho
    rw [mul_div_cancel₀ _ hNpos.ne']
    exact Fin.sum_univ_eq_sum_range
      (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l)) N
  -- the sums S_b = ∑_l K_bl/ρ_l
  have hS1 : ∀ b : Fin N, (N : ℝ) * ρ b ≤ (∑ l, K b l / ρ l) * (1 + δ) := fun b => by
    rw [← hsumK b, Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      rw [div_mul_eq_mul_div, le_div_iff₀ (hρp l)]
      exact mul_le_mul_of_nonneg_left (hρhi l) (hK0 b l)
  have hS2 : ∀ b : Fin N, (∑ l, K b l / ρ l) * (1 - δ) ≤ (N : ℝ) * ρ b := fun b => by
    rw [← hsumK b, Finset.sum_mul]
    exact Finset.sum_le_sum fun l _ => by
      rw [div_mul_eq_mul_div, div_le_iff₀ (hρp l)]
      exact mul_le_mul_of_nonneg_left (hρlo l) (hK0 b l)
  have hSpos : ∀ b : Fin N, 0 < ∑ l, K b l / ρ l := fun b => by
    have h1 : 0 < (∑ l, K b l / ρ l) * (1 + δ) :=
      lt_of_lt_of_le (mul_pos hNpos (hρp b)) (hS1 b)
    exact (mul_pos_iff_of_pos_right h1p).mp h1
  have hwlo : (0 : ℝ) < N / (1 + δ) := div_pos hNpos h1p
  have hw : ∀ b : Fin N, (N : ℝ) / (1 + δ) ≤ (∑ l, K b l / ρ l) / ρ b
      ∧ (∑ l, K b l / ρ l) / ρ b ≤ (N : ℝ) / (1 - δ) := fun b => by
    constructor
    · rw [div_le_div_iff₀ h1p (hρp b)]
      exact hS1 b
    · rw [div_le_div_iff₀ (hρp b) h1m]
      exact hS2 b
  have hP0 : ∀ a b : Fin N, 0 ≤ walkMatrix K ρ a b := fun a b => by
    rw [walkMatrix_apply' _ _ a b (hρp a).ne']
    exact div_nonneg (div_nonneg (hK0 a b) (hρp b).le) (hSpos a).le
  have hstat := walkMatrix_stationary K ρ hKsym hρp hSpos
  -- the one-step defect in matrix form
  have hterm : ∀ m, 1 ≤ m → ∀ b : Fin N,
      ((walkMatrix K ρ) *ᵥ (fun b' : Fin N => heatP d σ m (x b' - x i))) b
          - heatP d σ (m + 1) (x b - x i)
        = heatDefect d σ N m x b i := by
    intro m hm b
    have e1 : (fun b' : Fin N => heatP d σ m (x b' - x i))
        = fun b' : Fin N => heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (x b' - x i) :=
      funext fun b' => heatP_of_ne d σ (by omega) _
    rw [e1, heatP_succ, hKdef, hρdef]
    exact walk_defect_eq d σ N m hN x (fun j => (hρpos j).ne') b i
  -- last step
  have hc : ∑ b : Fin N, |(fun b : Fin N => (N : ℝ) * walkMatrix K ρ b i) b
      - (fun k (b : Fin N) => heatP d σ k (x b - x i)) 1 b| ≤ 4 * δ * (N * (1 + δ)) := by
    have h1 : ∀ b : Fin N, |(N : ℝ) * walkMatrix K ρ b i - heatP d σ 1 (x b - x i)|
        ≤ 4 * δ * K i b := fun b => by
      have h := walk_last_step K ρ hK0 (fun a => by rw [hcard]; exact hsumK a) hδ0 hδ
        (fun a => by rw [hρdef]; exact hρ a) b i
      rw [hcard] at h
      rw [heatP_one, hKsym i b]
      have e : K b i = heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x i) := by rw [hKdef]
      rw [← e]
      exact h
    calc ∑ b : Fin N, |(N : ℝ) * walkMatrix K ρ b i - heatP d σ 1 (x b - x i)|
        ≤ ∑ b : Fin N, 4 * δ * K i b := Finset.sum_le_sum fun b _ => h1 b
      _ = 4 * δ * ((N : ℝ) * ρ i) := by rw [← Finset.mul_sum, hsumK i]
      _ ≤ 4 * δ * (N * (1 + δ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hρhi i) hNpos.le) (by linarith)
  have hbar : ∀ m, m < j + 1 →
      ∑ b : Fin N, |((walkMatrix K ρ) *ᵥ (fun k (b : Fin N) => heatP d σ k (x b - x i)) (m + 1)
          - (fun k (b : Fin N) => heatP d σ k (x b - x i)) (m + 2)) b|
        ≤ (fun m : ℕ => (N : ℝ) * heatEtaBar d σ N m M L δ δ3) (m + 1) := by
    intro m hm
    have hm1 : 1 ≤ m + 1 := by omega
    have hmj : m + 1 ≤ j + 1 := by omega
    calc ∑ b : Fin N, |((walkMatrix K ρ) *ᵥ (fun k (b : Fin N) => heatP d σ k (x b - x i)) (m + 1)
          - (fun k (b : Fin N) => heatP d σ k (x b - x i)) (m + 2)) b|
        = ∑ b : Fin N, |heatDefect d σ N (m + 1) x b i| :=
          Finset.sum_congr rfl fun b _ => by
            rw [← hterm (m + 1) hm1 b]; rfl
      _ ≤ ∑ b : Fin N, heatDefBound d σ N (m + 1) M L δ (x b - x i) :=
          Finset.sum_le_sum fun b _ => hdef (m + 1) hm1 hmj b b.2 i i.2
      _ = ∑ b ∈ Finset.range N, heatDefBound d σ N (m + 1) M L δ (x b - x i) :=
          Fin.sum_univ_eq_sum_range (fun b => heatDefBound d σ N (m + 1) M L δ (x b - x i)) N
      _ ≤ _ := heat_defect_mean_det_min hσ hM hL hδ0 d N (m + 1) hN hm1 x i hδ3
          (hA (m + 1) hm1 hmj i i.2) (hB (m + 1) hm1 hmj i i.2) (hC (m + 1) hm1 hmj i i.2)
          (hC12 (m + 1) hm1 hmj i i.2)
  have hmain := l1_kernel_bound (walkMatrix K ρ) hP0 (fun b => (∑ l, K b l / ρ l) / ρ b) hwlo hw
    hstat (fun k (b : Fin N) => heatP d σ k (x b - x i))
    (fun b : Fin N => (N : ℝ) * walkMatrix K ρ b i) hc
    (fun m : ℕ => (N : ℝ) * heatEtaBar d σ N m M L δ δ3) j hbar
  have epow : ∀ a : Fin N, (((walkMatrix K ρ) ^ (j + 1)) *ᵥ
        (fun b : Fin N => (N : ℝ) * walkMatrix K ρ b i)) a
      = (N : ℝ) * ((walkMatrix K ρ) ^ (j + 2)) a i := by
    intro a
    have e2 : (walkMatrix K ρ) ^ (j + 2) = (walkMatrix K ρ) ^ (j + 1) * walkMatrix K ρ :=
      pow_succ _ _
    rw [e2, Matrix.mul_apply, Finset.mul_sum]
    show ∑ b, ((walkMatrix K ρ) ^ (j + 1)) a b * ((N : ℝ) * walkMatrix K ρ b i) = _
    exact Finset.sum_congr rfl fun b _ => by ring
  have hB0 : 0 ≤ 4 * δ * (N * (1 + δ))
      + ∑ m ∈ Finset.range (j + 1), (N : ℝ) * heatEtaBar d σ N (m + 1) M L δ δ3 := by
    refine add_nonneg (by positivity) (Finset.sum_nonneg fun m hm => ?_)
    exact (Finset.sum_nonneg fun _ _ => abs_nonneg _).trans (hbar m (Finset.mem_range.mp hm))
  have hr : (N : ℝ) / (1 - δ) / ((N : ℝ) / (1 + δ)) ≤ 9 / 7 := by
    rw [div_le_iff₀ hwlo]
    have e1 : (N : ℝ) / (1 - δ) = (N : ℝ) * (1 + δ) / ((1 - δ) * (1 + δ)) := by field_simp
    have e2 : 9 / 7 * ((N : ℝ) / (1 + δ)) = 9 / 7 * (N : ℝ) * (1 - δ) / ((1 - δ) * (1 + δ)) := by
      field_simp
    rw [e1, e2]
    refine div_le_div_of_nonneg_right ?_ (mul_pos h1m h1p).le
    nlinarith [mul_nonneg hNpos.le (by linarith : (0 : ℝ) ≤ 1 / 8 - δ)]
  calc ∑ a : Fin N, |(N : ℝ) * ((walkMatrix K ρ) ^ (j + 2)) a i - heatP d σ (j + 2) (x a - x i)|
      = ∑ a : Fin N, |(((walkMatrix K ρ) ^ (j + 1)) *ᵥ
            (fun b : Fin N => (N : ℝ) * walkMatrix K ρ b i)) a
          - (fun k (b : Fin N) => heatP d σ k (x b - x i)) (j + 2) a| :=
        Finset.sum_congr rfl fun a _ => by rw [epow a]
    _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_right hr hB0

/-- The conclusion of the kernel theorem in the mean: for `j + 1 < K` and every `i`,
    `∑_a |N P^{j+2}(a,i) - p_{(j+2)σ}(x_a - x_i)| ≤ (9/7) N (4δ(1+δ) + 2 a √(j+1))`. -/
def heatKernelL1 (d : ℕ) (σ δ a : ℝ) (N K : ℕ) (x : ℕ → FlatTorus d) : Prop :=
  ∀ j, j + 1 < K → ∀ i : Fin N,
    ∑ a' : Fin N,
        |(N : ℝ) * ((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ (j + 2)) a' i - heatP d σ (j + 2) (x a' - x i)|
      ≤ 9 / 7 * (N * (4 * δ * (1 + δ) + 2 * a * Real.sqrt ((j + 1 : ℕ) : ℝ)))

/-- The mean bound of the defect in closed form: `heatEtaBar_m ≤ a/√m` with `a = heatRateA`, for
    `σ ≤ 1`, `m < K`, `K σ ≤ 1` and `(2L + 2)(kb + M) √K ≤ θ N`. -/
theorem heatEtaBar_closed {σ M L δ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (d N K : ℕ) (hN : 0 < N) (hKσ : (K : ℝ) * σ ≤ 1)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N) (m : ℕ) (hm : 1 ≤ m)
    (hmK : m < K) :
    heatEtaBar d σ N m M L δ δ ≤ heatRateA d N M L δ θ / Real.sqrt m := by
  have hc := cvConst_nonneg
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmK' : (m : ℝ) ≤ K := by exact_mod_cast hmK.le
  have r1 : σ ≤ (m : ℝ) * σ := by nlinarith
  have r2 : (m : ℝ) * σ ≤ 1 := by nlinarith
  have r3 : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N := by
    have h1 : Real.sqrt m ≤ Real.sqrt K := Real.sqrt_le_sqrt hmK'
    have h2 : 0 ≤ (2 * L + 2) * (heatKbar d σ + M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hrc : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
      * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  have hcq := heatCV_heatQ hσ r1 r2 d
  have e : σ / ((m : ℝ) * σ) = 1 / m := by field_simp
  rw [e] at hcq
  unfold heatRateA
  refine heatEtaBar_le hσ hM hL hδ d N m hN hm hkb0 (Real.sqrt_nonneg _)
    (by unfold heatKbar; exact heatKB_le hσ r1 hσ1 d) ?_ r3
  rw [Real.sq_sqrt hrc]
  calc _ ≤ _ := hcq
    _ = _ := by ring

/-- **The kernel theorem in the mean, deterministic, in closed form.** On the good event, if
    `heatEtaBar_m ≤ a/√m` for `1 ≤ m < K`, then `heatKernelL1` holds. -/
theorem heat_kernel_l1_closed_det {σ M L δ δ3 : ℝ} (hσ : 0 < σ) (d N K : ℕ) (hN : 0 < N)
    (x : ℕ → FlatTorus d) (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hδ3 : 0 ≤ δ3)
    (hρ : ∀ j, |heatRho d σ N x j - 1| ≤ δ)
    (hdef : ∀ m, 1 ≤ m → m < K → ∀ b, b < N → ∀ i, i < N →
      |heatDefect d σ N m x b i| ≤ heatDefBound d σ N m M L δ (x b - x i))
    (hA : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hB : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)
        ≤ N * (1 + δ3))
    (hC : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    (hC12 : ∀ m, 1 ≤ m → m < K → ∀ i, i < N →
      ∑ b ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i)
        ≤ N * (1 + δ3))
    {a : ℝ} (ha : 0 ≤ a)
    (hEta : ∀ m, 1 ≤ m → m < K → heatEtaBar d σ N m M L δ δ3 ≤ a / Real.sqrt m) :
    heatKernelL1 d σ δ a N K x := by
  intro j hj i
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := heat_kernel_l1_det hσ d N hN x hM hL hδ0 hδ hδ3 hρ j
    (fun m h1 h2 => hdef m h1 (by omega)) (fun m h1 h2 => hA m h1 (by omega))
    (fun m h1 h2 => hB m h1 (by omega)) (fun m h1 h2 => hC m h1 (by omega))
    (fun m h1 h2 => hC12 m h1 (by omega)) i
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have hs : ∑ m ∈ Finset.range (j + 1), (N : ℝ) * heatEtaBar d σ N (m + 1) M L δ δ3
      ≤ N * (a * (2 * Real.sqrt ((j + 1 : ℕ) : ℝ))) := by
    calc ∑ m ∈ Finset.range (j + 1), (N : ℝ) * heatEtaBar d σ N (m + 1) M L δ δ3
        ≤ ∑ m ∈ Finset.range (j + 1), (N : ℝ) * (a * (1 / Real.sqrt ((m : ℝ) + 1))) :=
          Finset.sum_le_sum fun m hm => by
            have hmm := Finset.mem_range.mp hm
            have h1 := hEta (m + 1) (by omega) (by omega)
            rw [Nat.cast_succ] at h1
            rw [mul_one_div]
            exact mul_le_mul_of_nonneg_left h1 hNpos.le
      _ = N * (a * ∑ m ∈ Finset.range (j + 1), 1 / Real.sqrt ((m : ℝ) + 1)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (sum_inv_sqrt_le (j + 1)) ha) hNpos.le
  linarith

/-- **The kernel theorem in the mean for a random sample, with the normalisation events as
    hypothesis.** As `heat_kernel_sharp_whp`, for the `L¹` form: no summation hypothesis and no
    smallness condition on `W`. HYPOTHESIS `hBn` as there; HYPOTHESIS on numbers: `hEta`. -/
theorem heat_kernel_l1_whp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {M L epsn pn : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M) (hL : 0 < L)
    (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 8)
    (hBn : ∀ τ, σ ≤ τ → μ.real {ω | ∃ x : FlatTorus d,
        epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} ≤ pn)
    {a : ℝ} (ha : 0 ≤ a)
    (hEta : ∀ m, 1 ≤ m → m < K →
      heatEtaBar d σ N m M L (epsn / N) (epsn / N) ≤ a / Real.sqrt m) :
    μ.real {ω | ¬ heatKernelL1 d σ (epsn / N) a N K (fun j => X j ω)}
      ≤ pn + (pn + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))))) + (K : ℝ) * (4 * pn) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM0 : 0 ≤ M := (heatTorus_nonneg hcσ d 0).trans (hMσ 0)
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : ℝ → Set Ω, Bn = fun τ => {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} := ⟨_, rfl⟩
  have hBnP : ∀ τ, σ ≤ τ → μ.real (Bn τ) ≤ pn := fun τ hτ => by rw [hBnd]; exact hBn τ hτ
  have hBnc : ∀ τ ω, ω ∉ Bn τ → ∀ y : FlatTorus d,
      |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (y - X j ω) - N| ≤ epsn := by
    intro τ ω hω y
    by_contra h
    rw [hBnd] at hω
    exact hω ⟨y, not_le.mp h⟩
  obtain ⟨D, hDd⟩ : ∃ D : Set Ω, D = {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N,
      ∃ i ∈ Finset.range N, heatDefBound d σ N m M L (epsn / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|} := ⟨_, rfl⟩
  have hDP : μ.real D ≤ pn + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))) := by
    rw [hDd]
    exact heat_defect_whp hσ d X h_indep hX hlaw N K hN hMσ hL hepsn0 (by linarith) (hBn σ le_rfl)
  obtain ⟨A, hAd⟩ : ∃ A : ℕ → Set Ω, A = fun m : ℕ =>
      Bn ((m : ℝ) * σ + 2 * σ) ∪ (Bn (σ + (m : ℝ) * σ)
        ∪ (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ)))) := ⟨_, rfl⟩
  have hAP : ∀ m ∈ Finset.Icc 1 K, μ.real (A m) ≤ 4 * pn := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have t1 : σ ≤ (m : ℝ) * σ + 2 * σ := by nlinarith
    have t2 : σ ≤ σ + (m : ℝ) * σ := by nlinarith
    have t3 : σ ≤ 6 * ((m : ℝ) * σ) := by nlinarith
    have t4 : σ ≤ 12 * ((m : ℝ) * σ) := by nlinarith
    rw [hAd]
    have u1 := measureReal_union_le (μ := μ) (Bn ((m : ℝ) * σ + 2 * σ))
      (Bn (σ + (m : ℝ) * σ) ∪ (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ))))
    have u2 := measureReal_union_le (μ := μ) (Bn (σ + (m : ℝ) * σ))
      (Bn (6 * ((m : ℝ) * σ)) ∪ Bn (12 * ((m : ℝ) * σ)))
    have u3 := measureReal_union_le (μ := μ) (Bn (6 * ((m : ℝ) * σ))) (Bn (12 * ((m : ℝ) * σ)))
    linarith [hBnP _ t1, hBnP _ t2, hBnP _ t3, hBnP _ t4]
  have hUP : μ.real (⋃ m ∈ Finset.Icc 1 K, A m) ≤ (K : ℝ) * (4 * pn) := by
    calc μ.real (⋃ m ∈ Finset.Icc 1 K, A m) ≤ ∑ m ∈ Finset.Icc 1 K, μ.real (A m) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, 4 * pn := Finset.sum_le_sum hAP
      _ = (K : ℝ) * (4 * pn) := by simp
  have hsub : {ω | ¬ heatKernelL1 d σ (epsn / N) a N K (fun j => X j ω)}
      ⊆ Bn σ ∪ D ∪ ⋃ m ∈ Finset.Icc 1 K, A m := by
    intro ω hbad
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨hn, hD⟩, hAm⟩ := hcon
    apply hbad
    have hδ0 : 0 ≤ epsn / N := div_nonneg hepsn0 hNpos.le
    have hδ8 : epsn / N ≤ 1 / 8 := by rw [div_le_iff₀ hNpos]; linarith
    have hρ : ∀ j, |heatRho d σ N (fun j => X j ω) j - 1| ≤ epsn / N := by
      intro j
      have h := hBnc σ ω hn (X j ω)
      have e : heatRho d σ N (fun j => X j ω) j - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    have hmem : ∀ m, 1 ≤ m → m < K → m ∈ Finset.Icc 1 K := fun m h1 h2 =>
      Finset.mem_Icc.mpr ⟨h1, h2.le⟩
    refine heat_kernel_l1_closed_det hσ d N K hN (fun j => X j ω) hM0 hL.le hδ0 hδ8 hδ0 hρ
      ?_ ?_ ?_ ?_ ?_ ha hEta
    · intro m hm hmK b hb i hi
      by_contra h
      rw [hDd] at hD
      exact hD ⟨m, hmem m hm hmK, b, Finset.mem_range.mpr hb, i, Finset.mem_range.mpr hi,
        not_le.mp h⟩
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.2.1) i
    · intro m hm hmK i _
      have hA' := hAm m (hmem m hm hmK)
      rw [hAd] at hA'
      simp only [Set.mem_union, not_or] at hA'
      exact norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA'.2.2.2) i
  calc μ.real _ ≤ μ.real (Bn σ ∪ D ∪ ⋃ m ∈ Finset.Icc 1 K, A m) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real (Bn σ ∪ D) + μ.real (⋃ m ∈ Finset.Icc 1 K, A m) := measureReal_union_le _ _
    _ ≤ (μ.real (Bn σ) + μ.real D) + μ.real (⋃ m ∈ Finset.Icc 1 K, A m) :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := by linarith [hBnP σ le_rfl]

/-- **The kernel theorem in the mean (`L¹` form) for a random sample on the torus.** Independent
    uniform points on the flat torus, kernel time `σ ≤ 1`, `K σ ≤ 1`,
    `δ = (ε + 2 N Lip/g)/N ≤ 1/8`, `(2L + 2)(kb + M) √K ≤ θ N`. No hypothesis on events, no
    summation hypothesis, NO smallness condition `4δ + (1 + 4δ) W_K ≤ 1`. CONCLUSION: except on an
    event of probability at most `(2 + 4K) · 2 g^d exp(-ε²/(4NM + 2Mε)) + 4 K N² e^{-L}`, for all
    `j + 1 < K` and every `i`,
    `(1/N) ∑_a |N P^{j+2}(a,i) - p_{(j+2)σ}(x_a - x_i)| ≤ (9/7)(4δ(1+δ) + 2 a √(j+1))`,
    `a = heatRateA`. -/
theorem heat_kernel_l1_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hKσ : (K : ℝ) * σ ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N) :
    μ.real {ω | ¬ heatKernelL1 d σ δ (heatRateA d N M L δ θ) N K (fun j => X j ω)}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
            + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
        + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  have hconst : ∀ τ, σ ≤ τ →
      (∀ u, heatTorus d (2 * Real.pi ^ 2 * τ) u ≤ M)
      ∧ (∀ u u', |heatTorus d (2 * Real.pi ^ 2 * τ) u - heatTorus d (2 * Real.pi ^ 2 * τ) u'|
          ≤ Lip * dist u u') := by
    intro τ hτ
    have hcτ : 0 < 2 * Real.pi ^ 2 * τ := by have := lt_of_lt_of_le hσ hτ; positivity
    have hcc : 2 * Real.pi ^ 2 * σ ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    obtain ⟨a1, a2⟩ := heat_consts_anti hcσ hcc d
    constructor
    · intro u; rw [hMdef]; exact (heatTorus_le hcτ d u).trans a1
    · intro u u'; rw [hLipdef]
      exact (heatTorus_lipschitz hcτ d u u').trans (mul_le_mul_of_nonneg_right a2 dist_nonneg)
  have hepsn0 : 0 ≤ ε + 2 * (N * Lip) * (1 / g) := by positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hEta := fun m hm hmK =>
    heatEtaBar_closed hσ hσ1 hM0 hL.le hδ0 d N K hN hKσ hθ m hm hmK
  subst hδ
  exact heat_kernel_l1_whp hσ d X h_indep hX hlaw N K hN (hconst σ le_rfl).1 hL hepsn0 hsmall
    (fun τ hτ => heat_normalisation_whp (lt_of_lt_of_le hσ hτ) d X h_indep hX hlaw N hg
      (hconst τ hτ).1 (hconst τ hτ).2 hLip0 hε) (heatRateA_nonneg hM0 hL.le (div_nonneg hepsn0 hNpos.le) hθ0 d N) hEta

/-- Closed bound for the coefficient `heatCV` for times `s ≥ 1` (and `σ ≤ s`): the same bound
    `d c₁ 2√6 (12(1 + √(2π)))^{d-1} (σ/s)` as for `heatCV · heatQ²` at times `s ≤ 1`. -/
theorem heatCV_le_large {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : 1 ≤ s) (d : ℕ) :
    heatCV d σ s
      ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (σ / s) := by
  have hs : 0 < s := by linarith
  have hpi := Real.pi_pos
  have hc := cvConst_nonneg
  unfold heatCV
  simp only [← Real.sqrt_eq_rpow, pow_one]
  have e12 : Real.pi / (1 / (12 * s)) = 12 * Real.pi * s := by field_simp
  have e12' : 2 * Real.pi * (6 * s) = 12 * Real.pi * s := by ring
  rw [e12, e12']
  have hT : Real.sqrt (12 * Real.pi * s) = Real.sqrt (12 * Real.pi) * Real.sqrt s :=
    Real.sqrt_mul (by positivity) s
  have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hs1' : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs1
  have hT0 : 0 < Real.sqrt (12 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h2pi1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.two_le_pi])
  have h61 : 1 ≤ Real.sqrt 6 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  -- the scalar factor
  have hfac : 4 / (Real.pi * s) * ((1 + Real.sqrt (12 * Real.pi * s)) * Real.sqrt (12 * Real.pi * s))
      ≤ cvConst := by
    rw [hT]
    have h1 : (1 + Real.sqrt (12 * Real.pi) * Real.sqrt s) * (Real.sqrt (12 * Real.pi) * Real.sqrt s)
        ≤ s * ((1 + Real.sqrt (12 * Real.pi)) * Real.sqrt (12 * Real.pi)) := by
      have h2 : Real.sqrt s ≤ s := by nlinarith
      nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr h2), mul_pos hT0 hT0]
    have h3 : 4 / (Real.pi * s) * ((1 + Real.sqrt (12 * Real.pi) * Real.sqrt s)
          * (Real.sqrt (12 * Real.pi) * Real.sqrt s))
        ≤ 4 / (Real.pi * s) * (s * ((1 + Real.sqrt (12 * Real.pi)) * Real.sqrt (12 * Real.pi))) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 4 / (Real.pi * s) * (s * ((1 + Real.sqrt (12 * Real.pi)) * Real.sqrt (12 * Real.pi)))
        = 4 / Real.pi * (1 + Real.sqrt (12 * Real.pi)) * Real.sqrt (12 * Real.pi) := by
      field_simp
    have h5 : 4 / Real.pi * (1 + Real.sqrt (12 * Real.pi)) * Real.sqrt (12 * Real.pi) ≤ cvConst := by
      unfold cvConst
      have h6 : 0 ≤ 4 / Real.pi * (1 + Real.sqrt (12 * Real.pi)) * Real.sqrt (12 * Real.pi) := by
        positivity
      nlinarith
    linarith
  -- the last factor
  have hY1 : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_one (by positivity)]
    have h1 : Real.pi ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
    have h2 : Real.pi ^ 2 ≤ Real.pi ^ 2 * s := le_mul_of_one_le_right (by positivity) hs1
    nlinarith
  have hlast : (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)))
        * Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s)))
      ≤ 12 * (1 + Real.sqrt (2 * Real.pi)) := by
    have h6 : Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s))) ≤ Real.sqrt 6 := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg Real.pi, mul_pos hpi hpi]
    have h66 : Real.sqrt 6 ≤ 6 := by
      have := Real.sqrt_le_sqrt (show (6 : ℝ) ≤ 36 by norm_num)
      rwa [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    calc (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)))
          * Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s)))
        ≤ 2 * 6 := mul_le_mul (by linarith) (h6.trans h66) (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ 12 * (1 + Real.sqrt (2 * Real.pi)) := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity) hlast (d - 1)
  have hσs0 : 0 ≤ σ / s := by positivity
  have hP0 : 0 ≤ (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  calc (d : ℝ) * (σ / s * (4 / (Real.pi * s))
          * ((1 + Real.sqrt (12 * Real.pi * s)) * Real.sqrt (12 * Real.pi * s)))
        * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)))
          * Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s)))) ^ (d - 1)
      = (d : ℝ) * (σ / s * (4 / (Real.pi * s)
          * ((1 + Real.sqrt (12 * Real.pi * s)) * Real.sqrt (12 * Real.pi * s))))
        * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s)))
          * Real.sqrt (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * (σ + s)))) ^ (d - 1) := by
        ring
    _ ≤ (d : ℝ) * (σ / s * cvConst) * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by
        refine mul_le_mul ?_ hpow (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfac hσs0) (Nat.cast_nonneg d)
    _ ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (σ / s) := by
        have hA : 0 ≤ (d : ℝ) * (σ / s * cvConst) * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by
          positivity
        have e : (d : ℝ) * cvConst * (2 * Real.sqrt 6)
              * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (σ / s)
            = (2 * Real.sqrt 6)
              * ((d : ℝ) * (σ / s * cvConst) * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)) := by
          ring
        rw [e]
        nlinarith

/-- As `heatEtaBar_le`, with the product of `√heatCV` and the kernel quantity bounded directly
    (hypothesis `hZ'`), so that either branch of the minimum can be used. -/
theorem heatEtaBar_le_gen {σ M L δ kb θ r : ℝ} (hσ : 0 < σ) (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m) (hkb : 0 ≤ kb) (hr : 0 ≤ r)
    (hKB : heatKB d σ ((m : ℝ) * σ) ≤ kb)
    (hZ' : Real.sqrt (heatCV d σ ((m : ℝ) * σ))
        * min ((N : ℝ) * Real.sqrt (1 + δ))
          (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ)))
      ≤ r / Real.sqrt m * (N * (1 + δ)))
    (hθ : (2 * L + 2) * (kb + M) * Real.sqrt m ≤ θ * N) :
    heatEtaBar d σ N m M L δ δ
      ≤ 3 * (1 + δ) * ((1 + 2 * δ) * (θ + 2 * (Real.sqrt (N * M * L) / N) * r) + 2 * δ * r)
        / Real.sqrt m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hc6 : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)) := by positivity
  have hCV := heatCV_nonneg hσ hs d
  have hQ := heatQ_nonneg hc6 d
  have hKB0 := heatKB_nonneg hσ hs d
  obtain ⟨q, hq⟩ : ∃ q, q = min ((N : ℝ) * Real.sqrt (1 + δ))
      (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ))) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact le_min (by positivity) (by positivity)
  have hZ : Real.sqrt (heatCV d σ ((m : ℝ) * σ)) * q ≤ r / Real.sqrt m * (N * (1 + δ)) := by
    rw [hq]; exact hZ'
  have hT : Real.sqrt (N * (M * heatCV d σ ((m : ℝ) * σ)) * L) * q
      ≤ Real.sqrt (N * M * L) * (r / Real.sqrt m * (N * (1 + δ))) := by
    have e : Real.sqrt (N * (M * heatCV d σ ((m : ℝ) * σ)) * L)
        = Real.sqrt (N * M * L) * Real.sqrt (heatCV d σ ((m : ℝ) * σ)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1; ring
    rw [e, mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)
  have hX : heatKB d σ ((m : ℝ) * σ) * (N * (1 + δ)) + M * (N * (1 + δ))
      ≤ (kb + M) * (N * (1 + δ)) := by
    have := mul_le_mul_of_nonneg_right hKB (by positivity : (0 : ℝ) ≤ N * (1 + δ))
    linarith
  have hcore := defect_closed_core (S := Real.sqrt (N * M * L)) hNpos hL hδ hX hT hZ
  have hnum : heatDefNum d σ N m M L δ (N * (1 + δ)) (N * (1 + δ)) q
      ≤ 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * ((kb + M) * (N * (1 + δ)))
          + 2 * Real.sqrt (N * M * L) * (r / Real.sqrt m * (N * (1 + δ))))
        + 2 * δ * N * (r / Real.sqrt m * (N * (1 + δ)))) := by
    refine le_trans (le_of_eq ?_) hcore
    unfold heatDefNum
    ring
  have hu : (2 * L + 2) * (kb + M) / N ≤ θ / Real.sqrt m := by
    rw [div_le_div_iff₀ hNpos hsm]; exact hθ
  unfold heatEtaBar
  rw [← hq]
  calc heatDefNum d σ N m M L δ (N * (1 + δ)) (N * (1 + δ)) q / N
      ≤ 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * ((kb + M) * (N * (1 + δ)))
          + 2 * Real.sqrt (N * M * L) * (r / Real.sqrt m * (N * (1 + δ))))
        + 2 * δ * N * (r / Real.sqrt m * (N * (1 + δ)))) / N :=
        div_le_div_of_nonneg_right hnum hNpos.le
    _ = 3 * (1 + δ) * ((1 + 2 * δ) * ((2 * L + 2) * (kb + M) / N
          + 2 * (Real.sqrt (N * M * L) / N) * (r / Real.sqrt m)) + 2 * δ * (r / Real.sqrt m)) := by
        field_simp
    _ ≤ 3 * (1 + δ) * ((1 + 2 * δ) * (θ / Real.sqrt m
          + 2 * (Real.sqrt (N * M * L) / N) * (r / Real.sqrt m)) + 2 * δ * (r / Real.sqrt m)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := mul_le_mul_of_nonneg_left hu (by linarith : (0 : ℝ) ≤ 1 + 2 * δ)
        linarith
    _ = _ := by field_simp

/-- **The mean bound of the defect in closed form at every time:** `heatEtaBar_m ≤ a/√m` with
    `a = heatRateA`, for `σ ≤ 1` and `(2L + 2)(kb + M) √m ≤ θ N`; no restriction `m σ ≤ 1`. For
    `m σ ≤ 1` the branch with (P5) is used, for `m σ ≥ 1` the branch with the Cauchy--Schwarz
    inequality. -/
theorem heatEtaBar_closed_all {σ M L δ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (d N : ℕ) (hN : 0 < N) (m : ℕ) (hm : 1 ≤ m)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N) :
    heatEtaBar d σ N m M L δ δ ≤ heatRateA d N M L δ θ / Real.sqrt m := by
  have hc := cvConst_nonneg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have r1 : σ ≤ (m : ℝ) * σ := by nlinarith
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hrc : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
      * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  have e : σ / ((m : ℝ) * σ) = 1 / m := by field_simp
  have hc6 : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)) := by positivity
  have hCV := heatCV_nonneg hσ hs d
  have hQ := heatQ_nonneg hc6 d
  unfold heatRateA
  refine heatEtaBar_le_gen hσ hM hL hδ d N m hN hm hkb0 (Real.sqrt_nonneg _)
    (by unfold heatKbar; exact heatKB_le hσ r1 hσ1 d) ?_ hθ
  have hroot : ∀ x : ℝ, 0 ≤ x → x ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
        * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (1 / m) →
      Real.sqrt x ≤ Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
        * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)) / Real.sqrt m := by
    intro x _ hx
    rw [← Real.sqrt_div hrc]
    refine Real.sqrt_le_sqrt ?_
    rw [div_eq_mul_one_div]
    exact hx
  rcases le_total ((m : ℝ) * σ) 1 with r2 | r2
  · have hcq := heatCV_heatQ hσ r1 r2 d
    rw [e] at hcq
    have h1 := hroot _ (by positivity) hcq
    rw [Real.sqrt_mul hCV, Real.sqrt_sq hQ] at h1
    calc Real.sqrt (heatCV d σ ((m : ℝ) * σ))
          * min ((N : ℝ) * Real.sqrt (1 + δ))
            (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ)))
        ≤ Real.sqrt (heatCV d σ ((m : ℝ) * σ))
          * (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (heatCV d σ ((m : ℝ) * σ))
          * heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
  · have hcv := heatCV_le_large hσ r1 r2 d
    rw [e] at hcv
    have h1 := hroot _ hCV hcv
    have hsq1 : Real.sqrt (1 + δ) ≤ 1 + δ := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    calc Real.sqrt (heatCV d σ ((m : ℝ) * σ))
          * min ((N : ℝ) * Real.sqrt (1 + δ))
            (heatQ d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) * (N * (1 + δ)))
        ≤ Real.sqrt (heatCV d σ ((m : ℝ) * σ)) * ((N : ℝ) * Real.sqrt (1 + δ)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (heatCV d σ ((m : ℝ) * σ)) * ((N : ℝ) * (1 + δ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq1 hNpos.le) (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **The kernel theorem in the mean (`L¹` form) for a random sample on the torus.** Independent
    uniform points on the flat torus, kernel time `σ ≤ 1`, EVERY number of steps `K` (no condition `K σ ≤ 1`),
    `δ = (ε + 2 N Lip/g)/N ≤ 1/8`, `(2L + 2)(kb + M) √K ≤ θ N`. No hypothesis on events, no
    summation hypothesis, NO smallness condition `4δ + (1 + 4δ) W_K ≤ 1`. CONCLUSION: except on an
    event of probability at most `(2 + 4K) · 2 g^d exp(-ε²/(4NM + 2Mε)) + 4 K N² e^{-L}`, for all
    `j + 1 < K` and every `i`,
    `(1/N) ∑_a |N P^{j+2}(a,i) - p_{(j+2)σ}(x_a - x_i)| ≤ (9/7)(4δ(1+δ) + 2 a √(j+1))`,
    `a = heatRateA`. -/
theorem heat_kernel_l1_sample_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N) :
    μ.real {ω | ¬ heatKernelL1 d σ δ (heatRateA d N M L δ θ) N K (fun j => X j ω)}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
            + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
        + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  have hconst : ∀ τ, σ ≤ τ →
      (∀ u, heatTorus d (2 * Real.pi ^ 2 * τ) u ≤ M)
      ∧ (∀ u u', |heatTorus d (2 * Real.pi ^ 2 * τ) u - heatTorus d (2 * Real.pi ^ 2 * τ) u'|
          ≤ Lip * dist u u') := by
    intro τ hτ
    have hcτ : 0 < 2 * Real.pi ^ 2 * τ := by have := lt_of_lt_of_le hσ hτ; positivity
    have hcc : 2 * Real.pi ^ 2 * σ ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    obtain ⟨a1, a2⟩ := heat_consts_anti hcσ hcc d
    constructor
    · intro u; rw [hMdef]; exact (heatTorus_le hcτ d u).trans a1
    · intro u u'; rw [hLipdef]
      exact (heatTorus_lipschitz hcτ d u u').trans (mul_le_mul_of_nonneg_right a2 dist_nonneg)
  have hepsn0 : 0 ≤ ε + 2 * (N * Lip) * (1 / g) := by positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hEta : ∀ m, 1 ≤ m → m < K →
      heatEtaBar d σ N m M L δ δ ≤ heatRateA d N M L δ θ / Real.sqrt m := by
    intro m hm hmK
    refine heatEtaBar_closed_all hσ hσ1 hM0 hL.le hδ0 d N hN m hm ?_
    have h1 : Real.sqrt m ≤ Real.sqrt K := Real.sqrt_le_sqrt (by exact_mod_cast hmK.le)
    have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
    have h2 : 0 ≤ (2 * L + 2) * (heatKbar d σ + M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  subst hδ
  exact heat_kernel_l1_whp hσ d X h_indep hX hlaw N K hN (hconst σ le_rfl).1 hL hepsn0 hsmall
    (fun τ hτ => heat_normalisation_whp (lt_of_lt_of_le hσ hτ) d X h_indep hX hlaw N hg
      (hconst τ hτ).1 (hconst τ hτ).2 hLip0 hε) (heatRateA_nonneg hM0 hL.le (div_nonneg hepsn0 hNpos.le) hθ0 d N) hEta

/-- The constant `b'` of the supremum bound `heatDefSup ≤ b' mu_m/√m` valid at every time. -/
noncomputable def heatRateB' (d N : ℕ) (M L δ θ : ℝ) : ℝ :=
  3 * ((1 + 2 * δ) * (θ + 2 * (Real.sqrt (N * M * L) / N)
      * Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)))
    + 2 * δ * Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)))

/-- The numbers `W'_k = 2 · 2^d · max(2a, b') · √k`. -/
noncomputable def heatW' (d N : ℕ) (M L δ θ : ℝ) (k : ℕ) : ℝ :=
  2 * 2 ^ d * max (2 * heatRateA d N M L δ θ) (heatRateB' d N M L δ θ) * Real.sqrt k

theorem heatRateB'_nonneg {M L δ θ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (d N : ℕ) : 0 ≤ heatRateB' d N M L δ θ := by
  unfold heatRateB'
  have := cvConst_nonneg
  positivity

/-- **The supremum bound of the defect in closed form at every time:**
    `heatDefSup_m ≤ b' mu_m/√m` for `σ ≤ 1` and `(2L + 2)(kb + M) √m ≤ θ N`; no restriction
    `m σ ≤ 1`. -/
theorem heatDefSup_closed_all {σ M L δ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (d N : ℕ) (hN : 0 < N) (m : ℕ) (hm : 1 ≤ m)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N) :
    heatDefSup d σ N m M L δ ≤ heatRateB' d N M L δ θ * heatMu d σ m / Real.sqrt m := by
  have hc := cvConst_nonneg
  have hpi := Real.pi_pos
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have r1 : σ ≤ (m : ℝ) * σ := by nlinarith
  have hrc : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
      * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  have e : σ / ((m : ℝ) * σ) = 1 / m := by field_simp
  have hM1 : 1 ≤ heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) := by
    unfold heatM
    exact one_le_pow₀ (by linarith [Real.sqrt_nonneg (Real.pi / (2 * Real.pi ^ 2 * ((m : ℝ) * σ)))])
  have hM0' : 0 ≤ heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) := by linarith
  unfold heatRateB'
  refine heatDefSup_le hσ hM hL hδ d N m hN hm hkb0 hrc
    (by unfold heatKbar; exact heatKB_le hσ r1 hσ1 d) ?_ hθ
  rcases le_total ((m : ℝ) * σ) 1 with r2 | r2
  · have hcv := heatCV_le_mu hσ r1 r2 d
    rw [e] at hcv
    have h66 : Real.sqrt 6 ≤ 6 := by
      have := Real.sqrt_le_sqrt (show (6 : ℝ) ≤ 36 by norm_num)
      rwa [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have h61 : 1 ≤ Real.sqrt 6 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have hb : Real.sqrt 6 ≤ 12 * (1 + Real.sqrt (2 * Real.pi)) := by
      nlinarith [Real.sqrt_nonneg (2 * Real.pi)]
    have hp : Real.sqrt 6 ^ (d - 1) ≤ (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hb _
    have hconst : (d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1)
        ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by
      have h0 : 0 ≤ (d : ℝ) * cvConst := by positivity
      have h1 : (d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1)
          ≤ (d : ℝ) * cvConst * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left hp h0
      have h2 : 0 ≤ (d : ℝ) * cvConst * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by
        positivity
      nlinarith
    calc heatCV d σ ((m : ℝ) * σ)
        ≤ (d : ℝ) * cvConst * Real.sqrt 6 ^ (d - 1) * (1 / m)
          * heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) := hcv
      _ ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
            * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (1 / m)
          * heatM d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hconst (by positivity)) hM0'
      _ = _ := by ring
  · have hcv := heatCV_le_large hσ r1 r2 d
    rw [e] at hcv
    have hx : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
        * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) / m := by positivity
    calc heatCV d σ ((m : ℝ) * σ)
        ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
            * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (1 / m) := hcv
      _ = (d : ℝ) * cvConst * (2 * Real.sqrt 6)
            * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) / m * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM1 hx

/-- **The summation hypothesis of the sharp kernel theorem in closed form, at every time:** as
    `heat_hsum_closed`, without `K σ ≤ 1`, with `W'_k`. -/
theorem heat_hsum_closed_all {σ M L δ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hδ : 0 ≤ δ) (hθ0 : 0 ≤ θ) (d N K : ℕ) (hN : 0 < N)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N) (j : ℕ) (hj : j + 1 < K) :
    ∑ m ∈ Finset.range j, min (2 * heatMu d σ (j - m) * heatEtaBar d σ N (m + 1) M L δ δ)
        (heatDefSup d σ N (m + 1) M L δ) + heatDefSup d σ N (j + 1) M L δ
      ≤ heatW' d N M L δ θ (j + 1) * heatMu d σ (j + 2) := by
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hr3 : ∀ m : ℕ, m < K →
      (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N := by
    intro m hmK
    have h1 : Real.sqrt m ≤ Real.sqrt K := Real.sqrt_le_sqrt (by exact_mod_cast hmK.le)
    have h2 : 0 ≤ (2 * L + 2) * (heatKbar d σ + M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hbar : ∀ m, 1 ≤ m → m < K →
      heatEtaBar d σ N m M L δ δ ≤ heatRateA d N M L δ θ / Real.sqrt m :=
    fun m hm hmK => heatEtaBar_closed_all hσ hσ1 hM hL hδ d N hN m hm (hr3 m hmK)
  have hsup : ∀ m, 1 ≤ m → m < K →
      heatDefSup d σ N m M L δ ≤ heatRateB' d N M L δ θ * heatMu d σ m / Real.sqrt m :=
    fun m hm hmK => heatDefSup_closed_all hσ hσ1 hM hL hδ d N hN m hm (hr3 m hmK)
  have h := kernel_sum_bound (heatMu d σ) (fun m => heatEtaBar d σ N m M L δ δ)
    (fun m => heatDefSup d σ N m M L δ) (heatRateA_nonneg hM hL hδ hθ0 d N)
    (heatRateB'_nonneg hM hL hδ hθ0 d N) (c0 := 2 ^ d) (by positivity) K (heatMu_nonneg d σ)
    (fun l k hl hk hkl => heatMu_doubling hσ d hl hk hkl) hbar hsup j hj
  unfold heatW'
  have e : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; rfl
  rw [e]
  exact h

theorem heatW'_mono {M L δ θ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) (d N : ℕ)
    {k k' : ℕ} (hk : k ≤ k') :
    0 ≤ heatW' d N M L δ θ k ∧ heatW' d N M L δ θ k ≤ heatW' d N M L δ θ k' := by
  have ha := heatRateA_nonneg hM hL hδ hθ d N
  have hb := heatRateB'_nonneg hM hL hδ hθ d N
  have hmax : 0 ≤ max (2 * heatRateA d N M L δ θ) (heatRateB' d N M L δ θ) :=
    le_max_of_le_right hb
  unfold heatW'
  refine ⟨by positivity, ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hk)) (by positivity)

/-- **Theorem "kernel" for a random sample on the torus with the rate `√k`.** Independent uniform
    points on the flat torus, kernel time `σ ≤ 1`, EVERY number of steps `K` (no condition `K σ ≤ 1`), `δ = (ε + 2 N Lip/g)/N ≤ 1/8`. No
    hypothesis on events and no summation hypothesis. HYPOTHESES on numbers:
    `(2L + 2)(kb + M) √K ≤ θ N` and `4δ + (1 + 4δ) W_K ≤ 1` with `W_k = 2·2^d·max(2a, b')·√k` (`b' = heatRateB'`).
    CONCLUSION: except on an event of probability at most
    `(2 + 4K) · 2 g^d exp(-ε²/(4NM + 2Mε)) + 4 K N² e^{-L}`, for all `1 ≤ l ≤ K` and all entries
    `|N P^l(a,i) - p_{lσ}(x_a - x_i)| ≤ mu_l`, and for `j + 1 < K`
    `|N P^{j+2}(a,i) - p_{(j+2)σ}(x_a - x_i)| ≤ (4δ + (1 + 4δ) W_{j+1}) mu_{j+2}`. -/
theorem heat_kernel_rate_sample_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ K ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ δ N K (heatW' d N M L δ θ) (fun j => X j ω)}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
          + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
            + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))))
        + (K : ℝ) * (4 * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hsum := fun j hj => heat_hsum_closed_all hσ hσ1 hM0 hL.le hδ0 hθ0 d N K hN hθ j hj
  have hW : ∀ j, j + 1 < K → 0 ≤ heatW' d N M L δ θ (j + 1)
      ∧ 4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ (j + 1) ≤ 1 := by
    intro j hj
    obtain ⟨w0, w1⟩ := heatW'_mono hM0 hL.le hδ0 hθ0 d N (by omega : j + 1 ≤ K)
    refine ⟨w0, ?_⟩
    have := mul_le_mul_of_nonneg_left w1 (by linarith : (0 : ℝ) ≤ 1 + 4 * δ)
    linarith
  subst hδ
  exact heat_kernel_sharp_sample hσ d X h_indep hX hlaw N K hN hg hMdef hLipdef hL hε hsmall
    (heatW' d N M L ((ε + 2 * (N * Lip) * (1 / g)) / N) θ) hsum hW

/-- **Theorem "kernel" with the rate `√k` and failure probability `2/N³`.** As
    `heat_kernel_rate_sample`, with the level `L = log(4 K N⁵)` and a tolerance `ε` large enough
    that `log((2 + 4K) · 2 g^d · N³) · (4NM + 2Mε) ≤ ε²`: the conclusion fails with probability at
    most `2/N³`. -/
theorem heat_kernel_rate_prob_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    {g : ℕ} (hg : 0 < g)
    {M Lip L ε δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLdef : L = Real.log (4 * K * (N : ℝ) ^ 5)) (hε : 0 < ε)
    (hT : Real.log ((2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3) * (4 * (N * M) + 2 * M * ε)
      ≤ ε ^ 2)
    (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8)
    (hδ : δ = (ε + 2 * (N * Lip) * (1 / g)) / N)
    (hθ0 : 0 ≤ θ)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ K ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ δ N K (heatW' d N M L δ θ) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hgpos : (0 : ℝ) < g := by exact_mod_cast hg
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hN5 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ hN1
  have hLarg : (1 : ℝ) < 4 * K * (N : ℝ) ^ 5 := by nlinarith
  have hL : 0 < L := by rw [hLdef]; exact Real.log_pos hLarg
  have h := heat_kernel_rate_sample_all hσ hσ1 d X h_indep hX hlaw N K hN hg hMdef hLipdef hL hε hsmall
    hδ hθ0 hθ hWK
  refine h.trans ?_
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3 := ⟨_, rfl⟩
  have hApos : 0 < A := by rw [hA]; positivity
  have hD : 0 < 4 * (N * M) + 2 * M * ε := by positivity
  rw [← hA] at hT
  have he1 : Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ 1 / A := by
    have h1 : -ε ^ 2 / (4 * (N * M) + 2 * M * ε) ≤ -Real.log A := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD]; exact hT
    calc Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ Real.exp (-Real.log A) :=
          Real.exp_le_exp.mpr h1
      _ = 1 / A := by rw [Real.exp_neg, Real.exp_log hApos, one_div]
  have he2 : Real.exp (-L) = 1 / (4 * K * (N : ℝ) ^ 5) := by
    rw [hLdef, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hp : (2 + 4 * (K : ℝ)) * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
      ≤ 1 / (N : ℝ) ^ 3 := by
    calc (2 + 4 * (K : ℝ)) * ((g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
        ≤ (2 + 4 * (K : ℝ)) * ((g : ℝ) ^ d * (2 * (1 / A))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 1 / (N : ℝ) ^ 3 := by rw [hA]; field_simp
  have hq : (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) = 1 / (2 * (N : ℝ) ^ 3) := by
    rw [he2]; field_simp; ring
  have e3 : 2 / (N : ℝ) ^ 3 = 1 / (N : ℝ) ^ 3 + (1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3)) := by
    field_simp; ring
  rw [hq, e3]
  linarith

/-- The numbers `W_k` increase with the normalisation error `δ`. -/
theorem heatW'_mono_delta {M L δ δ' θ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ')
    (hθ : 0 ≤ θ) (d N k : ℕ) : heatW' d N M L δ θ k ≤ heatW' d N M L δ' θ k := by
  have hc := cvConst_nonneg
  have hδ'0 : 0 ≤ δ' := hδ0.trans hδ
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (N * M * L) / N := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have key : ∀ r : ℝ, 0 ≤ r →
      (1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r ≤ (1 + 2 * δ') * (θ + 2 * S * r) + 2 * δ' * r := by
    intro r hr
    have h1 : 0 ≤ θ + 2 * S * r := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hδ h1, mul_le_mul_of_nonneg_right hδ hr]
  have key0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ (1 + 2 * δ) * (θ + 2 * S * r) + 2 * δ * r := by
    intro r hr; positivity
  have hA : heatRateA d N M L δ θ ≤ heatRateA d N M L δ' θ := by
    unfold heatRateA
    rw [← hS]
    have hr : 0 ≤ Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
        * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)) := Real.sqrt_nonneg _
    have h1 := key _ hr
    have h0 := key0 _ hr
    have h2 : 3 * (1 + δ) ≤ 3 * (1 + δ') := by linarith
    exact mul_le_mul h2 h1 h0 (by linarith)
  have hB : heatRateB' d N M L δ θ ≤ heatRateB' d N M L δ' θ := by
    unfold heatRateB'
    rw [← hS]
    have hr : 0 ≤ Real.sqrt ((d : ℝ) * cvConst * (2 * Real.sqrt 6)
        * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1)) := Real.sqrt_nonneg _
    have h1 := key _ hr
    linarith
  unfold heatW'
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_left (max_le_max (by linarith) hB) (by positivity)

/-- **Theorem "kernel" with the rate `√k`, all parameters explicit.** Independent uniform points on
    the flat torus, kernel time `σ ≤ 1`, every `K`, grid parameter `g`. With
    `T = log((2 + 4K) · 2 g^d · N³)`, `L = log(4 K N⁵)`, `δ = 6 √(N M T)/N` and
    `θ = (2L + 2)(kb + M) √K / N`, under the three inequalities
    `2 N Lip/g ≤ 3 √(N M T)`, `6 √(N M T) ≤ N/8` and `4δ + (1 + 4δ) W_K ≤ 1`, the conclusion of
    the kernel theorem with `W_k = 2·2^d·max(2a, b)·√k` fails with probability at most `2/N³`. -/
theorem heat_kernel_rate_explicit_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) (hK : 0 < K)
    {g : ℕ} (hg : 0 < g)
    {M Lip L T δ θ : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLdef : L = Real.log (4 * K * (N : ℝ) ^ 5))
    (hTdef : T = Real.log ((2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3))
    (hδdef : δ = 6 * Real.sqrt (N * M * T) / N)
    (hθdef : θ = (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K / N)
    (hgc : 2 * (N * Lip) * (1 / g) ≤ 3 * Real.sqrt (N * M * T))
    (hsm : 6 * Real.sqrt (N * M * T) ≤ N / 8)
    (hWK : 4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ K ≤ 1) :
    μ.real {ω | ¬ heatKernelSharp d σ δ N K (heatW' d N M L δ θ) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hLarg : (1 : ℝ) < 4 * K * (N : ℝ) ^ 5 := by nlinarith [one_le_pow₀ hN1 (n := 5)]
  have hL : 0 < L := by rw [hLdef]; exact Real.log_pos hLarg
  have hTarg : (1 : ℝ) < (2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (g : ℝ) ^ d := one_le_pow₀ hg1
    have h2 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
    have h3 : (6 : ℝ) ≤ 2 + 4 * K := by linarith
    have h4 : (2 : ℝ) ≤ 2 * (g : ℝ) ^ d := by linarith
    have h5 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * (g : ℝ) ^ d) := by nlinarith
    nlinarith
  have hT : 0 < T := by rw [hTdef]; exact Real.log_pos hTarg
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * M * T) := ⟨_, rfl⟩
  have hsq : 0 < Real.sqrt (N * M * T) := Real.sqrt_pos.mpr (by positivity)
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε2 : ε ^ 2 = 9 * (N * M * T) := by
    rw [hεdef, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  have hεN : ε ≤ N / 16 := by rw [hεdef]; linarith
  have hTcond : Real.log ((2 + 4 * K) * (2 * (g : ℝ) ^ d) * (N : ℝ) ^ 3)
      * (4 * (N * M) + 2 * M * ε) ≤ ε ^ 2 := by
    rw [← hTdef, hε2]
    have h1 : 2 * M * ε * T ≤ 5 * (N * M * T) := by
      have : ε ≤ 5 * N / 2 := by linarith
      have hMT : 0 ≤ M * T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hMT]
    nlinarith
  have hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 8 := by rw [hεdef]; linarith
  obtain ⟨δ0, hδ0def⟩ : ∃ δ0 : ℝ, δ0 = (ε + 2 * (N * Lip) * (1 / g)) / N := ⟨_, rfl⟩
  have hδ00 : 0 ≤ δ0 := by rw [hδ0def]; positivity
  have hδ0le : δ0 ≤ δ := by
    rw [hδ0def, hδdef]
    apply div_le_div_of_nonneg_right _ hNpos.le
    rw [hεdef]; linarith
  have hδpos : 0 ≤ δ := hδ00.trans hδ0le
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N := by
    rw [hθdef, div_mul_cancel₀ _ hNpos.ne']
  have hWmono := fun k => heatW'_mono_delta hMpos.le hL.le hδ00 hδ0le hθ0 d N k
  have hWK0 : 4 * δ0 + (1 + 4 * δ0) * heatW' d N M L δ0 θ K ≤ 1 := by
    have w0 := (heatW'_mono hMpos.le hL.le hδ00 hθ0 d N (le_refl K)).1
    have h3 : (1 + 4 * δ0) * heatW' d N M L δ0 θ K ≤ (1 + 4 * δ) * heatW' d N M L δ θ K :=
      mul_le_mul (by linarith) (hWmono K) w0 (by linarith)
    linarith
  have h := heat_kernel_rate_prob_all hσ hσ1 d X h_indep hX hlaw N K hN hK hg hMdef hLipdef hLdef hε
    hTcond hsmall hδ0def hθ0 hθ hWK0
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  exact hω (heatKernelSharp_mono (fun j => X j ω) hgood hδ00 hδ0le
    (fun j => ⟨(heatW'_mono hMpos.le hL.le hδ00 hθ0 d N (le_refl j)).1, hWmono j⟩))

/-- The constant of the kernel theorem in the form `D_k ≤ C δ' √k mu_k`. -/
noncomputable def rateCfin' (d : ℕ) : ℝ :=
  48 * Real.sqrt ((d : ℝ) + 5)
    + 3 * 2 ^ d * max
        (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
          + 12 * Real.sqrt ((d : ℝ) + 5) * rateRA d)))
        (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
          + 12 * Real.sqrt ((d : ℝ) + 5) * rateRA d))

set_option maxHeartbeats 1600000 in
/-- **Theorem "kernel" in the form `D_k ≤ C δ' √k mu_k`.** Independent uniform points on the flat
    torus, `σ ≤ 1` the variance of the Gaussian kernel, every `K`, `1 ≤ K ≤ N`, `N ≥ 12`,
    `δ' = √(M log N / N)`. HYPOTHESES on numbers: `2 Lip ≤ 3 √(N M log N)` and the smallness
    condition `C δ' √K ≤ 1` with the explicit constant `C = rateCfin' d` depending only on `d`. Then,
    except on an event of probability at most `2/N³`, for all `2 ≤ k ≤ K` and all entries
    `|N P^k(a,i) - p_{kσ}(x_a - x_i)| ≤ C δ' √k mu_k`. -/
theorem heat_kernel_rate_paper_all {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * Real.sqrt (N * M * Real.log N))
    (hsmall : rateCfin' d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ rateCfin' d * δp * Real.sqrt k * heatMu d σ k}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hN : 0 < N := by omega
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hpi := Real.pi_pos
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hc := cvConst_nonneg
  -- logarithms
  obtain ⟨lg, hlg⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  rw [← hlg] at hδp hLipc
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log ((2 + 4 * K) * (2 * ((N : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (4 * K * (N : ℝ) ^ 5) := ⟨_, rfl⟩
  have hNd : (1 : ℝ) ≤ (N : ℝ) ^ d := one_le_pow₀ (by linarith)
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hargpos : 0 < (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3 := by positivity
  have hTle : T ≤ ((d : ℝ) + 5) * lg := by
    have h1 : (2 + 4 * (K : ℝ)) * 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (d + 5) := by
      calc (2 + 4 * (K : ℝ)) * (2 * (N : ℝ) ^ d) * (N : ℝ) ^ 3
          = ((2 + 4 * (K : ℝ)) * 2) * ((N : ℝ) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (d + 5) := by ring
    rw [hT, hlg]
    calc Real.log ((2 + 4 * (K : ℝ)) * (2 * ((N : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3)
        ≤ Real.log ((N : ℝ) ^ (d + 5)) := Real.log_le_log hargpos h2
      _ = ((d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hTge : lg ≤ T := by
    rw [hT, hlg]
    refine Real.log_le_log hNpos ?_
    have h6 : (6 : ℝ) ≤ 2 + 4 * K := by linarith
    have h2 : (2 : ℝ) ≤ 2 * (N : ℝ) ^ d := by linarith
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (N : ℝ)]
    have h12 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * (N : ℝ) ^ d) := by nlinarith
    have h13 := mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
    linarith
  have hLle : L ≤ 7 * lg := by
    have h1 : 4 * (K : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 7 := by
      calc 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ 7 := by ring
    rw [hL, hlg]
    calc Real.log (4 * (K : ℝ) * (N : ℝ) ^ 5) ≤ Real.log ((N : ℝ) ^ 7) :=
          Real.log_le_log (by positivity) h2
      _ = 7 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos
    have : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hTpos : 0 < T := by linarith
  -- δ' and the square roots
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * M * lg) := ⟨_, rfl⟩
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hQeq : Q = δp * N := by
    have hsq : (δp * N) ^ 2 = N * M * lg := by
      rw [mul_pow, hδp, Real.sq_sqrt (by positivity)]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt ((d : ℝ) + 5) := ⟨_, rfl⟩
  have hAa0 : 0 ≤ Aa := by rw [hAa]; exact Real.sqrt_nonneg _
  have hAa1 : 1 ≤ Aa := by
    rw [hAa, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hsqT : Real.sqrt (N * M * T) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ N * M)
    exact this.trans (le_of_eq (by ring))
  have hsqTge : Q ≤ Real.sqrt (N * M * T) := by
    rw [hQ]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTge (by positivity))
  -- the constant
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = rateCfin' d := ⟨_, rfl⟩
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d)) := ⟨_, rfl⟩
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hRB0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hmx0 : 0 ≤ mx := by rw [hmx]; exact le_max_of_le_right (by positivity)
  have hCfeq : Cf = 48 * Aa + 3 * 2 ^ d * mx := by rw [hCf, hmx, hAa]; unfold rateCfin'; rfl
  rw [← hCf] at hsmall
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hCf48 : 48 * Aa ≤ Cf := by
    rw [hCfeq]
    have : 0 ≤ 3 * 2 ^ d * mx := by positivity
    linarith
  have hCf0 : 0 ≤ Cf := by linarith
  have h48 : 48 * Aa * δp ≤ 1 := by
    have h1 : 48 * Aa * δp ≤ Cf * δp := mul_le_mul_of_nonneg_right hCf48 hδp0
    have h2 : Cf * δp ≤ Cf * δp * Real.sqrt K :=
      le_mul_of_one_le_right (mul_nonneg hCf0 hδp0) hsK1
    linarith
  have hδK : δp * Real.sqrt K ≤ 1 := by
    have h1 : 1 * (δp * Real.sqrt K) ≤ Cf * (δp * Real.sqrt K) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : Cf * (δp * Real.sqrt K) = Cf * δp * Real.sqrt K := by ring
    linarith
  -- the parameters of the explicit theorem
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 6 * Real.sqrt (N * M * T) / N := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K / N := ⟨_, rfl⟩
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδle : δ ≤ 6 * Aa * δp := by
    rw [hδ, div_le_iff₀ hNpos]
    calc 6 * Real.sqrt (N * M * T) ≤ 6 * (Aa * Q) := by linarith
      _ = 6 * Aa * δp * N := by rw [hQeq]; ring
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hsm : 6 * Real.sqrt (N * M * T) ≤ N / 8 := by
    have : 6 * Real.sqrt (N * M * T) = δ * N := by rw [hδ]; field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hδ8 hNpos.le
    linarith
  have hgc : 2 * (N * Lip) * (1 / ((N : ℕ) : ℝ)) ≤ 3 * Real.sqrt (N * M * T) := by
    have e : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ)) = 2 * Lip := by field_simp
    rw [e]
    calc 2 * Lip ≤ 3 * Q := by rw [hQ]; exact hLipc
      _ ≤ 3 * Real.sqrt (N * M * T) := by linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθle : θ ≤ 16 * (rateCK d + 1) * δp := by
    have hkb := heatKbar_le_M hσ d
    rw [← hMdef] at hkb
    have h1 : 2 * L + 2 ≤ 16 * lg := by linarith
    have h2 : heatKbar d σ + M ≤ (rateCK d + 1) * M := by linarith
    have h3 : (2 * L + 2) * (heatKbar d σ + M) ≤ 16 * lg * ((rateCK d + 1) * M) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have hδp2 : δp ^ 2 = M * lg / N := by rw [hδp, Real.sq_sqrt (by positivity)]
    rw [hθ, div_le_iff₀ hNpos]
    calc (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K
        ≤ 16 * lg * ((rateCK d + 1) * M) * Real.sqrt K :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = 16 * (rateCK d + 1) * (δp ^ 2 * N) * Real.sqrt K := by rw [hδp2]; field_simp
      _ = 16 * (rateCK d + 1) * δp * N * (δp * Real.sqrt K) := by ring
      _ ≤ 16 * (rateCK d + 1) * δp * N * 1 :=
          mul_le_mul_of_nonneg_left hδK (by positivity)
      _ = 16 * (rateCK d + 1) * δp * N := by ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (N * M * L) / N := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hSle : S ≤ Real.sqrt 7 * δp := by
    rw [hS, div_le_iff₀ hNpos]
    calc Real.sqrt (N * M * L) ≤ Real.sqrt (7 * (N * M * lg)) := by
          apply Real.sqrt_le_sqrt
          have := mul_le_mul_of_nonneg_left hLle (by positivity : (0 : ℝ) ≤ N * M)
          exact this.trans (le_of_eq (by ring))
      _ = Real.sqrt 7 * Q := by rw [hQ, Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 7 * δp * N := by rw [hQeq]; ring
  have habA := (rate_ab_bound hδ0 hδ8 hδle hθ0 hθle hS0 hSle hRA0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).1
  have habB := (rate_ab_bound hδ0 hδ8 hδle hθ0 hθle hS0 hSle hRB0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).2
  have hA : heatRateA d N M L δ θ
      ≤ 3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d) * δp := by
    unfold heatRateA; rw [← hS]; exact habA
  have hB : heatRateB' d N M L δ θ
      ≤ 3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d) * δp := by
    unfold heatRateB'; rw [← hS]; exact habB
  have hmaxle : max (2 * heatRateA d N M L δ θ) (heatRateB' d N M L δ θ) ≤ mx * δp := by
    rw [hmx, max_mul_of_nonneg _ _ hδp0]
    exact max_le_max (by linarith) hB
  have hWle : ∀ k : ℕ, heatW' d N M L δ θ k ≤ 2 * 2 ^ d * (mx * δp) * Real.sqrt k := by
    intro k
    unfold heatW'
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmaxle (by positivity)) (Real.sqrt_nonneg _)
  have hW0 : ∀ k : ℕ, 0 ≤ heatW' d N M L δ θ k := fun k =>
    (heatW'_mono hMpos.le hLpos.le hδ0 hθ0 d N (le_refl k)).1
  have hrel : ∀ k : ℕ, 1 ≤ k →
      4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ k ≤ Cf * δp * Real.sqrt k := by
    intro k hk
    have hk1 : 1 ≤ Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
    have h1 : (1 + 4 * δ) * heatW' d N M L δ θ k
        ≤ 3 / 2 * (2 * 2 ^ d * (mx * δp) * Real.sqrt k) :=
      mul_le_mul (by linarith) (hWle k) (hW0 k) (by norm_num)
    have h2 : 4 * δ ≤ 24 * Aa * δp * Real.sqrt k := by
      have : 24 * Aa * δp ≤ 24 * Aa * δp * Real.sqrt k :=
        le_mul_of_one_le_right (by positivity) hk1
      linarith
    rw [hCfeq]
    have h3 : 0 ≤ 24 * Aa * δp * Real.sqrt k := by positivity
    have e : (48 * Aa + 3 * 2 ^ d * mx) * δp * Real.sqrt k
        = 2 * (24 * Aa * δp * Real.sqrt k) + 3 / 2 * (2 * 2 ^ d * (mx * δp) * Real.sqrt k) := by
      ring
    rw [e]
    linarith
  have hWK : 4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ K ≤ 1 := (hrel K hK).trans hsmall
  have h := heat_kernel_rate_explicit_all hσ hσ1 d X h_indep hX hlaw N K hN hK hN hMdef hLipdef hL hT
    hδ hθ hgc hsm hWK
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk2 hkK a i
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h1 := hgood.2 j (by omega) a i
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (heatMu_nonneg d σ _)
  refine (hrel (j + 1) (by omega)).trans ?_
  rw [hCf]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by rw [← hCf]; exact mul_nonneg hCf0 hδp0)
  push_cast; linarith



/-- The heat kernel of the torus at the origin is at least one. -/
theorem heatTorus_zero_ge_one {c : ℝ} (hc : 0 < c) (d : ℕ) : 1 ≤ heatTorus d c 0 := by
  unfold heatTorus
  rw [cosSeries_zero]
  have h := (gauss_summable hc d).le_tsum 0 (fun n _ => (Real.exp_pos _).le)
  simpa using h

/-- The uniform bound `mu_k` against the value at the origin, at every time:
    `mu_k ≤ (1 + √(2π))^d p_{kσ}(0)` for all `k ≥ 1`. -/
theorem heatMu_le_m_all {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (hk : 1 ≤ k) :
    heatMu d σ k
      ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by
  have hpi := Real.pi_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hc : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := by positivity
  rcases le_total ((k : ℝ) * σ) 1 with h | h
  · exact heatMu_le_m hσ d k hk h
  · have h1 := heatTorus_zero_ge_one hc d
    have h2 : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ))) ≤ Real.sqrt (2 * Real.pi) := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ hc]
      have h3 : Real.pi ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
      have h4 : Real.pi ^ 2 ≤ Real.pi ^ 2 * ((k : ℝ) * σ) := le_mul_of_one_le_right (by positivity) h
      nlinarith [mul_pos hpi hpi, mul_pos (mul_pos hpi hpi) hpi]
    unfold heatMu heatM
    rw [if_neg (by omega)]
    calc (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * ((k : ℝ) * σ)))) ^ d
        ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d := pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = (1 + Real.sqrt (2 * Real.pi)) ^ d * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- The constant of the kernel theorem in the form `D_k ≤ C δ' √k mu_k`. -/
noncomputable def rateCfin3 (d : ℕ) : ℝ :=
  48 * Real.sqrt (3 * (d : ℝ) + 5)
    + 3 * 2 ^ d * max
        (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
          + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d)))
        (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
          + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d))

set_option maxHeartbeats 1600000 in
/-- **Theorem "kernel" in the form `D_k ≤ C δ' √k mu_k`.** Independent uniform points on the flat
    torus, `σ ≤ 1` the variance of the Gaussian kernel, every `K`, `1 ≤ K ≤ N`, `N ≥ 12`,
    `δ' = √(M log N / N)`. HYPOTHESES on numbers: `2 Lip ≤ 3 √(N M log N)` and the smallness
    condition `C δ' √K ≤ 1` with the explicit constant `C = rateCfin3 d` depending only on `d`. Then,
    except on an event of probability at most `2/N³`, for all `2 ≤ k ≤ K` and all entries
    `|N P^k(a,i) - p_{kσ}(x_a - x_i)| ≤ C δ' √k mu_k`. -/
theorem heat_kernel_rate_paper_g3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * M * Real.log N)))
    (hsmall : rateCfin3 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ rateCfin3 d * δp * Real.sqrt k * heatMu d σ k}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hN : 0 < N := by omega
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hpi := Real.pi_pos
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hc := cvConst_nonneg
  -- logarithms
  obtain ⟨lg, hlg⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  rw [← hlg] at hδp hLipc
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log ((2 + 4 * K) * (2 * ((N ^ 3 : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (4 * K * (N : ℝ) ^ 5) := ⟨_, rfl⟩
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hg3 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; rfl
  have hNd : (1 : ℝ) ≤ ((N : ℝ) ^ 3) ^ d := one_le_pow₀ hN3
  rw [hg3] at hT
  have hargpos : 0 < (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3 := by positivity
  have hTle : T ≤ (3 * (d : ℝ) + 5) * lg := by
    have h1 : (2 + 4 * (K : ℝ)) * 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (3 * d + 5) := by
      calc (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3
          = ((2 + 4 * (K : ℝ)) * 2) * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (3 * d + 5) := by rw [← pow_mul]; ring
    rw [hT, hlg]
    calc Real.log ((2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3)
        ≤ Real.log ((N : ℝ) ^ (3 * d + 5)) := Real.log_le_log hargpos h2
      _ = (3 * (d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hTge : lg ≤ T := by
    rw [hT, hlg]
    refine Real.log_le_log hNpos ?_
    have h6 : (6 : ℝ) ≤ 2 + 4 * K := by linarith
    have h2 : (2 : ℝ) ≤ 2 * ((N : ℝ) ^ 3) ^ d := by linarith
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (N : ℝ)]
    have h12 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * ((N : ℝ) ^ 3) ^ d) := by nlinarith
    have h13 := mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
    linarith
  have hLle : L ≤ 7 * lg := by
    have h1 : 4 * (K : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 7 := by
      calc 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ 7 := by ring
    rw [hL, hlg]
    calc Real.log (4 * (K : ℝ) * (N : ℝ) ^ 5) ≤ Real.log ((N : ℝ) ^ 7) :=
          Real.log_le_log (by positivity) h2
      _ = 7 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos
    have : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hTpos : 0 < T := by linarith
  -- δ' and the square roots
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * M * lg) := ⟨_, rfl⟩
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hQeq : Q = δp * N := by
    have hsq : (δp * N) ^ 2 = N * M * lg := by
      rw [mul_pow, hδp, Real.sq_sqrt (by positivity)]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt (3 * (d : ℝ) + 5) := ⟨_, rfl⟩
  have hAa0 : 0 ≤ Aa := by rw [hAa]; exact Real.sqrt_nonneg _
  have hAa1 : 1 ≤ Aa := by
    rw [hAa, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hsqT : Real.sqrt (N * M * T) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ N * M)
    exact this.trans (le_of_eq (by ring))
  have hsqTge : Q ≤ Real.sqrt (N * M * T) := by
    rw [hQ]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTge (by positivity))
  -- the constant
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = rateCfin3 d := ⟨_, rfl⟩
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d)) := ⟨_, rfl⟩
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hRB0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hmx0 : 0 ≤ mx := by rw [hmx]; exact le_max_of_le_right (by positivity)
  have hCfeq : Cf = 48 * Aa + 3 * 2 ^ d * mx := by rw [hCf, hmx, hAa]; unfold rateCfin3; rfl
  rw [← hCf] at hsmall
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hCf48 : 48 * Aa ≤ Cf := by
    rw [hCfeq]
    have : 0 ≤ 3 * 2 ^ d * mx := by positivity
    linarith
  have hCf0 : 0 ≤ Cf := by linarith
  have h48 : 48 * Aa * δp ≤ 1 := by
    have h1 : 48 * Aa * δp ≤ Cf * δp := mul_le_mul_of_nonneg_right hCf48 hδp0
    have h2 : Cf * δp ≤ Cf * δp * Real.sqrt K :=
      le_mul_of_one_le_right (mul_nonneg hCf0 hδp0) hsK1
    linarith
  have hδK : δp * Real.sqrt K ≤ 1 := by
    have h1 : 1 * (δp * Real.sqrt K) ≤ Cf * (δp * Real.sqrt K) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : Cf * (δp * Real.sqrt K) = Cf * δp * Real.sqrt K := by ring
    linarith
  -- the parameters of the explicit theorem
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 6 * Real.sqrt (N * M * T) / N := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K / N := ⟨_, rfl⟩
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδle : δ ≤ 6 * Aa * δp := by
    rw [hδ, div_le_iff₀ hNpos]
    calc 6 * Real.sqrt (N * M * T) ≤ 6 * (Aa * Q) := by linarith
      _ = 6 * Aa * δp * N := by rw [hQeq]; ring
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hsm : 6 * Real.sqrt (N * M * T) ≤ N / 8 := by
    have : 6 * Real.sqrt (N * M * T) = δ * N := by rw [hδ]; field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hδ8 hNpos.le
    linarith
  have hgc : 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤ 3 * Real.sqrt (N * M * T) := by
    rw [hg3]
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have e : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ) ^ 3) = 2 * Lip / (N : ℝ) ^ 2 := by field_simp
    rw [e, div_le_iff₀ hN2]
    calc 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Q) := by rw [hQ]; exact hLipc
      _ ≤ 3 * Real.sqrt (N * M * T) * (N : ℝ) ^ 2 := by nlinarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθle : θ ≤ 16 * (rateCK d + 1) * δp := by
    have hkb := heatKbar_le_M hσ d
    rw [← hMdef] at hkb
    have h1 : 2 * L + 2 ≤ 16 * lg := by linarith
    have h2 : heatKbar d σ + M ≤ (rateCK d + 1) * M := by linarith
    have h3 : (2 * L + 2) * (heatKbar d σ + M) ≤ 16 * lg * ((rateCK d + 1) * M) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have hδp2 : δp ^ 2 = M * lg / N := by rw [hδp, Real.sq_sqrt (by positivity)]
    rw [hθ, div_le_iff₀ hNpos]
    calc (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K
        ≤ 16 * lg * ((rateCK d + 1) * M) * Real.sqrt K :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = 16 * (rateCK d + 1) * (δp ^ 2 * N) * Real.sqrt K := by rw [hδp2]; field_simp
      _ = 16 * (rateCK d + 1) * δp * N * (δp * Real.sqrt K) := by ring
      _ ≤ 16 * (rateCK d + 1) * δp * N * 1 :=
          mul_le_mul_of_nonneg_left hδK (by positivity)
      _ = 16 * (rateCK d + 1) * δp * N := by ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (N * M * L) / N := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hSle : S ≤ Real.sqrt 7 * δp := by
    rw [hS, div_le_iff₀ hNpos]
    calc Real.sqrt (N * M * L) ≤ Real.sqrt (7 * (N * M * lg)) := by
          apply Real.sqrt_le_sqrt
          have := mul_le_mul_of_nonneg_left hLle (by positivity : (0 : ℝ) ≤ N * M)
          exact this.trans (le_of_eq (by ring))
      _ = Real.sqrt 7 * Q := by rw [hQ, Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 7 * δp * N := by rw [hQeq]; ring
  have habA := (rate_ab_bound hδ0 hδ8 hδle hθ0 hθle hS0 hSle hRA0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).1
  have habB := (rate_ab_bound hδ0 hδ8 hδle hθ0 hθle hS0 hSle hRB0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).2
  have hA : heatRateA d N M L δ θ
      ≤ 3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d) * δp := by
    unfold heatRateA; rw [← hS]; exact habA
  have hB : heatRateB' d N M L δ θ
      ≤ 3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d) * δp := by
    unfold heatRateB'; rw [← hS]; exact habB
  have hmaxle : max (2 * heatRateA d N M L δ θ) (heatRateB' d N M L δ θ) ≤ mx * δp := by
    rw [hmx, max_mul_of_nonneg _ _ hδp0]
    exact max_le_max (by linarith) hB
  have hWle : ∀ k : ℕ, heatW' d N M L δ θ k ≤ 2 * 2 ^ d * (mx * δp) * Real.sqrt k := by
    intro k
    unfold heatW'
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmaxle (by positivity)) (Real.sqrt_nonneg _)
  have hW0 : ∀ k : ℕ, 0 ≤ heatW' d N M L δ θ k := fun k =>
    (heatW'_mono hMpos.le hLpos.le hδ0 hθ0 d N (le_refl k)).1
  have hrel : ∀ k : ℕ, 1 ≤ k →
      4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ k ≤ Cf * δp * Real.sqrt k := by
    intro k hk
    have hk1 : 1 ≤ Real.sqrt k := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
    have h1 : (1 + 4 * δ) * heatW' d N M L δ θ k
        ≤ 3 / 2 * (2 * 2 ^ d * (mx * δp) * Real.sqrt k) :=
      mul_le_mul (by linarith) (hWle k) (hW0 k) (by norm_num)
    have h2 : 4 * δ ≤ 24 * Aa * δp * Real.sqrt k := by
      have : 24 * Aa * δp ≤ 24 * Aa * δp * Real.sqrt k :=
        le_mul_of_one_le_right (by positivity) hk1
      linarith
    rw [hCfeq]
    have h3 : 0 ≤ 24 * Aa * δp * Real.sqrt k := by positivity
    have e : (48 * Aa + 3 * 2 ^ d * mx) * δp * Real.sqrt k
        = 2 * (24 * Aa * δp * Real.sqrt k) + 3 / 2 * (2 * 2 ^ d * (mx * δp) * Real.sqrt k) := by
      ring
    rw [e]
    linarith
  have hWK : 4 * δ + (1 + 4 * δ) * heatW' d N M L δ θ K ≤ 1 := (hrel K hK).trans hsmall
  have h := heat_kernel_rate_explicit_all hσ hσ1 d X h_indep hX hlaw N K hN hK (pow_pos hN 3) hMdef hLipdef hL (by rw [hg3]; exact hT)
    hδ hθ hgc hsm hWK
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk2 hkK a i
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h1 := hgood.2 j (by omega) a i
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (heatMu_nonneg d σ _)
  refine (hrel (j + 1) (by omega)).trans ?_
  rw [hCf]
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by rw [← hCf]; exact mul_nonneg hCf0 hδp0)
  push_cast; linarith

/-- Lower bounds for the constant `rateCfin3`. -/
theorem rateCfin3_ge (d : ℕ) :
    48 * Real.sqrt (3 * (d : ℝ) + 5) ≤ rateCfin3 d ∧ (2 : ℝ) ^ d ≤ rateCfin3 d := by
  have hc := cvConst_nonneg
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d)) := ⟨_, rfl⟩
  have hmx1 : 1 ≤ mx := by
    rw [hmx]
    refine le_max_of_le_right ?_
    have h1 : 0 ≤ 2 * Real.sqrt 7 * rateRA d := by positivity
    have h2 : 0 ≤ 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d := by positivity
    nlinarith
  have e : rateCfin3 d = 48 * Real.sqrt (3 * (d : ℝ) + 5) + 3 * 2 ^ d * mx := by
    rw [hmx]; rfl
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  have p1 : (2 : ℝ) ^ d * 1 ≤ 2 ^ d * mx := mul_le_mul_of_nonneg_left hmx1 h2.le
  have hs0 : 0 ≤ Real.sqrt (3 * (d : ℝ) + 5) := Real.sqrt_nonneg _
  rw [e]
  constructor <;> nlinarith

/-- Arithmetic of the normalisation event: with `T = log(2 G n₃)` and `ε² = 9 n M T`,
    `0 < ε ≤ 5n/2`, the bound `G · 2 exp(-ε²/(4 n M + 2 M ε))` is at most `1/n₃`. -/
theorem g28_prob_arith {n M T G n3 ε : ℝ} (hn : 0 < n) (hM : 0 < M) (hT : 0 < T) (hG : 0 < G)
    (hn3 : 0 < n3) (hTdef : T = Real.log (2 * G * n3)) (hε : 0 < ε) (hεn : ε ≤ 5 * n / 2)
    (hε2 : ε ^ 2 = 9 * (n * M * T)) :
    G * (2 * Real.exp (-ε ^ 2 / (4 * (n * M) + 2 * M * ε))) ≤ 1 / n3 := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * G * n3 := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hB]; positivity
  rw [← hB] at hTdef
  have hD : 0 < 4 * (n * M) + 2 * M * ε := by positivity
  have hcond : T * (4 * (n * M) + 2 * M * ε) ≤ ε ^ 2 := by
    rw [hε2]
    have hMT : 0 ≤ M * T := by positivity
    have h1 : M * T * (2 * ε) ≤ M * T * (5 * n) := mul_le_mul_of_nonneg_left (by linarith) hMT
    have e1 : T * (4 * (n * M) + 2 * M * ε) = 4 * (n * M * T) + M * T * (2 * ε) := by ring
    have e2 : M * T * (5 * n) = 5 * (n * M * T) := by ring
    linarith
  have he1 : Real.exp (-ε ^ 2 / (4 * (n * M) + 2 * M * ε)) ≤ 1 / B := by
    have h1 : -ε ^ 2 / (4 * (n * M) + 2 * M * ε) ≤ -Real.log B := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD, ← hTdef]; exact hcond
    calc Real.exp (-ε ^ 2 / (4 * (n * M) + 2 * M * ε)) ≤ Real.exp (-Real.log B) :=
          Real.exp_le_exp.mpr h1
      _ = 1 / B := by rw [Real.exp_neg, Real.exp_log hBpos, one_div]
  calc G * (2 * Real.exp (-ε ^ 2 / (4 * (n * M) + 2 * M * ε)))
      ≤ G * (2 * (1 / B)) := by
        refine mul_le_mul_of_nonneg_left ?_ hG.le
        linarith
    _ = 1 / n3 := by rw [hB]; field_simp

/-- The constant `C₁` of the kernel theorem in the form of the appendix: it depends only on `d`. -/
noncomputable def kernelC1 (d : ℕ) : ℝ := rateCfin3 d * ((1 + Real.sqrt (2 * Real.pi)) ^ d) ^ 2

set_option maxHeartbeats 6400000 in
/-- **Theorem "kernel" in the form of the appendix.** Independent uniform points on the flat torus
    of dimension `d ≥ 1`, periodised Gaussian kernel of variance `σ = ξ² ≤ 1`, graph with
    self-loops, `N ≥ 2`, `M = p(0)`, `δ' = √(M log N/N)`, `m_k = p_{kσ}(0)`. With the constant
    `C₁ = kernelC1 d`, which depends only on `d`: if `C₁ δ' √K ≤ 1`, that is `K ≤ (C₁ δ')^{-2}`,
    then except on an event of probability at most `3/N³`, for ALL `1 ≤ k ≤ K` and all entries
    `|N P^k(a,i) - p_{kσ}(x_a - x_i)| ≤ C₁ δ' √k m_k`. No further hypothesis. -/
theorem kernel_theorem_G28 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ kernelC1 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ≤ 3 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  -- the logarithm
  obtain ⟨lg, hlgdef⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg : (1 / 2 : ℝ) ≤ lg := by
    rw [hlgdef, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith
  rw [← hlgdef] at hδp
  -- the two kernel bounds
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 + Real.sqrt (2 * Real.pi)) ^ d := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hA]; exact one_le_pow₀ (by linarith [Real.sqrt_nonneg (2 * Real.pi)])
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ)) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  have hyy : y * y = Real.pi / (2 * Real.pi ^ 2 * σ) := by
    rw [hy]; exact Real.mul_self_sqrt (by positivity)
  obtain ⟨ML, hML⟩ : ∃ ML : ℝ, ML = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d :=
    ⟨_, rfl⟩
  have hMLy : ML = (1 + y) ^ d := by rw [hML, hy]
  have hMp1 : 1 ≤ Mp := by rw [hMp]; exact heatTorus_zero_ge_one hcσ d
  have hMpML : Mp ≤ ML := by rw [hMp, hML]; exact heatTorus_le hcσ d 0
  have hML1 : 1 ≤ ML := hMp1.trans hMpML
  have hMLA : ML ≤ A * Mp := by
    have h := heatMu_le_m hσ d 1 le_rfl (by simpa using hσ1)
    unfold heatMu heatM at h
    rw [if_neg one_ne_zero] at h
    simp only [Nat.cast_one, one_mul] at h
    rw [hML, hA, hMp]; exact h
  have hyML : 1 + y ≤ ML := by
    rw [hMLy]
    calc 1 + y = (1 + y) ^ 1 := (pow_one _).symm
      _ ≤ (1 + y) ^ d := pow_le_pow_right₀ (by linarith) hd
  -- δ' of the file
  obtain ⟨δL, hδL⟩ : ∃ δL : ℝ, δL = Real.sqrt (ML * lg / N) := ⟨_, rfl⟩
  have hδL0 : 0 ≤ δL := by rw [hδL]; exact Real.sqrt_nonneg _
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hδLle : δL ≤ A * δp := by
    have h1 : ML * lg / N ≤ A ^ 2 * (Mp * lg / N) := by
      have h2 : ML ≤ A ^ 2 * Mp := by nlinarith
      have h3 : 0 ≤ lg / N := by positivity
      calc ML * lg / N = ML * (lg / N) := by ring
        _ ≤ A ^ 2 * Mp * (lg / N) := mul_le_mul_of_nonneg_right h2 h3
        _ = A ^ 2 * (Mp * lg / N) := by ring
    calc δL = Real.sqrt (ML * lg / N) := hδL
      _ ≤ Real.sqrt (A ^ 2 * (Mp * lg / N)) := Real.sqrt_le_sqrt h1
      _ = A * δp := by rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA0, hδp]
  have hδL2 : δL ^ 2 = ML * lg / N := by rw [hδL, Real.sq_sqrt (by positivity)]
  -- the constant
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = rateCfin3 d := ⟨_, rfl⟩
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt (3 * (d : ℝ) + 5) := ⟨_, rfl⟩
  have hAa1 : 1 ≤ Aa := by
    rw [hAa, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hCAa : 48 * Aa ≤ C := by rw [hC, hAa]; exact (rateCfin3_ge d).1
  have hC2d : (2 : ℝ) ^ d ≤ C := by rw [hC]; exact (rateCfin3_ge d).2
  have hC48 : 48 ≤ C := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC1 : kernelC1 d = C * A ^ 2 := by unfold kernelC1; rw [hC, hA]
  rw [hC1] at hrange ⊢
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hsmallL : C * δL * Real.sqrt K ≤ 1 := by
    have h1 : C * δL ≤ C * A ^ 2 * δp := by
      have h2 : A * δp ≤ A ^ 2 * δp := by nlinarith [mul_nonneg hA0 hδp0]
      have h3 := mul_le_mul_of_nonneg_left (hδLle.trans h2) hC0
      linarith
    exact (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)).trans hrange
  have hCδL : C * δL ≤ 1 := by
    have h1 : C * δL ≤ C * δL * Real.sqrt K := le_mul_of_one_le_right (by positivity) hsK1
    linarith
  -- N is large
  have hNbig : C ^ 2 * (ML * lg) ≤ N := by
    have h1 : (C * δL) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ C * δL := by positivity
      nlinarith
    rw [mul_pow, hδL2] at h1
    have h2 : C ^ 2 * (ML * lg / N) * N ≤ 1 * N := mul_le_mul_of_nonneg_right h1 hNpos.le
    have e : C ^ 2 * (ML * lg / N) * N = C ^ 2 * (ML * lg) := by field_simp
    linarith
  have hMLlg : (1 / 2 : ℝ) ≤ ML * lg := by nlinarith
  have hC2 : (2304 : ℝ) ≤ C ^ 2 := by nlinarith
  have hNr12 : (12 : ℝ) ≤ N := by nlinarith
  have hN12 : 12 ≤ N := by exact_mod_cast hNr12
  have hKN : K ≤ N := by
    have h1 : (C * δL * Real.sqrt K) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ C * δL * Real.sqrt K := by positivity
      nlinarith
    have hKsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by positivity)
    have h2 : C ^ 2 * (ML * lg / N) * K ≤ 1 := by
      have e : (C * δL * Real.sqrt K) ^ 2 = C ^ 2 * δL ^ 2 * Real.sqrt K ^ 2 := by ring
      rw [e, hδL2, hKsq] at h1; exact h1
    have h3 : C ^ 2 * (ML * lg) * K ≤ N := by
      have h4 := mul_le_mul_of_nonneg_right h2 hNpos.le
      have e : C ^ 2 * (ML * lg / N) * K * N = C ^ 2 * (ML * lg) * K := by field_simp
      linarith
    have h5 : (1 : ℝ) ≤ C ^ 2 * (ML * lg) := by nlinarith
    have h6 : (K : ℝ) ≤ N := by nlinarith
    exact_mod_cast h6
  -- the Lipschitz constant
  obtain ⟨Lip, hLip⟩ : ∃ Lip : ℝ, Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d := ⟨_, rfl⟩
  have hLip0 : 0 ≤ Lip := by rw [hLip]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * ML * lg) := ⟨_, rfl⟩
  have hQeq : Q = δL * N := by
    have hsq : (δL * N) ^ 2 = N * ML * lg := by
      rw [mul_pow, hδL2]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  have hLipML : Lip ≤ 4 * (2 : ℝ) ^ d * (ML * ML * ML) := by
    have e1 : 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ)) = 4 * (y * y) := by
      rw [hyy]; field_simp; ring
    have e2 : Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ)) = Real.sqrt 2 * y := by
      rw [hy, ← Real.sqrt_mul (by norm_num)]
      congr 1; ring
    have hs2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 4 by norm_num)
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have h1 : 1 + Real.sqrt 2 * y ≤ 2 * (1 + y) := by nlinarith [Real.sqrt_nonneg 2]
    have h2 : (1 + Real.sqrt 2 * y) ^ d ≤ 2 ^ d * ML := by
      calc (1 + Real.sqrt 2 * y) ^ d ≤ (2 * (1 + y)) ^ d :=
            pow_le_pow_left₀ (by positivity) h1 d
        _ = 2 ^ d * ML := by rw [mul_pow, hMLy]
    have h3 : y * y ≤ ML * ML := by nlinarith
    rw [hLip, e1, e2]
    calc 4 * (y * y) * (1 + Real.sqrt 2 * y) ^ d
        ≤ 4 * (ML * ML) * (2 ^ d * ML) :=
          mul_le_mul (by linarith) h2 (by positivity) (by positivity)
      _ = 4 * (2 : ℝ) ^ d * (ML * ML * ML) := by ring
  have hNa : 24 * C * ML ≤ N := by
    have h1 : 24 ≤ C * lg := by nlinarith
    have h2 : 0 ≤ C * ML := by positivity
    have h3 : C * ML * 24 ≤ C * ML * (C * lg) := mul_le_mul_of_nonneg_left h1 h2
    have e : C ^ 2 * (ML * lg) = C * ML * (C * lg) := by ring
    linarith
  have hNb : ML ≤ N := by
    have h1 : ML ≤ 24 * C * ML := by nlinarith
    linarith
  have hQge : 24 * ML ≤ Q := by
    have h1 : 24 * ML ≤ δL * N := by
      -- (24 ML)² ≤ δL² N² = ML lg N
      have h2 : (24 * ML) ^ 2 ≤ (δL * N) ^ 2 := by
        have e2 : (δL * N) ^ 2 = ML * lg * N := by
          rw [mul_pow, hδL2]; field_simp
        rw [e2]
        have h3 : (1152 : ℝ) * ML ≤ N := by
          have h30 : 2304 * (ML * lg) ≤ C ^ 2 * (ML * lg) :=
            mul_le_mul_of_nonneg_right hC2 (by positivity)
          have h31 : ML * (1 / 2) ≤ ML * lg := mul_le_mul_of_nonneg_left hlg (by linarith)
          linarith
        have h4 : ML / 2 ≤ ML * lg := by
          have := mul_le_mul_of_nonneg_left hlg (by linarith : (0 : ℝ) ≤ ML)
          linarith
        have h5 : ML / 2 * (1152 * ML) ≤ ML * lg * N :=
          mul_le_mul h4 h3 (by positivity) (by positivity)
        nlinarith
      exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
    rw [hQeq]; exact h1
  have hLipc : 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * ML * Real.log N)) := by
    rw [← hlgdef, ← hQ]
    have h1 : 24 * C * ML * ML ≤ (N : ℝ) * N := mul_le_mul hNa hNb (by positivity) hNpos.le
    have h2 : 24 * C * ML * ML * (24 * ML) ≤ (N : ℝ) * N * Q :=
      mul_le_mul h1 hQge (by positivity) (by positivity)
    have h3 : 2 * Lip ≤ 8 * C * (ML * ML * ML) := by
      have h4 : 4 * (2 : ℝ) ^ d * (ML * ML * ML) ≤ 4 * C * (ML * ML * ML) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hP : 0 ≤ C * (ML * ML * ML) := by positivity
    nlinarith
  -- the event for k ≥ 2
  have hδLdef : δL = Real.sqrt (ML * Real.log N / N) := by rw [hδL, hlgdef]
  have hEA := heat_kernel_rate_paper_g3 hσ hσ1 d X h_indep hX hlaw N K hN12 hK hKN hML hLip
    hδLdef hLipc (by rw [← hC]; exact hsmallL)
  -- the normalisation event for k = 1
  obtain ⟨TB, hTB⟩ : ∃ TB : ℝ, TB = Real.log (2 * ((N ^ 3 : ℕ) : ℝ) ^ d * (N : ℝ) ^ 3) :=
    ⟨_, rfl⟩
  have hg3 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; rfl
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hNd : (1 : ℝ) ≤ ((N : ℝ) ^ 3) ^ d := one_le_pow₀ hN3
  have hBarg : (2 : ℝ) ≤ 2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3 := by nlinarith
  have hTB0 : 0 < TB := by
    rw [hTB, hg3]; exact Real.log_pos (by linarith)
  have hTBle : TB ≤ (3 * (d : ℝ) + 5) * lg := by
    have h2 : 2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (3 * d + 5) := by
      have h1 : (2 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      calc 2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3
          = 2 * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (3 * d + 5) := by rw [← pow_mul]; ring
    rw [hTB, hg3, hlgdef]
    calc Real.log (2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3)
        ≤ Real.log ((N : ℝ) ^ (3 * d + 5)) := Real.log_le_log (by linarith) h2
      _ = (3 * (d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * ML * TB) := ⟨_, rfl⟩
  have hsqTB : Real.sqrt (N * ML * TB) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTBle (by positivity : (0 : ℝ) ≤ N * ML)
    exact this.trans (le_of_eq (by ring))
  have hεpos : 0 < ε := by
    rw [hε]; have : 0 < Real.sqrt (N * ML * TB) := Real.sqrt_pos.mpr (by positivity)
    linarith
  have hεle : ε ≤ 3 * Aa * δL * N := by
    rw [hε]
    calc 3 * Real.sqrt (N * ML * TB) ≤ 3 * (Aa * Q) := by linarith
      _ = 3 * Aa * δL * N := by rw [hQeq]; ring
  have hAaδ : 48 * Aa * δL ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hCAa hδL0
    linarith
  have hεN : ε ≤ N / 16 := by
    have h1 : 3 * Aa * δL * N ≤ 1 / 16 * N := mul_le_mul_of_nonneg_right (by linarith) hNpos.le
    linarith
  obtain ⟨thr, hthr⟩ : ∃ thr : ℝ, thr = ε + 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hthrle : thr ≤ 6 * Aa * δL * N := by
    have hN2' : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have e : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ) ^ 3) = 2 * Lip / (N : ℝ) ^ 2 := by field_simp
    have h1 : 2 * Lip / (N : ℝ) ^ 2 ≤ 3 * Q := by
      rw [div_le_iff₀ hN2']
      have := hLipc
      rw [← hlgdef, ← hQ] at this
      linarith
    rw [hthr, hg3, e]
    have h2 : 3 * Q = 3 * δL * N := by rw [hQeq]; ring
    have h3 : 3 * δL * N ≤ 3 * Aa * δL * N := by
      have : 0 ≤ δL * N := by positivity
      nlinarith
    linarith
  have hthr0 : 0 ≤ thr := by rw [hthr]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = thr / N := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδle : δ ≤ 6 * Aa * δL := by
    rw [hδ, div_le_iff₀ hNpos]; exact hthrle
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hconstM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ ML := fun u => by
    rw [hML]; exact heatTorus_le hcσ d u
  have hconstL : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u - heatTorus d (2 * Real.pi ^ 2 * σ) u'|
      ≤ Lip * dist u u' := fun u u' => by
    rw [hLip]; exact heatTorus_lipschitz hcσ d u u'
  have hEB0 := heat_normalisation_whp hσ d X h_indep hX hlaw N (pow_pos hN 3) hconstM hconstL
    hLip0 hεpos
  rw [← hthr] at hEB0
  have hEB : μ.real {ω | ∃ x : FlatTorus d,
      thr < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|}
      ≤ 1 / (N : ℝ) ^ 3 := by
    refine hEB0.trans ?_
    rw [hg3]
    have hε2 : ε ^ 2 = 9 * (N * ML * TB) := by
      rw [hε, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    exact g28_prob_arith hNpos (by linarith) hTB0 (by positivity : (0 : ℝ) < ((N : ℝ) ^ 3) ^ d)
      (by positivity : (0 : ℝ) < (N : ℝ) ^ 3) (by rw [hTB, hg3]) hεpos (by linarith) hε2
  -- the union
  obtain ⟨SA, hSA⟩ : ∃ SA : Set Ω, SA = {ω | ¬ ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ rateCfin3 d * δL * Real.sqrt k * heatMu d σ k} := ⟨_, rfl⟩
  obtain ⟨SB, hSB⟩ : ∃ SB : Set Ω, SB = {ω | ∃ x : FlatTorus d,
      thr < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} :=
    ⟨_, rfl⟩
  have hPA : μ.real SA ≤ 2 / (N : ℝ) ^ 3 := by rw [hSA]; exact hEA
  have hPB : μ.real SB ≤ 1 / (N : ℝ) ^ 3 := by rw [hSB]; exact hEB
  have hsub : {ω | ¬ ∀ k, 1 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ C * A ^ 2 * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ⊆ SA ∪ SB := by
    intro ω hbad
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hnA, hnB⟩ := hcon
    apply hbad
    have hgoodA : ∀ k, 2 ≤ k → k ≤ K → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
            - heatP d σ k (X a ω - X i ω)|
          ≤ rateCfin3 d * δL * Real.sqrt k * heatMu d σ k := by
      by_contra h
      rw [hSA] at hnA
      exact hnA h
    have hgoodB : ∀ x : FlatTorus d,
        |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N| ≤ thr := by
      intro x
      by_contra h
      rw [hSB] at hnB
      exact hnB ⟨x, not_le.mp h⟩
    intro k hk1 hkK a i
    rcases Nat.lt_or_ge k 2 with hk | hk
    · -- k = 1
      have hk1' : k = 1 := by omega
      subst hk1'
      haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      have hρ : ∀ j : Fin N, |heatRho d σ N (fun j => X j ω) j - 1| ≤ δ := by
        intro j
        have h := hgoodB (X j ω)
        have e : heatRho d σ N (fun j => X j ω) j - 1
            = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
          unfold heatRho; field_simp
        rw [e, abs_div, abs_of_pos hNpos, hδ]
        exact div_le_div_of_nonneg_right h hNpos.le
      have hK0 : ∀ a j : Fin N, 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω) :=
        fun a j => heatTorus_nonneg hcσ d _
      have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp
      have h1 := walk_last_step
        (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
        (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) hK0
        (fun a => by
          rw [hcard]
          unfold heatRho
          rw [mul_div_cancel₀ _ hNpos.ne']
          exact Fin.sum_univ_eq_sum_range
            (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X l ω)) N)
        hδ0 hδ8 hρ a i
      rw [hcard] at h1
      rw [pow_one, heatP_one, Nat.cast_one, Real.sqrt_one, one_mul, mul_one, ← hMp]
      refine h1.trans ?_
      have hKle : heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X i ω) ≤ ML := hconstM _
      have hKnn := hK0 a i
      -- 4 δ K ≤ 4 (6 Aa δL) ML ≤ (C/2) (A δp) (A Mp)
      have h2 : 4 * δ * heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X i ω)
          ≤ 4 * (6 * Aa * δL) * ML :=
        mul_le_mul (by linarith) hKle hKnn (by positivity)
      have h3 : 4 * (6 * Aa * δL) * ML ≤ C * (A * δp) * (A * Mp) := by
        have h4 : 24 * Aa * δL ≤ C * (A * δp) := by
          have h5 : 24 * Aa * δL ≤ C * δL := by
            have := mul_le_mul_of_nonneg_right hCAa hδL0
            nlinarith
          have h6 : C * δL ≤ C * (A * δp) := mul_le_mul_of_nonneg_left hδLle hC0
          linarith
        have h7 : 24 * Aa * δL * ML ≤ C * (A * δp) * (A * Mp) :=
          mul_le_mul h4 hMLA (by linarith) (by positivity)
        linarith
      calc 4 * δ * heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X i ω)
          ≤ C * (A * δp) * (A * Mp) := h2.trans h3
        _ = C * A ^ 2 * δp * Mp := by ring
    · -- k ≥ 2
      refine (hgoodA k hk hkK a i).trans ?_
      have hmu := heatMu_le_m_all hσ d k (by omega)
      rw [← hA] at hmu
      have hmu0 := heatMu_nonneg d σ k
      rw [← hC]
      calc C * δL * Real.sqrt k * heatMu d σ k
          ≤ C * (A * δp) * Real.sqrt k
              * (A * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0) :=
            mul_le_mul
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hδLle hC0)
                (Real.sqrt_nonneg _))
              hmu hmu0 (by positivity)
        _ = C * A ^ 2 * δp * Real.sqrt k
              * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by ring
  calc μ.real _ ≤ μ.real (SA ∪ SB) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real SA + μ.real SB := measureReal_union_le _ _
    _ ≤ 2 / (N : ℝ) ^ 3 + 1 / (N : ℝ) ^ 3 := add_le_add hPA hPB
    _ = 3 / (N : ℝ) ^ 3 := by ring

/-- **The trace statement of Theorem "kernel":** if all diagonal entries satisfy
    `|N (P^k)_{aa} - m| ≤ E`, then `|Tr P^k - m| ≤ E`. -/
theorem trace_from_diagonal {N : ℕ} (hN : 0 < N) (B : Matrix (Fin N) (Fin N) ℝ) {m E : ℝ}
    (h : ∀ a : Fin N, |(N : ℝ) * B a a - m| ≤ E) : |B.trace - m| ≤ E := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : B.trace - m = (∑ a : Fin N, ((N : ℝ) * B a a - m)) / N := by
    rw [Matrix.trace, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Matrix.diag_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  rw [e, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
  calc |∑ a : Fin N, ((N : ℝ) * B a a - m)| ≤ ∑ a : Fin N, |(N : ℝ) * B a a - m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin N, E := Finset.sum_le_sum fun a _ => h a
    _ = E * N := by simp [mul_comm]

end KernelL1

end Probability

end CTG.Reals
