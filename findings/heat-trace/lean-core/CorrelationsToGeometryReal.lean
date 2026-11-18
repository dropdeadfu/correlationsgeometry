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
import Mathlib.Probability.Moments.SubGaussian
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

end Probability

end CTG.Reals
