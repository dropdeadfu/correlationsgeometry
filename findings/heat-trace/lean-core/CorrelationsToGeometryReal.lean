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
    (hbar : ∀ m i, 1 ≤ m → ∑ b, |(P *ᵥ (fun b' => p m b' i)) b - p (m + 1) b i|
        ≤ (Fintype.card n : ℝ) * etabar m)
    (hsup : ∀ m i b, 1 ≤ m → |(P *ᵥ (fun b' => p m b' i)) b - p (m + 1) b i| ≤ etasup m)
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
      (fun m _ => by simpa using hbar (m + 1) i (by omega)) hw
      (fun b => by simpa using hsup (j + 1) i b (by omega)) a
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

end Powers

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

end Probability

end CTG.Reals
