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

end CTG.Reals
