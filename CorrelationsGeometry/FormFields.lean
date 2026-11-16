import Mathlib

/-!
# Form fields: the heat coefficient of coexact forms (Proposition 9.13 of the paper)

Paper: M. Neuberger, *From Correlations to Geometry* (November 2026).

On a slice of dimension `D` the Hodge Laplacian on `p`-forms has first heat coefficient
`[C(D,p)/6 − C(D−2,p−1)] R`. A `p`-form is a coexact `p`-form plus an exact one, and the exact
`p`-forms are the coexact `(p−1)`-forms. Writing `κ_p R / 6` for the heat coefficient of the coexact
`p`-forms, this gives the recursion

  `κ_0 = 1`,  `κ_p = C(D,p) − 6 C(D−2,p−1) − κ_{p−1}`.

Proposition 9.13 states `κ_p = d − 6 I` with `d = C(D−1,p)` and `I = C(D−3,p−1)`, and reports that
this "was verified for `D ≤ 12`". The theorem below proves it for every `D ≥ 3` and every `p`.

Input (not proven here): the Hodge heat coefficient and the recursion, as stated in the paper.
-/

namespace CorrelationsGeometry

/-- `kappa n p` is `κ_p` in dimension `D = n + 3`, defined by the recursion of Proposition 9.13. -/
def kappa (n : ℕ) : ℕ → ℤ
  | 0 => 1
  | p + 1 => (Nat.choose (n + 3) (p + 1) : ℤ) - 6 * (Nat.choose (n + 1) p : ℤ) - kappa n p

/-- `κ_0 = 1 = C(D−1, 0)`: the scalar field. -/
@[simp] theorem kappa_zero (n : ℕ) : kappa n 0 = 1 := rfl

/-- **Proposition 9.13, heat coefficient, all dimensions.** For `D = n + 3` and `p ≥ 1`,
`κ_p = C(D−1, p) − 6 C(D−3, p−1)`. -/
theorem kappa_succ (n p : ℕ) :
    kappa n (p + 1) = (Nat.choose (n + 2) (p + 1) : ℤ) - 6 * (Nat.choose n p : ℤ) := by
  induction p with
  | zero =>
    simp [kappa]
    ring
  | succ p ih =>
    rw [kappa, ih]
    have h1 : (Nat.choose (n + 3) (p + 2) : ℤ)
        = (Nat.choose (n + 2) (p + 1) : ℤ) + (Nat.choose (n + 2) (p + 2) : ℤ) := by
      exact_mod_cast Nat.choose_succ_succ (n + 2) (p + 1)
    have h2 : (Nat.choose (n + 1) (p + 1) : ℤ)
        = (Nat.choose n p : ℤ) + (Nat.choose n (p + 1) : ℤ) := by
      exact_mod_cast Nat.choose_succ_succ n p
    rw [h1, h2]
    ring

/-- The Maxwell field in three dimensions (`D = 3`, `p = 1`) has `κ = −4`, as in Table 2
(`b_R = 10 κ = −40`). -/
example : kappa 0 1 = -4 := by
  rw [kappa_succ]; norm_num

end CorrelationsGeometry
