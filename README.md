# CorrelationsGeometry

Lean 4 / Mathlib proofs of selected results from M. Neuberger, *From Correlations to Geometry:
A Conditional Spectral Reconstruction* (November 2026).

This covers the algebraic and finite-dimensional results of the paper and the analytic half of
Proposition 4.2. It does **not** cover the reconstruction theorems on manifolds, the field-theory
results or the physical interpretation; Mathlib does not yet contain the mathematics those need.

`HANDOVER.md` gives the current state and next steps for anyone picking the work up.
`PLAN.md` describes the planned work on the quantum half of Proposition 4.2.
`vendor/openai-math/` holds 26 files copied from github.com/openai/math for that work; nothing in
`CorrelationsGeometry/` imports them yet.

## Status

`lake build` completes with no errors and no `sorry`. `CorrelationsGeometry/Audit.lean` prints the
axioms behind every main theorem; all depend only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

Toolchain: `leanprover/lean4:v4.36.0-rc2`, Mathlib `v4.36.0-rc2`.

## What is proven

| Paper | Lean | File |
|---|---|---|
| Thm 3.11, Poisson representation, non-negativity of `Tr P^k`, both bounds | `theorem_3_11` | `PoissonTrace.lean` |
| Thm 3.11, series for an arbitrary real matrix | `poisson_trace` | `PoissonTrace.lean` |
| Prop. 4.2, `f' = ln((ν+½)/(ν−½))`, `f'' = −1/(ν²−¼)` | `hasDerivAt_entropyFn`, `hasDerivAt_entropyFnDeriv` | `TwoModeExpansion.lean` |
| Prop. 4.2, expansion (4.2) of `2f(ν) − f(ν₊) − f(ν₋)` with fourth-order remainder | `two_mode_expansion`, `two_mode_expansion_isBigO` | `TwoModeExpansion.lean` |
| Prop. 4.2, symmetry under `(x, p) ↦ (−x, −p)` | `twoModeMI_neg` | `TwoModeExpansion.lean` |
| Prop. 9.4, infimum of affine functions is concave | `concaveOn_iInf_affine` | `Concavity.lean` |
| Prop. 9.4, second-order change is non-positive | `second_order_nonpos` | `Concavity.lean` |
| Prop. 9.4, no cancellation between species | `sum_second_order_eq_zero_iff`, `sum_response_eq_zero_iff` | `Concavity.lean` |
| Prop. 9.5, `λ ≤ 1`, equality iff `ℓ = 0` | `lam_le_one`, `lam_eq_one_iff` | `Concavity.lean` |
| Eq. (9.10), `λ = (3 − D²)/2`, `λ = −3` for `D = 3` | `lam_scalar`, `lam_scalar_three` | `Concavity.lean` |
| Prop. 9.13, `κ = d − 6I` in every dimension | `kappa_succ` | `FormFields.lean` |
| Prop. 9.18 (i), (ii), (iii) | `Content.relation_i`, `Masses.relation_ii`, `Masses.relation_iii` | `FieldContent.lean` |
| Cor. 9.14 | `Content.covariant_iff`, `Content.a_of_covariant`, `Content.no_induced_action` | `FieldContent.lean` |
| Eq. (9.19), range of `λ` for scalar and Dirac fields | `Content.lam_scalar_dirac`, `Content.lam_scalar_dirac_mem` | `FieldContent.lean` |
| Cor. 9.17 (i), (ii), (iii) | `Masses.lf_pos_of_no_vector`, `Masses.exists_Z_iff`, `Masses.bfProfile_sub_af` | `FieldContent.lean` |
| Cor. 9.19 | `Content.a_eq_zero_of_covariant_of_str1`, `Masses.a_eq_zero_of_covariant`, `Masses.ratio_of_covariant`, `Masses.a_eq_zero_of_covariant_profile` | `FieldContent.lean` |
| Prop. 9.15, table entries from the cutoff integrals | `MassTerms.scalar_leading`, `scalar_finite`, `scalar_log`, `dirac_all`, `vector_all` | `FieldContent.lean` |

## What is taken as input

Lean checks that each theorem follows from its stated hypotheses and definitions. It does not check
that those match the physics. The inputs are:

* **Theorem 3.11**: none. The statement is the paper's, for any symmetric matrix with non-negative
  entries and positive row sums.
* **Proposition 4.2**: that the mutual information of the two-mode Gaussian state equals
  `2f(ν) − f(ν₊) − f(ν₋)` with `ν± = √((x0 ± x)(p0 ± p))`. This formula is the definition
  `twoModeMI`; the expansion is proven for it. The constants `C`, `δ` in `two_mode_expansion`
  depend on `(x0, p0)`; uniformity on compact sets is not proven.
* **Propositions 9.4 and 9.5**: that the ground-state energy is an infimum of expectation values that
  are affine in the shift, and that the second-order response has the form (9.9).
* **Section 9.6**: the entries of Table 2 and of the table in Proposition 9.15 (as definitions), and,
  for `MassTerms`, the expansions of the cutoff integrals and the per-field formulas (9.6)/(9.20),
  (9.18), (9.23) after angular averaging.
* **Proposition 9.13**: the Hodge heat coefficient and the recursion between exact and coexact forms.

## Building

```
lake exe cache get
lake build
```

Lake needs a reasonably recent Git to fetch Mathlib (Git 2.21 is too old).

The copied openai/math files are a separate library and are not built by `lake build`:

```
lake build OAI
lake env lean vendor/openai-math/Audit.lean
```

They are under the Apache License 2.0; see `vendor/openai-math/README.md` for their origin and the
two files that were changed.
