# Heat trace of the sampled graph: findings of 17 November 2026

Working material on Appendix G of M. Neuberger, *From Correlations to Geometry* (the version with
Appendix G, about 100 pages; `main` of this repository refers to the 74-page version without it).
Produced on 17 November 2026 by two Claude sessions working together over a mesh: one on the author's
side (paper, numerics, core-library Lean file) and a second session on the repository owner's side ("the second session" below).

This branch does not touch `main` or the Mathlib project in `CorrelationsGeometry/`.

## Status of each item

No statement here has been read by a person. "Proven" means: a complete proof is written out and,
unless the table says otherwise, has been read formula by formula by a second AI session.

| Item | Statement | Status |
|---|---|---|
| Proposition G.22 (`prop:bias`) | On the flat torus, for fixed kernel scale and fixed `k`: `E Tr P^k = mu_k + beta_k/N + O(N^(-3/2))` with an explicit `beta_k`, with and without self-loops | proven; proof by the second session, read by the author-side session; numerics |
| Proposition G.24 (`prop:variance`) | `Var Tr P^k = v_k/N^2 + O(N^(-5/2))`, `v_k = 1/2 int H_k^2`; with self-loops `beta_k = H_k(0)/2` | proven, same provenance; numerics |
| Remarks G.23 (v), G.25 (v) | Relative bias a bounded multiple of `M/N` and relative fluctuation of order `sqrt(M)/N`, uniformly in `k`; rate `xi^2/t` for `N xi^(d+2) -> infinity` | conjecture; numerics |
| Self-loops | Most of the `1/N` bias of the sampled trace is due to the self-loops (about `(d/2) M/N` relative); removing the diagonal of the kernel reduces the deviation of the subtracted trace from the population value by about a factor ten in the runs below | numerics for the size; the difference of the two coefficients is part of G.22 |
| Lemmas G.26, G.27 (`lem:pgauss`, `lem:consistency`) | Consistency of the normalised walk: the one-step defect `h_m` is at most `C delta' m^(-1/2) p_6m`, `delta' = sqrt(M log N/N)`, with probability at least `1 - 7 N^(-3)` | proven; proof by the second session, read line by line by the author-side session |
| Theorem G.28 (`thm:kernel`) | `max |N (P^k)_ai - p_k(x_a - x_i)| <= C_1 delta' sqrt(k) m_k` for all `k <= (C_1 delta')^(-2)`: stability plus consistency in the supremum norm, no walk with exact normalisation, no eigenvalues | proven given G.27; written by the author-side session; the written-out proof has been read by the second session, which found no error and four points of presentation, now included |
| Corollary G.29 (`cor:kernel-trace`) | Almost surely: the trace converges for `N xi^(d+2)/log N -> infinity`; the rate `xi^2/t` with the sharp coefficient holds for `N xi^(d+6)/log N -> infinity`, in every dimension (Theorem G.14 has `2d+6`, in probability, `d >= 2`) | proven given G.28; read by the second session |
| Corollary G.30 (`cor:kernel-corrected`) | The corrected estimator `T - (sigma t/2) T''` of the sampled graph deviates from the heat trace by `O(tau^-2) + O(tau delta' sqrt(tau + log N))` | proven given G.28; written by the author-side session; the second session checked the statement and a summary of the proof (not the text in the paper) and found no error. The error is smaller than the gain of the correction only for `N xi^(d+10)/log N -> infinity` at a fixed time |
| Sharp rate for `N xi^(d+2) -> infinity` | would need the averaging over the diagonal (bias `M/N` instead of the entrywise error `delta'`) | open; conjecture |
| Theorem G.14, proof | Six small gaps closed (self-term in Step 1, tail `j > J`, bounds on Theta, uniform form of the expansion, two presentational points); statement unchanged | done in the paper; not part of this folder |

## Files

- `appendix_G22_G31.pdf` — the pages of the paper with G.22 to G.31 (the first and the last page
  also show the end of the preceding and the beginning of the following item).
- `bias_variance_excerpt.tex` — TeX of Propositions G.22, G.24 and Remarks G.23, G.25.
- `kernel_bound_excerpt.tex` — TeX of Lemmas G.26, G.27, Theorem G.28, Corollaries G.29, G.30, Remark G.31.
  Both are fragments that use the macros and labels of the paper; they do not compile on their own.
- `scripts/kernel_sup_norm.py` — for one sample, the entrywise error of `P^k` against the heat kernel and
  the size of the consistency defect relative to the bound of Lemma G.27.
- `scripts/normalised_walk_bias.py` — Monte Carlo for `Tr P^k - m_k` on the torus (`d = 1, 2, 3`, with
  and without self-loops) against `beta_k/N`.
- `scripts/normalised_walk_variance.py` — `N` times the standard deviation of `Tr P^k` against
  `sqrt(v_k)`, and the coefficients `c_k = v_k/(M m_k^2)`.
- `scripts/subtracted_trace_loops.py` — the subtracted trace with and without self-loops against the
  population value and against the first-order prediction.
- `lean-core/CorrelationsToGeometry.lean` — the author's Lean file (Lean 4.29.0, core library only, no
  Mathlib; 237 theorems, no `sorry`, no `axiom`). Its last section contains the algebra of G.22 and
  G.24 (`gamma_expansion`, `bias_sum`, `bias_loops`, `variance_kernel_sum`, `bias_is_diagonal`) and the
  stability of a row-stochastic matrix in the supremum norm (`Stoch.app_le`, `lax_stability`,
  `weighted_sum_bound`) and the telescoping identity of Theorem G.28, Step 1 (`telescope`), the step inequality (`kernel_step`) and the logic of its induction (`bootstrap`). The probabilistic parts are not formalised. Check with
  `lean CorrelationsToGeometry.lean` (no output and exit code 0 means accepted).

The scripts need `numpy`. All numbers come from single runs with a fixed seed and a few samples per
configuration; they are not evidence for a rate.

## What the numbers show

- Bias, `d = 2`, `xi = 0.05`, `N = 3000`, six samples, relative bias in units of `M/N`, observed /
  formula: `k = 1`: -0.240 / -0.250; `2`: 0.317 / 0.313; `4`: 0.860 / 0.893; `8`: 1.148 / 1.200;
  `16`: 1.144 / 1.186; `32`: 1.001 / 1.025.
- Subtracted trace, `d = 2`, `xi = 0.05`, `N = 1500`, twelve samples: relative deviation from the
  population value at `tau = 10, 20, 40`: 0.053, 0.056, 0.046 with self-loops; -0.002, 0.007, 0.003
  without.
- Variance, `d = 2`, `xi = 0.15`, `N = 800`, 600 samples: `N sd` = 3.69, 2.36, 2.98, 1.54 for
  `k = 1, 2, 4, 8` (statistical error three percent) against `sqrt(v_k)` = 3.49, 2.33, 2.93, 1.48.
  At larger `M/N` the observed values exceed `sqrt(v_k)` by up to about twenty percent.
- Kernel, `d = 2`, `xi = 0.05`, `N = 4000`, one sample (`delta' = 0.36`, so the hypotheses of Lemma G.27
  do not hold; the run shows the shape of the bounds only): `max |N P^k - p_k| / m_k` = 0.51, 0.39, 0.32,
  0.24, 0.21, 0.20, 0.20 for `k = 1, 2, 4, ..., 64`; `max |h_m| sqrt(m) / p_6m` divided by `delta'` =
  1.45, 1.66, 1.71, 1.58, 1.01, 0.46, 0.12 for `m = 1, 2, 4, ..., 64`.
