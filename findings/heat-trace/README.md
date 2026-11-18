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
| Corollary G.31 (`cor:kernel-noloops`) | G.28 and G.29 for the graph without self-loops: `D_1 = m_1`, the bound holds from `k = 2` on, and the subtracted trace is compared with `T_sigma - tau e^(-tau) M` | proven given G.27, G.28; written by the author-side session, read by the second session |
| Proposition G.32 (`prop:reduction`) | Second stage. On the event of G.27: `|Tr P^(k+1) - m_(k+1) - Pi_k| <= C delta'^2 k phi_d(k) m_(k+1)` for an explicit polynomial statistic `Pi_k` of degree four (`phi_d = 1` for `d <= 2`, `1 + log k` for `d = 3`, `k^((d-3)/2)` for `d >= 4`) | proven given G.28; written by the author-side session; read adversarially by a fresh session on the author side (no error, four presentational points included), NOT yet read by the second session; numerics |
| Lemmas G.33, G.34 (`lem:degenerate`, `lem:pibound`) | Moment bounds for statistics that are degenerate in one index, and from them `E|Pi_k| <= C (M/N) k m_k` uniformly in `k` | proven; plan by the second session, written out by the author-side session; read adversarially by a fresh session on the author side (no error; norm table and the representation of `Pi_k` also checked numerically), NOT yet read by the second session |
| Corollary G.35 (`cor:secondstage`) | The rate `xi^2/t` with the sharp coefficient holds in probability for `N xi^(d+4)/log N -> infinity` in dimensions one and two, and for `N xi^7/(log N)^2 -> infinity` in dimension three | proven given G.32 to G.34; read adversarially by a fresh session on the author side (no error), NOT yet read by the second session |
| Lemma G.37, Theorem G.38 (`lem:kernelmatrix`, `thm:eigtorus`) | Eigenvalues of the sampled graph on the flat torus, uniformly in the index and with multiplicities: `|lambda_j^N - (1 - exp(-sigma lambda_j))/sigma| <= C (delta'/xi) max(1, lambda_j)^((d+1)/2)`; the hypothesis `eq:eigrate2` of the paper holds on the torus for `N xi^(3d)/log N -> infinity` | proven given G.28; written by the author-side session, read adversarially by a fresh session on the author side (no error, presentational points included), NOT yet read by the second session; numerics |
| Corollary G.39 (`cor:eigspace`) | Eigenspaces on the torus in the Euclidean norm on the points: every sampled Fourier mode of an eigenvalue `Lambda` lies within `C (delta'/xi) Lambda^((d+1)/2) / gap` of the corresponding eigenspace of the graph | proven given G.38; written by the author-side session, read adversarially by a fresh session on the author side (no error, presentational points included), NOT yet read by the second session |
| Corollary G.40 (`cor:deloc`) | Delocalisation: a unit eigenvector `u` of `S` with eigenvalue index `j` satisfies `max |u_a| <= C max(1, lambda_j)^(d/4) N^(-1/2)` | proven given G.38; written by the author-side session, read adversarially by a fresh session on the author side (no error, presentational points included), NOT yet read by the second session |
| Sharp rate below `(log N/N)^(1/(d+4))`, down to `N xi^(d+2) -> infinity` | would need the terms of second order in the normalisation errors explicitly and uniformly in `k` (numerically they contribute at the same order `M/N` as `Pi_k`) | open; conjecture |
| Theorem G.14, proof | Six small gaps closed (self-term in Step 1, tail `j > J`, bounds on Theta, uniform form of the expansion, two presentational points); statement unchanged | done in the paper; not part of this folder |

## Files

- `appendix_G22_G44.pdf` — the pages of the paper with G.22 to G.44 (the first and the last page
  also show the end of the preceding and the beginning of the following item).
- `bias_variance_excerpt.tex` — TeX of Propositions G.22, G.24 and Remarks G.23, G.25.
- `kernel_bound_excerpt.tex` — TeX of Lemmas G.26, G.27, Theorem G.28, Corollaries G.29 to G.31, Lemma G.37, Theorem G.38, Corollaries G.39, G.40, Remarks G.41, G.42 (numbers as in `appendix_G22_G44.pdf`).
  Both are fragments that use the macros and labels of the paper; they do not compile on their own.
- `scripts/torus_eigenvalues.py` — eigenvalues of the graph Laplacian against the population values of G.38.
- `scripts/kernel_sup_norm.py` — for one sample, the entrywise error of `P^k` against the heat kernel and
  the size of the consistency defect relative to the bound of Lemma G.27.
- `second_stage_excerpt.tex` — TeX of G.32 to G.36 (reduction, degenerate statistics, bound for `Pi_k`, corollary, remark).
- `scripts/second_stage_reduction.py` — for one sample, the trace error, `Pi_k` and the remainder of G.32.
- `scripts/second_stage_remainder_mc.py` — the remainder of G.32 over independent samples: a bias of order `M/N` (0.39 to 0.89 times `(M/N) m`) with smaller fluctuations; numerics only.
- `scripts/corrected_estimator_sample.py` — the corrected estimator of G.30 on sampled graphs with and without self-loops, against the population walk; numerics only, outside the range where the bound of G.30 is small.
- `scripts/second_stage_entrywise.py` — the reduction of G.32 entry by entry (remark G.36 (iii)); `scripts/pi_k_large_k.py` — `E|Pi_k|/((M/N) m_k)` for `k` up to 256 (levels off at about 0.4).
- `scripts/profile_counterexample.py` — counterexample to the earlier wording of the theorem on other profiles (hypothesis (F2) was incomplete; corrected in the paper on 17 November 2026); `scripts/sphere_beta_check.py` — the quartic coefficient of the population walk on the sphere.
- `scripts/pi_k_bound_mc.py` — Monte Carlo attempt to falsify G.34: `E|Pi_k| / ((M/N) k m_k)` stays between 0.19 and 0.29 for `k = 1` and falls to about 0.01 for `k = 32` (`d = 2`, `N` from 300 to 1200); no contradiction.
- `scripts/normalised_walk_bias.py` — Monte Carlo for `Tr P^k - m_k` on the torus (`d = 1, 2, 3`, with
  and without self-loops) against `beta_k/N`.
- `scripts/normalised_walk_variance.py` — `N` times the standard deviation of `Tr P^k` against
  `sqrt(v_k)`, and the coefficients `c_k = v_k/(M m_k^2)`.
- `scripts/subtracted_trace_loops.py` — the subtracted trace with and without self-loops against the
  population value and against the first-order prediction.
- `lean-core/CorrelationsToGeometry.lean` — the author's Lean file (Lean 4.29.0, core library only, no
  Mathlib; 265 theorems, no `sorry`, no `axiom`). Its last section contains the algebra of G.22 and
  G.24 (`gamma_expansion`, `bias_sum`, `bias_loops`, `variance_kernel_sum`, `bias_is_diagonal`) and the
  stability of a row-stochastic matrix in the supremum norm (`Stoch.app_le`, `lax_stability`,
  `weighted_sum_bound`) and the telescoping identity of Theorem G.28, Step 1 (`telescope`), the step inequality (`kernel_step`) and the logic of its induction (`bootstrap`). As whole deductions, with the non-formalised inputs as explicit hypotheses: `kernel_induction` (Step 4 of
  G.28), `eigtorus_ii` (part (i) implies part (ii) of G.38), `delocalisation` (G.40). The probabilistic parts are not formalised. The namespace `CTG.TwoMode` at the end
  contains the algebra of work package WP1 of `PLAN.md` (symplectic spectrum of the two-mode covariance
  matrix: `xp_eigenvalues`, `xp_charpoly`, `rotation_diagonalises`, `squeeze`, `symplectic_block`,
  `symplectic_diagonal`), without Mathlib and with the square roots as hypotheses; it does not replace
  milestone M1 of the Mathlib project. Check with
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
- Eigenvalues, `d = 2`, `xi = 0.05`, three samples each: within a group of equal eigenvalues the mean relative
  deviation of the graph eigenvalues from the population value is -0.99, -1.06, -1.31 times `M/N` for
  `lambda = 39.5, 79.0, 157.9` at `N = 3000`, and the spread within the group is 0.6 to 1.4 times
  `N^(-1/2)`. Reading (not proven): a bias of order `M/N` and a random splitting of relative order
  `N^(-1/2)` for a single eigenvalue; the bound of G.38 is far from sharp.
- Falsification test (`scripts/torus_eigenvalue_groups.py`, `xi = 0.1`, `lambda = 39.5`, 120/80/40 samples at
  `N = 400/800/1600`): the standard deviation of the mean of a group of eigenvalues times `N` is 3.5, 3.7, 3.3,
  that of the lowest eigenvalue of the group times `sqrt(N)` is 0.53, 0.48, 0.51. The alternative that the group
  mean fluctuates at order `N^(-1/2)` is rejected by these numbers; the single eigenvalue does.

## Review on 17 November 2026

Appendix G (G.1 to G.21 and G.32 to G.40) was read by further AI sessions on the author side, each instructed to find errors and unaware of earlier assessments. Result: one error in a statement (a missing hypothesis in the theorem on other profiles, with an explicit counterexample; corrected), otherwise gaps of presentation, which were closed. Cited results were not checked by these readings. No person has read the proofs. A comparison with the literature (abstracts, introductions and main theorems only) is in remark G.41 (v) of the paper: an estimate of graph Laplacian eigenvalues that is uniform in the index up to the scale of the inverse squared bandwidth exists already for Poisson point clouds with the indicator kernel (Armstrong and Venkatraman, arXiv:2312.08149).

## Second Lean file (uses Mathlib)

`lean-core/CorrelationsToGeometryReal.lean` imports the core file unchanged and Mathlib at tag v4.29.0 (Lean 4.29.0). It shows that the real numbers are Archimedean in the sense of the core file and that `Real.exp` has the two properties the core file assumes of `exp`, so that the Taylor bounds, the convergence of the exponential series, the low-mode estimate of the corrected estimator and the Poisson identity hold for the real exponential without a hypothesis on it. Sixty statements (among them: an inequality of Bernstein type, proven in the file because the library has none; the weighted recursion of the kernel theorem for matrices; the deterministic core of the kernel theorem G.28 for matrices, i.e. stability in the supremum norm, the telescoping identity and a conditional form whose hypothesis is the consistency lemma; the flat torus of every dimension, the almost sure form of the trace bounds by Borel-Cantelli, a lattice-point count for the upper Weyl bound on the torus; the trace bounds of the walk with their probability on a torus, i.e. a compact abelian group with Haar measure and a translation-invariant Lipschitz kernel, with the circle as a checked instance; the uniform concentration of the normalisation over all points via a net and Lipschitz continuity; the spectrum of the normalised graph matrix lies in [-1, 1]; Hoeffding for the normalisation at a fixed point, with the probability theory of Mathlib; the deterministic part of the proof of Theorem 3.12 as an inequality for arbitrary real symmetric matrices, with a conditional form whose hypotheses are the eigenvalue estimates; the lower bounds of the heat trace for matrices and the identity of Theorem 3.11 with the matrix exponential, `Tr exp(tau (S - 1)) = sum_j e^(-tau) tau^j/j! Tr S^j`, for every real symmetric matrix without hypotheses; the Poisson identity stated with `HasSum`, and, via the spectral theorem of Mathlib, the Poisson representation of Theorem 3.11 in spectral form for arbitrary real symmetric matrices without hypotheses), standard axioms only, no `sorry`. The existence of the sums over the modes is still a hypothesis. `lean-core/check_real.sh` documents how it was checked on the author-side machine (paths refer to that machine). This file is independent of the Mathlib project in the root of this repository and does not replace it.
