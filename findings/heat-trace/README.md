# From Correlations to Geometry — paper (version 4) and machine-checked statements

**Authors:** Michael Neuberger (Versino PsiOmega GmbH) and Christoph Heuwieser.
**Version 4, 27 November 2026.** DOI of this version: [10.5281/zenodo.24580848](https://doi.org/10.5281/zenodo.24580848);
all versions: [10.5281/zenodo.16605659](https://doi.org/10.5281/zenodo.16605659).

| What | Where |
|---|---|
| The paper (181 pages) | [`paper/correlations_to_geometry.pdf`](paper/correlations_to_geometry.pdf), source `paper/correlations_to_geometry.tex`, figures `paper/figures/` |
| Lean 4 files (56 files, 4745 accepted statements) | [`lean-core/`](lean-core/), one check script per file |
| Numerics (every number in the paper comes from one of these) | [`scripts/`](scripts/) |
| Contributions and cross-reading of the second session | [`second-session/`](second-session/) |
| How the material grew, day by day (the former README) | [`HISTORY.md`](HISTORY.md) |
| Superseded excerpts | `archive/` |

## What the paper is

*From Correlations to Geometry. A Conditional Spectral Reconstruction* asks which parts of the programme
"geometry from correlations" can be proved with present means. The input is a matrix of mutual informations
between subsystems; a diffusion-map pipeline reconstructs the Laplace–Beltrami operator, its spectrum, a spectral
embedding and curvature invariants. Every statement carries a status in Table 1 of the paper:
proven / cited / proof in outline / conditional / numerics / open.

## Read this before quoting anything

* **No proof has been checked by a person independently of the AI sessions with which the paper was written.**
  This sentence stands in the abstract. The paper was written by the authors working with sessions of an AI system
  (Claude); Appendix G from Proposition G.22 on and Appendix H were obtained by two such sessions, one on each
  author's side, working together over an a4sx mesh and cross-reading each other.
* **The Lean files prove *forms* of statements of the paper, not the statements in their wording.** Typically:
  flat torus (or the sphere S², or a compact manifold, as stated per file), Gaussian profile, explicit constants
  that are far larger than those of the paper, exceptional events of the file's own, nested samples (the first N
  points of one sequence), and often a different proof. Remark G.49 of the paper ("Machine-checked statements") and
  its addendum say for each item what is covered and what is not. Do not write "Theorem X is machine-checked"
  without that qualification.
* **Not formalised in any form:** the reconstruction theorems of Section 3 on general manifolds (Laplace–Beltrami
  on curved manifolds is not in Mathlib), completeness on the sphere, Theorem 6.3 (`thm:vargap`), modular data, and
  anything about field equations (the paper derives none; Appendix H states what remains free).
* The Lean statements written after 25 November 2026 have not been read by anyone but the session that wrote or
  checked them. The ten JPEG figures were made with an image generator and are marked as schematic in their captions.

## The Lean files

Lean 4.29.0 with Mathlib at tag v4.29.0 (the core file uses no Mathlib). No `sorry`, no `axiom`, no
`native_decide`; whatever is not proven is a hypothesis of the statement and marked HYPOTHESIS in the comment.
Each file has a header that says what is proven, what is a hypothesis and what is not formalised.

To check a file, run its script from `lean-core/` (for example `./check_real.sh`, `./check_flat_npoint_lattice_direct.sh`);
"accepted" means Lean reported no error. Most files import the compiled module of an earlier file; the header of
each script names it. The large files need about 2.5 GB of memory and up to 50 minutes.

**Core file, no Mathlib (any ordered field)**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometry.lean` | 265 | Algebra of Section 9 (field contents, linear relations, values of lambda), concavity, time reversal, spectral bounds for the heat trace, Poisson identity, mode estimates for Appendix G; existence of series sums is always a hypothesis |

**Appendix G on the flat torus, over the reals (Mathlib)**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometryReal.lean` | 593 | Theorem 3.11 for real symmetric matrices; Weyl inequality; Bernstein; periodised Gaussian kernel; consistency lemma; the estimate of Theorem G.28 (`kernel_theorem_G28`) and of Theorem G.38 (`eig_theorem_G38`, `eig_theorem_G38_i`); trace G.29; measurability of the exceptional sets |
| `lean-core/CorrelationsToGeometryReal2.lean` | 624 | Reduction and second stage (G.34, G.42, G.43: `pi_bound`, `torus_reduction_paper`, `second_stage_limit`); G.30, G.31, G.37, G.39, G.40, G.44 in sample forms; almost-sure forms under the regime |
| `lean-core/CorrelationsToGeometryReal3.lean` | 1016 | Rates of G.29; Theorem G.4 and G.5 as statements on sums with the constants of the paper; sharp rate (`sharp_rate_ae`); consistency lemma with the weight of the paper; older parts G.1-G.21 in torus forms; walk counting G.13; bias for k = 1, 2, 3; variance for k = 1; one-dimensional part of the sphere |
| `lean-core/CorrelationsToGeometryReal3b.lean` | 487 | Deterministic cores of Appendix H (lapse, cross-ratio, Schwarzian, stability); variance for k = 2; Lemma `lem:degenerate`(b) for three indices; bias for every k |
| `lean-core/CorrelationsToGeometryReal4.lean` | 392 | Variance for every k, with and without self-loops, with the remainders of the paper; bias without self-loops; `lem:degenerate` for any number of indices; limits N(E Tr P^k - m_k) -> beta_k and N^2 Var -> v_k |

**Laplacian and heat operator of the flat torus**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometrySpectrum.lean` | 49 | Classical eigenfunctions of the Laplacian on the flat torus and their multiplicities (Mathlib only) |
| `lean-core/CorrelationsToGeometryHeatOperator.lean` | 25 | Heat semigroup as a diagonal operator on L^2, trace class, trace = theta sum (builds on two files ported from the Lean archive of Levent Alpöge, see below) |
| `lean-core/CorrelationsToGeometryHeatSpectrum.lean` | 33 | m_k and the Poisson mean as traces of powers of one operator; action on Fourier modes |
| `lean-core/CorrelationsToGeometryHeatSpectrumL2.lean` | 33 | Spectrum and eigenspaces of the heat operator on L^2; generator on trigonometric polynomials |

**Riemannian distance in time and the two-time statement of Appendix H on compact manifolds**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometryManifold.lean` | 108 | Mathlib's Riemannian distance under a time-dependent metric: comparison, Lipschitz dependence on time, kernel increments, minimising curves (metric), length = variation for C^1 paths |
| `lean-core/CorrelationsToGeometryVolume.lean` | 12 | Hausdorff measure of small balls on a compact manifold; volume growth of a sampling measure |
| `lean-core/CorrelationsToGeometryNPoint.lean` | 49 | Steps 2-5 of Proposition H.33 (`prop:dotLN-diff`) with abstract kernel bounds |
| `lean-core/CorrelationsToGeometryNPointGeom.lean` | 6 | The same without geometric hypotheses (crude form) |
| `lean-core/CorrelationsToGeometryNPointRate.lean` | 39 | Rate bookkeeping for the crude form |
| `lean-core/CorrelationsToGeometryNPointSharp.lean` | 59 | Repaired form: error C delta' in the regime N xi^n >= C log N |
| `lean-core/CorrelationsToGeometryNPointLip.lean` | 34 | Lipschitz test function: first inequality in the form C delta'/xi (`npoint_step5_lip_geom_log`) |
| `lean-core/CorrelationsToGeometryNPointUniform.lean` | 11 | Finitely many pairs of times; measurability |
| `lean-core/CorrelationsToGeometryNPointGrid.lean` | 25 | All pairs of a time window on one event (crude constants) |

**Flat core of Theorem 3.1 and the two-time statement on the flat torus**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometryFlatLB.lean` | 16 | Averaging operator: expansion to third order, radial kernels |
| `lean-core/CorrelationsToGeometryFlatLB2.lean` | 14 | C^3 functions, Mathlib's Laplacian, conformally flat metrics, two times |
| `lean-core/CorrelationsToGeometryFlatLB3.lean` | 22 | Fourth order; error xi^2 min{C1/|eta|, C2} |
| `lean-core/CorrelationsToGeometryFlatLB4.lean` | 12 | General constant metric; time-dependent test function |
| `lean-core/CorrelationsToGeometryFlatNPoint.lean` | 27 | Both inequalities of `prop:dotLN-diff` as one statement on the flat torus (compactly supported profile) |
| `lean-core/CorrelationsToGeometryFlatNPointRate.lean` | 16 | The same in the rate form C delta'/xi |
| `lean-core/CorrelationsToGeometryFlatNPointFinal.lean` | 15 | Bounded derivative from periodicity; measurability; finitely many pairs; `prop:dotL` flat |
| `lean-core/CorrelationsToGeometryFlatNPointClose.lean` | 9 | `prop:dotL` in the flat conformal case without hypothesis |
| `lean-core/CorrelationsToGeometryFlatNPointWindow.lean` | 27 | All pairs of times of a window on one event |
| `lean-core/CorrelationsToGeometryFlatNPointWindow2.lean` | 24 | The same without free parameters, probability 32 D^2/N^2; measurability |
| `lean-core/CorrelationsToGeometryFlatNPointGauss.lean` | 45 | Gaussian profile cut off at a radius |
| `lean-core/CorrelationsToGeometryFlatNPointGaussFull.lean` | 18 | Full Gaussian profile by comparison (weak form) |
| `lean-core/CorrelationsToGeometryFlatNPointGaussLattice.lean` | 24 | Sharper comparison; kernel summed over all lattice images on the sample side |
| `lean-core/CorrelationsToGeometryFlatNPointLatticePop.lean` | 18 | Population operator of the lattice-sum kernel (unfolding) |
| `lean-core/CorrelationsToGeometryFlatNPointLatticeDirect.lean` | 67 | The statement directly for the periodised Gaussian kernel, no cut-off (`flat_npoint_lattice_direct`) |
| `lean-core/CorrelationsToGeometryGaussMoment.lean` | 10 | Second moment of the Gaussian profile is 1; final form `flat_npoint_lattice_final` and measurability of its exceptional set |

**The sphere S^2**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometryFunkHecke.lean` | 77 | Area measure, rotation invariance, Funk-Hecke for every degree on (a.y)^l, eigenvalues s_l of the population walk |
| `lean-core/CorrelationsToGeometryFunkHeckeLink.lean` | 6 | The copied definitions agree with those of the seventh file |
| `lean-core/CorrelationsToGeometryFunkHeckeMult.lean` | 24 | Multiplicity at least 2l+1 |
| `lean-core/CorrelationsToGeometryFunkHeckeSample.lean` | 24 | Sampled walk at fixed scale, one step |
| `lean-core/CorrelationsToGeometryFunkHeckePowers.lean` | 26 | Iterates of the sampled walk |
| `lean-core/CorrelationsToGeometryFunkHeckeSampleEig.lean` | 16 | An eigenvalue of the sample matrix near s_l |
| `lean-core/CorrelationsToGeometryFunkHeckeSampleMult.lean` | 8 | Deterministic part of: at least 2l+1 eigenvalues near s_l |
| `lean-core/CorrelationsToGeometryFunkHeckeSampleMultProb.lean` | 2 | The same for random points |
| `lean-core/CorrelationsToGeometryFunkHeckeSampleMultAE.lean` | 8 | Almost surely; several degrees at once |
| `lean-core/CorrelationsToGeometryFunkHeckeDistinct.lean` | 13 | s_l strictly decreasing for low degrees and small xi |
| `lean-core/CorrelationsToGeometryFunkHeckeSphereLB.lean` | 24 | (2/xi^2)(1 - s_l) -> l(l+1) with explicit error |
| `lean-core/CorrelationsToGeometryFunkHeckeSphereLaplace.lean` | 10 | A Laplacian of the sphere defined extrinsically; eigenvalue -l(l+1) for harmonic homogeneous functions; the limit statement with it |
| `lean-core/CorrelationsToGeometryFunkHeckeSphereLinComb.lean` | 33 | The same for finite linear combinations of the harmonics |

**Bessel functions (Appendix H)**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometryBessel.lean` | 43 | K_0, K_1 by their integral representations; 0 < z(K_1/K_0 - 1) <= 1/2; Proposition `prop:lapse-stab` with its constants |

**Density response of the kernel graph (note after Proposition 9.8)**

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometryDensityResponse.lean` | 29 | Finite form: S = diag(A) K diag(A); first-order response of q, D, A and of Tr P^k |
| `lean-core/CorrelationsToGeometryDensityResponseCont.lean` | 50 | Integral kernels; convolution kernels on a group |
| `lean-core/CorrelationsToGeometryDensityResponseTorus.lean` | 11 | Flat torus, heat kernel: factor (1 - e^{-xi^2 a^2/2})^2/2 <= (a xi)^4/8, no hypothesis |
| `lean-core/CorrelationsToGeometryDensityResponseTrace.lean` | 56 | Derivatives of all iterated kernels and of their traces |
| `lean-core/CorrelationsToGeometryDensityResponseLocal.lean` | 25 | Local response (diagonal of the iterated kernels); Fourier sum on the torus |
| `lean-core/CorrelationsToGeometrySqrtSeries.lean` | 17 | Power series of 1 - sqrt(1-s) through the Catalan numbers; sum over the powers for one mode |
| `lean-core/CorrelationsToGeometryDensityResponseSum.lean` | 19 | Sum over powers and modes; symmetrised form |
This is a different project from the Mathlib project in `CorrelationsGeometry/` at the root of this repository
(Lean 4.36, written independently, see the root `README.md`); the two are not merged.

## After version 4

Lean files added after the text of version 4 was fixed. They are described in the working text after version 4,
[`paper/after-v4/correlations_to_geometry.pdf`](paper/after-v4/correlations_to_geometry.pdf), in paragraphs marked "after version 4"; the
paper in `paper/` is the deposited version 4 and is unchanged.

| File | Statements | Content |
|---|---:|---|
| `lean-core/CorrelationsToGeometryFlatNPointLatticeWindow.lean` | 26 | The two-time statement for the periodised Gaussian kernel for ALL pairs of times of a window on one event (`flat_npoint_lattice_window`), and without free parameters with exceptional probability at most 32 D²/N² (`flat_npoint_lattice_window_N2`); pairs of times closer than η₀ are not shown (measurability: next file); read by nobody |
| `lean-core/CorrelationsToGeometryDensityResponseExchange.lean` | 12 | Exchange of the derivative in the density with the sum over the powers, finite-dimensional and abstract: after splitting off the top mode, under a uniform spectral gap (a hypothesis), the sum of the termwise derivatives is the derivative (`deriv_sum_powers`); `r = sqrt(n D)` is the top eigenfunction of the symmetrised kernel (`Sc_top_eigen`). The flat torus (infinite-dimensional, gap for small perturbations) is not formalised; read by nobody |
| `lean-core/CorrelationsToGeometryFlatNPointLatticeWindowFinal.lean` | 15 | Final form of the window statement for the periodised Gaussian kernel: second moment 1 inserted, the same kernel in the sample and in the population operator (`flat_npoint_lattice_window_final`), and measurability of its exceptional set (`flat_npoint_lattice_window_final_set_measurable`); pairs of times closer than η₀ are not treated; read by nobody |
| `lean-core/CorrelationsToGeometryDensityResponseExchangeGraph.lean` | 20 | The exchange of derivative and sum over the powers for the concrete finite kernel graph: top eigenvector, smoothness in the density, gap for small perturbations from the gap of the background (the background gap is a hypothesis), `graph_deriv_sum_powers`; the continuum case is not formalised; read by nobody |
| `lean-core/CorrelationsToGeometryDensityResponseDoeblin.lean` | 13 | Spectral gap of the background from strict positivity of the kernel (`doeblin_gap`, `Sn_gap`), and with it the exchange of derivative and sum over the powers for a finite kernel graph without a gap hypothesis (`graph_deriv_sum_powers_pos`); the constant is exponentially small for a Gaussian kernel on many points, so nothing uniform in the number of nodes follows; read by nobody |
| `lean-core/CorrelationsToGeometryFlatNPointLatticeDeriv.lean` | 47 | Time derivative of the sampled operator and all pairs of times of a window for the periodised Gaussian kernel (`flat_npoint_lattice_deriv`): the derivative exists for every sample, and on the event of the window statement it is controlled up to a term `M_tot·η₀` with an explicit but very large `M_tot`; the choice of `η₀` that makes this a rate statement is not made; measurability not shown; read by nobody |
| `lean-core/CorrelationsToGeometryFlatNPointLatticeRate.lean` | 15 | Rate statement for the time derivative of the sampled operator, periodised Gaussian kernel, flat torus (`flat_npoint_lattice_deriv_rate`): outside a set of probability at most 32 D²/N² (D explicit, independent of N), for all times of a window and all sample points, the derivative exists and is within C(δ'/ξ + ξ²) of the derivative of the Laplacian term; the constant is a large negative power of ξ and is not evaluated; measurability not shown; the derivative of the scale is assumed Lipschitz; read by nobody |
| `lean-core/CorrelationsToGeometryDensityResponseKernel.lean` | 80 | Exchange of the derivative in the density with the sum over the powers for integral kernels, by a Doeblin argument on the kernels (no spectral theory), and on the flat torus without hypothesis: the first-order density response of the energy density of the node model summed over all powers equals (1 − t_n)² Σ_m cl(t_m, t_{m+n}) Re χ_n(x) (`torus_density_response`), the lattice form of α(a) I(a) in the note after Proposition 9.8; continuum limit, coefficient c(a) and its limit 3(aξ)² not formalised; read by nobody |
| `lean-core/CorrelationsToGeometryDensityCoefficient.lean` | 66 | Coefficient of the density term of the node model: on the flat unit torus, for d ≥ 2 and n ≠ 0, the ratio c/(b_R (aξ)²) tends to 3 (`coefficient_limit`), confirming the statement of the note after Proposition 9.8 in the joint limit c → 0 at fixed n; b_R is the normalising constant of equation (9.16); the integral at finite aξ, the next order and the case d = 1 (where the statement fails, as the paper says) are not formalised; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeComplete.lean` | 27 | Completeness on the sphere: the harmonics Re(a·y)^l span a dense subspace of C(S²) (`harmCl_eq_top`, `harm_approx`, no hypothesis); Theorem 3.1 on S² for series of harmonics with summable degree-weighted bounds (`LB_sphere_series`), with the termwise application of the extrinsic Laplacian as a hypothesis; that smooth functions have such series is not formalised; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeTermwise.lean` | 31 | Theorem 3.1 on S² for series of harmonics without the termwise-Laplacian hypothesis: under summable explicit bounds `degM` from the coefficients the extrinsic Laplacian may be applied termwise (`sphLapS_hasSum`), giving `LB_sphere_series_M`; that smooth functions have such series is not formalised; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeProj.lean` | 40 | Orthogonality of the degrees of harmonics on S² (`orth_harm`, `orth_span`, every pair of degrees, via Funk–Hecke with the Legendre weight, no self-adjointness of the Laplacian needed) and the projection onto a degree (`proj_self`, `proj_other`, `proj_mem`, `proj_orth`); convergence of the series of projections and decay from smoothness are not formalised; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeParseval.lean` | 27 | Parseval on S² for continuous functions (`bessel`, `L2_tendsto`: partial sums of the projections converge in L², `parseval`, no hypothesis), reproducing-kernel bound `|F x| ≤ √(2l+1)·‖F‖₂` on a degree (`repro_bound`); decay of the projections from smoothness (`decay_L2`, `decay_sup`) only under the HYPOTHESIS that projection and Laplacian commute, which is not proven; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeGreen.lean` | 45 | Green's identity on S² for the extrinsically defined Laplacian (`sym_S2`, `green_harmonic`; radial cut-off on a shell, integration by parts in ℝ³, polar coordinates), commutation of projection and Laplacian (`proj_lap`: Π_l(Δf) = −l(l+1)·Π_l f) and decay of the projections from smoothness without hypothesis (`decay_sup_fin`: (l(l+1))^k·|Π_l f(x)| ≤ √(2l+1)·‖Δ^k f‖₂); regularity via `SphC2`; not shown: identification with the intrinsic Laplace–Beltrami operator, uniform convergence of Σ Π_l f; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeLBSmooth.lean` | 24 | Theorem LB on S² for smooth functions at the population level, for the extrinsically defined Laplacian (`LB_sphere_smooth_sup`: ∃ C, |L_ξ f(x) + Δf(x)| ≤ C ξ² for all x and 0 < ξ ≤ 1/20, if Δ^j f, j < 4, have C² extensions of degree zero; C = 3·W·‖Δ⁴f‖₂); pointwise expansion f = Σ Π_l f (`expansion`), expansions of L_ξ and Δ; not shown: identification with the intrinsic Laplace–Beltrami operator, value of W, sample statements; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeLBSample.lean` | 13 | Sample version of Theorem LB on S² for smooth functions (extrinsic Laplacian, walk with self-loop): at fixed ξ with probability bound (`LB_sample`) and almost surely up to Cξ² + ε (`LB_sample_ae`), and in a joint limit ξ_N → 0 with (N−1)ξ_N⁸/log N → ∞ almost surely max_i |L_N f(X_i) + Δf(X_i)| → 0 (`LB_sample_joint`; regime from coarse constants, not sharp); measurability of the exceptional sets not shown; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeSphereCoord.lean` | 31 | The extrinsically defined Laplacian of S² equals in spherical coordinates the classical coordinate formula of the Laplace–Beltrami operator of the round metric, (1/sinθ)∂_θ(sinθ ∂_θ u) + (1/sin²θ)∂_φ²u (`sphLapS_coord`, `lap_spherical_div`; via the trace of the Hessian in an orthonormal frame); consistency check on harmonics (`coord_harmonic`); poles and an intrinsic operator in Mathlib not covered; read by nobody |
| `lean-core/CorrelationsToGeometryFunkHeckeSphereCharts.lean` | 20 | Two charts for S²: every non-polar point is Φ(θ,φ), the poles are covered by a rotated chart; the Laplacian of ℝ³ is invariant under linear isometries (`laplacian_comp_isometry`), so at every point of S² the extrinsic Laplacian equals the coordinate formula of the round metric in one of the two charts (`sphLapS_atlas`); charts in the sense of Mathlib and an intrinsic operator not covered; read by nobody |

## Third-party material

* `lean-core/ports/alpoge-rh/`: two files (`HilbertSchmidt.lean`, `TraceClass.lean`) from the Lean archive that
  accompanies the note of **Levent Alpöge** (https://alpo.ge/remark.pdf, 20 November 2026), ported to Lean 4.29;
  every change and the SHA-256 of the original are in the file headers; the unchanged originals are in
  `vendor/alpoge-rh/` at the repository root. Three files here build on them (`…HeatOperator`, `…HeatSpectrum`,
  `…HeatSpectrumL2`). **The archive carries no licence and its author has not been asked**; the files are included
  with attribution and will be removed on request.
* `vendor/openai-math-reference/` at the repository root: unchanged reference copies from github.com/openai/math
  (Apache License 2.0). Nothing here imports them.

## Licence

Lean files and scripts: Apache License 2.0. Paper and figures: CC BY-NC 4.0 (as on Zenodo). Third-party material is excluded.
Details and exceptions: [`LICENSE.md`](LICENSE.md).

## Contact

Michael Neuberger, Versino PsiOmega GmbH. Christoph Heuwieser, X: @dropdeadfu.
