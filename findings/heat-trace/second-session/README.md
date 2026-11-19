# Contributions of the second session

Material written by the Claude session on the repository owner's side ("the second session" in
`../README.md`), put on this branch on 19 November 2026. Nothing here is part of the paper, and nothing
here has been read by a person. Each file states its own status at the top.

| File | Content | Status on 19 November 2026 |
|---|---|---|
| `l1_kernel_lemma.tex` | Lemma: on the event of the consistency lemma, `(1/N) sum_a |N (P^k)_ai - p_k(x_a - x_i)| <= C delta' sqrt(k)` for `k <= delta'^(-2)`. The proof uses the stationary weight `w_b = u_b r_b` of the walk and the telescoping identity of G.28; no induction, no doubling property, no smallness condition. | Lemma and proof recomputed on paper by the author-side session: no error; that session improved a constant from 3 to 9/7. Machine-checked by the author-side session for random samples on the torus: `heat_kernel_l1_sample` in `../lean-core/CorrelationsToGeometryReal.lean` (its own hypotheses and range, see `../README.md`; standard axioms only). |
| same file, first consequence | In the reduction G.32 the factor `phi_d(k)` can be dropped in every dimension, so the second stage (G.35) would hold for all `d` under `N xi^(d+4)/log N -> infinity`. | Written by the second session; written out as a proposition and a corollary with full proofs in `l1_consequences.tex`; read line by line by the author-side session on 19 November: no error. Not formalised. |
| same file, second consequence | `||S^k - Q_k|| <= C delta' sqrt(k)` without the factor `m_k`, which would sharpen G.38 to `C (delta'/xi) lambda^(1/2) + C sqrt(log N/N) lambda^((d+2)/2)` and the regime of `eq:eigrate2` to `N xi^(max(d+2, 2d))/log N -> infinity`. | Written by the second session; written out as a theorem with its conditions and proof in `l1_consequences.tex`; read line by line by the author-side session on 19 November: no error; the resulting form fits `eq:eigrate2` of the paper according to that session. Not formalised. |
| `pi_bound_independent.tex` | A proof of `E|Pi_k| <= C (M/N) k m_k` written before the second session had seen G.33 and G.34. Same decomposition of `Pi_k`, different lemma on degenerate statistics (degeneracy in every index, bounds through projections). | Checked by its author session only. The paper's own proof (G.33, G.34) is shorter and needs less; this file is kept as an independent derivation of the same bound. |
| `KernelRecursion.lean` | Lean 4 with Mathlib: the deterministic half of Theorem G.28 for an arbitrary row-stochastic kernel on a finite type: `act_telescope` (Step 1), `abs_act_le_sup` and `abs_act_le_weight` (Step 3), `sum_inv_sqrt_le`, and `kernel_recursion` (the induction of Step 4, constant `24 + 12 A c`). The two bounds of the consistency lemma, the bound for the last step of the walk, and monotonicity and doubling of `m_s` are hypotheses. No restriction to `k sigma <= 1`. | Accepted by Lean with the toolchain and Mathlib of the root project (`v4.36.0-rc2`); no `sorry`; `#print axioms` of the six main statements shows only `propext`, `Classical.choice`, `Quot.sound`. The match between its hypotheses and the statements of the paper has not been checked by a second session or a person. |

## Checking the Lean file

From the repository root (the Mathlib project of `main`; `lake` must find its Mathlib build):

    lake env lean findings/heat-trace/second-session/KernelRecursion.lean

No output and exit code 0 mean accepted (checked on 19 November 2026; it takes a few minutes). The file is deliberately not
inside `CorrelationsGeometry/` and not imported by the root module: `main`'s `README.md` and
`CorrelationsGeometry/Audit.lean` list what that project proves, and this file is not on those lists. To
adopt it there, move it to `CorrelationsGeometry/KernelRecursion.lean`, import it in
`CorrelationsGeometry.lean`, and add its statements to `Audit.lean` and to the README.

It is independent of `../lean-core/CorrelationsToGeometryReal.lean` (Lean 4.29.0, Mathlib v4.29.0), which
contains its own recursion (`kernel_theorem_matrix_min`).

## Cross-reading done by the second session

What was read, in which version, and what was not:

- Lemma G.13, Theorem G.14: read on 17 November; no error, six points of presentation.
- Theorem G.28, Corollaries G.29 to G.31: read on 17 November in the text of that day; no error.
- Proposition G.32 (`prop:reduction`): the draft of 17 November was read line by line and the constants
  were recomputed (the bound `14 delta^2` as `9/7 + 16/7 + 72/49 + 18432/2401 = 12.72`); the text of
  `../second_stage_excerpt.tex` as on this branch was read again on 19 November. No error.
- Lemmas G.33, G.34 (`lem:degenerate`, `lem:pibound`) and Corollary G.35 (`cor:secondstage`): read on
  19 November in the text of `../second_stage_excerpt.tex` on this branch, with the instruction to find an
  error. Recomputed: every case of the proof of G.33 (a) and (b) and the counts of pairs; the
  representation of `Pi_k` by the statistics `Z^0`, `Z^1` (signs and positions `a`); all sixteen entries
  of the table of norms; the insertion into G.33; in G.35 the term `j = 1`, the bounds
  `E|mean(eps)| <= C M/N` and `E eps_l^2 <= 4 M/N` (it is at most `2 M/N`), the Poisson-weighted sum and
  the two cases of `log N` against `xi^(-2)`. No error found.
- Lemma G.37, Theorem G.38 (`lem:kernelmatrix`, `thm:eigtorus`): read on 17 November; the text of these
  two statements on this branch is unchanged since. No error; the theorem needs `N >= N_0` from the
  lemma. Not checked: the wording of `eq:eigrate2` and the comparison with `thm:rate2`.
- Corollaries G.39, G.40 (`cor:eigspace`, `cor:deloc`): read on 19 November in the text of
  `../kernel_bound_excerpt.tex` on this branch, proofs and statements. No error. In G.39 two steps are
  implicit: that the indices `j` with `lambda_j = Lambda` are at most `N` (true for `N >= N_0(d)`, since
  there are at most `C xi^(-d)` eigenvalues up to `xi^(-2)`), and that `k <= (C_1 delta')^(-2)`, which
  follows from `theta_Lambda <= 1` because `Lambda^((d+1)/2)/g_Lambda >= 1`. In G.40,
  `N (S^(2k))_aa = N (P^(2k))_aa` exactly, so the factor `1 + 16 delta` is not needed.
- NOT read by the second session: the remarks, the Lean files in `../lean-core`, and everything in the
  paper outside the excerpts on this branch.

"No error found" by a second AI session is weaker evidence than it sounds: such a reader agrees readily.
For the statements that carry the results, a machine-checked proof and a blind check of the match between
the Lean statement and the paper's statement are the stronger evidence.
