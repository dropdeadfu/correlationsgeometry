# Handover

For whoever picks this work up next, human or agent. It says where the project stands, what to do
next and what is easy to get wrong. `README.md` lists what is proven; `PLAN.md` describes the next
block of work. This file does not repeat them.

Last updated: 2026-11-19, on the branch `mesh/heat-trace-findings` (this is the branch's copy; the copy on
`main` is older and does not mention the branch).

## Keeping this file current

Every push to `main` must leave this file correct. Update it in the same push as the work it
describes, so the head of `main` never carries a stale handover. Rewrite the sections below to
describe the present state; do not append a diary (the Git log is the history). Change the
"Last updated" line each time.

## What the project is

Lean 4 / Mathlib proofs of selected results from M. Neuberger, *From Correlations to Geometry:
A Conditional Spectral Reconstruction* (November 2026, 74 pages). The PDF is not in the
repository; ask the owner for it. Section, theorem and equation numbers in the Lean files and in
the documentation refer to that PDF.

The owner's standard is "no mistake". In practice:

* Report a result as proven only if `lake build` succeeds, the proof has no `sorry`, and
  `#print axioms` shows nothing beyond `propext`, `Classical.choice`, `Quot.sound`.
* Say exactly what each Lean theorem assumes. Where the physics enters as a definition or a
  hypothesis and not as a proof, list it under "What is taken as input" in `README.md`.
* Do not describe a definition as a result. Example: `twoModeMI` *defines* the mutual information
  as `2f(ν) − f(ν₊) − f(ν₋)`; that this is the mutual information of the Gaussian state is not
  proven.

## Current state

Everything in `README.md` under "What is proven" is done and builds. The last piece added was the
analytic half of Proposition 4.2 (`CorrelationsGeometry/TwoModeExpansion.lean`, main theorems
`two_mode_expansion` and `two_mode_expansion_isBigO`).

One branch is open: `mesh/heat-trace-findings`. It adds the folder `findings/heat-trace/` and changes
nothing in the Mathlib project. The folder holds working material on Appendix G of a longer version of
the paper (about 100 pages; `main` refers to the 74-page version): proofs, numerics and two Lean files of
the author's side, written by two AI sessions, one on the author's side and one on the owner's side.
Start with `findings/heat-trace/README.md` (status of every item) and
`findings/heat-trace/second-session/README.md` (what the owner-side session wrote and what it has and
has not read). No statement there has been read by a person.

Pending with the owner, for that branch:

* Whether and when it is merged into `main`. `README.md` and `CorrelationsGeometry/Audit.lean` on `main`
  list what the Mathlib project proves; nothing on the branch is on those lists.
* Whether `findings/heat-trace/second-session/KernelRecursion.lean` (deterministic half of Theorem G.28,
  accepted by Lean with this project's Mathlib) is adopted into `CorrelationsGeometry/`. The steps are
  in the README of that folder.
Both sides push to the branch. Fetch and rebase or merge before pushing. Never force-push and never
rewrite the branch's history without the owner's word.

Not done, and known:

* The quantum half of Proposition 4.2 (see `PLAN.md`). Not started.
* Uniformity of the remainder in `two_mode_expansion` on compact sets of `(x0, p0)`. The constants
  `C`, `δ` are for fixed `(x0, p0)`. Lemma E.3 (c) of the paper uses the uniform version.
* Everything that needs Riemannian geometry on manifolds or quantum field theory (the
  reconstruction theorems, Theorem 4.4, Proposition 4.3). Mathlib does not have the foundations;
  this is left out on purpose.

## Next steps

Waiting for the owner's decision on both. Do not start either without it.

1. **Milestone M1 of `PLAN.md`** (recommended next step, 2 to 4 days): prove that `ν±` are the
   symplectic eigenvalues of the two-mode covariance matrix. Pure matrix algebra; it does not need
   the copied files. Proposed location: `CorrelationsGeometry/Gaussian/`.
2. **Build-only CI.** Offered to the owner, not yet approved. See "Repository conventions".

The other decisions (how far to take the quantum half beyond M1, and by which route) are listed at
the end of `PLAN.md`.

## Layout

| Path | Content |
|---|---|
| `CorrelationsGeometry/*.lean` | The project's own proofs, one file per group of results |
| `CorrelationsGeometry/Audit.lean` | `#print axioms` for every main theorem; its output appears during `lake build` |
| `CorrelationsGeometry.lean` | Root file importing all of the above |
| `vendor/openai-math/` | 26 Lean files copied from github.com/openai/math (Apache-2.0), with licence, provenance README and an audit file |
| `lakefile.toml` | Two libraries: `CorrelationsGeometry` (default target) and `OAI` (the copied files, not in the default build) |
| `README.md` | What is proven, what each result takes as input, how to build |
| `PLAN.md` | Plan for the quantum half of Proposition 4.2 |

## Building and checking

```
lake exe cache get
lake build
```

`lake build` must end with "Build completed successfully" and print only the three standard
axioms for the theorems in `Audit.lean`.

The copied files are built and checked separately (about 4 minutes):

```
lake build OAI
lake env lean vendor/openai-math/Audit.lean
```

Toolchain and Mathlib are both pinned to `v4.36.0-rc2`.

## When adding a result

1. Put it in the fitting file under `CorrelationsGeometry/`, or a new file imported from
   `CorrelationsGeometry.lean`.
2. Add `#print axioms` for it to `CorrelationsGeometry/Audit.lean`.
3. Add a row to the table in `README.md`, and state its inputs under "What is taken as input".
4. Run `lake build` and read the axiom output before claiming anything.
5. Update `PLAN.md` if the plan changed, update this file, commit and push.

The Mathlib linters are on for the `CorrelationsGeometry` library (line length 100 characters,
`change` and not `show` when the goal is altered, and others). Fix the warnings they raise in new
code.

## Things that are easy to get wrong

* **Lean options are per library.** The options in `lakefile.toml` apply to `CorrelationsGeometry`
  only. The copied files are compiled with the upstream option `autoImplicit = false` alone; they
  were not checked under the Mathlib linter set. Do not move the options back to package level.
* **The copied files.** 24 of 26 are byte-identical to upstream commit
  `4eaee87548250b2682affda7d05d947c05554bae`. `Entropy.lean` and `Functions.lean` carry
  compatibility patches and a notice in their first lines. If you change any copied file, add such
  a notice to it and record the change in `vendor/openai-math/README.md`; the Apache licence
  requires it. Prefer adding new files under `CorrelationsGeometry/` to editing copied ones.
* **Nothing imports `OAI` yet.** The first import of an `OAI` module from `CorrelationsGeometry`
  makes `lake build` compile the copied files it needs.
* **What the copied files lack.** Their ladder operators are bounded, regularised versions. There
  are no position or momentum operators, squeezers, covariance matrices, characteristic functions,
  marginals of a state or mutual information. `PLAN.md` gives the consequences for the effort.
* **The paper's `f(ν)` is the copied files' `g (ν − 1/2)`.**
* **Constants blow up as `ν → 1/2`.** A numerical check of `two_mode_expansion` (run outside the
  repository) gave a remainder constant of about 0.36 at `ν ≈ 1.08` and about 327,000 at
  `ν ≈ 0.505`. Any uniform version needs `ν` bounded away from `1/2`.

## Repository conventions

* One branch, `main`. Commit and push each finished, verified piece of work; the owner wants the
  work kept in this repository.
* Commits are made under the owner's GitHub no-reply address, set in the local repository
  configuration, so that no private email address is published. Keep that when working in another
  clone.
* **No GitHub workflows are tracked, on purpose.** `lake new … math` generates three. One creates
  a public release whenever `lean-toolchain` changes; the CI one also tries to deploy a
  documentation site to GitHub Pages. They are kept out until the owner decides. If the owner
  approves CI, add a workflow that only builds.
* Do not rewrite history on `main`.

## Notes for the owner's Windows machine

These apply to that machine only.

* `lake` is not on the `PATH` of an agent shell. It is in the `.elan\bin` folder of the user
  profile.
* The installed Git (2.21) is too old for `lake update` and for GitHub sign-in. A plain
  `lake build` with the dependencies already fetched does not need Git. Pushing needs a current
  Git with Git Credential Manager; the owner has signed in once, so the credential is stored.
