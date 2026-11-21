# Review of the Lean files of `openai/math` for statements this paper could reuse

Second session of an AI system, 2026-11-21/22, on the repository owner's instruction. This is a reading list,
not a result: nothing in it was compiled, imported or proved here.

**Source.** Public repository `github.com/openai/math`, commit `4eaee875` (2026-10-29): 163,096 Lean files in
1,137 projects under `lean/OAI/<Area>/<Project>/`. Its root `LICENSE` file is the Apache License 2.0 text; its
`lean/lean-toolchain` says `leanprover/lean4:v4.34.1` (the paper's Lean files are on 4.29.0). The statement
headers quoted in `shortlist_score3.md` are taken verbatim from that repository; all paths are relative to
`lean/OAI/`.

**Method.**
1. Stage 1 (file names only): 14 readers went through the index of all file names, 4 through `CONTENTS.md`;
   2,245 candidate files, every path checked against the repository's file list.
2. Stage 2 (statements): for every candidate file, and for every file of the 55 folders in
   `folders_read_in_full.txt`, the declaration headers (keyword up to the first `:=`, proofs left out) were cut
   out mechanically: 4,966 files, 48,108 declarations. 50 readers (Claude Opus, medium effort) read them one
   by one against `reader_brief.md` (needs N1 to N9) and listed 2,516 statements; each listed line was checked
   mechanically against the text the reader had (file, number and name must match; 0 mismatches).
3. The 253 files that hold a statement rated 3 were scanned as text (comments stripped) for `sorry`, `admit`,
   `axiom`, `native_decide` and own `macro`/`elab`/`syntax` declarations: none found.

**Files.**
- `shortlist_score3.md`: the 398 statements rated 3 ("general and squarely on a need"), grouped by need, each
  with the reader's one-line description, caveat and the source wording.
- `statements_all.tsv`: all 2,516 lines: score, need, file, `[k] name`, description, general/special/project,
  caveat, bundle.
- `reader_brief.md`, `folders_read_in_full.txt`: what the readers were asked and which folders were read whole.

**What was and was not verified.**
- Read at the source by the session itself (wording and surrounding definitions): 
  `Combinatorics/Progressions/Lattices/LatticeGaussianPoisson` `normalizedLatticeGaussian_poisson`
  (Poisson summation of the Gaussian for an arbitrary lattice, any dimension),
  `InformationTheory/PhotonNumber/ThermalLimit` `thermalState_entropy` (= n g(r)),
  `MathematicalPhysics/PEPSMove/StrongSubadditivity` `strong_subadditivity`,
  `Geometry/RCD/Heat/CanonicalAllTimeLogLimit` `canonicalHeatKernel_compact_log_limit_allTimes`.
  A random sample of nine further rated-3 lines was compared with the source wording: all nine descriptions
  matched.
- NOT verified: that anything builds under Lean 4.29 or at all here; the bodies of the definitions the
  statements use (a name such as `canonicalHeatKernel`, `NoncollapsedRCD`, `entropy`, `ptrR` hides
  hypotheses; the readers' caveats say where a judgement depends on one); the remaining descriptions.
- Coverage limit: files that stage 1 did not pick by name and that lie outside the 55 folders were not read.
  Statement headers longer than 1,400 characters were cut ("statement cut" in the caveat).
- Need N6 (heat kernels on manifolds: Gaussian bounds, Li-Yau, Varadhan-type limit) has no line rated 3
  because all such statements are for the repository's own noncollapsed RCD(K,n) setting; they are rated 2
  under `Geometry/RCD/Heat` and `Analysis/RCDHeat` in `statements_all.tsv`.
