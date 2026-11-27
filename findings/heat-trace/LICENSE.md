# Licences

Copyright 2025–2026 Michael Neuberger and Christoph Heuwieser, unless stated otherwise below.

| Material | Licence |
|---|---|
| **Software**: the Lean files `lean-core/CorrelationsToGeometry*.lean`, their check scripts, and the Python scripts in `scripts/` | **Apache License, Version 2.0** — full text in `LICENSE-APACHE-2.0`, https://www.apache.org/licenses/LICENSE-2.0 |
| **The paper**: `paper/correlations_to_geometry.tex`, the PDF built from it, and the figures in `paper/figures/` | **Creative Commons Attribution-NonCommercial 4.0 International (CC BY-NC 4.0)** — https://creativecommons.org/licenses/by-nc/4.0/ (the licence of the Zenodo record, doi:10.5281/zenodo.24580848) |
| **`second-session/`**: the `.lean` files there | Apache License, Version 2.0 |
| **`second-session/`**: the `.tex` files and the review notes in `openai-math-review/` (declarations quoted there from github.com/openai/math remain under that project's Apache License 2.0) | CC BY-NC 4.0 (the same licence as the paper) |

Why these two: Apache 2.0 is the licence of Lean's mathematical library Mathlib, so the Lean files can be combined
with it, reused and upstreamed without restriction, and it contains an explicit patent grant; CC BY-NC 4.0 is the
licence under which the paper is published on Zenodo: reuse with attribution for non-commercial purposes. Neither licence limits what the authors
themselves may do with their work later (for example a journal submission or a different licence for a new version).

## Not covered by the licences above

* `lean-core/ports/alpoge-rh/` and `vendor/alpoge-rh/` at the repository root: files from the Lean archive of
  Levent Alpöge, ported with every change recorded in the file headers. **That archive carries no licence**; the files
  are included with attribution, remain the work of their author, and will be removed on request. Nothing in this
  file grants any right in them.
* `vendor/openai-math*` at the repository root (Apache License 2.0 of github.com/openai/math, see the READMEs
  there) and the Mathlib project at the repository root, which belongs to the owner of that repository.

When you use the paper or the Lean files, please cite the paper:
M. Neuberger and C. Heuwieser, *From Correlations to Geometry. A Conditional Spectral Reconstruction*, version 4,
27 November 2026, doi:10.5281/zenodo.24580848.

These licences were chosen on 27 November 2026 and apply to the material named above as published in this repository,
including `second-session/`.
