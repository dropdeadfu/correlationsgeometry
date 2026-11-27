import CorrelationsToGeometryReal3
import CorrelationsToGeometryFunkHecke

/-!
# A129b: the copies in `CTG.FunkHecke` equal the project's `SphereOneDim` objects

`CorrelationsToGeometryFunkHecke.lean` (Mathlib only) contains verbatim copies of `legP`, `sw`,
`sphI`, `sphZ`, `sphE`, `sphS` from `CTG.Reals2.SphereOneDim`. This file imports both and checks
that the copies are equal to the originals.
-/

namespace CTG.FunkHeckeLink

theorem legP_eq : ∀ (n : ℕ) (x : ℝ), CTG.FunkHecke.legP n x = CTG.Reals2.SphereOneDim.legP n x
  | 0, x => by simp [CTG.FunkHecke.legP, CTG.Reals2.SphereOneDim.legP]
  | 1, x => by simp [CTG.FunkHecke.legP, CTG.Reals2.SphereOneDim.legP]
  | n + 2, x => by
      have h1 : CTG.FunkHecke.legP n x = CTG.Reals2.SphereOneDim.legP n x := legP_eq n x
      have h2 : CTG.FunkHecke.legP (n + 1) x = CTG.Reals2.SphereOneDim.legP (n + 1) x :=
        legP_eq (n + 1) x
      rw [CTG.FunkHecke.legP, CTG.Reals2.SphereOneDim.legP, h1, h2]

theorem sw_eq : CTG.FunkHecke.sw = CTG.Reals2.SphereOneDim.sw := rfl

theorem sphI_eq : CTG.FunkHecke.sphI = CTG.Reals2.SphereOneDim.sphI := rfl

theorem sphZ_eq : CTG.FunkHecke.sphZ = CTG.Reals2.SphereOneDim.sphZ := rfl

theorem sphE_eq : CTG.FunkHecke.sphE = CTG.Reals2.SphereOneDim.sphE := rfl

theorem sphS_eq (ξ : ℝ) (l : ℕ) : CTG.FunkHecke.sphS ξ l = CTG.Reals2.SphereOneDim.sphS ξ l := by
  unfold CTG.FunkHecke.sphS CTG.Reals2.SphereOneDim.sphS
  rw [sphE_eq]
  simp only [legP_eq]

end CTG.FunkHeckeLink
