/-
Seventy-third file (A186, written by a subagent of the author-side session, checked by that session; read by nobody
else). Closes two points left open in the header of the seventy-second file (`…FunkHeckeSphereCoord`): every non-polar
point of `S²` is Φ(θ,φ) with 0 < θ < π, and the poles are covered by a rotated chart Ψ = R₀∘Φ. Namespace
`CTG.FunkHecke.SphereCharts`; imports Mathlib and the compiled module of the seventy-second file. Check with
`./check_funk_hecke_sphere_charts.sh` from `lean/`.

Main statements: `cover`, `sphLapS_coord_nonpolar`, `laplacian_comp_isometry` (the Laplacian of ℝ³ is invariant under
linear isometries, no smoothness needed), `sphLap_rotate`, `sphLapS_coord_rot` (coordinate formula in every rotated
chart), `atlas_cover`, `sphLapS_atlas` (at every point of `S²` with `SphC2 f x`, the extrinsic Laplacian equals the
coordinate formula of the round metric in one of the two charts).
NOT shown: an intrinsic Laplace–Beltrami operator (none in Mathlib v4.29); that ΦS, ΨS R₀ are charts in the sense of
Mathlib (homeomorphism, smooth inverse, transition maps); agreement on the overlap as a statement about the transition
map (it follows only because both equal `sphLapS`); uniqueness of (θ,φ). No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSphereCoord

open Real Filter Topology
open scoped RealInnerProductSpace
open Laplacian

namespace CTG.FunkHecke.SphereCharts

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLaplace (ext0 sphLap sphLapS extS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord

/-! ### (1) Coverage of the non-polar points -/

theorem e_apply (i j : Fin 3) : (e i : E3) j = if j = i then 1 else 0 := by
  unfold e; simp [PiLp.single_apply]

theorem Φ_apply (θ φ : ℝ) :
    (Φ θ φ) 0 = sin θ * cos φ ∧ (Φ θ φ) 1 = sin θ * sin φ ∧ (Φ θ φ) 2 = cos θ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Φ, A, e_apply]

theorem norm_sq_E3 (x : E3) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

theorem ext_E3 {x y : E3} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext i; fin_cases i <;> simp [h0, h1, h2]

/-- **Coverage.** A point of `S²` with `x₂² < 1` is `Φ(θ,φ)` with `θ = arccos x₂ ∈ (0,π)` and
`φ = arg (x₀ + i x₁)`. -/
theorem cover (x : E3) (hx : ‖x‖ = 1) (h2 : x 2 ^ 2 < 1) :
    ∃ θ φ : ℝ, 0 < θ ∧ θ < π ∧ x = Φ θ φ := by
  have hn := norm_sq_E3 x
  rw [hx] at hn
  have hlo : -1 < x 2 := by nlinarith
  have hhi : x 2 < 1 := by nlinarith
  set z : ℂ := ⟨x 0, x 1⟩ with hz
  have hzn : ‖z‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hz]; ring
  have hzpos : 0 < ‖z‖ := by
    have : 0 < ‖z‖ ^ 2 := by rw [hzn]; nlinarith
    rcases (norm_nonneg z).lt_or_eq with h | h
    · exact h
    · rw [← h] at this; simp at this
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  refine ⟨arccos (x 2), Complex.arg z, arccos_pos.mpr hhi, arccos_lt_pi.mpr hlo, ?_⟩
  have hc : cos (arccos (x 2)) = x 2 := cos_arccos hlo.le hhi.le
  have hs : sin (arccos (x 2)) = ‖z‖ := by
    rw [sin_arccos, ← sqrt_sq (norm_nonneg z), hzn]
    congr 1; linarith
  obtain ⟨p0, p1, p2⟩ := Φ_apply (arccos (x 2)) (Complex.arg z)
  apply ext_E3
  · rw [p0, hs, Complex.cos_arg hz0]; field_simp; simp [hz]
  · rw [p1, hs, Complex.sin_arg]; field_simp; simp [hz]
  · rw [p2, hc]

/-- `sin θ ≠ 0` on `(0,π)`. -/
theorem sin_ne_zero_of_mem {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π) : sin θ ≠ 0 :=
  (sin_pos_of_pos_of_lt_pi h0 h1).ne'

/-- **Stage 1.** At every non-polar point (`x₂² < 1`) of `S²`, `sphLapS f` equals the coordinate formula of the
round metric in the chart Φ. -/
theorem sphLapS_coord_nonpolar (f : S2 → ℝ) (x : S2) (h2 : (x : E3) 2 ^ 2 < 1) (hF : SphC2 f x) :
    ∃ θ φ : ℝ, x = ΦS θ φ ∧ 0 < θ ∧ θ < π ∧
      sphLapS f x =
        1 / sin θ * deriv (fun a => sin a * deriv (fun b => f (ΦS b φ)) a) θ
          + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΦS θ b)) a) φ := by
  obtain ⟨θ, φ, h0, h1, hx⟩ := cover (x : E3) (mem_sphere_zero_iff_norm.mp x.2) h2
  have hxS : x = ΦS θ φ := Subtype.ext hx
  refine ⟨θ, φ, hxS, h0, h1, ?_⟩
  subst hxS
  exact sphLapS_coord f (sin_ne_zero_of_mem h0 h1) hF

/-! ### (2) Rotation invariance of the Laplacian -/

/-- Second iterated derivative of `G ∘ R` for a linear isometry equivalence (no regularity needed). -/
theorem iteratedFDeriv_two_comp_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E → ℝ) (R : E ≃ₗᵢ[ℝ] E) (y v w : E) :
    iteratedFDeriv ℝ 2 (G ∘ R) y ![v, w] = iteratedFDeriv ℝ 2 G (R y) ![R v, R w] := by
  have h := R.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right G uniqueDiffOn_univ
    (Set.mem_univ (R.toContinuousLinearEquiv y)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  have h' := congrArg (fun T => T ![v, w]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h'
  convert h' using 2
  · ext i; fin_cases i <;> rfl

/-- **Invariance of the Euclidean Laplacian under linear isometries**: `Δ(G ∘ R)(y) = (ΔG)(R y)`, for every
`G` (no regularity assumption). -/
theorem laplacian_comp_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (G : E → ℝ) (R : E ≃ₗᵢ[ℝ] E) (y : E) :
    Δ (G ∘ R) y = Δ G (R y) := by
  set b := stdOrthonormalBasis ℝ E
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (G ∘ R) b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis G (b.map R)]
  simp only [OrthonormalBasis.map_apply, iteratedFDeriv_two_comp_isometry]

theorem ext0_comp_isometry (g : E3 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) : ext0 (g ∘ R) = ext0 g ∘ R := by
  funext y
  simp only [ext0, Function.comp, LinearIsometryEquiv.norm_map, map_smul]

/-- `sphLap (g ∘ R) y = sphLap g (R y)` for every linear isometry `R` of `ℝ³`. -/
theorem sphLap_comp_isometry (g : E3 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) (y : E3) :
    sphLap (g ∘ R) y = sphLap g (R y) := by
  unfold sphLap
  rw [ext0_comp_isometry, laplacian_comp_isometry]

/-- The same in the form asked for: `sphLap (f ∘ R⁻¹) (R x) = sphLap f x`. -/
theorem sphLap_rotate (f : E3 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) (x : E3) :
    sphLap (f ∘ R.symm) (R x) = sphLap f x := by
  have h := sphLap_comp_isometry (f ∘ R.symm) R x
  have hc : (f ∘ R.symm) ∘ R = f := by funext y; simp
  rw [hc] at h; exact h.symm

/-! ### (3) The rotated chart -/

theorem norm_RΦ (R : E3 ≃ₗᵢ[ℝ] E3) (θ φ : ℝ) : ‖R (Φ θ φ)‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, norm_Φ]

/-- The chart `Ψ_R = R ∘ Φ` as a map into `S2`. -/
noncomputable def ΨS (R : E3 ≃ₗᵢ[ℝ] E3) (θ φ : ℝ) : S2 :=
  ⟨R (Φ θ φ), mem_sphere_zero_iff_norm.mpr (norm_RΦ R θ φ)⟩

theorem extS_RΦ (f : S2 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) (a b : ℝ) :
    (extS f ∘ R) (Φ a b) = f (ΨS R a b) := by
  simp only [Function.comp]
  unfold extS; rw [dif_pos (mem_sphere_zero_iff_norm.mpr (norm_RΦ R a b))]; rfl

/-- **Coordinate formula in the rotated chart.** For a linear isometry `R`, `sin θ ≠ 0` and `SphC2 f` at
`Ψ_R(θ,φ)`, `sphLapS f (Ψ_R(θ,φ))` is the coordinate formula of the round metric for `u = f ∘ Ψ_R`. -/
theorem sphLapS_coord_rot (f : S2 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) {θ φ : ℝ} (hs : sin θ ≠ 0)
    (hF : SphC2 f (ΨS R θ φ)) :
    sphLapS f (ΨS R θ φ) =
      1 / sin θ * deriv (fun a => sin a * deriv (fun b => f (ΨS R b φ)) a) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΨS R θ b)) a) φ := by
  unfold sphLapS
  rw [show ((ΨS R θ φ : S2) : E3) = R (Φ θ φ) from rfl, ← sphLap_comp_isometry]
  have hF' : ContDiffAt ℝ 2 (ext0 (extS f ∘ R)) (Φ θ φ) := by
    rw [ext0_comp_isometry]
    have h1 : ContDiffAt ℝ 2 (ext0 (extS f)) (R (Φ θ φ)) := hF
    exact h1.comp (Φ θ φ) (R.toContinuousLinearEquiv.contDiff.contDiffAt)
  rw [sphLap_coord (extS f ∘ R) hs hF']
  simp only [extS_RΦ]

/-! ### (4) A concrete rotation and the atlas -/

/-- The rotation `R₀`: `e₀ ↦ e₀`, `e₁ ↦ −e₂`, `e₂ ↦ e₁` (the moving frame at `θ = π/2`, `φ = 0`). -/
noncomputable def R0 : E3 ≃ₗᵢ[ℝ] E3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).equiv (frameONB (π / 2) 0) (Equiv.refl _)

theorem R0_e2 : R0 (e 2) = e 1 := by
  have h := OrthonormalBasis.equiv_apply_basis (EuclideanSpace.basisFun (Fin 3) ℝ)
    (frameONB (π / 2) 0) (Equiv.refl _) 2
  rw [EuclideanSpace.basisFun_apply] at h
  unfold R0; rw [show e 2 = EuclideanSpace.single 2 (1 : ℝ) from rfl, h, frameONB_apply]
  simp [frame, B]

theorem coord_eq_inner (x : E3) (i : Fin 3) : x i = ⟪e i, x⟫ := by
  unfold e
  first
    | (have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) x
       simp only [map_one, one_mul] at h
       exact h.symm)
    | (fin_cases i <;> simp [PiLp.inner_apply, PiLp.single_apply, Fin.sum_univ_three])

/-- The third coordinate of `R₀⁻¹ x` is `x₁`. -/
theorem R0_symm_2 (x : E3) : (R0.symm x) 2 = x 1 := by
  rw [coord_eq_inner, coord_eq_inner x 1, ← R0_e2, ← LinearIsometryEquiv.inner_map_map R0,
    LinearIsometryEquiv.apply_symm_apply]

/-- **Atlas.** Every point of `S²` lies in the image of `Φ` or of `Ψ_{R₀}` with `0 < θ < π`. -/
theorem atlas_cover (x : S2) :
    (∃ θ φ : ℝ, 0 < θ ∧ θ < π ∧ x = ΦS θ φ) ∨ (∃ θ φ : ℝ, 0 < θ ∧ θ < π ∧ x = ΨS R0 θ φ) := by
  have hx : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  by_cases h2 : (x : E3) 2 ^ 2 < 1
  · obtain ⟨θ, φ, h0, h1, h⟩ := cover (x : E3) hx h2
    exact Or.inl ⟨θ, φ, h0, h1, Subtype.ext h⟩
  · right
    have hn := norm_sq_E3 (x : E3)
    rw [hx] at hn
    have hy : ‖R0.symm (x : E3)‖ = 1 := by rw [LinearIsometryEquiv.norm_map, hx]
    have hy2 : (R0.symm (x : E3)) 2 ^ 2 < 1 := by
      rw [R0_symm_2]; push Not at h2; nlinarith [sq_nonneg ((x : E3) 0), sq_nonneg ((x : E3) 1)]
    obtain ⟨θ, φ, h0, h1, h⟩ := cover _ hy hy2
    refine ⟨θ, φ, h0, h1, Subtype.ext ?_⟩
    show (x : E3) = R0 (Φ θ φ)
    rw [← h, LinearIsometryEquiv.apply_symm_apply]

/-- **Main statement (two charts).** For every `x ∈ S²` with `SphC2 f x`: either `x = Φ(θ,φ)` with `0<θ<π` and
`sphLapS f x` equals the coordinate formula for `u = f ∘ Φ`, or `x = Ψ_{R₀}(θ,φ)` with `0<θ<π` and `sphLapS f x`
equals the coordinate formula for `u = f ∘ Ψ_{R₀}`. -/
theorem sphLapS_atlas (f : S2 → ℝ) (x : S2) (hF : SphC2 f x) :
    (∃ θ φ : ℝ, 0 < θ ∧ θ < π ∧ x = ΦS θ φ ∧
      sphLapS f x =
        1 / sin θ * deriv (fun a => sin a * deriv (fun b => f (ΦS b φ)) a) θ
          + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΦS θ b)) a) φ) ∨
    (∃ θ φ : ℝ, 0 < θ ∧ θ < π ∧ x = ΨS R0 θ φ ∧
      sphLapS f x =
        1 / sin θ * deriv (fun a => sin a * deriv (fun b => f (ΨS R0 b φ)) a) θ
          + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΨS R0 θ b)) a) φ) := by
  rcases atlas_cover x with ⟨θ, φ, h0, h1, rfl⟩ | ⟨θ, φ, h0, h1, rfl⟩
  · exact Or.inl ⟨θ, φ, h0, h1, rfl, sphLapS_coord f (sin_ne_zero_of_mem h0 h1) hF⟩
  · exact Or.inr ⟨θ, φ, h0, h1, rfl, sphLapS_coord_rot f R0 (sin_ne_zero_of_mem h0 h1) hF⟩

end CTG.FunkHecke.SphereCharts

#print axioms CTG.FunkHecke.SphereCharts.sphLapS_coord_nonpolar
#print axioms CTG.FunkHecke.SphereCharts.laplacian_comp_isometry
#print axioms CTG.FunkHecke.SphereCharts.sphLap_rotate
#print axioms CTG.FunkHecke.SphereCharts.sphLapS_coord_rot
#print axioms CTG.FunkHecke.SphereCharts.sphLapS_atlas
