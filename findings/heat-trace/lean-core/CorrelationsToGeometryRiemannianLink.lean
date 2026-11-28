/-
Eighty-third Lean file (after version 4). Link of the chart-independent Laplace–Beltrami operator `lapM` of
`CorrelationsToGeometryLaplaceBeltramiManifold` with Mathlib's Riemannian metrics. Written by a subagent of the
author-side session (task A196), checked here.

For a C² manifold `M` modelled on `Fin n → ℝ` and a `ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n) (TangentSpace …)`
of Mathlib v4.29: `coordOf` (coordinate expression of the metric in a chart), `coordOf_compat`, `coordOf_symm`,
`coordOf_pos`, `coordOf_det`, `diffAtCenters_of_contMDiff` (differentiability of the coordinate expressions from the
C¹ property in the bundle sense), `ofRiemannian : CoordMetric n M` (no field left as a hypothesis),
`lapRiem gR u x := lapM (ofRiemannian gR) u x`, `lapRiem_eq_chart`, `lapRiem_eq_coordExpr` (the coordinate
formula in every chart of the maximal C² atlas), `stdRiem`, `lapRiem_std_laplacian` (flat case: Mathlib's Laplacian).

NOT shown: the type classes `RiemannianBundle`, `IsContMDiffRiemannianBundle`, `IsRiemannianManifold` are not
connected (only the structure `ContMDiffRiemannianMetric`); only the model `Fin n → ℝ`, without boundary; metric C¹,
manifold C²; `lapRiem` is a pointwise formula (u of class C² in a chart), not an operator on a function space.
No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryLaplaceBeltramiManifold

open Bundle Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace CTG.RiemannianLink

open CTG.LaplaceBeltrami CTG.LaplaceBeltramiManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (E n) M]

/-! ### Linear algebra -/

/-- A positive definite bilinear form has invertible Gram matrix. -/
theorem det_ne_of_pos {B : Bil n} (h : ∀ v, v ≠ 0 → 0 < B v v) : (mat B).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have := h v hv
  rw [bil_expand, hBv, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- Differentiability of a pulled-back metric field. -/
theorem pullback_differentiableAt {ψ : E n → E n} {G : E n → Bil n} {y : E n}
    (hψd : DifferentiableAt ℝ ψ y) (hJd : DifferentiableAt ℝ (fderiv ℝ ψ) y)
    (hGd : DifferentiableAt ℝ G (ψ y)) : DifferentiableAt ℝ (pullback ψ G) y := by
  have hpb : pullback ψ G = fun z => ((ContinuousLinearMap.compL ℝ (E n) (E n) ℝ).flip (fderiv ℝ ψ z)).comp
      ((G (ψ z)).comp (fderiv ℝ ψ z)) := by
    funext z; ext a b; rfl
  have hr := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E n →L[ℝ] E n)
    (F := (E n →L[ℝ] ℝ) →L[ℝ] (E n →L[ℝ] ℝ)) (x := fderiv ℝ ψ y)
    ((ContinuousLinearMap.compL ℝ (E n) (E n) ℝ).flip)
  have h1 := HasFDerivAt.comp (𝕜 := ℝ) (E := E n) (F := E n →L[ℝ] E n)
    (G := (E n →L[ℝ] ℝ) →L[ℝ] (E n →L[ℝ] ℝ)) y hr hJd.hasFDerivAt
  have h2 := HasFDerivAt.comp (𝕜 := ℝ) (E := E n) (F := E n) (G := Bil n) y
    hGd.hasFDerivAt hψd.hasFDerivAt
  have h3 := HasFDerivAt.clm_comp (𝕜 := ℝ) (E := E n) (F := E n) (G := E n) (H := E n →L[ℝ] ℝ) h2
    hJd.hasFDerivAt
  have h4 := HasFDerivAt.clm_comp (𝕜 := ℝ) (E := E n) (F := E n) (G := E n →L[ℝ] ℝ) (H := E n →L[ℝ] ℝ)
    h1 h3
  exact h4.differentiableAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by rw [hpb]; rfl)

/-! ### Transition maps: injective derivative -/

theorem trans_injective [IsManifold 𝓘(ℝ, E n) 2 M] {e e' : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M)
    {y : E n} (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    Function.Injective (fderiv ℝ (e' ∘ e.symm) y) := by
  set ψ := e' ∘ e.symm
  set φ := e ∘ e'.symm
  have hψy : ψ y ∈ e'.target := e'.map_source hy'
  have hφ' : e'.symm (ψ y) ∈ e.source := by
    simp only [ψ, Function.comp_apply, e'.left_inv hy']; exact e.map_target hy
  have hψd : DifferentiableAt ℝ ψ y := (trans_contDiffAt he he' hy hy').differentiableAt (by norm_num)
  have hφd : DifferentiableAt ℝ φ (ψ y) :=
    (trans_contDiffAt he' he hψy hφ').differentiableAt (by norm_num)
  have hid : φ ∘ ψ =ᶠ[𝓝 y] id := by
    filter_upwards [overlap_mem_nhds hy hy'] with z hz
    simp only [φ, ψ, Function.comp_apply, e'.left_inv hz.2, e.right_inv hz.1, id]
  have h := fderiv_comp y hφd hψd
  rw [hid.fderiv_eq, fderiv_id] at h
  intro a b hab
  have := congrArg (fderiv ℝ φ (ψ y)) hab
  rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ← h] at this
  simpa using this

/-! ### Stage 1: coordinate expression of a family of bilinear forms on the tangent spaces -/

/-- Coordinate expression of a family `g x` of bilinear forms on the tangent spaces `T_x M` (which are, by definition,
`E n`, the coordinate vectors in the preferred chart at `x`) in an arbitrary chart `e`:
`G_e(y)(v,w) = g_{e⁻¹ y}(D(e⁻¹)_y v, D(e⁻¹)_y w)`, with Mathlib's manifold derivative `mfderiv`. -/
def coordOf (g : ∀ x : M, TangentSpace 𝓘(ℝ, E n) x →L[ℝ] TangentSpace 𝓘(ℝ, E n) x →L[ℝ] ℝ)
    (e : OpenPartialHomeomorph M (E n)) (y : E n) : Bil n :=
  let D : E n →L[ℝ] E n := mfderiv 𝓘(ℝ, E n) 𝓘(ℝ, E n) e.symm y
  let B : Bil n := g (e.symm y)
  B.bilinearComp D D


section Stage2
variable [IsManifold 𝓘(ℝ, E n) 2 M]

/-- Mathlib's manifold derivative of the inverse of a chart, written in the preferred chart at the image point. -/
theorem mfderiv_symm_eq {e : OpenPartialHomeomorph M (E n)} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M)
    {y : E n} (hy : y ∈ e.target) :
    mfderiv 𝓘(ℝ, E n) 𝓘(ℝ, E n) e.symm y = fderiv ℝ (chartAt (E n) (e.symm y) ∘ e.symm) y := by
  have h := (contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by norm_num)
  rw [h.mfderiv]
  simp [writtenInExtChartAt, fderivWithin_univ]

variable (g : ∀ x : M, TangentSpace 𝓘(ℝ, E n) x →L[ℝ] TangentSpace 𝓘(ℝ, E n) x →L[ℝ] ℝ)

/-- The coordinate expression as a pull-back of the constant form `g (e⁻¹ y)` by the transition map. -/
theorem coordOf_eq {e : OpenPartialHomeomorph M (E n)} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M)
    {y : E n} (hy : y ∈ e.target) :
    coordOf g e y = pullback (chartAt (E n) (e.symm y) ∘ e.symm) (fun _ => (g (e.symm y) : Bil n)) y := by
  unfold coordOf pullback
  rw [mfderiv_symm_eq he hy]

/-- **Compatibility** (chain rule for the change of charts): `G_{e'} = (e ∘ e'⁻¹)* G_e` on the overlap. -/
theorem coordOf_compat {e e' : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M)
    {y : E n} (hy : y ∈ e'.target) (hys : e'.symm y ∈ e.source) :
    coordOf g e' y = pullback (e ∘ e'.symm) (coordOf g e) y := by
  set z := e'.symm y with hzdef
  set c := chartAt (E n) z
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M := IsManifold.chart_mem_maximalAtlas z
  have hw : (e ∘ e'.symm) y ∈ e.target := e.map_source hys
  have hwz : e.symm ((e ∘ e'.symm) y) = z := by
    simp only [Function.comp_apply, e.left_inv hys, z]
  have hwc : e.symm ((e ∘ e'.symm) y) ∈ c.source := by rw [hwz]; exact mem_chart_source (E n) z
  have h1 : coordOf g e ((e ∘ e'.symm) y) =
      pullback (c ∘ e.symm) (fun _ => (g z : Bil n)) ((e ∘ e'.symm) y) := by
    rw [coordOf_eq g he hw, hwz]
  rw [coordOf_eq g he' hy, pullback_congr_point h1,
    ← pullback_comp ((trans_contDiffAt he hc hw hwc).differentiableAt (by norm_num))
      ((trans_contDiffAt he' he hy hys).differentiableAt (by norm_num))]
  apply pullback_congr_fun
  filter_upwards [overlap_mem_nhds hy hys] with w hw'
  simp only [Function.comp_apply, e.left_inv hw'.2]
  try rfl

/-- **Symmetry.** -/
theorem coordOf_symm (hs : ∀ x v w, g x v w = g x w v) (e : OpenPartialHomeomorph M (E n)) (y v w : E n) :
    coordOf g e y v w = coordOf g e y w v := by
  simp only [coordOf, ContinuousLinearMap.bilinearComp_apply]
  exact hs _ _ _

/-- **Positive definiteness.** -/
theorem coordOf_pos (hp : ∀ x v, v ≠ 0 → 0 < g x v v) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {y : E n} (hy : y ∈ e.target) (v : E n) (hv : v ≠ 0) :
    0 < coordOf g e y v v := by
  rw [coordOf_eq g he hy]
  simp only [pullback, ContinuousLinearMap.bilinearComp_apply]
  apply hp
  intro h0
  have hinj := trans_injective he (IsManifold.chart_mem_maximalAtlas (e.symm y)) hy
    (mem_chart_source (E n) (e.symm y))
  exact hv (hinj (h0.trans (map_zero _).symm))

/-- **Nondegeneracy.** -/
theorem coordOf_det (hp : ∀ x v, v ≠ 0 → 0 < g x v v) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {y : E n} (hy : y ∈ e.target) :
    (mat (coordOf g e y)).det ≠ 0 :=
  det_ne_of_pos fun v hv => coordOf_pos g hp he hy v hv

/-- Regularity condition at the centres of the preferred charts: the coordinate expression in the preferred chart at
`x` is differentiable at `chartAt x x`. -/
def DiffAtCenters : Prop :=
  ∀ x : M, DifferentiableAt ℝ (coordOf g (chartAt (E n) x)) (chartAt (E n) x x)

/-- **Differentiability** in every chart of the maximal atlas, from differentiability at the chart centres. -/
theorem coordOf_diff (hg : DiffAtCenters g) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {y : E n} (hy : y ∈ e.target) :
    DifferentiableAt ℝ (coordOf g e) y := by
  set z := e.symm y
  set c := chartAt (E n) z
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M := IsManifold.chart_mem_maximalAtlas z
  have hzc : z ∈ c.source := mem_chart_source (E n) z
  have hev : coordOf g e =ᶠ[𝓝 y] pullback (c ∘ e.symm) (coordOf g c) := by
    filter_upwards [overlap_mem_nhds hy hzc] with w hw
    exact coordOf_compat g hc he hw.1 hw.2
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hψ := trans_contDiffAt he hc hy hzc
  refine pullback_differentiableAt (hψ.differentiableAt (by norm_num))
    ((hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)) ?_
  exact hg z

/-! ### Stage 3: the `CoordMetric` and the Laplace–Beltrami operator -/

/-- A symmetric, positive definite family of forms on the tangent spaces, differentiable at the chart centres, is a
`CoordMetric`. -/
def toCoordMetric (hs : ∀ x v w, g x v w = g x w v) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hd : DiffAtCenters g) : CoordMetric n M where
  G := coordOf g
  diff e he y hy := coordOf_diff g hd (IsManifold.subset_maximalAtlas he) hy
  symm e _ y _ v w := coordOf_symm g hs e y v w
  pos e he y hy v hv := coordOf_pos g hp (IsManifold.subset_maximalAtlas he) hy v hv
  det e he y hy := coordOf_det g hp (IsManifold.subset_maximalAtlas he) hy
  compat e he e' he' y hy hys :=
    coordOf_compat g (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he') hy hys

/-- In every chart of the maximal `C²` atlas, the chart-independent operator is the coordinate operator of the
coordinate expression `coordOf g e`. -/
theorem lapM_toCoordMetric (hs : ∀ x v w, g x v w = g x w v) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hd : DiffAtCenters g) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {x : M} (hx : x ∈ e.source) {u : M → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapM (toCoordMetric g hs hp hd) u x = lapB (coordOf g e) (u ∘ e.symm) (e x) := by
  rw [lapM_eq_coordExpr _ he hx hu]
  refine lapB_congr ?_ EventuallyEq.rfl
  filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
  exact (coordOf_compat g (IsManifold.chart_mem_maximalAtlas (e.symm y)) he hy
    (mem_chart_source (E n) (e.symm y))).symm

end Stage2

section Flat

/-- The standard form on every tangent space of the model space. -/
def stdField (n : ℕ) : ∀ x : E n, TangentSpace 𝓘(ℝ, E n) x →L[ℝ] TangentSpace 𝓘(ℝ, E n) x →L[ℝ] ℝ :=
  fun _ => stdBil n

theorem std_symm (v w : E n) : stdBil n v w = stdBil n w v := by
  simp only [stdBil_apply, mul_comm]

theorem std_pos (v : E n) (hv : v ≠ 0) : 0 < stdBil n v v := by
  rw [stdBil_apply]
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  calc (0 : ℝ) < v k * v k := mul_self_pos.2 hk
    _ ≤ ∑ j, v j * v j :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)

theorem stdField_symm : ∀ (x : E n) (v w : TangentSpace 𝓘(ℝ, E n) x), stdField n x v w = stdField n x w v :=
  fun _ v w => std_symm v w

theorem stdField_pos : ∀ (x : E n) (v : TangentSpace 𝓘(ℝ, E n) x), v ≠ 0 → 0 < stdField n x v v :=
  fun _ v hv => std_pos v hv

theorem mfderiv_refl_symm (y : E n) :
    mfderiv 𝓘(ℝ, E n) 𝓘(ℝ, E n) (OpenPartialHomeomorph.refl (E n)).symm y =
      ContinuousLinearMap.id ℝ (E n) := by
  have : ((OpenPartialHomeomorph.refl (E n)).symm : E n → E n) = id := by funext z; simp
  rw [this, mfderiv_id]; rfl

theorem coordOf_std (x : E n) : coordOf (stdField n) (chartAt (E n) x) = fun _ => stdBil n := by
  funext y
  rw [chartAt_self_eq]
  ext a b
  simp only [coordOf, mfderiv_refl_symm, ContinuousLinearMap.bilinearComp_apply]
  rfl

theorem stdField_diff : DiffAtCenters (stdField n) := fun x => by
  rw [coordOf_std]; exact differentiableAt_const _

/-- **Flat consistency.** The metric of `Fin n → ℝ` given on its tangent spaces by the standard form yields Mathlib's
Laplacian (transported to `EuclideanSpace`), for `u` of class C². -/
theorem lapM_std_laplacian {u : E n → ℝ} (hu : ContDiff ℝ 2 u) (x : E n) :
    lapM (toCoordMetric (stdField n) stdField_symm stdField_pos stdField_diff) u x =
      Laplacian.laplacian (u ∘ (EuclideanSpace.equiv (Fin n) ℝ))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x) := by
  rw [← lapM_flat_laplacian hu x]
  unfold lapM
  show lapB (coordOf (stdField n) (chartAt (E n) x)) _ _ = lapB (fun _ => stdBil n) _ _
  rw [coordOf_std]

end Flat

section Bundle
variable [IsManifold 𝓘(ℝ, E n) 2 M]

/-- The fibre derivative of the tangent bundle trivialization at `x₀`, read in charts. -/
theorem tcc_eq (x₀ z : M) :
    tangentCoordChange 𝓘(ℝ, E n) x₀ z z =
      fderiv ℝ (chartAt (E n) z ∘ (chartAt (E n) x₀).symm) (chartAt (E n) x₀ z) := by
  simp [fderivWithin_univ]

/-- A Riemannian metric in Mathlib's sense on the tangent bundle, read in the trivialization of the bundle of bilinear
forms at `x₀`. -/
theorem triv_apply (g : ∀ x : M, TangentSpace 𝓘(ℝ, E n) x →L[ℝ] TangentSpace 𝓘(ℝ, E n) x →L[ℝ] ℝ)
    (x₀ z : M) (hz : z ∈ (chartAt (E n) x₀).source) (v w : E n) :
    ((trivializationAt (Bil n) (fun x : M => TangentSpace 𝓘(ℝ, E n) x →L[ℝ] TangentSpace 𝓘(ℝ, E n) x →L[ℝ] ℝ) x₀
      ⟨z, g z⟩).2 : Bil n) v w =
    g z (tangentCoordChange 𝓘(ℝ, E n) x₀ z z v) (tangentCoordChange 𝓘(ℝ, E n) x₀ z z w) := by
  have hs : ∀ u : E n, (trivializationAt (E n) (TangentSpace 𝓘(ℝ, E n)) x₀).symm z u =
      tangentCoordChange 𝓘(ℝ, E n) x₀ z z u := fun u => by
    exact DFunLike.congr_fun (TangentBundle.symmL_trivializationAt_eq_core hz) u
  rw [hom_trivializationAt_apply]
  dsimp only
  rw [inCoordinates_apply_eq₂ (by simpa using hz) (by simpa using hz) (by simp)]
  first | (rw [hs, hs]) | (rw [TangentBundle.symmL_trivializationAt_eq_core hz])
  simp [Trivialization.linearMapAt_apply]

/-- **Differentiability from the bundle regularity.** A `C¹` Riemannian metric on the tangent bundle in Mathlib's
sense (`ContMDiffRiemannianMetric`) has coordinate expressions that are differentiable at the chart centres. -/
theorem diffAtCenters_of_contMDiff (gR : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n)
      (fun x : M => TangentSpace 𝓘(ℝ, E n) x)) : DiffAtCenters gR.inner := by
  intro x₀
  set c := chartAt (E n) x₀
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M := IsManifold.chart_mem_maximalAtlas x₀
  have hx₀ : x₀ ∈ c.source := mem_chart_source (E n) x₀
  have hct : c x₀ ∈ c.target := c.map_source hx₀
  have h0 := (contMDiffAt_section x₀).1 (gR.contMDiff x₀)
  have h1 := ContMDiffAt.comp (c x₀) (by rw [c.left_inv hx₀]; exact h0)
    ((contMDiffAt_symm_of_mem_maximalAtlas hc hct).of_le (by norm_num))
  have h2 := (contMDiffAt_iff_contDiffAt.1 h1).differentiableAt (by norm_num)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [c.open_target.mem_nhds hct] with y hy
  ext v w
  have hz : c.symm y ∈ c.source := c.map_target hy
  refine Eq.trans ?_ (triv_apply gR.inner x₀ _ hz v w).symm
  rw [tcc_eq, c.right_inv hy]
  simp only [coordOf, ContinuousLinearMap.bilinearComp_apply, mfderiv_symm_eq hc hy]
  try rfl

/-- **A `C¹` Riemannian metric in Mathlib's sense is a `CoordMetric`**, with coordinate expressions
`G_e(y) = g_{e⁻¹y}(D(e⁻¹)_y ·, D(e⁻¹)_y ·)`. No hypothesis beyond `IsManifold 𝓘(ℝ, Fin n → ℝ) 2 M`. -/
def ofRiemannian (gR : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n)
    (fun x : M => TangentSpace 𝓘(ℝ, E n) x)) : CoordMetric n M :=
  toCoordMetric gR.inner gR.symm gR.pos (diffAtCenters_of_contMDiff gR)

/-- **Laplace–Beltrami operator of a Mathlib Riemannian metric.** -/
def lapRiem (gR : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n) (fun x : M => TangentSpace 𝓘(ℝ, E n) x))
    (u : M → ℝ) (x : M) : ℝ :=
  lapM (ofRiemannian gR) u x

/-- In every chart `e` of the maximal `C²` atlas with `x ∈ e.source` and `u ∘ e⁻¹` C² at `e x`, `lapRiem` is the
coordinate operator `lapB` of the coordinate expression `coordOf gR.inner e`. -/
theorem lapRiem_eq_chart (gR : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n)
      (fun x : M => TangentSpace 𝓘(ℝ, E n) x)) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {x : M} (hx : x ∈ e.source) {u : M → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapRiem gR u x = lapB (coordOf gR.inner e) (u ∘ e.symm) (e x) :=
  lapM_toCoordMetric _ _ _ _ he hx hu

/-- The same, with the canonical coordinate expression `coordExpr` of `CorrelationsToGeometryLaplaceBeltramiManifold`. -/
theorem lapRiem_eq_coordExpr (gR : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n)
      (fun x : M => TangentSpace 𝓘(ℝ, E n) x)) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {x : M} (hx : x ∈ e.source) {u : M → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapRiem gR u x = lapB (coordExpr (ofRiemannian gR) e) (u ∘ e.symm) (e x) :=
  lapM_eq_coordExpr _ he hx hu

end Bundle

section FlatBundle

/-- The standard metric of `Fin n → ℝ` as a Mathlib `ContMDiffRiemannianMetric` on its tangent bundle (Mathlib's
`riemannianMetricVectorSpace` needs an inner product space; `Fin n → ℝ` carries the sup norm). -/
def stdRiem (n : ℕ) : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n) (fun x : E n => TangentSpace 𝓘(ℝ, E n) x) where
  inner := stdField n
  symm := stdField_symm
  pos := stdField_pos
  isVonNBounded x := by
    have key : ∀ u : E n, ∑ k, u k * u k < 1 → u ∈ Metric.ball (0 : E n) 1 := by
      intro u hu
      rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
      intro k
      have hk : u k * u k ≤ ∑ j, u j * u j :=
        Finset.single_le_sum (f := fun j => u j * u j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
      rw [Real.norm_eq_abs, ← sq_lt_one_iff_abs_lt_one, pow_two]
      linarith
    refine (NormedSpace.isVonNBounded_ball ℝ (E n) 1).subset fun v hv => ?_
    have hv' : stdBil n v v < 1 := hv
    rw [stdBil_apply] at hv'
    exact key v hv'
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    refine (contMDiffAt_const (c := stdBil n)).congr_of_eventuallyEq ?_
    filter_upwards with z
    ext v w
    rw [triv_apply (stdField n) x z (by simp)]
    first | (simp [stdField]; done) | (simp [stdField]; rfl)

/-- **Flat consistency for the Mathlib metric.** -/
theorem lapRiem_std_laplacian {u : E n → ℝ} (hu : ContDiff ℝ 2 u) (x : E n) :
    lapRiem (stdRiem n) u x =
      Laplacian.laplacian (u ∘ (EuclideanSpace.equiv (Fin n) ℝ))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x) :=
  lapM_std_laplacian hu x

end FlatBundle


end CTG.RiemannianLink

