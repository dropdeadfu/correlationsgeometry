/-
Seventy-ninth Lean file (after version 4). A chart-independent Laplace–Beltrami operator on a C² manifold `M` with
model `Fin n → ℝ`, built from the coordinate operator `lapB` of `CorrelationsToGeometryLaplaceBeltrami`.
Written by a subagent of the author-side session (task A191), checked here.

`CoordMetric n M`: a metric given by its coordinate expressions `G e` in the charts of the atlas (differentiable,
symmetric, positive definite, det ≠ 0 on the target) with the compatibility `G e' = pullback (e ∘ e'.symm) (G e)`
on overlaps. This is NOT Mathlib's `RiemannianBundle`. `lapM g u x := lapB (G (chartAt x)) (u ∘ (chartAt x).symm)
(chartAt x x)`. `lapM_eq_chart` (same value in every chart of the atlas), `lapM_eq_pullback`, `lapM_eq_coordExpr`
(in every chart of the maximal C² atlas, with the pulled-back coordinate expression), `lapB_chart_indep`,
`lapM_flat_laplacian` (flat metric on `Fin n → ℝ`: Mathlib's Laplacian, for u of class C² globally).

NOT shown: that a Mathlib `RiemannianBundle` yields a `CoordMetric`; a manifold structure on S² with the round
metric as a `CoordMetric` (no link to `CTG.LBSphere`); `ContMDiff` regularity of u (the hypothesis is pointwise, in
a chart); an operator on function spaces; positive definiteness is a field of the structure and used in no proof.
No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryLaplaceBeltrami

open Filter Topology Set
open scoped Manifold

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace CTG.LaplaceBeltramiManifold

open CTG.LaplaceBeltrami

variable {n : ℕ}

/-! ### Local analytic lemmas -/

theorem lapB_congr {G H : E n → Bil n} {u v : E n → ℝ} {x : E n}
    (hG : G =ᶠ[𝓝 x] H) (hu : u =ᶠ[𝓝 x] v) : lapB G u x = lapB H v x := by
  unfold lapB; rw [hG.eq_of_nhds, hG.fderiv_eq, hu.fderiv_eq, hu.fderiv.fderiv_eq]

theorem amat_eq (J : E n →L[ℝ] E n) : amat J = LinearMap.toMatrix' (J : E n →ₗ[ℝ] E n) := by
  ext i j; simp [amat, LinearMap.toMatrix'_apply, ev]

theorem amat_det_ne_of_comp {A B : E n →L[ℝ] E n} (h : A.comp B = ContinuousLinearMap.id ℝ (E n)) :
    (amat B).det ≠ 0 := by
  have h1 : amat A * amat B = 1 := by
    rw [amat_eq, amat_eq, ← LinearMap.toMatrix'_comp]
    have : (A : E n →ₗ[ℝ] E n) ∘ₗ (B : E n →ₗ[ℝ] E n) = LinearMap.id := by
      ext v; simp [← ContinuousLinearMap.comp_apply, h]
    rw [this, LinearMap.toMatrix'_id]
  intro h0
  have := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

/-! ### Transition maps of the maximal atlas -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (E n) M]

theorem trans_contDiffOn [IsManifold 𝓘(ℝ, E n) 2 M] {e e' : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) :
    ContDiffOn ℝ 2 (e' ∘ e.symm) (e.target ∩ e.symm ⁻¹' e'.source) := by
  have h := (IsManifold.compatible_of_mem_maximalAtlas he he').1
  simpa [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    OpenPartialHomeomorph.trans_source] using h


/-- Smoothness of a transition map at a point of the overlap. -/
theorem trans_contDiffAt [IsManifold 𝓘(ℝ, E n) 2 M] {e e' : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M)
    {y : E n} (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    ContDiffAt ℝ 2 (e' ∘ e.symm) y :=
  (trans_contDiffOn he he').contDiffAt
    ((e.isOpen_inter_preimage_symm e'.open_source).mem_nhds ⟨hy, hy'⟩)

/-- The overlap is a neighbourhood. -/
theorem overlap_mem_nhds {e e' : OpenPartialHomeomorph M (E n)} {y : E n} (hy : y ∈ e.target)
    (hy' : e.symm y ∈ e'.source) : e.target ∩ e.symm ⁻¹' e'.source ∈ 𝓝 y :=
  (e.isOpen_inter_preimage_symm e'.open_source).mem_nhds ⟨hy, hy'⟩

/-- Transition maps have invertible derivative. -/
theorem trans_det [IsManifold 𝓘(ℝ, E n) 2 M] {e e' : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M)
    {y : E n} (hy : y ∈ e.target) (hy' : e.symm y ∈ e'.source) :
    (amat (fderiv ℝ (e' ∘ e.symm) y)).det ≠ 0 := by
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
  exact amat_det_ne_of_comp h.symm

/-! ### Metrics given in the charts of the atlas -/

variable (n M) in
/-- A (Riemannian) metric on `M`, given by its coordinate expression `G e` in every chart `e` of the atlas, regular in
every chart and compatible on overlaps: `G e' = (e ∘ e'⁻¹)* G e`. -/
structure CoordMetric where
  /-- Coordinate expression of the metric in the chart `e`. -/
  G : OpenPartialHomeomorph M (E n) → E n → Bil n
  diff : ∀ e ∈ atlas (E n) M, ∀ y ∈ e.target, DifferentiableAt ℝ (G e) y
  symm : ∀ e ∈ atlas (E n) M, ∀ y ∈ e.target, ∀ v w, G e y v w = G e y w v
  pos : ∀ e ∈ atlas (E n) M, ∀ y ∈ e.target, ∀ v, v ≠ 0 → 0 < G e y v v
  det : ∀ e ∈ atlas (E n) M, ∀ y ∈ e.target, (mat (G e y)).det ≠ 0
  compat : ∀ e ∈ atlas (E n) M, ∀ e' ∈ atlas (E n) M, ∀ y ∈ e'.target, e'.symm y ∈ e.source →
    G e' y = pullback (e ∘ e'.symm) (G e) y

/-- **The Laplace–Beltrami operator on `M`**: the coordinate operator `lapB` in the preferred chart at `x`. -/
def lapM (g : CoordMetric n M) (u : M → ℝ) (x : M) : ℝ :=
  lapB (g.G (chartAt (E n) x)) (u ∘ (chartAt (E n) x).symm) (chartAt (E n) x x)

/-- **Chart independence, maximal atlas.** For every chart `e` of the maximal `C²` atlas with `x ∈ e.source` and
`u ∘ e⁻¹` C² at `e x`, `lapM g u x` is the coordinate operator in `e` of the metric expression
`(chartAt x ∘ e⁻¹)* G_{chartAt x}`. -/
theorem lapM_eq_pullback [IsManifold 𝓘(ℝ, E n) 2 M] (g : CoordMetric n M) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {x : M} (hx : x ∈ e.source) {u : M → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapM g u x = lapB (pullback (chartAt (E n) x ∘ e.symm) (g.G (chartAt (E n) x))) (u ∘ e.symm) (e x) := by
  set c := chartAt (E n) x
  have hcA : c ∈ atlas (E n) M := chart_mem_atlas (E n) x
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M := IsManifold.chart_mem_maximalAtlas x
  have hxc : x ∈ c.source := mem_chart_source (E n) x
  have hy : e x ∈ e.target := e.map_source hx
  have hy' : e.symm (e x) ∈ c.source := by rw [e.left_inv hx]; exact hxc
  set ψ := c ∘ e.symm
  have hψy : ψ (e x) = c x := by simp only [ψ, Function.comp_apply, e.left_inv hx]
  have hψ : ContDiffAt ℝ 2 ψ (e x) := trans_contDiffAt he hc hy hy'
  have hJ := trans_det he hc hy hy'
  have hcx : c x ∈ c.target := c.map_source hxc
  have hcx' : c.symm (c x) ∈ e.source := by rw [c.left_inv hxc]; exact hx
  -- `u ∘ c⁻¹` is C² at `c x`
  have hv : ContDiffAt ℝ 2 (u ∘ c.symm) (ψ (e x)) := by
    rw [hψy]
    have h1 : ContDiffAt ℝ 2 ((u ∘ e.symm) ∘ (e ∘ c.symm)) (c x) := by
      refine ContDiffAt.comp (c x) ?_ (trans_contDiffAt hc he hcx hcx')
      simpa [Function.comp_apply, c.left_inv hxc] using hu
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [overlap_mem_nhds hcx hcx'] with z hz
    simp only [Function.comp_apply, e.left_inv hz.2]
  have key := lapB_pullback (ψ := ψ) (G := g.G c) (u := u ∘ c.symm) hψ hJ hv
    (by rw [hψy]; exact g.diff c hcA _ hcx) (by rw [hψy]; exact g.symm c hcA _ hcx)
    (by rw [hψy]; exact g.det c hcA _ hcx)
  rw [hψy] at key
  show lapB (g.G c) (u ∘ c.symm) (c x) = _
  rw [← key]
  refine lapB_congr EventuallyEq.rfl ?_
  filter_upwards [overlap_mem_nhds hy hy'] with z hz
  simp only [ψ, Function.comp_apply, c.left_inv hz.2]

/-- **Chart independence, atlas.** For every chart `e` of the atlas with `x ∈ e.source` and `u ∘ e⁻¹` C² at `e x`:
`lapM g u x = lapB (G e) (u ∘ e⁻¹) (e x)`. -/
theorem lapM_eq_chart [IsManifold 𝓘(ℝ, E n) 2 M] (g : CoordMetric n M) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ atlas (E n) M) {x : M} (hx : x ∈ e.source) {u : M → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapM g u x = lapB (g.G e) (u ∘ e.symm) (e x) := by
  rw [lapM_eq_pullback g (IsManifold.subset_maximalAtlas he) hx hu]
  have hy : e x ∈ e.target := e.map_source hx
  have hy' : e.symm (e x) ∈ (chartAt (E n) x).source := by
    rw [e.left_inv hx]; exact mem_chart_source (E n) x
  refine lapB_congr ?_ EventuallyEq.rfl
  filter_upwards [overlap_mem_nhds hy hy'] with z hz
  exact (g.compat _ (chart_mem_atlas (E n) x) e he z hz.1 hz.2).symm

/-- Two charts of the atlas around `x` give the same value. -/
theorem lapB_chart_indep [IsManifold 𝓘(ℝ, E n) 2 M] (g : CoordMetric n M)
    {e e' : OpenPartialHomeomorph M (E n)} (he : e ∈ atlas (E n) M) (he' : e' ∈ atlas (E n) M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) {u : M → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) (hu' : ContDiffAt ℝ 2 (u ∘ e'.symm) (e' x)) :
    lapB (g.G e) (u ∘ e.symm) (e x) = lapB (g.G e') (u ∘ e'.symm) (e' x) := by
  rw [← lapM_eq_chart g he hx hu, ← lapM_eq_chart g he' hx' hu']


/-! ### The canonical coordinate expression in every chart of the maximal atlas -/

theorem pullback_congr_point {φ : E n → E n} {G H : E n → Bil n} {y : E n} (h : G (φ y) = H (φ y)) :
    pullback φ G y = pullback φ H y := by
  unfold pullback; rw [h]

theorem pullback_congr_fun {φ φ' : E n → E n} {G : E n → Bil n} {y : E n} (h : φ =ᶠ[𝓝 y] φ') :
    pullback φ G y = pullback φ' G y := by
  unfold pullback; rw [h.eq_of_nhds, h.fderiv_eq]

theorem pullback_comp {φ ψ : E n → E n} {G : E n → Bil n} {y : E n} (hψ : DifferentiableAt ℝ ψ (φ y))
    (hφ : DifferentiableAt ℝ φ y) : pullback (ψ ∘ φ) G y = pullback φ (pullback ψ G) y := by
  unfold pullback; rw [fderiv_comp y hψ hφ]; rfl

/-- Coordinate expression of `g` in an arbitrary chart `e` of the maximal atlas: at `y`, pull back the expression in
the preferred chart at `e⁻¹ y`. -/
def coordExpr (g : CoordMetric n M) (e : OpenPartialHomeomorph M (E n)) (y : E n) : Bil n :=
  pullback (chartAt (E n) (e.symm y) ∘ e.symm) (g.G (chartAt (E n) (e.symm y))) y

/-- On a chart of the atlas the canonical expression is the given one. -/
theorem coordExpr_atlas (g : CoordMetric n M) {e : OpenPartialHomeomorph M (E n)} (he : e ∈ atlas (E n) M)
    {y : E n} (hy : y ∈ e.target) : coordExpr g e y = g.G e y :=
  (g.compat _ (chart_mem_atlas (E n) _) e he y hy (mem_chart_source (E n) _)).symm

/-- Near `e x`, the canonical expression is the pull-back from the preferred chart at `x`. -/
theorem coordExpr_eventually [IsManifold 𝓘(ℝ, E n) 2 M] (g : CoordMetric n M)
    {e : OpenPartialHomeomorph M (E n)} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {x : M}
    (hx : x ∈ e.source) :
    coordExpr g e =ᶠ[𝓝 (e x)] pullback (chartAt (E n) x ∘ e.symm) (g.G (chartAt (E n) x)) := by
  set c := chartAt (E n) x
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M := IsManifold.chart_mem_maximalAtlas x
  have hy : e x ∈ e.target := e.map_source hx
  have hy' : e.symm (e x) ∈ c.source := by rw [e.left_inv hx]; exact mem_chart_source (E n) x
  filter_upwards [overlap_mem_nhds hy hy'] with y hyS
  set z := e.symm y
  set c' := chartAt (E n) z
  have hc' : c' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M := IsManifold.chart_mem_maximalAtlas z
  have hzc' : z ∈ c'.source := mem_chart_source (E n) z
  have hzc : z ∈ c.source := hyS.2
  have hcz : c' z ∈ c'.target := c'.map_source hzc'
  have hcz' : c'.symm (c' z) ∈ c.source := by rw [c'.left_inv hzc']; exact hzc
  have h1 : g.G c' ((c' ∘ e.symm) y) = pullback (c ∘ c'.symm) (g.G c) ((c' ∘ e.symm) y) :=
    g.compat c (chart_mem_atlas (E n) x) c' (chart_mem_atlas (E n) z) (c' z) hcz hcz'
  show pullback (c' ∘ e.symm) (g.G c') y = pullback (c ∘ e.symm) (g.G c) y
  rw [pullback_congr_point h1, ← pullback_comp
    ((trans_contDiffAt hc' hc hcz hcz').differentiableAt (by norm_num))
    ((trans_contDiffAt he hc' hyS.1 hzc').differentiableAt (by norm_num))]
  apply pullback_congr_fun
  filter_upwards [overlap_mem_nhds hyS.1 hzc'] with w hw
  simp only [Function.comp_apply, c'.left_inv hw.2]

/-- **Chart independence in the maximal atlas**, with the canonical coordinate expression. -/
theorem lapM_eq_coordExpr [IsManifold 𝓘(ℝ, E n) 2 M] (g : CoordMetric n M)
    {e : OpenPartialHomeomorph M (E n)} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {x : M}
    (hx : x ∈ e.source) {u : M → ℝ} (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapM g u x = lapB (coordExpr g e) (u ∘ e.symm) (e x) := by
  rw [lapM_eq_pullback g he hx hu]
  exact lapB_congr (coordExpr_eventually g he hx).symm EventuallyEq.rfl

/-- The canonical expression is symmetric. -/
theorem coordExpr_symm (g : CoordMetric n M) (e : OpenPartialHomeomorph M (E n)) (y : E n) (v w : E n) : coordExpr g e y v w = coordExpr g e y w v := by
  have hm : chartAt (E n) (e.symm y) (e.symm y) ∈ (chartAt (E n) (e.symm y)).target :=
    mem_chart_target (E n) _
  simp only [coordExpr, pullback, ContinuousLinearMap.bilinearComp_apply, Function.comp_apply]
  exact g.symm _ (chart_mem_atlas (E n) _) _ hm _ _

/-- The canonical expression is nondegenerate on the target of a chart of the maximal atlas. -/
theorem coordExpr_det [IsManifold 𝓘(ℝ, E n) 2 M] (g : CoordMetric n M) {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {y : E n} (hy : y ∈ e.target) :
    (mat (coordExpr g e y)).det ≠ 0 := by
  set c := chartAt (E n) (e.symm y)
  have hJ := trans_det he (IsManifold.chart_mem_maximalAtlas (e.symm y)) hy (mem_chart_source (E n) _)
  have hG := g.det c (chart_mem_atlas (E n) _) _ (mem_chart_target (E n) (e.symm y))
  simp only [coordExpr, pullback, mat_comp, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hJ hG) hJ

/-! ### The flat space `E n` with its standard metric -/

/-- The standard bilinear form `Σ_k v_k w_k`. -/
def stdBil (n : ℕ) : Bil n :=
  ∑ k : Fin n, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k)

theorem stdBil_apply (v w : E n) : stdBil n v w = ∑ k, v k * w k := by
  simp [stdBil, ContinuousLinearMap.sum_apply, smul_eq_mul]

theorem mat_stdBil : mat (stdBil n) = 1 := by
  ext i j
  simp [mat, stdBil_apply, ev, Pi.single_apply, Matrix.one_apply, eq_comm]

/-- The flat metric on the model space (charted over itself by the identity). -/
def flatMetric (n : ℕ) : CoordMetric n (E n) where
  G _ _ := stdBil n
  diff _ _ _ _ := differentiableAt_const _
  symm _ _ _ _ v w := by simp only [stdBil_apply, mul_comm]
  pos _ _ _ _ v hv := by
    rw [stdBil_apply]
    obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h; push Not at h; exact hv (funext h)
    calc (0 : ℝ) < v k * v k := mul_self_pos.2 hk
      _ ≤ ∑ j, v j * v j :=
        Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
  det _ _ _ _ := by rw [mat_stdBil, Matrix.det_one]; exact one_ne_zero
  compat e he e' he' y _ _ := by
    rw [chartedSpaceSelf_atlas] at he he'
    subst he he'
    have hf : (⇑(OpenPartialHomeomorph.refl (E n)) ∘ ⇑(OpenPartialHomeomorph.refl (E n)).symm) = id := by
      funext z; simp
    ext a b
    simp [pullback, hf, fderiv_id]

/-- The coordinate operator of the constant standard metric is the sum of pure second derivatives. -/
theorem lapB_std (u : E n → ℝ) (x : E n) :
    lapB (fun _ => stdBil n) u x = ∑ i, fderiv ℝ (fderiv ℝ u) x (ev i) (ev i) := by
  unfold lapB LB hessG koszul
  simp only [fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply, mat_stdBil, inv_one,
    Matrix.one_apply]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- **Flat consistency.** On the model space with the flat metric, `lapM` is `Σ_i ∂_i² u`. -/
theorem lapM_flat (u : E n → ℝ) (x : E n) :
    lapM (flatMetric n) u x = ∑ i, fderiv ℝ (fderiv ℝ u) x (ev i) (ev i) := by
  unfold lapM
  rw [chartAt_self_eq]
  have : (u ∘ ⇑(OpenPartialHomeomorph.refl (E n)).symm) = u := by funext z; simp
  rw [this]
  exact lapB_std u x

/-- **Flat consistency with Mathlib's Laplacian.** Transported to `EuclideanSpace ℝ (Fin n)` (the inner product
space on which Mathlib's `Δ` is defined), `lapM` of the flat metric is Mathlib's Laplacian, for `u` of class C². -/
theorem lapM_flat_laplacian {u : E n → ℝ} (hu : ContDiff ℝ 2 u) (x : E n) :
    lapM (flatMetric n) u x =
      Laplacian.laplacian (u ∘ (EuclideanSpace.equiv (Fin n) ℝ))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x) := by
  have hL := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (u ∘ ⇑(EuclideanSpace.equiv (Fin n) ℝ)) (EuclideanSpace.basisFun (Fin n) ℝ))
    ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
  rw [lapM_flat]
  refine Eq.trans ?_ hL.symm
  refine Finset.sum_congr rfl fun i _ => ?_
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] E n := (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap with hLdef
  have hc : (u ∘ ⇑(EuclideanSpace.equiv (Fin n) ℝ)) = u ∘ ⇑L := rfl
  rw [hc, ContinuousLinearMap.iteratedFDeriv_comp_right L hu _ le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  have h0 : L ((EuclideanSpace.equiv (Fin n) ℝ).symm x) = x :=
    (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply x
  have h1 : L (EuclideanSpace.basisFun (Fin n) ℝ i) = ev i := by
    ext j; simp [L, ev, EuclideanSpace.basisFun_apply, Pi.single_apply]
  have h0' : L (WithLp.toLp 2 x) = x := by simpa using h0
  have h1' : L (EuclideanSpace.single i 1) = ev i := by simpa [EuclideanSpace.basisFun_apply] using h1
  simp
  rw [h0', h1']

end CTG.LaplaceBeltramiManifold
