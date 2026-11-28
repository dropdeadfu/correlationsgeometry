/-
Eighty-fourth Lean file (after version 4). Link of the chart-independent Laplace–Beltrami operator with Mathlib's
type classes for Riemannian bundles, and the round sphere as a Mathlib Riemannian metric. Written by a subagent of
the author-side session (task A197), checked here.

`lapRiem_congr_inner` (the operator depends only on the inner products). For `M` with `RiemannianBundle` and
`IsContMDiffRiemannianBundle … 1` on the tangent bundle (model `Fin n → ℝ`): `ofBundle`, `lapRiemTC`,
`coordOf_ofBundle_apply` (coordinate expression = inner product of the fibre of the images under the derivative of
the inverse chart), `lapRiemTC_eq_chart`, `lapRiemTC_eq_coordExpr`, `riemannianManifold_ofBundle`. Sphere:
`roundRiem` (the round metric of `CorrelationsToGeometrySphereAtlas` as a `ContMDiffRiemannianMetric`, all fields
proved), `lapRiem_round` and `lapRiemTC_round` (= `sphLapS f x` at every point, for `SphC2 f x`).

NOT shown: that `roundRiem` is the metric induced from ℝ³ as a statement about `roundRiem` (it is built from
`gRound` in the charts; the induced-metric statement is `indMetric_coordPt` of the LBSphere file); the relation to
Mathlib's own manifold structure on the sphere; an `IsRiemannianManifold` instance for S² (no distance); `roundRiem`
only C¹; model `Fin n → ℝ` without boundary; pointwise formula, not an operator on a function space.
No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryRiemannianLink
import CorrelationsToGeometrySphereAtlas

open Bundle Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace CTG.RiemannianBundleLink

open CTG.LaplaceBeltrami (E Bil lapB pullback)
open CTG.LaplaceBeltramiManifold
open CTG.RiemannianLink

/-! ### Stage 2: `lapRiem` depends only on the inner product -/

section Stage2
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (E n) M] [IsManifold 𝓘(ℝ, E n) 2 M]

/-- Two `ContMDiffRiemannianMetric`s with the same inner product are equal (the other fields are propositions). -/
theorem riem_ext {gR gR' : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n) (fun x : M => TangentSpace 𝓘(ℝ, E n) x)}
    (h : gR.inner = gR'.inner) : gR = gR' := by
  cases gR; cases gR'; cases h; rfl

/-- **Independence.** `lapRiem` depends only on the inner product of the metric. -/
theorem lapRiem_congr_inner (gR gR' : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n)
      (fun x : M => TangentSpace 𝓘(ℝ, E n) x)) (h : gR.inner = gR'.inner) :
    lapRiem gR = lapRiem gR' := by
  rw [riem_ext h]

end Stage2

/-! ### Stage 1: Mathlib's type classes `RiemannianBundle`, `IsContMDiffRiemannianBundle` -/

section Stage1
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (E n) M] [IsManifold 𝓘(ℝ, E n) 2 M]
  [hR : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E n) x)]

/-- The inner product of the fibres (registered by `RiemannianBundle`) is the form of the bundle metric. -/
theorem inner_eq_g (x : M) (v w : TangentSpace 𝓘(ℝ, E n) x) : inner ℝ v w = hR.g.inner x v w := rfl

variable [hC : IsContMDiffRiemannianBundle 𝓘(ℝ, E n) 1 (E n) (fun x : M => TangentSpace 𝓘(ℝ, E n) x)]

variable (M) in
/-- **The C¹ Riemannian metric of a Riemannian tangent bundle** in Mathlib's type-class form, as a
`ContMDiffRiemannianMetric`; its form is the inner product of the fibres. -/
def ofBundle : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n) (fun x : M => TangentSpace 𝓘(ℝ, E n) x) where
  inner := hR.g.inner
  symm := hR.g.symm
  pos := hR.g.pos
  isVonNBounded := hR.g.isVonNBounded
  contMDiff := by
    obtain ⟨g, hg, hgi⟩ := hC.exists_contMDiff
    have hgeq : g = hR.g.inner := by
      funext x; ext v w; exact (hgi x v w).symm
    rw [← hgeq]; exact hg

theorem ofBundle_inner (x : M) (v w : TangentSpace 𝓘(ℝ, E n) x) : (ofBundle M).inner x v w = inner ℝ v w := rfl

/-- `‖v‖² = g(v,v)` for the norm of the fibres (the norm used by `riemannianEDist`). -/
theorem norm_sq_ofBundle (x : M) (v : TangentSpace 𝓘(ℝ, E n) x) : ‖v‖ ^ 2 = (ofBundle M).inner x v v := by
  rw [ofBundle_inner]; exact (real_inner_self_eq_norm_sq v).symm

variable (n) in
/-- **Laplace–Beltrami operator of the Riemannian tangent bundle** (type-class form). -/
def lapRiemTC (u : M → ℝ) (x : M) : ℝ := lapRiem (ofBundle (n := n) M) u x

/-- Coordinate expression in a chart `e`: `G_e(y)(v,w) = ⟪D(e⁻¹)_y v, D(e⁻¹)_y w⟫` (inner product of the fibre at
`e⁻¹ y`). -/
theorem coordOf_ofBundle_apply (e : OpenPartialHomeomorph M (E n)) (y v w : E n) :
    coordOf (ofBundle M).inner e y v w =
      inner ℝ (mfderiv 𝓘(ℝ, E n) 𝓘(ℝ, E n) e.symm y v : TangentSpace 𝓘(ℝ, E n) (e.symm y))
        (mfderiv 𝓘(ℝ, E n) 𝓘(ℝ, E n) e.symm y w) := rfl

/-- **Coordinate formula in every chart of the maximal C² atlas.** -/
theorem lapRiemTC_eq_chart {e : OpenPartialHomeomorph M (E n)} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M)
    {x : M} (hx : x ∈ e.source) {u : M → ℝ} (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapRiemTC n u x = lapB (coordOf (ofBundle M).inner e) (u ∘ e.symm) (e x) :=
  lapRiem_eq_chart (ofBundle M) he hx hu

/-- The same, with the canonical coordinate expression of the induced `CoordMetric`. -/
theorem lapRiemTC_eq_coordExpr {e : OpenPartialHomeomorph M (E n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E n) 2 M) {x : M} (hx : x ∈ e.source) {u : M → ℝ}
    (hu : ContDiffAt ℝ 2 (u ∘ e.symm) (e x)) :
    lapRiemTC n u x = lapB (coordExpr (ofRiemannian (ofBundle M)) e) (u ∘ e.symm) (e x) :=
  lapRiem_eq_coordExpr (ofBundle M) he hx hu

/-- If the bundle structure was registered from a `ContMDiffRiemannianMetric` `gR`, then `lapRiemTC = lapRiem gR`. -/
theorem lapRiemTC_eq_lapRiem (gR : ContMDiffRiemannianMetric 𝓘(ℝ, E n) 1 (E n)
      (fun x : M => TangentSpace 𝓘(ℝ, E n) x)) (h : ∀ x (v w : TangentSpace 𝓘(ℝ, E n) x),
      inner ℝ v w = gR.inner x v w) :
    lapRiemTC n (M := M) = lapRiem gR := by
  unfold lapRiemTC
  funext u x
  rw [lapRiem_congr_inner (ofBundle M) gR (by funext x; ext v w; exact h x v w)]

end Stage1

section RiemannianManifold
variable {n : ℕ} {M : Type*} [PseudoEMetricSpace M] [ChartedSpace (E n) M] [IsManifold 𝓘(ℝ, E n) 2 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E n) 1 (E n) (fun x : M => TangentSpace 𝓘(ℝ, E n) x)]
  [IsRiemannianManifold 𝓘(ℝ, E n) M]

/-- **Riemannian manifold.** On a Riemannian manifold in Mathlib's sense, the metric `ofBundle M` used by `lapRiemTC`
is the one whose length structure gives the distance: `edist = riemannianEDist` (computed with the fibre norm), and
the fibre norm satisfies `‖v‖² = (ofBundle M).inner x v v`. -/
theorem riemannianManifold_ofBundle (x y : M) :
    edist x y = Manifold.riemannianEDist 𝓘(ℝ, E n) x y ∧
      ∀ (z : M) (v : TangentSpace 𝓘(ℝ, E n) z), ‖v‖ ^ 2 = (ofBundle M).inner z v v :=
  ⟨IsRiemannianManifold.out x y, fun z v => norm_sq_ofBundle z v⟩

end RiemannianManifold

/-! ### Stage 3: the round metric of S² as a `ContMDiffRiemannianMetric` -/

section Sphere

open CTG.FunkHecke (S2)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.LaplaceBeltrami (gRound)
open CTG.SphereAtlas (chartR rots mem_atlas_iff chartAt_eq trans_eq pullback_trR mem_src_idx gRound_pos
  roundMetricS lapM_roundS)
open CTG.SphereManifold (tgt sin_pos_tgt gRound_apply)

/-- The round metric on the tangent spaces of S²: at `x`, the form `gRound` at the point `chartAt x x` (tangent
vectors at `x` are coordinate vectors in the preferred chart at `x`). -/
def roundField (x : S2) : TangentSpace 𝓘(ℝ, E 2) x →L[ℝ] TangentSpace 𝓘(ℝ, E 2) x →L[ℝ] ℝ :=
  gRound (chartAt (E 2) x x)

theorem chart_target_tgt (x : S2) : chartAt (E 2) x x ∈ tgt := mem_chart_target (E 2) x

/-- In every chart of the atlas, the coordinate expression of `roundField` is `gRound`. -/
theorem coordOf_round {e : OpenPartialHomeomorph S2 (E 2)} (he : e ∈ atlas (E 2) S2) {y : E 2}
    (hy : y ∈ e.target) : coordOf roundField e y = gRound y := by
  have hem := IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, E 2)) (n := 2) he
  rw [coordOf_eq roundField hem hy]
  obtain ⟨i, rfl⟩ := mem_atlas_iff.mp he
  set z := (chartR (rots i)).symm y
  have h1 : pullback (chartAt (E 2) z ∘ (chartR (rots i)).symm) (fun _ => (roundField z : Bil 2)) y =
      pullback (chartAt (E 2) z ∘ (chartR (rots i)).symm) gRound y := pullback_congr_point rfl
  rw [h1, chartAt_eq, trans_eq]
  exact pullback_trR _ _ hy (mem_src_idx z)

/-- Abstract form (instance search on `Bil 2` fails for `IsBoundedSMul` otherwise). -/
theorem contDiff_const_add_smul {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {s : V → ℝ} (hs : ContDiff ℝ 1 s) (C B : W) :
    ContDiff ℝ 1 (fun x => C + s x • B) := contDiff_const.add (hs.smul contDiff_const)

theorem gRound_contDiff : ContDiff ℝ 1 gRound := by
  have hs : ContDiff ℝ 1 fun x : E 2 => Real.sin (x 0) ^ 2 := by fun_prop
  exact contDiff_const_add_smul hs (CTG.LaplaceBeltrami.sq 0) (CTG.LaplaceBeltrami.sq 1)

theorem ball_of_round {s : ℝ} (hs : 0 < s) (u : E 2) (hu : u 0 * u 0 + s ^ 2 * (u 1 * u 1) < 1) :
    u ∈ Metric.ball (0 : E 2) (1 + 1 / s) := by
  have hr : 0 < 1 + 1 / s := by positivity
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hr]
  have h0 : 0 ≤ s ^ 2 * (u 1 * u 1) := mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
  have hinv : 0 < 1 / s := by positivity
  intro k; fin_cases k
  · show ‖u 0‖ < 1 + 1 / s
    have : |u 0| < 1 := by rw [← sq_lt_one_iff_abs_lt_one]; nlinarith
    rw [Real.norm_eq_abs]; linarith
  · show ‖u 1‖ < 1 + 1 / s
    have h1 : |s * u 1| < 1 := by rw [← sq_lt_one_iff_abs_lt_one]; nlinarith [mul_self_nonneg (u 0)]
    rw [abs_mul, abs_of_pos hs] at h1
    have : |u 1| < 1 / s := by rw [lt_div_iff₀ hs]; linarith
    rw [Real.norm_eq_abs]; linarith

/-- **The round metric of S² as a Mathlib `ContMDiffRiemannianMetric`** (class C¹ in the bundle sense). -/
def roundRiem : ContMDiffRiemannianMetric 𝓘(ℝ, E 2) 1 (E 2) (fun x : S2 => TangentSpace 𝓘(ℝ, E 2) x) where
  inner := roundField
  symm x v w := CTG.LBSphere.gRound_symm _ v w
  pos x v hv := gRound_pos (chart_target_tgt x) v hv
  isVonNBounded x := by
    have hs := sin_pos_tgt (chart_target_tgt x)
    set s := Real.sin ((chartAt (E 2) x x) 0) with hsdef
    refine (NormedSpace.isVonNBounded_ball ℝ (E 2) (1 + 1 / s)).subset fun v hv => ?_
    have hv' : gRound (chartAt (E 2) x x) v v < 1 := hv
    rw [gRound_apply, ← hsdef] at hv'
    exact ball_of_round hs v hv'
  contMDiff := by
    intro x₀
    rw [contMDiffAt_section]
    have hc : chartAt (E 2) x₀ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E 2) 2 S2 := IsManifold.chart_mem_maximalAtlas x₀
    have hx₀ : x₀ ∈ (chartAt (E 2) x₀).source := mem_chart_source (E 2) x₀
    have hch : ContMDiffAt 𝓘(ℝ, E 2) 𝓘(ℝ, E 2) 1 (chartAt (E 2) x₀) x₀ :=
      (contMDiffOn_chart (x := x₀)).contMDiffAt ((chartAt (E 2) x₀).open_source.mem_nhds hx₀)
    have hcd : ContMDiffAt 𝓘(ℝ, E 2) 𝓘(ℝ, Bil 2) 1 (fun z => gRound (chartAt (E 2) x₀ z)) x₀ :=
      ContMDiffAt.comp x₀ (gRound_contDiff.contMDiff.contMDiffAt) hch
    refine hcd.congr_of_eventuallyEq ?_
    filter_upwards [(chartAt (E 2) x₀).open_source.mem_nhds hx₀] with z hz
    ext v w
    have hy : chartAt (E 2) x₀ z ∈ (chartAt (E 2) x₀).target := (chartAt (E 2) x₀).map_source hz
    have h2 := congrArg (fun B : Bil 2 => B v w) (coordOf_round (chart_mem_atlas (E 2) x₀) hy)
    simp only at h2
    rw [← h2, triv_apply roundField x₀ z hz v w, tcc_eq]
    simp only [coordOf, ContinuousLinearMap.bilinearComp_apply]
    rw [mfderiv_symm_eq hc hy, (chartAt (E 2) x₀).left_inv hz]
    rfl

theorem roundRiem_inner (x : S2) : roundRiem.inner x = gRound (chartAt (E 2) x x) := rfl

/-- The coordinate expressions of the induced `CoordMetric` in the charts of the atlas are `gRound`, as for
`roundMetricS`. -/
theorem ofRiemannian_round_G {e : OpenPartialHomeomorph S2 (E 2)} (he : e ∈ atlas (E 2) S2) {y : E 2}
    (hy : y ∈ e.target) : (ofRiemannian roundRiem).G e y = roundMetricS.G e y :=
  coordOf_round he hy

/-- **Main theorem.** For the round metric as a Mathlib `ContMDiffRiemannianMetric`, the Laplace–Beltrami operator
`lapRiem` equals the extrinsic Laplacian `sphLapS` at every point of S², for `f` with `SphC2 f x`. -/
theorem lapRiem_round (f : S2 → ℝ) (x : S2) (hF : SphC2 f x) : lapRiem roundRiem f x = sphLapS f x := by
  rw [← lapM_roundS f x hF]
  show lapB (coordOf roundField (chartAt (E 2) x)) _ _ = lapB gRound _ _
  refine lapB_congr ?_ EventuallyEq.rfl
  filter_upwards [(chartAt (E 2) x).open_target.mem_nhds (mem_chart_target (E 2) x)] with y hy
  exact coordOf_round (chart_mem_atlas (E 2) x) hy

/-- The same in every chart of the maximal C² atlas, with the canonical coordinate expression. -/
theorem lapB_coordExpr_roundRiem (f : S2 → ℝ) {e : OpenPartialHomeomorph S2 (E 2)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E 2) 2 S2) {x : S2} (hx : x ∈ e.source)
    (hu : ContDiffAt ℝ 2 (f ∘ e.symm) (e x)) (hF : SphC2 f x) :
    lapB (coordExpr (ofRiemannian roundRiem) e) (f ∘ e.symm) (e x) = sphLapS f x := by
  rw [← lapRiem_eq_coordExpr roundRiem he hx hu, lapRiem_round f x hF]

/-- **Type-class form.** Registering the round metric as Mathlib's `RiemannianBundle` on the tangent bundle of S²
(this also registers `IsContMDiffRiemannianBundle 𝓘(ℝ, E 2) 1`), the type-class operator `lapRiemTC` is `sphLapS`. -/
theorem lapRiemTC_round (f : S2 → ℝ) (x : S2) (hF : SphC2 f x) :
    letI : RiemannianBundle (fun x : S2 => TangentSpace 𝓘(ℝ, E 2) x) := ⟨roundRiem.toRiemannianMetric⟩
    lapRiemTC 2 f x = sphLapS f x := by
  letI : RiemannianBundle (fun x : S2 => TangentSpace 𝓘(ℝ, E 2) x) := ⟨roundRiem.toRiemannianMetric⟩
  rw [lapRiemTC_eq_lapRiem roundRiem (fun _ _ _ => rfl)]
  exact lapRiem_round f x hF

end Sphere

end CTG.RiemannianBundleLink

end

