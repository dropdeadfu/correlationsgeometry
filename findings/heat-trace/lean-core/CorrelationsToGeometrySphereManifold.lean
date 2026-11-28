/-
Eightieth Lean file (after version 4). The sphere S² minus a closed half great circle as a C² manifold with ONE
chart (spherical coordinates), the round metric as a `CoordMetric` of `CorrelationsToGeometryLaplaceBeltramiManifold`,
and `lapM = sphLapS` there. Written by a subagent of the author-side session (task A193), checked here.

`U` = points of S² with `x₀ + i x₁` in the slit plane (removes the closed half great circle `x₁ = 0, x₀ ≤ 0`,
including both poles). Chart `x ↦ (arccos x₂, arg (x₀ + i x₁))` onto `(0,π) × (−π,π)`, inverse `coordPt`.
`roundMetric`, `round_eq_ind` (the coordinate expression is the metric induced by spherical coordinates),
`lapM_round` (lapM roundMetric f x = sphLapS f x for SphC2 f x), `lapB_coordExpr_round` (the same value in every
chart of the maximal C² atlas of U).

NOT shown: a manifold structure on the whole sphere (the half great circle with the poles is missing; no atlas with
several charts); a link with Mathlib's `RiemannianBundle`; an intrinsic Laplace–Beltrami operator in the sense of
Mathlib (`sphLapS` is the extrinsically defined operator); `ContMDiff` regularity; that U is open in S².
No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryLBSphere
import CorrelationsToGeometryLaplaceBeltramiManifold

open Real Filter Topology Set
open scoped Manifold

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace CTG.SphereManifold

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord (Φ ΦS norm_Φ)
open CTG.FunkHecke.SphereCharts (Φ_apply ext_E3 norm_sq_E3)
open CTG.LaplaceBeltrami (E Bil lapB gRound pullback mat gDiag)
open CTG.LBSphere (cpx cpx_normSq invPt inv_formula coordPt coordPt_contDiff uΦ sphLapS_eq_lapB pt_eta
  gRound_differentiableAt gRound_symm det_gRound indMetric indMetric_coordPt)
open CTG.LaplaceBeltramiManifold (CoordMetric lapM coordExpr lapM_eq_coordExpr)

/-- The open part of S² covered by one spherical-coordinate chart. -/
def U : Set S2 := {x | cpx (x : E3) ∈ Complex.slitPlane}

/-- The target `(0,π) × (−π,π)`. -/
def tgt : Set (E 2) := {y | 0 < y 0} ∩ {y | y 0 < π} ∩ {y | -π < y 1} ∩ {y | y 1 < π}

theorem tgt_open : IsOpen tgt :=
  (((isOpen_lt continuous_const (continuous_apply 0)).inter (isOpen_lt (continuous_apply 0) continuous_const)).inter
    (isOpen_lt continuous_const (continuous_apply 1))).inter (isOpen_lt (continuous_apply 1) continuous_const)

theorem norm_S2 (x : S2) : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2

theorem nonpolar (x : S2) (hx : cpx (x : E3) ∈ Complex.slitPlane) : -1 < (x : E3) 2 ∧ (x : E3) 2 < 1 := by
  have hn := norm_sq_E3 (x : E3)
  rw [norm_S2] at hn
  have hc : cpx (x : E3) ≠ 0 := Complex.slitPlane_ne_zero hx
  have hp : 0 < ‖cpx (x : E3)‖ := norm_pos_iff.mpr hc
  have h2 := cpx_normSq (x : E3)
  have : 0 < (x : E3) 0 ^ 2 + (x : E3) 1 ^ 2 := by nlinarith
  constructor <;> nlinarith

theorem invPt_one (w : E3) : invPt 0 w 1 = Complex.arg (cpx w) := by
  simp [invPt]

theorem invPt_zero (w : E3) : invPt 0 w 0 = Real.arccos (w 2) := rfl

theorem invPt_mem (x : S2) (hx : cpx (x : E3) ∈ Complex.slitPlane) : invPt 0 (x : E3) ∈ tgt := by
  obtain ⟨h1, h2⟩ := nonpolar x hx
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · show 0 < invPt 0 (x : E3) 0
    rw [invPt_zero]; exact Real.arccos_pos.mpr h2
  · show invPt 0 (x : E3) 0 < π
    rw [invPt_zero]; exact Real.arccos_lt_pi.mpr h1
  · show -π < invPt 0 (x : E3) 1
    rw [invPt_one]; exact Complex.neg_pi_lt_arg _
  · show invPt 0 (x : E3) 1 < π
    rw [invPt_one]
    exact lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.slitPlane_arg_ne_pi hx)

theorem cpx_coordPt (y : E 2) :
    cpx (coordPt y) = (Real.sin (y 0) : ℂ) * (Real.cos (y 1) + Real.sin (y 1) * Complex.I) := by
  obtain ⟨p0, p1, -⟩ := Φ_apply (y 0) (y 1)
  have e0 : coordPt y 0 = Real.sin (y 0) * Real.cos (y 1) := p0
  have e1 : coordPt y 1 = Real.sin (y 0) * Real.sin (y 1) := p1
  unfold cpx; rw [e0, e1]; push_cast; ring

theorem coordPt_two (y : E 2) : coordPt y 2 = Real.cos (y 0) := (Φ_apply (y 0) (y 1)).2.2

theorem coordPt_mem (y : E 2) (hy : y ∈ tgt) :
    cpx (coordPt y) ∈ Complex.slitPlane ∧ invPt 0 (coordPt y) = y := by
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hy
  have hs : 0 < Real.sin (y 0) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  have harg : Complex.arg (cpx (coordPt y)) = y 1 := by
    rw [cpx_coordPt, Complex.arg_real_mul _ hs]
    have := Complex.arg_cos_add_sin_mul_I (θ := y 1) ⟨h3, h4.le⟩
    simpa using this
  have hne : cpx (coordPt y) ≠ 0 := by
    rw [cpx_coordPt]
    refine mul_ne_zero (by exact_mod_cast hs.ne') ?_
    intro h0
    have hr := congrArg Complex.re h0
    have hi := congrArg Complex.im h0
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re] at hr hi
    nlinarith [Real.sin_sq_add_cos_sq (y 1)]
  refine ⟨Complex.mem_slitPlane_iff_arg.mpr ⟨by rw [harg]; exact h4.ne, hne⟩, ?_⟩
  ext i; fin_cases i
  · show invPt 0 (coordPt y) 0 = y 0
    rw [invPt_zero, coordPt_two, Real.arccos_cos h1.le h2.le]
  · show invPt 0 (coordPt y) 1 = y 1
    rw [invPt_one, harg]

/-- The base point `(π/2, 0) ↦ (1,0,0)`. -/
theorem tgt_base : (![π / 2, 0] : E 2) ∈ tgt := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> simp <;> linarith [Real.pi_pos]

def basePt : U := ⟨ΦS (π / 2) 0, by
  have := (coordPt_mem _ tgt_base).1
  simpa [coordPt] using this⟩

/-- Chart map. -/
def toF (x : U) : E 2 := invPt 0 ((x : S2) : E3)

open Classical in
/-- Inverse chart map. -/
def invF (y : E 2) : U :=
  if h : cpx (coordPt y) ∈ Complex.slitPlane then ⟨ΦS (y 0) (y 1), h⟩ else basePt

theorem coordPt_toF (x : U) : coordPt (toF x) = ((x : S2) : E3) := by
  obtain ⟨h1, h2⟩ := nonpolar (x : S2) x.2
  exact inv_formula _ (norm_S2 _) (by nlinarith) 0

theorem invF_toF (x : U) : invF (toF x) = x := by
  have hc := coordPt_toF x
  unfold invF
  rw [dif_pos (by rw [hc]; exact x.2)]
  exact Subtype.ext (Subtype.ext hc)

theorem toF_invF (y : E 2) (hy : y ∈ tgt) : toF (invF y) = y := by
  unfold invF
  rw [dif_pos (coordPt_mem y hy).1]
  exact (coordPt_mem y hy).2

theorem invF_val (y : E 2) (hy : y ∈ tgt) : ((invF y : S2) : E3) = coordPt y := by
  unfold invF
  rw [dif_pos (coordPt_mem y hy).1]
  rfl

def chartPE : PartialEquiv U (E 2) where
  toFun := toF
  invFun := invF
  source := univ
  target := tgt
  map_source' x _ := invPt_mem (x : S2) x.2
  map_target' _ _ := mem_univ _
  left_inv' x _ := invF_toF x
  right_inv' y hy := toF_invF y hy

theorem cpx_cont : Continuous fun w : E3 => cpx w := by
  unfold cpx
  have h0 : Continuous fun w : E3 => w 0 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).continuous
  have h1 : Continuous fun w : E3 => w 1 := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).continuous
  exact (Complex.continuous_ofReal.comp h0).add ((Complex.continuous_ofReal.comp h1).mul continuous_const)

theorem toF_cont : Continuous toF := by
  have hv : Continuous fun x : U => ((x : S2) : E3) := continuous_subtype_val.comp continuous_subtype_val
  rw [continuous_pi_iff]; intro i; fin_cases i
  · show Continuous fun x : U => invPt 0 ((x : S2) : E3) 0
    simp only [invPt_zero]
    exact Real.continuous_arccos.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).continuous.comp hv)
  · show Continuous fun x : U => invPt 0 ((x : S2) : E3) 1
    simp only [invPt_one]
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact ContinuousAt.comp (f := fun x : U => cpx ((x : S2) : E3)) (Complex.continuousAt_arg x.2)
      (cpx_cont.comp hv).continuousAt

theorem invF_contOn : ContinuousOn invF tgt := by
  rw [continuousOn_iff_continuous_restrict]
  let g : tgt → U := fun y => ⟨ΦS (y.1 0) (y.1 1), (coordPt_mem y.1 y.2).1⟩
  have hg : Continuous g := by
    have h0 : Continuous fun y : tgt => coordPt y.1 := coordPt_contDiff.continuous.comp continuous_subtype_val
    exact Continuous.subtype_mk (Continuous.subtype_mk h0 _) _
  have heq : tgt.restrict invF = g := by
    funext y
    show invF y.1 = g y
    unfold invF; rw [dif_pos (coordPt_mem y.1 y.2).1]
  rw [heq]; exact hg

/-- **The spherical-coordinate chart of `U`.** -/
def chart : OpenPartialHomeomorph U (E 2) where
  toPartialEquiv := chartPE
  open_source := isOpen_univ
  open_target := tgt_open
  continuousOn_toFun := toF_cont.continuousOn
  continuousOn_invFun := invF_contOn

theorem chart_source : chart.source = univ := rfl
theorem chart_target : chart.target = tgt := rfl

instance : ChartedSpace (E 2) U := chart.singletonChartedSpace chart_source

theorem chartAt_eq (x : U) : chartAt (E 2) x = chart := rfl

theorem atlas_eq {e : OpenPartialHomeomorph U (E 2)} (he : e ∈ atlas (E 2) U) : e = chart := he

instance (k : WithTop ℕ∞) : IsManifold 𝓘(ℝ, E 2) k U := by
  haveI := chart.singleton_hasGroupoid chart_source (contDiffGroupoid k 𝓘(ℝ, E 2))
  exact IsManifold.mk' _ _ _

theorem sin_pos_tgt {y : E 2} (hy : y ∈ tgt) : 0 < Real.sin (y 0) :=
  Real.sin_pos_of_pos_of_lt_pi hy.1.1.1 hy.1.1.2

theorem gRound_apply (y v w : E 2) : gRound y v w = v 0 * w 0 + Real.sin (y 0) ^ 2 * (v 1 * w 1) := by
  simp [gRound, gDiag, CTG.LaplaceBeltrami.sq]

theorem pullback_id_eventually {ψ : E 2 → E 2} {G : E 2 → Bil 2} {y : E 2} (h : ψ =ᶠ[𝓝 y] id) :
    pullback ψ G y = G y := by
  unfold pullback
  rw [h.fderiv_eq, h.eq_of_nhds, fderiv_id]
  rfl

/-- **The round metric on `U` as a `CoordMetric`** (its coordinate expression in the chart is `gRound`, the metric
induced by spherical coordinates, `round_eq_ind`). -/
def roundMetric : CoordMetric 2 U where
  G _ := gRound
  diff _ _ y _ := gRound_differentiableAt y
  symm _ _ y _ v w := gRound_symm y v w
  pos e he y hy v hv := by
    rw [atlas_eq he] at hy
    have hs := sin_pos_tgt hy
    rw [gRound_apply]
    have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra h; push Not at h; apply hv; ext i; fin_cases i <;> simp [h.1, h.2]
    rcases hv' with h | h
    · have : 0 < v 0 * v 0 := mul_self_pos.mpr h
      have : 0 ≤ Real.sin (y 0) ^ 2 * (v 1 * v 1) := mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
      linarith
    · have : 0 < v 1 * v 1 := mul_self_pos.mpr h
      have : 0 < Real.sin (y 0) ^ 2 * (v 1 * v 1) := mul_pos (pow_pos hs 2) this
      nlinarith [mul_self_nonneg (v 0)]
  det e he y hy := by
    rw [atlas_eq he] at hy
    rw [det_gRound]; exact pow_ne_zero 2 (sin_pos_tgt hy).ne'
  compat e he e' he' y hy hy' := by
    rw [atlas_eq he, atlas_eq he'] at *
    symm
    apply pullback_id_eventually
    filter_upwards [tgt_open.mem_nhds hy] with z hz
    exact chart.right_inv hz

theorem round_eq_ind (y : E 2) : roundMetric.G chart y = indMetric coordPt y := (indMetric_coordPt y).symm

theorem chart_symm_eq (z : E 2) : chart.symm z = invF z := rfl
theorem chart_apply (x : U) : chart x = toF x := rfl

/-- **Main theorem.** On `U ⊆ S²` with its spherical-coordinate chart and the round metric, the chart-independent
Laplace–Beltrami operator `lapM` equals the extrinsically defined Laplacian `sphLapS`, for `f` with `SphC2 f` at `x`. -/
theorem lapM_round (f : S2 → ℝ) (x : U) (hF : SphC2 f (x : S2)) :
    lapM roundMetric (fun z : U => f z) x = sphLapS f x := by
  set y := toF x with hy
  have hyT : y ∈ tgt := invPt_mem (x : S2) x.2
  have hpt : ΦS (y 0) (y 1) = (x : S2) := Subtype.ext (coordPt_toF x)
  have hs : Real.sin (y 0) ≠ 0 := (sin_pos_tgt hyT).ne'
  have key := sphLapS_eq_lapB f hs (by rw [hpt]; exact hF)
  rw [hpt, ← pt_eta y] at key
  rw [key]
  show lapB gRound ((fun z : U => f z) ∘ chart.symm) (chart x) = lapB gRound (uΦ f) y
  rw [chart_apply, ← hy]
  apply CTG.LBSphere.lapB_congr
  filter_upwards [tgt_open.mem_nhds hyT] with z hz
  show f (invF z : S2) = f (ΦS (z 0) (z 1))
  congr 1
  exact Subtype.ext (invF_val z hz)

/-- **Every chart of the maximal C² atlas of `U`.** With the canonical coordinate expression of the round metric,
the coordinate Laplace–Beltrami operator of `f ∘ e⁻¹` at `e x` equals `sphLapS f x`. -/
theorem lapB_coordExpr_round (f : S2 → ℝ) {e : OpenPartialHomeomorph U (E 2)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E 2) 2 U) (x : U) (hx : x ∈ e.source)
    (hu : ContDiffAt ℝ 2 ((fun z : U => f z) ∘ e.symm) (e x)) (hF : SphC2 f (x : S2)) :
    lapB (coordExpr roundMetric e) ((fun z : U => f z) ∘ e.symm) (e x) = sphLapS f x := by
  rw [← lapM_eq_coordExpr roundMetric he hx hu, lapM_round f x hF]

end CTG.SphereManifold

end

