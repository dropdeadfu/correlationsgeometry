/-
Eighty-first Lean file (after version 4). The WHOLE sphere S² as a C^k manifold (model `Fin 2 → ℝ`, every k) with an
atlas of three spherical-coordinate charts composed with linear isometries of ℝ³ (identity, `−id`, the coordinate
swap x₁ ↔ x₂), the round metric as a `CoordMetric 2 S2`, and `lapM roundMetricS f x = sphLapS f x` at EVERY point
of S² (for f with `SphC2 f x`). Written by a subagent of the author-side session (task A194), checked here.

`cover3` (the three chart domains cover the sphere), `chartR`, `chartedS2`, the `IsManifold` instance,
`pullback_trR` (the chart transitions are isometries of `gRound`), `roundMetricS`, `lapM_roundS`,
`lapB_chart_roundS`, `lapB_coordExpr_roundS` (every chart of the maximal C² atlas).

NOT shown: an intrinsic Laplace–Beltrami operator in the sense of Mathlib (`sphLapS` is the extrinsically defined
operator; shown is its equality with the chart-independent coordinate operator of a `CoordMetric` built here);
a link with Mathlib's `RiemannianBundle`; that this manifold structure agrees with Mathlib's own structure on the
sphere (model `EuclideanSpace ℝ (Fin 2)`); `ContMDiff` regularity (the hypotheses are pointwise).
No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometrySphereManifold

open Real Filter Topology Set
open scoped Manifold

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace CTG.SphereAtlas

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord (Φ ΦS norm_Φ)
open CTG.FunkHecke.SphereCharts (ΨS Φ_apply ext_E3 norm_sq_E3)
open CTG.LaplaceBeltrami (E Bil lapB gRound pullback mat gDiag)
open CTG.LBSphere (cpx cpx_normSq invPt inv_formula coordPt uΨ sphLapS_eq_lapB_rot pt_eta
  gRound_differentiableAt gRound_symm det_gRound transition_isometry)
open CTG.LaplaceBeltramiManifold (CoordMetric lapM lapM_eq_chart coordExpr lapM_eq_coordExpr)
open CTG.SphereManifold (tgt tgt_open invPt_mem coordPt_mem invPt_zero invPt_one cpx_cont sin_pos_tgt
  gRound_apply)

abbrev Iso := E3 ≃ₗᵢ[ℝ] E3

/-! ### Stage 0: generic facts -/

theorem norm_unit_slit {w : E3} (hw : ‖w‖ = 1) (hc : cpx w ∈ Complex.slitPlane) : -1 < w 2 ∧ w 2 < 1 := by
  have hn := norm_sq_E3 w
  rw [hw] at hn
  have hc0 : cpx w ≠ 0 := Complex.slitPlane_ne_zero hc
  have hp : 0 < ‖cpx w‖ := norm_pos_iff.mpr hc0
  have h2 := cpx_normSq w
  have : 0 < w 0 ^ 2 + w 1 ^ 2 := by nlinarith
  constructor <;> nlinarith

theorem cpx_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n fun w : E3 => cpx w := by
  unfold cpx
  have h0 := Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 0).contDiff (n := n))
  have h1 := Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 1).contDiff (n := n))
  exact h0.add (h1.mul contDiff_const)

set_option backward.isDefEq.respectTransparency false in
theorem arg_contDiffAt' {p : ℂ} (hp : p ∈ Complex.slitPlane) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n Complex.arg p := by
  have h : Complex.arg = fun x => Complex.imCLM (Complex.log x) := by
    funext x; simp [Complex.log_im]
  rw [h]
  have hl : ContDiffAt ℝ n Complex.log p := (Complex.contDiffAt_log hp).restrict_scalars ℝ
  exact Complex.imCLM.contDiff.contDiffAt.comp p hl

theorem invPt0_eq (w : E3) : invPt 0 w = ![Real.arccos (w 2), Complex.arg (cpx w)] := by
  ext i; fin_cases i
  · rfl
  · simp [invPt]

/-- `invPt 0` is smooth at non-polar points with `w₀ + i w₁` in the slit plane. -/
theorem invPt0_contDiffAt {w : E3} (hw : ‖w‖ = 1) (hc : cpx w ∈ Complex.slitPlane) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (invPt 0) w := by
  obtain ⟨hlo, hhi⟩ := norm_unit_slit hw hc
  have hfun : invPt 0 = fun w : E3 => ![Real.arccos (w 2), Complex.arg (cpx w)] := funext invPt0_eq
  rw [hfun, contDiffAt_pi]
  intro i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    exact (Real.contDiffAt_arccos hlo.ne' hhi.ne).comp (f := fun w : E3 => w 2) w
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).contDiff.contDiffAt)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact (arg_contDiffAt' hc).comp (f := fun w : E3 => cpx w) w cpx_contDiff.contDiffAt

theorem coordPt_contDiff' {n : WithTop ℕ∞} : ContDiff ℝ n coordPt := by
  unfold coordPt Φ CTG.FunkHecke.SphereCoord.A; fun_prop

theorem norm_coordPt (y : E 2) : ‖coordPt y‖ = 1 := norm_Φ _ _

/-! ### Stage 1: the three isometries and the covering -/

/-- The coordinate swap `x₁ ↔ x₂`. -/
def Psw : Iso := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (1 : Fin 3) 2)

theorem Psw_symm_apply (x : E3) (i : Fin 3) : (Psw.symm x) i = x (Equiv.swap (1 : Fin 3) 2 i) := by
  simp [Psw, LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply]

/-- The three isometries of the atlas. -/
def rots : Fin 3 → Iso := ![LinearIsometryEquiv.refl ℝ E3, LinearIsometryEquiv.neg ℝ, Psw]

theorem cpx_re (w : E3) : (cpx w).re = w 0 := by simp [cpx]
theorem cpx_im (w : E3) : (cpx w).im = w 1 := by simp [cpx]

theorem slit_of_im {w : E3} (h : w 1 ≠ 0) : cpx w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [cpx_im]; exact h))

theorem slit_of_re {w : E3} (h : 0 < w 0) : cpx w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (by rw [cpx_re]; exact h))

/-- **Covering.** Every point of the unit sphere lies in the slit domain of one of the three isometries. -/
theorem cover3 (x : E3) (hx : ‖x‖ = 1) : ∃ i : Fin 3, cpx ((rots i).symm x) ∈ Complex.slitPlane := by
  by_cases h1 : x 1 ≠ 0
  · exact ⟨0, slit_of_im (by simpa [rots] using h1)⟩
  push Not at h1
  rcases lt_trichotomy (x 0) 0 with h0 | h0 | h0
  · refine ⟨1, slit_of_re ?_⟩
    simp [rots]; linarith
  · refine ⟨2, slit_of_im ?_⟩
    show (Psw.symm x) 1 ≠ 0
    rw [Psw_symm_apply]
    have : Equiv.swap (1 : Fin 3) 2 1 = 2 := Equiv.swap_apply_left _ _
    rw [this]
    have hn := norm_sq_E3 x
    rw [hx, h0, h1] at hn
    intro h2; rw [h2] at hn; norm_num at hn
  · exact ⟨0, slit_of_re (by simpa [rots] using h0)⟩

end CTG.SphereAtlas

namespace CTG.SphereAtlas

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord (Φ ΦS norm_Φ)
open CTG.FunkHecke.SphereCharts (ΨS Φ_apply ext_E3 norm_sq_E3)
open CTG.LaplaceBeltrami (E Bil lapB gRound pullback mat gDiag)
open CTG.LBSphere (cpx cpx_normSq invPt inv_formula coordPt uΨ sphLapS_eq_lapB_rot pt_eta
  gRound_differentiableAt gRound_symm det_gRound transition_isometry)
open CTG.LaplaceBeltramiManifold (CoordMetric lapM lapM_eq_chart coordExpr lapM_eq_coordExpr)
open CTG.SphereManifold (tgt tgt_open invPt_mem coordPt_mem invPt_zero invPt_one cpx_cont sin_pos_tgt
  gRound_apply)

/-! ### Stage 2: the rotated charts on the whole sphere -/

theorem norm_S2 (x : S2) : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2

/-- Source of the chart attached to `R`: points `x` with `R⁻¹ x` off the closed half great circle. -/
def src (R : Iso) : Set S2 := {x | cpx (R.symm (x : E3)) ∈ Complex.slitPlane}

/-- Chart map. -/
def toR (R : Iso) (x : S2) : E 2 := invPt 0 (R.symm (x : E3))

/-- Inverse chart map (defined everywhere). -/
def invR (R : Iso) (y : E 2) : S2 := ΨS R (y 0) (y 1)

theorem invR_val (R : Iso) (y : E 2) : ((invR R y : S2) : E3) = R (coordPt y) := rfl

theorem norm_symm (R : Iso) (x : S2) : ‖R.symm (x : E3)‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, norm_S2]

theorem coordPt_toR (R : Iso) {x : S2} (hx : x ∈ src R) : coordPt (toR R x) = R.symm (x : E3) := by
  obtain ⟨h1, h2⟩ := norm_unit_slit (norm_symm R x) hx
  exact inv_formula _ (norm_symm R x) (by nlinarith) 0

theorem src_open (R : Iso) : IsOpen (src R) :=
  Complex.isOpen_slitPlane.preimage
    (cpx_cont.comp (R.symm.continuous.comp continuous_subtype_val))

theorem toR_mem (R : Iso) {x : S2} (hx : x ∈ src R) : toR R x ∈ tgt :=
  invPt_mem ⟨R.symm (x : E3), mem_sphere_zero_iff_norm.mpr (norm_symm R x)⟩ hx

theorem invR_mem (R : Iso) {y : E 2} (hy : y ∈ tgt) : invR R y ∈ src R := by
  show cpx (R.symm (R (coordPt y))) ∈ Complex.slitPlane
  rw [LinearIsometryEquiv.symm_apply_apply]; exact (coordPt_mem y hy).1

theorem invR_toR (R : Iso) {x : S2} (hx : x ∈ src R) : invR R (toR R x) = x := by
  apply Subtype.ext
  rw [invR_val, coordPt_toR R hx, LinearIsometryEquiv.apply_symm_apply]

theorem toR_invR (R : Iso) {y : E 2} (hy : y ∈ tgt) : toR R (invR R y) = y := by
  show invPt 0 (R.symm (R (coordPt y))) = y
  rw [LinearIsometryEquiv.symm_apply_apply]; exact (coordPt_mem y hy).2

theorem toR_contOn (R : Iso) : ContinuousOn (toR R) (src R) := by
  have hv : Continuous fun x : S2 => R.symm (x : E3) := R.symm.continuous.comp continuous_subtype_val
  intro x hx
  apply ContinuousAt.continuousWithinAt
  rw [continuousAt_pi]; intro i; fin_cases i
  · show ContinuousAt (fun x : S2 => invPt 0 (R.symm (x : E3)) 0) x
    simp only [invPt_zero]
    exact (Real.continuous_arccos.comp
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) 2).continuous.comp hv)).continuousAt
  · show ContinuousAt (fun x : S2 => invPt 0 (R.symm (x : E3)) 1) x
    simp only [invPt_one]
    exact ContinuousAt.comp (f := fun x : S2 => cpx (R.symm (x : E3))) (Complex.continuousAt_arg hx)
      (cpx_cont.comp hv).continuousAt

theorem invR_cont (R : Iso) : Continuous (invR R) := by
  have h : Continuous fun y : E 2 => R (coordPt y) := R.continuous.comp (coordPt_contDiff' (n := 0)).continuous
  exact Continuous.subtype_mk (f := fun y : E 2 => R (coordPt y)) h _

/-- **The chart attached to the isometry `R`** (spherical coordinates composed with `R⁻¹`). -/
def chartR (R : Iso) : OpenPartialHomeomorph S2 (E 2) where
  toFun := toR R
  invFun := invR R
  source := src R
  target := tgt
  map_source' _ hx := toR_mem R hx
  map_target' _ hy := invR_mem R hy
  left_inv' _ hx := invR_toR R hx
  right_inv' _ hy := toR_invR R hy
  open_source := src_open R
  open_target := tgt_open
  continuousOn_toFun := toR_contOn R
  continuousOn_invFun := (invR_cont R).continuousOn

theorem chartR_source (R : Iso) : (chartR R).source = src R := rfl
theorem chartR_target (R : Iso) : (chartR R).target = tgt := rfl
theorem chartR_apply (R : Iso) (x : S2) : chartR R x = toR R x := rfl
theorem chartR_symm_apply (R : Iso) (y : E 2) : (chartR R).symm y = invR R y := rfl

/-! ### Stage 3: charted space and manifold structure -/

open Classical in
/-- Index of the preferred chart at `x`. -/
def idx (x : S2) : Fin 3 :=
  if h : ∃ i : Fin 3, x ∈ src (rots i) then Classical.choose h else 0

theorem mem_src_idx (x : S2) : x ∈ src (rots (idx x)) := by
  have h : ∃ i : Fin 3, x ∈ src (rots i) := cover3 (x : E3) (norm_S2 x)
  unfold idx; rw [dif_pos h]; exact Classical.choose_spec h

/-- **S² (the whole sphere) as a charted space** over `Fin 2 → ℝ`, with three charts. -/
instance chartedS2 : ChartedSpace (E 2) S2 where
  atlas := Set.range fun i : Fin 3 => chartR (rots i)
  chartAt x := chartR (rots (idx x))
  mem_chart_source x := mem_src_idx x
  chart_mem_atlas x := ⟨idx x, rfl⟩

theorem chartAt_eq (x : S2) : chartAt (E 2) x = chartR (rots (idx x)) := rfl

theorem mem_atlas_iff {e : OpenPartialHomeomorph S2 (E 2)} :
    e ∈ atlas (E 2) S2 ↔ ∃ i : Fin 3, e = chartR (rots i) := by
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

/-- The transition map between the charts of `R` (source) and `R'` (target), in coordinates. -/
def trR (R R' : Iso) (z : E 2) : E 2 := invPt 0 (R'.symm (R (coordPt z)))

theorem trans_eq (R R' : Iso) : ⇑(chartR R') ∘ ⇑(chartR R).symm = trR R R' := rfl

theorem norm_trw (R R' : Iso) (z : E 2) : ‖R'.symm (R (coordPt z))‖ = 1 := by
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, norm_coordPt]

theorem trR_contDiffAt (R R' : Iso) {z : E 2} (hz : cpx (R'.symm (R (coordPt z))) ∈ Complex.slitPlane)
    {n : WithTop ℕ∞} : ContDiffAt ℝ n (trR R R') z := by
  have hQ : ContDiff ℝ n fun z : E 2 => R'.symm (R (coordPt z)) :=
    R'.symm.toContinuousLinearEquiv.contDiff.comp (R.toContinuousLinearEquiv.contDiff.comp coordPt_contDiff')
  exact (invPt0_contDiffAt (norm_trw R R' z) hz).comp (f := fun z : E 2 => R'.symm (R (coordPt z))) z
    hQ.contDiffAt

theorem coordPt_trR (R R' : Iso) {z : E 2} (hz : cpx (R'.symm (R (coordPt z))) ∈ Complex.slitPlane) :
    coordPt (trR R R' z) = R'.symm (R (coordPt z)) := by
  obtain ⟨h1, h2⟩ := norm_unit_slit (norm_trw R R' z) hz
  exact inv_formula _ (norm_trw R R' z) (by nlinarith) 0

theorem trans_contDiffOn (R R' : Iso) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (trR R R') ((chartR R).symm ≫ₕ chartR R').source := by
  intro z hz
  rw [OpenPartialHomeomorph.trans_source] at hz
  exact (trR_contDiffAt R R' hz.2).contDiffWithinAt

instance (k : WithTop ℕ∞) : IsManifold 𝓘(ℝ, E 2) k S2 := by
  haveI : HasGroupoid S2 (contDiffGroupoid k 𝓘(ℝ, E 2)) := by
    apply hasGroupoid_of_pregroupoid
    intro e e' he he'
    obtain ⟨i, rfl⟩ := mem_atlas_iff.mp he
    obtain ⟨j, rfl⟩ := mem_atlas_iff.mp he'
    simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Set.range_id, Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id,
      OpenPartialHomeomorph.coe_trans]
    exact trans_contDiffOn (rots i) (rots j)
  exact IsManifold.mk' _ _ _

end CTG.SphereAtlas


namespace CTG.SphereAtlas

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCharts (ΨS)
open CTG.LaplaceBeltrami (E Bil lapB gRound pullback mat gDiag)
open CTG.LBSphere (cpx coordPt uΨ sphLapS_eq_lapB_rot pt_eta gRound_differentiableAt gRound_symm det_gRound
  transition_isometry)
open CTG.LaplaceBeltramiManifold (CoordMetric lapM lapM_eq_chart coordExpr lapM_eq_coordExpr)
open CTG.SphereManifold (tgt tgt_open sin_pos_tgt gRound_apply)

/-! ### Stage 4: the round metric as a `CoordMetric` on the whole sphere -/

/-- Transition maps are isometries of `gRound`. -/
theorem pullback_trR (R R' : Iso) {y : E 2} (hy : y ∈ tgt)
    (hy' : (chartR R).symm y ∈ (chartR R').source) :
    pullback (trR R R') gRound y = gRound y := by
  have hmem : ((chartR R).symm ≫ₕ chartR R').source ∈ 𝓝 y := by
    refine ((chartR R).symm ≫ₕ chartR R').open_source.mem_nhds ?_
    rw [OpenPartialHomeomorph.trans_source]; exact ⟨hy, hy'⟩
  have hd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (trR R R') z := by
    filter_upwards [hmem] with z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact (trR_contDiffAt R R' hz.2 (n := 1)).differentiableAt one_ne_zero
  have he : ∀ᶠ z in 𝓝 y, coordPt (trR R R' z) = (R.trans R'.symm) (coordPt z) := by
    filter_upwards [hmem] with z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    exact coordPt_trR R R' hz.2
  exact (transition_isometry (R.trans R'.symm) hd he).self_of_nhds

theorem gRound_pos {y : E 2} (hy : y ∈ tgt) (v : E 2) (hv : v ≠ 0) : 0 < gRound y v v := by
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

/-- **The round metric on the whole sphere** as a `CoordMetric`: its coordinate expression in each of the three
charts is `gRound` (the metric induced by spherical coordinates, an isometry-invariant expression). -/
def roundMetricS : CoordMetric 2 S2 where
  G _ := gRound
  diff _ _ y _ := gRound_differentiableAt y
  symm _ _ y _ v w := gRound_symm y v w
  pos e he y hy v hv := by
    obtain ⟨i, rfl⟩ := mem_atlas_iff.mp he
    exact gRound_pos hy v hv
  det e he y hy := by
    obtain ⟨i, rfl⟩ := mem_atlas_iff.mp he
    rw [det_gRound]; exact pow_ne_zero 2 (sin_pos_tgt hy).ne'
  compat e he e' he' y hy hy' := by
    obtain ⟨i, rfl⟩ := mem_atlas_iff.mp he
    obtain ⟨j, rfl⟩ := mem_atlas_iff.mp he'
    rw [trans_eq]
    exact (pullback_trR (rots j) (rots i) hy hy').symm

/-! ### Stage 5: main theorem -/

/-- **Main theorem.** On the whole sphere `S²`, with the three-chart atlas and the round metric, the
chart-independent Laplace–Beltrami operator `lapM` equals the extrinsically defined Laplacian `sphLapS` at EVERY
point `x`, for every `f` with `SphC2 f x`. -/
theorem lapM_roundS (f : S2 → ℝ) (x : S2) (hF : SphC2 f x) : lapM roundMetricS f x = sphLapS f x := by
  set R := rots (idx x)
  have hx : x ∈ src R := mem_src_idx x
  set y := toR R x with hy
  have hyT : y ∈ tgt := toR_mem R hx
  have hpt : ΨS R (y 0) (y 1) = x := invR_toR R hx
  have hs : Real.sin (y 0) ≠ 0 := (sin_pos_tgt hyT).ne'
  have key := sphLapS_eq_lapB_rot f R hs (by rw [hpt]; exact hF)
  rw [hpt, ← pt_eta y] at key
  rw [key]
  rfl

/-- In every chart of the atlas containing `x` (where `f ∘ e⁻¹` is C²), the coordinate operator of `gRound`
gives `sphLapS f x`. -/
theorem lapB_chart_roundS (f : S2 → ℝ) {e : OpenPartialHomeomorph S2 (E 2)} (he : e ∈ atlas (E 2) S2)
    {x : S2} (hx : x ∈ e.source) (hu : ContDiffAt ℝ 2 (f ∘ e.symm) (e x)) (hF : SphC2 f x) :
    lapB gRound (f ∘ e.symm) (e x) = sphLapS f x := by
  rw [← lapM_roundS f x hF]
  exact (lapM_eq_chart roundMetricS he hx hu).symm

/-- **Every chart of the maximal C² atlas of S²**, with the canonical coordinate expression of the round metric. -/
theorem lapB_coordExpr_roundS (f : S2 → ℝ) {e : OpenPartialHomeomorph S2 (E 2)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E 2) 2 S2) {x : S2} (hx : x ∈ e.source)
    (hu : ContDiffAt ℝ 2 (f ∘ e.symm) (e x)) (hF : SphC2 f x) :
    lapB (coordExpr roundMetricS e) (f ∘ e.symm) (e x) = sphLapS f x := by
  rw [← lapM_eq_coordExpr roundMetricS he hx hu, lapM_roundS f x hF]

end CTG.SphereAtlas

end

example : IsManifold 𝓘(ℝ, CTG.LaplaceBeltrami.E 2) 2 CTG.FunkHecke.S2 := inferInstance
