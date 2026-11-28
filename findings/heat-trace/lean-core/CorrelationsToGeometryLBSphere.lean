/-
Seventy-seventh Lean file (after version 4). Connects the coordinate Laplace–Beltrami operator `lapB gRound` of
`CorrelationsToGeometryLaplaceBeltrami` with the extrinsically defined Laplacian `sphLapS` of S² in both charts
`ΦS` and `ΨS R0` of `CorrelationsToGeometryFunkHeckeSphereCharts`. Written by a subagent of the author-side
session (task A190), checked here.

`bridge` (deriv of partial functions = fderiv in the coordinate directions, first and second order);
`sphLapS_eq_lapB`, `sphLapS_eq_lapB_rot` (sphLapS f = lapB gRound (f ∘ chart) for SphC2, sin θ ≠ 0);
`indMetric_coordPt` (gRound is the metric induced by spherical coordinates); `transition_isometry`;
`charts_agree`; `inv_formula`; `transition_exists` (explicit C² transition map via arccos and arg);
`charts_agree_explicit` (both charts give the same value, transition map constructed, not assumed).

NOT shown: an intrinsic Laplace–Beltrami operator of a Riemannian manifold (none in Mathlib v4.29); the transition
map only as a germ at each point, no global diffeomorphism, the charts are not Mathlib charts, uniqueness of (θ,φ)
not shown; poles (sin θ = 0) and polar points of R0Φ(y) excluded, the latter as a hypothesis; in
`charts_agree_explicit` the second chart point is only existential. No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryLaplaceBeltrami
import CorrelationsToGeometryFunkHeckeSphereCharts

open Real Filter Topology
open scoped RealInnerProductSpace

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace CTG.LBSphere

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLaplace (ext0 sphLap sphLapS extS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord (Φ ΦS A B e eθ sphLap_coord' extS_Φ ext0_Φ norm_Φ)
open CTG.FunkHecke.SphereCharts (ΨS R0 extS_RΦ ext0_comp_isometry sphLap_comp_isometry)
open CTG.LaplaceBeltrami (lapB gRound ev lapB_gRound)

/-! ### Stage 1: `deriv` of partial functions versus `fderiv` -/

section Bridge
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- First derivative along a curve of constant velocity. -/
theorem curve_d1 {u : V → ℝ} {x v : V} (hu : DifferentiableAt ℝ u x) {c : ℝ → V} {t0 : ℝ}
    (hc : ∀ t, HasDerivAt c v t) (hx : c t0 = x) :
    deriv (fun t => u (c t)) t0 = fderiv ℝ u x v := by
  have hd : DifferentiableAt ℝ u (c t0) := by rw [hx]; exact hu
  have := hd.hasFDerivAt.comp_hasDerivAt t0 (hc t0)
  rw [hx] at this
  exact this.deriv

/-- Second derivative along a curve of constant velocity. -/
theorem curve_d2 {u : V → ℝ} {x v : V} (hu : ContDiffAt ℝ 2 u x) {c : ℝ → V} {t0 : ℝ}
    (hc : ∀ t, HasDerivAt c v t) (hx : c t0 = x) :
    deriv (fun t => deriv (fun s => u (c s)) t) t0 = fderiv ℝ (fderiv ℝ u) x v v := by
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y :=
    (hu.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hcont : ContinuousAt c t0 := (hc t0).continuousAt
  have hev' : ∀ᶠ t in 𝓝 t0, DifferentiableAt ℝ u (c t) := by
    rw [← hx] at hev; exact hcont.eventually hev
  have heq : (fun t => deriv (fun s => u (c s)) t) =ᶠ[𝓝 t0] fun t => fderiv ℝ u (c t) v := by
    filter_upwards [hev'] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hc t)).deriv
  have hD : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD' : DifferentiableAt ℝ (fderiv ℝ u) (c t0) := by rw [hx]; exact hD
  have h1 : HasDerivAt (fun t => fderiv ℝ u (c t)) (fderiv ℝ (fderiv ℝ u) x v) t0 := by
    have := hD'.hasFDerivAt.comp_hasDerivAt t0 (hc t0)
    rw [hx] at this; exact this
  have h2 : HasDerivAt (fun t => fderiv ℝ u (c t) v) (fderiv ℝ (fderiv ℝ u) x v v) t0 := by
    have := h1.clm_apply (hasDerivAt_const t0 v)
    simpa using this
  exact (h2.congr_of_eventuallyEq heq).deriv

end Bridge

theorem hasDerivAt_c0 (φ t : ℝ) : HasDerivAt (fun s : ℝ => (![s, φ] : Fin 2 → ℝ)) (ev 0) t := by
  rw [hasDerivAt_pi]; intro i; fin_cases i
  · simpa [ev] using hasDerivAt_id t
  · simpa [ev] using hasDerivAt_const t φ

theorem hasDerivAt_c1 (θ t : ℝ) : HasDerivAt (fun s : ℝ => (![θ, s] : Fin 2 → ℝ)) (ev 1) t := by
  rw [hasDerivAt_pi]; intro i; fin_cases i
  · simpa [ev] using hasDerivAt_const t θ
  · simpa [ev] using hasDerivAt_id t

/-- **Bridge.** For `u` C² at `(θ,φ)`, the four `fderiv` expressions of `lapB_gRound` are the `deriv` of the partial
functions. -/
theorem bridge {u : (Fin 2 → ℝ) → ℝ} {θ φ : ℝ} (hu : ContDiffAt ℝ 2 u ![θ, φ]) :
    deriv (fun t => u ![t, φ]) θ = fderiv ℝ u ![θ, φ] (ev 0) ∧
    deriv (fun t => u ![θ, t]) φ = fderiv ℝ u ![θ, φ] (ev 1) ∧
    deriv (fun t => deriv (fun s => u ![s, φ]) t) θ = fderiv ℝ (fderiv ℝ u) ![θ, φ] (ev 0) (ev 0) ∧
    deriv (fun t => deriv (fun s => u ![θ, s]) t) φ = fderiv ℝ (fderiv ℝ u) ![θ, φ] (ev 1) (ev 1) := by
  have hd : DifferentiableAt ℝ u ![θ, φ] := hu.differentiableAt (by norm_num)
  exact ⟨curve_d1 hd (hasDerivAt_c0 φ) rfl, curve_d1 hd (hasDerivAt_c1 θ) rfl,
    curve_d2 hu (hasDerivAt_c0 φ) rfl, curve_d2 hu (hasDerivAt_c1 θ) rfl⟩

/-! ### Stage 2: `sphLapS = lapB gRound` in both charts -/

/-- Spherical coordinates as a map on `Fin 2 → ℝ`. -/
def coordPt (y : Fin 2 → ℝ) : E3 := Φ (y 0) (y 1)

theorem coordPt_contDiff : ContDiff ℝ 2 coordPt := by
  unfold coordPt Φ A; fun_prop

/-- `u = f ∘ Φ` on `Fin 2 → ℝ`. -/
def uΦ (f : S2 → ℝ) (y : Fin 2 → ℝ) : ℝ := f (ΦS (y 0) (y 1))

/-- `u = f ∘ Ψ_R` on `Fin 2 → ℝ`. -/
def uΨ (f : S2 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) (y : Fin 2 → ℝ) : ℝ := f (ΨS R (y 0) (y 1))

theorem ext0_unit (g : E3 → ℝ) {z : E3} (hz : ‖z‖ = 1) : ext0 g z = g z := by
  unfold ext0; rw [hz, inv_one, one_smul]

theorem uΦ_eq (f : S2 → ℝ) : uΦ f = ext0 (extS f) ∘ coordPt := by
  funext y; simp only [Function.comp, coordPt, uΦ, ext0_Φ, extS_Φ]

theorem uΨ_eq (f : S2 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) : uΨ f R = (ext0 (extS f) ∘ R) ∘ coordPt := by
  funext y
  simp only [Function.comp, coordPt, uΨ]
  rw [ext0_unit _ (by rw [LinearIsometryEquiv.norm_map, norm_Φ])]
  exact (extS_RΦ f R (y 0) (y 1)).symm

theorem uΦ_contDiffAt (f : S2 → ℝ) {θ φ : ℝ} (hF : SphC2 f (ΦS θ φ)) :
    ContDiffAt ℝ 2 (uΦ f) ![θ, φ] := by
  rw [uΦ_eq]
  have h1 : ContDiffAt ℝ 2 (ext0 (extS f)) (coordPt ![θ, φ]) := hF
  exact h1.comp _ coordPt_contDiff.contDiffAt

theorem uΨ_contDiffAt (f : S2 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) {θ φ : ℝ} (hF : SphC2 f (ΨS R θ φ)) :
    ContDiffAt ℝ 2 (uΨ f R) ![θ, φ] := by
  rw [uΨ_eq]
  have h1 : ContDiffAt ℝ 2 (ext0 (extS f)) (R (coordPt ![θ, φ])) := hF
  exact (h1.comp _ R.toContinuousLinearEquiv.contDiff.contDiffAt).comp _ coordPt_contDiff.contDiffAt

/-- Coordinate formula (non-divergence form) in the rotated chart. -/
theorem sphLapS_coord_rot' (f : S2 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) {θ φ : ℝ} (hs : sin θ ≠ 0)
    (hF : SphC2 f (ΨS R θ φ)) :
    sphLapS f (ΨS R θ φ) =
      deriv (fun a => deriv (fun b => f (ΨS R b φ)) a) θ
        + cos θ / sin θ * deriv (fun b => f (ΨS R b φ)) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΨS R θ b)) a) φ := by
  unfold sphLapS
  rw [show ((ΨS R θ φ : S2) : E3) = R (Φ θ φ) from rfl, ← sphLap_comp_isometry]
  have hF' : ContDiffAt ℝ 2 (ext0 (extS f ∘ R)) (Φ θ φ) := by
    rw [ext0_comp_isometry]
    have h1 : ContDiffAt ℝ 2 (ext0 (extS f)) (R (Φ θ φ)) := hF
    exact h1.comp (Φ θ φ) (R.toContinuousLinearEquiv.contDiff.contDiffAt)
  rw [sphLap_coord' (extS f ∘ R) hs hF']
  simp only [extS_RΦ]

theorem sphLapS_coord' (f : S2 → ℝ) {θ φ : ℝ} (hs : sin θ ≠ 0) (hF : SphC2 f (ΦS θ φ)) :
    sphLapS f (ΦS θ φ) =
      deriv (fun a => deriv (fun b => f (ΦS b φ)) a) θ
        + cos θ / sin θ * deriv (fun b => f (ΦS b φ)) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΦS θ b)) a) φ := by
  unfold sphLapS
  rw [show ((ΦS θ φ : S2) : E3) = Φ θ φ from rfl, sphLap_coord' (extS f) hs hF]
  simp only [extS_Φ]

/-- Generic assembly: the `deriv`-form coordinate formula of `u` equals `lapB gRound u`. -/
theorem coord_eq_lapB {u : (Fin 2 → ℝ) → ℝ} {θ φ : ℝ} (hs : sin θ ≠ 0) (hu : ContDiffAt ℝ 2 u ![θ, φ]) :
    deriv (fun a => deriv (fun b => u ![b, φ]) a) θ
        + cos θ / sin θ * deriv (fun b => u ![b, φ]) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => u ![θ, b]) a) φ
      = lapB gRound u ![θ, φ] := by
  obtain ⟨h1, -, h3, h4⟩ := bridge hu
  have h0 : Real.sin ((![θ, φ] : Fin 2 → ℝ) 0) ≠ 0 := by simpa using hs
  rw [lapB_gRound u h0, h1, h3, h4]
  simp

/-- **Main statement, chart Φ.** `sphLapS f (Φ(θ,φ)) = lapB gRound (f ∘ Φ) (θ,φ)` for `SphC2 f` at `Φ(θ,φ)` and
`sin θ ≠ 0`. -/
theorem sphLapS_eq_lapB (f : S2 → ℝ) {θ φ : ℝ} (hs : sin θ ≠ 0) (hF : SphC2 f (ΦS θ φ)) :
    sphLapS f (ΦS θ φ) = lapB gRound (uΦ f) ![θ, φ] := by
  rw [sphLapS_coord' f hs hF, ← coord_eq_lapB hs (uΦ_contDiffAt f hF)]
  rfl

/-- **Main statement, rotated chart Ψ_R** (any linear isometry `R`, in particular `R0`). -/
theorem sphLapS_eq_lapB_rot (f : S2 → ℝ) (R : E3 ≃ₗᵢ[ℝ] E3) {θ φ : ℝ} (hs : sin θ ≠ 0)
    (hF : SphC2 f (ΨS R θ φ)) :
    sphLapS f (ΨS R θ φ) = lapB gRound (uΨ f R) ![θ, φ] := by
  rw [sphLapS_coord_rot' f R hs hF, ← coord_eq_lapB hs (uΨ_contDiffAt f R hF)]
  rfl

end CTG.LBSphere

/-! ### Stage 3: the transition map is an isometry of `gRound`; agreement via `lapB_isometry` -/

namespace CTG.LBSphere

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLaplace (ext0 sphLap sphLapS extS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord (Φ ΦS A B e eθ frame frame_orthonormal hasDerivAt_Φθ hasDerivAt_Φφ)
open CTG.FunkHecke.SphereCharts (ΨS R0)
open CTG.LaplaceBeltrami (lapB gRound ev lapB_gRound pullback lapB_isometry mat amat gDiag mat_gDiag
  mat_comp vec_expand)

/-- Metric induced on coordinates by a map into `ℝ³`: `(v,w) ↦ ⟪DP v, DP w⟫`. -/
def indMetric (P : (Fin 2 → ℝ) → E3) (y : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ : E3 →L[ℝ] E3 →L[ℝ] ℝ).bilinearComp (fderiv ℝ P y) (fderiv ℝ P y)

theorem indMetric_apply (P : (Fin 2 → ℝ) → E3) (y v w : Fin 2 → ℝ) :
    indMetric P y v w = ⟪fderiv ℝ P y v, fderiv ℝ P y w⟫ := rfl

theorem indMetric_comp {P : (Fin 2 → ℝ) → E3} {ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {z : Fin 2 → ℝ}
    (hP : DifferentiableAt ℝ P (ψ z)) (hψ : DifferentiableAt ℝ ψ z) :
    indMetric (P ∘ ψ) z = pullback ψ (indMetric P) z := by
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  simp only [indMetric_apply, pullback, ContinuousLinearMap.bilinearComp_apply, fderiv_comp z hP hψ,
    ContinuousLinearMap.coe_comp', Function.comp_apply]

theorem indMetric_isometry (R : E3 ≃ₗᵢ[ℝ] E3) {P : (Fin 2 → ℝ) → E3} {z : Fin 2 → ℝ}
    (hP : DifferentiableAt ℝ P z) : indMetric (R ∘ P) z = indMetric P z := by
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  have h : fderiv ℝ (R ∘ P) z = (R.toContinuousLinearEquiv : E3 →L[ℝ] E3).comp (fderiv ℝ P z) :=
    fderiv_comp z (R.toContinuousLinearEquiv : E3 →L[ℝ] E3).differentiableAt hP |>.trans (by
      rw [ContinuousLinearMap.fderiv])
  simp only [indMetric_apply, h, ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact LinearIsometryEquiv.inner_map_map R _ _

theorem pt_eta (y : Fin 2 → ℝ) : y = ![y 0, y 1] := by ext i; fin_cases i <;> rfl

theorem fderiv_coordPt_0' (θ φ : ℝ) : fderiv ℝ coordPt ![θ, φ] (ev 0) = eθ θ φ := by
  have hd : DifferentiableAt ℝ coordPt ![θ, φ] := coordPt_contDiff.differentiable (by norm_num) _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_c0 φ θ)
  have h2 : HasDerivAt (fun t => coordPt ![t, φ]) (eθ θ φ) θ := by
    simpa [coordPt] using hasDerivAt_Φθ θ φ
  exact h1.unique h2

theorem fderiv_coordPt_1' (θ φ : ℝ) : fderiv ℝ coordPt ![θ, φ] (ev 1) = sin θ • B φ := by
  have hd : DifferentiableAt ℝ coordPt ![θ, φ] := coordPt_contDiff.differentiable (by norm_num) _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt φ (hasDerivAt_c1 θ φ)
  have h2 : HasDerivAt (fun t => coordPt ![θ, t]) (sin θ • B φ) φ := by
    simpa [coordPt] using hasDerivAt_Φφ θ φ
  exact h1.unique h2

theorem fderiv_coordPt_0 (y : Fin 2 → ℝ) : fderiv ℝ coordPt y (ev 0) = eθ (y 0) (y 1) := by
  have := fderiv_coordPt_0' (y 0) (y 1); rwa [← pt_eta y] at this

theorem fderiv_coordPt_1 (y : Fin 2 → ℝ) : fderiv ℝ coordPt y (ev 1) = sin (y 0) • B (y 1) := by
  have := fderiv_coordPt_1' (y 0) (y 1); rwa [← pt_eta y] at this

/-- **The round metric is the metric induced by spherical coordinates.** -/
theorem indMetric_coordPt (y : Fin 2 → ℝ) : indMetric coordPt y = gRound y := by
  have ho := orthonormal_iff_ite.mp (frame_orthonormal (y 0) (y 1))
  have h11 : ⟪eθ (y 0) (y 1), eθ (y 0) (y 1)⟫ = 1 := by simpa [frame] using ho 1 1
  have h12 : ⟪eθ (y 0) (y 1), B (y 1)⟫ = 0 := by simpa [frame] using ho 1 2
  have h21 : ⟪B (y 1), eθ (y 0) (y 1)⟫ = 0 := by simpa [frame] using ho 2 1
  have h22 : ⟪B (y 1), B (y 1)⟫ = 1 := by simpa [frame] using ho 2 2
  refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
  have hv : v = v 0 • ev 0 + v 1 • ev 1 := by ext i; fin_cases i <;> simp [ev]
  have hw : w = w 0 • ev 0 + w 1 • ev 1 := by ext i; fin_cases i <;> simp [ev]
  rw [indMetric_apply]
  conv_lhs => rw [hv, hw]
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, fderiv_coordPt_0, fderiv_coordPt_1]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h11, h12,
    h21, h22]
  simp [gRound, gDiag, CTG.LaplaceBeltrami.sq]
  ring

end CTG.LBSphere

namespace CTG.LBSphere

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord (Φ ΦS)
open CTG.FunkHecke.SphereCharts (ΨS R0)
open CTG.LaplaceBeltrami (lapB gRound ev pullback lapB_isometry mat amat gDiag mat_gDiag mat_comp)

/-- Abstract form (instance search on `Bil 2` fails for `IsBoundedSMul` otherwise). -/
theorem diff_const_add_smul {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] {s : V → ℝ} {x : V} (hs : DifferentiableAt ℝ s x) (C B : W) :
    DifferentiableAt ℝ (fun x => C + s x • B) x := (differentiableAt_const C).add (hs.smul_const B)

theorem gRound_differentiableAt (x : Fin 2 → ℝ) : DifferentiableAt ℝ gRound x := by
  have hs : DifferentiableAt ℝ (fun x : Fin 2 → ℝ => Real.sin (x 0) ^ 2) x := by fun_prop
  exact diff_const_add_smul hs (CTG.LaplaceBeltrami.sq 0) (CTG.LaplaceBeltrami.sq 1)

theorem gRound_symm (x v w : Fin 2 → ℝ) : gRound x v w = gRound x w v := by
  simp [gRound, gDiag, CTG.LaplaceBeltrami.sq]; ring

theorem det_gRound (x : Fin 2 → ℝ) : (mat (gRound x)).det = sin (x 0) ^ 2 := by
  rw [gRound, mat_gDiag]; simp [Matrix.det_diagonal, Fin.prod_univ_two]

theorem lapB_congr {G : (Fin 2 → ℝ) → CTG.LaplaceBeltrami.Bil 2} {u v : (Fin 2 → ℝ) → ℝ}
    {x : Fin 2 → ℝ} (h : u =ᶠ[𝓝 x] v) : lapB G u x = lapB G v x := by
  unfold lapB; rw [h.fderiv_eq, h.fderiv.fderiv_eq]

/-- **The transition map is an isometry of the round metric.** If `ψ` is differentiable near `y` and
`Φ(ψ z) = R(Φ z)` near `y` for a linear isometry `R`, then `ψ* gRound = gRound` near `y`. -/
theorem transition_isometry (R : E3 ≃ₗᵢ[ℝ] E3) {ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {y : Fin 2 → ℝ}
    (hψd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ ψ z)
    (heq : ∀ᶠ z in 𝓝 y, coordPt (ψ z) = R (coordPt z)) :
    pullback ψ gRound =ᶠ[𝓝 y] gRound := by
  have hcd : ∀ y, DifferentiableAt ℝ coordPt y := fun y => coordPt_contDiff.differentiable (by norm_num) y
  have hind : indMetric coordPt = gRound := funext indMetric_coordPt
  filter_upwards [hψd, heq.eventually_nhds] with z hz hz'
  have hfun : coordPt ∘ ψ =ᶠ[𝓝 z] R ∘ coordPt := hz'
  calc pullback ψ gRound z = pullback ψ (indMetric coordPt) z := by rw [hind]
    _ = indMetric (coordPt ∘ ψ) z := (indMetric_comp (hcd _) hz).symm
    _ = indMetric (R ∘ coordPt) z := by simp only [indMetric, hfun.fderiv_eq]
    _ = indMetric coordPt z := indMetric_isometry R (hcd z)
    _ = gRound z := indMetric_coordPt z

/-- An isometry of `gRound` has invertible derivative where `sin θ ≠ 0`. -/
theorem det_ne_of_iso {ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {y : Fin 2 → ℝ}
    (hiso : pullback ψ gRound y = gRound y) (hs : sin (y 0) ≠ 0) :
    (amat (fderiv ℝ ψ y)).det ≠ 0 := by
  intro h0
  have h := congrArg (fun B => (mat B).det) hiso
  simp only [pullback, mat_comp, Matrix.det_mul, Matrix.det_transpose, h0, det_gRound] at h
  exact pow_ne_zero 2 hs (by simpa using h.symm)

/-- **Agreement of the two charts through `lapB_isometry`.** HYPOTHESIS (not constructed here): a transition map
`ψ`, C² at `y`, with `Φ(ψ z) = R₀(Φ z)` near `y`. Then the two coordinate expressions of the Laplace–Beltrami operator
of the round metric agree: `lapB gRound (f ∘ Ψ_{R₀}) y = lapB gRound (f ∘ Φ) (ψ y)`. -/
theorem charts_agree (f : S2 → ℝ) {ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {y : Fin 2 → ℝ}
    (hψ : ContDiffAt ℝ 2 ψ y) (heq : ∀ᶠ z in 𝓝 y, coordPt (ψ z) = R0 (coordPt z))
    (hs : sin (y 0) ≠ 0) (hs' : sin (ψ y 0) ≠ 0) (hF : SphC2 f (ΦS (ψ y 0) (ψ y 1))) :
    lapB gRound (uΨ f R0) y = lapB gRound (uΦ f) (ψ y) := by
  have hψd : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ ψ z :=
    (hψ.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hiso := transition_isometry R0 hψd heq
  have hu : ContDiffAt ℝ 2 (uΦ f) (ψ y) := by
    have := uΦ_contDiffAt f hF; rwa [← pt_eta (ψ y)] at this
  have hfun : uΦ f ∘ ψ =ᶠ[𝓝 y] uΨ f R0 := by
    filter_upwards [heq] with z hz
    exact congrArg f (Subtype.ext hz)
  rw [← lapB_congr hfun]
  exact lapB_isometry hψ (det_ne_of_iso hiso.self_of_nhds hs) hu (gRound_differentiableAt _)
    (gRound_symm _) (by rw [det_gRound]; exact pow_ne_zero 2 hs') hiso

end CTG.LBSphere

/-! ### Stage 3b: an explicit C² transition map between the charts `Ψ_{R₀}` and `Φ` -/

namespace CTG.LBSphere

open CTG.FunkHecke (S2 E3)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.SphereCoord (Φ ΦS norm_Φ)
open CTG.FunkHecke.SphereCharts (ΨS R0 Φ_apply ext_E3 norm_sq_E3)
open CTG.LaplaceBeltrami (lapB gRound)

/-- The complex number `w₀ + i w₁`. -/
def cpx (w : E3) : ℂ := (w 0 : ℂ) + (w 1 : ℂ) * Complex.I

theorem cpx_normSq (w : E3) : ‖cpx w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp [cpx]; ring

/-- Inverse of spherical coordinates on the non-polar part, with a free reference angle `φ₀`. -/
def invPt (φ0 : ℝ) (w : E3) : Fin 2 → ℝ :=
  ![Real.arccos (w 2), φ0 + Complex.arg (cpx w * Complex.exp (-(φ0 * Complex.I)))]

theorem inv_formula (w : E3) (hw : ‖w‖ = 1) (h2 : w 2 ^ 2 < 1) (φ0 : ℝ) :
    coordPt (invPt φ0 w) = w := by
  have hn := norm_sq_E3 w
  rw [hw] at hn
  have hlo : -1 < w 2 := by nlinarith
  have hhi : w 2 < 1 := by nlinarith
  set c := cpx w with hcdef
  set d := c * Complex.exp (-(φ0 * Complex.I)) with hddef
  set α := Complex.arg d with hα
  have hnd : ‖d‖ = ‖c‖ := by
    rw [hddef, norm_mul, show -((φ0 : ℂ) * Complex.I) = ((-φ0 : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hcd : c = d * Complex.exp (φ0 * Complex.I) := by
    rw [hddef, mul_assoc, ← Complex.exp_add]; simp
  have hc2 : c = (‖d‖ : ℂ) * Complex.exp (((φ0 + α : ℝ) : ℂ) * Complex.I) := by
    rw [hcd]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I d]
    rw [mul_assoc, ← Complex.exp_add, ← hα]; push_cast; ring_nf
  have hre : w 0 = ‖d‖ * Real.cos (φ0 + α) := by
    have := congrArg Complex.re hc2
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at this
    simpa [hcdef, cpx] using this
  have him : w 1 = ‖d‖ * Real.sin (φ0 + α) := by
    have := congrArg Complex.im hc2
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at this
    simpa [hcdef, cpx] using this
  have hs : Real.sin (Real.arccos (w 2)) = ‖d‖ := by
    rw [Real.sin_arccos, hnd, ← Real.sqrt_sq (norm_nonneg c), cpx_normSq]
    congr 1; linarith
  have hco : Real.cos (Real.arccos (w 2)) = w 2 := Real.cos_arccos hlo.le hhi.le
  obtain ⟨p0, p1, p2⟩ := Φ_apply (Real.arccos (w 2)) (φ0 + α)
  show Φ (invPt φ0 w 0) (invPt φ0 w 1) = w
  have e0 : invPt φ0 w 0 = Real.arccos (w 2) := rfl
  have e1 : invPt φ0 w 1 = φ0 + α := rfl
  rw [e0, e1]
  apply ext_E3
  · rw [p0, hs, hre]
  · rw [p1, hs, him]
  · rw [p2, hco]

/-- `R₀ ∘ Φ` in coordinates. -/
def Wpt (z : Fin 2 → ℝ) : E3 := R0 (coordPt z)

theorem Wpt_contDiff : ContDiff ℝ 2 Wpt :=
  R0.toContinuousLinearEquiv.contDiff.comp coordPt_contDiff

theorem Wpt_comp_contDiff (i : Fin 3) : ContDiff ℝ 2 (fun z => Wpt z i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).contDiff.comp Wpt_contDiff

theorem norm_Wpt (z : Fin 2 → ℝ) : ‖Wpt z‖ = 1 := by
  rw [Wpt, LinearIsometryEquiv.norm_map]; exact norm_Φ _ _

theorem cpx_contDiff : ContDiff ℝ 2 (fun z => cpx (Wpt z)) := by
  unfold cpx
  have h0 := Complex.ofRealCLM.contDiff.comp (Wpt_comp_contDiff 0)
  have h1 := Complex.ofRealCLM.contDiff.comp (Wpt_comp_contDiff 1)
  exact h0.add (h1.mul contDiff_const)

set_option backward.isDefEq.respectTransparency false in
theorem arg_contDiffAt {p : ℂ} (hp : p ∈ Complex.slitPlane) : ContDiffAt ℝ 2 Complex.arg p := by
  have h : Complex.arg = fun x => Complex.imCLM (Complex.log x) := by
    funext x; simp [Complex.log_im]
  rw [h]
  have hl : ContDiffAt ℝ 2 Complex.log p := (Complex.contDiffAt_log hp).restrict_scalars ℝ
  exact Complex.imCLM.contDiff.contDiffAt.comp p hl

/-- **Existence of a C² transition map.** At a point `y` with `R₀Φ(y)` non-polar, `ψ = invPt φ₀ ∘ R₀ ∘ Φ` (with
`φ₀ = arg` of the base point) is C² at `y` and satisfies `Φ(ψ z) = R₀(Φ z)` near `y`; moreover `sin` of its first
coordinate does not vanish at `y`. -/
theorem transition_exists {y : Fin 2 → ℝ} (hpol : Wpt y 2 ^ 2 < 1) :
    ∃ ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ), ContDiffAt ℝ 2 ψ y ∧
      (∀ᶠ z in 𝓝 y, coordPt (ψ z) = R0 (coordPt z)) ∧ Real.sin (ψ y 0) ≠ 0 := by
  set φ0 := Complex.arg (cpx (Wpt y))
  have hn := norm_sq_E3 (Wpt y)
  rw [norm_Wpt] at hn
  have hlo : -1 < Wpt y 2 := by nlinarith
  have hhi : Wpt y 2 < 1 := by nlinarith
  have hc0 : cpx (Wpt y) ≠ 0 := by
    intro h
    have := cpx_normSq (Wpt y); rw [h, norm_zero] at this; nlinarith
  refine ⟨fun z => invPt φ0 (Wpt z), ?_, ?_, ?_⟩
  · -- smoothness
    have hA0 : ContDiffAt ℝ 2 Real.arccos (Wpt y 2) := Real.contDiffAt_arccos hlo.ne' hhi.ne
    have hA : ContDiffAt ℝ 2 (fun z => Real.arccos (Wpt z 2)) y :=
      hA0.comp (f := fun z => Wpt z 2) y (Wpt_comp_contDiff 2).contDiffAt
    have hmem : cpx (Wpt y) * Complex.exp (-(φ0 * Complex.I)) ∈ Complex.slitPlane := by
      have h1 := Complex.norm_mul_exp_arg_mul_I (cpx (Wpt y))
      have h2 : cpx (Wpt y) * Complex.exp (-(φ0 * Complex.I)) = (‖cpx (Wpt y)‖ : ℂ) := by
        conv_lhs => rw [← h1]
        rw [mul_assoc, ← Complex.exp_add]; simp [φ0]
      rw [h2, Complex.ofReal_mem_slitPlane]; exact norm_pos_iff.mpr hc0
    have hB : ContDiffAt ℝ 2
        (fun z => φ0 + Complex.arg (cpx (Wpt z) * Complex.exp (-(φ0 * Complex.I)))) y :=
      contDiffAt_const.add ((arg_contDiffAt hmem).comp
        (f := fun z => cpx (Wpt z) * Complex.exp (-(φ0 * Complex.I))) y
        (cpx_contDiff.mul (contDiff_const (c := Complex.exp (-(φ0 * Complex.I))))).contDiffAt)
    rw [contDiffAt_pi]
    intro i; fin_cases i
    · simpa [invPt] using hA
    · simpa [invPt] using hB
  · -- the equation, near `y`
    have hcont : ContinuousAt (fun z => Wpt z 2) y := (Wpt_comp_contDiff 2).continuous.continuousAt
    have hopen : IsOpen {t : ℝ | t ^ 2 < 1} := isOpen_lt (continuous_pow 2) continuous_const
    filter_upwards [hcont.preimage_mem_nhds (hopen.mem_nhds hpol)] with z hz
    exact inv_formula (Wpt z) (norm_Wpt z) hz φ0
  · -- `sin θ ≠ 0` at the image point
    show Real.sin (Real.arccos (Wpt y 2)) ≠ 0
    rw [Real.sin_arccos]
    exact (Real.sqrt_pos.mpr (by nlinarith)).ne'

/-- **Agreement of the two charts, transition map constructed.** At every `y` with `sin y₀ ≠ 0` and `R₀Φ(y)`
non-polar, and every `f` with `SphC2 f` at `Ψ_{R₀}(y)`, there is a C² transition map `ψ` (`Φ ∘ ψ = R₀ ∘ Φ` near `y`)
and the two coordinate expressions of the Laplace–Beltrami operator of the round metric agree. -/
theorem charts_agree_explicit (f : S2 → ℝ) {y : Fin 2 → ℝ} (hs : Real.sin (y 0) ≠ 0)
    (hpol : (R0 (coordPt y)) 2 ^ 2 < 1) (hF : SphC2 f (ΨS R0 (y 0) (y 1))) :
    ∃ ψ : (Fin 2 → ℝ) → (Fin 2 → ℝ), ContDiffAt ℝ 2 ψ y ∧
      (∀ᶠ z in 𝓝 y, coordPt (ψ z) = R0 (coordPt z)) ∧
      lapB gRound (uΨ f R0) y = lapB gRound (uΦ f) (ψ y) := by
  obtain ⟨ψ, hψ, heq, hs'⟩ := transition_exists (y := y) hpol
  refine ⟨ψ, hψ, heq, charts_agree f hψ heq hs hs' ?_⟩
  have hpt : ΦS (ψ y 0) (ψ y 1) = ΨS R0 (y 0) (y 1) := Subtype.ext heq.self_of_nhds
  rw [hpt]; exact hF

end CTG.LBSphere

end

