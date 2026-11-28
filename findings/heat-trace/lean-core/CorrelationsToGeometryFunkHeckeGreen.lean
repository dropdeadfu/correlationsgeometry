/-
Sixty-ninth file (A182, written by a subagent of the author-side session, checked by that session; read by nobody else).
Green's identity on `S²` for the extrinsically defined Laplacian `sphLapS`, commutation of projection and Laplacian,
and decay of the projections from smoothness without hypothesis. Namespace `CTG.FunkHecke.Green`; imports the compiled
module of the sixty-eighth file (`CorrelationsToGeometryFunkHeckeParseval`). Check with `./check_funk_hecke_green.sh`.

Main statements: `sym_S2` (∫ g·Δf dσ = ∫ f·Δg dσ for f, g with `SphC2` everywhere), `green_harmonic`, `harm_lap`,
`proj_lap` (Π_l(Δf) = −l(l+1)·Π_l f), `decay_sup_smooth`, `decay_sup_fin`
((l(l+1))^k·|Π_l f(x)| ≤ √(2l+1)·√(∫ (Δ^k f)² dσ) if the iterates Δ^j f, j < k, satisfy `SphC2` everywhere).
Route: radial cut-off w(y) = ψ(‖y‖²) on a shell, integration by parts in ℝ³ (Mathlib), Euler's identity for
degree-0 extensions, scaling of the Laplacian, polar coordinates.
NOT shown: that `sphLapS` is the intrinsic Laplace–Beltrami operator of `S²`; weak/Sobolev versions; the link of the
decay bound to `degM` of `LB_sphere_series_M` (uniform convergence of Σ Π_l f for smooth f). No sorry, no axiom,
no native_decide.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeParseval

open MeasureTheory Set Metric Real Filter Topology
open scoped RealInnerProductSpace
open Laplacian

namespace CTG.FunkHecke.Green

open CTG.FunkHecke (S2 E3 cdot Isotropic zonalOp sigma sigma0 integral_sigma polar_mul)
open CTG.FunkHecke.SphereLaplace (ext0 sphLap extS sphLapS lap_eq_sum euler_of_homogeneous)
open CTG.FunkHecke.SphereLinComb (SphC2 S2_ne_zero sphC2_re sphC2_im)

local instance : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

local instance : IsProbabilityMeasure sigma :=
  ⟨by rw [← ofReal_measureReal, CTG.FunkHecke.Proj.sigma_real_univ', ENNReal.ofReal_one]⟩

local notation "bE" => EuclideanSpace.basisFun (Fin 3) ℝ

/-! ## (A) Degree-zero extensions and `C²` away from the origin -/

theorem ext0_hom (g : E3 → ℝ) {r : ℝ} (hr : 0 < r) (y : E3) : ext0 g (r • y) = ext0 g y := by
  unfold ext0
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul]
    congr 2
    field_simp

theorem ext0_on_S2 (f : S2 → ℝ) (x : S2) : ext0 (extS f) (x : E3) = f x := by
  have hx1 : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  simp [ext0, extS, hx1]

/-- `C²` at every point of `ℝ³ ∖ {0}`. -/
def C2off (U : E3 → ℝ) : Prop := ∀ y : E3, y ≠ 0 → ContDiffAt ℝ 2 U y

/-- `SphC2` on all of `S²` gives `C²` of the degree-zero extension on `ℝ³ ∖ {0}`. -/
theorem c2off_ext0 {f : S2 → ℝ} (hf : ∀ x : S2, SphC2 f x) : C2off (ext0 (extS f)) := by
  intro y hy
  set U := ext0 (extS f)
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hm : ‖y‖⁻¹ • y ∈ S2 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hU : ContDiffAt ℝ 2 U (‖y‖⁻¹ • y) := hf ⟨_, hm⟩
  have hN : ContDiffAt ℝ 2 (fun z : E3 => ‖z‖⁻¹ • z) y :=
    ((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.mpr hy)).smul contDiffAt_id
  have hc : ContDiffAt ℝ 2 (fun z : E3 => U (‖z‖⁻¹ • z)) y :=
    ContDiffAt.comp (g := U) (f := fun z : E3 => ‖z‖⁻¹ • z) y hU hN
  have heq : (fun z : E3 => U (‖z‖⁻¹ • z)) =ᶠ[𝓝 y] U := by
    filter_upwards [isOpen_ne.mem_nhds hy] with z hz
    exact ext0_hom _ (inv_pos.2 (norm_pos_iff.2 hz)) z
  exact hc.congr_of_eventuallyEq heq.symm

theorem C2off.contOn {U : E3 → ℝ} (h : C2off U) : ContinuousOn U {0}ᶜ :=
  fun y hy => (h y hy).continuousAt.continuousWithinAt

theorem C2off.cdo {U : E3 → ℝ} (h : C2off U) : ContDiffOn ℝ 2 U {0}ᶜ :=
  fun y hy => (h y hy).contDiffWithinAt

theorem C2off.d1 {U : E3 → ℝ} (h : C2off U) : ContDiffOn ℝ 1 (fderiv ℝ U) {0}ᶜ :=
  h.cdo.fderiv_of_isOpen isOpen_compl_singleton (by norm_num)

theorem C2off.d1_contOn {U : E3 → ℝ} (h : C2off U) (v : E3) :
    ContinuousOn (fun y => fderiv ℝ U y v) {0}ᶜ :=
  h.d1.continuousOn.clm_apply continuousOn_const

theorem C2off.d2_contOn {U : E3 → ℝ} (h : C2off U) (v w : E3) :
    ContinuousOn (fun y => fderiv ℝ (fderiv ℝ U) y v w) {0}ᶜ := by
  have h2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ U)) {0}ᶜ :=
    h.d1.fderiv_of_isOpen isOpen_compl_singleton (by norm_num)
  exact (h2.continuousOn.clm_apply continuousOn_const).clm_apply continuousOn_const

theorem C2off.lap_contOn {U : E3 → ℝ} (h : C2off U) : ContinuousOn (Δ U) {0}ᶜ := by
  have e : Δ U = fun y => ∑ i, fderiv ℝ (fderiv ℝ U) y (bE i) (bE i) := funext (lap_eq_sum U)
  rw [e]
  exact continuousOn_finset_sum _ fun i _ => h.d2_contOn (bE i) (bE i)

theorem C2off.hasFDerivAt2 {U : E3 → ℝ} (h : C2off U) {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (fderiv ℝ U) (fderiv ℝ (fderiv ℝ U) y) y :=
  (((h y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt

/-! ## (B) Cut-offs -/

theorem cut_integrable {c h : E3 → ℝ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (h0 : (0:E3) ∉ tsupport c) (hh : ContinuousOn h {0}ᶜ) :
    Integrable (fun y => c y * h y) := by
  have hcont : Continuous (fun y => c y * h y) := by
    rw [continuous_iff_continuousAt]; intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have hz : c =ᶠ[𝓝 (0:E3)] 0 := (notMem_tsupport_iff_eventuallyEq).1 h0
      have : (fun y => c y * h y) =ᶠ[𝓝 (0:E3)] fun _ => (0:ℝ) := by
        filter_upwards [hz] with y hy; simp [hy]
      exact (continuousAt_const).congr this.symm
    · exact hc.continuousAt.mul (hh.continuousAt (isOpen_compl_singleton.mem_nhds hx))
  exact hcont.integrable_of_hasCompactSupport (hcs.mul_right (f' := h))

/-- The radial profile: a bump around `1` with inner radius `1/4`, outer radius `1/2`. -/
noncomputable def psiB : ContDiffBump (1:ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

theorem psiB_rIn : psiB.rIn = 1/4 := rfl
theorem psiB_rOut : psiB.rOut = 1/2 := rfl

/-- The cut-off `w(y) = ψ(‖y‖²)`. -/
noncomputable def wcut (y : E3) : ℝ := psiB (‖y‖ ^ 2)

theorem wcut_contDiff : ContDiff ℝ (2 : ℕ∞) wcut :=
  (psiB.contDiff (n := 2)).comp (contDiff_norm_sq ℝ)

theorem wcut_zero_of {y : E3} (h : 1/2 ≤ |‖y‖ ^ 2 - 1|) : wcut y = 0 := by
  unfold wcut; apply psiB.zero_of_le_dist; rw [psiB_rOut, Real.dist_eq]; exact h

theorem wcut_notMem : (0:E3) ∉ tsupport wcut := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have hc : ContinuousAt (fun y : E3 => ‖y‖ ^ 2) 0 := (continuous_norm.pow 2).continuousAt
  have hev : ∀ᶠ y in 𝓝 (0:E3), ‖y‖ ^ 2 < 1/2 :=
    hc.eventually_lt continuousAt_const (by simp)
  filter_upwards [hev] with y hy
  apply wcut_zero_of
  rw [abs_of_neg (by linarith)]; linarith

theorem wcut_ne_zero {y : E3} (hy : y ∈ tsupport wcut) : y ≠ 0 := by
  rintro rfl; exact wcut_notMem hy

theorem wcut_hcs : HasCompactSupport wcut := by
  refine HasCompactSupport.intro (isCompact_closedBall (0:E3) 2) fun y hy => ?_
  rw [mem_closedBall, dist_zero_right, not_le] at hy
  apply wcut_zero_of
  have : (4:ℝ) < ‖y‖ ^ 2 := by nlinarith
  rw [abs_of_pos (by linarith)]; linarith

theorem fderiv_wcut (y v : E3) :
    fderiv ℝ wcut y v = deriv psiB (‖y‖ ^ 2) * (2 * ⟪y, v⟫) := by
  have hψ : HasDerivAt psiB (deriv psiB (‖y‖ ^ 2)) (‖y‖ ^ 2) :=
    ((psiB.contDiffAt (n := 1)).differentiableAt (by simp)).hasDerivAt
  have h := hψ.comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have e : wcut = psiB ∘ fun x : E3 => ‖x‖ ^ 2 := rfl
  rw [e, h.fderiv]
  simp

theorem dw_cont (v : E3) : Continuous fun y => fderiv ℝ wcut y v :=
  (wcut_contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem dw_hcs (v : E3) : HasCompactSupport fun y => fderiv ℝ wcut y v :=
  wcut_hcs.fderiv_apply (𝕜 := ℝ) v

theorem dw_notMem (v : E3) : (0:E3) ∉ tsupport fun y => fderiv ℝ wcut y v :=
  fun h => wcut_notMem (tsupport_fderiv_apply_subset ℝ v h)

theorem cut_int_w {h : E3 → ℝ} (hh : ContinuousOn h {0}ᶜ) : Integrable (fun y => wcut y * h y) :=
  cut_integrable wcut_contDiff.continuous wcut_hcs wcut_notMem hh

theorem cut_int_dw (v : E3) {h : E3 → ℝ} (hh : ContinuousOn h {0}ᶜ) :
    Integrable (fun y => fderiv ℝ wcut y v * h y) :=
  cut_integrable (dw_cont v) (dw_hcs v) (dw_notMem v) hh

/-- Euler: `∇w ⟂ ∇U` for a degree-zero homogeneous `U`. -/
theorem euler_sum {U : E3 → ℝ} (hhom : ∀ r : ℝ, 0 < r → ∀ y, U (r • y) = U y) (hU : C2off U)
    (y : E3) : ∑ i, fderiv ℝ wcut y (bE i) * fderiv ℝ U y (bE i) = 0 := by
  simp_rw [fderiv_wcut]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hd : DifferentiableAt ℝ U y := (hU y hy).differentiableAt (by norm_num)
    have he := euler_of_homogeneous (F := U) (l := 0) (fun r hr z => by simp [hhom r hr z]) hd
    have h := congrArg (fderiv ℝ U y) ((bE).sum_repr' y)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    calc ∑ i, deriv psiB (‖y‖ ^ 2) * (2 * ⟪y, bE i⟫) * fderiv ℝ U y (bE i)
        = 2 * deriv psiB (‖y‖ ^ 2) * ∑ i, ⟪bE i, y⟫ * fderiv ℝ U y (bE i) := by
          rw [Finset.mul_sum]; congr 1; ext i; rw [real_inner_comm]; ring
      _ = 0 := by
          have hS : ∑ i, ⟪bE i, y⟫ * fderiv ℝ U y (bE i) = 0 := by
            convert h.trans he using 1; simp
          rw [hS, mul_zero]

/-! ## (C) One integration by parts per coordinate -/

theorem fderiv_prod {U V : E3 → ℝ} (hU : C2off U) (hV : C2off V) (i : Fin 3) {y : E3} (hy : y ≠ 0) :
    HasFDerivAt (fun z => V z * fderiv ℝ U z (bE i))
      (V y • ((fderiv ℝ U y).comp (0 : E3 →L[ℝ] E3) + (fderiv ℝ (fderiv ℝ U) y).flip (bE i))
        + fderiv ℝ U y (bE i) • fderiv ℝ V y) y := by
  have ha := (hU.hasFDerivAt2 hy).clm_apply (hasFDerivAt_const (bE i) y)
  exact ((hV y hy).differentiableAt (by norm_num)).hasFDerivAt.mul ha

theorem ibp_i {U V : E3 → ℝ} (hU : C2off U) (hV : C2off V) (i : Fin 3) :
    ∫ y, wcut y * (fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i)
        + V y * fderiv ℝ (fderiv ℝ U) y (bE i) (bE i))
      = - ∫ y, fderiv ℝ wcut y (bE i) * (V y * fderiv ℝ U y (bE i)) := by
  have key : ∀ y, wcut y * fderiv ℝ (fun z => V z * fderiv ℝ U z (bE i)) y (bE i)
      = wcut y * (fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i)
        + V y * fderiv ℝ (fderiv ℝ U) y (bE i) (bE i)) := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · have : wcut 0 = 0 := by apply wcut_zero_of; norm_num
      simp [this]
    · rw [(fderiv_prod hU hV i hy).fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.flip_apply, smul_eq_mul]
      ring
  have hcV := hV.contOn
  have hcU := hU.d1_contOn (bE i)
  have hcV' := hV.d1_contOn (bE i)
  have hcU2 := hU.d2_contOn (bE i) (bE i)
  have hA : ContinuousOn (fun y => fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i)
        + V y * fderiv ℝ (fderiv ℝ U) y (bE i) (bE i)) {0}ᶜ :=
    (hcV'.mul hcU).add (hcV.mul hcU2)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := wcut)
    (g := fun z => V z * fderiv ℝ U z (bE i)) (v := bE i)
    (cut_int_dw (bE i) (hcV.mul hcU))
    (by simp_rw [key]; exact cut_int_w hA)
    (cut_int_w (hcV.mul hcU))
    (fun x _ => (wcut_contDiff.differentiable (by norm_num)) x)
    (fun x hx => (fderiv_prod hU hV i (wcut_ne_zero hx)).differentiableAt)
  simp_rw [key] at h
  exact h

/-- `∫ w (∇V·∇U + V ΔU) = 0` for degree-zero homogeneous `U`. -/
theorem green_half {U V : E3 → ℝ} (hU : C2off U) (hV : C2off V)
    (hhom : ∀ r : ℝ, 0 < r → ∀ y, U (r • y) = U y) :
    ∫ y, wcut y * (∑ i, fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i) + V y * Δ U y) = 0 := by
  have e : ∀ y, wcut y * (∑ i, fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i) + V y * Δ U y)
      = ∑ i, wcut y * (fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i)
        + V y * fderiv ℝ (fderiv ℝ U) y (bE i) (bE i)) := by
    intro y; rw [lap_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [e]
  rw [integral_finset_sum (f := fun i y => wcut y * (fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i)
        + V y * fderiv ℝ (fderiv ℝ U) y (bE i) (bE i))) _
    (fun i _ => cut_int_w (((hV.d1_contOn (bE i)).mul
    (hU.d1_contOn (bE i))).add (hV.contOn.mul (hU.d2_contOn (bE i) (bE i)))))]
  simp_rw [ibp_i hU hV]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum (f := fun i y =>
    fderiv ℝ wcut y (bE i) * (V y * fderiv ℝ U y (bE i))) _ (fun i _ =>
    cut_int_dw (bE i) (hV.contOn.mul (hU.d1_contOn (bE i))))]
  have z : ∀ y, ∑ i, fderiv ℝ wcut y (bE i) * (V y * fderiv ℝ U y (bE i)) = 0 := by
    intro y
    have h := euler_sum hhom hU y
    calc ∑ i, fderiv ℝ wcut y (bE i) * (V y * fderiv ℝ U y (bE i))
        = V y * ∑ i, fderiv ℝ wcut y (bE i) * fderiv ℝ U y (bE i) := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ = 0 := by rw [h, mul_zero]
  simp_rw [z]; simp

/-- **Weighted Green identity** in `ℝ³`: `∫ w (V ΔU − U ΔV) = 0` for degree-zero `U`, `V`. -/
theorem green_w {U V : E3 → ℝ} (hU : C2off U) (hV : C2off V)
    (hhomU : ∀ r : ℝ, 0 < r → ∀ y, U (r • y) = U y)
    (hhomV : ∀ r : ℝ, 0 < r → ∀ y, V (r • y) = V y) :
    ∫ y, wcut y * (V y * Δ U y - U y * Δ V y) = 0 := by
  have h1 := green_half hU hV hhomU
  have h2 := green_half hV hU hhomV
  have hS : ContinuousOn (fun y => ∑ i, fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i)) {0}ᶜ :=
    continuousOn_finset_sum _ fun i _ => (hV.d1_contOn (bE i)).mul (hU.d1_contOn (bE i))
  have hS' : ContinuousOn (fun y => ∑ i, fderiv ℝ U y (bE i) * fderiv ℝ V y (bE i)) {0}ᶜ :=
    continuousOn_finset_sum _ fun i _ => (hU.d1_contOn (bE i)).mul (hV.d1_contOn (bE i))
  have i1 := cut_int_w (h := fun y => ∑ i, fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i) + V y * Δ U y)
    (hS.add (hV.contOn.mul hU.lap_contOn))
  have i2 := cut_int_w (h := fun y => ∑ i, fderiv ℝ U y (bE i) * fderiv ℝ V y (bE i) + U y * Δ V y)
    (hS'.add (hU.contOn.mul hV.lap_contOn))
  have h := integral_sub i1 i2
  rw [h1, h2, sub_zero] at h
  rw [← h]
  congr 1; ext y
  have : ∑ i, fderiv ℝ U y (bE i) * fderiv ℝ V y (bE i)
      = ∑ i, fderiv ℝ V y (bE i) * fderiv ℝ U y (bE i) := by
    congr 1; ext i; ring
  beta_reduce
  rw [this]; ring

/-! ## (D) Scaling of the Laplacian of a degree-zero function -/

theorem lap_scale {U : E3 → ℝ} (hhom : ∀ r : ℝ, 0 < r → ∀ y, U (r • y) = U y) (hU : C2off U)
    {r : ℝ} (hr : 0 < r) {x : E3} (hx : x ≠ 0) :
    Δ U (r • x) = (r ^ 2)⁻¹ * Δ U x := by
  have hrx : r • x ≠ 0 := smul_ne_zero hr.ne' hx
  have e : Δ U x = Δ (fun y => U (r • y)) x :=
    congrArg (fun F : E3 → ℝ => Δ F x) (funext fun y => (hhom r hr y).symm)
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ U (r • y) := by
    have hc : Tendsto (fun y : E3 => r • y) (𝓝 x) (𝓝 (r • x)) :=
      (continuous_const_smul r).continuousAt
    have h1 : ∀ᶠ z in 𝓝 (r • x), DifferentiableAt ℝ U z := by
      filter_upwards [isOpen_ne.mem_nhds hrx] with z hz
      exact (hU z hz).differentiableAt (by norm_num)
    exact hc.eventually h1
  have hD : fderiv ℝ (fun y => U (r • y)) =ᶠ[𝓝 x] fun y => r • fderiv ℝ U (r • y) := by
    filter_upwards [hev] with y hy
    have h : HasFDerivAt (fun y => U (r • y))
        ((fderiv ℝ U (r • y)).comp (r • ContinuousLinearMap.id ℝ E3)) y :=
      hy.hasFDerivAt.comp y ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul r)
    rw [h.fderiv]; ext v; simp
  have h2 : HasFDerivAt (fun y => r • fderiv ℝ U (r • y))
      (r • (fderiv ℝ (fderiv ℝ U) (r • x)).comp (r • ContinuousLinearMap.id ℝ E3)) x :=
    ((hU.hasFDerivAt2 hrx).comp x ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul r)).const_smul r
  have key : Δ (fun y => U (r • y)) x = r ^ 2 * Δ U (r • x) := by
    rw [lap_eq_sum, hD.fderiv_eq, h2.fderiv, lap_eq_sum, Finset.mul_sum]
    congr 1; ext i
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    ring
  rw [e, key]
  field_simp

/-! ## (E) Polar coordinates: the symmetry on `S²` -/

theorem radial_pos : 0 < ∫ r in Ioi (0:ℝ), r ^ 2 * (psiB (r ^ 2) * (r ^ 2)⁻¹) := by
  have e : ∫ r in Ioi (0:ℝ), r ^ 2 * (psiB (r ^ 2) * (r ^ 2)⁻¹)
      = ∫ r in Ioi (0:ℝ), psiB (r ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : r ≠ 0 := ne_of_gt hr
    field_simp
  rw [e]
  have hcont : Continuous fun r : ℝ => psiB (r ^ 2) := psiB.continuous.comp (continuous_pow 2)
  have hcs : HasCompactSupport fun r : ℝ => psiB (r ^ 2) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-2:ℝ)) (b := 2)) fun r hr => ?_
    apply psiB.zero_of_le_dist
    rw [psiB_rOut, Real.dist_eq]
    have : 2 < |r| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hr
      rcases hr with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have h4 : (4:ℝ) < r ^ 2 := by
      have := sq_abs r; nlinarith [abs_nonneg r]
    rw [abs_of_pos (by linarith)]; linarith
  have hint : IntegrableOn (fun r : ℝ => psiB (r ^ 2)) (Ioi 0) :=
    (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  have hsub : Icc (9/10:ℝ) (11/10) ⊆ Ioi 0 := fun r hr => by
    simp only [mem_Icc] at hr; simp only [mem_Ioi]; linarith [hr.1]
  have h1 : ∫ r in Icc (9/10:ℝ) (11/10), psiB (r ^ 2) = 1/5 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (1:ℝ)) (fun r hr => ?_)]
    · rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num)]; norm_num
    · apply psiB.one_of_mem_closedBall
      rw [psiB_rIn, mem_closedBall, Real.dist_eq, abs_le]
      simp only [mem_Icc] at hr
      constructor <;> nlinarith [hr.1, hr.2]
  have h2 := setIntegral_mono_set hint (Eventually.of_forall fun r => psiB.nonneg' _)
    hsub.eventuallyLE
  linarith

/-- **Green's symmetry on `S²` (unnormalised measure, degree-zero form).** -/
theorem sphere_green {U V : E3 → ℝ} (hU : C2off U) (hV : C2off V)
    (hhomU : ∀ r : ℝ, 0 < r → ∀ y, U (r • y) = U y)
    (hhomV : ∀ r : ℝ, 0 < r → ∀ y, V (r • y) = V y) :
    ∫ x : S2, V x * Δ U x - U x * Δ V x ∂sigma0 = 0 := by
  have h := green_w hU hV hhomU hhomV
  rw [polar_mul (fun x : S2 => V x * Δ U x - U x * Δ V x) (fun r => psiB (r ^ 2) * (r ^ 2)⁻¹) _
    (fun u r hr => ?_)] at h
  · exact (mul_eq_zero.1 h).resolve_right radial_pos.ne'
  · have hu1 : ‖(u : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
    have hu0 := S2_ne_zero u
    have hw : wcut (r • (u : E3)) = psiB (r ^ 2) := by
      simp [wcut, norm_smul, hu1, abs_of_pos hr]
    rw [hw, hhomU r hr, hhomV r hr, lap_scale hhomU hU hr hu0, lap_scale hhomV hV hr hu0]
    ring

theorem sphC2_cont {f : S2 → ℝ} (hf : ∀ x, SphC2 f x) : Continuous f := by
  have e : f = fun x : S2 => ext0 (extS f) (x : E3) := funext fun x => (ext0_on_S2 f x).symm
  rw [e]
  exact (c2off_ext0 hf).contOn.comp_continuous continuous_subtype_val fun x => S2_ne_zero x

theorem sphLapS_cont {f : S2 → ℝ} (hf : ∀ x, SphC2 f x) : Continuous (sphLapS f) :=
  (c2off_ext0 hf).lap_contOn.comp_continuous continuous_subtype_val fun x => S2_ne_zero x

/-- **Green's symmetry of `Δ_{S²}`** (extrinsic `sphLapS`): for `f`, `g` whose degree-zero extensions are `C²`
near every point of `S²`, `∫ g Δf dσ = ∫ f Δg dσ`. -/
theorem sym_S2 {f g : S2 → ℝ} (hf : ∀ x, SphC2 f x) (hg : ∀ x, SphC2 g x) :
    ∫ x, g x * sphLapS f x ∂sigma = ∫ x, f x * sphLapS g x ∂sigma := by
  have h := sphere_green (c2off_ext0 hf) (c2off_ext0 hg) (fun r hr y => ext0_hom _ hr y)
    (fun r hr y => ext0_hom _ hr y)
  have e : ∀ x : S2, ext0 (extS g) (x : E3) * Δ (ext0 (extS f)) (x : E3)
      - ext0 (extS f) (x : E3) * Δ (ext0 (extS g)) (x : E3)
      = g x * sphLapS f x - f x * sphLapS g x := by
    intro x; rw [ext0_on_S2, ext0_on_S2]; rfl
  simp_rw [e] at h
  have h' : ∫ x, g x * sphLapS f x - f x * sphLapS g x ∂sigma = 0 := by
    rw [integral_sigma, h, mul_zero]
  have i1 : Integrable (fun x => g x * sphLapS f x) sigma :=
    CTG.FunkHecke.Proj.integrable_of_cont sigma ((sphC2_cont hg).mul (sphLapS_cont hf))
  have i2 : Integrable (fun x => f x * sphLapS g x) sigma :=
    CTG.FunkHecke.Proj.integrable_of_cont sigma ((sphC2_cont hf).mul (sphLapS_cont hg))
  rw [integral_sub i1 i2] at h'
  linarith



/-- The form asked for: for `K = Re (a·y)^l` (`a` isotropic) and `f` with `SphC2` on `S²`,
`∫ K Δf = ∫ f ΔK = −l(l+1) ∫ f K`. -/
theorem green_harmonic (p q : E3) (hpq : Isotropic p q) (l : ℕ) {f : S2 → ℝ} (hf : ∀ x, SphC2 f x) :
    (∫ x, (cdot p q (x : E3) ^ l).re * sphLapS f x ∂sigma
      = ∫ x, f x * sphLapS (fun y : S2 => (cdot p q (y : E3) ^ l).re) x ∂sigma) ∧
    (∫ x, f x * sphLapS (fun y : S2 => (cdot p q (y : E3) ^ l).re) x ∂sigma
      = -((l:ℝ) * (l + 1)) * ∫ x, f x * (cdot p q (x : E3) ^ l).re ∂sigma) := by
  refine ⟨sym_S2 (g := fun y : S2 => (cdot p q (y : E3) ^ l).re) hf (sphC2_re p q l), ?_⟩
  simp_rw [CTG.FunkHecke.SphereLaplace.sphLapS_harmonic p q hpq l]
  rw [← integral_const_mul]; congr 1; ext x; ring

/-! ## (F) Harmonics of degree `l` and the exchange `Π_l Δ = −l(l+1) Π_l` -/

open CTG.FunkHecke.Proj (harmDeg GenDeg IsHarm projDeg legendre_mem_deg integrable_of_cont)

/-- For `K` in the span `H_l` of `Re/Im (a·y)^l` (`a` isotropic) and `f` with `SphC2` on `S²`:
`∫ K Δ_{S²} f dσ = −l(l+1) ∫ K f dσ`. -/
theorem harm_lap {l : ℕ} {F : C(S2, ℝ)} (hF : F ∈ harmDeg l) {f : S2 → ℝ} (hf : ∀ x, SphC2 f x) :
    ∫ x, F x * sphLapS f x ∂sigma = -((l:ℝ) * (l + 1)) * ∫ x, F x * f x ∂sigma := by
  have hcf := sphC2_cont hf
  have hcl := sphLapS_cont hf
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨p, q, hpq, e | e⟩ := (hF : IsHarm l ⇑F)
      · have e' : ∀ x, F x = (cdot p q (x : E3) ^ l).re := fun x => congrFun e x
        simp_rw [e']
        have hs := sym_S2 (g := fun y : S2 => (cdot p q (y : E3) ^ l).re) hf (sphC2_re p q l)
        simp only at hs
        rw [hs]
        simp_rw [CTG.FunkHecke.SphereLaplace.sphLapS_harmonic p q hpq l]
        rw [← integral_const_mul]; congr 1; ext x; ring
      · have e' : ∀ x, F x = (cdot p q (x : E3) ^ l).im := fun x => congrFun e x
        simp_rw [e']
        have hs := sym_S2 (g := fun y : S2 => (cdot p q (y : E3) ^ l).im) hf (sphC2_im p q l)
        simp only at hs
        rw [hs]
        simp_rw [CTG.FunkHecke.SphereLinComb.sphLapS_harmonic_im p q hpq l]
        rw [← integral_const_mul]; congr 1; ext x; ring
  | zero => simp
  | add F G _ _ ihF ihG =>
      simp only [ContinuousMap.coe_add, Pi.add_apply, add_mul]
      have i1 : Integrable (fun x => F x * sphLapS f x) sigma :=
        integrable_of_cont _ (F.continuous.mul hcl)
      have i2 : Integrable (fun x => G x * sphLapS f x) sigma :=
        integrable_of_cont _ (G.continuous.mul hcl)
      have i3 : Integrable (fun x => F x * f x) sigma := integrable_of_cont _ (F.continuous.mul hcf)
      have i4 : Integrable (fun x => G x * f x) sigma := integrable_of_cont _ (G.continuous.mul hcf)
      rw [integral_add i1 i2, integral_add i3 i4, ihF, ihG]
      ring
  | smul c F _ ihF =>
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [integral_const_mul, integral_const_mul, ihF]
      ring

/-- **The exchange `Π_l Δ_{S²} = −l(l+1) Π_l`** for `f` whose degree-zero extension is `C²` near `S²`
(this is the HYPOTHESIS `hΔ` of `decay_L2`/`decay_sup` of the sixty-eighth file). -/
theorem proj_lap (l : ℕ) {f : S2 → ℝ} (hf : ∀ x, SphC2 f x) (x : S2) :
    projDeg l (sphLapS f) x = -((l:ℝ) * (l + 1)) * projDeg l f x := by
  obtain ⟨F, hF, hFy⟩ := legendre_mem_deg (x : E3) (mem_sphere_zero_iff_norm.mp x.2) l
  have e : ∀ h : S2 → ℝ, projDeg l h x = (2 * (l:ℝ) + 1) * ∫ y, F y * h y ∂sigma := by
    intro h; unfold projDeg zonalOp; simp_rw [hFy]
  rw [e, e, harm_lap hF hf]; ring

/-! ## (G) Decay of `Π_l f` without the hypothesis -/

/-- The hypothesis of `decay_L2`, `decay_sup` holds for a sequence `g` with `g (j+1) = Δ_{S²} g j`. -/
theorem hexch (g : ℕ → C(S2, ℝ)) (hg : ∀ j x, SphC2 (g j) x)
    (hstep : ∀ j x, g (j + 1) x = sphLapS (g j) x) :
    ∀ j l x, projDeg l (g (j + 1)) x = -((l : ℝ) * (l + 1)) * projDeg l (g j) x := by
  intro j l x
  have e : ⇑(g (j + 1)) = sphLapS ⇑(g j) := funext (hstep j)
  rw [e]; exact proj_lap l (hg j) x

theorem decay_L2_smooth (g : ℕ → C(S2, ℝ)) (hg : ∀ j x, SphC2 (g j) x)
    (hstep : ∀ j x, g (j + 1) x = sphLapS (g j) x) (k l : ℕ) :
    ((l : ℝ) * (l + 1)) ^ (2 * k) * ∫ x, projDeg l (g 0) x ^ 2 ∂sigma ≤ ∫ x, g k x ^ 2 ∂sigma :=
  CTG.FunkHecke.Parseval.decay_L2 g (hexch g hg hstep) k l

theorem decay_sup_smooth (g : ℕ → C(S2, ℝ)) (hg : ∀ j x, SphC2 (g j) x)
    (hstep : ∀ j x, g (j + 1) x = sphLapS (g j) x) (k l : ℕ) (x : S2) :
    ((l : ℝ) * (l + 1)) ^ k * |projDeg l (g 0) x|
      ≤ Real.sqrt (2 * (l : ℝ) + 1) * Real.sqrt (∫ y, g k y ^ 2 ∂sigma) :=
  CTG.FunkHecke.Parseval.decay_sup g (hexch g hg hstep) k l x

/-- Iterates `Δ^j f`, `j < k`, all with `SphC2`; the `k`-th iterate is then continuous. -/
theorem iter_cont (f : S2 → ℝ) (hcf : Continuous f) (k : ℕ)
    (hf : ∀ j < k, ∀ x, SphC2 (sphLapS^[j] f) x) : Continuous (sphLapS^[k] f) := by
  cases k with
  | zero => simpa using hcf
  | succ k =>
      rw [Function.iterate_succ_apply']
      exact sphLapS_cont (hf k (Nat.lt_succ_self k))

theorem proj_iter_fin (f : S2 → ℝ) (l : ℕ) (x : S2) :
    ∀ k : ℕ, (∀ j < k, ∀ y, SphC2 (sphLapS^[j] f) y) →
      projDeg l (sphLapS^[k] f) x = (-((l : ℝ) * (l + 1))) ^ k * projDeg l f x := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hf
      rw [Function.iterate_succ_apply', proj_lap l (hf k (Nat.lt_succ_self k)),
        ih (fun j hj => hf j (Nat.lt_succ_of_lt hj)), pow_succ]
      ring

/-- **Decay in `L²` with `C^{2k}`-type regularity** (`k` iterates, no hypothesis on `Π_l`). -/
theorem decay_L2_fin (f : S2 → ℝ) (hcf : Continuous f) (k : ℕ)
    (hf : ∀ j < k, ∀ x, SphC2 (sphLapS^[j] f) x) (l : ℕ) :
    ((l : ℝ) * (l + 1)) ^ (2 * k) * ∫ x, projDeg l f x ^ 2 ∂sigma
      ≤ ∫ x, (sphLapS^[k] f) x ^ 2 ∂sigma := by
  let Fk : C(S2, ℝ) := ⟨sphLapS^[k] f, iter_cont f hcf k hf⟩
  refine le_trans (le_of_eq ?_) (CTG.FunkHecke.Parseval.proj_L2_le l Fk)
  rw [← integral_const_mul]; congr 1; ext x
  show _ = projDeg l (sphLapS^[k] f) x ^ 2
  rw [proj_iter_fin f l x k hf]
  set A : ℝ := (l : ℝ) * (l + 1)
  set P : ℝ := projDeg l f x
  rw [show ((-A) ^ k * P) ^ 2 = ((-A) ^ 2) ^ k * P ^ 2 by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2], neg_sq, ← pow_mul]

/-- **Decay in the supremum norm with `C^{2k}`-type regularity**:
`(l(l+1))^k |Π_l f(x)| ≤ √(2l+1) ‖Δ^k f‖_{L²(σ)}`. -/
theorem decay_sup_fin (f : S2 → ℝ) (hcf : Continuous f) (k : ℕ)
    (hf : ∀ j < k, ∀ x, SphC2 (sphLapS^[j] f) x) (l : ℕ) (x : S2) :
    ((l : ℝ) * (l + 1)) ^ k * |projDeg l f x|
      ≤ Real.sqrt (2 * (l : ℝ) + 1) * Real.sqrt (∫ y, (sphLapS^[k] f) y ^ 2 ∂sigma) := by
  let F0 : C(S2, ℝ) := ⟨f, hcf⟩
  have hr := CTG.FunkHecke.Parseval.repro_bound (CTG.FunkHecke.Parseval.projC_mem l F0) x
  simp only [CTG.FunkHecke.Parseval.projC_apply] at hr
  have hlam : (0 : ℝ) ≤ ((l : ℝ) * (l + 1)) ^ k := by positivity
  have hd := decay_L2_fin f hcf k hf l
  have hsq : ((l : ℝ) * (l + 1)) ^ k * Real.sqrt (∫ y, projDeg l f y ^ 2 ∂sigma)
      ≤ Real.sqrt (∫ y, (sphLapS^[k] f) y ^ 2 ∂sigma) := by
    rw [← Real.sqrt_sq hlam, ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    rw [← pow_mul, mul_comm k 2]; exact hd
  calc ((l : ℝ) * (l + 1)) ^ k * |projDeg l f x|
      ≤ ((l : ℝ) * (l + 1)) ^ k * (Real.sqrt (2 * (l : ℝ) + 1)
          * Real.sqrt (∫ y, projDeg l f y ^ 2 ∂sigma)) := mul_le_mul_of_nonneg_left hr hlam
    _ = Real.sqrt (2 * (l : ℝ) + 1) * (((l : ℝ) * (l + 1)) ^ k
          * Real.sqrt (∫ y, projDeg l f y ^ 2 ∂sigma)) := by ring
    _ ≤ Real.sqrt (2 * (l : ℝ) + 1) * Real.sqrt (∫ y, (sphLapS^[k] f) y ^ 2 ∂sigma) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)

end CTG.FunkHecke.Green

#print axioms CTG.FunkHecke.Green.sym_S2
#print axioms CTG.FunkHecke.Green.green_harmonic
#print axioms CTG.FunkHecke.Green.proj_lap
#print axioms CTG.FunkHecke.Green.decay_sup_smooth
#print axioms CTG.FunkHecke.Green.decay_sup_fin
