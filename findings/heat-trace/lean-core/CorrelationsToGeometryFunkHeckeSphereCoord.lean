/-
Seventy-second file (A185, written by a subagent of the author-side session, checked by that session; read by nobody
else). The extrinsically defined Laplacian `sphLap`/`sphLapS` of `S²` equals, in spherical coordinates
Φ(θ,φ) = (sinθ cosφ, sinθ sinφ, cosθ), the classical coordinate formula of the Laplace–Beltrami operator of the round
metric dθ² + sin²θ dφ²: (1/sinθ)∂_θ(sinθ ∂_θ u) + (1/sin²θ)∂_φ²u, u = f∘Φ. Namespace `CTG.FunkHecke.SphereCoord`;
imports Mathlib and the compiled module `CorrelationsToGeometryFunkHeckeSphereLinComb`. Check with
`./check_funk_hecke_sphere_coord.sh` from `lean/`.

Main statements: `lap_frame` (Laplacian = trace of the Hessian in the orthonormal frame {Φ, e_θ, B}), `curve_second`,
`radial`, `lap_spherical`, `lap_spherical_div`, `sphLap_coord`, `sphLapS_coord`, `coord_harmonic` (consistency check:
the coordinate formula gives −l(l+1)u on the harmonics). Assumptions: C² at the point (`ContDiffAt`/`SphC2`), sin θ ≠ 0.
NOT shown: identification with an intrinsic Laplace–Beltrami operator defined in Mathlib (none exists in v4.29; that the
coordinate formula is that operator is a textbook fact, not stated in Lean); the poles (no second chart, no rotation
invariance); that every non-polar point is of the form Φ(θ,φ). No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSphereLinComb

open Real Filter Topology
open scoped RealInnerProductSpace
open Laplacian

namespace CTG.FunkHecke.SphereCoord

open CTG.FunkHecke (S2 E3 cdot Isotropic)
open CTG.FunkHecke.SphereLaplace (ext0 sphLap sphLapS extS)
open CTG.FunkHecke.SphereLinComb (SphC2)

/-! ### (0) The vectors of spherical coordinates -/

noncomputable def e (i : Fin 3) : E3 := EuclideanSpace.single i (1 : ℝ)

/-- `A φ = (cos φ, sin φ, 0)`. -/
noncomputable def A (φ : ℝ) : E3 := cos φ • e 0 + sin φ • e 1
/-- `B φ = (−sin φ, cos φ, 0)` (unit vector `e_φ`). -/
noncomputable def B (φ : ℝ) : E3 := (-sin φ) • e 0 + cos φ • e 1
/-- `Φ(θ,φ) = (sinθ cosφ, sinθ sinφ, cosθ)`. -/
noncomputable def Φ (θ φ : ℝ) : E3 := sin θ • A φ + cos θ • e 2
/-- `e_θ = ∂_θ Φ = (cosθ cosφ, cosθ sinφ, −sinθ)`. -/
noncomputable def eθ (θ φ : ℝ) : E3 := cos θ • A φ + (-sin θ) • e 2

theorem inner_e (i j : Fin 3) : ⟪e i, e j⟫ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)) i j

theorem inner_AA (φ : ℝ) : ⟪A φ, A φ⟫ = 1 := by
  simp only [A, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_e]
  simp; nlinarith [sin_sq_add_cos_sq φ]

theorem inner_BB (φ : ℝ) : ⟪B φ, B φ⟫ = 1 := by
  simp only [B, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_e]
  simp; nlinarith [sin_sq_add_cos_sq φ]

theorem inner_AB (φ : ℝ) : ⟪A φ, B φ⟫ = 0 := by
  simp only [A, B, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, inner_e]
  simp; ring

theorem inner_A2 (φ : ℝ) : ⟪A φ, e 2⟫ = 0 := by
  simp only [A, inner_add_left, real_inner_smul_left, inner_e]; simp

theorem inner_B2 (φ : ℝ) : ⟪B φ, e 2⟫ = 0 := by
  simp only [B, inner_add_left, real_inner_smul_left, inner_e]; simp

theorem inner_22 : ⟪e 2, e 2⟫ = 1 := by rw [inner_e]; simp

theorem norm_Φ (θ φ : ℝ) : ‖Φ θ φ‖ = 1 := by
  have h : ⟪Φ θ φ, Φ θ φ⟫ = 1 := by
    simp only [Φ, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [inner_AA, inner_A2, real_inner_comm (A φ) (e 2), inner_A2, inner_22]
    nlinarith [sin_sq_add_cos_sq θ]
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (Φ θ φ)]

/-- The three vectors `Φ, e_θ, B` of the moving frame. -/
noncomputable def frame (θ φ : ℝ) : Fin 3 → E3 := ![Φ θ φ, eθ θ φ, B φ]

theorem frame_orthonormal (θ φ : ℝ) : Orthonormal ℝ (frame θ φ) := by
  rw [orthonormal_iff_ite]
  have hBA : ⟪B φ, A φ⟫ = 0 := by rw [real_inner_comm]; exact inner_AB φ
  have h2A : ⟪e 2, A φ⟫ = 0 := by rw [real_inner_comm]; exact inner_A2 φ
  have h2B : ⟪e 2, B φ⟫ = 0 := by rw [real_inner_comm]; exact inner_B2 φ
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [frame, Φ, eθ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, inner_AA, inner_BB, inner_AB, inner_A2, inner_B2, inner_22, hBA, h2A, h2B,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> simp <;> nlinarith [sin_sq_add_cos_sq θ]

/-- The moving frame as an orthonormal basis of `ℝ³`. -/
noncomputable def frameONB (θ φ : ℝ) : OrthonormalBasis (Fin 3) ℝ E3 :=
  OrthonormalBasis.mk (frame_orthonormal θ φ) (by
    have hb := (basisOfOrthonormalOfCardEqFinrank (frame_orthonormal θ φ)
      (by simp : Fintype.card (Fin 3) = Module.finrank ℝ E3)).span_eq
    rw [coe_basisOfOrthonormalOfCardEqFinrank] at hb
    rw [hb])

theorem frameONB_apply (θ φ : ℝ) (i : Fin 3) : frameONB θ φ i = frame θ φ i := by
  unfold frameONB; rw [OrthonormalBasis.coe_mk]

/-- **Trace of the Hessian in the moving frame** (basis independence of `Δ`). -/
theorem lap_frame (F : E3 → ℝ) (θ φ : ℝ) (x : E3) :
    Δ F x = fderiv ℝ (fderiv ℝ F) x (Φ θ φ) (Φ θ φ) + fderiv ℝ (fderiv ℝ F) x (eθ θ φ) (eθ θ φ)
      + fderiv ℝ (fderiv ℝ F) x (B φ) (B φ) := by
  have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F
    (frameONB θ φ)) x
  refine h.trans ?_
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, frameONB_apply,
    Fin.sum_univ_three, frame, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-! ### (1) Derivatives of the curves -/

theorem hasDerivAt_A (φ : ℝ) : HasDerivAt A (B φ) φ := by
  have := ((hasDerivAt_cos φ).smul_const (e 0)).add ((hasDerivAt_sin φ).smul_const (e 1))
  convert this using 1

theorem hasDerivAt_B (φ : ℝ) : HasDerivAt B (-A φ) φ := by
  have := ((hasDerivAt_sin φ).neg.smul_const (e 0)).add ((hasDerivAt_cos φ).smul_const (e 1))
  convert this using 1
  simp only [A, neg_add, neg_smul]

theorem hasDerivAt_Φθ (θ φ : ℝ) : HasDerivAt (fun t => Φ t φ) (eθ θ φ) θ := by
  have := ((hasDerivAt_sin θ).smul_const (A φ)).add ((hasDerivAt_cos θ).smul_const (e 2))
  convert this using 1

theorem hasDerivAt_eθθ (θ φ : ℝ) : HasDerivAt (fun t => eθ t φ) (-Φ θ φ) θ := by
  have := ((hasDerivAt_cos θ).smul_const (A φ)).add ((hasDerivAt_sin θ).neg.smul_const (e 2))
  convert this using 1
  simp only [Φ, neg_add, neg_smul]

theorem hasDerivAt_Φφ (θ φ : ℝ) : HasDerivAt (fun t => Φ θ t) (sin θ • B φ) φ := by
  have := ((hasDerivAt_A φ).const_smul (sin θ)).add_const (cos θ • e 2)
  convert this using 1

theorem hasDerivAt_sB (θ φ : ℝ) : HasDerivAt (fun t => sin θ • B t) (-(sin θ • A φ)) φ := by
  have := (hasDerivAt_B φ).const_smul (sin θ)
  convert this using 1
  rw [smul_neg]

theorem A_decomp (θ φ : ℝ) : A φ = sin θ • Φ θ φ + cos θ • eθ θ φ := by
  simp only [Φ, eθ, smul_add, smul_smul]
  rw [show sin θ * sin θ = 1 - cos θ * cos θ by nlinarith [sin_sq_add_cos_sq θ]]
  module

/-! ### (2) Second derivative along a curve -/

theorem curve_first {F : E3 → ℝ} {x : E3} (hF : ContDiffAt ℝ 2 F x) {γ γ' : ℝ → E3} {t₀ : ℝ}
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hx : γ t₀ = x) :
    HasDerivAt (fun s => F (γ s)) (fderiv ℝ F x (γ' t₀)) t₀ := by
  have hd : DifferentiableAt ℝ F (γ t₀) := by
    rw [hx]; exact hF.differentiableAt (by norm_num)
  have := hd.hasFDerivAt.comp_hasDerivAt t₀ (hγ t₀)
  rw [hx] at this; exact this

theorem curve_second {F : E3 → ℝ} {x : E3} (hF : ContDiffAt ℝ 2 F x) {γ γ' : ℝ → E3} {t₀ : ℝ}
    {a : E3} (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : HasDerivAt γ' a t₀) (hx : γ t₀ = x) :
    HasDerivAt (fun t => deriv (fun s => F (γ s)) t)
      (fderiv ℝ (fderiv ℝ F) x (γ' t₀) (γ' t₀) + fderiv ℝ F x a) t₀ := by
  -- `F` is differentiable near `x`, hence near `γ t₀` along the curve
  have hev : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hcont : ContinuousAt γ t₀ := (hγ t₀).continuousAt
  have hev' : ∀ᶠ t in 𝓝 t₀, DifferentiableAt ℝ F (γ t) := by
    rw [← hx] at hev; exact hcont.eventually hev
  have heq : (fun t => deriv (fun s => F (γ s)) t) =ᶠ[𝓝 t₀] fun t => fderiv ℝ F (γ t) (γ' t) := by
    filter_upwards [hev'] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  -- derivative of `t ↦ DF(γ t)(γ' t)`
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD' : DifferentiableAt ℝ (fderiv ℝ F) (γ t₀) := by rw [hx]; exact hD
  have h1 : HasDerivAt (fun t => fderiv ℝ F (γ t)) (fderiv ℝ (fderiv ℝ F) x (γ' t₀)) t₀ := by
    have := hD'.hasFDerivAt.comp_hasDerivAt t₀ (hγ t₀)
    rw [hx] at this; exact this
  have h2 := h1.clm_apply hγ'
  have h3 : HasDerivAt (fun t => fderiv ℝ F (γ t) (γ' t))
      (fderiv ℝ (fderiv ℝ F) x (γ' t₀) (γ' t₀) + fderiv ℝ F x a) t₀ := by
    convert h2 using 1; rw [hx]
  exact h3.congr_of_eventuallyEq heq

/-! ### (3) Radial direction -/

theorem radial {F : E3 → ℝ} (hhom : ∀ r : ℝ, 0 < r → ∀ y, F (r • y) = F y) {x : E3}
    (hF : ContDiffAt ℝ 2 F x) :
    fderiv ℝ F x x = 0 ∧ fderiv ℝ (fderiv ℝ F) x x x = 0 := by
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • x) ((fun _ => x) t) t := fun t => by
    simpa using (hasDerivAt_id t).smul_const x
  have hγ' : HasDerivAt (fun _ : ℝ => x) (0 : E3) 1 := hasDerivAt_const _ _
  have hconst : (fun s : ℝ => F (s • x)) =ᶠ[𝓝 1] fun _ => F x := by
    filter_upwards [lt_mem_nhds (show (0:ℝ) < 1 by norm_num)] with s hs
    exact hhom s hs x
  have h1 := curve_first hF hγ (t₀ := 1) (by simp)
  have h1' : HasDerivAt (fun s : ℝ => F (s • x)) 0 1 :=
    (hasDerivAt_const (1:ℝ) (F x)).congr_of_eventuallyEq hconst
  have h2 := curve_second hF hγ hγ' (t₀ := 1) (by simp)
  have hderiv : (fun t => deriv (fun s : ℝ => F (s • x)) t) =ᶠ[𝓝 1] fun _ => (0:ℝ) := by
    have := hconst.deriv
    filter_upwards [this] with t ht
    rw [ht]; simp
  have h2' : HasDerivAt (fun t => deriv (fun s : ℝ => F (s • x)) t) 0 1 :=
    (hasDerivAt_const (1:ℝ) (0:ℝ)).congr_of_eventuallyEq hderiv
  refine ⟨h1.unique h1', ?_⟩
  have := h2.unique h2'
  simpa using this

/-! ### (4) Main theorem -/

/-- **Laplacian of a degree-zero homogeneous function in spherical coordinates.** If
`F(r y) = F(y)` for `r > 0`, `F` is `C²` at `Φ(θ,φ)` and `sin θ ≠ 0`, then with `u(a,b) = F(Φ(a,b))`:
`Δ_{ℝ³} F (Φ(θ,φ)) = ∂_θ²u + (cosθ/sinθ) ∂_θu + (1/sin²θ) ∂_φ²u`. -/
theorem lap_spherical {F : E3 → ℝ} (hhom : ∀ r : ℝ, 0 < r → ∀ y, F (r • y) = F y) {θ φ : ℝ}
    (hs : sin θ ≠ 0) (hF : ContDiffAt ℝ 2 F (Φ θ φ)) :
    Δ F (Φ θ φ) =
      deriv (fun a => deriv (fun b => F (Φ b φ)) a) θ
        + cos θ / sin θ * deriv (fun b => F (Φ b φ)) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => F (Φ θ b)) a) φ := by
  set x := Φ θ φ with hxdef
  obtain ⟨hr1, hr2⟩ := radial hhom hF
  -- θ-curve
  have hθ1 := curve_first hF (fun t => hasDerivAt_Φθ t φ) (t₀ := θ) rfl
  have hθ2 := curve_second hF (fun t => hasDerivAt_Φθ t φ) (hasDerivAt_eθθ θ φ) (t₀ := θ) rfl
  -- φ-curve
  have hφ2 := curve_second hF (fun t => hasDerivAt_Φφ θ t) (hasDerivAt_sB θ φ) (t₀ := φ) rfl
  rw [hθ1.deriv, hθ2.deriv, hφ2.deriv, lap_frame F θ φ x, ← hxdef, hr2]
  -- simplify the second-order terms
  have eA : fderiv ℝ F x (A φ) = cos θ * fderiv ℝ F x (eθ θ φ) := by
    rw [A_decomp θ φ, map_add, map_smul, map_smul, ← hxdef, hr1]; simp
  have hS : fderiv ℝ (fderiv ℝ F) x (sin θ • B φ) (sin θ • B φ)
      = sin θ ^ 2 * fderiv ℝ (fderiv ℝ F) x (B φ) (B φ) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  have hN1 : fderiv ℝ F x (-Φ θ φ) = 0 := by rw [map_neg, ← hxdef, hr1, neg_zero]
  have hN2 : fderiv ℝ F x (-(sin θ • A φ)) = -(sin θ * cos θ * fderiv ℝ F x (eθ θ φ)) := by
    rw [map_neg, map_smul, eA, smul_eq_mul]; ring
  rw [hN1, hS, hN2]
  field_simp
  ring

/-- Divergence form `(1/sinθ) ∂_θ (sinθ ∂_θ u)` of the θ-part. -/
theorem lap_spherical_div {F : E3 → ℝ} (hhom : ∀ r : ℝ, 0 < r → ∀ y, F (r • y) = F y) {θ φ : ℝ}
    (hs : sin θ ≠ 0) (hF : ContDiffAt ℝ 2 F (Φ θ φ)) :
    Δ F (Φ θ φ) =
      1 / sin θ * deriv (fun a => sin a * deriv (fun b => F (Φ b φ)) a) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => F (Φ θ b)) a) φ := by
  have hθ2 := curve_second hF (fun t => hasDerivAt_Φθ t φ) (hasDerivAt_eθθ θ φ) (t₀ := θ) rfl
  have hprod : HasDerivAt (fun a => sin a * deriv (fun b => F (Φ b φ)) a) _ θ :=
    (hasDerivAt_sin θ).mul hθ2
  rw [lap_spherical hhom hs hF, hprod.deriv, hθ2.deriv]
  field_simp
  ring

/-! ### (5) Application to `sphLap` and `sphLapS` -/

theorem ext0_homog (f : E3 → ℝ) : ∀ r : ℝ, 0 < r → ∀ y, ext0 f (r • y) = ext0 f y := by
  intro r hr y
  unfold ext0
  by_cases hy : y = 0
  · subst hy; simp
  · congr 1
    rw [norm_smul, Real.norm_of_nonneg hr.le, smul_smul, mul_inv_rev, mul_assoc,
      inv_mul_cancel₀ hr.ne', mul_one]

theorem ext0_Φ (f : E3 → ℝ) (a b : ℝ) : ext0 f (Φ a b) = f (Φ a b) := by
  unfold ext0; rw [norm_Φ, inv_one, one_smul]

/-- **Identification of `sphLap` with the coordinate formula of the Laplace–Beltrami operator of the
round metric**, `0 < θ < π` (only `sin θ ≠ 0` is used), `u = f ∘ Φ`. -/
theorem sphLap_coord (f : E3 → ℝ) {θ φ : ℝ} (hs : sin θ ≠ 0)
    (hF : ContDiffAt ℝ 2 (ext0 f) (Φ θ φ)) :
    sphLap f (Φ θ φ) =
      1 / sin θ * deriv (fun a => sin a * deriv (fun b => f (Φ b φ)) a) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (Φ θ b)) a) φ := by
  unfold sphLap
  rw [lap_spherical_div (ext0_homog f) hs hF]
  simp only [ext0_Φ]

theorem sphLap_coord' (f : E3 → ℝ) {θ φ : ℝ} (hs : sin θ ≠ 0)
    (hF : ContDiffAt ℝ 2 (ext0 f) (Φ θ φ)) :
    sphLap f (Φ θ φ) =
      deriv (fun a => deriv (fun b => f (Φ b φ)) a) θ
        + cos θ / sin θ * deriv (fun b => f (Φ b φ)) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (Φ θ b)) a) φ := by
  unfold sphLap
  rw [lap_spherical (ext0_homog f) hs hF]
  simp only [ext0_Φ]

/-- The parametrisation as a map into the subtype `S2`. -/
noncomputable def ΦS (θ φ : ℝ) : S2 := ⟨Φ θ φ, mem_sphere_zero_iff_norm.mpr (norm_Φ θ φ)⟩

theorem extS_Φ (f : S2 → ℝ) (a b : ℝ) : extS f (Φ a b) = f (ΦS a b) := by
  unfold extS; rw [dif_pos (mem_sphere_zero_iff_norm.mpr (norm_Φ a b))]; rfl

/-- The same for functions on the subtype `S2` under the regularity hypothesis `SphC2`. -/
theorem sphLapS_coord (f : S2 → ℝ) {θ φ : ℝ} (hs : sin θ ≠ 0) (hF : SphC2 f (ΦS θ φ)) :
    sphLapS f (ΦS θ φ) =
      1 / sin θ * deriv (fun a => sin a * deriv (fun b => f (ΦS b φ)) a) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΦS θ b)) a) φ := by
  unfold sphLapS
  rw [show ((ΦS θ φ : S2) : E3) = Φ θ φ from rfl, sphLap_coord (extS f) hs hF]
  simp only [extS_Φ]

theorem sphLapS_coord_of_mem (f : S2 → ℝ) {θ φ : ℝ} (hθ : 0 < θ) (hθ' : θ < π)
    (hF : SphC2 f (ΦS θ φ)) :
    sphLapS f (ΦS θ φ) =
      1 / sin θ * deriv (fun a => sin a * deriv (fun b => f (ΦS b φ)) a) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => f (ΦS θ b)) a) φ :=
  sphLapS_coord f (sin_pos_of_pos_of_lt_pi hθ hθ').ne' hF

/-! ### (6) Consistency check: the harmonics -/

/-- For `u = Re (a·Φ)^l`, the coordinate formula gives `−l(l+1) u` (consequence of `sphLapS_coord`
and `sphLapS_harmonic`). -/
theorem coord_harmonic (p q : E3) (h : Isotropic p q) (l : ℕ) {θ φ : ℝ} (hs : sin θ ≠ 0) :
    1 / sin θ * deriv (fun a => sin a * deriv (fun b => (cdot p q (ΦS b φ) ^ l).re) a) θ
        + 1 / sin θ ^ 2 * deriv (fun a => deriv (fun b => (cdot p q (ΦS θ b) ^ l).re) a) φ
      = -((l : ℝ) * (l + 1)) * (cdot p q (ΦS θ φ) ^ l).re := by
  rw [← sphLapS_coord (fun y : S2 => (cdot p q y ^ l).re) hs
    (CTG.FunkHecke.SphereLinComb.sphC2_re p q l (ΦS θ φ))]
  exact CTG.FunkHecke.SphereLaplace.sphLapS_harmonic p q h l (ΦS θ φ)

end CTG.FunkHecke.SphereCoord

#print axioms CTG.FunkHecke.SphereCoord.lap_spherical
#print axioms CTG.FunkHecke.SphereCoord.lap_spherical_div
#print axioms CTG.FunkHecke.SphereCoord.sphLap_coord
#print axioms CTG.FunkHecke.SphereCoord.sphLapS_coord
#print axioms CTG.FunkHecke.SphereCoord.coord_harmonic
