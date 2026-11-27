/-
Forty-fourth file: a Laplacian of the sphere `S²` as an object, and Theorem `thm:LB` on `S²` for the
harmonics `Re (a·y)^l` with that operator.  Namespace `CTG.FunkHecke.SphereLaplace`; imports the forty-second
file (compiled module); check with `./check_funk_hecke_sphere_laplace.sh`.
DEFINITION (extrinsic): `ext0 f y = f (y/‖y‖)` (extension homogeneous of degree zero), `sphLap f x = Δ_{ℝ³}(ext0 f)(x)`
with Mathlib's Laplacian, and `sphLapS` for functions on the subtype `S2` (extension by zero off the sphere, which
does not enter).  NOT FORMALISED: that this is the Laplace–Beltrami operator of the Riemannian manifold `S²`
(Mathlib v4.29 has none); the statement below is about the extrinsic operator.
PROVEN: `euler_of_homogeneous`; `sphLap_harmonic_homogeneous` (F is C² away from 0, homogeneous of degree l,
harmonic at x, ‖x‖ = 1 ⇒ `sphLap F x = −l(l+1) F x`); `sphLapS_restrict`; `sphLap_Fext`, `sphLapS_harmonic`
(`Re (a·y)^l`, `a` isotropic, is an eigenfunction with eigenvalue `−l(l+1)`); `LB_sphere`
(`|L_ξ f + Δ_{S²} f| ≤ [(ξ²/6 + 5ξ⁴/12)λ + (51/200)ξ²λ² + (27/200)ξ⁴λ³]|f|` pointwise, `0 < ξ ≤ 1/20`, `λ = l(l+1)`).
NOT formalised: general smooth functions on the sphere, completeness of the harmonics, multiplicity exactly `2l+1`,
any sample statement.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSphereLB

open Real Filter Topology Metric
open scoped RealInnerProductSpace
open Laplacian

namespace CTG.FunkHecke.SphereLaplace

open CTG.FunkHecke (S2 E3 cdot Isotropic)

/-! ### (1) Definition of the spherical Laplacian (extrinsic, via the degree-zero extension)

`ext0 f y = f (y/‖y‖)` is the extension of `f|_{S²}` that is homogeneous of degree `0`, and
`sphLap f x = Δ_{ℝ³} (ext0 f) (x)` for `‖x‖ = 1`. This is the usual extrinsic definition of the
Laplace–Beltrami operator `Δ_{S²}` of the round unit sphere. NOT FORMALISED: that it agrees with
the intrinsic Laplace–Beltrami operator of the Riemannian manifold `S²` (Mathlib v4.29 has no
Laplace–Beltrami operator on Riemannian manifolds). Only values of `f` on `S²` enter (`ext0 f y`
uses `f` at `y/‖y‖ ∈ S²` for `y ≠ 0`, and `sphLap f x` only depends on `ext0 f` near `x`). -/

/-- Degree-zero extension `y ↦ f (y/‖y‖)` (at `y = 0` the value `f 0`, irrelevant near `S²`). -/
noncomputable def ext0 (f : E3 → ℝ) (y : E3) : ℝ := f (‖y‖⁻¹ • y)

/-- The spherical Laplacian `Δ_{S²} f (x) := Δ_{ℝ³} (ext0 f) (x)` (meaningful for `‖x‖ = 1`). -/
noncomputable def sphLap (f : E3 → ℝ) (x : E3) : ℝ := Δ (ext0 f) x

/-! ### (2) Harmonic homogeneous functions are eigenfunctions of `sphLap` -/

/-- Euler's identity from homogeneity: `F(r y) = r^l F(y)` for `r > 0` gives `DF(y) y = l F(y)`. -/
theorem euler_of_homogeneous {F : E3 → ℝ} {l : ℕ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ y, F (r • y) = r ^ l * F y) {y : E3}
    (hd : DifferentiableAt ℝ F y) : fderiv ℝ F y y = l * F y := by
  have hl : HasDerivAt (fun r : ℝ => r • y) y 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const y
  have hF : HasFDerivAt F (fderiv ℝ F y) ((1:ℝ) • y) := by
    rw [one_smul]; exact hd.hasFDerivAt
  have h1 : HasDerivAt (fun r : ℝ => F (r • y)) (fderiv ℝ F y y) 1 :=
    hF.comp_hasDerivAt (x := (1:ℝ)) hl
  have h2 : HasDerivAt (fun r : ℝ => r ^ l * F y) ((l:ℝ) * 1 ^ (l-1) * F y) 1 :=
    (hasDerivAt_pow l (1:ℝ)).mul_const _
  have heq : (fun r : ℝ => F (r • y)) =ᶠ[𝓝 1] (fun r => r ^ l * F y) := by
    filter_upwards [lt_mem_nhds (show (0:ℝ) < 1 by norm_num)] with r hr
    exact hhom r hr y
  have := h1.unique (h2.congr_of_eventuallyEq heq)
  simpa using this

/-- The real inner product as a continuous bilinear map, with plain (not semilinear) type. -/
noncomputable def iL : E3 →L[ℝ] E3 →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem iL_apply (y v : E3) : iL y v = ⟪y, v⟫ := by unfold iL; rfl

noncomputable def wt (l : ℕ) (y : E3) : ℝ := (‖y‖ ^ 2) ^ (-(l:ℝ) / 2)

theorem wt_mul_pow {l : ℕ} {y : E3} (hy : y ≠ 0) : wt l y * ‖y‖ ^ l = 1 := by
  unfold wt
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [← Real.rpow_natCast ‖y‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_natCast ‖y‖ l,
    ← Real.rpow_add hn]
  have : ((2:ℕ) : ℝ) * (-(l:ℝ) / 2) + l = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

theorem ext0_eq {F : E3 → ℝ} {l : ℕ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ y, F (r • y) = r ^ l * F y) {y : E3} (hy : y ≠ 0) :
    ext0 F y = wt l y * F y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h1 := hhom ‖y‖ hn (‖y‖⁻¹ • y)
  rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at h1
  unfold ext0
  rw [h1, ← mul_assoc, wt_mul_pow hy, one_mul]

theorem lap_eq_sum (f : E3 → ℝ) (x : E3) :
    Δ f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)) x
  refine h.trans ?_
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Main theorem.** If `F : ℝ³ → ℝ` is `C²` away from `0`, homogeneous of degree `l`
(`F(r y) = r^l F(y)` for `r > 0`) and harmonic at `x` (`Δ F x = 0`), then for `‖x‖ = 1`:
`Δ_{S²} F (x) = −l(l+1) F(x)`. Proof: `ext0 F = ‖y‖^{−l} F` near `x`, product rule for the two
second derivatives along an orthonormal basis, `Σ⟨x,b_i⟩ DF(b_i) = DF(x) x = l F(x)` (Euler),
`Δ ‖y‖^{−l} = l(l−1)` on `S²`: `0 − 2l² F + l(l−1) F = −l(l+1) F`. -/
theorem sphLap_harmonic_homogeneous {F : E3 → ℝ} {l : ℕ}
    (hC : ∀ y : E3, y ≠ 0 → ContDiffAt ℝ 2 F y)
    (hhom : ∀ r : ℝ, 0 < r → ∀ y, F (r • y) = r ^ l * F y)
    {x : E3} (hx : ‖x‖ = 1) (hΔ : Δ F x = 0) :
    sphLap F x = -((l:ℝ) * (l + 1)) * F x := by
  have hx0 : x ≠ 0 := by
    intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
  set a : ℝ := -(l:ℝ) / 2 with ha
  have hpos : ∀ y : E3, y ≠ 0 → ‖y‖ ^ 2 ≠ 0 := fun y hy =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hy)
  -- the derivative of the weight `g(y) = ‖y‖^{-l}`
  let c : E3 → ℝ := fun y => a * (‖y‖ ^ 2) ^ (a - 1)
  let Dg : E3 → (E3 →L[ℝ] ℝ) := fun y => c y • ((2:ℝ) • iL y)
  have hg : ∀ y : E3, y ≠ 0 → HasFDerivAt (wt l) (Dg y) y := by
    intro y hy
    have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.rpow_const (p := a)
      (Or.inl (hpos y hy))
    have e : wt l = fun x : E3 => (‖x‖ ^ 2) ^ a := rfl
    rw [e]
    convert h using 1
    ext v
    simp [Dg, c]
  -- the derivative of `Dg`
  let c' : E3 →L[ℝ] ℝ := a • (((a - 1) * (‖x‖ ^ 2) ^ (a - 1 - 1)) • ((2:ℝ) • iL x))
  have hc : HasFDerivAt c c' x := by
    have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const (p := a - 1)
      (Or.inl (hpos x hx0))).const_mul a
    convert h using 1
    ext v
    simp [c']
  have hL : HasFDerivAt (fun y : E3 => (2:ℝ) • iL y) ((2:ℝ) • iL) x :=
    ((2:ℝ) • iL).hasFDerivAt
  have hDg : HasFDerivAt Dg (c x • ((2:ℝ) • iL) + c'.smulRight ((2:ℝ) • iL x)) x :=
    hc.smul hL
  have hF1 : ∀ y : E3, y ≠ 0 → DifferentiableAt ℝ F y := fun y hy =>
    (hC y hy).differentiableAt (by norm_num)
  have hH : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x :=
    (((hC x hx0).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  let Φ : E3 → (E3 →L[ℝ] ℝ) := fun y => wt l y • fderiv ℝ F y + F y • Dg y
  have hΦ : HasFDerivAt Φ
      ((wt l x • fderiv ℝ (fderiv ℝ F) x + (Dg x).smulRight (fderiv ℝ F x))
        + (F x • (c x • ((2:ℝ) • iL) + c'.smulRight ((2:ℝ) • iL x))
          + (fderiv ℝ F x).smulRight (Dg x))) x :=
    ((hg x hx0).smul hH).add ((hF1 x hx0).hasFDerivAt.smul hDg)
  have hne : ∀ᶠ y in 𝓝 x, y ≠ 0 := isOpen_ne.mem_nhds hx0
  have heq1 : ext0 F =ᶠ[𝓝 x] fun y => wt l y * F y := by
    filter_upwards [hne] with y hy
    exact ext0_eq hhom hy
  have heq2 : fderiv ℝ (fun y => wt l y * F y) =ᶠ[𝓝 x] Φ := by
    filter_upwards [hne] with y hy
    exact ((hg y hy).mul (hF1 y hy).hasFDerivAt).fderiv
  have hlap : sphLap F x = Δ (fun y => wt l y * F y) x :=
    (InnerProductSpace.laplacian_congr_nhds heq1).eq_of_nhds
  rw [hlap, lap_eq_sum, heq2.fderiv_eq, hΦ.fderiv]
  rw [lap_eq_sum] at hΔ
  set b := EuclideanSpace.basisFun (Fin 3) ℝ with hb
  set H := fderiv ℝ (fderiv ℝ F) x
  set dF := fderiv ℝ F x
  have hwx : wt l x = 1 := by simp [wt, hx]
  have hcx : c x = a := by simp [c, hx]
  have hn2 : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
  have key : ∀ i, ((wt l x • H + (Dg x).smulRight dF)
        + (F x • (c x • ((2:ℝ) • iL) + c'.smulRight ((2:ℝ) • iL x))
          + dF.smulRight (Dg x))) (b i) (b i)
      = H (b i) (b i) + 4 * a * (⟪b i, x⟫ * dF (b i))
        + F x * (2 * a * ⟪b i, b i⟫ + 4 * a * (a - 1) * (⟪x, b i⟫ * ⟪b i, x⟫)) := by
    intro i
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, iL_apply, smul_eq_mul, hwx, Dg, hcx, c',
      hn2, Real.one_rpow]
    rw [real_inner_comm x (b i)]
    ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hΔ, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have S1 : ∑ i, ⟪b i, x⟫ * dF (b i) = l * F x := by
    have h := congrArg dF (b.sum_repr' x)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.trans (euler_of_homogeneous hhom (hF1 x hx0))
  have S2 : ∑ i, ⟪b i, b i⟫ = 3 := by
    have : ∀ i, ⟪b i, b i⟫ = 1 := fun i => by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
    simp [this]
  have S3 : ∑ i, ⟪x, b i⟫ * ⟪b i, x⟫ = 1 := by
    have h1 : ⟪x, x⟫ = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
    exact (b.sum_inner_mul_inner x x).trans h1
  rw [S1, S2, S3, ha]
  ring

/-! ### (3) Application to `F = Re (a·y)^l` -/

/-- Extension of a function on `S²` to `ℝ³` by `0` off the sphere (only its values on `S²` enter
`sphLap` through the degree-zero extension). -/
noncomputable def extS (f : S2 → ℝ) (y : E3) : ℝ :=
  haveI := Classical.propDecidable (y ∈ S2)
  if h : y ∈ S2 then f ⟨y, h⟩ else 0

/-- The spherical Laplacian of a function on `S²`: `Δ_{S²} f (x) := Δ_{ℝ³} (f ∘ (y ↦ y/‖y‖)) (x)`.
(Extrinsic definition; see the comment at `sphLap`.) -/
noncomputable def sphLapS (f : S2 → ℝ) (x : S2) : ℝ := sphLap (extS f) (x : E3)

theorem ext0_extS_restrict (G : E3 → ℝ) {y : E3} (hy : y ≠ 0) :
    ext0 (extS (fun z : S2 => G z)) y = ext0 G y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hm : ‖y‖⁻¹ • y ∈ S2 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  simp only [ext0, extS, dif_pos hm]

/-- `sphLapS` of a restriction only depends on the extension through its degree-zero part. -/
theorem sphLapS_restrict (G : E3 → ℝ) (x : S2) :
    sphLapS (fun z : S2 => G z) x = sphLap G (x : E3) := by
  have hx0 : (x : E3) ≠ 0 := by
    intro h; have := mem_sphere_zero_iff_norm.mp x.2; rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne : ∀ᶠ y in 𝓝 (x : E3), y ≠ 0 := isOpen_ne.mem_nhds hx0
  have heq : ext0 (extS (fun z : S2 => G z)) =ᶠ[𝓝 (x : E3)] ext0 G := by
    filter_upwards [hne] with y hy
    exact ext0_extS_restrict G hy
  exact (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds

/-- `F = Re (a·y)^l` (isotropic `a`) is an eigenfunction of `sphLap` with eigenvalue `−l(l+1)`. -/
theorem sphLap_Fext (p q : E3) (h : Isotropic p q) (l : ℕ) {x : E3} (hx : ‖x‖ = 1) :
    sphLap (SphereLB.Fext p q l) x = -((l : ℝ) * (l + 1)) * SphereLB.Fext p q l x := by
  have hC : ContDiff ℝ 2 (SphereLB.Fext p q l) := by
    rw [SphereLB.Fext_eq]; exact Complex.reCLM.contDiff.comp (SphereLB.contDiff_G p q l)
  refine sphLap_harmonic_homogeneous (fun y _ => hC.contDiffAt)
    (fun r _ y => SphereLB.Fext_homogeneous p q l r y) hx ?_
  rw [SphereLB.laplacian_F p q h l]; rfl

/-- The same for the function on `S²`: `Δ_{S²} f = −l(l+1) f` for `f(y) = Re (a·y)^l`. -/
theorem sphLapS_harmonic (p q : E3) (h : Isotropic p q) (l : ℕ) (x : S2) :
    sphLapS (fun y : S2 => (cdot p q y ^ l).re) x = -((l : ℝ) * (l + 1)) * (cdot p q x ^ l).re := by
  have e := sphLapS_restrict (SphereLB.Fext p q l) x
  rw [show (fun y : S2 => (cdot p q y ^ l).re) = fun z : S2 => SphereLB.Fext p q l z from rfl, e]
  exact sphLap_Fext p q h l (mem_sphere_zero_iff_norm.mp x.2)

/-- **`thm:LB` on `S²` for the harmonics `Re (a·y)^l`, with the operator `Δ_{S²} = sphLapS`:**
for `0 < ξ ≤ 1/20`, isotropic `a = p + i q`, every `l` and `x ∈ S²`, with `λ = l(l+1)`,
`|L_ξ f(x) + Δ_{S²} f(x)| ≤ [(ξ²/6 + 5ξ⁴/12) λ + (51/200) ξ² λ² + (27/200) ξ⁴ λ³] · |f(x)|`. -/
theorem LB_sphere {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (p q : E3) (h : Isotropic p q)
    (l : ℕ) (x : S2) :
    |SphereLB.Lxi ξ (fun y : S2 => (cdot p q y ^ l).re) x
        + sphLapS (fun y : S2 => (cdot p q y ^ l).re) x|
      ≤ ((ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * ((l : ℝ) * (l + 1))
          + 51 / 200 * ξ ^ 2 * ((l : ℝ) * (l + 1)) ^ 2
          + 27 / 200 * ξ ^ 4 * ((l : ℝ) * (l + 1)) ^ 3) * |(cdot p q x ^ l).re| := by
  rw [sphLapS_harmonic p q h l x]
  have hb := SphereLB.Lxi_limit hξ hξ1 p q h l x
  convert hb using 2
  ring

end CTG.FunkHecke.SphereLaplace
