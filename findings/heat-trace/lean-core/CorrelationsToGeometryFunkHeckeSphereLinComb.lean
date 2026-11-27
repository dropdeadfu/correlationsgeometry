/-
Forty-ninth file: Theorem `thm:LB` on `S²` for FINITE LINEAR COMBINATIONS of the harmonics `Re (a·y)^l`.
Namespace `CTG.FunkHecke.SphereLinComb`; imports the forty-fourth file
(`CorrelationsToGeometryFunkHeckeSphereLaplace`, compiled module).  Check with `./check_funk_hecke_sphere_lincomb.sh`.
OPERATORS: `L_ξ = SphereLB.Lxi ξ` (`(2/ξ²)(f − P_∞ f)`, the population walk of the angular Gaussian kernel) and
`Δ_{S²} = SphereLaplace.sphLapS`, which is EXTRINSICALLY defined (`Δ_{ℝ³}` of the degree-zero extension
`y ↦ f(y/‖y‖)`). NOT FORMALISED: that `sphLapS` is the Laplace–Beltrami operator of the Riemannian manifold `S²`.
PROVEN:
 (1) linearity: `zonalOp_add`, `zonalOp_smul`, `zonalOp_sum`, `Lxi_add`, `Lxi_smul`, `Lxi_sum` (bounded measurable
     functions); `sphLapS_add`, `sphLapS_smul`, `sphLapS_sum` under `SphC2 f x` (the degree-zero extension is `C²`
     at `x`); `sphC2_restrict` (`SphC2` holds for restrictions of functions that are `C²` at `x ∈ S²`);
     `sphC2_re`, `sphC2_im`, `bddMeas_re`, `bddMeas_im` for `Re (a·y)^l`, `Im (a·y)^l`; `im_rot`
     (`Im (a·y)^l = Re (a'·y)^l` with isotropic `a' = e^{−iπ/(2l)} a`, `l ≥ 1`) and the eigen-relations
     `Lxi_harmonic_im`, `sphLapS_harmonic_im`, `LB_sphere_im` for the imaginary parts;
 (2) `LB_sphere_sum`: `|L_ξ f + Δ_{S²} f| ≤ Σ_r |c_r| c(ξ,l_r) |f_r(x)|` for `f = Σ c_r Re(a_r·y)^{l_r}`, and
     `LB_sphere_sum_L` (`≤ c(ξ,L) Σ_r |c_r||f_r(x)|` if all `l_r ≤ L`), with `cLB_mono`;
 (3) `LB_sphere_same_degree`: same degree `l`: `L_ξ f = (2/ξ²)(1 − s_l) f`, `Δ_{S²} f = −l(l+1) f` exactly, and
     `|L_ξ f + Δ_{S²} f| ≤ c(ξ,l) |f(x)|` for the combination itself.
NOT FORMALISED: completeness of the spherical harmonics, general smooth functions, any sample statement, the
intrinsic Laplace–Beltrami operator. No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSphereLaplace

open Real Filter Topology Metric MeasureTheory
open scoped RealInnerProductSpace
open Laplacian

namespace CTG.FunkHecke.SphereLinComb

open CTG.FunkHecke (S2 E3 cdot Isotropic gk Pinf zonalOp)
open CTG.FunkHecke.SphereLB (Lxi)
open CTG.FunkHecke.SphereLaplace (ext0 sphLap extS sphLapS)

/-! ### (1a) Linearity of `L_ξ` -/

/-- Bounded measurable functions on `S²`. -/
def BddMeas (f : S2 → ℝ) : Prop := Measurable f ∧ ∃ C, ∀ y, |f y| ≤ C

theorem integrable_kernel (ξ : ℝ) {f : S2 → ℝ} (hf : BddMeas f) (x : S2) :
    Integrable (fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫ * f y) CTG.FunkHecke.sigma := by
  obtain ⟨hm, C, hC⟩ := hf
  refine Integrable.of_bound ?_ C (Filter.Eventually.of_forall fun y => ?_)
  · have hc : Continuous (fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫) :=
      (CTG.FunkHecke.gk_continuous ξ).comp (continuous_const.inner continuous_subtype_val)
    exact (hc.measurable.mul hm).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    calc |gk ξ ⟪(x : E3), (y : E3)⟫| * |f y| ≤ 1 * C :=
          mul_le_mul (CTG.FunkHecke.abs_gk_le ξ _) (hC y) (abs_nonneg _) zero_le_one
      _ = C := one_mul C

theorem zonalOp_add (ξ : ℝ) {f g : S2 → ℝ} (hf : BddMeas f) (hg : BddMeas g) (x : S2) :
    zonalOp (gk ξ) (fun y => f y + g y) x = zonalOp (gk ξ) f x + zonalOp (gk ξ) g x := by
  unfold zonalOp
  rw [← integral_add (integrable_kernel ξ hf x) (integrable_kernel ξ hg x)]
  congr 1; funext y; ring

theorem zonalOp_smul (ξ c : ℝ) (f : S2 → ℝ) (x : S2) :
    zonalOp (gk ξ) (fun y => c * f y) x = c * zonalOp (gk ξ) f x := by
  unfold zonalOp
  rw [← integral_const_mul]
  congr 1; funext y; ring

theorem zonalOp_sum (ξ : ℝ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → S2 → ℝ)
    (hF : ∀ r ∈ s, BddMeas (F r)) (x : S2) :
    zonalOp (gk ξ) (fun y => ∑ r ∈ s, c r * F r y) x = ∑ r ∈ s, c r * zonalOp (gk ξ) (F r) x := by
  unfold zonalOp
  have e : (fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫ * ∑ r ∈ s, c r * F r y)
      = fun y : S2 => ∑ r ∈ s, c r * (gk ξ ⟪(x : E3), (y : E3)⟫ * F r y) := by
    funext y; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; ring
  rw [e, integral_finset_sum]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [integral_const_mul]
  · intro r hr
    exact (integrable_kernel ξ (hF r hr) x).const_mul (c r)

theorem Lxi_add (ξ : ℝ) {f g : S2 → ℝ} (hf : BddMeas f) (hg : BddMeas g) (x : S2) :
    Lxi ξ (fun y => f y + g y) x = Lxi ξ f x + Lxi ξ g x := by
  unfold Lxi Pinf
  rw [zonalOp_add ξ hf hg x]
  ring

theorem Lxi_smul (ξ c : ℝ) (f : S2 → ℝ) (x : S2) :
    Lxi ξ (fun y => c * f y) x = c * Lxi ξ f x := by
  unfold Lxi Pinf
  rw [zonalOp_smul ξ c f x]
  ring

theorem Lxi_sum (ξ : ℝ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → S2 → ℝ)
    (hF : ∀ r ∈ s, BddMeas (F r)) (x : S2) :
    Lxi ξ (fun y => ∑ r ∈ s, c r * F r y) x = ∑ r ∈ s, c r * Lxi ξ (F r) x := by
  unfold Lxi Pinf
  rw [zonalOp_sum ξ s c F hF x, Finset.sum_div, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-! ### (1b) Linearity of `Δ_{S²}` -/

/-- Regularity hypothesis for `sphLapS` at `x`: the degree-zero extension is `C²` at `x`. -/
def SphC2 (f : S2 → ℝ) (x : S2) : Prop := ContDiffAt ℝ 2 (ext0 (extS f)) (x : E3)

theorem ext0_extS_add (f g : S2 → ℝ) :
    ext0 (extS (fun y => f y + g y)) = ext0 (extS f) + ext0 (extS g) := by
  funext y
  simp only [ext0, extS, Pi.add_apply]
  split_ifs <;> simp

theorem ext0_extS_smul (c : ℝ) (f : S2 → ℝ) :
    ext0 (extS (fun y => c * f y)) = c • ext0 (extS f) := by
  funext y
  simp only [ext0, extS, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem ext0_extS_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → S2 → ℝ) :
    ext0 (extS (fun y => ∑ r ∈ s, c r * F r y)) = fun z => ∑ r ∈ s, c r * ext0 (extS (F r)) z := by
  funext y
  simp only [ext0, extS]
  split_ifs <;> simp

theorem laplacian_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (G : ι → E3 → ℝ) (x : E3)
    (hG : ∀ r ∈ s, ContDiffAt ℝ 2 (G r) x) :
    Δ (fun z => ∑ r ∈ s, c r * G r z) x = ∑ r ∈ s, c r * Δ (G r) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [InnerProductSpace.laplacian_const]; rfl
  | insert a s ha ih =>
    have hs : ∀ r ∈ s, ContDiffAt ℝ 2 (G r) x := fun r hr => hG r (Finset.mem_insert_of_mem hr)
    have ha' : ContDiffAt ℝ 2 (G a) x := hG a (Finset.mem_insert_self a s)
    have hA : ContDiffAt ℝ 2 (fun z => c a * G a z) x := contDiffAt_const.mul ha'
    have hB : ContDiffAt ℝ 2 (fun z => ∑ r ∈ s, c r * G r z) x :=
      ContDiffAt.sum fun r hr => contDiffAt_const.mul (hs r hr)
    simp only [Finset.sum_insert ha]
    rw [show (fun z => c a * G a z + ∑ r ∈ s, c r * G r z)
        = (fun z => c a * G a z) + (fun z => ∑ r ∈ s, c r * G r z) from rfl,
      hA.laplacian_add hB, ih hs,
      show (fun z => c a * G a z) = c a • G a from rfl, InnerProductSpace.laplacian_smul (c a) ha', smul_eq_mul]

theorem sphLapS_add {f g : S2 → ℝ} {x : S2} (hf : SphC2 f x) (hg : SphC2 g x) :
    sphLapS (fun y => f y + g y) x = sphLapS f x + sphLapS g x := by
  unfold sphLapS sphLap
  rw [ext0_extS_add]
  exact hf.laplacian_add hg

theorem sphLapS_smul (c : ℝ) {f : S2 → ℝ} {x : S2} (hf : SphC2 f x) :
    sphLapS (fun y => c * f y) x = c * sphLapS f x := by
  unfold sphLapS sphLap
  rw [ext0_extS_smul, InnerProductSpace.laplacian_smul c hf, smul_eq_mul]

theorem sphLapS_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → S2 → ℝ) (x : S2)
    (hF : ∀ r ∈ s, SphC2 (F r) x) :
    sphLapS (fun y => ∑ r ∈ s, c r * F r y) x = ∑ r ∈ s, c r * sphLapS (F r) x := by
  unfold sphLapS sphLap
  rw [ext0_extS_sum]
  exact laplacian_finset_sum s c (fun r => ext0 (extS (F r))) (x : E3) hF

theorem S2_ne_zero (x : S2) : (x : E3) ≠ 0 := by
  intro h; have := mem_sphere_zero_iff_norm.mp x.2; rw [h, norm_zero] at this
  exact zero_ne_one this

/-- `SphC2` holds for restrictions of functions on `ℝ³` that are `C²` at `x ∈ S²` (in particular for
restrictions of `C²` functions on `ℝ³ ∖ {0}`). -/
theorem sphC2_restrict (G : E3 → ℝ) (x : S2) (hG : ContDiffAt ℝ 2 G (x : E3)) :
    SphC2 (fun z : S2 => G z) x := by
  have hx0 := S2_ne_zero x
  have hx1 : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hne : ∀ᶠ y in 𝓝 (x : E3), y ≠ 0 := isOpen_ne.mem_nhds hx0
  have heq : ext0 (extS (fun z : S2 => G z)) =ᶠ[𝓝 (x : E3)] ext0 G := by
    filter_upwards [hne] with y hy
    exact SphereLaplace.ext0_extS_restrict G hy
  have hN : ContDiffAt ℝ 2 (fun y : E3 => ‖y‖⁻¹ • y) (x : E3) :=
    ((contDiffAt_norm ℝ hx0).inv (norm_ne_zero_iff.mpr hx0)).smul contDiffAt_id
  have hfx : ‖(x : E3)‖⁻¹ • (x : E3) = (x : E3) := by rw [hx1, inv_one, one_smul]
  have hG' : ContDiffAt ℝ 2 G (‖(x : E3)‖⁻¹ • (x : E3)) := by rw [hfx]; exact hG
  have hc : ContDiffAt ℝ 2 (ext0 G) (x : E3) :=
    ContDiffAt.comp (g := G) (f := fun y : E3 => ‖y‖⁻¹ • y) (x : E3) hG' hN
  exact hc.congr_of_eventuallyEq heq

/-! ### (1c) The harmonics `Re (a·y)^l`, `Im (a·y)^l` -/

/-- Imaginary part extension `Im (a·y)^l` on `ℝ³`. -/
noncomputable def Fim (p q : E3) (l : ℕ) (y : E3) : ℝ := (cdot p q y ^ l).im

theorem Fim_eq (p q : E3) (l : ℕ) : Fim p q l = Complex.imCLM ∘ SphereLB.Gext p q l := by
  funext y; simp [Fim, SphereLB.Gext, SphereLB.Lform_apply]

theorem contDiff_Fext (p q : E3) (l : ℕ) : ContDiff ℝ 2 (SphereLB.Fext p q l) := by
  rw [SphereLB.Fext_eq]; exact Complex.reCLM.contDiff.comp (SphereLB.contDiff_G p q l)

theorem contDiff_Fim (p q : E3) (l : ℕ) : ContDiff ℝ 2 (Fim p q l) := by
  rw [Fim_eq]; exact Complex.imCLM.contDiff.comp (SphereLB.contDiff_G p q l)

theorem sphC2_re (p q : E3) (l : ℕ) (x : S2) : SphC2 (fun y : S2 => (cdot p q y ^ l).re) x :=
  sphC2_restrict (SphereLB.Fext p q l) x (contDiff_Fext p q l).contDiffAt

theorem sphC2_im (p q : E3) (l : ℕ) (x : S2) : SphC2 (fun y : S2 => (cdot p q y ^ l).im) x :=
  sphC2_restrict (Fim p q l) x (contDiff_Fim p q l).contDiffAt

theorem cdot_pow_norm_le (p q : E3) (l : ℕ) (y : S2) : ‖cdot p q y ^ l‖ ≤ (‖p‖ + ‖q‖) ^ l := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (CTG.FunkHecke.norm_cdot_le p q _ (mem_sphere_zero_iff_norm.1 y.2)) l

theorem bddMeas_re (p q : E3) (l : ℕ) : BddMeas (fun y : S2 => (cdot p q y ^ l).re) := by
  refine ⟨?_, (‖p‖ + ‖q‖) ^ l, fun y => (Complex.abs_re_le_norm _).trans (cdot_pow_norm_le p q l y)⟩
  exact Complex.measurable_re.comp
    (((CTG.FunkHecke.continuous_cdot p q).comp continuous_subtype_val).measurable.pow_const l)

theorem bddMeas_im (p q : E3) (l : ℕ) : BddMeas (fun y : S2 => (cdot p q y ^ l).im) := by
  refine ⟨?_, (‖p‖ + ‖q‖) ^ l, fun y => (Complex.abs_im_le_norm _).trans (cdot_pow_norm_le p q l y)⟩
  exact Complex.measurable_im.comp
    (((CTG.FunkHecke.continuous_cdot p q).comp continuous_subtype_val).measurable.pow_const l)

/-- For `l ≥ 1`, `Im (a·y)^l = Re (a'·y)^l` with the isotropic `a' = e^{−iθ} a`, `θ = π/(2l)`. -/
theorem im_rot (p q : E3) (h : Isotropic p q) {l : ℕ} (hl : 0 < l) :
    ∃ p' q' : E3, Isotropic p' q' ∧ ∀ y, (cdot p q y ^ l).im = (cdot p' q' y ^ l).re := by
  set θ : ℝ := π / (2 * l) with hθ
  set c := Real.cos θ
  set s := Real.sin θ
  refine ⟨c • p + s • q, c • q - s • p, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := h
    have h3 : ⟪q, p⟫ = 0 := by rw [real_inner_comm]; exact h2
    have hcs : c ^ 2 + s ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
    constructor
    · simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      simp only [h1, h2, h3]
      ring
    · simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      simp only [h1, h2, h3]
      ring
  · intro y
    have hc : cdot (c • p + s • q) (c • q - s • p) y = ((c : ℂ) - s * Complex.I) * cdot p q y := by
      apply Complex.ext <;>
        simp [CTG.FunkHecke.cdot, inner_add_left, inner_sub_left, real_inner_smul_left] <;> ring
    have hr : (l : ℝ) * θ = π / 2 := by
      rw [hθ]; have : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
      field_simp
    have hw : ((c : ℂ) - s * Complex.I) ^ l = -Complex.I := by
      have e1 : ((c : ℂ) - s * Complex.I) = Complex.cos (-(θ : ℂ)) + Complex.sin (-(θ : ℂ)) * Complex.I := by
        rw [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; ring
      have e2 : (l : ℂ) * -(θ : ℂ) = -((π / 2 : ℝ) : ℂ) := by
        rw [← hr]; push_cast; ring
      rw [e1, Complex.cos_add_sin_mul_I_pow, e2, Complex.cos_neg, Complex.sin_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    rw [hc, mul_pow, hw]
    simp [Complex.mul_re]

/-- `L_ξ` on `Im (a·y)^l`: multiplication by `(2/ξ²)(1 − s_l)`. -/
theorem Lxi_harmonic_im (ξ : ℝ) (p q : E3) (h : Isotropic p q) (l : ℕ) (x : S2) :
    Lxi ξ (fun y => (cdot p q y ^ l).im) x
      = 2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) * (cdot p q x ^ l).im := by
  rcases Nat.eq_zero_or_pos l with h0 | hl
  · subst h0
    simp [Lxi, Pinf, CTG.FunkHecke.zonalOp]
  · obtain ⟨p', q', h', he⟩ := im_rot p q h hl
    have hf : (fun y : S2 => (cdot p q y ^ l).im) = fun y : S2 => (cdot p' q' y ^ l).re := by
      funext y; exact he y
    rw [hf, SphereLB.Lxi_harmonic ξ p' q' h' l x, he]

/-- `Δ_{S²}` on `Im (a·y)^l`: eigenvalue `−l(l+1)`. -/
theorem sphLapS_harmonic_im (p q : E3) (h : Isotropic p q) (l : ℕ) (x : S2) :
    sphLapS (fun y : S2 => (cdot p q y ^ l).im) x = -((l : ℝ) * (l + 1)) * (cdot p q x ^ l).im := by
  rcases Nat.eq_zero_or_pos l with h0 | hl
  · subst h0
    have e : (fun y : S2 => (cdot p q y ^ 0).im) = fun y : S2 => (0:ℝ) * (cdot p q y ^ 0).re := by
      funext y; simp
    rw [e, sphLapS_smul 0 (sphC2_re p q 0 x)]
    simp
  · obtain ⟨p', q', h', he⟩ := im_rot p q h hl
    have hf : (fun y : S2 => (cdot p q y ^ l).im) = fun y : S2 => (cdot p' q' y ^ l).re := by
      funext y; exact he y
    rw [hf, SphereLaplace.sphLapS_harmonic p' q' h' l x, he]

/-! ### (2) `thm:LB` on `S²` for finite linear combinations -/

/-- The error constant `c(ξ,l)` of `LB_sphere`. -/
noncomputable def cLB (ξ : ℝ) (l : ℕ) : ℝ :=
  (ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * ((l : ℝ) * (l + 1)) + 51 / 200 * ξ ^ 2 * ((l : ℝ) * (l + 1)) ^ 2
    + 27 / 200 * ξ ^ 4 * ((l : ℝ) * (l + 1)) ^ 3

theorem cLB_nonneg (ξ : ℝ) (l : ℕ) : 0 ≤ cLB ξ l := by
  unfold cLB; positivity

theorem cLB_mono (ξ : ℝ) {l L : ℕ} (hlL : l ≤ L) : cLB ξ l ≤ cLB ξ L := by
  unfold cLB
  have h0 : (0 : ℝ) ≤ (l : ℝ) * (l + 1) := by positivity
  have h1 : (l : ℝ) * (l + 1) ≤ (L : ℝ) * (L + 1) := by
    have : (l : ℝ) ≤ L := by exact_mod_cast hlL
    nlinarith
  have a1 : 0 ≤ ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4 := by positivity
  have a2 : 0 ≤ 51 / 200 * ξ ^ 2 := by positivity
  have a3 : 0 ≤ 27 / 200 * ξ ^ 4 := by positivity
  have p2 := pow_le_pow_left₀ h0 h1 2
  have p3 := pow_le_pow_left₀ h0 h1 3
  have := mul_le_mul_of_nonneg_left h1 a1
  have := mul_le_mul_of_nonneg_left p2 a2
  have := mul_le_mul_of_nonneg_left p3 a3
  linarith

/-- `LB_sphere` for the imaginary parts. -/
theorem LB_sphere_im {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (p q : E3) (h : Isotropic p q)
    (l : ℕ) (x : S2) :
    |Lxi ξ (fun y : S2 => (cdot p q y ^ l).im) x + sphLapS (fun y : S2 => (cdot p q y ^ l).im) x|
      ≤ cLB ξ l * |(cdot p q x ^ l).im| := by
  rw [Lxi_harmonic_im ξ p q h l x, sphLapS_harmonic_im p q h l x]
  have he := SphereLB.eig_limit hξ hξ1 l
  rw [show 2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) * (cdot p q x ^ l).im
      + -((l : ℝ) * (l + 1)) * (cdot p q x ^ l).im
      = (2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) - (l : ℝ) * (l + 1)) * (cdot p q x ^ l).im by ring,
    abs_mul]
  exact mul_le_mul_of_nonneg_right he (abs_nonneg _)

/-- **`thm:LB` on `S²` for finite linear combinations of harmonics** (operator `Δ_{S²} = sphLapS`,
extrinsic): for `f = Σ_{r∈s} c_r Re (a_r·y)^{l_r}` (`a_r = P_r + i Q_r` isotropic), `0 < ξ ≤ 1/20`, `x ∈ S²`:
`|L_ξ f(x) + Δ_{S²} f(x)| ≤ Σ_r |c_r| c(ξ,l_r) |Re (a_r·x)^{l_r}|`. -/
theorem LB_sphere_sum {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (P Q : ι → E3) (deg : ι → ℕ) (hiso : ∀ r ∈ s, Isotropic (P r) (Q r)) (x : S2) :
    |Lxi ξ (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ deg r).re) x
        + sphLapS (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ deg r).re) x|
      ≤ ∑ r ∈ s, |c r| * cLB ξ (deg r) * |(cdot (P r) (Q r) x ^ deg r).re| := by
  rw [Lxi_sum ξ s c (fun r y => (cdot (P r) (Q r) y ^ deg r).re)
      (fun r _ => bddMeas_re (P r) (Q r) (deg r)) x,
    sphLapS_sum s c (fun r y => (cdot (P r) (Q r) y ^ deg r).re) x
      (fun r _ => sphC2_re (P r) (Q r) (deg r) x), ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
  rw [← mul_add, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (SphereLaplace.LB_sphere hξ hξ1 _ _ (hiso r hr) (deg r) x)
    (abs_nonneg _)

/-- The same with one constant: if all degrees are `≤ L`,
`|L_ξ f(x) + Δ_{S²} f(x)| ≤ c(ξ,L) Σ_r |c_r| |Re (a_r·x)^{l_r}|` (error `O(ξ²)` for fixed `L`). -/
theorem LB_sphere_sum_L {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (P Q : ι → E3) (deg : ι → ℕ) (hiso : ∀ r ∈ s, Isotropic (P r) (Q r))
    (L : ℕ) (hL : ∀ r ∈ s, deg r ≤ L) (x : S2) :
    |Lxi ξ (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ deg r).re) x
        + sphLapS (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ deg r).re) x|
      ≤ cLB ξ L * ∑ r ∈ s, |c r| * |(cdot (P r) (Q r) x ^ deg r).re| := by
  refine (LB_sphere_sum hξ hξ1 s c P Q deg hiso x).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hm := cLB_mono ξ (hL r hr)
  have h0 : 0 ≤ |c r| * |(cdot (P r) (Q r) x ^ deg r).re| := by positivity
  calc |c r| * cLB ξ (deg r) * |(cdot (P r) (Q r) x ^ deg r).re|
      = cLB ξ (deg r) * (|c r| * |(cdot (P r) (Q r) x ^ deg r).re|) := by ring
    _ ≤ cLB ξ L * (|c r| * |(cdot (P r) (Q r) x ^ deg r).re|) := mul_le_mul_of_nonneg_right hm h0

/-! ### (3) Same degree: the combination is itself an eigenfunction -/

/-- **Same degree `l`**: for `f = Σ_r c_r Re (a_r·y)^l`, `L_ξ f = (2/ξ²)(1 − s_l) f` and
`Δ_{S²} f = −l(l+1) f` exactly, and `|L_ξ f(x) + Δ_{S²} f(x)| ≤ c(ξ,l) |f(x)|`
(no triangle inequality over the summands). -/
theorem LB_sphere_same_degree {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (P Q : ι → E3) (l : ℕ) (hiso : ∀ r ∈ s, Isotropic (P r) (Q r)) (x : S2) :
    Lxi ξ (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ l).re) x
        = 2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) * ∑ r ∈ s, c r * (cdot (P r) (Q r) x ^ l).re
      ∧ sphLapS (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ l).re) x
        = -((l : ℝ) * (l + 1)) * ∑ r ∈ s, c r * (cdot (P r) (Q r) x ^ l).re
      ∧ |Lxi ξ (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ l).re) x
          + sphLapS (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ l).re) x|
        ≤ cLB ξ l * |∑ r ∈ s, c r * (cdot (P r) (Q r) x ^ l).re| := by
  have hL : Lxi ξ (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ l).re) x
      = 2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) * ∑ r ∈ s, c r * (cdot (P r) (Q r) x ^ l).re := by
    rw [Lxi_sum ξ s c (fun r y => (cdot (P r) (Q r) y ^ l).re)
      (fun r _ => bddMeas_re (P r) (Q r) l) x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [SphereLB.Lxi_harmonic ξ (P r) (Q r) (hiso r hr) l x]; ring
  have hD : sphLapS (fun y => ∑ r ∈ s, c r * (cdot (P r) (Q r) y ^ l).re) x
      = -((l : ℝ) * (l + 1)) * ∑ r ∈ s, c r * (cdot (P r) (Q r) x ^ l).re := by
    rw [sphLapS_sum s c (fun r y => (cdot (P r) (Q r) y ^ l).re) x
      (fun r _ => sphC2_re (P r) (Q r) l x), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [SphereLaplace.sphLapS_harmonic (P r) (Q r) (hiso r hr) l x]; ring
  refine ⟨hL, hD, ?_⟩
  rw [hL, hD]
  have he := SphereLB.eig_limit hξ hξ1 l
  rw [← add_mul, abs_mul,
    show 2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) + -((l : ℝ) * (l + 1))
      = 2 / ξ ^ 2 * (1 - CTG.FunkHecke.sphS ξ l) - (l : ℝ) * (l + 1) by ring]
  exact mul_le_mul_of_nonneg_right he (abs_nonneg _)

end CTG.FunkHecke.SphereLinComb
