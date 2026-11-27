/-
Sixty-seventh file: orthogonality of the degrees of harmonics on `S²` and the projection onto a degree.
Namespace `CTG.FunkHecke.Proj`; imports the compiled modules of the sixty-fifth and twenty-first files; check with
`./check_funk_hecke_proj.sh`.
Weight `w = P_l` (cut off outside `[−1,1]`): by Funk–Hecke and `∫_{−1}^1 P_m P_n = 2δ_{mn}/(2n+1)` the harmonics of
degree `k` are eigenfunctions of the zonal operator with eigenvalue `δ_{lk}/(2l+1)`; the zonal operator is symmetric
(Fubini).  `orth_harm`, `orth_span`: harmonics of different degrees are orthogonal in `L²(σ)`, for every pair of degrees.
`harmDeg l`: the span of `Re/Im (a·y)^l` (`a` isotropic) in `C(S²)`; `harmDeg_finiteDimensional`.
`projDeg l f = (2l+1) ∫ P_l(⟨x,y⟩) f(y) dσ(y)` (`σ` has mass 1): `proj_self`, `proj_other`, `proj_symm`, `proj_mem`
(`Π_l f` lies in `harmDeg l` for every continuous `f`), `proj_idem`, `proj_orth` (`f − Π_l f ⊥ harmDeg l`).
NOT formalised: dimension exactly `2l+1`; convergence of `Σ_l Π_l f` to `f` (in `L²` or uniformly for smooth `f`),
Parseval, decay of `Π_l f` from smoothness — the input that `LB_sphere_series_M` needs; `L²` functions; the link of
`harmDeg` with `harmSpan`/`degPart` beyond `harm_memDeg`.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeComplete
import CorrelationsToGeometryFunkHeckeMult

open MeasureTheory Set Metric Real
open scoped RealInnerProductSpace

namespace CTG.FunkHecke.Proj

open CTG.FunkHecke

local instance : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

theorem sigma_real_univ' : sigma.real univ = 1 := by
  have h := integral_sigma (fun _ => (1:ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [h, sigma0_real_univ]
  field_simp

local instance : IsProbabilityMeasure sigma :=
  ⟨by rw [← ofReal_measureReal, sigma_real_univ', ENNReal.ofReal_one]⟩

/-- Continuous real functions on a compact space are integrable for a finite measure. -/
theorem integrable_of_cont {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] {F : X → ℝ} (hF : Continuous F) : Integrable F μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hF.continuousOn
  exact Integrable.of_bound hF.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => hC y (mem_univ y))

theorem inner_mem (x y : S2) : ⟪(x : E3), (y : E3)⟫ ∈ Icc (-1:ℝ) 1 := by
  have h := abs_real_inner_le_norm (x : E3) (y : E3)
  rw [mem_sphere_zero_iff_norm.1 x.2, mem_sphere_zero_iff_norm.1 y.2, one_mul] at h
  exact abs_le.1 h

/-! ## Legendre integrals on `[-1,1]` -/

theorem legInt (m n : ℕ) :
    ∫ t in (-1:ℝ)..1, legP m t * legP n t = if m = n then 2 / (2 * (n : ℝ) + 1) else 0 := by
  rw [← cos_subst (fun t => legP m t * legP n t) ((legP_continuous m).mul (legP_continuous n))]
  have h : ∫ θ in (0:ℝ)..π, legP m (Real.cos θ) * legP n (Real.cos θ) * Real.sin θ
      = CTG.Reals2.SphereOneDim.ip (CTG.Reals2.SphereOneDim.lf m) (CTG.Reals2.SphereOneDim.lf n) := by
    unfold CTG.Reals2.SphereOneDim.ip CTG.Reals2.SphereOneDim.lf
    simp only [CTG.FunkHeckeLink.legP_eq]
  rw [h]
  split_ifs with hmn
  · subst hmn; exact CTG.Reals2.SphereOneDim.ip_norm m
  · exact CTG.Reals2.SphereOneDim.ip_orth hmn

/-- The eigenvalue `λ_k(P_l) = ½∫_{-1}^1 P_l P_k`. -/
noncomputable def lamDeg (l k : ℕ) : ℝ := (1/2) * ∫ t in (-1:ℝ)..1, legP l t * legP k t

theorem lamDeg_self (l : ℕ) : lamDeg l l = 1 / (2 * (l : ℝ) + 1) := by
  unfold lamDeg; rw [legInt, if_pos rfl]; field_simp

theorem lamDeg_ne {l k : ℕ} (h : l ≠ k) : lamDeg l k = 0 := by
  unfold lamDeg; rw [legInt, if_neg h, mul_zero]

/-! ## The clipped Legendre weight (bounded on `ℝ`, equal to `P_l` on `[-1,1]`) -/

noncomputable def clip (t : ℝ) : ℝ := max (-1) (min 1 t)

theorem clip_mem (t : ℝ) : clip t ∈ Icc (-1:ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clip_of_mem {t : ℝ} (h : t ∈ Icc (-1:ℝ) 1) : clip t = t := by
  unfold clip; rw [min_eq_right h.2, max_eq_right h.1]

theorem continuous_clip : Continuous clip :=
  continuous_const.max (continuous_const.min continuous_id)

noncomputable def wl (l : ℕ) (t : ℝ) : ℝ := legP l (clip t)

theorem wl_continuous (l : ℕ) : Continuous (wl l) := (legP_continuous l).comp continuous_clip

theorem wl_bound (l : ℕ) (t : ℝ) : |wl l t| ≤ 1 := by
  unfold wl
  rw [CTG.FunkHeckeLink.legP_eq]
  exact CTG.Reals2.SphereOneDim.abs_legP_le (clip_mem t).1 (clip_mem t).2 l

theorem wl_int (l k : ℕ) :
    ∫ t in (-1:ℝ)..1, wl l t * legP k t = ∫ t in (-1:ℝ)..1, legP l t * legP k t := by
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [uIcc_of_le (by norm_num)] at ht
  simp only [wl, clip_of_mem ht]

theorem zonalOp_wl (l : ℕ) (f : S2 → ℝ) (x : S2) : zonalOp (wl l) f x = zonalOp (legP l) f x := by
  unfold zonalOp
  congr 1; ext y
  simp only [wl, clip_of_mem (inner_mem x y)]

/-! ## Harmonics of degree `l` and their eigenvalues -/

/-- `f` is `Re (a·y)^l` or `Im (a·y)^l` for an isotropic `a = p + i q`. -/
def IsHarm (l : ℕ) (f : S2 → ℝ) : Prop :=
  ∃ p q : E3, Isotropic p q ∧
    (f = (fun y : S2 => (cdot p q (y : E3) ^ l).re) ∨ f = (fun y : S2 => (cdot p q (y : E3) ^ l).im))

theorem IsHarm.continuous {l : ℕ} {f : S2 → ℝ} (hf : IsHarm l f) : Continuous f := by
  obtain ⟨p, q, _, h | h⟩ := hf <;> subst h
  · exact Complex.continuous_re.comp (((continuous_cdot p q).comp continuous_subtype_val).pow l)
  · exact Complex.continuous_im.comp (((continuous_cdot p q).comp continuous_subtype_val).pow l)

/-- Funk–Hecke with the weight `P_n`: a harmonic of degree `l` is an eigenfunction, eigenvalue `lamDeg n l`. -/
theorem IsHarm.eigen {l : ℕ} {f : S2 → ℝ} (hf : IsHarm l f) (n : ℕ) (x : S2) :
    zonalOp (legP n) f x = lamDeg n l * f x := by
  rw [← zonalOp_wl]
  obtain ⟨p, q, hpq, h | h⟩ := hf <;> subst h
  · rw [zonalOp_harmonic (wl n) (wl_continuous n).measurable 1 (wl_bound n) p q hpq l x, wl_int]; rfl
  · rw [CTG.FunkHecke.Mult.zonalOp_harmonic_im (wl n) (wl_continuous n).measurable 1 (wl_bound n)
      p q hpq l x, wl_int]; rfl

/-! ## Symmetry of the zonal operator -/

/-- `∫ g · T_w f = ∫ f · T_w g` for continuous `f`, `g`, `w` (Fubini on `S² × S²`). -/
theorem zonal_symm (w : ℝ → ℝ) (hw : Continuous w) (f g : S2 → ℝ) (hf : Continuous f)
    (hg : Continuous g) :
    ∫ x, g x * zonalOp w f x ∂sigma = ∫ x, f x * zonalOp w g x ∂sigma := by
  have hc : Continuous (Function.uncurry fun (x y : S2) => g x * (w ⟪(x : E3), (y : E3)⟫ * f y)) := by
    show Continuous (fun z : S2 × S2 => g z.1 * (w ⟪(z.1 : E3), (z.2 : E3)⟫ * f z.2))
    exact (hg.comp continuous_fst).mul ((hw.comp ((continuous_subtype_val.comp continuous_fst).inner
      (continuous_subtype_val.comp continuous_snd))).mul (hf.comp continuous_snd))
  have hF := integrable_of_cont (sigma.prod sigma) hc
  unfold zonalOp
  calc ∫ x, g x * ∫ y, w ⟪(x : E3), (y : E3)⟫ * f y ∂sigma ∂sigma
      = ∫ x, ∫ y, g x * (w ⟪(x : E3), (y : E3)⟫ * f y) ∂sigma ∂sigma := by
        congr 1; ext x; rw [integral_const_mul]
    _ = ∫ y, ∫ x, g x * (w ⟪(x : E3), (y : E3)⟫ * f y) ∂sigma ∂sigma := integral_integral_swap hF
    _ = ∫ y, f y * ∫ x, w ⟪(y : E3), (x : E3)⟫ * g x ∂sigma ∂sigma := by
        congr 1; ext y; rw [← integral_const_mul]; congr 1; ext x
        rw [real_inner_comm]; ring

/-- Eigenfunctions of a zonal operator with different eigenvalues are orthogonal. -/
theorem eigen_orth (w : ℝ → ℝ) (hw : Continuous w) (f g : S2 → ℝ) (hf : Continuous f)
    (hg : Continuous g) (a1 a2 : ℝ) (hfe : ∀ x, zonalOp w f x = a1 * f x)
    (hge : ∀ x, zonalOp w g x = a2 * g x) (hne : a1 ≠ a2) :
    ∫ x, f x * g x ∂sigma = 0 := by
  have h := zonal_symm w hw f g hf hg
  simp only [hfe, hge] at h
  have e1 : ∫ x, g x * (a1 * f x) ∂sigma = a1 * ∫ x, f x * g x ∂sigma := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  have e2 : ∫ x, f x * (a2 * g x) ∂sigma = a2 * ∫ x, f x * g x ∂sigma := by
    rw [← integral_const_mul]; congr 1; ext x; ring
  rw [e1, e2] at h
  have : (a1 - a2) * ∫ x, f x * g x ∂sigma = 0 := by rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

/-! ## Stage 1: orthogonality of harmonics of different degrees -/

/-- **Orthogonality of the degrees**: `∫_{S²} f g dσ = 0` for `f = Re/Im (a·y)^l`, `g = Re/Im (b·y)^k`, `a`, `b`
isotropic, `l ≠ k`. -/
theorem orth_harm {l k : ℕ} (hlk : l ≠ k) {f g : S2 → ℝ} (hf : IsHarm l f) (hg : IsHarm k g) :
    ∫ x, f x * g x ∂sigma = 0 := by
  refine eigen_orth (legP l) (legP_continuous l) f g hf.continuous hg.continuous (lamDeg l l)
    (lamDeg l k) (hf.eigen l) (hg.eigen l) ?_
  rw [lamDeg_self, lamDeg_ne hlk]; positivity

/-! ## Stage 2: the span of degree `l` and the projection `Π_l` -/

/-- The generators of degree `l` as continuous functions. -/
def GenDeg (l : ℕ) : Set C(S2, ℝ) := {F | IsHarm l F}

/-- The real span `H_l` of `Re (a·y)^l`, `Im (a·y)^l`, `a` isotropic. -/
noncomputable def harmDeg (l : ℕ) : Submodule ℝ C(S2, ℝ) := Submodule.span ℝ (GenDeg l)

theorem zonalOp_add (w : ℝ → ℝ) (hw : Continuous w) (F G : C(S2, ℝ)) (x : S2) :
    zonalOp w ⇑(F + G) x = zonalOp w F x + zonalOp w G x := by
  unfold zonalOp
  have hk : Continuous fun y : S2 => w ⟪(x : E3), (y : E3)⟫ :=
    hw.comp (continuous_const.inner continuous_subtype_val)
  have h1 : Integrable (fun y : S2 => w ⟪(x : E3), (y : E3)⟫ * F y) sigma :=
    integrable_of_cont sigma (hk.mul F.continuous)
  have h2 : Integrable (fun y : S2 => w ⟪(x : E3), (y : E3)⟫ * G y) sigma :=
    integrable_of_cont sigma (hk.mul G.continuous)
  rw [← integral_add h1 h2]
  congr 1; ext y; simp only [ContinuousMap.coe_add, Pi.add_apply]; ring

theorem zonalOp_smul (w : ℝ → ℝ) (c : ℝ) (F : C(S2, ℝ)) (x : S2) :
    zonalOp w ⇑(c • F) x = c * zonalOp w F x := by
  unfold zonalOp
  rw [← integral_const_mul]
  congr 1; ext y; simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

theorem zonalOp_zero (w : ℝ → ℝ) (x : S2) : zonalOp w ⇑(0 : C(S2, ℝ)) x = 0 := by
  unfold zonalOp; simp

/-- Every element of `H_l` is an eigenfunction of `T_{P_n}` with eigenvalue `lamDeg n l`. -/
theorem eigen_span {l : ℕ} {F : C(S2, ℝ)} (hF : F ∈ harmDeg l) (n : ℕ) (x : S2) :
    zonalOp (legP n) F x = lamDeg n l * F x := by
  induction hF using Submodule.span_induction generalizing x with
  | mem F hF => exact IsHarm.eigen hF n x
  | zero => rw [zonalOp_zero]; simp
  | add F G _ _ hF hG =>
      rw [zonalOp_add _ (legP_continuous n), hF, hG]; simp only [ContinuousMap.coe_add, Pi.add_apply]
      ring
  | smul c F _ hF =>
      rw [zonalOp_smul, hF]; simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

/-- The projection onto degree `l`: `Π_l f(x) = (2l+1) ∫ P_l(⟨x,y⟩) f(y) dσ(y)` (`σ` has mass `1`). -/
noncomputable def projDeg (l : ℕ) (f : S2 → ℝ) (x : S2) : ℝ :=
  (2 * (l : ℝ) + 1) * zonalOp (legP l) f x

/-- `Π_l F = F` on `H_l`. -/
theorem proj_self {l : ℕ} {F : C(S2, ℝ)} (hF : F ∈ harmDeg l) (x : S2) : projDeg l F x = F x := by
  unfold projDeg
  rw [eigen_span hF l x, lamDeg_self]
  field_simp

/-- `Π_l G = 0` on `H_k`, `k ≠ l`. -/
theorem proj_other {l k : ℕ} (hlk : l ≠ k) {G : C(S2, ℝ)} (hG : G ∈ harmDeg k) (x : S2) :
    projDeg l G x = 0 := by
  unfold projDeg
  rw [eigen_span hG l x, lamDeg_ne hlk]; ring

/-- Orthogonality for whole spans: `∫ F G dσ = 0` for `F ∈ H_l`, `G ∈ H_k`, `l ≠ k`. -/
theorem orth_span {l k : ℕ} (hlk : l ≠ k) {F G : C(S2, ℝ)} (hF : F ∈ harmDeg l)
    (hG : G ∈ harmDeg k) : ∫ x, F x * G x ∂sigma = 0 := by
  refine eigen_orth (legP l) (legP_continuous l) F G F.continuous G.continuous (lamDeg l l)
    (lamDeg l k) (eigen_span hF l) (eigen_span hG l) ?_
  rw [lamDeg_self, lamDeg_ne hlk]; positivity

/-- `Π_l` is self-adjoint: `∫ g Π_l f = ∫ f Π_l g` for continuous `f`, `g`. -/
theorem proj_symm (l : ℕ) (f g : S2 → ℝ) (hf : Continuous f) (hg : Continuous g) :
    ∫ x, g x * projDeg l f x ∂sigma = ∫ x, f x * projDeg l g x ∂sigma := by
  unfold projDeg
  have e : ∀ (u v : S2 → ℝ), ∫ x, v x * ((2 * (l : ℝ) + 1) * zonalOp (legP l) u x) ∂sigma
      = (2 * (l : ℝ) + 1) * ∫ x, v x * zonalOp (legP l) u x ∂sigma := by
    intro u v; rw [← integral_const_mul]; congr 1; ext x; ring
  rw [e, e, zonal_symm (legP l) (legP_continuous l) f g hf hg]

/-! ## Stage 3: `H_l` is finite-dimensional, `P_l(⟨u,·⟩) ∈ H_l`, and `Π_l f ∈ H_l` -/

/-- Monomials `y₀^i y₁^j y₂^k` on `S²`. -/
noncomputable def mono (i j k : ℕ) : C(S2, ℝ) :=
  ⟨fun y => cc 0 y ^ i * cc 1 y ^ j * cc 2 y ^ k, by fun_prop⟩

def MonoSet (n : ℕ) : Set C(S2, ℝ) := {F | ∃ i j k, i ≤ n ∧ j ≤ n ∧ k ≤ n ∧ F = mono i j k}

theorem monoSet_finite (n : ℕ) : (MonoSet n).Finite := by
  refine (((Set.finite_Iic n).prod ((Set.finite_Iic n).prod (Set.finite_Iic n))).image
    (fun t : ℕ × ℕ × ℕ => mono t.1 t.2.1 t.2.2)).subset ?_
  rintro F ⟨i, j, k, hi, hj, hk, rfl⟩
  exact ⟨(i, j, k), ⟨hi, hj, hk⟩, rfl⟩

/-- The span of the monomials with exponents `≤ n`. -/
noncomputable def monoSpan (n : ℕ) : Submodule ℝ C(S2, ℝ) := Submodule.span ℝ (MonoSet n)

instance monoSpan_fd (n : ℕ) : FiniteDimensional ℝ (monoSpan n) :=
  FiniteDimensional.span_of_finite ℝ (monoSet_finite n)

/-- The coordinate functions. -/
noncomputable def coordF (t : Fin 3) : C(S2, ℝ) := ⟨cc t, continuous_cc t⟩

theorem coord_mono_mem (t : Fin 3) {n i j k : ℕ} (hi : i ≤ n) (hj : j ≤ n) (hk : k ≤ n) :
    coordF t * mono i j k ∈ monoSpan (n + 1) := by
  apply Submodule.subset_span
  fin_cases t
  · refine ⟨i + 1, j, k, by omega, by omega, by omega, ?_⟩
    ext y; simp [coordF, mono, pow_succ]; ring
  · refine ⟨i, j + 1, k, by omega, by omega, by omega, ?_⟩
    ext y; simp [coordF, mono, pow_succ]; ring
  · refine ⟨i, j, k + 1, by omega, by omega, by omega, ?_⟩
    ext y; simp [coordF, mono, pow_succ]; ring

theorem coord_mul_mem (t : Fin 3) {n : ℕ} {F : C(S2, ℝ)} (hF : F ∈ monoSpan n) :
    coordF t * F ∈ monoSpan (n + 1) := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨i, j, k, hi, hj, hk, rfl⟩ := hF
      exact coord_mono_mem t hi hj hk
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add F G _ _ hF hG => rw [mul_add]; exact Submodule.add_mem _ hF hG
  | smul c F _ hF => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hF

/-- `y ↦ Re (c (a·y)^n)` as a continuous function. -/
noncomputable def reC (c : ℂ) (p q : E3) (n : ℕ) : C(S2, ℝ) :=
  ⟨fun y => (c * cdot p q y ^ n).re,
    Complex.continuous_re.comp (continuous_const.mul
      (((continuous_cdot p q).comp continuous_subtype_val).pow n))⟩

theorem reC_mem (p q : E3) : ∀ (n : ℕ) (c : ℂ), reC c p q n ∈ monoSpan n
  | 0, c => by
      have : reC c p q 0 = c.re • mono 0 0 0 := by
        ext y; simp [reC, mono]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, 0, 0, le_rfl, le_rfl, le_rfl, rfl⟩)
  | n + 1, c => by
      have e : reC c p q (n + 1) = coordF 0 * reC (c * ac p q 0) p q n
          + coordF 1 * reC (c * ac p q 1) p q n + coordF 2 * reC (c * ac p q 2) p q n := by
        ext y
        simp only [reC, coordF, cc, ContinuousMap.add_apply, ContinuousMap.mul_apply,
          ContinuousMap.coe_mk]
        have hz : c * cdot p q (y : E3) ^ (n + 1)
            = c * ac p q 0 * cdot p q (y : E3) ^ n * (((y : E3) 0 : ℝ) : ℂ)
              + c * ac p q 1 * cdot p q (y : E3) ^ n * (((y : E3) 1 : ℝ) : ℂ)
              + c * ac p q 2 * cdot p q (y : E3) ^ n * (((y : E3) 2 : ℝ) : ℂ) := by
          rw [pow_succ, cdot_coord p q (y : E3)]; ring
        rw [hz, Complex.add_re, Complex.add_re, Complex.re_mul_ofReal, Complex.re_mul_ofReal,
          Complex.re_mul_ofReal]
        ring
      rw [e]
      exact Submodule.add_mem _ (Submodule.add_mem _ (coord_mul_mem 0 (reC_mem p q n _))
        (coord_mul_mem 1 (reC_mem p q n _))) (coord_mul_mem 2 (reC_mem p q n _))

theorem genDeg_le (l : ℕ) : GenDeg l ⊆ monoSpan l := by
  rintro F ⟨p, q, _, h | h⟩
  · have : F = reC 1 p q l := by ext y; simp [reC, congrFun h y]
    rw [this]; exact reC_mem p q l 1
  · have : F = reC (-Complex.I) p q l := by
      ext y; simp [reC, congrFun h y]
    rw [this]; exact reC_mem p q l _

theorem harmDeg_le_mono (l : ℕ) : harmDeg l ≤ monoSpan l := Submodule.span_le.2 (genDeg_le l)

/-- **`H_l` is finite-dimensional** (inside the span of the monomials of exponents `≤ l`). -/
instance harmDeg_finiteDimensional (l : ℕ) : FiniteDimensional ℝ (harmDeg l) :=
  Submodule.finiteDimensional_of_le (harmDeg_le_mono l)

theorem harmDeg_closed (l : ℕ) : IsClosed (harmDeg l : Set C(S2, ℝ)) :=
  Submodule.closed_of_finiteDimensional _

theorem harm_memDeg (p q : E3) (l : ℕ) (h : Isotropic p q) :
    CTG.FunkHecke.Complete.harm p q l ∈ harmDeg l :=
  Submodule.subset_span ⟨p, q, h, Or.inl rfl⟩

/-- **`P_l(⟨u,·⟩)` lies in the finite span `H_l`** (circle average of rotated harmonics, as in
`Complete.legendre_mem`, now with the closed set `H_l`). -/
theorem legendre_mem_deg (u : E3) (hu : ‖u‖ = 1) (l : ℕ) :
    ∃ F ∈ harmDeg l, ∀ y : S2, F y = legP l ⟪u, (y : E3)⟫ := by
  set e0 : E3 := EuclideanSpace.single 0 1 with he0def
  set e1 : E3 := EuclideanSpace.single 1 1 with he1def
  have he0 : ‖e0‖ = 1 := by simp [e0]
  set R := (ℝ ∙ (u - e0))ᗮ.reflection
  have hR : R u = e0 := Submodule.reflection_sub (hu.trans he0.symm)
  have hcoord : ∀ v : E3, (R v) 0 = ⟪u, v⟫ := by
    intro v
    have := EuclideanSpace.inner_single_left (0 : Fin 3) (1 : ℝ) (R v)
    rw [← he0def, ← hR] at this
    simp only [map_one, one_mul] at this
    rw [← this]; exact R.inner_map_map _ _
  have hac : ac e0 e1 0 = 1 := by simp [ac, e0, e1]
  have hcR : ∀ i : Fin 3, Continuous (fun z : ℝ × S2 => (R (z.2 : E3)) i) := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
      (R.continuous.comp (continuous_subtype_val.comp continuous_snd))
  let g : ℝ × S2 → ℝ := fun z => (cdot e0 e1 (rotAx z.1 (R (z.2 : E3))) ^ l).re
  have hg : Continuous g := by
    have e : g = fun z => (cw (ac e0 e1 0 * (R (z.2 : E3)) 0)
        (ac e0 e1 1 * (R (z.2 : E3)) 1 + ac e0 e1 2 * (R (z.2 : E3)) 2)
        (ac e0 e1 2 * (R (z.2 : E3)) 1 - ac e0 e1 1 * (R (z.2 : E3)) 2) z.1 ^ l).re := by
      funext z; simp only [g, cdot_rot]
    rw [e]; unfold cw
    have h0 := hcR 0; have h1 := hcR 1; have h2 := hcR 2
    fun_prop
  let G : C(ℝ × S2, ℝ) := ⟨g, hg⟩
  let F : ℝ → C(S2, ℝ) := fun φ => G.curry φ
  have hFc : Continuous F := G.curry.continuous
  have hFmem : ∀ φ, F φ ∈ harmDeg l := by
    intro φ
    set B : E3 ≃ₗᵢ[ℝ] E3 := R.trans (rotAx φ)
    have hB : F φ = CTG.FunkHecke.Complete.harm (B.symm e0) (B.symm e1) l := by
      ext y
      show (cdot e0 e1 (rotAx φ (R (y : E3))) ^ l).re = (cdot (B.symm e0) (B.symm e1) y ^ l).re
      have := cdot_isom B (B.symm e0) (B.symm e1) y
      simp only [LinearIsometryEquiv.apply_symm_apply] at this
      rw [← this]; rfl
    rw [hB]
    exact harm_memDeg _ _ _ (isotropic_isom _ _ _ CTG.FunkHecke.Complete.isotropic_e01)
  set c : ℝ := (2 * π)⁻¹ with hcdef
  have hc0 : 0 < c := by positivity
  let μ : Measure ℝ := ENNReal.ofReal c • volume.restrict (Ioc (0:ℝ) (2 * π))
  have hμ : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc, smul_eq_mul]
    rw [← ENNReal.ofReal_mul hc0.le]
    rw [hcdef, sub_zero, inv_mul_cancel₀ (by positivity)]; simp
  have hFi : Integrable F μ :=
    ((hFc.integrableOn_Ioc (a := 0) (b := 2 * π))).smul_measure ENNReal.ofReal_ne_top
  have hIm : (∫ φ, F φ ∂μ) ∈ harmDeg l :=
    Convex.integral_mem (Submodule.convex _) (harmDeg_closed l)
      (Filter.Eventually.of_forall hFmem) hFi
  refine ⟨∫ φ, F φ ∂μ, hIm, fun y => ?_⟩
  have hev : (∫ φ, F φ ∂μ) y = ∫ φ, F φ y ∂μ :=
    ((ContinuousMap.evalCLM ℝ y).integral_comp_comm hFi).symm
  rw [hev]
  set y' : S2 := rotS R y
  have hy' : (y' : E3) = R y := rfl
  have hint : IntegrableOn (fun φ => cdot e0 e1 (rotAx φ (R (y : E3))) ^ l) (Ioc (0:ℝ) (2 * π)) := by
    apply Continuous.integrableOn_Ioc
    have e : (fun φ => cdot e0 e1 (rotAx φ (R (y : E3))) ^ l) = fun φ => cw (ac e0 e1 0 * (R (y : E3)) 0)
        (ac e0 e1 1 * (R (y : E3)) 1 + ac e0 e1 2 * (R (y : E3)) 2)
        (ac e0 e1 2 * (R (y : E3)) 1 - ac e0 e1 1 * (R (y : E3)) 2) φ ^ l := by
      funext φ; rw [cdot_rot]
    rw [e]; exact (cw_continuous _ _ _).pow l
  have hpa := pole_avg e0 e1 CTG.FunkHecke.Complete.isotropic_e01 y' l
  rw [hy', hac, one_pow, mul_one, intervalIntegral.integral_of_le (by positivity)] at hpa
  have h1 : ∫ φ, F φ y ∂μ = c * ∫ φ in Ioc (0:ℝ) (2 * π), F φ y := by
    simp only [μ]
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc0.le, smul_eq_mul]
  have h2 : ∫ φ in Ioc (0:ℝ) (2 * π), F φ y
      = (∫ φ in Ioc (0:ℝ) (2 * π), cdot e0 e1 (rotAx φ (R (y : E3))) ^ l).re := by
    exact integral_re hint
  rw [h1, h2, hpa, hcoord]
  have : ((2 * π : ℂ) * (legP l ⟪u, (y : E3)⟫ : ℂ)).re = 2 * π * legP l ⟪u, (y : E3)⟫ := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [this, hcdef]; field_simp

/-- **Stage 3: `Π_l f` lies in the finite span `H_l`** for every continuous `f`: there is `F ∈ H_l` (a finite
real linear combination of `Re (a·y)^l`, `Im (a·y)^l`, `a` isotropic) with `F = Π_l f` pointwise. -/
theorem proj_mem (l : ℕ) (f : C(S2, ℝ)) : ∃ F ∈ harmDeg l, ∀ x, F x = projDeg l f x := by
  have hGc : Continuous (fun z : S2 × S2 => f z.1 * legP l ⟪(z.1 : E3), (z.2 : E3)⟫) :=
    (f.continuous.comp continuous_fst).mul ((legP_continuous l).comp
      ((continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)))
  let Gc : C(S2 × S2, ℝ) := ⟨_, hGc⟩
  let K : S2 → C(S2, ℝ) := fun y => Gc.curry y
  have hKc : Continuous K := Gc.curry.continuous
  have hKmem : ∀ y, K y ∈ harmDeg l := by
    intro y
    obtain ⟨L, hL, hLe⟩ := legendre_mem_deg (y : E3) (mem_sphere_zero_iff_norm.1 y.2) l
    have : K y = f y • L := by
      ext x; simp only [K, ContinuousMap.curry_apply, ContinuousMap.coe_smul, Pi.smul_apply,
        smul_eq_mul, hLe]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hL
  have hKi : Integrable K sigma := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hKc.continuousOn
    exact Integrable.of_bound hKc.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => hC y (mem_univ y))
  have hI : (∫ y, K y ∂sigma) ∈ harmDeg l :=
    Convex.integral_mem (Submodule.convex _) (harmDeg_closed l)
      (Filter.Eventually.of_forall hKmem) hKi
  refine ⟨(2 * (l : ℝ) + 1) • ∫ y, K y ∂sigma, Submodule.smul_mem _ _ hI, fun x => ?_⟩
  have hev : (∫ y, K y ∂sigma) x = ∫ y, K y x ∂sigma :=
    ((ContinuousMap.evalCLM ℝ x).integral_comp_comm hKi).symm
  rw [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, hev]
  unfold projDeg zonalOp
  congr 1; congr 1; ext y
  show f y * legP l ⟪(y : E3), (x : E3)⟫ = legP l ⟪(x : E3), (y : E3)⟫ * f y
  rw [real_inner_comm]; ring


/-- Consequences: `Π_l` maps continuous functions into `H_l`, is idempotent on its range, annihilates
`H_k` (`k ≠ l`), and `f − Π_l f ⊥ H_l`. -/
theorem proj_idem (l : ℕ) (f : C(S2, ℝ)) :
    ∃ F ∈ harmDeg l, (∀ x, F x = projDeg l f x) ∧ ∀ x, projDeg l F x = F x := by
  obtain ⟨F, hF, he⟩ := proj_mem l f
  exact ⟨F, hF, he, proj_self hF⟩

/-- `f − Π_l f` is orthogonal to `H_l`. -/
theorem proj_orth (l : ℕ) (f : C(S2, ℝ)) {G : C(S2, ℝ)} (hG : G ∈ harmDeg l) :
    ∫ x, G x * (f x - projDeg l f x) ∂sigma = 0 := by
  obtain ⟨F, _, he⟩ := proj_mem l f
  have hPf : Continuous (projDeg l f) := by
    have : projDeg l f = F := funext fun x => (he x).symm
    rw [this]; exact F.continuous
  have hs := proj_symm l f G f.continuous G.continuous
  have hG' : ∀ x, projDeg l G x = G x := proj_self hG
  simp only [hG'] at hs
  have hi1 : Integrable (fun x => G x * f x) sigma :=
    integrable_of_cont sigma (G.continuous.mul f.continuous)
  have hi2 : Integrable (fun x => G x * projDeg l f x) sigma :=
    integrable_of_cont sigma (G.continuous.mul hPf)
  have : ∫ x, G x * (f x - projDeg l f x) ∂sigma
      = ∫ x, G x * f x ∂sigma - ∫ x, G x * projDeg l f x ∂sigma := by
    rw [← integral_sub hi1 hi2]; congr 1; ext x; ring
  rw [this, hs]
  have : ∫ x, f x * G x ∂sigma = ∫ x, G x * f x ∂sigma := by congr 1; ext x; ring
  rw [this, sub_self]


end CTG.FunkHecke.Proj
