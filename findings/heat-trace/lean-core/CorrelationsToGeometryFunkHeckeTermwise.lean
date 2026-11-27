/-
Sixty-sixth file: Theorem `thm:LB` on `S²` for series of harmonics WITHOUT the hypothesis of the termwise Laplacian.
Namespace `CTG.FunkHecke.TermwiseLB`; imports the compiled module of the sixty-fifth file; check with
`./check_funk_hecke_termwise.sh`.
`lap_tsum` (Mathlib only): termwise Laplacian of a series of `C²` functions on an open preconnected set with summable
bounds on the first two derivatives.  `degM l = (1 + l²) Σ_r |c_{l,r}| (‖p_{l,r}‖ + ‖q_{l,r}‖)^l` (explicit bound from the
coefficients); `comp_bound` (derivatives of the degree-zero extension up to order 2 near the sphere, with a universal
constant `D` from compactness); `sphLapS_hasSum`: if `Σ_l degM l < ∞` and `f = Σ_l f_l` pointwise, the extrinsic
Laplacian may be applied termwise (the former hypothesis `hΔ`).
`LB_sphere_series'`, `LB_sphere_series_M`: `|L_ξ f(x) + Δ_{S²} f(x)| ≤ Σ_l cLB(ξ,l) |f_l(x)|` for `0 < ξ ≤ 1/20` under
`Σ degM < ∞`, `Σ cLB(ξ,l) degM l < ∞` and pointwise convergence; no hypothesis beyond these.
NOT formalised: that a smooth `f` has such a series with summable `degM` (orthogonality of degrees, projections,
self-adjointness, decay from smoothness); a bound by `‖f_l‖_∞` instead of the coefficients (Bernstein–Markov
inequalities for spherical harmonics); `D` explicit; the Laplacian is still defined extrinsically.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeComplete

open Real Filter Topology Metric Set
open scoped RealInnerProductSpace
open Laplacian

namespace CTG.FunkHecke.TermwiseLB

/-! ### Stage 1: termwise Laplacian of a series -/

section Stage1

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem s_d1 (f : E → ℝ) (y : E) (h : ContDiffAt ℝ 2 f y) : HasFDerivAt f (fderiv ℝ f y) y :=
  (h.differentiableAt (by norm_num)).hasFDerivAt

theorem s_d2 (f : E → ℝ) (y : E) (h : ContDiffAt ℝ 2 f y) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) y) y :=
  ((h.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt

theorem s_tsum {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) (F : ℕ → E → G)
    (F' : ℕ → E → E →L[ℝ] G) (u : ℕ → ℝ) (hu : Summable u)
    (hd1 : ∀ l y, y ∈ U → HasFDerivAt (F l) (F' l y) y)
    (hb1 : ∀ l y, y ∈ U → ‖F' l y‖ ≤ u l)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hs₀ : Summable fun l => F l x₀) (y : E) (hy : y ∈ U) :
    HasFDerivAt (fun z => ∑' l, F l z) (∑' l, F' l y) y :=
  hasFDerivAt_tsum_of_isPreconnected hu hU hUc hd1 hb1 hx₀ hs₀ hy

theorem s_second {U : Set E} (hU : IsOpen U) (S : E → ℝ) (S1 : E → E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (h1 : ∀ y, y ∈ U → HasFDerivAt S (S1 y) y) {x : E} (hx : x ∈ U)
    (h2 : HasFDerivAt S1 T x) : fderiv ℝ (fderiv ℝ S) x = T := by
  have hev : fderiv ℝ S =ᶠ[nhds x] S1 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (h1 y hy).fderiv
  rw [hev.fderiv_eq]; exact h2.fderiv

theorem sum_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (a : ℕ → G) (u : ℕ → ℝ) (hu : Summable u) (h : ∀ l, ‖a l‖ ≤ u l) : HasSum a (∑' l, a l) :=
  (Summable.of_norm_bounded hu h).hasSum

theorem happ (a : ℕ → E →L[ℝ] E →L[ℝ] ℝ) (T : E →L[ℝ] E →L[ℝ] ℝ) (hT : HasSum a T) (v w : E) :
    HasSum (fun l => a l v w) (T v w) := by
  have h1 : HasSum (fun l => a l v) (T v) :=
    ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))).hasSum hT
  exact ((ContinuousLinearMap.apply ℝ ℝ w : (E →L[ℝ] ℝ) →L[ℝ] ℝ)).hasSum h1

theorem hfin {ι : Type*} [Fintype ι] (v : ι → E) (a : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (hT : HasSum a T) :
    HasSum (fun l => ∑ i, a l (v i) (v i)) (∑ i, T (v i) (v i)) :=
  hasSum_sum fun i _ => happ a T hT (v i) (v i)

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem hlapT {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) (x : E) (G : E → ℝ) :
    Δ G x = ∑ i, fderiv ℝ (fderiv ℝ G) x (v i) (v i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis G v]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]


/-- **Stage 1.** Termwise Laplacian (Mathlib's `Δ`) of a series of `C²` functions on an open
preconnected set `U`, with a summable common bound `u` for the first two derivatives on `U` and
convergence at one point of `U`. -/
theorem lap_tsum {U : Set E} (hU : IsOpen U) (hUc : IsPreconnected U) (F : ℕ → E → ℝ)
    (hF : ∀ l, ContDiffOn ℝ 2 (F l) U) (u : ℕ → ℝ) (hu : Summable u)
    (hb1 : ∀ l y, y ∈ U → ‖fderiv ℝ (F l) y‖ ≤ u l)
    (hb2 : ∀ l y, y ∈ U → ‖fderiv ℝ (fderiv ℝ (F l)) y‖ ≤ u l)
    {x₀ : E} (hx₀ : x₀ ∈ U) (hs₀ : Summable fun l => F l x₀) {x : E} (hx : x ∈ U) :
    HasSum (fun l => Δ (F l) x) (Δ (fun y => ∑' l, F l y) x) := by
  have hCA : ∀ l y, y ∈ U → ContDiffAt ℝ 2 (F l) y := fun l y hy =>
    (hF l).contDiffAt (hU.mem_nhds hy)
  have hS1 := s_tsum hU hUc F (fun l y => fderiv ℝ (F l) y) u hu
    (fun l y hy => s_d1 (F l) y (hCA l y hy)) hb1 hx₀ hs₀
  have hsum1 : Summable fun l => fderiv ℝ (F l) x₀ :=
    Summable.of_norm_bounded hu fun l => hb1 l x₀ hx₀
  have hS2 := s_tsum hU hUc (fun l => fderiv ℝ (F l)) (fun l y => fderiv ℝ (fderiv ℝ (F l)) y) u hu
    (fun l y hy => s_d2 (F l) y (hCA l y hy)) hb2 hx₀ hsum1 x hx
  have hD2 := s_second hU (fun z => ∑' l, F l z) (fun y => ∑' l, fderiv ℝ (F l) y) _ hS1 hx hS2
  have hT : HasSum (fun l => fderiv ℝ (fderiv ℝ (F l)) x) (∑' l, fderiv ℝ (fderiv ℝ (F l)) x) :=
    sum_bound (G := E →L[ℝ] E →L[ℝ] ℝ) _ u hu fun l => hb2 l x hx
  have hfin' := hfin (stdOrthonormalBasis ℝ E) _ _ hT
  rw [← hD2] at hfin'
  rw [hlapT (stdOrthonormalBasis ℝ E) x (fun y => ∑' l, F l y)]
  convert hfin' using 1
  funext l
  exact hlapT (stdOrthonormalBasis ℝ E) x (F l)

end Stage1

/-! ### Stage 2: bounds for the degree-zero extensions of degree-`l` parts -/

open CTG.FunkHecke (S2 E3 cdot Isotropic)
open CTG.FunkHecke.SphereLB (Lform Gext DG Fext Fext_eq fderiv_G hasFDerivAt_DG contDiff_G
  Lform_apply Lxi)
open CTG.FunkHecke.SphereLaplace (ext0 sphLap extS sphLapS sphLapS_restrict)
open CTG.FunkHecke.SphereLinComb (cLB)
open CTG.FunkHecke.CompleteLB (degPart)

/-- The normalisation `y ↦ y/‖y‖`. -/
noncomputable def Nrm (y : E3) : E3 := ‖y‖⁻¹ • y

theorem contDiffAt_Nrm {y : E3} (hy : y ≠ 0) : ContDiffAt ℝ 2 Nrm y :=
  ((contDiffAt_norm ℝ hy).inv (norm_ne_zero_iff.mpr hy)).smul contDiffAt_id

theorem norm_Nrm {y : E3} (hy : y ≠ 0) : ‖Nrm y‖ = 1 := by
  unfold Nrm
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]

/-- Universal bound for the first two derivatives of `y ↦ y/‖y‖` on the shell `1/2 ≤ ‖y‖ ≤ 3/2`
(by compactness; the constant is not computed). -/
theorem Nrm_bound : ∃ D : ℝ, 1 ≤ D ∧ ∀ y : E3, 1 / 2 ≤ ‖y‖ → ‖y‖ ≤ 3 / 2 →
    ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i Nrm y‖ ≤ D ^ i := by
  set s : Set E3 := {y | y ≠ 0} with hs_def
  have hs : IsOpen s := isOpen_ne
  have hN : ContDiffOn ℝ 2 Nrm s := fun y hy => (contDiffAt_Nrm hy).contDiffWithinAt
  have hcont : ∀ i : ℕ, i ≤ 2 → ContinuousOn (iteratedFDeriv ℝ i Nrm) s := by
    intro i hi
    exact (hN.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast hi)
      hs.uniqueDiffOn).congr fun y hy => (iteratedFDerivWithin_of_isOpen i hs hy).symm
  set K : Set E3 := {y | 1 / 2 ≤ ‖y‖} ∩ closedBall 0 (3 / 2) with hK_def
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : E3) (3 / 2)).inter_left (isClosed_le continuous_const continuous_norm)
  have hKs : K ⊆ s := by
    intro y hy
    rw [hs_def, mem_setOf_eq]
    intro h0
    have h1 : (1:ℝ) / 2 ≤ ‖y‖ := hy.1
    rw [h0, norm_zero] at h1
    norm_num at h1
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn ((hcont 1 (by norm_num)).mono hKs)
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn ((hcont 2 le_rfl).mono hKs)
  refine ⟨1 + |B1| + |B2|, by linarith [abs_nonneg B1, abs_nonneg B2], ?_⟩
  intro y hy1 hy2 i hi1 hi2
  have hyK : y ∈ K := ⟨hy1, by simpa using hy2⟩
  have hD1 : (1:ℝ) ≤ 1 + |B1| + |B2| := by linarith [abs_nonneg B1, abs_nonneg B2]
  interval_cases i
  · rw [pow_one]; linarith [hB1 y hyK, le_abs_self B1, abs_nonneg B2]
  · have h := hB2 y hyK
    have : 1 + |B1| + |B2| ≤ (1 + |B1| + |B2|) ^ 2 := by nlinarith
    linarith [le_abs_self B2, abs_nonneg B1]

theorem Lform_le (p q v : E3) : ‖Lform p q v‖ ≤ (‖p‖ + ‖q‖) * ‖v‖ := by
  rw [Lform_apply]
  unfold cdot
  calc ‖(⟪p, v⟫ : ℂ) + Complex.I * (⟪q, v⟫ : ℂ)‖ ≤ ‖(⟪p, v⟫ : ℂ)‖ + ‖Complex.I * (⟪q, v⟫ : ℂ)‖ :=
        norm_add_le _ _
    _ = |⟪p, v⟫| + |⟪q, v⟫| := by simp [Complex.norm_real]
    _ ≤ ‖p‖ * ‖v‖ + ‖q‖ * ‖v‖ := add_le_add (abs_real_inner_le_norm p v) (abs_real_inner_le_norm q v)
    _ = (‖p‖ + ‖q‖) * ‖v‖ := by ring

theorem Lform_opNorm (p q : E3) : ‖Lform p q‖ ≤ ‖p‖ + ‖q‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (Lform_le p q)

theorem Lform_unit (p q : E3) {z : E3} (hz : ‖z‖ = 1) : ‖Lform p q z‖ ≤ ‖p‖ + ‖q‖ := by
  simpa [hz] using Lform_le p q z

theorem csmul_norm_le (w : ℂ) (L : E3 →L[ℝ] ℂ) : ‖w • L‖ ≤ ‖w‖ * ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => by
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (L.le_opNorm v) (norm_nonneg _)

theorem G_bound0 (p q : E3) (l : ℕ) {z : E3} (hz : ‖z‖ = 1) :
    ‖Gext p q l z‖ ≤ (‖p‖ + ‖q‖) ^ l := by
  unfold Gext; rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (Lform_unit p q hz) l

theorem G_bound1 (p q : E3) (l : ℕ) {z : E3} (hz : ‖z‖ = 1) :
    ‖fderiv ℝ (Gext p q l) z‖ ≤ l * (‖p‖ + ‖q‖) ^ l := by
  set A := ‖p‖ + ‖q‖
  have hA : 0 ≤ A := by positivity
  rw [fderiv_G]; unfold DG
  have h1 : ‖l • Lform p q z ^ (l - 1)‖ ≤ l * A ^ (l - 1) := by
    refine norm_nsmul_le.trans ?_
    rw [norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (Lform_unit p q hz) _)
      (Nat.cast_nonneg _)
  calc ‖(l • Lform p q z ^ (l - 1)) • Lform p q‖ ≤ ‖l • Lform p q z ^ (l - 1)‖ * ‖Lform p q‖ :=
        csmul_norm_le _ _
    _ ≤ (l * A ^ (l - 1)) * A := mul_le_mul h1 (Lform_opNorm p q) (norm_nonneg _) (by positivity)
    _ ≤ l * A ^ l := by
        rcases l with _ | n
        · simp
        · rw [Nat.add_sub_cancel, pow_succ]
          exact le_of_eq (by ring)

theorem smulRight_norm_le (c : E3 →L[ℝ] ℂ) (f : E3 →L[ℝ] ℂ) :
    ‖c.smulRight f‖ ≤ ‖c‖ * ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.smulRight_apply]
  calc ‖c v • f‖ ≤ ‖c v‖ * ‖f‖ := csmul_norm_le _ _
    _ ≤ (‖c‖ * ‖v‖) * ‖f‖ := mul_le_mul_of_nonneg_right (c.le_opNorm v) (norm_nonneg _)
    _ = ‖c‖ * ‖f‖ * ‖v‖ := by ring

theorem G_bound2 (p q : E3) (l : ℕ) {z : E3} (hz : ‖z‖ = 1) :
    ‖fderiv ℝ (fderiv ℝ (Gext p q l)) z‖ ≤ (l : ℝ) ^ 2 * (‖p‖ + ‖q‖) ^ l := by
  set A := ‖p‖ + ‖q‖
  have hA : 0 ≤ A := by positivity
  rw [fderiv_G, (hasFDerivAt_DG p q l z).fderiv]
  have hL := Lform_opNorm p q
  have hc : ‖l • (((l - 1) • Lform p q z ^ (l - 1 - 1)) • Lform p q)‖
      ≤ l * (((l - 1 : ℕ) : ℝ) * A ^ (l - 1 - 1) * A) := by
    refine norm_nsmul_le.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    refine (csmul_norm_le _ _).trans (mul_le_mul ?_ hL (norm_nonneg _) (by positivity))
    refine norm_nsmul_le.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (Lform_unit p q hz) _
  refine (smulRight_norm_le _ _).trans ?_
  calc _ ≤ (l * (((l - 1 : ℕ) : ℝ) * A ^ (l - 1 - 1) * A)) * A :=
        mul_le_mul hc hL (norm_nonneg _) (by positivity)
    _ ≤ (l : ℝ) ^ 2 * A ^ l := by
        match l with
        | 0 => simp
        | 1 => norm_num [hA]
        | n + 2 =>
          rw [show n + 2 - 1 - 1 = n by omega, show n + 2 - 1 = n + 1 by omega]
          push_cast
          have hB : A ^ (n + 2) = A ^ n * A * A := by ring
          rw [hB]
          have hAA : 0 ≤ A ^ n * A * A := by positivity
          nlinarith [mul_nonneg (show (0:ℝ) ≤ (n:ℝ) + 2 by positivity) hAA]

theorem Fext_iter_le (p q : E3) (l i : ℕ) (hi : i ≤ 2) (z : E3) :
    ‖iteratedFDeriv ℝ i (Fext p q l) z‖ ≤ ‖iteratedFDeriv ℝ i (Gext p q l) z‖ := by
  rw [Fext_eq]
  refine (Complex.reCLM.norm_iteratedFDeriv_comp_left (contDiff_G p q l).contDiffAt
    (by exact_mod_cast hi)).trans ?_
  rw [Complex.reCLM_norm, one_mul]

theorem Fext_bound (p q : E3) (l i : ℕ) (hi : i ≤ 2) {z : E3} (hz : ‖z‖ = 1) :
    ‖iteratedFDeriv ℝ i (Fext p q l) z‖ ≤ (1 + (l : ℝ) ^ 2) * (‖p‖ + ‖q‖) ^ l := by
  refine (Fext_iter_le p q l i hi z).trans ?_
  have hA : 0 ≤ (‖p‖ + ‖q‖) ^ l := by positivity
  interval_cases i
  · rw [norm_iteratedFDeriv_zero]
    refine (G_bound0 p q l hz).trans ?_
    nlinarith [sq_nonneg (l : ℝ)]
  · rw [norm_iteratedFDeriv_one]
    refine (G_bound1 p q l hz).trans ?_
    have : (l : ℝ) ≤ 1 + (l : ℝ) ^ 2 := by nlinarith [sq_nonneg ((l:ℝ) - 1)]
    exact mul_le_mul_of_nonneg_right this hA
  · have e2 : ‖iteratedFDeriv ℝ 2 (Gext p q l) z‖ = ‖fderiv ℝ (fderiv ℝ (Gext p q l)) z‖ := by
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (Gext p q l)), norm_iteratedFDeriv_fderiv]
    rw [e2]
    refine (G_bound2 p q l hz).trans ?_
    nlinarith

/-- The degree-`l` part as a function on `ℝ³`. -/
noncomputable def Gl (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l : ℕ) (y : E3) : ℝ :=
  ∑ r : Fin (n l), c l r * Fext (P l r) (Q l r) l y

/-- The explicit bound `degM l = (1 + l²) Σ_r |c_{l,r}| (‖p_{l,r}‖ + ‖q_{l,r}‖)^l`. -/
noncomputable def degM (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l : ℕ) : ℝ :=
  (1 + (l : ℝ) ^ 2) * ∑ r : Fin (n l), |c l r| * (‖P l r‖ + ‖Q l r‖) ^ l

theorem degM_nonneg (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l : ℕ) : 0 ≤ degM n c P Q l := by
  unfold degM
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun r _ => by positivity)

theorem Gl_contDiff (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l : ℕ) : ContDiff ℝ 2 (Gl n c P Q l) := by
  unfold Gl
  exact ContDiff.sum fun r _ =>
    contDiff_const.mul (CTG.FunkHecke.SphereLinComb.contDiff_Fext (P l r) (Q l r) l)

theorem Gl_bound (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l i : ℕ) (hi : i ≤ 2) {z : E3} (hz : ‖z‖ = 1) :
    ‖iteratedFDeriv ℝ i (Gl n c P Q l) z‖ ≤ degM n c P Q l := by
  unfold Gl degM
  have hC : ∀ r ∈ (Finset.univ : Finset (Fin (n l))),
      ContDiffAt ℝ i (fun y => c l r * Fext (P l r) (Q l r) l y) z := fun r _ =>
    ((contDiff_const.mul (CTG.FunkHecke.SphereLinComb.contDiff_Fext (P l r) (Q l r) l)).of_le
      (by exact_mod_cast hi)).contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hC]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  have hF : ContDiffAt ℝ i (Fext (P l r) (Q l r) l) z :=
    ((CTG.FunkHecke.SphereLinComb.contDiff_Fext (P l r) (Q l r) l).of_le
      (by exact_mod_cast hi)).contDiffAt
  have e : iteratedFDeriv ℝ i (fun y => c l r * Fext (P l r) (Q l r) l y) z
      = c l r • iteratedFDeriv ℝ i (Fext (P l r) (Q l r) l) z :=
    iteratedFDeriv_const_smul_apply' (a := c l r) hF
  rw [e, norm_smul, Real.norm_eq_abs]
  calc |c l r| * ‖iteratedFDeriv ℝ i (Fext (P l r) (Q l r) l) z‖
      ≤ |c l r| * ((1 + (l : ℝ) ^ 2) * (‖P l r‖ + ‖Q l r‖) ^ l) :=
        mul_le_mul_of_nonneg_left (Fext_bound _ _ l i hi hz) (abs_nonneg _)
    _ = (1 + (l : ℝ) ^ 2) * (|c l r| * (‖P l r‖ + ‖Q l r‖) ^ l) := by ring

theorem norm_bounds_of_ball {x : S2} {y : E3} (hy : y ∈ ball (x : E3) (1 / 2)) :
    1 / 2 < ‖y‖ ∧ ‖y‖ < 3 / 2 := by
  have hx : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  rw [mem_ball, dist_eq_norm] at hy
  have h1 := norm_sub_norm_le y (x : E3)
  have h2 := norm_sub_norm_le (x : E3) y
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- Derivative bounds for `Gl ∘ Nrm = ext0 (Gl)` on the ball `B(x, 1/2)`, `x ∈ S²`. -/
theorem comp_bound (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    {D : ℝ} (hD1 : 1 ≤ D) (hD : ∀ y : E3, 1 / 2 ≤ ‖y‖ → ‖y‖ ≤ 3 / 2 →
      ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ‖iteratedFDeriv ℝ i Nrm y‖ ≤ D ^ i)
    (l : ℕ) {x : S2} {y : E3} (hy : y ∈ ball (x : E3) (1 / 2)) (i : ℕ) (hi : i ≤ 2) :
    ‖iteratedFDeriv ℝ i (Gl n c P Q l ∘ Nrm) y‖ ≤ 2 * D ^ 2 * degM n c P Q l := by
  obtain ⟨hy1, hy2⟩ := norm_bounds_of_ball hy
  have hy0 : ∀ w ∈ ball (x : E3) (1 / 2), w ≠ 0 := by
    intro w hw h0
    have := (norm_bounds_of_ball hw).1
    rw [h0, norm_zero] at this; norm_num at this
  have hNs : ContDiffOn ℝ 2 Nrm (ball (x : E3) (1 / 2)) := fun w hw =>
    (contDiffAt_Nrm (hy0 w hw)).contDiffWithinAt
  have h := norm_iteratedFDerivWithin_comp_le (g := Gl n c P Q l) (f := Nrm) (n := i)
    (s := ball (x : E3) (1 / 2)) (t := univ) (N := 2)
    (Gl_contDiff n c P Q l).contDiffOn hNs (by exact_mod_cast hi) uniqueDiffOn_univ
    isOpen_ball.uniqueDiffOn (mapsTo_univ _ _) hy (C := degM n c P Q l) (D := D)
    (fun j hj => by
      rw [iteratedFDerivWithin_univ]
      exact Gl_bound n c P Q l j (hj.trans hi) (norm_Nrm (hy0 y hy)))
    (fun j hj1 hj2 => by
      rw [iteratedFDerivWithin_of_isOpen (f := Nrm) j isOpen_ball hy]
      exact hD y hy1.le hy2.le j hj1 (hj2.trans hi))
  rw [iteratedFDerivWithin_of_isOpen (f := Gl n c P Q l ∘ Nrm) i isOpen_ball hy] at h
  refine h.trans ?_
  have hM := degM_nonneg n c P Q l
  have hfac : (i.factorial : ℝ) ≤ 2 := by
    interval_cases i <;> norm_num [Nat.factorial]
  have hpow : D ^ i ≤ D ^ 2 := pow_le_pow_right₀ hD1 hi
  have hD0 : 0 ≤ D ^ i := by positivity
  calc (i.factorial : ℝ) * degM n c P Q l * D ^ i ≤ 2 * degM n c P Q l * D ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hfac hM) hpow hD0 (by positivity)
    _ = 2 * D ^ 2 * degM n c P Q l := by ring

/-- **Stage 2: the hypothesis `hΔ` of `LB_sphere_series` holds** as soon as
`Σ_l degM l < ∞`, `degM l = (1 + l²) Σ_r |c_{l,r}| (‖p_{l,r}‖ + ‖q_{l,r}‖)^l` (no isotropy needed). -/
theorem sphLapS_hasSum (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (hM : Summable (degM n c P Q))
    (f : S2 → ℝ) (hf : ∀ y, HasSum (fun l => degPart n c P Q l y) (f y)) (x : S2) :
    HasSum (fun l => sphLapS (degPart n c P Q l) x) (sphLapS f x) := by
  obtain ⟨D, hD1, hD⟩ := Nrm_bound
  have hx1 : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.mp x.2
  have hx0 : (x : E3) ≠ 0 := by intro h; rw [h, norm_zero] at hx1; exact zero_ne_one hx1
  have hxU : (x : E3) ∈ ball (x : E3) (1 / 2) := mem_ball_self (by norm_num)
  have hy0 : ∀ w ∈ ball (x : E3) (1 / 2), w ≠ 0 := by
    intro w hw h0
    have := (norm_bounds_of_ball hw).1
    rw [h0, norm_zero] at this; norm_num at this
  have hNs : ContDiffOn ℝ 2 Nrm (ball (x : E3) (1 / 2)) := fun w hw =>
    (contDiffAt_Nrm (hy0 w hw)).contDiffWithinAt
  have hNx : Nrm (x : E3) = x := by
    unfold Nrm; rw [hx1, inv_one, one_smul]
  have key := lap_tsum isOpen_ball (convex_ball (x : E3) (1 / 2)).isPreconnected
    (fun l => Gl n c P Q l ∘ Nrm) (fun l => (Gl_contDiff n c P Q l).comp_contDiffOn hNs)
    (fun l => 2 * D ^ 2 * degM n c P Q l) (hM.mul_left _)
    (fun l y hy => by
      rw [← norm_iteratedFDeriv_one]; exact comp_bound n c P Q hD1 hD l hy 1 (by norm_num))
    (fun l y hy => by
      have e2 := comp_bound n c P Q hD1 hD l hy 2 le_rfl
      rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ (Gl n c P Q l ∘ Nrm)),
        norm_iteratedFDeriv_fderiv]
      exact e2)
    hxU (by
      have h := (hf x).summable
      convert h using 2 with l
      simp only [Function.comp_apply, hNx]; rfl)
    hxU
  have hterm : ∀ l, sphLapS (degPart n c P Q l) x = Δ (Gl n c P Q l ∘ Nrm) (x : E3) := by
    intro l
    have e1 : degPart n c P Q l = fun z : S2 => Gl n c P Q l z := rfl
    rw [e1, sphLapS_restrict]; rfl
  have heq : ext0 (extS f) =ᶠ[𝓝 (x : E3)] fun y => ∑' l, (Gl n c P Q l ∘ Nrm) y := by
    filter_upwards [isOpen_ne.mem_nhds hx0] with y hy
    have hm : ‖y‖⁻¹ • y ∈ S2 := by
      rw [mem_sphere_zero_iff_norm]; exact norm_Nrm hy
    simp only [ext0, extS, dif_pos hm, Function.comp_apply]
    exact ((hf ⟨_, hm⟩).tsum_eq).symm
  have hR : sphLapS f x = Δ (fun y => ∑' l, (Gl n c P Q l ∘ Nrm) y) (x : E3) :=
    (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
  rw [hR]
  simp only [hterm]
  exact key

/-! ### Stage 3: `thm:LB` on `S²` for series without the hypothesis `hΔ` -/

/-- **`thm:LB` on `S²` for series of harmonics, without the termwise-Laplacian hypothesis.**
As `CompleteLB.LB_sphere_series`, with `hΔ` replaced by `Σ_l degM l < ∞`. -/
theorem LB_sphere_series' {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20)
    (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (hiso : ∀ l r, Isotropic (P l r) (Q l r))
    (B : ℕ → ℝ) (hB : ∀ l y, |degPart n c P Q l y| ≤ B l) (hBs : Summable B)
    (hcB : Summable fun l => cLB ξ l * B l)
    (hM : Summable (degM n c P Q))
    (f : S2 → ℝ) (hf : ∀ y, HasSum (fun l => degPart n c P Q l y) (f y)) (x : S2) :
    |Lxi ξ f x + sphLapS f x| ≤ ∑' l, cLB ξ l * |degPart n c P Q l x| :=
  CTG.FunkHecke.CompleteLB.LB_sphere_series hξ hξ1 n c P Q hiso B hB hBs hcB f hf x
    (sphLapS_hasSum n c P Q hM f hf x)

theorem degPart_le_degM (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l : ℕ) (y : S2) : |degPart n c P Q l y| ≤ degM n c P Q l := by
  unfold degPart degM
  have hs : 0 ≤ ∑ r : Fin (n l), |c l r| * (‖P l r‖ + ‖Q l r‖) ^ l :=
    Finset.sum_nonneg fun r _ => by positivity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (le_mul_of_one_le_left hs (by nlinarith [sq_nonneg (l : ℝ)]))
  refine Finset.sum_le_sum fun r _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
    (CTG.FunkHecke.SphereLinComb.cdot_pow_norm_le _ _ l y)) (abs_nonneg _)

/-- The same with `B := degM`: hypotheses only on the coefficients. -/
theorem LB_sphere_series_M {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20)
    (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (hiso : ∀ l r, Isotropic (P l r) (Q l r))
    (hM : Summable (degM n c P Q)) (hcM : Summable fun l => cLB ξ l * degM n c P Q l)
    (f : S2 → ℝ) (hf : ∀ y, HasSum (fun l => degPart n c P Q l y) (f y)) (x : S2) :
    |Lxi ξ f x + sphLapS f x| ≤ ∑' l, cLB ξ l * |degPart n c P Q l x| :=
  LB_sphere_series' hξ hξ1 n c P Q hiso (degM n c P Q) (degPart_le_degM n c P Q) hM hcM hM f hf x

end CTG.FunkHecke.TermwiseLB
