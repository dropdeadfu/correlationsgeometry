/-
Sixty-fifth file: completeness of the harmonics on the sphere `S²`, and Theorem `thm:LB` on `S²` for series of
harmonics.  Namespaces `CTG.FunkHecke.Complete`, `CTG.FunkHecke.CompleteLB`; imports the compiled module of the
forty-ninth file; check with `./check_funk_hecke_complete.sh`.
`harmCl_eq_top`, `harmSpan_dense`, `harm_approx`: the functions `y ↦ Re (a·y)^l` (`a` isotropic, `l ≥ 0`) span a dense
subspace of `C(S², ℝ)` in the supremum norm, without hypothesis (Legendre polynomials as circle means of harmonics,
powers of linear forms by the Bonnet recursion, exponentials of linear forms in the Banach algebra, Stone–Weierstrass).
`zonalOp_tsum`, `Lxi_hasSum`: the population operator commutes with uniformly dominated series.
`LB_sphere_series`: for `f = Σ_l f_l` with `f_l` in the span of the harmonics of degree `l`, `|f_l| ≤ B_l`, `Σ B_l < ∞`,
`Σ cLB(ξ,l) B_l < ∞`, and the HYPOTHESIS that the extrinsic Laplacian `sphLapS` may be applied termwise to the series:
`|L_ξ f(x) + Δ_{S²} f(x)| ≤ Σ_l cLB(ξ,l) |f_l(x)|`, `0 < ξ ≤ 1/20`.
NOT formalised: the termwise Laplacian; that a smooth `f` has such a representation with fast decaying `B_l`
(orthogonality of the degrees, projection onto a degree, self-adjointness of the Laplacian on `S²`, decay from
smoothness); density in `L²` as a statement; the Laplacian is still defined extrinsically.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSphereLinComb

/-!
# A178: the harmonics `Re (a·y)^l` (`a` isotropic) are dense in `C(S², ℝ)`

Stage 1 of the completeness question.  Route (no harmonic decomposition, no polarisation):
1. `legendre_mem`: for a unit vector `u` and every `l`, `y ↦ P_l(⟨u,y⟩)` lies in the closed span `harmCl`
   (average of rotated harmonics over a circle, `pole_avg`, as a Bochner integral in `C(S², ℝ)`).
2. `pow_mem_legSpan`, `lin_pow_mem`: `y ↦ ⟨b,y⟩^n ∈ harmCl` for every `b ∈ ℝ³`.
3. `expL_mem`: `y ↦ exp ⟨b,y⟩ ∈ harmCl` (exponential series in the Banach algebra `C(S², ℝ)`).
4. Stone–Weierstraß for the subalgebra spanned by these exponentials: `harmCl_eq_top`, `harmSpan_dense`,
   `harm_approx`.
No `sorry`, no `axiom`, no `native_decide`.
-/

open MeasureTheory Set Metric Real
open scoped RealInnerProductSpace

namespace CTG.FunkHecke.Complete

open CTG.FunkHecke

theorem continuous_harmFun (p q : E3) (l : ℕ) :
    Continuous (fun y : S2 => (cdot p q y ^ l).re) :=
  Complex.continuous_re.comp (((continuous_cdot p q).comp continuous_subtype_val).pow l)

/-- The harmonic `y ↦ Re (a·y)^l`, `a = p + i q`, as a continuous function on `S²`. -/
noncomputable def harm (p q : E3) (l : ℕ) : C(S2, ℝ) :=
  ⟨fun y => (cdot p q y ^ l).re, continuous_harmFun p q l⟩

@[simp] theorem harm_apply (p q : E3) (l : ℕ) (y : S2) : harm p q l y = (cdot p q y ^ l).re := rfl

/-- The generating set: all `Re (a·y)^l` with `a` isotropic, `l ≥ 0`. -/
def harmSet : Set C(S2, ℝ) := {f | ∃ p q : E3, ∃ l : ℕ, Isotropic p q ∧ f = harm p q l}

/-- Their real linear span. -/
noncomputable def harmSpan : Submodule ℝ C(S2, ℝ) := Submodule.span ℝ harmSet

/-- Its closure in the supremum norm. -/
noncomputable def harmCl : Submodule ℝ C(S2, ℝ) := harmSpan.topologicalClosure

theorem harmCl_closed : IsClosed (harmCl : Set C(S2, ℝ)) :=
  Submodule.isClosed_topologicalClosure _

theorem harm_mem (p q : E3) (l : ℕ) (h : Isotropic p q) : harm p q l ∈ harmCl :=
  harmSpan.le_topologicalClosure (Submodule.subset_span ⟨p, q, l, h, rfl⟩)

theorem isotropic_e01 :
    Isotropic (EuclideanSpace.single 0 1 : E3) (EuclideanSpace.single 1 1) := by
  refine ⟨?_, ?_⟩ <;> simp [inner3]

/-! ### Step 1: Legendre polynomials of `⟨u,y⟩` from circle averages of harmonics -/

theorem legendre_mem (u : E3) (hu : ‖u‖ = 1) (l : ℕ) :
    ∃ F ∈ harmCl, ∀ y : S2, F y = legP l ⟪u, (y : E3)⟫ := by
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
  -- the jointly continuous integrand
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
  -- each slice is a generator
  have hFmem : ∀ φ, F φ ∈ harmCl := by
    intro φ
    set B : E3 ≃ₗᵢ[ℝ] E3 := R.trans (rotAx φ)
    have hB : F φ = harm (B.symm e0) (B.symm e1) l := by
      ext y
      show (cdot e0 e1 (rotAx φ (R (y : E3))) ^ l).re = (cdot (B.symm e0) (B.symm e1) y ^ l).re
      have := cdot_isom B (B.symm e0) (B.symm e1) y
      simp only [LinearIsometryEquiv.apply_symm_apply] at this
      rw [← this]; rfl
    rw [hB]; exact harm_mem _ _ _ (isotropic_isom _ _ _ isotropic_e01)
  -- the probability measure on the circle
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
  have hIm : (∫ φ, F φ ∂μ) ∈ harmCl :=
    Convex.integral_mem (Submodule.convex _) harmCl_closed (Filter.Eventually.of_forall hFmem) hFi
  refine ⟨∫ φ, F φ ∂μ, hIm, fun y => ?_⟩
  have hev : (∫ φ, F φ ∂μ) y = ∫ φ, F φ y ∂μ :=
    ((ContinuousMap.evalCLM ℝ y).integral_comp_comm hFi).symm
  rw [hev]
  -- evaluate the scalar integral
  set y' : S2 := rotS R y
  have hy' : (y' : E3) = R y := rfl
  have hint : IntegrableOn (fun φ => cdot e0 e1 (rotAx φ (R (y : E3))) ^ l) (Ioc (0:ℝ) (2 * π)) := by
    apply Continuous.integrableOn_Ioc
    have e : (fun φ => cdot e0 e1 (rotAx φ (R (y : E3))) ^ l) = fun φ => cw (ac e0 e1 0 * (R (y : E3)) 0)
        (ac e0 e1 1 * (R (y : E3)) 1 + ac e0 e1 2 * (R (y : E3)) 2)
        (ac e0 e1 2 * (R (y : E3)) 1 - ac e0 e1 1 * (R (y : E3)) 2) φ ^ l := by
      funext φ; rw [cdot_rot]
    rw [e]; exact (cw_continuous _ _ _).pow l
  have hpa := pole_avg e0 e1 isotropic_e01 y' l
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

/-! ### Step 2: powers of linear forms -/

/-- The span of the Legendre polynomials (as functions `ℝ → ℝ`). -/
noncomputable def legSpan : Submodule ℝ (ℝ → ℝ) := Submodule.span ℝ (Set.range legP)

theorem mul_id_mem {f : ℝ → ℝ} (hf : f ∈ legSpan) : (fun t => t * f t) ∈ legSpan := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      cases k with
      | zero =>
          have e : (fun t => t * legP 0 t) = legP 1 := by
            funext t; simp [legP_zero, legP_one]
          rw [e]; exact Submodule.subset_span ⟨1, rfl⟩
      | succ k =>
          have e : (fun t => t * legP (k + 1) t)
              = (((k:ℝ) + 2) / (2 * (k:ℝ) + 3)) • legP (k + 2)
                + (((k:ℝ) + 1) / (2 * (k:ℝ) + 3)) • legP k := by
            funext t
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, legP_succ_succ]
            field_simp
            ring
          rw [e]
          exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k + 2, rfl⟩))
            (Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  | zero =>
      have e : (fun t : ℝ => t * (0 : ℝ → ℝ) t) = 0 := by funext t; simp
      rw [e]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      have e : (fun t => t * (x + y) t) = (fun t => t * x t) + (fun t => t * y t) := by
        funext t; simp [mul_add]
      rw [e]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      have e : (fun t => t * (a • x) t) = a • (fun t => t * x t) := by
        funext t; simp; ring
      rw [e]; exact Submodule.smul_mem _ _ hx

theorem pow_mem_legSpan (n : ℕ) : (fun t : ℝ => t ^ n) ∈ legSpan := by
  induction n with
  | zero =>
      have e : (fun t : ℝ => t ^ 0) = legP 0 := by funext t; simp [legP_zero]
      rw [e]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
      have e : (fun t : ℝ => t ^ (n + 1)) = fun t => t * (fun t : ℝ => t ^ n) t := by
        funext t; ring
      rw [e]; exact mul_id_mem ih

theorem legSpan_transfer (u : E3) (hu : ‖u‖ = 1) {f : ℝ → ℝ} (hf : f ∈ legSpan) :
    ∃ F ∈ harmCl, ∀ y : S2, F y = f ⟪u, (y : E3)⟫ := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact legendre_mem u hu k
  | zero => exact ⟨0, Submodule.zero_mem _, fun y => by simp⟩
  | add x y _ _ hx hy =>
      obtain ⟨F1, h1, e1⟩ := hx; obtain ⟨F2, h2, e2⟩ := hy
      exact ⟨F1 + F2, Submodule.add_mem _ h1 h2, fun z => by simp [e1, e2]⟩
  | smul a x _ hx =>
      obtain ⟨F1, h1, e1⟩ := hx
      exact ⟨a • F1, Submodule.smul_mem _ _ h1, fun z => by simp [e1]⟩

theorem lin_pow_mem (b : E3) (n : ℕ) : ∃ F ∈ harmCl, ∀ y : S2, F y = ⟪b, (y : E3)⟫ ^ n := by
  obtain ⟨r, u, hu, hb⟩ : ∃ r : ℝ, ∃ u : E3, ‖u‖ = 1 ∧ b = r • u := by
    by_cases h0 : b = 0
    · exact ⟨0, EuclideanSpace.single 0 1, by simp, by simp [h0]⟩
    · refine ⟨‖b‖, ‖b‖⁻¹ • b, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
  obtain ⟨F, hF, eF⟩ := legSpan_transfer u hu (pow_mem_legSpan n)
  refine ⟨r ^ n • F, Submodule.smul_mem _ _ hF, fun y => ?_⟩
  simp only [ContinuousMap.smul_apply, eF, smul_eq_mul, hb, inner_smul_left]
  simp [mul_pow]

/-! ### Step 3: exponentials of linear forms -/

/-- The linear form `y ↦ ⟨b,y⟩` on `S²`. -/
noncomputable def lin (b : E3) : C(S2, ℝ) :=
  ⟨fun y => ⟪b, (y : E3)⟫, continuous_const.inner continuous_subtype_val⟩

@[simp] theorem lin_apply (b : E3) (y : S2) : lin b y = ⟪b, (y : E3)⟫ := rfl

theorem lin_pow_mem' (b : E3) (n : ℕ) : lin b ^ n ∈ harmCl := by
  obtain ⟨F, hF, eF⟩ := lin_pow_mem b n
  have : lin b ^ n = F := by ext y; simp [eF]
  rw [this]; exact hF

/-- `y ↦ exp ⟨b,y⟩`, as the exponential in the Banach algebra `C(S², ℝ)`. -/
noncomputable def expL (b : E3) : C(S2, ℝ) := NormedSpace.exp (lin b)

theorem expL_hasSum (b : E3) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • lin b ^ n) (expL b) :=
  NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (lin b)

theorem expL_mem (b : E3) : expL b ∈ harmCl := by
  refine harmCl_closed.mem_of_tendsto (expL_hasSum b).tendsto_sum_nat
    (Filter.Eventually.of_forall fun n => ?_)
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lin_pow_mem' b k)

theorem expL_apply (b : E3) (y : S2) : expL b y = Real.exp ⟪b, (y : E3)⟫ := by
  have h1 := (expL_hasSum b).mapL (ContinuousMap.evalCLM ℝ y)
  have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (⟪b, (y : E3)⟫ : ℝ)
  rw [Real.exp_eq_exp_ℝ]
  refine h1.unique ?_
  convert h2 using 1

theorem lin_add (b c : E3) : lin (b + c) = lin b + lin c := by
  ext y; simp [inner_add_left]

theorem lin_zero : lin 0 = 0 := by ext y; simp

theorem expL_add (b c : E3) : expL (b + c) = expL b * expL c := by
  unfold expL; rw [lin_add]; exact NormedSpace.exp_add

theorem expL_zero : expL 0 = 1 := by
  unfold expL; rw [lin_zero]; exact NormedSpace.exp_zero

/-- The exponentials of linear forms form a submonoid of `C(S², ℝ)`. -/
noncomputable def expMonoid : Submonoid C(S2, ℝ) where
  carrier := Set.range expL
  one_mem' := ⟨0, expL_zero⟩
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b + c, expL_add b c⟩

/-- The subalgebra generated by the exponentials. -/
noncomputable def expAlg : Subalgebra ℝ C(S2, ℝ) := Algebra.adjoin ℝ (expMonoid : Set C(S2, ℝ))

theorem expAlg_le : (expAlg : Set C(S2, ℝ)) ⊆ harmCl := by
  intro f hf
  have hf' : f ∈ Subalgebra.toSubmodule expAlg := hf
  rw [expAlg, Algebra.adjoin_eq_span, Submonoid.closure_eq] at hf'
  refine (Submodule.span_le.2 ?_) hf'
  rintro _ ⟨b, rfl⟩
  exact expL_mem b

theorem expAlg_separates : expAlg.SeparatesPoints := by
  intro x y hxy
  refine ⟨expL x, ⟨expL x, Algebra.subset_adjoin ⟨(x : E3), rfl⟩, rfl⟩, ?_⟩
  simp only [expL_apply]
  intro h
  have h' := Real.exp_injective h
  have hx : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  have hy : ‖(y : E3)‖ = 1 := mem_sphere_zero_iff_norm.1 y.2
  rw [real_inner_self_eq_norm_sq, hx, one_pow] at h'
  exact hxy (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one hx hy).1 h'.symm))

/-! ### Step 4: density -/

/-- **Completeness (density) of the harmonics on `S²`**: the closed real span of the functions
`y ↦ Re (a·y)^l` (`a = p + i q` isotropic, `l ≥ 0`) is all of `C(S², ℝ)` (supremum norm). -/
theorem harmCl_eq_top : harmCl = ⊤ := by
  have hSW := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints expAlg
    expAlg_separates
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ (expAlg.topologicalClosure : Set C(S2, ℝ)) := by rw [hSW]; trivial
  rw [Subalgebra.topologicalClosure_coe] at hf
  exact closure_minimal expAlg_le harmCl_closed hf

theorem harmSpan_dense : Dense (harmSpan : Set C(S2, ℝ)) := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 harmCl_eq_top

/-- **Pointwise form**: every continuous `f` on `S²` is uniformly approximable to any `ε > 0` by a finite
real linear combination of harmonics `Re (a_i·y)^{l_i}` with `a_i = p_i + i q_i` isotropic. -/
theorem harm_approx (f : C(S2, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (p q : Fin n → E3) (l : Fin n → ℕ),
      (∀ i, Isotropic (p i) (q i)) ∧
      ∀ y : S2, |f y - ∑ i, c i * (cdot (p i) (q i) y ^ l i).re| < ε := by
  obtain ⟨g, hgb, hgs⟩ := Metric.dense_iff.1 harmSpan_dense f ε hε
  obtain ⟨n, c, G, hG⟩ := Submodule.mem_span_set'.1 hgs
  have hmem : ∀ i, ∃ p q : E3, ∃ l : ℕ, Isotropic p q ∧ (G i : C(S2, ℝ)) = harm p q l :=
    fun i => (G i).2
  choose p q l hiso hpql using hmem
  refine ⟨n, c, p, q, l, hiso, fun y => ?_⟩
  have hgy : g y = ∑ i, c i * (cdot (p i) (q i) y ^ l i).re := by
    rw [← hG]
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hpql, harm_apply]
  rw [← hgy, ← Real.dist_eq]
  calc dist (f y) (g y) ≤ dist f g := ContinuousMap.dist_apply_le_dist y
    _ < ε := by rw [dist_comm]; exact hgb

end CTG.FunkHecke.Complete

/-! ## Stage 2: `thm:LB` on `S²` for series of same-degree harmonic combinations (conditional) -/

namespace CTG.FunkHecke.CompleteLB

open CTG.FunkHecke (S2 E3 cdot Isotropic gk Pinf zonalOp sigma)
open CTG.FunkHecke.SphereLB (Lxi)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (BddMeas cLB integrable_kernel bddMeas_re)

/-- The degree-`l` part `f_l(y) = Σ_r c_{l,r} Re (a_{l,r}·y)^l`. -/
noncomputable def degPart (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l : ℕ) (y : S2) : ℝ :=
  ∑ r : Fin (n l), c l r * (cdot (P l r) (Q l r) y ^ l).re

theorem degPart_bddMeas (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (l : ℕ) : Measurable (degPart n c P Q l) := by
  unfold degPart
  refine Finset.measurable_sum _ fun r _ => ?_
  exact measurable_const.mul (bddMeas_re (P l r) (Q l r) l).1

theorem sigma_real_univ : sigma.real univ = 1 := by
  have h := CTG.FunkHecke.integral_sigma (fun _ => (1:ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at h
  rw [h, CTG.FunkHecke.sigma0_real_univ]
  field_simp

/-- Exchange of `T_g` with a uniformly dominated series. -/
theorem zonalOp_tsum (ξ : ℝ) (F : ℕ → S2 → ℝ) (hF : ∀ l, Measurable (F l)) (B : ℕ → ℝ)
    (hB : ∀ l y, |F l y| ≤ B l) (hBs : Summable B) (f : S2 → ℝ) (hf : ∀ y, HasSum (fun l => F l y) (f y))
    (x : S2) : HasSum (fun l => zonalOp (gk ξ) (F l) x) (zonalOp (gk ξ) f x) := by
  have hint : ∀ l, Integrable (fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫ * F l y) sigma :=
    fun l => integrable_kernel ξ ⟨hF l, B l, hB l⟩ x
  have hnorm : ∀ l, ∫ y, ‖gk ξ ⟪(x : E3), (y : E3)⟫ * F l y‖ ∂sigma ≤ B l := by
    intro l
    calc ∫ y, ‖gk ξ ⟪(x : E3), (y : E3)⟫ * F l y‖ ∂sigma ≤ ∫ _y, B l ∂sigma := by
          refine integral_mono (hint l).norm (integrable_const _) fun y => ?_
          rw [Real.norm_eq_abs, abs_mul]
          calc |gk ξ ⟪(x : E3), (y : E3)⟫| * |F l y| ≤ 1 * B l :=
                mul_le_mul (CTG.FunkHecke.abs_gk_le ξ _) (hB l y) (abs_nonneg _) zero_le_one
            _ = B l := one_mul _
      _ = B l := by rw [integral_const, sigma_real_univ, one_smul]
  have hsum : Summable fun l => ∫ y, ‖gk ξ ⟪(x : E3), (y : E3)⟫ * F l y‖ ∂sigma :=
    Summable.of_nonneg_of_le (fun l => integral_nonneg fun y => norm_nonneg _) hnorm hBs
  have hpt : ∀ y : S2, ∑' l, gk ξ ⟪(x : E3), (y : E3)⟫ * F l y = gk ξ ⟪(x : E3), (y : E3)⟫ * f y := by
    intro y; rw [tsum_mul_left, (hf y).tsum_eq]
  have key := integral_tsum_of_summable_integral_norm hint hsum
  have hs2 : Summable fun l => zonalOp (gk ξ) (F l) x := by
    refine Summable.of_norm_bounded hsum fun l => ?_
    exact norm_integral_le_integral_norm _
  unfold zonalOp at hs2 ⊢
  convert hs2.hasSum using 1
  rw [key]; exact (integral_congr_ae (Filter.Eventually.of_forall hpt)).symm

/-- Exchange of `L_ξ` with a uniformly dominated series. -/
theorem Lxi_hasSum (ξ : ℝ) (F : ℕ → S2 → ℝ) (hF : ∀ l, Measurable (F l)) (B : ℕ → ℝ)
    (hB : ∀ l y, |F l y| ≤ B l) (hBs : Summable B) (f : S2 → ℝ) (hf : ∀ y, HasSum (fun l => F l y) (f y))
    (x : S2) : HasSum (fun l => Lxi ξ (F l) x) (Lxi ξ f x) := by
  unfold Lxi Pinf
  have h1 := zonalOp_tsum ξ F hF B hB hBs f hf x
  have h2 := (hf x).sub (h1.div_const (zonalOp (gk ξ) (fun _ => 1) x))
  exact h2.mul_left (2 / ξ ^ 2)

/-- **`thm:LB` on `S²` for series** (conditional).  Let `f = Σ_l f_l` pointwise, where `f_l` is a finite
linear combination of degree-`l` harmonics `Re (a·y)^l` (`a` isotropic), with `|f_l| ≤ B_l`, `Σ B_l < ∞`
and `Σ c(ξ,l) B_l < ∞`.  HYPOTHESIS `hΔ`: the extrinsic spherical Laplacian may be applied termwise at `x`
(`Δ_{S²} f(x) = Σ_l Δ_{S²} f_l(x)`; not proven here, it needs uniform convergence of derivatives up to
order 2 of the degree-zero extensions).  Then for `0 < ξ ≤ 1/20`:
`|L_ξ f(x) + Δ_{S²} f(x)| ≤ Σ_l c(ξ,l) |f_l(x)|`. -/
theorem LB_sphere_series {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20)
    (n : ℕ → ℕ) (c : (l : ℕ) → Fin (n l) → ℝ) (P Q : (l : ℕ) → Fin (n l) → E3)
    (hiso : ∀ l r, Isotropic (P l r) (Q l r))
    (B : ℕ → ℝ) (hB : ∀ l y, |degPart n c P Q l y| ≤ B l) (hBs : Summable B)
    (hcB : Summable fun l => cLB ξ l * B l)
    (f : S2 → ℝ) (hf : ∀ y, HasSum (fun l => degPart n c P Q l y) (f y)) (x : S2)
    (hΔ : HasSum (fun l => sphLapS (degPart n c P Q l) x) (sphLapS f x)) :
    |Lxi ξ f x + sphLapS f x| ≤ ∑' l, cLB ξ l * |degPart n c P Q l x| := by
  have hL := Lxi_hasSum ξ (degPart n c P Q) (degPart_bddMeas n c P Q) B hB hBs f hf x
  have hsum := hL.add hΔ
  have hterm : ∀ l, |Lxi ξ (degPart n c P Q l) x + sphLapS (degPart n c P Q l) x|
      ≤ cLB ξ l * |degPart n c P Q l x| := by
    intro l
    exact (CTG.FunkHecke.SphereLinComb.LB_sphere_same_degree hξ hξ1 Finset.univ (c l) (P l) (Q l) l
      (fun r _ => hiso l r) x).2.2
  generalize ha : (fun l => Lxi ξ (degPart n c P Q l) x + sphLapS (degPart n c P Q l) x) = a at hsum
  generalize hb : (fun l => cLB ξ l * |degPart n c P Q l x|) = b
  have hterm' : ∀ l, |a l| ≤ b l := by
    intro l; rw [← ha, ← hb]; exact hterm l
  have hb0 : ∀ l, 0 ≤ b l := by
    intro l; rw [← hb]
    exact mul_nonneg (CTG.FunkHecke.SphereLinComb.cLB_nonneg ξ l) (abs_nonneg _)
  have hdom : Summable b := by
    rw [← hb]
    exact Summable.of_nonneg_of_le
      (fun l => mul_nonneg (CTG.FunkHecke.SphereLinComb.cLB_nonneg ξ l) (abs_nonneg _))
      (fun l => mul_le_mul_of_nonneg_left (hB l x) (CTG.FunkHecke.SphereLinComb.cLB_nonneg ξ l)) hcB
  have hs : Summable fun l => |a l| := Summable.of_nonneg_of_le (fun l => abs_nonneg _) hterm' hdom
  have hs' : Summable fun l => ‖a l‖ := by simpa only [Real.norm_eq_abs] using hs
  rw [← hsum.tsum_eq]
  calc |∑' l, a l| = ‖∑' l, a l‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' l, ‖a l‖ := norm_tsum_le_tsum_norm hs'
    _ = ∑' l, |a l| := by simp only [Real.norm_eq_abs]
    _ ≤ ∑' l, b l := Summable.tsum_le_tsum hterm' hs hdom

end CTG.FunkHecke.CompleteLB
