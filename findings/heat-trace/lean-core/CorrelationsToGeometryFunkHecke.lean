import Mathlib

/-!
# The sphere S²: surface measure, Archimedes' theorem, zonal operators, Funk–Hecke in degrees 0 and 1

Seventeenth Lean file of the project "From Correlations to Geometry"; it imports only Mathlib (tag v4.29.0).
Check with `cd lean && ./check_funk_hecke.sh`.

Content: for `S² ⊂ ℝ³` with the normalised surface measure `sigma` (from Mathlib's `Measure.toSphere`):
polar coordinates for arbitrary integrands, moments of a coordinate, invariance of the surface measure under
linear isometries, Archimedes' theorem (a coordinate is uniformly distributed on `[-1,1]`), the zonal operator
`zonalOp g f x = ∫ g ⟨x,y⟩ f y dσ(y)` and its rotation invariance, and the Funk–Hecke formula in degrees 0 and 1:
constants and linear functions are eigenfunctions, with eigenvalues `½∫ g` and `½∫ g(t) t dt`.  For the kernel
`gk ξ t = exp(-arccos(t)²/(2ξ²))` of the paper the normalised population walk `Pinf` has the eigenvalues
`sphS ξ 0` and `sphS ξ 1`; here `legP`, `sphS` etc. are VERBATIM COPIES of the definitions of
`CTG.Reals2.SphereOneDim` in the seventh file (no file imports both, so Lean does not check the identification).
NOT formalised: the Funk–Hecke formula for degree `l ≥ 2`, spherical harmonics, multiplicities, the limit
`N → ∞` on the sphere.  No `sorry`, no `axiom`, no `native_decide`.
Written by a sub-task of an AI session on 26 November 2026.
-/

/-!
# A126: Funk–Hecke on `S²`, degrees 0 and 1 (Mathlib only)

* `sigma0` = Mathlib's `Measure.toSphere` of Lebesgue measure on `ℝ³`, `sigma = sigma0 / (4π)`.
* `polar`, `polar_mul`: polar coordinates on `ℝ³` for arbitrary integrands.
* `mom_even`, `mom_odd`, `sigma0_real_univ`: all moments of the first coordinate
  (`∫ y₀^n dσ₀ = 4π/(n+1)` for even `n`, `0` for odd `n`), via Gaussian integrals and `Γ`.
* `nu1_eq_nu2` / `archimedes`: the first coordinate is uniform on `[-1,1]` under `σ`
  (moments + Weierstrass + uniqueness of finite Borel measures).
* `sigma0_map_rotS`, `integral_rotS`: invariance under every linear isometry of `ℝ³`.
* `zonalOp`, `zonalOp_rotS`: the zonal operator commutes with linear isometries.
* `slice`, `slice_linear`, `zonalOp_const`, `zonalOp_linear`: Funk–Hecke for degree 0 and 1.
* `Pinf_const`, `Pinf_linear`: for the angular Gaussian kernel the normalised population walk
  has eigenvalues `sphS ξ 0` and `sphS ξ 1` (copies of the project's definitions, see below).

NOT in this file: Funk–Hecke for degree `l ≥ 2`; spherical harmonics; the limit `N → ∞`.
No hypotheses beyond measurability/boundedness of the kernel `g`.
-/

open MeasureTheory Set Metric Real
open scoped RealInnerProductSpace Pointwise

namespace CTG.FunkHecke

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 := Metric.sphere (0 : E3) 1

/-- Unnormalised surface measure on `S²` (Mathlib's `toSphere` of Lebesgue measure). -/
noncomputable def sigma0 : Measure S2 := (volume : Measure E3).toSphere

instance : IsFiniteMeasure sigma0 := by unfold sigma0; infer_instance

theorem finrank_E3 : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin

/-- Polar coordinates on `ℝ³`, for an arbitrary function. -/
theorem polar (f : E3 → ℝ) :
    ∫ x, f x = ∫ p : S2 × Ioi (0:ℝ), f (p.2.1 • (p.1 : E3))
      ∂(sigma0.prod (Measure.volumeIoiPow 2)) := by
  calc ∫ x, f x = ∫ x : ({(0:E3)}ᶜ : Set E3), f x.1 ∂((volume : Measure E3).comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = _ := by
      have h : MeasurePreserving (homeomorphUnitSphereProd E3)
          ((volume : Measure E3).comap (↑)) (sigma0.prod (Measure.volumeIoiPow 2)) := by
        have h0 := (volume : Measure E3).measurePreserving_homeomorphUnitSphereProd
        rw [finrank_E3] at h0; exact h0
      rw [← h.integral_comp (Homeomorph.measurableEmbedding _)]
      congr 1; ext x
      have hx : ‖(x:E3)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
      simp [smul_smul, hx]

/-- Radial integrals against `volumeIoiPow n`. -/
theorem integral_volumeIoiPow (n : ℕ) (ψ : ℝ → ℝ) :
    ∫ r : Ioi (0:ℝ), ψ r.1 ∂(Measure.volumeIoiPow n) = ∫ r in Ioi (0:ℝ), r ^ n * ψ r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi fun a ↦ Real.toNNReal (a ^ n) • ψ a,
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- Polar coordinates for a product of an angular and a radial factor. -/
theorem polar_mul (φ : S2 → ℝ) (ψ : ℝ → ℝ) (f : E3 → ℝ)
    (hf : ∀ (u : S2) (r : ℝ), 0 < r → f (r • (u:E3)) = φ u * ψ r) :
    ∫ x, f x = (∫ u, φ u ∂sigma0) * ∫ r in Ioi (0:ℝ), r ^ 2 * ψ r := by
  rw [polar, ← integral_volumeIoiPow, ← integral_prod_mul]
  congr 1; ext p; exact hf p.1 p.2.1 p.2.2

/-! ## Gaussian moments and the angular moments of the first coordinate -/

/-- Half-line Gaussian moments `∫_0^∞ r^n e^{-r²} dr`. -/
noncomputable def gC (n : ℕ) : ℝ := ∫ r in Ioi (0:ℝ), r ^ n * exp (-r ^ 2)

theorem gC_eq (n : ℕ) : gC n = (1/2) * Real.Gamma (((n:ℝ) + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (n:ℝ)) two_pos
    (by have := n.cast_nonneg (α := ℝ); linarith)
  rw [gC, ← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [Real.rpow_natCast, Real.rpow_two]

theorem gC_pos (n : ℕ) : 0 < gC n := by
  rw [gC_eq]; have := Real.Gamma_pos_of_pos (s := ((n:ℝ) + 1) / 2) (by positivity); positivity

theorem gC_add_two (n : ℕ) : gC (n+2) = ((n:ℝ) + 1) / 2 * gC n := by
  rw [gC_eq, gC_eq]
  have e : ((((n+2 : ℕ)) : ℝ) + 1) / 2 = ((n:ℝ) + 1) / 2 + 1 := by push_cast; ring
  rw [e, Real.Gamma_add_one (by positivity)]; ring

theorem gauss_line_even (n : ℕ) (hn : Even n) : ∫ t : ℝ, t ^ n * exp (-t ^ 2) = 2 * gC n := by
  have h := integral_comp_abs (f := fun t : ℝ => t ^ n * exp (-t ^ 2))
  rw [gC, ← h]; congr 1; ext t; simp [hn.pow_abs, sq_abs]

theorem gauss_line_odd (n : ℕ) (hn : Odd n) : ∫ t : ℝ, t ^ n * exp (-t ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => t ^ n * exp (-t ^ 2)) volume
  simp only [hn.neg_pow, neg_sq, neg_mul, integral_neg] at h
  linarith

/-- The Gaussian integral of `x₀^n e^{-‖x‖²}` over `ℝ³` (Fubini over the coordinates). -/
theorem gauss3 (n : ℕ) :
    ∫ x : E3, (x 0) ^ n * exp (-‖x‖ ^ 2) = (∫ t : ℝ, t ^ n * exp (-t ^ 2)) * π := by
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (g := fun y : Fin 3 → ℝ => ∏ i, (if i = 0 then y i ^ n else 1) * exp (-(y i) ^ 2))
  have h2 := integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (ι := Fin 3)
    (fun i (t : ℝ) => (if i = 0 then t ^ n else 1) * exp (-t ^ 2))
  have hg : ∫ t : ℝ, exp (-t ^ 2) = √π := by
    have := integral_gaussian 1; simpa using this
  calc ∫ x : E3, (x 0) ^ n * exp (-‖x‖ ^ 2)
      = ∫ x : E3, (fun y : Fin 3 → ℝ => ∏ i, (if i = 0 then y i ^ n else 1) * exp (-(y i) ^ 2))
          ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x) := by
        congr 1; ext x
        simp only [Fin.prod_univ_three]
        rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
        simp only [Fin.isValue, if_true, show (1 : Fin 3) ≠ 0 by decide,
          show (2 : Fin 3) ≠ 0 by decide, if_false, one_mul]
        rw [show -(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) = -x 0 ^ 2 + -x 1 ^ 2 + -x 2 ^ 2 by ring,
          exp_add, exp_add]
        simp only [MeasurableEquiv.toLp_symm_apply]
        ring
    _ = _ := by
        rw [h, h2, Fin.prod_univ_three]
        simp only [Fin.isValue, if_true, show (1 : Fin 3) ≠ 0 by decide,
          show (2 : Fin 3) ≠ 0 by decide, if_false, one_mul, hg]
        rw [mul_assoc, Real.mul_self_sqrt Real.pi_pos.le]

/-- Angular moments of the first coordinate on `S²` (unnormalised measure). -/
noncomputable def mom (n : ℕ) : ℝ := ∫ u, ((u : E3) 0) ^ n ∂sigma0

theorem mom_gauss (n : ℕ) :
    (∫ t : ℝ, t ^ n * exp (-t ^ 2)) * π = mom n * gC (n + 2) := by
  rw [← gauss3, polar_mul (fun u => ((u : E3) 0) ^ n) (fun r => r ^ n * exp (-r ^ 2))]
  · rw [mom, gC]; congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => by ring)
  · intro u r hr
    have hu : ‖(u : E3)‖ = 1 := by simp
    simp only [PiLp.smul_apply, smul_eq_mul, norm_smul, hu, Real.norm_eq_abs, abs_of_pos hr,
      mul_one]
    ring

theorem mom_even (n : ℕ) (hn : Even n) : mom n = 4 * π / ((n:ℝ) + 1) := by
  have h := mom_gauss n
  rw [gauss_line_even n hn, gC_add_two] at h
  have hp := gC_pos n
  have key : (mom n * ((n:ℝ) + 1) - 4 * π) * gC n = 0 := by linear_combination (-2) * h
  have h3 : mom n * ((n:ℝ) + 1) = 4 * π := by
    rcases mul_eq_zero.1 key with h' | h'
    · linarith
    · linarith
  rw [eq_div_iff (by positivity)]; exact h3

theorem mom_odd (n : ℕ) (hn : Odd n) : mom n = 0 := by
  have h := mom_gauss n
  rw [gauss_line_odd n hn, zero_mul] at h
  have := gC_pos (n + 2)
  rcases mul_eq_zero.1 h.symm with h' | h'
  · exact h'
  · linarith

/-- Total mass of the unnormalised surface measure: `4π`. -/
theorem sigma0_real_univ : sigma0.real univ = 4 * π := by
  have h := mom_even 0 ⟨0, rfl⟩
  simp only [mom, pow_zero, integral_const, smul_eq_mul, mul_one, Nat.cast_zero, zero_add,
    div_one] at h
  exact h

/-! ## The normalised measure and Archimedes' theorem -/


/-- Normalised surface measure `σ = σ₀ / (4π)` on `S²`. -/
noncomputable def sigma : Measure S2 := (Real.toNNReal (1 / (4 * π))) • sigma0

theorem integral_sigma (f : S2 → ℝ) : ∫ u, f u ∂sigma = (1 / (4 * π)) * ∫ u, f u ∂sigma0 := by
  rw [sigma, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (by positivity)]

instance : IsFiniteMeasure sigma := by unfold sigma; infer_instance

/-- The first coordinate of a point of `S²`. -/
noncomputable def coord0 (u : S2) : ℝ := (u : E3) 0

theorem continuous_coord0 : Continuous coord0 :=
  ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_subtype_val)

theorem coord0_mem (u : S2) : coord0 u ∈ Icc (-1:ℝ) 1 := by
  have h := PiLp.norm_apply_le (u : E3) 0
  have hu : ‖(u : E3)‖ = 1 := by simp
  rw [hu, Real.norm_eq_abs] at h
  exact abs_le.1 h

/-- Law of the first coordinate under `σ`. -/
noncomputable def nu1 : Measure ℝ := sigma.map coord0

/-- Uniform law on `[-1,1]`. -/
noncomputable def nu2 : Measure ℝ := (1/2 : NNReal) • (volume.restrict (Icc (-1:ℝ) 1))

instance : IsFiniteMeasure nu1 := by unfold nu1; infer_instance

instance : IsFiniteMeasure nu2 := by unfold nu2; infer_instance

theorem nu1_ae : ∀ᵐ t ∂nu1, t ∈ Icc (-1:ℝ) 1 :=
  (ae_map_iff continuous_coord0.measurable.aemeasurable measurableSet_Icc).2
    (Filter.Eventually.of_forall coord0_mem)

theorem nu2_ae : ∀ᵐ t ∂nu2, t ∈ Icc (-1:ℝ) 1 :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

theorem integrable_of_Icc (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ∀ᵐ t ∂ν, t ∈ Icc (-1:ℝ) 1)
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable f ν := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).exists_bound_of_continuousOn
    hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (hν.mono fun t ht => hC t ht)

theorem nu1_pow (k : ℕ) : ∫ t, t ^ k ∂nu1 = (1 / (4 * π)) * mom k := by
  rw [nu1, integral_map continuous_coord0.measurable.aemeasurable
    (continuous_pow k).aestronglyMeasurable, integral_sigma]
  rfl

theorem nu2_pow (k : ℕ) :
    ∫ t, t ^ k ∂nu2 = (1/2) * ((1 - (-1:ℝ) ^ (k + 1)) / ((k:ℝ) + 1)) := by
  rw [nu2, integral_smul_nnreal_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), integral_pow, NNReal.smul_def, smul_eq_mul]
  norm_num

theorem moments_eq (k : ℕ) : ∫ t, t ^ k ∂nu1 = ∫ t, t ^ k ∂nu2 := by
  rw [nu1_pow, nu2_pow]
  have hp := Real.pi_pos
  rcases Nat.even_or_odd k with hk | hk
  · rw [mom_even k hk, (Even.add_one hk).neg_one_pow]
    field_simp; ring
  · rw [mom_odd k hk, (Odd.add_one hk).neg_one_pow]
    ring

theorem poly_eq (p : Polynomial ℝ) : ∫ t, p.eval t ∂nu1 = ∫ t, p.eval t ∂nu2 := by
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finset_sum _ (fun i _ => integrable_of_Icc nu1 nu1_ae (by fun_prop)),
    integral_finset_sum _ (fun i _ => integrable_of_Icc nu2 nu2_ae (by fun_prop))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, integral_const_mul, moments_eq]

theorem approx (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ∀ᵐ t ∂ν, t ∈ Icc (-1:ℝ) 1)
    {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {ε : ℝ}
    (h : ∀ x ∈ Icc (-1:ℝ) 1, |f x - g x| ≤ ε) :
    |∫ t, f t ∂ν - ∫ t, g t ∂ν| ≤ ε * ν.real univ := by
  rw [← integral_sub (integrable_of_Icc ν hν hf) (integrable_of_Icc ν hν hg)]
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun t => f t - g t)
    (hν.mono fun t ht => by simpa [Real.norm_eq_abs] using h t ht)
  simpa [Real.norm_eq_abs] using this

theorem nu1_mass : nu1.real univ = 1 := by
  have h := nu1_pow 0
  rw [mom_even 0 ⟨0, rfl⟩] at h
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at h
  rw [h, Nat.cast_zero, zero_add, div_one, one_div, inv_mul_cancel₀ (by positivity)]

theorem nu2_mass : nu2.real univ = 1 := by
  have h := nu2_pow 0
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at h
  rw [h]; norm_num

/-- **Archimedes' hat-box theorem, measure form**: under the normalised surface measure the first
coordinate is uniformly distributed on `[-1,1]`. -/
theorem nu1_eq_nu2 : nu1 = nu2 := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro h
  have hc : Continuous (fun t => h t) := h.continuous
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun t => h t) hc.continuousOn
    (ε / 2) (by linarith)
  have hpc : Continuous (fun t => p.eval t) := p.continuous
  have h1 := approx nu1 nu1_ae hc hpc (ε := ε / 2)
    (fun x hx => by rw [abs_sub_comm]; exact (hp x hx).le)
  have h2 := approx nu2 nu2_ae hc hpc (ε := ε / 2)
    (fun x hx => by rw [abs_sub_comm]; exact (hp x hx).le)
  rw [nu1_mass] at h1
  rw [nu2_mass] at h2
  have hq := poly_eq p
  rw [Real.dist_eq]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Archimedes' hat-box theorem**: `∫_{S²} g(y₀) dσ(y) = ½ ∫_{-1}^{1} g(t) dt` for every
measurable `g` (both sides are `0` if `g` is not integrable, by the measure identity). -/
theorem archimedes (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ u, g (coord0 u) ∂sigma = (1/2) * ∫ t in (-1:ℝ)..1, g t := by
  have e : ∫ u, g (coord0 u) ∂sigma = ∫ t, g t ∂nu1 := by
    rw [nu1, integral_map continuous_coord0.measurable.aemeasurable hg.aestronglyMeasurable]
  rw [e, nu1_eq_nu2, nu2, integral_smul_nnreal_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), NNReal.smul_def, smul_eq_mul]
  norm_num

/-! ## Rotation invariance and the zonal operator -/

/-- Action of a linear isometry of `ℝ³` on `S²`. -/
noncomputable def rotS (A : E3 ≃ₗᵢ[ℝ] E3) : S2 ≃ₜ S2 where
  toFun u := ⟨A u, by rw [mem_sphere_zero_iff_norm, A.norm_map]; exact mem_sphere_zero_iff_norm.1 u.2⟩
  invFun u := ⟨A.symm u, by
    rw [mem_sphere_zero_iff_norm, A.symm.norm_map]; exact mem_sphere_zero_iff_norm.1 u.2⟩
  left_inv u := by ext1; simp
  right_inv u := by ext1; simp
  continuous_toFun := (A.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (A.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem rotS_coe (A : E3 ≃ₗᵢ[ℝ] E3) (u : S2) : ((rotS A u : S2) : E3) = A u := rfl

@[simp] theorem rotS_symm_coe (A : E3 ≃ₗᵢ[ℝ] E3) (u : S2) :
    (((rotS A).symm u : S2) : E3) = A.symm u := rfl

theorem smul_preimage_isom (A : E3 ≃ₗᵢ[ℝ] E3) (T : Set E3) :
    Ioo (0:ℝ) 1 • (A ⁻¹' T) = A ⁻¹' (Ioo (0:ℝ) 1 • T) := by
  ext x
  simp only [Set.mem_smul, Set.mem_preimage]
  constructor
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c, hc, A y, hy, by rw [A.map_smul]⟩
  · rintro ⟨c, hc, t, ht, hx⟩
    refine ⟨c, hc, A.symm t, by simpa using ht, ?_⟩
    rw [← A.symm.map_smul, hx, A.symm_apply_apply]

/-- The surface measure is invariant under every linear isometry of `ℝ³`. -/
theorem sigma0_map_rotS (A : E3 ≃ₗᵢ[ℝ] E3) : sigma0.map (rotS A) = sigma0 := by
  ext s hs
  rw [Measure.map_apply (rotS A).measurable hs, sigma0, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ ((rotS A).measurable hs)]
  congr 1
  have himg : ((↑) '' ((rotS A) ⁻¹' s) : Set E3) = A ⁻¹' ((↑) '' s) := by
    ext x; constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨rotS A u, hu, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨(rotS A).symm v, by simpa using hv, ?_⟩
      rw [rotS_symm_coe, hvx, A.symm_apply_apply]
  rw [himg, smul_preimage_isom]
  exact (A.measurePreserving).measure_preimage_emb A.toHomeomorph.measurableEmbedding _

theorem sigma_map_rotS (A : E3 ≃ₗᵢ[ℝ] E3) : sigma.map (rotS A) = sigma := by
  rw [sigma, Measure.map_smul, sigma0_map_rotS]

/-- Rotation invariance of integrals against `σ` (no measurability needed). -/
theorem integral_rotS (A : E3 ≃ₗᵢ[ℝ] E3) (F : S2 → ℝ) :
    ∫ u, F (rotS A u) ∂sigma = ∫ u, F u ∂sigma :=
  (MeasurePreserving.mk (rotS A).measurable (sigma_map_rotS A)).integral_comp
    (rotS A).measurableEmbedding F

/-- The zonal integral operator `(T_g f)(x) = ∫_{S²} g(⟨x,y⟩) f(y) dσ(y)`. -/
noncomputable def zonalOp (g : ℝ → ℝ) (f : S2 → ℝ) (x : S2) : ℝ :=
  ∫ y, g ⟪(x : E3), (y : E3)⟫ * f y ∂sigma

/-- `T_g` commutes with every linear isometry of `ℝ³`. -/
theorem zonalOp_rotS (A : E3 ≃ₗᵢ[ℝ] E3) (g : ℝ → ℝ) (f : S2 → ℝ) (x : S2) :
    zonalOp g (f ∘ rotS A) x = zonalOp g f (rotS A x) := by
  unfold zonalOp
  calc ∫ y, g ⟪(x : E3), (y : E3)⟫ * (f ∘ rotS A) y ∂sigma
      = ∫ y, g ⟪((rotS A x : S2) : E3), ((rotS A y : S2) : E3)⟫ * f (rotS A y) ∂sigma := by
        congr 1; ext y; simp [LinearIsometryEquiv.inner_map_map]
    _ = ∫ y, g ⟪((rotS A x : S2) : E3), (y : E3)⟫ * f y ∂sigma :=
        integral_rotS A (fun y => g ⟪((rotS A x : S2) : E3), (y : E3)⟫ * f y)

/-! ## Funk–Hecke in degrees 0 and 1 -/

/-- Slice formula: for every unit `x`, `∫ g(⟨x,y⟩) dσ(y) = ½ ∫_{-1}^1 g`. -/
theorem slice (g : ℝ → ℝ) (hg : Measurable g) (x : S2) :
    ∫ y, g ⟪(x : E3), (y : E3)⟫ ∂sigma = (1/2) * ∫ t in (-1:ℝ)..1, g t := by
  set e0 : E3 := EuclideanSpace.single 0 1 with he0def
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hx : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  set R := (ℝ ∙ ((x : E3) - e0))ᗮ.reflection
  have hR : R (x : E3) = e0 := Submodule.reflection_sub (hx.trans he0.symm)
  calc ∫ y, g ⟪(x : E3), (y : E3)⟫ ∂sigma = ∫ y, g (coord0 (rotS R y)) ∂sigma := by
        congr 1; ext y
        simp only [coord0, rotS_coe]
        congr 1
        rw [← R.inner_map_map (x : E3) (y : E3), hR, he0def]
        exact (EuclideanSpace.inner_single_left (0 : Fin 3) (1 : ℝ) (R (y : E3))).trans (by simp)
    _ = ∫ y, g (coord0 y) ∂sigma := integral_rotS R (fun y => g (coord0 y))
    _ = _ := archimedes g hg

/-- Degree one: `∫ g(⟨x,y⟩)⟨y,z⟩ dσ(y) = (½∫_{-1}^1 g(t) t dt) ⟨x,z⟩`, for bounded measurable `g`. -/
theorem slice_linear (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ t, |g t| ≤ C)
    (x : S2) (z : E3) :
    ∫ y, g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), z⟫ ∂sigma
      = ((1/2) * ∫ t in (-1:ℝ)..1, g t * t) * ⟪(x : E3), z⟫ := by
  set w : E3 := z - ⟪(x : E3), z⟫ • (x : E3) with hwdef
  have hx : ‖(x : E3)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  have hxx : ⟪(x : E3), (x : E3)⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx]; norm_num
  have hxw : ⟪(x : E3), w⟫ = 0 := by
    rw [hwdef, inner_sub_right, real_inner_smul_right, hxx]; ring
  have hdec : ∀ y : E3, ⟪y, z⟫ = ⟪(x : E3), z⟫ * ⟪y, (x : E3)⟫ + ⟪y, w⟫ := by
    intro y; rw [hwdef, inner_sub_right, real_inner_smul_right]; ring
  have hint : ∀ v : E3, Integrable (fun y : S2 => g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), v⟫) sigma := by
    intro v
    refine Integrable.of_bound ?_ (C * ‖v‖) (Filter.Eventually.of_forall fun y => ?_)
    · exact ((hg.comp (by fun_prop : Measurable fun y : S2 => ⟪(x : E3), (y : E3)⟫)).mul
        (by fun_prop : Measurable fun y : S2 => ⟪(y : E3), v⟫)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := hC ⟪(x : E3), (y : E3)⟫
      have h2 : |⟪(y : E3), v⟫| ≤ ‖v‖ := by
        have := abs_real_inner_le_norm (y : E3) v
        rwa [mem_sphere_zero_iff_norm.1 y.2, one_mul] at this
      exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
  have hodd : ∫ y, g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), w⟫ ∂sigma = 0 := by
    set S := (ℝ ∙ w)ᗮ.reflection
    have hSx : S (x : E3) = x :=
      Submodule.reflection_mem_subspace_eq_self
        (Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by rw [real_inner_comm]; exact hxw))
    have hSw : S w = -w := Submodule.reflection_orthogonalComplement_singleton_eq_neg w
    have h' : ∀ y : S2, g ⟪(x : E3), ((rotS S y : S2) : E3)⟫ * ⟪((rotS S y : S2) : E3), w⟫
        = -(g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), w⟫) := by
      intro y
      rw [rotS_coe]
      have e1 : ⟪(x : E3), S y⟫ = ⟪(x : E3), (y : E3)⟫ := by
        calc ⟪(x : E3), S y⟫ = ⟪S (x : E3), S y⟫ := by rw [hSx]
          _ = _ := S.inner_map_map _ _
      have e2 : ⟪S y, w⟫ = -⟪(y : E3), w⟫ := by
        rw [← S.inner_map_map (y : E3) w, hSw, inner_neg_right, neg_neg]
      rw [e1, e2]; ring
    have h := integral_rotS S (fun y => g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), w⟫)
    have h2 : ∫ y, -(g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), w⟫) ∂sigma
        = ∫ y, g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), w⟫ ∂sigma := by
      rw [← h]; congr 1; ext y; exact (h' y).symm
    rw [integral_neg] at h2
    linarith
  have hmain : ∫ y, g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), (x : E3)⟫ ∂sigma
      = (1/2) * ∫ t in (-1:ℝ)..1, g t * t := by
    have := slice (fun t => g t * t) (hg.mul measurable_id) x
    beta_reduce at this
    rw [← this]; congr 1; ext y; rw [real_inner_comm]
  calc ∫ y, g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), z⟫ ∂sigma
      = ∫ y, (⟪(x : E3), z⟫ * (g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), (x : E3)⟫)
          + g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), w⟫) ∂sigma := by
        congr 1; ext y; rw [hdec]; ring
    _ = ⟪(x : E3), z⟫ * (∫ y, g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), (x : E3)⟫ ∂sigma)
          + ∫ y, g ⟪(x : E3), (y : E3)⟫ * ⟪(y : E3), w⟫ ∂sigma := by
        rw [integral_add ((hint (x : E3)).const_mul _) (hint w), integral_const_mul]
    _ = _ := by rw [hmain, hodd]; ring

/-- Eigenvalue `s₀`: constants are eigenfunctions of `T_g`. -/
theorem zonalOp_const (g : ℝ → ℝ) (hg : Measurable g) (c : ℝ) (x : S2) :
    zonalOp g (fun _ => c) x = ((1/2) * ∫ t in (-1:ℝ)..1, g t) * c := by
  unfold zonalOp
  rw [integral_mul_const, slice g hg x]

/-- Eigenvalue `s₁`: every linear function `y ↦ ⟨y,z⟩` (restriction of a harmonic polynomial of
degree one) is an eigenfunction of `T_g`, eigenvalue `½∫_{-1}^1 g(t) t dt`. -/
theorem zonalOp_linear (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ t, |g t| ≤ C)
    (z : E3) (x : S2) :
    zonalOp g (fun y => ⟪(y : E3), z⟫) x
      = ((1/2) * ∫ t in (-1:ℝ)..1, g t * t) * ⟪(x : E3), z⟫ :=
  slice_linear g hg C hC x z

/-! ## Link to the one-dimensional objects of `CTG.Reals2.SphereOneDim`

The project file `CorrelationsToGeometryReal3.lean` cannot be imported here (Mathlib-only file).
The following five definitions are VERBATIM copies of `legP`, `sw`, `sphI`, `sphZ`, `sphE`, `sphS`
from namespace `CTG.Reals2.SphereOneDim`; the identification with the project objects is therefore
definitional (same bodies), but it is not checked by Lean in this file. -/

/-- Copy of `SphereOneDim.legP` (Bonnet recursion). -/
noncomputable def legP : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | n + 2, x => ((2 * (n : ℝ) + 3) * x * legP (n + 1) x - ((n : ℝ) + 1) * legP n x) / ((n : ℝ) + 2)

/-- Copy of `SphereOneDim.sw`: Gaussian weight in the angle times `sin θ`. -/
noncomputable def sw (ξ θ : ℝ) : ℝ := Real.exp (-(θ ^ 2 / (2 * ξ ^ 2))) * Real.sin θ

/-- Copy of `SphereOneDim.sphI`. -/
noncomputable def sphI (ξ : ℝ) (g : ℝ → ℝ) : ℝ := ∫ θ in (0 : ℝ)..Real.pi, g θ * sw ξ θ

/-- Copy of `SphereOneDim.sphZ`. -/
noncomputable def sphZ (ξ : ℝ) : ℝ := sphI ξ (fun _ => 1)

/-- Copy of `SphereOneDim.sphE`. -/
noncomputable def sphE (ξ : ℝ) (g : ℝ → ℝ) : ℝ := sphI ξ g / sphZ ξ

/-- Copy of `SphereOneDim.sphS`: `s_l = E[P_l(cos θ)]`. -/
noncomputable def sphS (ξ : ℝ) (l : ℕ) : ℝ := sphE ξ (fun θ => legP l (Real.cos θ))

theorem sphZ_pos (ξ : ℝ) : 0 < sphZ ξ := by
  unfold sphZ sphI sw
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun θ hθ => ?_) Real.pi_pos
  · exact (continuous_const.mul ((Real.continuous_exp.comp
      (((continuous_id.pow 2).div_const _).neg)).mul Real.continuous_sin)).intervalIntegrable _ _
  · have := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have := Real.exp_pos (-(θ ^ 2 / (2 * ξ ^ 2)))
    simp only [one_mul]; positivity

/-- Substitution `t = cos θ`. -/
theorem cos_subst (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ θ in (0:ℝ)..π, f (Real.cos θ) * Real.sin θ = ∫ t in (-1:ℝ)..1, f t := by
  have h := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π) (f := Real.cos)
    (f' := fun θ => -Real.sin θ) (g := f) (fun x _ => Real.hasDerivAt_cos x)
    Real.continuous_sin.neg.continuousOn hf
  simp only [Function.comp_apply, Real.cos_zero, Real.cos_pi, mul_neg,
    intervalIntegral.integral_neg] at h
  linarith [intervalIntegral.integral_symm (μ := volume) (f := f) (-1:ℝ) 1]

/-- The angular Gaussian kernel as a function of `t = ⟨x,y⟩`: `k(θ) = exp(-θ²/(2ξ²))`,
`θ = arccos t` the geodesic distance on `S²`. -/
noncomputable def gk (ξ t : ℝ) : ℝ := Real.exp (-(Real.arccos t ^ 2 / (2 * ξ ^ 2)))

theorem gk_continuous (ξ : ℝ) : Continuous (gk ξ) :=
  Real.continuous_exp.comp (((Real.continuous_arccos.pow 2).div_const _).neg)

theorem abs_gk_le (ξ t : ℝ) : |gk ξ t| ≤ 1 := by
  unfold gk
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff, neg_nonpos]
  positivity

/-- `∫_{-1}^1 k(arccos t) h(t) dt = sphI ξ (h ∘ cos)` for continuous `h`. -/
theorem zonal_weight (ξ : ℝ) (h : ℝ → ℝ) (hh : Continuous h) :
    ∫ t in (-1:ℝ)..1, gk ξ t * h t = sphI ξ (fun θ => h (Real.cos θ)) := by
  rw [← cos_subst (fun t => gk ξ t * h t) ((gk_continuous ξ).mul hh)]
  unfold sphI sw
  refine intervalIntegral.integral_congr (fun θ hθ => ?_)
  rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
  simp only [gk, Real.arccos_cos hθ.1 hθ.2]
  ring

/-- The normalised population walk `P_∞ f(x) = T_g f(x) / T_g 1(x)` on `S²`. -/
noncomputable def Pinf (g : ℝ → ℝ) (f : S2 → ℝ) (x : S2) : ℝ :=
  zonalOp g f x / zonalOp g (fun _ => 1) x

/-- For the angular Gaussian kernel, constants are eigenfunctions of `P_∞` with eigenvalue
`sphS ξ 0 = 1`. -/
theorem Pinf_const (ξ c : ℝ) (x : S2) : Pinf (gk ξ) (fun _ => c) x = sphS ξ 0 * c := by
  have h0 : ∫ t in (-1:ℝ)..1, gk ξ t = sphZ ξ := by
    have := zonal_weight ξ (fun _ => 1) continuous_const
    simpa only [mul_one] using this
  have hZ := sphZ_pos ξ
  unfold Pinf
  rw [zonalOp_const _ (gk_continuous ξ).measurable, zonalOp_const _ (gk_continuous ξ).measurable,
    h0]
  unfold sphS sphE
  simp only [legP]
  rw [show sphI ξ (fun _ => 1) = sphZ ξ from rfl, div_self hZ.ne']
  field_simp

/-- For the angular Gaussian kernel, every linear function `y ↦ ⟨y,z⟩` is an eigenfunction of
`P_∞` with eigenvalue `sphS ξ 1` (the project's `s_1`). -/
theorem Pinf_linear (ξ : ℝ) (z : E3) (x : S2) :
    Pinf (gk ξ) (fun y => ⟪(y : E3), z⟫) x = sphS ξ 1 * ⟪(x : E3), z⟫ := by
  have h0 : ∫ t in (-1:ℝ)..1, gk ξ t = sphZ ξ := by
    have := zonal_weight ξ (fun _ => 1) continuous_const
    simpa only [mul_one] using this
  have h1 : ∫ t in (-1:ℝ)..1, gk ξ t * t = sphI ξ (fun θ => legP 1 (Real.cos θ)) := by
    have := zonal_weight ξ (fun t => t) continuous_id
    simpa only [legP] using this
  have hZ := sphZ_pos ξ
  unfold Pinf
  rw [zonalOp_linear _ (gk_continuous ξ).measurable 1 (abs_gk_le ξ),
    zonalOp_const _ (gk_continuous ξ).measurable, h0, h1]
  unfold sphS sphE
  field_simp

end CTG.FunkHecke
