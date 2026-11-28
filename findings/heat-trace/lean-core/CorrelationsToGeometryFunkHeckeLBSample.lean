/-
Seventy-first file (A184, written by a subagent of the author-side session, checked by that session; read by nobody else).
Sample version of Theorem LB on `S²` for smooth functions, extrinsic Laplacian, walk WITH self-loop.
Namespace `CTG.FunkHecke.LBSample`; imports compiled modules of the seventieth file (`…FunkHeckeLBSmooth`) and of
`…FunkHeckeSample`. Check with `./check_funk_hecke_lb_sample.sh` from `lean/`.

Main statements: `LB_sample` (fixed ξ ∈ (0,1/20], N ≥ 2: outside probability 4N exp(−(N−1)η²/(2F²)), at all sample
points |L_N f(X_i) + Δf(X_i)| ≤ (2/ξ²)·4(η(1+F) + 2F/(N−1))/sphZ ξ + Cξ²), `LB_sample_ae` (almost surely, eventually
≤ Cξ² + ε), `LB_sample_joint` (ξ_N → 0 with (N−1)ξ_N⁸/log N → ∞: almost surely max_i |L_N f(X_i) + Δf(X_i)| → 0),
`sphZ_ge` (ξ²/(4π) ≤ sphZ ξ). Assumptions: Δ^j f, j < 4, satisfy `SphC2` everywhere; independent samples with law σ.
NOT shown: measurability of the exceptional sets (bounds for the outer measure); identification of `sphLapS` with the
intrinsic Laplace–Beltrami operator; a regime better than ξ⁸ (coarse constants, certainly not sharp); a walk without
self-loop; the value of C. The sample is nested (first N points of one sequence). No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeLBSmooth
import CorrelationsToGeometryFunkHeckeSample

open MeasureTheory ProbabilityTheory Set Metric Real Filter Topology
open scoped RealInnerProductSpace

namespace CTG.FunkHecke.LBSample

open CTG.FunkHecke (S2 E3 sigma gk Pinf sphZ sphZ_pos sphI sw)
open CTG.FunkHecke.Sample (walk walk_one_step bc_lin)
open CTG.FunkHecke.SphereLB (Lxi)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)
open CTG.FunkHecke.LBSmooth (LB_sphere_smooth_sup)

/-! ## Deterministic part -/

/-- The sampled Laplace–Beltrami operator `L_N f(X_i) = (2/ξ²)(f(X_i) − P_N f(X_i))`. -/
noncomputable def LN {Ω : Type*} (ξ : ℝ) (f : S2 → ℝ) (X : ℕ → Ω → S2) (N : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
  2 / ξ ^ 2 * (f (X i ω) - walk ξ f X N ω i)

theorem LN_split {Ω : Type*} (ξ : ℝ) (f : S2 → ℝ) (X : ℕ → Ω → S2) (N : ℕ) (ω : Ω) (i : ℕ) :
    LN ξ f X N ω i + sphLapS f (X i ω)
      = 2 / ξ ^ 2 * (Pinf (gk ξ) f (X i ω) - walk ξ f X N ω i)
        + (Lxi ξ f (X i ω) + sphLapS f (X i ω)) := by
  unfold LN Lxi; ring

theorem LN_abs_le {Ω : Type*} (ξ : ℝ) (f : S2 → ℝ) (X : ℕ → Ω → S2) (N : ℕ) (ω : Ω) (i : ℕ) :
    |LN ξ f X N ω i + sphLapS f (X i ω)|
      ≤ 2 / ξ ^ 2 * |Pinf (gk ξ) f (X i ω) - walk ξ f X N ω i|
        + |Lxi ξ f (X i ω) + sphLapS f (X i ω)| := by
  rw [LN_split]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 / ξ ^ 2)]

/-- Smooth `f` is continuous and bounded by some `F ≥ 1`. -/
theorem smooth_bound {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) :
    Continuous f ∧ ∃ F : ℝ, 1 ≤ F ∧ ∀ y, |f y| ≤ F := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  have hcf := CTG.FunkHecke.Green.sphC2_cont hf0
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hcf.continuousOn
  refine ⟨hcf, max 1 B, le_max_left _ _, fun y => ?_⟩
  have := hB y (mem_univ y)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_right _ _)

/-- Lower bound for the normalising integral: `ξ²/(4π) ≤ sphZ ξ` for `0 < ξ ≤ 1`. -/
theorem sphZ_ge {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) : ξ ^ 2 / (4 * π) ≤ sphZ ξ := by
  have hpi3 := Real.pi_gt_three
  have hcont : Continuous (fun θ => (fun _ : ℝ => (1:ℝ)) θ * sw ξ θ) := by
    unfold sw; fun_prop
  have step1 : ∫ θ in (ξ/2)..ξ, (fun _ : ℝ => (1:ℝ)) θ * sw ξ θ ≤ sphZ ξ := by
    unfold sphZ sphI
    apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      simp only [Pi.zero_apply, one_mul, sw]
      exact mul_nonneg (Real.exp_pos _).le
        (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2)
    · exact hcont.intervalIntegrable _ _
  have step2 : ∫ _θ in (ξ/2)..ξ, (ξ / (2 * π))
      ≤ ∫ θ in (ξ/2)..ξ, (fun _ : ℝ => (1:ℝ)) θ * sw ξ θ := by
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (hcont.intervalIntegrable _ _)
    intro θ hθ
    simp only [one_mul, sw]
    have h1 : 1 / 2 ≤ Real.exp (-(θ ^ 2 / (2 * ξ ^ 2))) := by
      have hx := Real.add_one_le_exp (-(θ ^ 2 / (2 * ξ ^ 2)))
      have : θ ^ 2 / (2 * ξ ^ 2) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith [hθ.1, hθ.2]
      linarith
    have h2 : ξ / π ≤ Real.sin θ := by
      have hs := Real.mul_le_sin (by linarith [hθ.1]) (by linarith [hθ.2] : θ ≤ π / 2)
      have hm : 2 / π * (ξ / 2) ≤ 2 / π * θ :=
        mul_le_mul_of_nonneg_left hθ.1 (by positivity)
      have e : ξ / π = 2 / π * (ξ / 2) := by field_simp
      linarith
    calc ξ / (2 * π) = 1 / 2 * (ξ / π) := by field_simp
      _ ≤ _ := mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
  rw [intervalIntegral.integral_const, smul_eq_mul] at step2
  have e : ξ ^ 2 / (4 * π) = (ξ - ξ / 2) * (ξ / (2 * π)) := by field_simp; ring
  linarith

/-- The walk error term of `walk_one_step` multiplied by `2/ξ²`, for `η = δ ξ⁴`. -/
theorem err_bound {ξ δ F n : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hδ : 0 ≤ δ) (hF : 0 ≤ F)
    (hn : 0 < n) :
    2 / ξ ^ 2 * (4 * (δ * ξ ^ 4 * (1 + F) + 2 * F / n) / sphZ ξ)
      ≤ 32 * π * (δ * (1 + F)) + 64 * π * F / (n * ξ ^ 4) := by
  have hZ := sphZ_ge hξ hξ1
  have hZp := sphZ_pos ξ
  have hA : 0 ≤ δ * ξ ^ 4 * (1 + F) + 2 * F / n := by positivity
  have h1 : 4 * (δ * ξ ^ 4 * (1 + F) + 2 * F / n) / sphZ ξ
      ≤ 4 * (δ * ξ ^ 4 * (1 + F) + 2 * F / n) / (ξ ^ 2 / (4 * π)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hZ
  calc 2 / ξ ^ 2 * (4 * (δ * ξ ^ 4 * (1 + F) + 2 * F / n) / sphZ ξ)
      ≤ 2 / ξ ^ 2 * (4 * (δ * ξ ^ 4 * (1 + F) + 2 * F / n) / (ξ ^ 2 / (4 * π))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by field_simp; ring

/-! ## Stage (1): with probability, fixed ξ -/

section Prob

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Theorem LB on `S²`, sample version at fixed scale.** `C` is the constant of
`LB_sphere_smooth_sup` (independent of `ξ`, `N`, `F`, `η`). -/
theorem LB_sample (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : ℝ, 1 ≤ F → (∀ y, |f y| ≤ F) → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 →
      ∀ N : ℕ, 2 ≤ N → ∀ η : ℝ, 0 < η → η ≤ sphZ ξ / 4 →
      μ.real {ω | ∃ i < N, 2 / ξ ^ 2 * (4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ) + C * ξ ^ 2
          < |LN ξ f X N ω i + sphLapS f (X i ω)|}
        ≤ 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
  obtain ⟨C, hC0, hC⟩ := LB_sphere_smooth_sup hf
  obtain ⟨hcf, -⟩ := smooth_bound hf
  refine ⟨C, hC0, fun F hF1 hfF ξ hξ hξ1 N hN η hη hηb => ?_⟩
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    (walk_one_step X hind hX hlaw ξ f hcf hF1 hfF hN hη hηb)
  rintro ω ⟨i, hi, h⟩
  refine ⟨i, hi, ?_⟩
  by_contra hle
  push_neg at hle
  apply not_le.mpr h
  refine (LN_abs_le ξ f X N ω i).trans (add_le_add (mul_le_mul_of_nonneg_left ?_ (by positivity))
    (hC ξ hξ hξ1 _))
  rw [abs_sub_comm]; exact hle

end Prob

/-! ## Stage (2): almost surely, fixed ξ -/

section AE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem walk_ae_eta (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) {f : S2 → ℝ}
    (hcf : Continuous f) {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F)
    {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ∀ i < N,
      |walk ξ f X N ω i - Pinf (gk ξ) f (X i ω)|
        ≤ 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ := by
  have hF : 0 < F := by linarith
  set c : ℝ := η ^ 2 / (2 * F ^ 2)
  have hc : 0 < c := by positivity
  have h := bc_lin (μ := μ) (fun N => {ω | ∃ i < N,
      4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk ξ f X N ω i - Pinf (gk ξ) f (X i ω)|})
    (C := 4 * Real.exp c) (by positivity) hc (fun N hN => by
      refine (walk_one_step X hind hX hlaw ξ f hcf hF1 hfF hN hη hηb).trans (le_of_eq ?_)
      have : Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) = Real.exp c * Real.exp (-(c * N)) := by
        rw [← Real.exp_add]; congr 1; simp only [c]; field_simp; ring
      rw [this]; ring)
  filter_upwards [h] with ω hω
  filter_upwards [hω] with N hN
  intro i hi
  by_contra hlt
  exact hN ⟨i, hi, not_le.mp hlt⟩

/-- Almost surely, the sampled walk converges to `P_∞ f` uniformly over the sample points
(continuous `f`, fixed `ξ`). -/
theorem walk_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) {f : S2 → ℝ}
    (hcf : Continuous f) {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |walk ξ f X N ω i - Pinf (gk ξ) f (X i ω)| ≤ ε := by
  set Z := sphZ ξ
  have hZ : 0 < Z := sphZ_pos ξ
  set ηk : ℕ → ℝ := fun k => min (Z / 4) (1 / ((k:ℝ) + 1))
  have hηk : ∀ k, 0 < ηk k := fun k => lt_min (by positivity) (by positivity)
  have hall := ae_all_iff.mpr (fun k => walk_ae_eta X hind hX hlaw ξ hcf hF1 hfF
    (hηk k) (min_le_left _ _))
  filter_upwards [hall] with ω hω
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (8 * (1 + F) / (Z * ε))
  obtain ⟨M, hM⟩ := exists_nat_gt (16 * F / (Z * ε) + 1)
  filter_upwards [hω k, eventually_ge_atTop (M + 2)] with N hN hNM
  intro i hi
  refine (hN i hi).trans ?_
  have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hη1 : ηk k * ((k:ℝ) + 1) ≤ 1 := by
    have : ηk k ≤ 1 / ((k:ℝ) + 1) := min_le_right _ _
    rwa [le_div_iff₀ hk1] at this
  have hkZ : 8 * (1 + F) < ((k:ℝ) + 1) * (Z * ε) := by
    rw [div_lt_iff₀ (by positivity)] at hk; nlinarith
  have hNr : (M:ℝ) + 2 ≤ N := by exact_mod_cast hNM
  have hMZ : 16 * F < ((M:ℝ) - 1 + 1) * (Z * ε) := by
    have : 16 * F / (Z * ε) < M := by linarith
    rw [div_lt_iff₀ (by positivity)] at this; nlinarith
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  have e : 4 * (ηk k * (1 + F) + 2 * F / (N - 1)) / Z
      = 4 * ηk k * (1 + F) / Z + 8 * F / (((N:ℝ) - 1) * Z) := by
    field_simp; ring
  rw [e]
  have t1 : 4 * ηk k * (1 + F) / Z ≤ ε / 2 := by
    rw [div_le_iff₀ hZ]
    refine le_of_mul_le_mul_left ?_ hk1
    have := mul_le_mul_of_nonneg_left hη1 (show (0:ℝ) ≤ 4 * (1 + F) by linarith)
    nlinarith
  have t2 : 8 * F / (((N:ℝ) - 1) * Z) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : ((M:ℝ) - 1 + 1) * (Z * ε) ≤ ((N:ℝ) - 1) * (Z * ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  linarith

/-- **Theorem LB on `S²`, sample version at fixed scale, almost surely**: for every `ε > 0`,
eventually in `N`, `|L_N f(X_i) + Δf(X_i)| ≤ Cξ² + ε` for all sample points. -/
theorem LB_sample_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 →
      ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
        |LN ξ f X N ω i + sphLapS f (X i ω)| ≤ C * ξ ^ 2 + ε := by
  obtain ⟨C, hC0, hC⟩ := LB_sphere_smooth_sup hf
  obtain ⟨hcf, F, hF1, hfF⟩ := smooth_bound hf
  refine ⟨C, hC0, fun ξ hξ hξ1 => ?_⟩
  filter_upwards [walk_ae X hind hX hlaw ξ hcf hF1 hfF] with ω hω ε hε
  filter_upwards [hω (ε * ξ ^ 2 / 2) (by positivity)] with N hN i hi
  have h1 : |Pinf (gk ξ) f (X i ω) - walk ξ f X N ω i| ≤ ε * ξ ^ 2 / 2 := by
    rw [abs_sub_comm]; exact hN i hi
  calc |LN ξ f X N ω i + sphLapS f (X i ω)|
      ≤ 2 / ξ ^ 2 * |Pinf (gk ξ) f (X i ω) - walk ξ f X N ω i|
        + |Lxi ξ f (X i ω) + sphLapS f (X i ω)| := LN_abs_le ξ f X N ω i
    _ ≤ 2 / ξ ^ 2 * (ε * ξ ^ 2 / 2) + C * ξ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity)) (hC ξ hξ hξ1 _)
    _ = C * ξ ^ 2 + ε := by field_simp; ring

end AE

/-! ## Stage (3): joint limit ξ_N → 0 -/

section Joint

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Borel–Cantelli for eventual bounds `4/N²`. -/
theorem bc_sq (B : ℕ → Set Ω) (hB : ∀ᶠ N in atTop, μ.real (B N) ≤ 4 * ((N:ℝ) ^ 2)⁻¹) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ω ∉ B N := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hB
  set B' : ℕ → Set Ω := fun N => if N0 ≤ N then B N else ∅
  have hsum : Summable (fun N : ℕ => 4 * ((N:ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num : 1 < 2)).mul_left 4
  have hle : ∀ N, μ (B' N) ≤ ENNReal.ofReal (4 * ((N:ℝ) ^ 2)⁻¹) := by
    intro N
    by_cases h : N0 ≤ N
    · simp only [B', if_pos h]
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (hN0 N h)
    · simp [B', if_neg h]
  have hfin : ∑' N, μ (B' N) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω, eventually_ge_atTop N0] with N hN h2
  simpa [B', if_pos h2] using hN

theorem log_ge_one {N : ℕ} (hN : 3 ≤ N) : 1 ≤ Real.log N := by
  have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
  have h3' : Real.exp 1 ≤ N := by linarith [Real.exp_one_lt_d9]
  calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) h3'

/-- Joint limit for one tolerance `ε ∈ (0,1]`. -/
theorem joint_eps (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ} (hcf : Continuous f) {F : ℝ} (hF1 : 1 ≤ F)
    (hfF : ∀ y, |f y| ≤ F) {C : ℝ}
    (hC : ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 → ∀ x, |Lxi ξ f x + sphLapS f x| ≤ C * ξ ^ 2)
    (ξs : ℕ → ℝ) (hpos : ∀ N, 0 < ξs N) (hle : ∀ N, ξs N ≤ 1 / 20)
    (hlim : Tendsto ξs atTop (𝓝 0))
    (hreg : Tendsto (fun N : ℕ => ((N:ℝ) - 1) * ξs N ^ 8 / Real.log N) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ∀ i < N, |LN (ξs N) f X N ω i + sphLapS f (X i ω)| ≤ ε := by
  have hF0 : 0 < F := by linarith
  have hpi := Real.pi_pos
  set δ : ℝ := ε / (96 * π * (1 + F)) with hδdef
  have hδ : 0 < δ := by positivity
  set M : ℝ := 6 * F ^ 2 / δ ^ 2 + 192 * π * F / ε with hMdef
  have hM : 0 ≤ M := by positivity
  set B : ℕ → Set Ω := fun N => {ω | ∃ i < N,
      4 * (δ * ξs N ^ 4 * (1 + F) + 2 * F / (N - 1)) / sphZ (ξs N)
        < |walk (ξs N) f X N ω i - Pinf (gk (ξs N)) f (X i ω)|}
  have hkey : ∀ᶠ N : ℕ in atTop, 3 ≤ N ∧ M * Real.log N ≤ ((N:ℝ) - 1) * ξs N ^ 8 := by
    filter_upwards [hreg.eventually (eventually_ge_atTop M), eventually_ge_atTop 3]
      with N h1 h2
    refine ⟨h2, ?_⟩
    have hl := log_ge_one h2
    rwa [le_div_iff₀ (by linarith)] at h1
  have hprob : ∀ᶠ N : ℕ in atTop, μ.real (B N) ≤ 4 * ((N:ℝ) ^ 2)⁻¹ := by
    filter_upwards [hkey] with N hNk
    obtain ⟨h3, hk⟩ := hNk
    have hN2 : 2 ≤ N := by omega
    have hξ := hpos N
    have hξ1' : ξs N ≤ 1 := by linarith [hle N]
    have hη : 0 < δ * ξs N ^ 4 := by positivity
    have hδ16 : δ ≤ 1 / (16 * π) := by
      rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    have h42 : ξs N ^ 4 ≤ ξs N ^ 2 := pow_le_pow_of_le_one hξ.le hξ1' (by norm_num)
    have hZ := sphZ_ge hξ hξ1'
    have hηb : δ * ξs N ^ 4 ≤ sphZ (ξs N) / 4 := by
      calc δ * ξs N ^ 4 ≤ 1 / (16 * π) * ξs N ^ 2 :=
            mul_le_mul hδ16 h42 (by positivity) (by positivity)
        _ = (ξs N ^ 2 / (4 * π)) / 4 := by field_simp; ring
        _ ≤ sphZ (ξs N) / 4 := by linarith
    have hw := walk_one_step X hind hX hlaw (ξs N) f hcf hF1 hfF hN2 hη hηb
    refine le_trans hw ?_
    have hL : 0 ≤ Real.log N := by linarith [log_ge_one h3]
    have h6 : 6 * F ^ 2 / δ ^ 2 * Real.log N ≤ ((N:ℝ) - 1) * ξs N ^ 8 := by
      refine le_trans ?_ hk
      apply mul_le_mul_of_nonneg_right _ hL
      rw [hMdef]; linarith [show 0 ≤ 192 * π * F / ε by positivity]
    have h7 := mul_le_mul_of_nonneg_right h6 (sq_nonneg δ)
    have e7 : 6 * F ^ 2 / δ ^ 2 * Real.log N * δ ^ 2 = 6 * F ^ 2 * Real.log N := by
      field_simp
    have e8 : ((N:ℝ) - 1) * (δ * ξs N ^ 4) ^ 2 = ((N:ℝ) - 1) * ξs N ^ 8 * δ ^ 2 := by ring
    have hexp : -(((N:ℝ) - 1) * (δ * ξs N ^ 4) ^ 2) / (2 * F ^ 2) ≤ -(3 * Real.log N) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hN0 : (0:ℝ) < N := by
      have : (3:ℝ) ≤ N := by exact_mod_cast h3
      linarith
    calc 4 * (N:ℝ) * Real.exp (-(((N:ℝ) - 1) * (δ * ξs N ^ 4) ^ 2) / (2 * F ^ 2))
        ≤ 4 * N * Real.exp (-(3 * Real.log N)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
      _ = 4 * ((N:ℝ) ^ 2)⁻¹ := by
          rw [Real.exp_neg, show 3 * Real.log N = Real.log ((N:ℝ) ^ 3) by
            rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
          field_simp
  have hsmall : ∀ᶠ N : ℕ in atTop, C * ξs N ^ 2 < ε / 3 := by
    have ht : Tendsto (fun N => C * ξs N ^ 2) atTop (𝓝 (C * 0 ^ 2)) := (hlim.pow 2).const_mul C
    rw [show C * (0:ℝ) ^ 2 = 0 by ring] at ht
    exact ht.eventually (gt_mem_nhds (by positivity))
  have hbc := bc_sq (μ := μ) B hprob
  filter_upwards [hbc] with ω hω
  filter_upwards [hω, hkey, hsmall] with N hN hNk hs
  obtain ⟨h3, hk⟩ := hNk
  intro i hi
  have hξ := hpos N
  have hξ1 := hle N
  have hξ1' : ξs N ≤ 1 := by linarith
  have hwalk : |Pinf (gk (ξs N)) f (X i ω) - walk (ξs N) f X N ω i|
      ≤ 4 * (δ * ξs N ^ 4 * (1 + F) + 2 * F / (N - 1)) / sphZ (ξs N) := by
    rw [abs_sub_comm]; by_contra h; exact hN ⟨i, hi, not_le.mp h⟩
  have hn : (0:ℝ) < (N:ℝ) - 1 := by
    have : (3:ℝ) ≤ N := by exact_mod_cast h3
    linarith
  have herr := err_bound hξ hξ1' hδ.le hF0.le hn
  have hq : 192 * π * F / ε ≤ ((N:ℝ) - 1) * ξs N ^ 4 := by
    have hl := log_ge_one h3
    have h84 : ξs N ^ 8 ≤ ξs N ^ 4 := pow_le_pow_of_le_one hξ.le hξ1' (by norm_num)
    calc 192 * π * F / ε ≤ M := by rw [hMdef]; linarith [show 0 ≤ 6 * F ^ 2 / δ ^ 2 by positivity]
      _ ≤ M * Real.log N := le_mul_of_one_le_right hM hl
      _ ≤ ((N:ℝ) - 1) * ξs N ^ 8 := hk
      _ ≤ ((N:ℝ) - 1) * ξs N ^ 4 := mul_le_mul_of_nonneg_left h84 hn.le
  have h4 : 64 * π * F / (((N:ℝ) - 1) * ξs N ^ 4) ≤ ε / 3 := by
    rw [div_le_iff₀ (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hq (show (0:ℝ) ≤ ε / 3 by positivity)
    have e : ε / 3 * (192 * π * F / ε) = 64 * π * F := by field_simp; ring
    linarith
  have h1 : 32 * π * (δ * (1 + F)) = ε / 3 := by rw [hδdef]; field_simp; ring
  calc |LN (ξs N) f X N ω i + sphLapS f (X i ω)|
      ≤ 2 / ξs N ^ 2 * |Pinf (gk (ξs N)) f (X i ω) - walk (ξs N) f X N ω i|
        + |Lxi (ξs N) f (X i ω) + sphLapS f (X i ω)| := LN_abs_le (ξs N) f X N ω i
    _ ≤ 2 / ξs N ^ 2 * (4 * (δ * ξs N ^ 4 * (1 + F) + 2 * F / (N - 1)) / sphZ (ξs N))
        + C * ξs N ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hwalk (by positivity)) (hC _ hξ hξ1 _)
    _ ≤ ε := by linarith

/-- **Joint limit (sample version of Theorem LB on `S²`).** For `ξ_N ∈ (0, 1/20]` with `ξ_N → 0`
and `(N−1)ξ_N⁸ / log N → ∞`, almost surely `max_{i<N} |L_N f(X_i) + Δf(X_i)| → 0`
(sample walk with self-loop, kernel scale `ξ_N`). -/
theorem LB_sample_joint (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    (ξs : ℕ → ℝ) (hpos : ∀ N, 0 < ξs N) (hle : ∀ N, ξs N ≤ 1 / 20)
    (hlim : Tendsto ξs atTop (𝓝 0))
    (hreg : Tendsto (fun N : ℕ => ((N:ℝ) - 1) * ξs N ^ 8 / Real.log N) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |LN (ξs N) f X N ω i + sphLapS f (X i ω)| ≤ ε := by
  obtain ⟨C, -, hC⟩ := LB_sphere_smooth_sup hf
  obtain ⟨hcf, F, hF1, hfF⟩ := smooth_bound hf
  have hall := ae_all_iff.mpr (fun k : ℕ => joint_eps X hind hX hlaw hcf hF1 hfF hC ξs hpos hle
    hlim hreg (ε := 1 / ((k:ℝ) + 1)) (by positivity)
    ((div_le_one (by positivity)).mpr (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])))
  filter_upwards [hall] with ω hω ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with N hN i hi
  exact (hN i hi).trans hk.le

end Joint

end CTG.FunkHecke.LBSample

#print axioms CTG.FunkHecke.LBSample.LB_sample
#print axioms CTG.FunkHecke.LBSample.LB_sample_ae
#print axioms CTG.FunkHecke.LBSample.LB_sample_joint
#print axioms CTG.FunkHecke.LBSample.sphZ_ge
