/-
Eighty-second Lean file (after version 4). The existing versions of Theorem LB on S² restated with the
chart-independent Laplace–Beltrami operator `lapM roundMetricS` of `CorrelationsToGeometrySphereAtlas` in place of
the extrinsically defined `sphLapS`. Written by a subagent of the author-side session (task A195), checked here.
No new analysis: every statement is the old one rewritten with `lapM_roundS`.

`lapS_harmonic` (eigenvalue equation of the harmonics), `LB_sphere_M`, `LB_sphere_smooth_explicit_M`,
`LB_sphere_smooth_explicit_MM` (also the iterates and the constant written with `lapM`), `LB_sphere_smooth_sup_M`,
`LB_sample_M`, `LB_sample_ae_M`, `LB_sample_joint_M`, `LB_sample_ae_MM`, `LB_sample_joint_MM`, `sym_S2_M` (Green),
`proj_lap_M`.

NOT shown: the hypothesis is still the extrinsic condition `SphC2` (a C² extension of degree zero), no intrinsic
smoothness condition and no equivalence of the two; the limits of the `sphLapS` statements remain (population level
or the walk with self-loop, exponent 8 in the joint regime, measurability not shown here).
No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometrySphereAtlas
import CorrelationsToGeometryFunkHeckeLBSmoothExplicit
import CorrelationsToGeometryFunkHeckeLBSample

open MeasureTheory ProbabilityTheory Set Metric Real Filter Topology

noncomputable section

namespace CTG.SphereLBM

open CTG.FunkHecke (S2 E3 cdot Isotropic sigma sphZ)
open CTG.FunkHecke.SphereLB (Lxi)
open CTG.FunkHecke.SphereLaplace (sphLapS sphLapS_harmonic)
open CTG.FunkHecke.SphereLinComb (SphC2 sphC2_re)
open CTG.LaplaceBeltramiManifold (lapM)
open CTG.SphereAtlas (roundMetricS lapM_roundS)
open CTG.FunkHecke.LBSmooth (N4)
open CTG.FunkHecke.LBSample (LN)

/-- If `f` satisfies `SphC2` everywhere, then `lapM roundMetricS f = sphLapS f` as functions. -/
theorem lapS_eq_fun {f : S2 → ℝ} (hf : ∀ x, SphC2 f x) : lapM roundMetricS f = sphLapS f :=
  funext fun x => lapM_roundS f x (hf x)

/-! ## 1. Eigenvalue equation of the harmonics -/

/-- `lapM roundMetricS (Re (a·y)^l) = −l(l+1) · Re (a·y)^l` at every point, for isotropic `a = p + i q`. -/
theorem lapS_harmonic (p q : E3) (h : Isotropic p q) (l : ℕ) (x : S2) :
    lapM roundMetricS (fun y : S2 => (cdot p q y ^ l).re) x
      = -((l : ℝ) * (l + 1)) * (cdot p q x ^ l).re := by
  rw [lapM_roundS _ x (sphC2_re p q l x)]
  exact sphLapS_harmonic p q h l x

/-! ## 2. Theorem LB at the population level -/

/-- `LB_sphere` with `lapM roundMetricS`. -/
theorem LB_sphere_M {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (p q : E3) (h : Isotropic p q)
    (l : ℕ) (x : S2) :
    |Lxi ξ (fun y : S2 => (cdot p q y ^ l).re) x
        + lapM roundMetricS (fun y : S2 => (cdot p q y ^ l).re) x|
      ≤ ((ξ ^ 2 / 6 + 5 / 12 * ξ ^ 4) * ((l : ℝ) * (l + 1))
          + 51 / 200 * ξ ^ 2 * ((l : ℝ) * (l + 1)) ^ 2
          + 27 / 200 * ξ ^ 4 * ((l : ℝ) * (l + 1)) ^ 3) * |(cdot p q x ^ l).re| := by
  rw [lapM_roundS _ x (sphC2_re p q l x)]
  exact CTG.FunkHecke.SphereLaplace.LB_sphere hξ hξ1 p q h l x

/-- `LB_sphere_smooth_explicit` with `lapM roundMetricS` in the conclusion; hypotheses and `N4` (iterates of
`sphLapS`) unchanged. -/
theorem LB_sphere_smooth_explicit_M {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (x : S2) :
    |Lxi ξ f x + lapM roundMetricS f x| ≤ 3 * (74 / 25) * N4 f * ξ ^ 2 := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  rw [lapM_roundS f x (hf0 x)]
  exact CTG.FunkHecke.LBSmoothExplicit.LB_sphere_smooth_explicit hf hξ hξ1 x

/-- Iterates agree: if `lapM^[j] f` satisfies `SphC2` everywhere for all `j < k`, then the iterates of `lapM`
and of `sphLapS` coincide up to order `k`. -/
theorem iterate_eq {f : S2 → ℝ} {k : ℕ} (hf : ∀ j < k, ∀ x, SphC2 ((lapM roundMetricS)^[j] f) x) :
    ∀ j ≤ k, (lapM roundMetricS)^[j] f = sphLapS^[j] f := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hj' : j < k := hj
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih hj'.le]
    exact lapS_eq_fun (hf j hj')

/-- The `lapM`-iterate hypothesis implies the `sphLapS`-iterate hypothesis. -/
theorem hyp_of_lapS {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 ((lapM roundMetricS)^[j] f) x) :
    ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x := by
  intro j hj x
  rw [← iterate_eq hf j hj.le]; exact hf j hj x

/-- The constant `N4` written with the iterates of `lapM roundMetricS`. -/
def N4M (f : S2 → ℝ) : ℝ := Real.sqrt (∫ y, ((lapM roundMetricS)^[4] f) y ^ 2 ∂sigma)

theorem N4M_eq {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 ((lapM roundMetricS)^[j] f) x) : N4M f = N4 f := by
  unfold N4M N4; rw [iterate_eq hf 4 le_rfl]

/-- **Theorem LB on `S²` for smooth `f`, everything with `lapM roundMetricS`:** hypotheses on the iterates of
`lapM`, constant `√(∫ (lapM^[4] f)² dσ)`. -/
theorem LB_sphere_smooth_explicit_MM {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 ((lapM roundMetricS)^[j] f) x)
    {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) (x : S2) :
    |Lxi ξ f x + lapM roundMetricS f x| ≤ 3 * (74 / 25) * N4M f * ξ ^ 2 := by
  rw [N4M_eq hf]
  exact LB_sphere_smooth_explicit_M (hyp_of_lapS hf) hξ hξ1 x

/-- `LB_sphere_smooth_sup` with `lapM roundMetricS`. -/
theorem LB_sphere_smooth_sup_M {f : S2 → ℝ} (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 → ∀ x : S2,
      |Lxi ξ f x + lapM roundMetricS f x| ≤ C * ξ ^ 2 := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  rw [lapS_eq_fun hf0]
  exact CTG.FunkHecke.LBSmooth.LB_sphere_smooth_sup hf

/-! ## 3. Sample versions -/

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- `LB_sample` with `lapM roundMetricS`. -/
theorem LB_sample_M (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : ℝ, 1 ≤ F → (∀ y, |f y| ≤ F) → ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 →
      ∀ N : ℕ, 2 ≤ N → ∀ η : ℝ, 0 < η → η ≤ sphZ ξ / 4 →
      μ.real {ω | ∃ i < N, 2 / ξ ^ 2 * (4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ) + C * ξ ^ 2
          < |LN ξ f X N ω i + lapM roundMetricS f (X i ω)|}
        ≤ 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  rw [lapS_eq_fun hf0]
  exact CTG.FunkHecke.LBSample.LB_sample X hind hX hlaw hf

/-- `LB_sample_ae` with `lapM roundMetricS`. -/
theorem LB_sample_ae_M (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 →
      ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
        |LN ξ f X N ω i + lapM roundMetricS f (X i ω)| ≤ C * ξ ^ 2 + ε := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  rw [lapS_eq_fun hf0]
  exact CTG.FunkHecke.LBSample.LB_sample_ae X hind hX hlaw hf

/-- `LB_sample_joint` with `lapM roundMetricS`. -/
theorem LB_sample_joint_M (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x)
    (ξs : ℕ → ℝ) (hpos : ∀ N, 0 < ξs N) (hle : ∀ N, ξs N ≤ 1 / 20)
    (hlim : Tendsto ξs atTop (𝓝 0))
    (hreg : Tendsto (fun N : ℕ => ((N:ℝ) - 1) * ξs N ^ 8 / Real.log N) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |LN (ξs N) f X N ω i + lapM roundMetricS f (X i ω)| ≤ ε := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  rw [lapS_eq_fun hf0]
  exact CTG.FunkHecke.LBSample.LB_sample_joint X hind hX hlaw hf ξs hpos hle hlim hreg

/-- Variants with the hypothesis on the iterates of `lapM` (instead of `sphLapS`). -/
theorem LB_sample_joint_MM (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 ((lapM roundMetricS)^[j] f) x)
    (ξs : ℕ → ℝ) (hpos : ∀ N, 0 < ξs N) (hle : ∀ N, ξs N ≤ 1 / 20)
    (hlim : Tendsto ξs atTop (𝓝 0))
    (hreg : Tendsto (fun N : ℕ => ((N:ℝ) - 1) * ξs N ^ 8 / Real.log N) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |LN (ξs N) f X N ω i + lapM roundMetricS f (X i ω)| ≤ ε :=
  LB_sample_joint_M X hind hX hlaw (hyp_of_lapS hf) ξs hpos hle hlim hreg

theorem LB_sample_ae_MM (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 ((lapM roundMetricS)^[j] f) x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, 0 < ξ → ξ ≤ 1 / 20 →
      ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
        |LN ξ f X N ω i + lapM roundMetricS f (X i ω)| ≤ C * ξ ^ 2 + ε :=
  LB_sample_ae_M X hind hX hlaw (hyp_of_lapS hf)

end Sample

/-! ## 4. Green's identity and projection -/

/-- `sym_S2` with `lapM roundMetricS`. -/
theorem sym_S2_M {f g : S2 → ℝ} (hf : ∀ x, SphC2 f x) (hg : ∀ x, SphC2 g x) :
    ∫ x, g x * lapM roundMetricS f x ∂sigma = ∫ x, f x * lapM roundMetricS g x ∂sigma := by
  rw [lapS_eq_fun hf, lapS_eq_fun hg]
  exact CTG.FunkHecke.Green.sym_S2 hf hg

/-- `proj_lap` with `lapM roundMetricS`: `Π_l (Δ f) = −l(l+1) Π_l f`. -/
theorem proj_lap_M (l : ℕ) {f : S2 → ℝ} (hf : ∀ x, SphC2 f x) (x : S2) :
    CTG.FunkHecke.Proj.projDeg l (lapM roundMetricS f) x
      = -((l:ℝ) * (l + 1)) * CTG.FunkHecke.Proj.projDeg l f x := by
  rw [lapS_eq_fun hf]
  exact CTG.FunkHecke.Green.proj_lap l hf x

end CTG.SphereLBM

end

