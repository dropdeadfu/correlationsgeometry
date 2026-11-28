/-
Sixty-eighth file (A181, written by a subagent of the author-side session, checked by that session; read by nobody else).
Parseval on `S²` for continuous functions, the reproducing-kernel bound on a degree, and decay of the projections
`Π_l f` from smoothness. Namespace `CTG.FunkHecke.Parseval`; imports the compiled module of the sixty-seventh file
(`CorrelationsToGeometryFunkHeckeProj`). Check with `./check_funk_hecke_parseval.sh` from `lean/`.

Proven without hypothesis, for every `f ∈ C(S²)`: `bessel_eq`, `bessel`, `L2_tendsto` (the partial sums of the
projections converge to `f` in `L²(σ)`), `parseval` (`HasSum (fun l ↦ ∫ (Π_l f)²) (∫ f²)`), `repro_bound`
(`|F x| ≤ √(2l+1) √(∫ F²)` on the degree-`l` span), `proj_L2_le`.
Proven under a HYPOTHESIS: `decay_L2`, `decay_sup` assume `Π_l (g_{j+1}) = −l(l+1) Π_l (g_j)` for a sequence `g`
with `g 0 = f`; that `g (j+1)` is the Laplacian of `g j` and that projection and Laplacian commute
(`Π_l Δ = −l(l+1) Π_l`) is NOT proven here. Not formalised either: uniform or pointwise convergence of the series,
the dimension `2l+1`, the link of `decay_sup` to `degM` of `LB_sphere_series_M`, the intrinsic Laplace–Beltrami
operator. No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeProj

open MeasureTheory Set Metric Real Filter Topology
open scoped RealInnerProductSpace

namespace CTG.FunkHecke.Parseval

open CTG.FunkHecke CTG.FunkHecke.Complete CTG.FunkHecke.Proj

local instance : CompactSpace S2 := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)

local instance : IsProbabilityMeasure sigma :=
  ⟨by rw [← ofReal_measureReal, sigma_real_univ', ENNReal.ofReal_one]⟩

/-- The embedding `C(S², ℝ) → L²(σ)`. -/
noncomputable abbrev TL : C(S2, ℝ) →L[ℝ] Lp ℝ 2 sigma := ContinuousMap.toLp 2 sigma ℝ

theorem ip (F G : C(S2, ℝ)) : ⟪TL F, TL G⟫ = ∫ x, F x * G x ∂sigma := by
  have h := ContinuousMap.inner_toLp (𝕜 := ℝ) sigma F G
  refine h.trans ?_
  congr 1; ext x; simp [mul_comm]

theorem nsq (F : C(S2, ℝ)) : ‖TL F‖ ^ 2 = ∫ x, F x ^ 2 ∂sigma := by
  rw [← real_inner_self_eq_norm_sq, ip]; congr 1; ext x; ring

theorem nsq_le (F : C(S2, ℝ)) : ‖TL F‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  rw [nsq]
  calc ∫ x, F x ^ 2 ∂sigma ≤ ∫ _x, ‖F‖ ^ 2 ∂sigma := by
        refine integral_mono (integrable_of_cont sigma (F.continuous.pow 2)) (integrable_const _)
          fun x => ?_
        have h := F.norm_coe_le_norm x
        rw [Real.norm_eq_abs] at h
        have : F x ^ 2 = |F x| ^ 2 := (sq_abs _).symm
        rw [this]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = ‖F‖ ^ 2 := by rw [integral_const, sigma_real_univ', one_smul]

/-! ## The projections as continuous maps -/

theorem projDeg_cont (l : ℕ) (f : C(S2, ℝ)) : Continuous (projDeg l f) := by
  obtain ⟨F, _, he⟩ := proj_mem l f
  have : projDeg l f = F := funext fun x => (he x).symm
  rw [this]; exact F.continuous

noncomputable def projC (l : ℕ) (f : C(S2, ℝ)) : C(S2, ℝ) := ⟨projDeg l f, projDeg_cont l f⟩

theorem projC_apply (l : ℕ) (f : C(S2, ℝ)) (x : S2) : projC l f x = projDeg l f x := rfl

theorem projC_mem (l : ℕ) (f : C(S2, ℝ)) : projC l f ∈ harmDeg l := by
  obtain ⟨F, hF, he⟩ := proj_mem l f
  have : projC l f = F := by ext x; exact (he x).symm
  rw [this]; exact hF

theorem orthC {l k : ℕ} (hlk : l ≠ k) {F G : C(S2, ℝ)} (hF : F ∈ harmDeg l) (hG : G ∈ harmDeg k) :
    ⟪TL F, TL G⟫ = 0 := by rw [ip]; exact orth_span hlk hF hG

theorem perpC (l : ℕ) (f : C(S2, ℝ)) {G : C(S2, ℝ)} (hG : G ∈ harmDeg l) :
    ⟪TL (f - projC l f), TL G⟫ = 0 := by
  rw [ip, ← proj_orth l f hG]; congr 1; ext x
  simp only [ContinuousMap.sub_apply, projC_apply]; ring

/-! ## The spaces `V_L` of degrees `≤ L` and the partial sums -/

noncomputable def VL (L : ℕ) : Submodule ℝ C(S2, ℝ) :=
  Submodule.span ℝ (⋃ (l : ℕ) (_ : l ≤ L), (harmDeg l : Set C(S2, ℝ)))

theorem VL_mono {L M : ℕ} (h : L ≤ M) : VL L ≤ VL M := by
  refine Submodule.span_mono ?_
  intro F hF
  simp only [mem_iUnion, exists_prop] at hF ⊢
  obtain ⟨l, hl, hF⟩ := hF
  exact ⟨l, by omega, hF⟩

theorem harmDeg_le_VL {l L : ℕ} (h : l ≤ L) : harmDeg l ≤ VL L := by
  intro F hF
  refine Submodule.subset_span ?_
  simp only [mem_iUnion, exists_prop]
  exact ⟨l, by omega, hF⟩

theorem harmSpan_VL {g : C(S2, ℝ)} (hg : g ∈ harmSpan) : ∃ L, g ∈ VL L := by
  induction hg using Submodule.span_induction with
  | mem F hF =>
      obtain ⟨p, q, l, hpq, rfl⟩ := hF
      exact ⟨l, harmDeg_le_VL le_rfl (harm_memDeg p q l hpq)⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add F G _ _ hF hG =>
      obtain ⟨L1, h1⟩ := hF; obtain ⟨L2, h2⟩ := hG
      exact ⟨max L1 L2, Submodule.add_mem _ (VL_mono (le_max_left _ _) h1)
        (VL_mono (le_max_right _ _) h2)⟩
  | smul c F _ hF =>
      obtain ⟨L, h⟩ := hF; exact ⟨L, Submodule.smul_mem _ c h⟩

noncomputable def SL (L : ℕ) (f : C(S2, ℝ)) : C(S2, ℝ) := ∑ l ∈ Finset.range (L + 1), projC l f

theorem SL_apply (L : ℕ) (f : C(S2, ℝ)) (x : S2) :
    SL L f x = ∑ l ∈ Finset.range (L + 1), projDeg l f x := by
  simp [SL, projC_apply]

theorem SL_mem (L : ℕ) (f : C(S2, ℝ)) : SL L f ∈ VL L :=
  Submodule.sum_mem _ fun l hl => harmDeg_le_VL (by simp at hl; omega) (projC_mem l f)

/-- `f − S_L f ⊥ V_L`. -/
theorem perp_VL (L : ℕ) (f : C(S2, ℝ)) {G : C(S2, ℝ)} (hG : G ∈ VL L) :
    ⟪TL (f - SL L f), TL G⟫ = 0 := by
  induction hG using Submodule.span_induction with
  | mem G hG =>
      simp only [mem_iUnion, exists_prop] at hG
      obtain ⟨k, hk, hG⟩ := hG
      have hsum : ⟪TL (SL L f), TL G⟫ = ⟪TL (projC k f), TL G⟫ := by
        unfold SL
        rw [map_sum, sum_inner]
        refine Finset.sum_eq_single k (fun l _ hlk => orthC hlk (projC_mem l f) hG) ?_
        intro hk'; simp at hk'; omega
      have hk2 := perpC k f hG
      rw [map_sub, inner_sub_left] at hk2 ⊢
      rw [hsum]; exact hk2
  | zero => simp
  | add F G _ _ hF hG => rw [map_add, inner_add_right, hF, hG, add_zero]
  | smul c F _ hF => rw [map_smul, inner_smul_right, hF, mul_zero]

/-- `S_L f` is the best `L²` approximation of `f` in `V_L`. -/
theorem best_approx (L : ℕ) (f : C(S2, ℝ)) {g : C(S2, ℝ)} (hg : g ∈ VL L) :
    ‖TL (f - SL L f)‖ ^ 2 ≤ ‖TL (f - g)‖ ^ 2 := by
  have hd : f - g = (f - SL L f) + (SL L f - g) := by abel
  have hm : SL L f - g ∈ VL L := Submodule.sub_mem _ (SL_mem L f) hg
  rw [hd, map_add, norm_add_sq_real, perp_VL L f hm]
  nlinarith [sq_nonneg ‖TL (SL L f - g)‖]

/-- Pythagoras for the partial sum. -/
theorem norm_SL (L : ℕ) (f : C(S2, ℝ)) :
    ‖TL (SL L f)‖ ^ 2 = ∑ l ∈ Finset.range (L + 1), ‖TL (projC l f)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold SL
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [inner_sum, ← real_inner_self_eq_norm_sq]
  refine Finset.sum_eq_single l (fun k _ hkl => orthC (Ne.symm hkl) (projC_mem l f) (projC_mem k f)) ?_
  intro h; exact absurd ‹l ∈ _› h

/-! ## Stage 1: Bessel, `L²` convergence, Parseval -/

/-- **Bessel identity**: `∫ f² = ∫ (f − Σ_{l≤L} Π_l f)² + Σ_{l≤L} ∫ (Π_l f)²`. -/
theorem bessel_eq (L : ℕ) (f : C(S2, ℝ)) :
    ∫ x, f x ^ 2 ∂sigma = ∫ x, (f x - ∑ l ∈ Finset.range (L + 1), projDeg l f x) ^ 2 ∂sigma
      + ∑ l ∈ Finset.range (L + 1), ∫ x, projDeg l f x ^ 2 ∂sigma := by
  have hd : f = (f - SL L f) + SL L f := by abel
  have h1 : ‖TL f‖ ^ 2 = ‖TL (f - SL L f)‖ ^ 2 + ‖TL (SL L f)‖ ^ 2 := by
    conv_lhs => rw [hd]
    rw [map_add, norm_add_sq_real, perp_VL L f (SL_mem L f)]; ring
  rw [norm_SL, nsq, nsq] at h1
  rw [h1]
  congr 1
  · congr 1; ext x; rw [ContinuousMap.sub_apply, SL_apply]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [nsq]; rfl

/-- **Bessel inequality**. -/
theorem bessel (L : ℕ) (f : C(S2, ℝ)) :
    ∑ l ∈ Finset.range (L + 1), ∫ x, projDeg l f x ^ 2 ∂sigma ≤ ∫ x, f x ^ 2 ∂sigma := by
  rw [bessel_eq L f]
  have : 0 ≤ ∫ x, (f x - ∑ l ∈ Finset.range (L + 1), projDeg l f x) ^ 2 ∂sigma :=
    integral_nonneg fun x => sq_nonneg _
  linarith

/-- **`L²` convergence of the expansion in degrees** for every continuous `f`. -/
theorem L2_tendsto (f : C(S2, ℝ)) :
    Tendsto (fun L => ∫ x, (f x - ∑ l ∈ Finset.range (L + 1), projDeg l f x) ^ 2 ∂sigma)
      atTop (𝓝 0) := by
  have herr : ∀ L, ∫ x, (f x - ∑ l ∈ Finset.range (L + 1), projDeg l f x) ^ 2 ∂sigma
      = ‖TL (f - SL L f)‖ ^ 2 := by
    intro L; rw [nsq]; congr 1; ext x; rw [ContinuousMap.sub_apply, SL_apply]
  simp only [herr]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := harmSpan_dense.exists_dist_lt f (lt_min one_pos hε)
  obtain ⟨L0, hL0⟩ := harmSpan_VL hg
  refine ⟨L0, fun L hL => ?_⟩
  have hgL : g ∈ VL L := VL_mono hL hL0
  have h1 := best_approx L f hgL
  have h2 := nsq_le (f - g)
  rw [← dist_eq_norm] at h2
  have hd0 : 0 ≤ dist f g := dist_nonneg
  have hd1 : dist f g < 1 := lt_of_lt_of_le hfg (min_le_left _ _)
  have hd2 : dist f g < ε := lt_of_lt_of_le hfg (min_le_right _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  nlinarith

/-- **Parseval**: `Σ_l ∫ (Π_l f)² dσ = ∫ f² dσ` for every continuous `f`. -/
theorem parseval (f : C(S2, ℝ)) :
    HasSum (fun l => ∫ x, projDeg l f x ^ 2 ∂sigma) (∫ x, f x ^ 2 ∂sigma) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun l => integral_nonneg fun x => sq_nonneg _)]
  rw [← tendsto_add_atTop_iff_nat 1]
  have h := (tendsto_const_nhds (x := ∫ x, f x ^ 2 ∂sigma)).sub (L2_tendsto f)
  rw [sub_zero] at h
  refine h.congr fun L => ?_
  rw [bessel_eq L f]; ring

/-! ## Stage 3: reproducing kernel on a degree and decay -/

theorem legP_one_val : ∀ n : ℕ, legP n 1 = 1 ∧ legP (n + 1) 1 = 1
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
      obtain ⟨h0, h1⟩ := legP_one_val n
      refine ⟨h1, ?_⟩
      show ((2 * (n : ℝ) + 3) * 1 * legP (n + 1) 1 - ((n : ℝ) + 1) * legP n 1) / ((n : ℝ) + 2) = 1
      rw [h0, h1]; field_simp; ring

theorem inner_self_S2 (x : S2) : ⟪(x : E3), (x : E3)⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, mem_sphere_zero_iff_norm.1 x.2]; norm_num

/-- **Reproducing-kernel bound**: `|F(x)| ≤ √(2l+1) · ‖F‖_{L²(σ)}` for `F` in the span of degree `l`. -/
theorem repro_bound {l : ℕ} {F : C(S2, ℝ)} (hF : F ∈ harmDeg l) (x : S2) :
    |F x| ≤ Real.sqrt (2 * (l : ℝ) + 1) * Real.sqrt (∫ y, F y ^ 2 ∂sigma) := by
  obtain ⟨K, hK, hKe⟩ := legendre_mem_deg (x : E3) (mem_sphere_zero_iff_norm.1 x.2) l
  have hc : (0 : ℝ) < 2 * (l : ℝ) + 1 := by positivity
  set s := Real.sqrt (2 * (l : ℝ) + 1) with hsdef
  -- `Π_l G(x) = (2l+1) ⟪TL K, TL G⟫`
  have hrep : ∀ G : C(S2, ℝ), projDeg l G x = (2 * (l : ℝ) + 1) * ⟪TL K, TL G⟫ := by
    intro G
    unfold projDeg zonalOp; rw [ip]; congr 1; congr 1; ext y; rw [hKe]
  have hKK : ‖TL K‖ ^ 2 = 1 / (2 * (l : ℝ) + 1) := by
    have h1 := hrep K
    rw [proj_self hK x, hKe, inner_self_S2, (legP_one_val l).1, real_inner_self_eq_norm_sq] at h1
    field_simp; linarith
  have hFx : F x = (2 * (l : ℝ) + 1) * ⟪TL K, TL F⟫ := by rw [← hrep F, proj_self hF x]
  have hcs := abs_real_inner_le_norm (TL K) (TL F)
  have hnK : ‖TL K‖ = 1 / s := by
    have h0 : 0 ≤ ‖TL K‖ := norm_nonneg _
    rw [← Real.sqrt_sq h0, hKK, Real.sqrt_div' 1 hc.le, Real.sqrt_one]
  have hnF : ‖TL F‖ = Real.sqrt (∫ y, F y ^ 2 ∂sigma) := by
    rw [← nsq, Real.sqrt_sq (norm_nonneg _)]
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hss : s ^ 2 = 2 * (l : ℝ) + 1 := Real.sq_sqrt hc.le
  rw [hFx, abs_mul, abs_of_pos hc, ← hnF]
  calc (2 * (l : ℝ) + 1) * |⟪TL K, TL F⟫| ≤ (2 * (l : ℝ) + 1) * (‖TL K‖ * ‖TL F‖) :=
        mul_le_mul_of_nonneg_left hcs hc.le
    _ = s * ‖TL F‖ := by
        rw [hnK, ← hss]; field_simp

/-- Single-term Bessel: `∫ (Π_l f)² ≤ ∫ f²`. -/
theorem proj_L2_le (l : ℕ) (f : C(S2, ℝ)) :
    ∫ x, projDeg l f x ^ 2 ∂sigma ≤ ∫ x, f x ^ 2 ∂sigma := by
  have hd : f = (f - projC l f) + projC l f := by abel
  have h1 : ‖TL f‖ ^ 2 = ‖TL (f - projC l f)‖ ^ 2 + ‖TL (projC l f)‖ ^ 2 := by
    conv_lhs => rw [hd]
    rw [map_add, norm_add_sq_real, perpC l f (projC_mem l f)]; ring
  rw [nsq, nsq] at h1
  have h2 : ∫ x, projDeg l f x ^ 2 ∂sigma = ‖TL (projC l f)‖ ^ 2 := by rw [nsq]; rfl
  rw [h2, h1]
  have : 0 ≤ ∫ x, (f - projC l f) x ^ 2 ∂sigma := integral_nonneg fun x => sq_nonneg _
  linarith

/-- Iterating the HYPOTHESIS `Π_l g_{j+1} = −l(l+1) Π_l g_j`. -/
theorem proj_iter (g : ℕ → C(S2, ℝ))
    (hΔ : ∀ j l x, projDeg l (g (j + 1)) x = -((l : ℝ) * (l + 1)) * projDeg l (g j) x)
    (k l : ℕ) (x : S2) :
    projDeg l (g k) x = (-((l : ℝ) * (l + 1))) ^ k * projDeg l (g 0) x := by
  induction k with
  | zero => simp
  | succ k ih => rw [hΔ, ih, pow_succ]; ring

/-- **Decay in `L²`** (conditional).  Let `g 0 = f` and HYPOTHESIS (Stage 2, the exchange of `Π_l` with the
spherical Laplacian applied to `g j`, where `g (j+1)` is meant to be `Δ_{S²} g j`):
`Π_l (g (j+1)) = −l(l+1) Π_l (g j)`.  Then `(l(l+1))^{2k} ∫ (Π_l f)² ≤ ∫ (g k)²`. -/
theorem decay_L2 (g : ℕ → C(S2, ℝ))
    (hΔ : ∀ j l x, projDeg l (g (j + 1)) x = -((l : ℝ) * (l + 1)) * projDeg l (g j) x)
    (k l : ℕ) :
    ((l : ℝ) * (l + 1)) ^ (2 * k) * ∫ x, projDeg l (g 0) x ^ 2 ∂sigma ≤ ∫ x, g k x ^ 2 ∂sigma := by
  refine le_trans (le_of_eq ?_) (proj_L2_le l (g k))
  rw [← integral_const_mul]; congr 1; ext x
  rw [proj_iter g hΔ k l x]
  set A : ℝ := (l : ℝ) * (l + 1)
  set P : ℝ := projDeg l (⇑(g 0)) x
  rw [show ((-A) ^ k * P) ^ 2 = ((-A) ^ 2) ^ k * P ^ 2 by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2], neg_sq, ← pow_mul]

/-- **Decay in the supremum norm** (conditional, same HYPOTHESIS):
`(l(l+1))^k · |Π_l f(x)| ≤ √(2l+1) · ‖g k‖_{L²(σ)}`. -/
theorem decay_sup (g : ℕ → C(S2, ℝ))
    (hΔ : ∀ j l x, projDeg l (g (j + 1)) x = -((l : ℝ) * (l + 1)) * projDeg l (g j) x)
    (k l : ℕ) (x : S2) :
    ((l : ℝ) * (l + 1)) ^ k * |projDeg l (g 0) x|
      ≤ Real.sqrt (2 * (l : ℝ) + 1) * Real.sqrt (∫ y, g k y ^ 2 ∂sigma) := by
  have hr := repro_bound (projC_mem l (g 0)) x
  simp only [projC_apply] at hr
  have hlam : (0 : ℝ) ≤ ((l : ℝ) * (l + 1)) ^ k := by positivity
  have hI : 0 ≤ ∫ y, projDeg l (g 0) y ^ 2 ∂sigma := integral_nonneg fun y => sq_nonneg _
  have hd := decay_L2 g hΔ k l
  have hsq : ((l : ℝ) * (l + 1)) ^ k * Real.sqrt (∫ y, projDeg l (g 0) y ^ 2 ∂sigma)
      ≤ Real.sqrt (∫ y, g k y ^ 2 ∂sigma) := by
    rw [← Real.sqrt_sq hlam, ← Real.sqrt_mul (sq_nonneg _)]
    refine Real.sqrt_le_sqrt ?_
    rw [← pow_mul, mul_comm k 2]; exact hd
  calc ((l : ℝ) * (l + 1)) ^ k * |projDeg l (g 0) x|
      ≤ ((l : ℝ) * (l + 1)) ^ k * (Real.sqrt (2 * (l : ℝ) + 1)
          * Real.sqrt (∫ y, projDeg l (g 0) y ^ 2 ∂sigma)) := mul_le_mul_of_nonneg_left hr hlam
    _ = Real.sqrt (2 * (l : ℝ) + 1) * (((l : ℝ) * (l + 1)) ^ k
          * Real.sqrt (∫ y, projDeg l (g 0) y ^ 2 ∂sigma)) := by ring
    _ ≤ Real.sqrt (2 * (l : ℝ) + 1) * Real.sqrt (∫ y, g k y ^ 2 ∂sigma) :=
        mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)

end CTG.FunkHecke.Parseval

#print axioms CTG.FunkHecke.Parseval.parseval
#print axioms CTG.FunkHecke.Parseval.L2_tendsto
#print axioms CTG.FunkHecke.Parseval.repro_bound
#print axioms CTG.FunkHecke.Parseval.decay_sup
