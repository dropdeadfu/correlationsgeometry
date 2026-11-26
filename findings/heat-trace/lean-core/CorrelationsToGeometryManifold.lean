import Mathlib

/-!
# Riemannian distance: comparison of two metrics (Mathlib only)

Ninth Lean file of the project "From Correlations to Geometry"; it imports only Mathlib (tag v4.29.0).
Check with `cd lean && ./check_manifold.sh`.

Begun on 23 November 2026 at the author's decision to build, step by step, the statements on curved
manifolds that Appendix H of the paper needs and that Mathlib does not contain.  Mathlib provides the
length of a path and the Riemannian extended distance `Manifold.riemannianEDist` for a manifold whose
tangent spaces carry an extended norm.  This file compares the distances of TWO such families of norms
on the same manifold.

First step (`riemannianEDist_le_mul`): if `‖v‖₂ ≤ c ‖v‖₁` for all tangent vectors, then
`d₂ ≤ c d₁`.  Consequence (`riemannianEDist_comparison`): if `e^{-x}‖v‖₁ ≤ ‖v‖₂ ≤ e^{x}‖v‖₁`, then
`e^{-x} d₁ ≤ d₂ ≤ e^{x} d₁`; this is the comparison of the distances in Step 1 of the proof of
Proposition `prop:dotLN-diff`, which was a hypothesis of `TimeAppendix4.distance_step`.

Second step (`metric_growth`, `norm_growth`): for one tangent vector, `f τ = h_τ(v,v) > 0` with
`|∂_τ f| ≤ 2κ f` gives `‖v‖_b ≤ e^{κ|b−a|} ‖v‖_a` (scalar statement).

Combined (`riemannianEDist_time`): for a family of norms `‖v‖_τ = (g τ x v)^{1/2}` with
`|∂_τ g| ≤ 2κ g`, `d_b ≤ e^{κ|b−a|} d_a`.

What this is NOT: `g` is an arbitrary function of `(τ, x, v)`, not a metric tensor (no bilinearity,
no smoothness in `x`); finiteness of the distance is a hypothesis of the real-valued form
(`riemannianDist_time_real`), minimisers do not occur; nothing on volume
growth, injectivity radius, curvature or the Laplace–Beltrami operator.
No `sorry`, no `axiom`, no `native_decide`.
-/

open Set MeasureTheory Bundle Manifold
open scoped Manifold ENNReal ContDiff Topology

noncomputable section

namespace CTG.ManifoldDistance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If the second family of norms is at most `c` times the first on every tangent vector, the second
Riemannian distance is at most `c` times the first (`0 < c < ∞`). -/
theorem riemannianEDist_le_mul (n1 n2 : ∀ x : M, ENorm (TangentSpace I x)) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hc : c ≠ ⊤)
    (h : ∀ (x : M) (v : TangentSpace I x), @enorm _ (n2 x) v ≤ c * @enorm _ (n1 x) v) (x y : M) :
    (letI := n2; Manifold.riemannianEDist I x y) ≤ c * (letI := n1; Manifold.riemannianEDist I x y) := by
  simp only [Manifold.riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne hc0 hc]
  refine iInf_mono fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 hc]
  refine iInf_mono fun _ => ?_
  rw [← lintegral_const_mul' _ _ hc]
  exact lintegral_mono fun t => h _ _

/-- Two-sided comparison: `e^{-x}‖v‖₁ ≤ ‖v‖₂ ≤ e^{x}‖v‖₁` for all tangent vectors implies
`e^{-x} d₁ ≤ d₂ ≤ e^{x} d₁`. -/
theorem riemannianEDist_comparison (n1 n2 : ∀ x : M, ENorm (TangentSpace I x)) (x : ℝ)
    (hup : ∀ (p : M) (v : TangentSpace I p),
      @enorm _ (n2 p) v ≤ ENNReal.ofReal (Real.exp x) * @enorm _ (n1 p) v)
    (hlo : ∀ (p : M) (v : TangentSpace I p),
      @enorm _ (n1 p) v ≤ ENNReal.ofReal (Real.exp x) * @enorm _ (n2 p) v) (p q : M) :
    (letI := n2; Manifold.riemannianEDist I p q)
        ≤ ENNReal.ofReal (Real.exp x) * (letI := n1; Manifold.riemannianEDist I p q) ∧
    (letI := n1; Manifold.riemannianEDist I p q)
        ≤ ENNReal.ofReal (Real.exp x) * (letI := n2; Manifold.riemannianEDist I p q) := by
  have h0 : ENNReal.ofReal (Real.exp x) ≠ 0 := by
    simp [Real.exp_pos]
  exact ⟨riemannianEDist_le_mul n1 n2 _ h0 ENNReal.ofReal_ne_top hup p q,
    riemannianEDist_le_mul n2 n1 _ h0 ENNReal.ofReal_ne_top hlo p q⟩

/-- Second step, pointwise in the tangent vector: if `f τ = h_τ(v,v) > 0` is differentiable in `τ`
with `|∂_τ f| ≤ 2κ f` (this is `∂_τ h_τ = 2K_τ`, `|K_τ(v,v)| ≤ κ h_τ(v,v)`), then
`f b ≤ e^{2κ|b−a|} f a`. -/
theorem metric_growth (f f' : ℝ → ℝ) (κ : ℝ) (hpos : ∀ t, 0 < f t)
    (hd : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, |f' t| ≤ 2 * κ * f t) (a b : ℝ) :
    f b ≤ Real.exp (2 * κ * |b - a|) * f a := by
  have hg : ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun s => Real.log (f s)) (f' t / f t) Set.univ t := fun t _ =>
    ((hd t).log (hpos t).ne').hasDerivWithinAt
  have hbd : ∀ t ∈ (Set.univ : Set ℝ), ‖f' t / f t‖ ≤ 2 * κ := fun t _ => by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos t), div_le_iff₀ (hpos t)]
    exact hb t
  have h := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbd
    (Set.mem_univ a) (Set.mem_univ b)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have h2 : Real.log (f b) ≤ 2 * κ * |b - a| + Real.log (f a) := by
    have := le_abs_self (Real.log (f b) - Real.log (f a)); linarith
  have h3 := Real.exp_le_exp.mpr h2
  rwa [Real.exp_add, Real.exp_log (hpos b), Real.exp_log (hpos a)] at h3

/-- The same for the norm `‖v‖_τ = (h_τ(v,v))^{1/2}`: `‖v‖_b ≤ e^{κ|b−a|} ‖v‖_a`. -/
theorem norm_growth (f f' : ℝ → ℝ) (κ : ℝ) (hpos : ∀ t, 0 < f t)
    (hd : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, |f' t| ≤ 2 * κ * f t) (a b : ℝ) :
    Real.sqrt (f b) ≤ Real.exp (κ * |b - a|) * Real.sqrt (f a) := by
  have h := metric_growth f f' κ hpos hd hb a b
  have e : Real.exp (2 * κ * |b - a|) = Real.exp (κ * |b - a|) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Real.sqrt (f b) ≤ Real.sqrt (Real.exp (κ * |b - a|) ^ 2 * f a) :=
    Real.sqrt_le_sqrt (by rw [← e]; exact h)
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] at h2

/-- First and second step combined, for a time-dependent family of norms on the tangent spaces:
if `‖v‖_τ = (g τ x v)^{1/2}` with `g` either identically zero in `τ` or positive, differentiable in `τ`
with `|∂_τ g| ≤ 2κ g`, then the Riemannian distances at two times satisfy
`d_b ≤ e^{κ|b−a|} d_a`.  With `a` and `b` exchanged this is the comparison
`e^{-κ|η|} d ≤ d' ≤ e^{κ|η|} d` of Step 1 of `prop:dotLN-diff`.  The hypothesis `hcase` holds
automatically when `g τ x ·` is a positive definite quadratic form for every `τ`. -/
theorem riemannianEDist_time (n : ℝ → ∀ x : M, ENorm (TangentSpace I x))
    (g g' : ℝ → (x : M) → TangentSpace I x → ℝ) (κ : ℝ)
    (hn : ∀ τ x v, @enorm _ (n τ x) v = ENNReal.ofReal (Real.sqrt (g τ x v)))
    (hcase : ∀ x v, (∀ τ, g τ x v = 0) ∨ (∀ τ, 0 < g τ x v))
    (hd : ∀ τ x v, HasDerivAt (fun s => g s x v) (g' τ x v) τ)
    (hb : ∀ τ x v, |g' τ x v| ≤ 2 * κ * g τ x v) (a b : ℝ) (p q : M) :
    (letI := n b; Manifold.riemannianEDist I p q)
      ≤ ENNReal.ofReal (Real.exp (κ * |b - a|)) * (letI := n a; Manifold.riemannianEDist I p q) := by
  refine riemannianEDist_le_mul (n a) (n b) _ (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
    (fun x v => ?_) p q
  rw [hn, hn]
  rcases hcase x v with h0 | hpos
  · simp [h0]
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal
      (norm_growth (fun s => g s x v) (fun s => g' s x v) κ hpos (fun t => hd t x v)
        (fun t => hb t x v) a b)

/-- Passage to real numbers: two extended distances with `d' ≤ e^{x} d`, `d ≤ e^{x} d'` and `d` finite
are both finite, and `e^{-x} d ≤ d' ≤ e^{x} d` holds for their real values.  This is the hypothesis of
`TimeAppendix4.distance_step` in the seventh file.  Finiteness of `d` is a HYPOTHESIS here. -/
theorem real_comparison (d d' : ℝ≥0∞) (x : ℝ)
    (h1 : d' ≤ ENNReal.ofReal (Real.exp x) * d) (h2 : d ≤ ENNReal.ofReal (Real.exp x) * d')
    (hd : d ≠ ⊤) :
    d' ≠ ⊤ ∧ Real.exp (-x) * d.toReal ≤ d'.toReal ∧ d'.toReal ≤ Real.exp x * d.toReal := by
  have hd' : d' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd) h1
  have e1 : d'.toReal ≤ Real.exp x * d.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos x).le] at this
  have e2 : d.toReal ≤ Real.exp x * d'.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd') h2
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos x).le] at this
  refine ⟨hd', ?_, e1⟩
  have h := mul_le_mul_of_nonneg_left e2 (Real.exp_pos (-x)).le
  rwa [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at h

/-- Step 1 of `prop:dotLN-diff` for the real distances at two times `a`, `b` of a time-dependent
family of norms, under the hypotheses of `riemannianEDist_time` and finiteness of the distance at
time `a`: `e^{-κ|b−a|} d_a ≤ d_b ≤ e^{κ|b−a|} d_a`. -/
theorem riemannianDist_time_real (n : ℝ → ∀ x : M, ENorm (TangentSpace I x))
    (g g' : ℝ → (x : M) → TangentSpace I x → ℝ) (κ : ℝ)
    (hn : ∀ τ x v, @enorm _ (n τ x) v = ENNReal.ofReal (Real.sqrt (g τ x v)))
    (hcase : ∀ x v, (∀ τ, g τ x v = 0) ∨ (∀ τ, 0 < g τ x v))
    (hd : ∀ τ x v, HasDerivAt (fun s => g s x v) (g' τ x v) τ)
    (hb : ∀ τ x v, |g' τ x v| ≤ 2 * κ * g τ x v) (a b : ℝ) (p q : M)
    (hfin : (letI := n a; Manifold.riemannianEDist I p q) ≠ ⊤) :
    (letI := n b; Manifold.riemannianEDist I p q) ≠ ⊤ ∧
    Real.exp (-(κ * |b - a|)) * (letI := n a; Manifold.riemannianEDist I p q).toReal
      ≤ (letI := n b; Manifold.riemannianEDist I p q).toReal ∧
    (letI := n b; Manifold.riemannianEDist I p q).toReal
      ≤ Real.exp (κ * |b - a|) * (letI := n a; Manifold.riemannianEDist I p q).toReal := by
  have h1 := riemannianEDist_time n g g' κ hn hcase hd hb a b p q
  have h2 := riemannianEDist_time n g g' κ hn hcase hd hb b a p q
  rw [abs_sub_comm a b] at h2
  exact real_comparison _ _ _ h1 h2 hfin

/-- In a preconnected pseudo-emetric space all extended distances are finite: the set of points at
finite distance from `x` is open, closed and non-empty. -/
theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have hopen : IsOpen {z : X | edist x z < ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    refine Filter.mem_of_superset (Metric.isOpen_eball.mem_nhds
      (Metric.mem_eball_self (x := z) (ε := 1) one_pos)) fun w hw => ?_
    have hw' : edist w z < 1 := hw
    calc edist x w ≤ edist x z + edist z w := edist_triangle _ _ _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hz, by rw [edist_comm]; exact hw'.trans ENNReal.one_lt_top⟩
  have hclosed : IsClosed {z : X | edist x z < ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro z hz
    refine Filter.mem_of_superset (Metric.isOpen_eball.mem_nhds
      (Metric.mem_eball_self (x := z) (ε := 1) one_pos)) fun w hw => ?_
    have hw' : edist w z < 1 := hw
    intro hfin
    apply hz
    calc edist x z ≤ edist x w + edist w z := edist_triangle _ _ _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hfin, hw'.trans ENNReal.one_lt_top⟩
  have huniv : {z : X | edist x z < ⊤} = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨x, by simp⟩
  have : y ∈ {z : X | edist x z < ⊤} := by rw [huniv]; trivial
  exact this.ne

/-- Hence on a connected Riemannian manifold in Mathlib's sense (`IsRiemannianManifold`: the extended
distance of the space is the infimum of the lengths of `C¹` paths) the Riemannian distance is finite. -/
theorem riemannianEDist_ne_top {M' : Type*} [PseudoEMetricSpace M'] [ChartedSpace H M']
    [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)] [IsRiemannianManifold I M']
    [PreconnectedSpace M'] (x y : M') : Manifold.riemannianEDist I x y ≠ ⊤ := by
  rw [← IsRiemannianManifold.out (I := I) x y]
  exact edist_ne_top_of_preconnected x y

/-- Interval form of `norm_growth`: the hypotheses are only required on a convex set `s` of times
(for instance `[-τ₀, τ₀]`), with derivatives within `s`. -/
theorem norm_growth_on (s : Set ℝ) (hs : Convex ℝ s) (f f' : ℝ → ℝ) (κ : ℝ)
    (hpos : ∀ t ∈ s, 0 < f t) (hd : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t)
    (hb : ∀ t ∈ s, |f' t| ≤ 2 * κ * f t) {a b : ℝ} (ha : a ∈ s) (hb' : b ∈ s) :
    Real.sqrt (f b) ≤ Real.exp (κ * |b - a|) * Real.sqrt (f a) := by
  have hg : ∀ t ∈ s, HasDerivWithinAt (fun u => Real.log (f u)) (f' t / f t) s t := fun t ht =>
    (hd t ht).log (hpos t ht).ne'
  have hbd : ∀ t ∈ s, ‖f' t / f t‖ ≤ 2 * κ := fun t ht => by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hpos t ht), div_le_iff₀ (hpos t ht)]
    exact hb t ht
  have h := hs.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbd ha hb'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have h2 : Real.log (f b) ≤ 2 * κ * |b - a| + Real.log (f a) := by
    have := le_abs_self (Real.log (f b) - Real.log (f a)); linarith
  have h3 := Real.exp_le_exp.mpr h2
  rw [Real.exp_add, Real.exp_log (hpos b hb'), Real.exp_log (hpos a ha)] at h3
  have e : Real.exp (2 * κ * |b - a|) = Real.exp (κ * |b - a|) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : Real.sqrt (f b) ≤ Real.sqrt (Real.exp (κ * |b - a|) ^ 2 * f a) :=
    Real.sqrt_le_sqrt (by rw [← e]; exact h3)
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] at h4

/-- Interval form of `riemannianEDist_time`: the family of norms and the bound `|∂_τ g| ≤ 2κ g` are
only required for times in a convex set `s`; for `a, b ∈ s`, `d_b ≤ e^{κ|b−a|} d_a`. -/
theorem riemannianEDist_time_on (s : Set ℝ) (hs : Convex ℝ s)
    (n : ℝ → ∀ x : M, ENorm (TangentSpace I x))
    (g g' : ℝ → (x : M) → TangentSpace I x → ℝ) (κ : ℝ)
    (hn : ∀ τ ∈ s, ∀ x v, @enorm _ (n τ x) v = ENNReal.ofReal (Real.sqrt (g τ x v)))
    (hcase : ∀ x v, (∀ τ ∈ s, g τ x v = 0) ∨ (∀ τ ∈ s, 0 < g τ x v))
    (hd : ∀ τ ∈ s, ∀ x v, HasDerivWithinAt (fun u => g u x v) (g' τ x v) s τ)
    (hb : ∀ τ ∈ s, ∀ x v, |g' τ x v| ≤ 2 * κ * g τ x v) {a b : ℝ} (ha : a ∈ s) (hb' : b ∈ s)
    (p q : M) :
    (letI := n b; Manifold.riemannianEDist I p q)
      ≤ ENNReal.ofReal (Real.exp (κ * |b - a|)) * (letI := n a; Manifold.riemannianEDist I p q) := by
  refine riemannianEDist_le_mul (n a) (n b) _ (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
    (fun x v => ?_) p q
  rw [hn b hb', hn a ha]
  rcases hcase x v with h0 | hpos
  · simp [h0 a ha, h0 b hb']
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal
      (norm_growth_on s hs (fun u => g u x v) (fun u => g' u x v) κ hpos (fun t ht => hd t ht x v)
        (fun t ht => hb t ht x v) ha hb')

/-- From `e^{-x} d ≤ d' ≤ e^{x} d` with `x, d ≥ 0`: `|d' − d| ≤ (e^{x} − 1) d`. -/
theorem abs_sub_le_of_comparison (d d' x : ℝ) (hd : 0 ≤ d) (hx : 0 ≤ x)
    (hlo : Real.exp (-x) * d ≤ d') (hhi : d' ≤ Real.exp x * d) :
    |d' - d| ≤ (Real.exp x - 1) * d := by
  have h1 : 1 ≤ Real.exp x := Real.one_le_exp hx
  have h2 : 1 - Real.exp (-x) ≤ Real.exp x - 1 := by
    have h3 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h1), h4.le]
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right h2 hd]
  · linarith

/-- Lipschitz dependence of the distance on the time (first part of step M3): under the hypotheses
of `riemannianEDist_time_on` and finiteness of the distance at time `a`, for `a, b` in the convex
set of times, `|d_b − d_a| ≤ (e^{κ|b−a|} − 1) d_a` for the real distances (`κ ≥ 0`).  No derivative
of the distance with respect to the time is used. -/
theorem riemannianDist_lipschitz_time (s : Set ℝ) (hs : Convex ℝ s)
    (n : ℝ → ∀ x : M, ENorm (TangentSpace I x))
    (g g' : ℝ → (x : M) → TangentSpace I x → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hn : ∀ τ ∈ s, ∀ x v, @enorm _ (n τ x) v = ENNReal.ofReal (Real.sqrt (g τ x v)))
    (hcase : ∀ x v, (∀ τ ∈ s, g τ x v = 0) ∨ (∀ τ ∈ s, 0 < g τ x v))
    (hd : ∀ τ ∈ s, ∀ x v, HasDerivWithinAt (fun u => g u x v) (g' τ x v) s τ)
    (hb : ∀ τ ∈ s, ∀ x v, |g' τ x v| ≤ 2 * κ * g τ x v) {a b : ℝ} (ha : a ∈ s) (hb' : b ∈ s)
    (p q : M) (hfin : (letI := n a; Manifold.riemannianEDist I p q) ≠ ⊤) :
    |(letI := n b; Manifold.riemannianEDist I p q).toReal
        - (letI := n a; Manifold.riemannianEDist I p q).toReal|
      ≤ (Real.exp (κ * |b - a|) - 1) * (letI := n a; Manifold.riemannianEDist I p q).toReal := by
  have h1 := riemannianEDist_time_on s hs n g g' κ hn hcase hd hb ha hb' p q
  have h2 := riemannianEDist_time_on s hs n g g' κ hn hcase hd hb hb' ha p q
  rw [abs_sub_comm a b] at h2
  obtain ⟨_, hlo, hhi⟩ := real_comparison _ _ _ h1 h2 hfin
  exact abs_sub_le_of_comparison _ _ _ ENNReal.toReal_nonneg
    (mul_nonneg hκ (abs_nonneg _)) hlo hhi

/-- Finiteness for a bare family of norms from a reference metric (remark of the second session):
on a connected Riemannian manifold in Mathlib's sense, a family of norms `n` that is dominated by
`c` times the norm of the Riemannian bundle has finite Riemannian distances.  Without such a
hypothesis finiteness is false for bare `ENorm` families (the norm may be `⊤`).  The norm on the
right of `h` is the norm of the Riemannian bundle on the tangent space, not of the model space.  That two continuous
metrics on a compact manifold are comparable is NOT proven here. -/
theorem riemannianEDist_ne_top_of_le {M' : Type*} [PseudoEMetricSpace M'] [ChartedSpace H M']
    [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)] [IsRiemannianManifold I M']
    [PreconnectedSpace M'] (n : ∀ x : M', ENorm (TangentSpace I x)) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hc : c ≠ ⊤)
    (h : ∀ (x : M') (v : TangentSpace I x),
      @enorm _ (n x) v ≤ c * @enorm _ SeminormedAddGroup.toContinuousENorm.toENorm v) (x y : M') :
    (letI := n; Manifold.riemannianEDist I x y) ≠ ⊤ := by
  have h1 := riemannianEDist_le_mul (I := I) (M := M') (fun x => SeminormedAddGroup.toContinuousENorm.toENorm) n c hc0 hc h x y
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hc (riemannianEDist_ne_top x y)) h1

/-! ### The kernel at two times (Step 1 of `prop:dotLN-diff` as one statement)

`mvt_bound` and `kernel_step_one` are copied from the seventh file (`TimeAppendix` in
`CorrelationsToGeometryReal3.lean`, state of 23 November 2026, 1082 statements), which this file does
not import; if one copy is changed, the other is not. -/

theorem mvt_bound (h h' : ℝ → ℝ) (a b M : ℝ) (hab : a < b)
    (hd : ∀ s, HasDerivAt h (h' s) s) (hM : ∀ s, a < s → s < b → |h' s| ≤ M) :
    |h b - h a| ≤ M * (b - a) := by
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h h' hab
    (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
  have hba : 0 < b - a := sub_pos.mpr hab
  have e : h b - h a = h' c * (b - a) := by
    rw [hslope]; field_simp
  rw [e, abs_mul, abs_of_pos hba]
  exact mul_le_mul_of_nonneg_right (hM c hc.1 hc.2) hba.le

theorem kernel_step_one (h h' : ℝ → ℝ) (A d d' x : ℝ) (hA : 0 ≤ A) (hd0 : 0 < d)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hder : ∀ s, HasDerivAt h (h' s) s) (hbd : ∀ s, 0 ≤ s → |h' s| ≤ A * Real.exp (-s))
    (hlo : d * Real.exp (-x) ≤ d') (hhi : d' ≤ d * Real.exp x) :
    |h d' - h d| ≤ 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) := by
  have hexp_hi : Real.exp x - 1 ≤ 2 * x := by
    have := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg hx0]; exact hx1)
    rw [abs_of_nonneg hx0] at this
    exact le_trans (le_abs_self _) this
  have hexp_lo : 1 - Real.exp (-x) ≤ 2 * x := by
    have := Real.add_one_le_exp (-x); linarith
  have he1 : Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hfloor : d * Real.exp (-1) ≤ d * Real.exp (-x) := mul_le_mul_of_nonneg_left he1 hd0.le
  have hfloor' : d * Real.exp (-1) ≤ d := by
    have : Real.exp (-1) ≤ 1 := by
      have := Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0); simpa using this
    nlinarith
  have hE : 0 ≤ Real.exp (-(d * Real.exp (-1))) := (Real.exp_pos _).le
  -- bound of the derivative on the segment
  have hseg : ∀ s, d * Real.exp (-1) ≤ s → |h' s| ≤ A * Real.exp (-(d * Real.exp (-1))) := by
    intro s hs
    have hs0 : 0 ≤ s := le_trans (by positivity) hs
    refine le_trans (hbd s hs0) (mul_le_mul_of_nonneg_left ?_ hA)
    exact Real.exp_le_exp.mpr (by linarith)
  have hgap_hi : d' - d ≤ 2 * x * d := by nlinarith
  have hgap_lo : d - d' ≤ 2 * x * d := by nlinarith
  rcases lt_trichotomy d d' with hlt | heq | hgt
  · have := mvt_bound h h' d d' (A * Real.exp (-(d * Real.exp (-1)))) hlt hder
      (fun s hs1 _ => hseg s (by linarith))
    have hM : 0 ≤ A * Real.exp (-(d * Real.exp (-1))) := mul_nonneg hA hE
    have h2 : A * Real.exp (-(d * Real.exp (-1))) * (d' - d)
        ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) :=
      mul_le_mul_of_nonneg_left hgap_hi hM
    calc |h d' - h d| ≤ A * Real.exp (-(d * Real.exp (-1))) * (d' - d) := this
      _ ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) := h2
      _ = 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) := by ring
  · have hnn : 0 ≤ 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hx0) hA) hd0.le) hE
    rw [← heq, sub_self, abs_zero]; exact hnn
  · have := mvt_bound h h' d' d (A * Real.exp (-(d * Real.exp (-1)))) hgt hder
      (fun s hs1 _ => hseg s (by linarith))
    have hM : 0 ≤ A * Real.exp (-(d * Real.exp (-1))) := mul_nonneg hA hE
    have h2 : A * Real.exp (-(d * Real.exp (-1))) * (d - d')
        ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) :=
      mul_le_mul_of_nonneg_left hgap_lo hM
    rw [abs_sub_comm]
    calc |h d - h d'| ≤ A * Real.exp (-(d * Real.exp (-1))) * (d - d') := this
      _ ≤ A * Real.exp (-(d * Real.exp (-1))) * (2 * x * d) := h2
      _ = 2 * x * A * d * Real.exp (-(d * Real.exp (-1))) := by ring

/-- Step 1 of `prop:dotLN-diff` as one statement: for a time-dependent family of norms as in
`riemannianEDist_time_on`, two times `a, b` in the convex set with `κ|b−a| ≤ 1`, a finite positive
distance `d_a(p,q)` at time `a`, a scale `ξ > 0` and a profile `h` with `|h'(s)| ≤ A e^{-s}`,
`|h(d_b/ξ) − h(d_a/ξ)| ≤ 2 κ|b−a| · A (d_a/ξ) e^{-(d_a/ξ)/e}`, i.e. `|Δ_η K| ≤ 2κ k_*(d/ξ)` with
`k_*(s) = A s e^{-s/e}` after division by `|η| = |b−a|`. -/
theorem kernel_two_times (s : Set ℝ) (hs : Convex ℝ s)
    (n : ℝ → ∀ x : M, ENorm (TangentSpace I x))
    (g g' : ℝ → (x : M) → TangentSpace I x → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hn : ∀ τ ∈ s, ∀ x v, @enorm _ (n τ x) v = ENNReal.ofReal (Real.sqrt (g τ x v)))
    (hcase : ∀ x v, (∀ τ ∈ s, g τ x v = 0) ∨ (∀ τ ∈ s, 0 < g τ x v))
    (hd : ∀ τ ∈ s, ∀ x v, HasDerivWithinAt (fun u => g u x v) (g' τ x v) s τ)
    (hb : ∀ τ ∈ s, ∀ x v, |g' τ x v| ≤ 2 * κ * g τ x v) {a b : ℝ} (ha : a ∈ s) (hb' : b ∈ s)
    (hab : κ * |b - a| ≤ 1) (p q : M)
    (hfin : (letI := n a; Manifold.riemannianEDist I p q) ≠ ⊤)
    (hpos : 0 < (letI := n a; Manifold.riemannianEDist I p q).toReal)
    (h h' : ℝ → ℝ) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) :
    |h ((letI := n b; Manifold.riemannianEDist I p q).toReal / ξ)
        - h ((letI := n a; Manifold.riemannianEDist I p q).toReal / ξ)|
      ≤ 2 * (κ * |b - a|) * A * ((letI := n a; Manifold.riemannianEDist I p q).toReal / ξ)
        * Real.exp (-((letI := n a; Manifold.riemannianEDist I p q).toReal / ξ * Real.exp (-1))) := by
  have h1 := riemannianEDist_time_on s hs n g g' κ hn hcase hd hb ha hb' p q
  have h2 := riemannianEDist_time_on s hs n g g' κ hn hcase hd hb hb' ha p q
  rw [abs_sub_comm a b] at h2
  obtain ⟨_, hlo, hhi⟩ := real_comparison _ _ _ h1 h2 hfin
  refine kernel_step_one h h' A _ _ (κ * |b - a|) hA (div_pos hpos hξ)
    (mul_nonneg hκ (abs_nonneg _)) hab hder hbd ?_ ?_
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hξ, mul_comm]; exact hlo
  · rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hξ, mul_comm]; exact hhi

/-- The case of distance zero at time `a`: then the distance at time `b` is zero as well, and the
kernel does not change. -/
theorem kernel_two_times_zero (s : Set ℝ) (hs : Convex ℝ s)
    (n : ℝ → ∀ x : M, ENorm (TangentSpace I x))
    (g g' : ℝ → (x : M) → TangentSpace I x → ℝ) (κ : ℝ)
    (hn : ∀ τ ∈ s, ∀ x v, @enorm _ (n τ x) v = ENNReal.ofReal (Real.sqrt (g τ x v)))
    (hcase : ∀ x v, (∀ τ ∈ s, g τ x v = 0) ∨ (∀ τ ∈ s, 0 < g τ x v))
    (hd : ∀ τ ∈ s, ∀ x v, HasDerivWithinAt (fun u => g u x v) (g' τ x v) s τ)
    (hb : ∀ τ ∈ s, ∀ x v, |g' τ x v| ≤ 2 * κ * g τ x v) {a b : ℝ} (ha : a ∈ s) (hb' : b ∈ s)
    (p q : M) (hfin : (letI := n a; Manifold.riemannianEDist I p q) ≠ ⊤)
    (hzero : (letI := n a; Manifold.riemannianEDist I p q).toReal = 0) (h : ℝ → ℝ) (ξ : ℝ) :
    h ((letI := n b; Manifold.riemannianEDist I p q).toReal / ξ)
      = h ((letI := n a; Manifold.riemannianEDist I p q).toReal / ξ) := by
  have h1 := riemannianEDist_time_on s hs n g g' κ hn hcase hd hb ha hb' p q
  have h2 := riemannianEDist_time_on s hs n g g' κ hn hcase hd hb hb' ha p q
  rw [abs_sub_comm a b] at h2
  obtain ⟨_, _, hhi⟩ := real_comparison _ _ _ h1 h2 hfin
  rw [hzero, mul_zero] at hhi
  have : (letI := n b; Manifold.riemannianEDist I p q).toReal = 0 :=
    le_antisymm hhi ENNReal.toReal_nonneg
  rw [this, hzero]


/-! ### Comparability of two continuous metrics on a compact base (block A109)

General vector-bundle form: `V` is a continuous Riemannian bundle (Mathlib's
`IsContinuousRiemannianBundle`), `g` a second family of bilinear forms on the fibres that depends
continuously on the base point (as a section of the hom bundle).  On a compact base `g` is bounded
by a constant times the bundle norm, and if `g` is positive definite and the model fibre is
finite-dimensional, it is bounded below by a positive constant times the bundle norm. -/

section Comparability

open Filter ContinuousLinearMap

/- The scoped instance `NormedAddCommGroup` of `RiemannianBundle` (active because the file opens
`Bundle`) makes instance search on spaces of bilinear maps time out in this general section; it is
not needed here (the fibres carry their own norm), so it is switched off locally. -/
attribute [-instance]
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal

/-- A property `P y C`, monotone in the constant `C`, that holds locally with some constant, holds
globally with one constant on a compact space. -/
theorem compact_bound {X : Type*} [TopologicalSpace X] [CompactSpace X] (P : X → ℝ → Prop)
    (hmono : ∀ y C C', C ≤ C' → P y C → P y C') (hloc : ∀ x, ∃ C, ∀ᶠ y in 𝓝 x, P y C) :
    ∃ C, ∀ y, P y C := by
  choose C hC using hloc
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover (fun x => {y | P y (C x)}) hC
  refine ⟨∑ x ∈ t, |C x|, fun y => ?_⟩
  have hy : y ∈ ⋃ x ∈ t, {y | P y (C x)} := by rw [ht]; trivial
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hPy⟩ := hy
  exact hmono y _ _ ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg (C i)) hx)) hPy

/-- A positive definite continuous bilinear form on a finite-dimensional space is bounded below by
a positive multiple of the squared norm. -/
theorem quad_lower {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (b : F →L[ℝ] F →L[ℝ] ℝ) (hb : ∀ w, w ≠ 0 → 0 < b w w) :
    ∃ μ > 0, ∀ w, μ * ‖w‖ ^ 2 ≤ b w w := by
  have hq : Continuous fun w => b w w := by fun_prop
  have hne : ∀ w ∈ Metric.sphere (0 : F) 1, b w w ≠ 0 := fun w hw => by
    have : w ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw; exact zero_ne_one hw
    exact (hb w this).ne'
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : F) 1).exists_bound_of_continuousOn
    (hq.continuousOn.inv₀ hne)
  refine ⟨(max K 1)⁻¹, by positivity, fun w => ?_⟩
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set u : F := ‖w‖⁻¹ • w with hu
  have hus : u ∈ Metric.sphere (0 : F) 1 := by
    rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hu0 : u ≠ 0 := by
    intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hus; exact zero_ne_one hus
  have hpos := hb u hu0
  have h1 : (b u u)⁻¹ ≤ max K 1 := by
    have := hK u hus
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)] at this
    exact this.trans (le_max_left _ _)
  have h2 : (max K 1)⁻¹ ≤ b u u := inv_le_of_inv_le₀ hpos h1
  have hw' : w = ‖w‖ • u := by rw [hu, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have h3 : b w w = ‖w‖ ^ 2 * b u u := by
    calc b w w = b (‖w‖ • u) (‖w‖ • u) := by rw [← hw']
      _ = ‖w‖ ^ 2 * b u u := by simp only [map_smul, smul_apply, smul_eq_mul]; ring
  rw [h3]
  have := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖w‖)
  linarith

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

/-- A bilinear form on the fibre over `y` read in the trivialisation at `x`. -/
theorem bilin_inCoordinates (g : ∀ x, V x →L[ℝ] V x →L[ℝ] ℝ) (x y : B)
    (hy : y ∈ (trivializationAt F V x).baseSet) (v w : V y) :
    g y v w = inCoordinates F V (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] ℝ) x y x y (g y)
      ((trivializationAt F V x).continuousLinearMapAt ℝ y v)
      ((trivializationAt F V x).continuousLinearMapAt ℝ y w) := by
  rw [inCoordinates_apply_eq₂ hy hy (Set.mem_univ _)]
  have A : ∀ u : V y,
      ((trivializationAt F V x).symm y) ((trivializationAt F V x).linearMapAt ℝ y u) = u := by
    intro u
    convert ((trivializationAt F V x).continuousLinearEquivAt ℝ _ hy).symm_apply_apply u
    rw [Trivialization.coe_continuousLinearEquivAt_eq _ hy]
    rfl
  simp [A]

theorem triv_symm_apply (x y : B) (hy : y ∈ (trivializationAt F V x).baseSet) (u : V y) :
    (trivializationAt F V x).symmL ℝ y ((trivializationAt F V x).continuousLinearMapAt ℝ y u)
      = u := by
  simp only [Trivialization.symmL_apply, Trivialization.continuousLinearMapAt_apply]
  convert ((trivializationAt F V x).continuousLinearEquivAt ℝ _ hy).symm_apply_apply u
  rw [Trivialization.coe_continuousLinearEquivAt_eq _ hy]
  rfl

theorem triv_apply_symm (x y : B) (hy : y ∈ (trivializationAt F V x).baseSet) (w : F) :
    (trivializationAt F V x).continuousLinearMapAt ℝ y ((trivializationAt F V x).symmL ℝ y w)
      = w := by
  simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symmL_apply]
  convert ((trivializationAt F V x).continuousLinearEquivAt ℝ _ hy).apply_symm_apply w
  rw [Trivialization.coe_continuousLinearEquivAt_eq _ hy]
  rfl

variable [IsContinuousRiemannianBundle F V]

/-- Local upper bound of a continuous family of bilinear forms against the bundle norm. -/
theorem local_bilin_upper (g : ∀ x, V x →L[ℝ] V x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x))) (x : B) :
    ∃ C, ∀ᶠ y in 𝓝 x, ∀ v w : V y, |g y v w| ≤ C * ‖v‖ * ‖w‖ := by
  obtain ⟨C, hC0, hC⟩ := eventually_norm_trivializationAt_lt F V x
  let g' : B → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F V (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] ℝ) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := hg.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have hev : ∀ᶠ y in 𝓝 x, dist (g' y) (g' x) < 1 :=
    hg' (Metric.ball_mem_nhds (g' x) one_pos)
  refine ⟨(‖g' x‖ + 1) * C * C, ?_⟩
  filter_upwards [hC, hev, (trivializationAt F V x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' x)] with y hy1 hy2 hy3 v w
  rw [bilin_inCoordinates g x y hy3 v w]
  set a := (trivializationAt F V x).continuousLinearMapAt ℝ y v with ha
  set b := (trivializationAt F V x).continuousLinearMapAt ℝ y w with hb
  have h1 : ‖a‖ ≤ C * ‖v‖ :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hy1.le (norm_nonneg _))
  have h2 : ‖b‖ ≤ C * ‖w‖ :=
    (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hy1.le (norm_nonneg _))
  have hd : ‖g' y - g' x‖ ≤ 1 := by
    have h := hy2.le
    rw [dist_eq_norm (E := F →L[ℝ] F →L[ℝ] ℝ)] at h
    exact h
  have e1 : g' y a b = (g' y - g' x) a b + g' x a b := by simp
  have e2 : |(g' y - g' x) a b| ≤ ‖g' y - g' x‖ * ‖a‖ * ‖b‖ := by
    rw [← Real.norm_eq_abs]; exact le_opNorm₂ _ _ _
  have e3 : |g' x a b| ≤ ‖g' x‖ * ‖a‖ * ‖b‖ := by
    rw [← Real.norm_eq_abs]; exact le_opNorm₂ _ _ _
  have e4 : ‖g' y - g' x‖ * ‖a‖ * ‖b‖ ≤ 1 * ‖a‖ * ‖b‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (norm_nonneg _)) (norm_nonneg _)
  have hab : ‖a‖ * ‖b‖ ≤ (C * ‖v‖) * (C * ‖w‖) :=
    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hg0 : 0 ≤ ‖g' x‖ + 1 := by positivity
  have e5 := mul_le_mul_of_nonneg_left hab hg0
  rw [e1]
  calc |(g' y - g' x) a b + g' x a b| ≤ |(g' y - g' x) a b| + |g' x a b| := abs_add_le _ _
    _ ≤ (‖g' x‖ + 1) * (‖a‖ * ‖b‖) := by nlinarith
    _ ≤ (‖g' x‖ + 1) * ((C * ‖v‖) * (C * ‖w‖)) := e5
    _ = (‖g' x‖ + 1) * C * C * ‖v‖ * ‖w‖ := by ring

/-- COMPARABILITY, upper half: on a compact base, a continuous family of bilinear forms on the
fibres of a continuous Riemannian bundle is bounded by a constant times the bundle norm. -/
theorem bilin_upper [CompactSpace B] (g : ∀ x, V x →L[ℝ] V x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x))) :
    ∃ C, ∀ y (v w : V y), |g y v w| ≤ C * ‖v‖ * ‖w‖ :=
  compact_bound (fun y C => ∀ v w : V y, |g y v w| ≤ C * ‖v‖ * ‖w‖)
    (fun y C C' hCC' h v w => (h v w).trans (by gcongr)) (local_bilin_upper g hg)

/-- Local lower bound for a positive definite continuous family (finite-dimensional fibres). -/
theorem local_bilin_lower [FiniteDimensional ℝ F] (g : ∀ x, V x →L[ℝ] V x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x)))
    (hpos : ∀ y (v : V y), v ≠ 0 → 0 < g y v v) (x : B) :
    ∃ K, ∀ᶠ y in 𝓝 x, ∀ v : V y, ‖v‖ ^ 2 ≤ K * g y v v := by
  have h'x : x ∈ (trivializationAt F V x).baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  obtain ⟨C, hC0, hC⟩ := eventually_norm_symmL_trivializationAt_lt F V x
  let g' : B → F →L[ℝ] F →L[ℝ] ℝ := fun y ↦
    inCoordinates F V (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] ℝ) x y x y (g y)
  have hg' : ContinuousAt g' x := by
    have W := hg.continuousAt (x := x)
    simp only [continuousAt_hom_bundle] at W
    exact W.2
  have hbpos : ∀ w : F, w ≠ 0 → 0 < g' x w w := by
    intro w hw
    have e := bilin_inCoordinates g x x h'x ((trivializationAt F V x).symmL ℝ x w)
      ((trivializationAt F V x).symmL ℝ x w)
    rw [triv_apply_symm x x h'x] at e
    have hne : (trivializationAt F V x).symmL ℝ x w ≠ 0 := by
      intro h0; apply hw
      have := triv_apply_symm (V := V) x x h'x w
      rw [h0, map_zero] at this; exact this.symm
    have := hpos x _ hne
    rw [e] at this; exact this
  obtain ⟨μ, hμ, hμb⟩ := quad_lower (g' x) hbpos
  have hev : ∀ᶠ y in 𝓝 x, dist (g' y) (g' x) < μ / 2 :=
    hg' (Metric.ball_mem_nhds (g' x) (by positivity))
  refine ⟨C ^ 2 * (2 / μ), ?_⟩
  filter_upwards [hC, hev, (trivializationAt F V x).open_baseSet.mem_nhds h'x] with y hy1 hy2 hy3 v
  set w := (trivializationAt F V x).continuousLinearMapAt ℝ y v with hw
  have hv : ‖v‖ ≤ C * ‖w‖ := by
    have e := triv_symm_apply x y hy3 v
    calc ‖v‖ = ‖(trivializationAt F V x).symmL ℝ y w‖ := by rw [e]
      _ ≤ ‖(trivializationAt F V x).symmL ℝ y‖ * ‖w‖ := le_opNorm _ _
      _ ≤ C * ‖w‖ := mul_le_mul_of_nonneg_right hy1.le (norm_nonneg _)
  have hgv : g y v v = g' y w w := bilin_inCoordinates g x y hy3 v v
  have hd : ‖g' y - g' x‖ ≤ μ / 2 := by
    have h := hy2.le
    rw [dist_eq_norm (E := F →L[ℝ] F →L[ℝ] ℝ)] at h
    exact h
  have hlow : μ / 2 * ‖w‖ ^ 2 ≤ g' y w w := by
    have e1 : g' y w w = (g' y - g' x) w w + g' x w w := by simp
    have e2 : |(g' y - g' x) w w| ≤ ‖g' y - g' x‖ * ‖w‖ * ‖w‖ := by
      rw [← Real.norm_eq_abs]; exact le_opNorm₂ _ _ _
    have e3 : ‖g' y - g' x‖ * ‖w‖ * ‖w‖ ≤ μ / 2 * ‖w‖ ^ 2 := by
      rw [pow_two, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
        (norm_nonneg _)
    have := neg_abs_le ((g' y - g' x) w w)
    have := hμb w
    linarith
  rw [hgv]
  have hv2 : ‖v‖ ^ 2 ≤ C ^ 2 * ‖w‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hv 2
  have hw2 : ‖w‖ ^ 2 ≤ 2 / μ * g' y w w := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hμ]; linarith
  calc ‖v‖ ^ 2 ≤ C ^ 2 * ‖w‖ ^ 2 := hv2
    _ ≤ C ^ 2 * (2 / μ * g' y w w) := by gcongr
    _ = C ^ 2 * (2 / μ) * g' y w w := by ring

/-- COMPARABILITY, lower half: on a compact base, with finite-dimensional model fibre, a positive
definite continuous family of bilinear forms is bounded below by a positive constant times the
squared bundle norm. -/
theorem bilin_lower [CompactSpace B] [FiniteDimensional ℝ F] (g : ∀ x, V x →L[ℝ] V x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (g x)))
    (hpos : ∀ y (v : V y), v ≠ 0 → 0 < g y v v) :
    ∃ c > 0, ∀ y (v : V y), c * ‖v‖ ^ 2 ≤ g y v v := by
  have hnn : ∀ y (v : V y), 0 ≤ g y v v := fun y v => by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hpos y v hv).le
  obtain ⟨K, hK⟩ := compact_bound (fun y K => ∀ v : V y, ‖v‖ ^ 2 ≤ K * g y v v)
    (fun y K K' hKK' h v => (h v).trans (mul_le_mul_of_nonneg_right hKK' (hnn y v)))
    (local_bilin_lower g hg hpos)
  refine ⟨(max K 1)⁻¹, by positivity, fun y v => ?_⟩
  have h1 : ‖v‖ ^ 2 ≤ max K 1 * g y v v :=
    (hK y v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn y v))
  rw [inv_mul_le_iff₀ (by positivity)]
  exact h1

end Comparability

/-! ### The tangent bundle: a second continuous metric against the Riemannian bundle (block A109)

`quadENorm g` is the family of norms `‖v‖_g = (g_x(v,v))^{1/2}` of a family of bilinear forms
`g` on the tangent spaces.  On a compact manifold whose tangent bundle is a continuous Riemannian
bundle, a continuous `g` (as a section of the hom bundle) is dominated by a multiple of the bundle
norm; if `g` is positive definite and the model space is finite-dimensional, it also dominates a
multiple of the bundle norm.  Hence the hypothesis of `riemannianEDist_ne_top_of_le` and of the
two-sided comparison hold with explicit (non-computed) constants. -/

section TangentComparability

/-- The family of extended norms `v ↦ (g_x(v,v))^{1/2}` defined by bilinear forms on the tangent
spaces (the square root of a negative number is `0` in Mathlib). -/
def quadENorm (g : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    ENorm (TangentSpace I x) :=
  ⟨fun v => ENNReal.ofReal (Real.sqrt (g x v v))⟩

variable {M' : Type*} [PseudoEMetricSpace M'] [ChartedSpace H M'] [IsManifold I 1 M']
  [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun (x : M') ↦ TangentSpace I x)]

/-- Upper comparability on a compact manifold: `‖v‖_g ≤ c ‖v‖` with `0 < c < ∞`. -/
theorem quadENorm_le_bundle [CompactSpace M']
    (g : ∀ x : M', TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g x))) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (x : M') (v : TangentSpace I x),
      @enorm _ (quadENorm g x) v ≤ c * @enorm _ SeminormedAddGroup.toContinuousENorm.toENorm v := by
  obtain ⟨C, hC⟩ := bilin_upper (V := fun x : M' ↦ TangentSpace I x) g hg
  refine ⟨ENNReal.ofReal (Real.sqrt (max C 1)), by simp, ENNReal.ofReal_ne_top, fun x v => ?_⟩
  show ENNReal.ofReal (Real.sqrt (g x v v)) ≤ _
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have h1 : g x v v ≤ max C 1 * ‖v‖ ^ 2 := by
    have := (le_abs_self _).trans (hC x v v)
    have h2 : C * ‖v‖ * ‖v‖ ≤ max C 1 * ‖v‖ * ‖v‖ := by gcongr; exact le_max_left _ _
    nlinarith
  calc Real.sqrt (g x v v) ≤ Real.sqrt (max C 1 * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (max C 1) * ‖v‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- Lower comparability on a compact manifold with finite-dimensional model space, for positive
definite `g`: `‖v‖ ≤ c ‖v‖_g` with `0 < c < ∞`. -/
theorem bundle_le_quadENorm [CompactSpace M'] [FiniteDimensional ℝ E]
    (g : ∀ x : M', TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g x)))
    (hpos : ∀ (x : M') (v : TangentSpace I x), v ≠ 0 → 0 < g x v v) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (x : M') (v : TangentSpace I x),
      @enorm _ SeminormedAddGroup.toContinuousENorm.toENorm v ≤ c * @enorm _ (quadENorm g x) v := by
  obtain ⟨c, hc, hcb⟩ := bilin_lower (V := fun x : M' ↦ TangentSpace I x) g hg hpos
  refine ⟨ENNReal.ofReal (Real.sqrt c⁻¹), by simp [hc], ENNReal.ofReal_ne_top, fun x v => ?_⟩
  show _ ≤ _ * ENNReal.ofReal (Real.sqrt (g x v v))
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.sqrt_mul (by positivity)]
  have h1 : ‖v‖ ^ 2 ≤ c⁻¹ * g x v v := by
    rw [le_inv_mul_iff₀ hc]; exact hcb x v
  calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (c⁻¹ * g x v v) := Real.sqrt_le_sqrt h1

/-- Finiteness of the distance of a second continuous metric on a compact connected Riemannian
manifold (Mathlib's `IsRiemannianManifold`). -/
theorem quadENorm_riemannianEDist_ne_top [CompactSpace M'] [PreconnectedSpace M']
    [IsRiemannianManifold I M']
    (g : ∀ x : M', TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g x))) (x y : M') :
    (letI := quadENorm g; Manifold.riemannianEDist I x y) ≠ ⊤ := by
  obtain ⟨c, hc0, hc, h⟩ := quadENorm_le_bundle g hg
  exact riemannianEDist_ne_top_of_le (quadENorm g) c hc0 hc h x y

/-- Two-sided comparison of the distances: `d_g ≤ c₁ d` and `d ≤ c₂ d_g` with `0 < c₁, c₂ < ∞`,
for a positive definite continuous `g` on a compact manifold with finite-dimensional model. -/
theorem quadENorm_riemannianEDist_comparable [CompactSpace M'] [FiniteDimensional ℝ E]
    (g : ∀ x : M', TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hg : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (g x)))
    (hpos : ∀ (x : M') (v : TangentSpace I x), v ≠ 0 → 0 < g x v v) :
    ∃ c₁ c₂ : ℝ≥0∞, c₁ ≠ 0 ∧ c₁ ≠ ⊤ ∧ c₂ ≠ 0 ∧ c₂ ≠ ⊤ ∧ ∀ x y : M',
      (letI := quadENorm g; Manifold.riemannianEDist I x y)
          ≤ c₁ * Manifold.riemannianEDist I x y ∧
      Manifold.riemannianEDist I x y
          ≤ c₂ * (letI := quadENorm g; Manifold.riemannianEDist I x y) := by
  obtain ⟨c₁, h10, h1t, h1⟩ := quadENorm_le_bundle g hg
  obtain ⟨c₂, h20, h2t, h2⟩ := bundle_le_quadENorm g hg hpos
  refine ⟨c₁, c₂, h10, h1t, h20, h2t, fun x y => ⟨?_, ?_⟩⟩
  · exact riemannianEDist_le_mul (I := I) (M := M')
      (fun x => SeminormedAddGroup.toContinuousENorm.toENorm) (quadENorm g) c₁ h10 h1t h1 x y
  · exact riemannianEDist_le_mul (I := I) (M := M')
      (quadENorm g) (fun x => SeminormedAddGroup.toContinuousENorm.toENorm) c₂ h20 h2t h2 x y

end TangentComparability

/-! ### A time-dependent metric as an object (block A109)

`TimeMetric I M s` packages a family `τ ↦ g_τ` of positive definite bilinear forms on the tangent
spaces, for times `τ` in a convex set `s`, with a derivative in `τ` of the quadratic forms and the
bound `|∂_τ g_τ(v,v)| ≤ 2κ g_τ(v,v)` (`∂_τ h_τ = 2K_τ`, `|K_τ(v,v)| ≤ κ h_τ(v,v)`).  The hypotheses
`hn`, `hcase` of the earlier statements hold automatically for it. -/

variable (I M) in
/-- A time-dependent family of positive definite bilinear forms on the tangent spaces with
`|∂_τ g_τ(v,v)| ≤ 2κ g_τ(v,v)` on a convex set of times.  No continuity in the base point is
required here (it enters only for finiteness, `TimeMetric.riemannianEDist_ne_top`). -/
structure TimeMetric (s : Set ℝ) where
  /-- The metric at time `τ`. -/
  g : ℝ → ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- The time derivative of the quadratic form `τ ↦ g τ x v v`. -/
  g' : ℝ → (x : M) → TangentSpace I x → ℝ
  /-- The constant in `|∂_τ g| ≤ 2κ g`. -/
  κ : ℝ
  κ_nonneg : 0 ≤ κ
  convex : Convex ℝ s
  pos : ∀ τ ∈ s, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < g τ x v v
  deriv : ∀ τ ∈ s, ∀ (x : M) (v : TangentSpace I x),
    HasDerivWithinAt (fun u => g u x v v) (g' τ x v) s τ
  bound : ∀ τ ∈ s, ∀ (x : M) (v : TangentSpace I x), |g' τ x v| ≤ 2 * κ * g τ x v v

namespace TimeMetric

variable {s : Set ℝ} (G : TimeMetric I M s)

/-- The family of norms at time `τ`. -/
def norms (τ : ℝ) (x : M) : ENorm (TangentSpace I x) := quadENorm (G.g τ) x

theorem hcase (x : M) (v : TangentSpace I x) :
    (∀ τ ∈ s, G.g τ x v v = 0) ∨ (∀ τ ∈ s, 0 < G.g τ x v v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · left; intro τ _; simp
  · right; intro τ hτ; exact G.pos τ hτ x v hv

/-- Comparison of the distances at two times: `d_b ≤ e^{κ|b−a|} d_a`. -/
theorem riemannianEDist_le {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (p q : M) :
    (letI := G.norms b; Manifold.riemannianEDist I p q)
      ≤ ENNReal.ofReal (Real.exp (G.κ * |b - a|))
          * (letI := G.norms a; Manifold.riemannianEDist I p q) :=
  riemannianEDist_time_on s G.convex G.norms (fun τ x v => G.g τ x v v) G.g' G.κ
    (fun _ _ _ _ => rfl) G.hcase G.deriv G.bound ha hb p q

/-- `riemannianDist_lipschitz_time` for a `TimeMetric`. -/
theorem lipschitz {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (p q : M)
    (hfin : (letI := G.norms a; Manifold.riemannianEDist I p q) ≠ ⊤) :
    |(letI := G.norms b; Manifold.riemannianEDist I p q).toReal
        - (letI := G.norms a; Manifold.riemannianEDist I p q).toReal|
      ≤ (Real.exp (G.κ * |b - a|) - 1) * (letI := G.norms a; Manifold.riemannianEDist I p q).toReal :=
  riemannianDist_lipschitz_time s G.convex G.norms (fun τ x v => G.g τ x v v) G.g' G.κ G.κ_nonneg
    (fun _ _ _ _ => rfl) G.hcase G.deriv G.bound ha hb p q hfin

/-- `kernel_two_times` for a `TimeMetric`. -/
theorem kernel {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (p q : M)
    (hfin : (letI := G.norms a; Manifold.riemannianEDist I p q) ≠ ⊤)
    (hpos : 0 < (letI := G.norms a; Manifold.riemannianEDist I p q).toReal)
    (h h' : ℝ → ℝ) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) :
    |h ((letI := G.norms b; Manifold.riemannianEDist I p q).toReal / ξ)
        - h ((letI := G.norms a; Manifold.riemannianEDist I p q).toReal / ξ)|
      ≤ 2 * (G.κ * |b - a|) * A * ((letI := G.norms a; Manifold.riemannianEDist I p q).toReal / ξ)
        * Real.exp (-((letI := G.norms a; Manifold.riemannianEDist I p q).toReal / ξ
            * Real.exp (-1))) :=
  kernel_two_times s G.convex G.norms (fun τ x v => G.g τ x v v) G.g' G.κ G.κ_nonneg
    (fun _ _ _ _ => rfl) G.hcase G.deriv G.bound ha hb hab p q hfin hpos h h' A ξ hA hξ hder hbd

end TimeMetric

/-- Finiteness at all times: on a compact connected Riemannian manifold (Mathlib's
`IsRiemannianManifold`, continuous Riemannian tangent bundle), if the metric of a `TimeMetric` is
continuous in the base point at one time `a ∈ s`, then all its distances are finite at every time
`b ∈ s`. -/
theorem TimeMetric.riemannianEDist_ne_top {M' : Type*} [PseudoEMetricSpace M'] [ChartedSpace H M']
    [IsManifold I 1 M'] [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun (x : M') ↦ TangentSpace I x)]
    [IsRiemannianManifold I M'] [CompactSpace M'] [PreconnectedSpace M']
    {s : Set ℝ} (G : TimeMetric I M' s) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x))) (p q : M') :
    (letI := G.norms b; Manifold.riemannianEDist I p q) ≠ ⊤ := by
  have hfa : (letI := G.norms a; Manifold.riemannianEDist I p q) ≠ ⊤ :=
    quadENorm_riemannianEDist_ne_top (G.g a) hcont p q
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfa)
    (G.riemannianEDist_le ha hb p q)


/-! ### Metric variation of a `C¹` path against its Riemannian length (block A112)

On a manifold satisfying Mathlib's `IsRiemannianManifold` (the extended distance of the space is the
infimum of the lengths of `C¹` paths), the metric variation `eVariationOn γ (Icc a b)` of a `C¹`
path (supremum over partitions of the sums of distances) is at most its Riemannian length
`pathELength I γ a b`.  Consequences: finite length gives bounded variation in the Riemannian
distance, and a path whose length is within `ε` of the distance of its endpoints is `ε`-almost
minimising on every subinterval, in length and in variation.  NOT proven here: the converse
`pathELength ≤ eVariationOn` (needs a lower comparison of the Riemannian distance with the chart
distance with constants tending to `1`, which Mathlib does not contain), and the existence of a
minimising curve. -/

section Variation

variable {M' : Type*} [PseudoEMetricSpace M'] [ChartedSpace H M']
  [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)] [IsRiemannianManifold I M']

/-- The distance of two points of a `C¹` path is at most the length of the path between them. -/
theorem edist_le_pathELength {γ : ℝ → M'} {a b s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    edist (γ s) (γ t) ≤ pathELength I γ s t := by
  rw [IsRiemannianManifold.out (I := I)]
  exact riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc hs ht)) rfl rfl hst

/-- The sum of the distances along a monotone sequence of times is at most the length between the
first and the last time. -/
theorem sum_edist_le_pathELength {γ : ℝ → M'} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) {u : ℕ → ℝ} (hu : Monotone u)
    (us : ∀ i, u i ∈ Icc a b) (n : ℕ) :
    ∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i)) ≤ pathELength I γ (u 0) (u n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← pathELength_add (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]
    refine add_le_add ih ?_
    rw [edist_comm]
    exact edist_le_pathELength hγ (us n).1 (hu (Nat.le_succ n)) (us (n + 1)).2

/-- STAGE (1): the metric variation of a `C¹` path is at most its Riemannian length. -/
theorem eVariationOn_le_pathELength {γ : ℝ → M'} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) :
    eVariationOn γ (Icc a b) ≤ pathELength I γ a b := by
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, us⟩ := p
  exact (sum_edist_le_pathELength hγ hu us n).trans (pathELength_mono (us 0).1 (us n).2)

/-- A `C¹` path of finite Riemannian length has bounded variation in the Riemannian distance. -/
theorem boundedVariationOn_of_pathELength_ne_top {γ : ℝ → M'} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) (hL : pathELength I γ a b ≠ ⊤) :
    BoundedVariationOn γ (Icc a b) :=
  ne_top_of_le_ne_top hL (eVariationOn_le_pathELength hγ)

/-- Almost minimising paths: if `L(γ|[a,b]) ≤ d(γ a, γ b) + ε` (finite), then on every
subinterval `L(γ|[s,t]) ≤ d(γ s, γ t) + ε`. -/
theorem pathELength_le_edist_add {γ : ℝ → M'} {a b s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    {ε : ℝ≥0∞} (hmin : pathELength I γ a b ≤ edist (γ a) (γ b) + ε)
    (hfin : edist (γ a) (γ b) + ε ≠ ⊤) :
    pathELength I γ s t ≤ edist (γ s) (γ t) + ε := by
  have hsplit : pathELength I γ a s + pathELength I γ s t + pathELength I γ t b
      = pathELength I γ a b := by
    rw [pathELength_add hs hst, pathELength_add (hs.trans hst) ht]
  have hA : edist (γ a) (γ s) ≤ pathELength I γ a s :=
    edist_le_pathELength hγ le_rfl hs (hst.trans ht)
  have hC : edist (γ t) (γ b) ≤ pathELength I γ t b :=
    edist_le_pathELength hγ (hs.trans hst) ht le_rfl
  have hLfin : pathELength I γ a b ≠ ⊤ := ne_top_of_le_ne_top hfin hmin
  have hAfin : edist (γ a) (γ s) ≠ ⊤ :=
    ne_top_of_le_ne_top hLfin (hA.trans (pathELength_mono le_rfl (hst.trans ht)))
  have hCfin : edist (γ t) (γ b) ≠ ⊤ :=
    ne_top_of_le_ne_top hLfin (hC.trans (pathELength_mono (hs.trans hst) le_rfl))
  have htri : edist (γ a) (γ b)
      ≤ edist (γ a) (γ s) + edist (γ s) (γ t) + edist (γ t) (γ b) :=
    calc edist (γ a) (γ b) ≤ edist (γ a) (γ t) + edist (γ t) (γ b) := edist_triangle _ _ _
      _ ≤ edist (γ a) (γ s) + edist (γ s) (γ t) + edist (γ t) (γ b) := by
        gcongr; exact edist_triangle _ _ _
  have key : edist (γ a) (γ s) + edist (γ t) (γ b) + pathELength I γ s t
      ≤ edist (γ a) (γ s) + edist (γ t) (γ b) + (edist (γ s) (γ t) + ε) := by
    calc edist (γ a) (γ s) + edist (γ t) (γ b) + pathELength I γ s t
        ≤ pathELength I γ a s + pathELength I γ t b + pathELength I γ s t := by gcongr
      _ = pathELength I γ a s + pathELength I γ s t + pathELength I γ t b := by ring
      _ = pathELength I γ a b := hsplit
      _ ≤ edist (γ a) (γ b) + ε := hmin
      _ ≤ edist (γ a) (γ s) + edist (γ s) (γ t) + edist (γ t) (γ b) + ε := by gcongr
      _ = edist (γ a) (γ s) + edist (γ t) (γ b) + (edist (γ s) (γ t) + ε) := by ring
  exact (ENNReal.add_le_add_iff_left (ENNReal.add_ne_top.2 ⟨hAfin, hCfin⟩)).1 key

/-- STAGE (2), metric form: under the hypotheses of `pathELength_le_edist_add`, on every
subinterval `d(γ s, γ t) ≤ var(γ|[s,t]) ≤ L(γ|[s,t]) ≤ d(γ s, γ t) + ε`. -/
theorem eVariationOn_almost_minimising {γ : ℝ → M'} {a b s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    {ε : ℝ≥0∞} (hmin : pathELength I γ a b ≤ edist (γ a) (γ b) + ε)
    (hfin : edist (γ a) (γ b) + ε ≠ ⊤) :
    edist (γ s) (γ t) ≤ eVariationOn γ (Icc s t) ∧
    eVariationOn γ (Icc s t) ≤ pathELength I γ s t ∧
    pathELength I γ s t ≤ edist (γ s) (γ t) + ε :=
  ⟨eVariationOn.edist_le γ (left_mem_Icc.2 hst) (right_mem_Icc.2 hst),
    eVariationOn_le_pathELength (hγ.mono (Icc_subset_Icc hs ht)),
    pathELength_le_edist_add hγ hs hst ht hmin hfin⟩

/-- Exact minimisers among `C¹` paths are geodesic segments in the metric sense: if
`L(γ|[a,b]) = d(γ a, γ b) < ∞`, then on every subinterval
`d(γ s, γ t) = var(γ|[s,t]) = L(γ|[s,t])`. -/
theorem minimising_path_metric_geodesic {γ : ℝ → M'} {a b s t : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    (hmin : pathELength I γ a b = edist (γ a) (γ b)) (hfin : edist (γ a) (γ b) ≠ ⊤) :
    edist (γ s) (γ t) = eVariationOn γ (Icc s t) ∧
    eVariationOn γ (Icc s t) = pathELength I γ s t := by
  obtain ⟨h1, h2, h3⟩ := eVariationOn_almost_minimising hγ hs hst ht (ε := 0)
    (by rw [add_zero, hmin]) (by rwa [add_zero])
  rw [add_zero] at h3
  exact ⟨le_antisymm h1 (h2.trans h3), le_antisymm h2 (h3.trans h1)⟩

/-- Existence of almost minimising paths: for two points at finite distance and every `ε > 0`
there is a path on `[0,1]`, `C¹` there, from `x` to `y`, that is `ε`-almost minimising on every
subinterval in the metric sense: `var(γ|[s,t]) ≤ d(γ s, γ t) + ε` for `0 ≤ s ≤ t ≤ 1`. -/
theorem exists_almost_minimising_path (x y : M') (hxy : edist x y ≠ ⊤) {ε : ℝ≥0∞}
    (hε : 0 < ε) (hε' : ε ≠ ⊤) :
    ∃ γ : ℝ → M', γ 0 = x ∧ γ 1 = y ∧ ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1) ∧
      pathELength I γ 0 1 < edist x y + ε ∧
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 →
        edist (γ s) (γ t) ≤ eVariationOn γ (Icc s t) ∧
        eVariationOn γ (Icc s t) ≤ pathELength I γ s t ∧
        pathELength I γ s t ≤ edist (γ s) (γ t) + ε := by
  have hlt : riemannianEDist I x y < edist x y + ε := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact ENNReal.lt_add_right hxy hε.ne'
  obtain ⟨γ, h0, h1, hγ, hL⟩ := exists_lt_of_riemannianEDist_lt (I := I) hlt
  refine ⟨γ, h0, h1, hγ, hL, fun s t hs hst ht => ?_⟩
  refine eVariationOn_almost_minimising hγ hs hst ht ?_ ?_
  · rw [h0, h1]; exact hL.le
  · rw [h0, h1]; exact ENNReal.add_ne_top.2 ⟨hxy, hε'⟩

end Variation

/-! ### Finite length, almost minimising paths, and a metric minimiser (block A114)

(i) A `C¹` path on a compact interval has finite length: with a bound on the derivative as a
hypothesis (`pathELength_ne_top_of_bound`), and without hypothesis for a continuous Riemannian
tangent bundle (`pathELength_ne_top_of_contMDiffOn`).
(ii) Almost minimising paths exist between any two points of a connected Riemannian manifold
(`exists_almost_minimising_path_of_connected`).
(iii) On a COMPACT connected Riemannian manifold (Mathlib's `IsRiemannianManifold`, an `EMetricSpace`)
any two points are joined by a curve `c : ℝ → M` with `c 0 = x`, `c 1 = y` and constant speed:
`d(c s, c t) = (t − s) d(x, y)` and `var(c|[s,t]) = d(c s, c t)` for `0 ≤ s ≤ t ≤ 1`
(`exists_minimising_curve`).  Route (midpoints, no arc-length reparametrisation): approximate
midpoints from almost minimising paths and the intermediate value theorem; exact midpoints by
compactness; a curve from iterated midpoints on dyadic points, extended by Cauchy limits.  The curve
is a metric minimiser; it is NOT shown to be `C¹`, nor a Riemannian geodesic, nor unique. -/

section FiniteLength

/-- (i), minimal form: if `‖γ'(t)‖ₑ ≤ C < ∞` on `[a,b]` (derivative within `[a,b]`), the length is
finite.  HYPOTHESIS: the bound `h`. -/
theorem pathELength_ne_top_of_bound [∀ x : M, ENorm (TangentSpace I x)] {γ : ℝ → M} {a b : ℝ}
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (h : ∀ t ∈ Icc a b, ‖mfderivWithin 𝓘(ℝ) I γ (Icc a b) t 1‖ₑ ≤ C) :
    pathELength I γ a b ≠ ⊤ := by
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  have hv : volume (Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC hv) ?_
  calc ∫⁻ t in Icc a b, ‖mfderivWithin 𝓘(ℝ) I γ (Icc a b) t 1‖ₑ
      ≤ ∫⁻ _ in Icc a b, C := setLIntegral_mono' measurableSet_Icc h
    _ = C * volume (Icc a b) := setLIntegral_const _ _

variable {M' : Type*} [PseudoEMetricSpace M'] [ChartedSpace H M'] [IsManifold I 1 M']
  [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun (x : M') ↦ TangentSpace I x)]

/-- (i), without hypothesis: on a manifold with a continuous Riemannian tangent bundle, a `C¹` path on
`[a, b]` (`a < b`) has finite length (the norm of its derivative is continuous on the compact
interval). -/
theorem pathELength_ne_top_of_contMDiffOn {γ : ℝ → M'} {a b : ℝ} (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc a b)) : pathELength I γ a b ≠ ⊤ := by
  have hU : UniqueMDiffOn 𝓘(ℝ) (Icc a b) :=
    uniqueMDiffOn_iff_uniqueDiffOn.2 (uniqueDiffOn_Icc hab)
  have hmk : Continuous (fun t : ℝ => (⟨t, 1⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hcont : ContinuousOn (fun t => (TotalSpace.mk' E (E := fun x : M' ↦ TangentSpace I x) (γ t)
      (mfderivWithin 𝓘(ℝ) I γ (Icc a b) t 1))) (Icc a b) :=
    (hγ.continuousOn_tangentMapWithin le_rfl hU).comp hmk.continuousOn (fun t ht => ht)
  have hinner := ContinuousOn.inner_bundle hcont hcont
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hinner
  refine pathELength_ne_top_of_bound (ENNReal.ofReal (Real.sqrt C)) ENNReal.ofReal_ne_top
    (fun t ht => ?_)
  rw [← ofReal_norm_eq_enorm]
  apply ENNReal.ofReal_le_ofReal
  have h1 := hC t ht
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h1
  calc ‖mfderivWithin 𝓘(ℝ) I γ (Icc a b) t 1‖
      = Real.sqrt (‖mfderivWithin 𝓘(ℝ) I γ (Icc a b) t 1‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt C := Real.sqrt_le_sqrt h1

end FiniteLength

section Minimiser

/-- (ii): on a connected Riemannian manifold every pair of points is joined, for every
`0 < ε < ∞`, by an `ε`-almost minimising `C¹` path on `[0,1]`. -/
theorem exists_almost_minimising_path_of_connected {M' : Type*} [PseudoEMetricSpace M']
    [ChartedSpace H M'] [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)]
    [IsRiemannianManifold I M'] [PreconnectedSpace M'] (x y : M') {ε : ℝ≥0∞}
    (hε : 0 < ε) (hε' : ε ≠ ⊤) :
    ∃ γ : ℝ → M', γ 0 = x ∧ γ 1 = y ∧ ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1) ∧
      pathELength I γ 0 1 < edist x y + ε ∧
      ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 →
        edist (γ s) (γ t) ≤ eVariationOn γ (Icc s t) ∧
        eVariationOn γ (Icc s t) ≤ pathELength I γ s t ∧
        pathELength I γ s t ≤ edist (γ s) (γ t) + ε :=
  exists_almost_minimising_path x y (edist_ne_top_of_preconnected x y) hε hε'

/-- Approximate midpoints on a Riemannian manifold: for points at finite distance and `0 < ε < ∞`
there is `z` with `d(x,z) ≤ d(x,y)/2 + ε` and `d(z,y) ≤ d(x,y)/2 + ε`. -/
theorem riemannian_approx_midpoint {M' : Type*} [PseudoEMetricSpace M']
    [ChartedSpace H M'] [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)]
    [IsRiemannianManifold I M'] (x y : M') (hxy : edist x y ≠ ⊤) {ε : ℝ≥0∞}
    (hε : 0 < ε) (hε' : ε ≠ ⊤) :
    ∃ z, edist x z ≤ edist x y / 2 + ε ∧ edist z y ≤ edist x y / 2 + ε := by
  obtain ⟨γ, h0, h1, hγ, hL, -⟩ := exists_almost_minimising_path (I := I) x y hxy hε hε'
  set D := edist x y with hD
  have hcont : ContinuousOn (fun t => edist x (γ t)) (Icc 0 1) :=
    (continuous_const.edist continuous_id).comp_continuousOn hγ.continuousOn
  have hmem : D / 2 ∈ Icc (edist x (γ 0)) (edist x (γ 1)) := by
    rw [h0, h1, edist_self]; exact ⟨zero_le _, ENNReal.half_le_self⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc zero_le_one hcont hmem
  have hft' : edist x (γ t) = D / 2 := hft
  refine ⟨γ t, by rw [hft']; exact le_self_add, ?_⟩
  have hA : edist (γ 0) (γ t) ≤ pathELength I γ 0 t := edist_le_pathELength hγ le_rfl ht.1 ht.2
  have hB : edist (γ t) (γ 1) ≤ pathELength I γ t 1 := edist_le_pathELength hγ ht.1 ht.2 le_rfl
  rw [h0] at hA
  rw [h1] at hB
  have hD2 : D / 2 ≠ ⊤ := ne_top_of_le_ne_top hxy ENNReal.half_le_self
  have key : D / 2 + pathELength I γ t 1 ≤ D / 2 + (D / 2 + ε) := by
    calc D / 2 + pathELength I γ t 1 ≤ pathELength I γ 0 t + pathELength I γ t 1 := by
          gcongr; rw [← hft']; exact hA
      _ = pathELength I γ 0 1 := pathELength_add ht.1 ht.2
      _ ≤ D + ε := hL.le
      _ = D / 2 + (D / 2 + ε) := by rw [← add_assoc, ENNReal.add_halves]
  exact hB.trans ((ENNReal.add_le_add_iff_left hD2).1 key)

variable {X : Type*} [EMetricSpace X]

/-- Exact midpoints from approximate ones in a compact space. -/
theorem exists_midpoint_of_approx [CompactSpace X]
    (happrox : ∀ a b : X, edist a b ≠ ⊤ → ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ⊤ →
      ∃ z, edist a z ≤ edist a b / 2 + ε ∧ edist z b ≤ edist a b / 2 + ε)
    (a b : X) (hab : edist a b ≠ ⊤) :
    ∃ m, edist a m ≤ edist a b / 2 ∧ edist m b ≤ edist a b / 2 := by
  set D := edist a b
  let S : ℕ → Set X := fun n =>
    {z | edist a z ≤ D / 2 + 2⁻¹ ^ n} ∩ {z | edist z b ≤ D / 2 + 2⁻¹ ^ n}
  have hcl : ∀ n, IsClosed (S n) := fun n =>
    (isClosed_le (continuous_const.edist continuous_id) continuous_const).inter
      (isClosed_le (continuous_id.edist continuous_const) continuous_const)
  have hpow : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) ≤ 2⁻¹ ^ n := fun n => by
    rw [pow_succ]
    exact mul_le_of_le_one_right (zero_le _) (ENNReal.inv_le_one.2 one_le_two)
  have hdec : ∀ n, S (n + 1) ⊆ S n := fun n z hz =>
    ⟨hz.1.trans (add_le_add le_rfl (hpow n)), hz.2.trans (add_le_add le_rfl (hpow n))⟩
  have hne : ∀ n, (S n).Nonempty := fun n => by
    obtain ⟨z, hz⟩ := happrox a b hab (2⁻¹ ^ n)
      (ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) n)
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 two_ne_zero))
    exact ⟨z, hz⟩
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hm
  have hlim : ∀ c : ℝ≥0∞, (∀ n : ℕ, c ≤ D / 2 + 2⁻¹ ^ n) → c ≤ D / 2 := fun c hc => by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.coe_ne_zero.2 hε.ne')
    exact (hc n).trans (add_le_add le_rfl hn.le)
  exact ⟨m, hlim _ fun n => (hm n).1, hlim _ fun n => (hm n).2⟩

/-- Iterated midpoints on the dyadic points `k / 2^n`. -/
def dyad (mid : X → X → X) (x y : X) : ℕ → ℕ → X
  | 0, k => if k = 0 then x else y
  | n + 1, k => if k % 2 = 0 then dyad mid x y n (k / 2)
      else mid (dyad mid x y n (k / 2)) (dyad mid x y n (k / 2 + 1))

theorem dyad_even (mid : X → X → X) (x y : X) (n j : ℕ) :
    dyad mid x y (n + 1) (2 * j) = dyad mid x y n j := by
  have h1 : 2 * j % 2 = 0 := by omega
  have h2 : 2 * j / 2 = j := by omega
  simp only [dyad, h1, h2, if_true]

theorem dyad_odd (mid : X → X → X) (x y : X) (n j : ℕ) :
    dyad mid x y (n + 1) (2 * j + 1) = mid (dyad mid x y n j) (dyad mid x y n (j + 1)) := by
  have h1 : (2 * j + 1) % 2 = 1 := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  simp only [dyad, h1, h2, one_ne_zero, if_false]

theorem dyad_zero (mid : X → X → X) (x y : X) (n : ℕ) : dyad mid x y n 0 = x := by
  induction n with
  | zero => simp [dyad]
  | succ n ih => rw [show (0 : ℕ) = 2 * 0 from rfl, dyad_even, ih]

theorem dyad_top (mid : X → X → X) (x y : X) (n : ℕ) : dyad mid x y n (2 ^ n) = y := by
  induction n with
  | zero => simp [dyad]
  | succ n ih => rw [pow_succ, mul_comm, dyad_even, ih]

variable {mid : X → X → X}
  (hmid : ∀ a b : X, edist a (mid a b) ≤ edist a b / 2 ∧ edist (mid a b) b ≤ edist a b / 2)
include hmid

theorem dyad_step (x y : X) (D : ℝ≥0∞) (hD : edist x y ≤ D) (n k : ℕ) :
    edist (dyad mid x y n k) (dyad mid x y n (k + 1)) ≤ D * 2⁻¹ ^ n := by
  induction n generalizing k with
  | zero =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [dyad] using hD
    · simp [dyad, hk.ne', edist_self]
  | succ n ih =>
    have e : D * 2⁻¹ ^ (n + 1) = D * 2⁻¹ ^ n / 2 := by
      rw [pow_succ, ← mul_assoc, div_eq_mul_inv]
    rw [e]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [dyad_even, dyad_odd]
      exact (hmid _ _).1.trans (ENNReal.div_le_div_right (ih j) 2)
    · rw [dyad_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, dyad_even]
      exact (hmid _ _).2.trans (ENNReal.div_le_div_right (ih j) 2)

theorem dyad_far (x y : X) (D : ℝ≥0∞) (hD : edist x y ≤ D) (n j k : ℕ) (hjk : j ≤ k) :
    edist (dyad mid x y n j) (dyad mid x y n k) ≤ ((k - j : ℕ) : ℝ≥0∞) * (D * 2⁻¹ ^ n) := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ k hjk ih =>
    calc edist (dyad mid x y n j) (dyad mid x y n (k + 1))
        ≤ edist (dyad mid x y n j) (dyad mid x y n k)
          + edist (dyad mid x y n k) (dyad mid x y n (k + 1)) := edist_triangle _ _ _
      _ ≤ ((k - j : ℕ) : ℝ≥0∞) * (D * 2⁻¹ ^ n) + D * 2⁻¹ ^ n :=
          add_le_add ih (dyad_step hmid x y D hD n k)
      _ = ((k + 1 - j : ℕ) : ℝ≥0∞) * (D * 2⁻¹ ^ n) := by
          rw [Nat.succ_sub hjk]; push_cast; ring

omit hmid in
theorem floor_two_mul (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    ⌊t * 2 ^ (n + 1)⌋₊ = 2 * ⌊t * 2 ^ n⌋₊ ∨ ⌊t * 2 ^ (n + 1)⌋₊ = 2 * ⌊t * 2 ^ n⌋₊ + 1 := by
  set a := ⌊t * 2 ^ n⌋₊
  have h0 : 0 ≤ t * 2 ^ n := by positivity
  have ha1 : (a : ℝ) ≤ t * 2 ^ n := Nat.floor_le h0
  have ha2 : t * 2 ^ n < a + 1 := Nat.lt_floor_add_one _
  have e : t * 2 ^ (n + 1) = 2 * (t * 2 ^ n) := by ring
  have hb1 : 2 * a ≤ ⌊t * 2 ^ (n + 1)⌋₊ := by
    apply Nat.le_floor; rw [e]; push_cast; linarith
  have hb2 : ⌊t * 2 ^ (n + 1)⌋₊ < 2 * a + 2 := by
    rw [Nat.floor_lt (by positivity), e]; push_cast; linarith
  omega

theorem dyad_seq_step (x y : X) (D : ℝ≥0∞) (hD : edist x y ≤ D) (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    edist (dyad mid x y n ⌊t * 2 ^ n⌋₊) (dyad mid x y (n + 1) ⌊t * 2 ^ (n + 1)⌋₊)
      ≤ D / 2 ^ n := by
  have hle : D * 2⁻¹ ^ (n + 1) ≤ D / 2 ^ n := by
    have hp : (2⁻¹ : ℝ≥0∞) ^ (n + 1) ≤ 2⁻¹ ^ n := by
      rw [pow_succ]; exact mul_le_of_le_one_right (zero_le _) (ENNReal.inv_le_one.2 one_le_two)
    calc D * 2⁻¹ ^ (n + 1) ≤ D * 2⁻¹ ^ n := mul_le_mul_left' hp D
      _ = D / 2 ^ n := by rw [div_eq_mul_inv, ENNReal.inv_pow]
  rcases floor_two_mul t ht n with h | h
  · rw [h, dyad_even, edist_self]; exact zero_le _
  · rw [h, ← dyad_even mid x y n ⌊t * 2 ^ n⌋₊]
    exact (dyad_step hmid x y D hD (n + 1) _).trans hle

omit hmid in
theorem div_two_pow_tendsto (D : ℝ≥0∞) (hD : D ≠ ⊤) :
    Filter.Tendsto (fun n : ℕ => D / 2 ^ n) Filter.atTop (𝓝 0) := by
  have h : Filter.Tendsto (fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n) Filter.atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)
  have h2 := ENNReal.Tendsto.const_mul h (Or.inr hD)
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  rw [div_eq_mul_inv, ENNReal.inv_pow]

omit hmid in
/-- A curve with `d(c s, c t) ≤ (t − s) D` on `[a,b]` has variation at most `(b − a) D` there. -/
theorem eVariationOn_le_of_lipschitz (c : ℝ → X) (D : ℝ≥0∞) {a b : ℝ}
    (hc : ∀ s t, a ≤ s → s ≤ t → t ≤ b → edist (c s) (c t) ≤ ENNReal.ofReal (t - s) * D) :
    eVariationOn c (Icc a b) ≤ ENNReal.ofReal (b - a) * D := by
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, us⟩ := p
  have key : ∀ n, ∑ i ∈ Finset.range n, edist (c (u (i + 1))) (c (u i))
      ≤ ENNReal.ofReal (u n - u 0) * D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : u 0 ≤ u n := hu (Nat.zero_le n)
      have h2 : u n ≤ u (n + 1) := hu (Nat.le_succ n)
      calc ∑ i ∈ Finset.range n, edist (c (u (i + 1))) (c (u i)) + edist (c (u (n + 1))) (c (u n))
          ≤ ENNReal.ofReal (u n - u 0) * D + ENNReal.ofReal (u (n + 1) - u n) * D := by
            refine add_le_add ih ?_
            rw [edist_comm]; exact hc _ _ (us n).1 h2 (us (n + 1)).2
        _ = ENNReal.ofReal (u (n + 1) - u 0) * D := by
            rw [← add_mul, ← ENNReal.ofReal_add (by linarith) (by linarith)]
            congr 2; ring
  refine (key n).trans (mul_le_mul_right' (ENNReal.ofReal_le_ofReal ?_) _)
  linarith [(us n).2, (us 0).1]

/-- The midpoint curve: limits of iterated midpoints at `⌊t 2^n⌋ / 2^n`. -/
theorem exists_midpoint_curve [CompleteSpace X] (x y : X) (hxy : edist x y ≠ ⊤) :
    ∃ c : ℝ → X, c 0 = x ∧ c 1 = y ∧
      ∀ s t, 0 ≤ s → s ≤ t → edist (c s) (c t) ≤ ENNReal.ofReal (t - s) * edist x y := by
  set D := edist x y with hDdef
  let g : ℝ → ℕ → X := fun t n => dyad mid x y n ⌊t * 2 ^ n⌋₊
  have hcauchy : ∀ t, 0 ≤ t → CauchySeq (g t) := fun t ht =>
    cauchySeq_of_edist_le_geometric_two D hxy (dyad_seq_step hmid x y D le_rfl t ht)
  haveI : Nonempty X := ⟨x⟩
  let c : ℝ → X := fun t => Filter.limUnder Filter.atTop (g t)
  have hlim : ∀ t, 0 ≤ t → Filter.Tendsto (g t) Filter.atTop (𝓝 (c t)) := fun t ht =>
    (hcauchy t ht).tendsto_limUnder
  have htail : ∀ t, 0 ≤ t → ∀ n, edist (g t n) (c t) ≤ 2 * D / 2 ^ n := fun t ht n =>
    edist_le_of_edist_le_geometric_two_of_tendsto D (dyad_seq_step hmid x y D le_rfl t ht)
      (hlim t ht) n
  refine ⟨c, ?_, ?_, ?_⟩
  · have hg : g 0 = fun _ => x := funext fun n => by simp [g, dyad_zero]
    have := hlim 0 le_rfl
    rw [hg] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  · have hg : g 1 = fun _ => y := funext fun n => by
      have : ⌊(1 : ℝ) * 2 ^ n⌋₊ = 2 ^ n := by
        rw [one_mul, show ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
      simp only [g, this, dyad_top]
    have := hlim 1 zero_le_one
    rw [hg] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  · intro s t hs hst
    have ht : 0 ≤ t := hs.trans hst
    have hbound : ∀ n : ℕ, edist (c s) (c t)
        ≤ ENNReal.ofReal (t - s) * D + 5 * (D / 2 ^ n) := by
      intro n
      set j := ⌊s * 2 ^ n⌋₊
      set k := ⌊t * 2 ^ n⌋₊
      have hjk : j ≤ k := Nat.floor_le_floor (by gcongr)
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      -- the dyadic estimate in real numbers
      have hreal : ((k - j : ℕ) : ℝ) / 2 ^ n ≤ (t - s) + 1 / 2 ^ n := by
        have hk : (k : ℝ) ≤ t * 2 ^ n := Nat.floor_le (by positivity)
        have hj : s * 2 ^ n < j + 1 := Nat.lt_floor_add_one _
        rw [Nat.cast_sub hjk, div_le_iff₀ h2n, add_mul, one_div, inv_mul_cancel₀ h2n.ne']
        nlinarith
      have hconv : ∀ r : ℝ, 0 ≤ r → ENNReal.ofReal (r / 2 ^ n) = ENNReal.ofReal r / 2 ^ n :=
        fun r hr => by
          rw [ENNReal.ofReal_div_of_pos h2n, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
      have hmid' : ((k - j : ℕ) : ℝ≥0∞) * (D * 2⁻¹ ^ n)
          ≤ ENNReal.ofReal (t - s) * D + D / 2 ^ n := by
        have e1 : ((k - j : ℕ) : ℝ≥0∞) * (D * 2⁻¹ ^ n)
            = ENNReal.ofReal (((k - j : ℕ) : ℝ) / 2 ^ n) * D := by
          rw [hconv _ (Nat.cast_nonneg _), ENNReal.ofReal_natCast, div_eq_mul_inv,
            ← ENNReal.inv_pow]; ring
        rw [e1]
        calc ENNReal.ofReal (((k - j : ℕ) : ℝ) / 2 ^ n) * D
            ≤ ENNReal.ofReal ((t - s) + 1 / 2 ^ n) * D :=
              mul_le_mul_right' (ENNReal.ofReal_le_ofReal hreal) _
          _ = ENNReal.ofReal (t - s) * D + D / 2 ^ n := by
              rw [ENNReal.ofReal_add (by linarith) (by positivity), add_mul, hconv 1 zero_le_one,
                ENNReal.ofReal_one]
              congr 1
              rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
      have h2D : 2 * D / 2 ^ n = 2 * (D / 2 ^ n) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
      calc edist (c s) (c t) ≤ edist (c s) (g s n) + edist (g s n) (g t n) + edist (g t n) (c t) :=
            edist_triangle4 _ _ _ _
        _ ≤ 2 * (D / 2 ^ n) + (ENNReal.ofReal (t - s) * D + D / 2 ^ n) + 2 * (D / 2 ^ n) := by
            gcongr
            · rw [edist_comm, ← h2D]; exact htail s hs n
            · exact (dyad_far hmid x y D le_rfl n j k hjk).trans hmid'
            · rw [← h2D]; exact htail t ht n
        _ = ENNReal.ofReal (t - s) * D + 5 * (D / 2 ^ n) := by ring
    have hT : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (t - s) * D + 5 * (D / 2 ^ n))
        Filter.atTop (𝓝 (ENNReal.ofReal (t - s) * D + 5 * 0)) :=
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul (div_two_pow_tendsto D hxy)
        (Or.inr ENNReal.ofNat_ne_top))
    rw [mul_zero, add_zero] at hT
    exact ge_of_tendsto' hT hbound

omit hmid in
/-- Constant speed and minimality of a curve with the Lipschitz bound `(t − s) d(x,y)`. -/
theorem curve_minimising (c : ℝ → X) (x y : X) (hxy : edist x y ≠ ⊤) (h0 : c 0 = x) (h1 : c 1 = y)
    (hc : ∀ s t, 0 ≤ s → s ≤ t → edist (c s) (c t) ≤ ENNReal.ofReal (t - s) * edist x y)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    edist (c s) (c t) = ENNReal.ofReal (t - s) * edist x y ∧
    eVariationOn c (Icc s t) = edist (c s) (c t) := by
  set D := edist x y
  have hlow : ENNReal.ofReal (t - s) * D ≤ edist (c s) (c t) := by
    have hA := hc 0 s le_rfl hs
    have hB := hc t 1 (hs.trans hst) ht
    rw [h0, sub_zero] at hA
    rw [h1] at hB
    have hAfin : ENNReal.ofReal s * D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hxy
    have hBfin : ENNReal.ofReal (1 - t) * D ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hxy
    have hsum : ENNReal.ofReal s * D + ENNReal.ofReal (1 - t) * D + ENNReal.ofReal (t - s) * D
        = D := by
      rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add hs (by linarith),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      rw [show s + (1 - t) + (t - s) = 1 by ring, ENNReal.ofReal_one, one_mul]
    have htri : D ≤ edist x (c s) + edist (c s) (c t) + edist (c t) y :=
      edist_triangle4 _ _ _ _
    have key : ENNReal.ofReal s * D + ENNReal.ofReal (1 - t) * D + ENNReal.ofReal (t - s) * D
        ≤ ENNReal.ofReal s * D + ENNReal.ofReal (1 - t) * D + edist (c s) (c t) := by
      rw [hsum]
      calc D ≤ edist x (c s) + edist (c s) (c t) + edist (c t) y := htri
        _ ≤ ENNReal.ofReal s * D + edist (c s) (c t) + ENNReal.ofReal (1 - t) * D := by gcongr
        _ = _ := by ring
    exact (ENNReal.add_le_add_iff_left (ENNReal.add_ne_top.2 ⟨hAfin, hBfin⟩)).1 key
  have hup : edist (c s) (c t) ≤ ENNReal.ofReal (t - s) * D := hc s t hs hst
  have hvar : eVariationOn c (Icc s t) ≤ ENNReal.ofReal (t - s) * D :=
    eVariationOn_le_of_lipschitz c D fun u v hu huv hv => hc u v (hs.trans hu) huv
  have hge : edist (c s) (c t) ≤ eVariationOn c (Icc s t) :=
    eVariationOn.edist_le c (left_mem_Icc.2 hst) (right_mem_Icc.2 hst)
  exact ⟨le_antisymm hup hlow, le_antisymm (hvar.trans hlow) hge⟩

omit hmid in
/-- (iii), abstract metric form: in a compact emetric space with approximate midpoints at finite
distance, any two points at finite distance are joined by a constant-speed minimising curve. -/
theorem exists_minimising_curve_of_approx [CompactSpace X]
    (happrox : ∀ a b : X, edist a b ≠ ⊤ → ∀ ε : ℝ≥0∞, 0 < ε → ε ≠ ⊤ →
      ∃ z, edist a z ≤ edist a b / 2 + ε ∧ edist z b ≤ edist a b / 2 + ε)
    (hfin : ∀ a b : X, edist a b ≠ ⊤) (x y : X) :
    ∃ c : ℝ → X, c 0 = x ∧ c 1 = y ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 →
        edist (c s) (c t) = ENNReal.ofReal (t - s) * edist x y ∧
        eVariationOn c (Icc s t) = edist (c s) (c t)) ∧
      eVariationOn c (Icc 0 1) = edist x y := by
  choose mid hmid using fun a b => exists_midpoint_of_approx happrox a b (hfin a b)
  obtain ⟨c, h0, h1, hc⟩ := exists_midpoint_curve (mid := mid) hmid x y (hfin x y)
  have hall := fun s t hs hst ht => curve_minimising c x y (hfin x y) h0 h1 hc s t hs hst ht
  refine ⟨c, h0, h1, hall, ?_⟩
  rw [(hall 0 1 le_rfl zero_le_one le_rfl).2, h0, h1]

omit hmid in
/-- (iii): on a COMPACT connected Riemannian manifold (Mathlib's `IsRiemannianManifold`, an
`EMetricSpace`), any two points are joined by a curve `c : ℝ → M` with `c 0 = x`, `c 1 = y`,
`d(c s, c t) = (t − s) d(x,y)` and `var(c|[s,t]) = d(c s, c t)` for `0 ≤ s ≤ t ≤ 1`; in particular
`var(c|[0,1]) = d(x,y)` and `c` is `d(x,y)`-Lipschitz on `[0,1]`.  The curve is a metric minimiser;
it is NOT shown to be `C¹` or a Riemannian geodesic, and NOT shown to be unique. -/
theorem exists_minimising_curve {M' : Type*} [EMetricSpace M'] [ChartedSpace H M']
    [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)] [IsRiemannianManifold I M']
    [CompactSpace M'] [PreconnectedSpace M'] (x y : M') :
    ∃ c : ℝ → M', c 0 = x ∧ c 1 = y ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 →
        edist (c s) (c t) = ENNReal.ofReal (t - s) * edist x y ∧
        eVariationOn c (Icc s t) = edist (c s) (c t)) ∧
      eVariationOn c (Icc 0 1) = edist x y :=
  exists_minimising_curve_of_approx
    (fun a b hab _ hε hε' => riemannian_approx_midpoint (I := I) a b hab hε hε')
    (fun a b => edist_ne_top_of_preconnected a b) x y

end Minimiser

/-! ### Differentiability of the distance in time almost everywhere, and a one-sided envelope theorem
(block A115)

(1) For a `TimeMetric` and a pair of points with finite distances, `τ ↦ d_τ(x,y)` is Lipschitz on
every compact subinterval of the time set, with explicit constant `κ e^{2κ(q−p)} d_p(x,y)`, hence
(Rademacher in one variable, Mathlib's `LipschitzOnWith.ae_differentiableWithinAt_of_mem_real`)
differentiable at almost every interior time; where it is differentiable,
`|∂_τ d_τ(x,y)| ≤ κ d_τ(x,y)`.  This is "almost every τ for each pair", NOT "every τ for almost
every pair"; the joint statement is not done (see the report of A115).
(2) An abstract one-sided (Danskin-type) envelope theorem: for `F τ ≤ g τ k` with equality at
`(τ₀, k₀)` and `g(·,k₀)` differentiable at `τ₀`, `F τ − F τ₀ ≤ ∂g (τ − τ₀) + o(|τ − τ₀|)`;
minimisers converge under lower semicontinuity, uniform convergence in `τ` and compactness; and
two-sided differentiability under a uniform one-sided first-order bound near `k₀`, which holds when
`∂_τ g` is jointly continuous (recovering `envelope_min` with lower semicontinuity in place of
continuity of `g`). -/

section DistanceInTime

/-- The real distance at time `τ` of a `TimeMetric`. -/
def TimeMetric.dist {s : Set ℝ} (G : TimeMetric I M s) (x y : M) (τ : ℝ) : ℝ :=
  (letI := G.norms τ; Manifold.riemannianEDist I x y).toReal

theorem TimeMetric.dist_nonneg {s : Set ℝ} (G : TimeMetric I M s) (x y : M) (τ : ℝ) :
    0 ≤ G.dist x y τ := ENNReal.toReal_nonneg

/-- `|d_b − d_a| ≤ (e^{κ|b−a|} − 1) d_a`. -/
theorem TimeMetric.dist_lip {s : Set ℝ} (G : TimeMetric I M s) (x y : M) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) (hfin : (letI := G.norms a; Manifold.riemannianEDist I x y) ≠ ⊤) :
    |G.dist x y b - G.dist x y a| ≤ (Real.exp (G.κ * |b - a|) - 1) * G.dist x y a :=
  G.lipschitz ha hb x y hfin

theorem exp_sub_one_le_mul_exp (y : ℝ) (hy : 0 ≤ y) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos y]

/-- Bound in a compact interval of times: `d_a ≤ e^{κ(q−p)} d_p` for `a ∈ [p, q] ⊆ s`. -/
theorem TimeMetric.dist_le_of_mem {s : Set ℝ} (G : TimeMetric I M s) (x y : M) {p q a : ℝ}
    (hsub : Icc p q ⊆ s) (ha : a ∈ Icc p q)
    (hfin : (letI := G.norms p; Manifold.riemannianEDist I x y) ≠ ⊤) :
    G.dist x y a ≤ Real.exp (G.κ * (q - p)) * G.dist x y p := by
  have hp : p ∈ Icc p q := left_mem_Icc.2 (ha.1.trans ha.2)
  have h := G.dist_lip x y (hsub hp) (hsub ha) hfin
  have h1 : G.dist x y a ≤ Real.exp (G.κ * |a - p|) * G.dist x y p := by
    have := le_abs_self (G.dist x y a - G.dist x y p); nlinarith
  have h2 : Real.exp (G.κ * |a - p|) ≤ Real.exp (G.κ * (q - p)) := by
    apply Real.exp_le_exp.2
    rw [abs_of_nonneg (by linarith [ha.1])]
    exact mul_le_mul_of_nonneg_left (by linarith [ha.2]) G.κ_nonneg
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (G.dist_nonneg x y p))

/-- (1a) Lipschitz in time on a compact subinterval `[p, q] ⊆ s`, with the explicit constant
`κ e^{2κ(q−p)} d_p(x,y)`.  HYPOTHESIS: finiteness of the distances at all times of `[p,q]`
(automatic on a compact connected manifold, `TimeMetric.riemannianEDist_ne_top`). -/
theorem TimeMetric.dist_lipschitzOn {s : Set ℝ} (G : TimeMetric I M s) (x y : M) {p q : ℝ}
    (hsub : Icc p q ⊆ s)
    (hfin : ∀ τ ∈ Icc p q, (letI := G.norms τ; Manifold.riemannianEDist I x y) ≠ ⊤) :
    ∀ a ∈ Icc p q, ∀ b ∈ Icc p q, |G.dist x y b - G.dist x y a|
      ≤ G.κ * Real.exp (2 * G.κ * (q - p)) * G.dist x y p * |b - a| := by
  intro a ha b hb
  have hpq : p ≤ q := ha.1.trans ha.2
  have hfp := hfin p (left_mem_Icc.2 hpq)
  have h := G.dist_lip x y (hsub ha) (hsub hb) (hfin a ha)
  have hy : 0 ≤ G.κ * |b - a| := mul_nonneg G.κ_nonneg (abs_nonneg _)
  have h1 := exp_sub_one_le_mul_exp _ hy
  have hba : |b - a| ≤ q - p := by
    rw [abs_le]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have h2 : Real.exp (G.κ * |b - a|) ≤ Real.exp (G.κ * (q - p)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hba G.κ_nonneg)
  have h3 := G.dist_le_of_mem x y hsub ha hfp
  have hD := G.dist_nonneg x y a
  have hDp := G.dist_nonneg x y p
  have e : Real.exp (2 * G.κ * (q - p)) = Real.exp (G.κ * (q - p)) * Real.exp (G.κ * (q - p)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  calc |G.dist x y b - G.dist x y a| ≤ (Real.exp (G.κ * |b - a|) - 1) * G.dist x y a := h
    _ ≤ (G.κ * |b - a| * Real.exp (G.κ * |b - a|)) * G.dist x y a :=
        mul_le_mul_of_nonneg_right h1 hD
    _ ≤ (G.κ * |b - a| * Real.exp (G.κ * (q - p))) * (Real.exp (G.κ * (q - p)) * G.dist x y p) := by
        apply mul_le_mul _ h3 hD (by positivity)
        exact mul_le_mul_of_nonneg_left h2 hy
    _ = G.κ * (Real.exp (G.κ * (q - p)) * Real.exp (G.κ * (q - p))) * G.dist x y p * |b - a| := by
        ring

/-- (1b) Differentiability at almost every interior time: for every compact `[p, q] ⊆ s`,
`τ ↦ d_τ(x,y)` is differentiable at almost every `τ ∈ (p, q)`. -/
theorem TimeMetric.dist_ae_differentiableAt_Icc {s : Set ℝ} (G : TimeMetric I M s) (x y : M)
    {p q : ℝ} (hsub : Icc p q ⊆ s)
    (hfin : ∀ τ ∈ Icc p q, (letI := G.norms τ; Manifold.riemannianEDist I x y) ≠ ⊤) :
    ∀ᵐ τ, τ ∈ Ioo p q → DifferentiableAt ℝ (G.dist x y) τ := by
  set L := G.κ * Real.exp (2 * G.κ * (q - p)) * G.dist x y p
  have hL : 0 ≤ L := by
    have := G.dist_nonneg x y p; have := G.κ_nonneg; positivity
  have hlip : LipschitzOnWith (Real.toNNReal L) (G.dist x y) (Icc p q) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    rw [Real.coe_toNNReal _ hL, Real.dist_eq, Real.dist_eq]
    exact G.dist_lipschitzOn x y hsub hfin b hb a ha
  filter_upwards [hlip.ae_differentiableWithinAt_of_mem_real] with τ hτ hτ'
  exact (hτ (Ioo_subset_Icc_self hτ')).differentiableAt (Icc_mem_nhds hτ'.1 hτ'.2)

/-- (1b') Differentiability at almost every time of the interior of `s`. -/
theorem TimeMetric.dist_ae_differentiableAt {s : Set ℝ} (G : TimeMetric I M s) (x y : M)
    (hfin : ∀ τ ∈ s, (letI := G.norms τ; Manifold.riemannianEDist I x y) ≠ ⊤) :
    ∀ᵐ τ, τ ∈ interior s → DifferentiableAt ℝ (G.dist x y) τ := by
  have hall : ∀ pq : ℚ × ℚ, ∀ᵐ τ, Icc (pq.1 : ℝ) pq.2 ⊆ s → τ ∈ Ioo (pq.1 : ℝ) pq.2 →
      DifferentiableAt ℝ (G.dist x y) τ := by
    intro pq
    by_cases h : Icc (pq.1 : ℝ) pq.2 ⊆ s
    · filter_upwards [G.dist_ae_differentiableAt_Icc x y h (fun τ hτ => hfin τ (h hτ))]
        with τ hτ _ using hτ
    · exact Filter.Eventually.of_forall fun τ h' => absurd h' h
  rw [← ae_all_iff] at hall
  filter_upwards [hall] with τ hτ hint
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show τ - ε < τ by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show τ < τ + ε by linarith)
  refine hτ (p, q) (fun u hu => ?_) ⟨hp2, hq1⟩
  dsimp only at hu
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hu.1, hu.2]

/-- (1c) Bound for the derivative: at every interior time where `τ ↦ d_τ(x,y)` has derivative `d'`,
`|d'| ≤ κ d_τ(x,y)`. -/
theorem TimeMetric.abs_deriv_dist_le {s : Set ℝ} (G : TimeMetric I M s) (x y : M) {τ d' : ℝ}
    (hint : τ ∈ interior s)
    (hfin : (letI := G.norms τ; Manifold.riemannianEDist I x y) ≠ ⊤)
    (hd : HasDerivAt (G.dist x y) d' τ) : |d'| ≤ G.κ * G.dist x y τ := by
  have hs : s ∈ 𝓝 τ := mem_interior_iff_mem_nhds.1 hint
  have hD := G.dist_nonneg x y τ
  have hk := G.κ_nonneg
  have hδ : ∀ n : ℕ, |d'| ≤ G.κ * Real.exp (G.κ * (1 / (n + 1 : ℝ))) * G.dist x y τ := by
    intro n
    have hn : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hev : ∀ᶠ b in 𝓝 τ, ‖G.dist x y b - G.dist x y τ‖
        ≤ G.κ * Real.exp (G.κ * (1 / (n + 1 : ℝ))) * G.dist x y τ * ‖b - τ‖ := by
      filter_upwards [hs, Metric.ball_mem_nhds τ hn] with b hb hb'
      rw [Metric.mem_ball, Real.dist_eq] at hb'
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have h := G.dist_lip x y (mem_of_mem_nhds hs) hb hfin
      have hy : 0 ≤ G.κ * |b - τ| := mul_nonneg hk (abs_nonneg _)
      have h1 := exp_sub_one_le_mul_exp _ hy
      have h2 : Real.exp (G.κ * |b - τ|) ≤ Real.exp (G.κ * (1 / (n + 1 : ℝ))) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hb'.le hk)
      calc |G.dist x y b - G.dist x y τ| ≤ (Real.exp (G.κ * |b - τ|) - 1) * G.dist x y τ := h
        _ ≤ (G.κ * |b - τ| * Real.exp (G.κ * |b - τ|)) * G.dist x y τ :=
            mul_le_mul_of_nonneg_right h1 hD
        _ ≤ (G.κ * |b - τ| * Real.exp (G.κ * (1 / (n + 1 : ℝ)))) * G.dist x y τ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hy) hD
        _ = G.κ * Real.exp (G.κ * (1 / (n + 1 : ℝ))) * G.dist x y τ * |b - τ| := by ring
    have := hd.le_of_lip' (by positivity) hev
    rwa [Real.norm_eq_abs] at this
  have hT : Filter.Tendsto (fun n : ℕ => G.κ * Real.exp (G.κ * (1 / (n + 1 : ℝ))) * G.dist x y τ)
      Filter.atTop (𝓝 (G.κ * Real.exp (G.κ * 0) * G.dist x y τ)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ))) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact ((tendsto_const_nhds.mul ((Real.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul h0))).mul tendsto_const_nhds)
  rw [mul_zero, Real.exp_zero, mul_one] at hT
  exact ge_of_tendsto' hT hδ

/-- (1) on a compact connected Riemannian manifold, for a `TimeMetric` whose metric is continuous
in the base point at one time `a ∈ s` (hypotheses of `TimeMetric.riemannianEDist_ne_top`): for every
pair `(x, y)`, `τ ↦ d_τ(x,y)` is differentiable at almost every time of the interior of `s`, and
`|∂_τ d_τ(x,y)| ≤ κ d_τ(x,y)` wherever it is differentiable in the interior. -/
theorem TimeMetric.dist_ae_differentiableAt_compact {M' : Type*} [PseudoEMetricSpace M']
    [ChartedSpace H M'] [IsManifold I 1 M'] [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun (x : M') ↦ TangentSpace I x)]
    [IsRiemannianManifold I M'] [CompactSpace M'] [PreconnectedSpace M']
    {s : Set ℝ} (G : TimeMetric I M' s) {a : ℝ} (ha : a ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x))) (x y : M') :
    (∀ᵐ τ, τ ∈ interior s → DifferentiableAt ℝ (G.dist x y) τ) ∧
    (∀ τ ∈ interior s, ∀ d', HasDerivAt (G.dist x y) d' τ → |d'| ≤ G.κ * G.dist x y τ) :=
  ⟨G.dist_ae_differentiableAt x y (fun τ hτ => G.riemannianEDist_ne_top ha hτ hcont x y),
    fun τ hτ d' hd => G.abs_deriv_dist_le x y hτ
      (G.riemannianEDist_ne_top ha (interior_subset hτ) hcont x y) hd⟩

end DistanceInTime

section Danskin

/-- (2a) One-sided envelope bound (no hypothesis on `K`): if `F τ ≤ g τ k` for all `τ, k`, with
equality at `(τ₀, k₀)`, and `g(·, k₀)` has derivative `d₀` at `τ₀`, then for every `ε > 0`, near `τ₀`,
`F τ − F τ₀ ≤ d₀ (τ − τ₀) + ε |τ − τ₀|`.  Equivalently: the upper right Dini derivative of `F` at
`τ₀` is `≤ d₀` and the lower left Dini derivative is `≥ d₀`, for EVERY minimiser `k₀`. -/
theorem envelope_upper {K : Type*} (g : ℝ → K → ℝ) (F : ℝ → ℝ) (τ₀ : ℝ) (k₀ : K) (d₀ : ℝ)
    (hF : ∀ τ k, F τ ≤ g τ k) (h0 : F τ₀ = g τ₀ k₀)
    (hd : HasDerivAt (fun τ => g τ k₀) d₀ τ₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ τ in 𝓝 τ₀, F τ - F τ₀ ≤ d₀ * (τ - τ₀) + ε * |τ - τ₀| := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at hd
  filter_upwards [hd hε] with τ hτ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul] at hτ
  have h1 := hF τ k₀
  have h2 := le_abs_self (g τ k₀ - g τ₀ k₀ - (τ - τ₀) * d₀)
  rw [h0]; linarith

/-- (2b) Convergence of minimisers: `K` compact, `g τ₀ ·` lower semicontinuous, `g τ · → g τ₀ ·`
uniformly as `τ → τ₀`, `kmin τ` a minimiser of `g τ ·` for every `τ`, and the minimiser at `τ₀`
unique (`k₀`).  Then `kmin τ → k₀` as `τ → τ₀`. -/
theorem minimiser_tendsto {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : ℝ → K → ℝ) (kmin : ℝ → K) (τ₀ : ℝ) (k₀ : K)
    (hmin : ∀ τ k, g τ (kmin τ) ≤ g τ k)
    (hlsc : LowerSemicontinuous (g τ₀))
    (hunif : ∀ η > 0, ∀ᶠ τ in 𝓝 τ₀, ∀ k, |g τ k - g τ₀ k| ≤ η)
    (huniq : ∀ k, (∀ k', g τ₀ k ≤ g τ₀ k') → k = k₀) :
    Filter.Tendsto kmin (𝓝 τ₀) (𝓝 k₀) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro kstar hcl
  apply huniq
  intro k'
  -- `g τ₀ kstar ≤ g τ₀ k'`
  by_contra hlt
  push_neg at hlt
  set c := (g τ₀ k' + g τ₀ kstar) / 2 with hcdef
  have hc1 : c < g τ₀ kstar := by rw [hcdef]; linarith
  have hc2 : g τ₀ k' < c := by rw [hcdef]; linarith
  set η := (c - g τ₀ k') / 2 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hηe : 2 * η = c - g τ₀ k' := by rw [hηdef]; ring
  have hU : {k | c < g τ₀ k} ∈ 𝓝 kstar := hlsc kstar c hc1
  have hfreq := (mapClusterPt_iff_frequently.1 hcl) _ hU
  obtain ⟨τ, hτ1, hτ2⟩ := (hfreq.and_eventually (hunif η hη)).exists
  have h1 : c < g τ₀ (kmin τ) := hτ1
  have h2 := hτ2 (kmin τ)
  have h3 := hτ2 k'
  have h4 := hmin τ k'
  rw [abs_le] at h2 h3
  linarith [h2.1, h3.2]

/-- (2c) Two-sided envelope theorem with lower semicontinuity instead of continuity of `g`:
`K` compact, `g τ₀ ·` lower semicontinuous, `g τ · → g τ₀ ·` uniformly, minimisers `kmin τ`,
unique minimiser `k₀` at `τ₀`, `g(·, k₀)` with derivative `d₀` at `τ₀`, and the UNIFORM ONE-SIDED
FIRST-ORDER BOUND (HYPOTHESIS `hfirst`): for every `ε > 0` there are a neighbourhood `U` of `k₀` and
`δ > 0` with `g τ k − g τ₀ k ≥ d₀ (τ − τ₀) − ε |τ − τ₀|` for `k ∈ U`, `|τ − τ₀| < δ`.  Then `F` is
differentiable at `τ₀` with derivative `d₀`. -/
theorem envelope_lsc {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : ℝ → K → ℝ) (F : ℝ → ℝ) (kmin : ℝ → K) (τ₀ : ℝ) (k₀ : K) (d₀ : ℝ)
    (hF : ∀ τ k, F τ ≤ g τ k) (hFmin : ∀ τ, F τ = g τ (kmin τ))
    (hlsc : LowerSemicontinuous (g τ₀))
    (hunif : ∀ η > 0, ∀ᶠ τ in 𝓝 τ₀, ∀ k, |g τ k - g τ₀ k| ≤ η)
    (huniq : ∀ k, (∀ k', g τ₀ k ≤ g τ₀ k') → k = k₀)
    (hd : HasDerivAt (fun τ => g τ k₀) d₀ τ₀)
    (hfirst : ∀ ε > 0, ∃ U ∈ 𝓝 k₀, ∃ δ > 0, ∀ k ∈ U, ∀ τ, |τ - τ₀| < δ →
      d₀ * (τ - τ₀) - ε * |τ - τ₀| ≤ g τ k - g τ₀ k) :
    HasDerivAt F d₀ τ₀ := by
  have hmin : ∀ τ k, g τ (kmin τ) ≤ g τ k := fun τ k => (hFmin τ).symm ▸ hF τ k
  have hk0 : F τ₀ = g τ₀ k₀ := by
    have := huniq (kmin τ₀) (hmin τ₀)
    rw [hFmin, this]
  have hT := minimiser_tendsto g kmin τ₀ k₀ hmin hlsc hunif huniq
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨U, hU, δ, hδ, hb⟩ := hfirst ε hε
  filter_upwards [envelope_upper g F τ₀ k₀ d₀ hF hk0 hd ε hε, hT hU,
    Metric.ball_mem_nhds τ₀ hδ] with τ hup hkU hball
  rw [Metric.mem_ball, Real.dist_eq] at hball
  have hlow := hb (kmin τ) hkU τ hball
  have h1 : g τ (kmin τ) - g τ₀ (kmin τ) ≤ F τ - F τ₀ := by
    rw [hFmin τ]; linarith [hF τ₀ (kmin τ)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_le]
  constructor <;> linarith

/-- (2d) The hypothesis `hfirst` of `envelope_lsc` holds (even two-sided) when `g(·, k)` has
derivative `g' τ k` for all `τ, k` and `g'` is jointly continuous at `(τ₀, k₀)`, with `d₀ = g' τ₀ k₀`
(mean value inequality). -/
theorem first_order_of_continuous_deriv {K : Type*} [TopologicalSpace K]
    (g g' : ℝ → K → ℝ) (τ₀ : ℝ) (k₀ : K)
    (hd : ∀ τ k, HasDerivAt (fun σ => g σ k) (g' τ k) τ)
    (hc : ContinuousAt (fun p : ℝ × K => g' p.1 p.2) (τ₀, k₀)) :
    ∀ ε > 0, ∃ U ∈ 𝓝 k₀, ∃ δ > 0, ∀ k ∈ U, ∀ τ, |τ - τ₀| < δ →
      |g τ k - g τ₀ k - g' τ₀ k₀ * (τ - τ₀)| ≤ ε * |τ - τ₀| := by
  intro ε hε
  have hN : {p : ℝ × K | |g' p.1 p.2 - g' τ₀ k₀| < ε} ∈ 𝓝 (τ₀, k₀) := by
    have : ContinuousAt (fun p : ℝ × K => |g' p.1 p.2 - g' τ₀ k₀|) (τ₀, k₀) :=
      ((hc.sub continuousAt_const).abs)
    exact this.eventually (gt_mem_nhds (by simp [hε]))
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hN
  obtain ⟨A, hA, B, hB, hAB⟩ := hN
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨B, hB, δ, hδ, fun k hk τ hτ => ?_⟩
  -- mean value inequality for `σ ↦ g σ k − g' τ₀ k₀ σ` on the segment
  let φ : ℝ → ℝ := fun σ => g σ k - g' τ₀ k₀ * σ
  have hφ : ∀ σ ∈ Metric.ball τ₀ δ, HasDerivWithinAt φ (g' σ k - g' τ₀ k₀) (Metric.ball τ₀ δ) σ :=
    fun σ _ => ((hd σ k).sub ((hasDerivAt_id σ).const_mul (g' τ₀ k₀))).hasDerivWithinAt.congr_deriv
      (by ring)
  have hb : ∀ σ ∈ Metric.ball τ₀ δ, ‖g' σ k - g' τ₀ k₀‖ ≤ ε := fun σ hσ => by
    rw [Real.norm_eq_abs]
    exact (hAB (Set.mk_mem_prod (hball hσ) hk)).le
  have hτb : τ ∈ Metric.ball τ₀ δ := by rw [Metric.mem_ball, Real.dist_eq]; exact hτ
  have h := (convex_ball τ₀ δ).norm_image_sub_le_of_norm_hasDerivWithin_le hφ hb
    (Metric.mem_ball_self hδ) hτb
  simp only [φ, Real.norm_eq_abs] at h
  calc |g τ k - g τ₀ k - g' τ₀ k₀ * (τ - τ₀)|
      = |g τ k - g' τ₀ k₀ * τ - (g τ₀ k - g' τ₀ k₀ * τ₀)| := by congr 1; ring
    _ ≤ ε * |τ - τ₀| := h

end Danskin

/-! ### Symmetry and triangle inequality of the time-dependent distance, joint continuity, and
Fubini for the almost-everywhere differentiability in time (block A116)

(1) `quadENorm g` is homogeneous (`ENormSMulClass`), with no positivity hypothesis; hence Mathlib's
`riemannianEDist_comm` and `riemannianEDist_triangle` hold for `G.norms τ`.  On a compact connected
Riemannian manifold, `d_τ ≤ C · edist`, and `(x, y) ↦ d_τ(x, y)` is Lipschitz, hence continuous.
(2) `(τ, x, y) ↦ d_τ(x, y)` is continuous on `s × M × M`.
(3) Fubini: for every s-finite measure `ν` on `M × M` (with a Borel-type σ-algebra), for
Lebesgue-almost every `τ`, for `ν`-almost every pair, `τ ↦ d_τ(x,y)` is differentiable at `τ` if
`τ ∈ interior s`.  (The other order, for EVERY pair at almost every `τ`, is
`TimeMetric.dist_ae_differentiableAt` of block A115.) -/

section TimeDistanceMetric

/-- `quadENorm g` is homogeneous: `‖r • v‖ = |r| ‖v‖` (no positivity of `g` needed: the square root
of a negative number is `0` on both sides). -/
theorem quadENorm_smulClass (g : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (x : M) :
    @ENormSMulClass ℝ (TangentSpace I x) _ (quadENorm g x) _ := by
  letI := quadENorm g x
  refine ⟨fun r v => ?_⟩
  show ENNReal.ofReal (Real.sqrt (g x (r • v) (r • v))) = ‖r‖ₑ * ENNReal.ofReal (Real.sqrt (g x v v))
  have e : g x (r • v) (r • v) = r ^ 2 * g x v v := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs, ENNReal.ofReal_mul (abs_nonneg r),
    Real.enorm_eq_ofReal_abs]

theorem TimeMetric.redist_comm {s : Set ℝ} (G : TimeMetric I M s) (τ : ℝ) (x y : M) :
    (letI := G.norms τ; Manifold.riemannianEDist I x y)
      = (letI := G.norms τ; Manifold.riemannianEDist I y x) := by
  letI := G.norms τ
  haveI : ∀ z : M, ENormSMulClass ℝ (TangentSpace I z) := fun z => quadENorm_smulClass (G.g τ) z
  exact Manifold.riemannianEDist_comm

theorem TimeMetric.redist_triangle {s : Set ℝ} (G : TimeMetric I M s) (τ : ℝ) (x y z : M) :
    (letI := G.norms τ; Manifold.riemannianEDist I x z)
      ≤ (letI := G.norms τ; Manifold.riemannianEDist I x y)
        + (letI := G.norms τ; Manifold.riemannianEDist I y z) := by
  letI := G.norms τ
  haveI : ∀ z : M, ENormSMulClass ℝ (TangentSpace I z) := fun z => quadENorm_smulClass (G.g τ) z
  exact Manifold.riemannianEDist_triangle

theorem TimeMetric.dist_comm {s : Set ℝ} (G : TimeMetric I M s) (x y : M) (τ : ℝ) :
    G.dist x y τ = G.dist y x τ := by
  unfold TimeMetric.dist; rw [G.redist_comm τ x y]

/-- Real triangle inequality (finite distances). -/
theorem TimeMetric.dist_triangle {s : Set ℝ} (G : TimeMetric I M s) (x y z : M) (τ : ℝ)
    (h1 : (letI := G.norms τ; Manifold.riemannianEDist I x y) ≠ ⊤)
    (h2 : (letI := G.norms τ; Manifold.riemannianEDist I y z) ≠ ⊤) :
    G.dist x z τ ≤ G.dist x y τ + G.dist y z τ := by
  unfold TimeMetric.dist
  rw [← ENNReal.toReal_add h1 h2]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1, h2⟩) (G.redist_triangle τ x y z)

/-- `|d(x,y) − d(x',y')| ≤ d(x,x') + d(y,y')` for finite distances. -/
theorem TimeMetric.dist_sub_le {s : Set ℝ} (G : TimeMetric I M s) (τ : ℝ)
    (hfin : ∀ x y : M, (letI := G.norms τ; Manifold.riemannianEDist I x y) ≠ ⊤) (x y x' y' : M) :
    |G.dist x y τ - G.dist x' y' τ| ≤ G.dist x x' τ + G.dist y y' τ := by
  have a1 := G.dist_triangle x x' y τ (hfin _ _) (hfin _ _)
  have a2 := G.dist_triangle x' y' y τ (hfin _ _) (hfin _ _)
  have b1 := G.dist_triangle x' x y' τ (hfin _ _) (hfin _ _)
  have b2 := G.dist_triangle x y y' τ (hfin _ _) (hfin _ _)
  have c1 := G.dist_comm y' y τ
  have c2 := G.dist_comm x' x τ
  rw [abs_le]; constructor <;> linarith

variable {M' : Type*} [PseudoEMetricSpace M'] [ChartedSpace H M'] [IsManifold I 1 M']
  [RiemannianBundle (fun (x : M') ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun (x : M') ↦ TangentSpace I x)]
  [IsRiemannianManifold I M'] [CompactSpace M'] [PreconnectedSpace M']

/-- On a compact connected Riemannian manifold, for a `TimeMetric` whose metric is continuous in the
base point at one time `a ∈ s`: at every time `τ ∈ s`, `d_τ ≤ C · edist` with `C < ∞`. -/
theorem TimeMetric.redist_le_edist {s : Set ℝ} (G : TimeMetric I M' s) {a τ : ℝ} (ha : a ∈ s)
    (hτ : τ ∈ s) (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x))) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x y : M',
      (letI := G.norms τ; Manifold.riemannianEDist I x y) ≤ C * edist x y := by
  obtain ⟨c, hc0, hct, h⟩ := quadENorm_le_bundle (G.g a) hcont
  refine ⟨ENNReal.ofReal (Real.exp (G.κ * |τ - a|)) * c,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hct, fun x y => ?_⟩
  have h1 := riemannianEDist_le_mul (I := I) (M := M')
      (fun x => SeminormedAddGroup.toContinuousENorm.toENorm) (quadENorm (G.g a)) c hc0 hct h x y
  have h2 := G.riemannianEDist_le ha hτ x y
  calc (letI := G.norms τ; Manifold.riemannianEDist I x y)
      ≤ ENNReal.ofReal (Real.exp (G.κ * |τ - a|)) * (letI := G.norms a; Manifold.riemannianEDist I x y) :=
        h2
    _ ≤ ENNReal.ofReal (Real.exp (G.κ * |τ - a|)) * (c * Manifold.riemannianEDist I x y) := by
        gcongr; exact h1
    _ = ENNReal.ofReal (Real.exp (G.κ * |τ - a|)) * c * edist x y := by
        rw [IsRiemannianManifold.out (I := I) x y, mul_assoc]

/-- (1) Continuity in the pair: `(x, y) ↦ d_τ(x, y)` is Lipschitz (product `edist`), hence
continuous, on a compact connected Riemannian manifold. -/
theorem TimeMetric.dist_lipschitz_pair {s : Set ℝ} (G : TimeMetric I M' s) {a τ : ℝ} (ha : a ∈ s)
    (hτ : τ ∈ s) (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x))) :
    ∃ K : NNReal, LipschitzWith K (fun p : M' × M' => G.dist p.1 p.2 τ) := by
  obtain ⟨C, hC, hle⟩ := G.redist_le_edist ha hτ hcont
  have hfin : ∀ x y : M', (letI := G.norms τ; Manifold.riemannianEDist I x y) ≠ ⊤ :=
    fun x y => G.riemannianEDist_ne_top ha hτ hcont x y
  refine ⟨(2 * C).toNNReal, fun p q => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hC), edist_dist, Real.dist_eq]
  have h := G.dist_sub_le τ hfin p.1 p.2 q.1 q.2
  have e1 : ENNReal.ofReal (G.dist p.1 q.1 τ) = (letI := G.norms τ; Manifold.riemannianEDist I p.1 q.1) :=
    ENNReal.ofReal_toReal (hfin _ _)
  have e2 : ENNReal.ofReal (G.dist p.2 q.2 τ) = (letI := G.norms τ; Manifold.riemannianEDist I p.2 q.2) :=
    ENNReal.ofReal_toReal (hfin _ _)
  calc ENNReal.ofReal |G.dist p.1 p.2 τ - G.dist q.1 q.2 τ|
      ≤ ENNReal.ofReal (G.dist p.1 q.1 τ + G.dist p.2 q.2 τ) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (G.dist p.1 q.1 τ) + ENNReal.ofReal (G.dist p.2 q.2 τ) :=
        ENNReal.ofReal_add (G.dist_nonneg _ _ _) (G.dist_nonneg _ _ _)
    _ ≤ C * edist p.1 q.1 + C * edist p.2 q.2 := by rw [e1, e2]; gcongr <;> exact hle _ _
    _ ≤ C * edist p q + C * edist p q := by
        rw [Prod.edist_eq]; gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = 2 * C * edist p q := by ring

theorem TimeMetric.dist_continuous_pair {s : Set ℝ} (G : TimeMetric I M' s) {a τ : ℝ} (ha : a ∈ s)
    (hτ : τ ∈ s) (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x))) :
    Continuous (fun p : M' × M' => G.dist p.1 p.2 τ) := by
  obtain ⟨K, hK⟩ := G.dist_lipschitz_pair ha hτ hcont
  exact hK.continuous

/-- (2) Joint continuity of `(τ, x, y) ↦ d_τ(x, y)` on `s × (M × M)`. -/
theorem TimeMetric.dist_continuousOn {s : Set ℝ} (G : TimeMetric I M' s) {a : ℝ} (ha : a ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x))) :
    ContinuousOn (fun q : ℝ × (M' × M') => G.dist q.2.1 q.2.2 q.1) (s ×ˢ univ) := by
  rintro ⟨τ₀, p₀⟩ ⟨hτ₀, -⟩
  have hc0 := G.dist_continuous_pair ha hτ₀ hcont
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hc0.continuousOn
  set f0 : M' × M' → ℝ := fun p => G.dist p.1 p.2 τ₀
  let A : ℝ × (M' × M') → ℝ := fun q =>
    (Real.exp (G.κ * |q.1 - τ₀|) - 1) * B + Dist.dist (f0 q.2) (f0 p₀)
  have hAc : Continuous A := by
    have h1 : Continuous (fun q : ℝ × (M' × M') => f0 q.2) := hc0.comp continuous_snd
    exact (((Real.continuous_exp.comp (continuous_const.mul
      ((continuous_fst.sub continuous_const).abs))).sub continuous_const).mul
      continuous_const).add (h1.dist continuous_const)
  have hA0 : A (τ₀, p₀) = 0 := by simp [A]
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => _root_.dist_nonneg) ?_
    (by rw [← hA0]; exact (hAc.tendsto _).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with q hq
  obtain ⟨hq1, -⟩ := hq
  have hfin : (letI := G.norms τ₀; Manifold.riemannianEDist I q.2.1 q.2.2) ≠ ⊤ :=
    G.riemannianEDist_ne_top ha hτ₀ hcont _ _
  have hl := G.dist_lip q.2.1 q.2.2 hτ₀ hq1 hfin
  have hb : f0 q.2 ≤ B := by
    have := hB q.2 (mem_univ _); rw [Real.norm_eq_abs] at this; exact (le_abs_self _).trans this
  have hexp : 0 ≤ Real.exp (G.κ * |q.1 - τ₀|) - 1 := by
    have := Real.one_le_exp (mul_nonneg G.κ_nonneg (abs_nonneg (q.1 - τ₀))); linarith
  have hfq : f0 q.2 = G.dist q.2.1 q.2.2 τ₀ := rfl
  have hp0 : G.dist p₀.1 p₀.2 τ₀ = f0 p₀ := rfl
  show Dist.dist (G.dist q.2.1 q.2.2 q.1) (G.dist p₀.1 p₀.2 τ₀)
    ≤ (Real.exp (G.κ * |q.1 - τ₀|) - 1) * B + Dist.dist (f0 q.2) (f0 p₀)
  calc Dist.dist (G.dist q.2.1 q.2.2 q.1) (G.dist p₀.1 p₀.2 τ₀)
      ≤ Dist.dist (G.dist q.2.1 q.2.2 q.1) (f0 q.2) + Dist.dist (f0 q.2) (f0 p₀) := by
        rw [hp0]; exact _root_.dist_triangle _ _ _
    _ ≤ (Real.exp (G.κ * |q.1 - τ₀|) - 1) * B + Dist.dist (f0 q.2) (f0 p₀) := by
        refine add_le_add ?_ le_rfl
        rw [Real.dist_eq, hfq]
        exact hl.trans (mul_le_mul_of_nonneg_left hb hexp)

/-- (3), one interval: for `[p, q] ⊆ s`, for almost every `τ`, for `ν`-almost every pair,
`τ ∈ (p, q)` implies differentiability of `τ ↦ d_τ(x, y)` at `τ`. -/
theorem TimeMetric.dist_fubini_Icc [MeasurableSpace (M' × M')] [OpensMeasurableSpace (M' × M')]
    {s : Set ℝ} (G : TimeMetric I M' s) {a : ℝ} (ha : a ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x)))
    (ν : Measure (M' × M')) [SFinite ν] {p q : ℝ} (hpq : p ≤ q) (hsub : Icc p q ⊆ s) :
    ∀ᵐ τ, ∀ᵐ pr ∂ν, τ ∈ Ioo p q → DifferentiableAt ℝ (G.dist pr.1 pr.2) τ := by
  set ft : M' × M' → ℝ → ℝ := fun pr τ => G.dist pr.1 pr.2 (projIcc p q hpq τ)
  have hjoint := G.dist_continuousOn ha hcont
  have hft : Continuous (Function.uncurry ft) := by
    have hφ : Continuous (fun z : (M' × M') × ℝ => (((projIcc p q hpq z.2) : ℝ), z.1)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)).prodMk continuous_fst
    exact hjoint.comp_continuous hφ (fun z => ⟨hsub (projIcc p q hpq z.2).2, mem_univ _⟩)
  have heq : ∀ pr τ, τ ∈ Ioo p q →
      (DifferentiableAt ℝ (ft pr) τ ↔ DifferentiableAt ℝ (G.dist pr.1 pr.2) τ) := by
    intro pr τ hτ
    apply Filter.EventuallyEq.differentiableAt_iff
    filter_upwards [Icc_mem_nhds hτ.1 hτ.2] with u hu
    simp only [ft, projIcc_of_mem hpq hu]
  have hM : MeasurableSet {z : (M' × M') × ℝ | DifferentiableAt ℝ (ft z.1) z.2} :=
    measurableSet_of_differentiableAt_with_param ℝ hft
  set Bad : Set ((M' × M') × ℝ) :=
    {z | z.2 ∈ Ioo p q} ∩ {z : (M' × M') × ℝ | DifferentiableAt ℝ (ft z.1) z.2}ᶜ with hBad
  have hBm : MeasurableSet Bad := (measurableSet_Ioo.preimage measurable_snd).inter hM.compl
  have hslice : ∀ pr : M' × M', volume (Prod.mk pr ⁻¹' Bad) = 0 := by
    intro pr
    have hae := G.dist_ae_differentiableAt_Icc pr.1 pr.2 hsub
      (fun τ hτ => G.riemannianEDist_ne_top ha (hsub hτ) hcont _ _)
    rw [ae_iff] at hae
    refine measure_mono_null (fun τ hτ => ?_) hae
    simp only [hBad, mem_preimage, mem_inter_iff, mem_setOf_eq, mem_compl_iff] at hτ
    simp only [mem_setOf_eq, Classical.not_imp]
    exact ⟨hτ.1, fun hd => hτ.2 ((heq pr τ hτ.1).2 hd)⟩
  have h1 : (ν.prod volume) Bad = 0 :=
    Measure.measure_prod_null_of_ae_null hBm (Filter.Eventually.of_forall hslice)
  have h2 : (volume.prod ν) (Prod.swap ⁻¹' Bad) = 0 := by
    rw [← Measure.prod_swap (μ := ν) (ν := volume),
      Measure.map_apply measurable_swap (hBm.preimage measurable_swap)]
    have : Prod.swap ⁻¹' (Prod.swap ⁻¹' Bad) = Bad := by
      ext z; simp
    rw [this, h1]
  filter_upwards [Measure.measure_ae_null_of_prod_null h2] with τ hτ
  rw [ae_iff]
  refine measure_mono_null (fun pr hpr => ?_) hτ
  simp only [mem_setOf_eq, Classical.not_imp] at hpr
  simp only [hBad, mem_preimage, Prod.swap_prod_mk, mem_inter_iff, mem_setOf_eq, mem_compl_iff]
  exact ⟨hpr.1, fun hd => hpr.2 ((heq pr τ hpr.1).1 hd)⟩

/-- (3) Fubini, both orders: on a compact connected Riemannian manifold, for a `TimeMetric` whose
metric is continuous in the base point at one time `a ∈ s`, and for every s-finite measure `ν` on
`M × M` (σ-algebra containing the open sets):
* for EVERY pair `(x, y)`, for Lebesgue-almost every `τ ∈ interior s`, `τ ↦ d_τ(x,y)` is
  differentiable at `τ`;
* for Lebesgue-almost every `τ`, for `ν`-almost every pair, if `τ ∈ interior s`, then
  `τ ↦ d_τ(x,y)` is differentiable at `τ`. -/
theorem TimeMetric.dist_fubini [MeasurableSpace (M' × M')] [OpensMeasurableSpace (M' × M')]
    {s : Set ℝ} (G : TimeMetric I M' s) {a : ℝ} (ha : a ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (G.g a x)))
    (ν : Measure (M' × M')) [SFinite ν] :
    (∀ x y : M', ∀ᵐ τ, τ ∈ interior s → DifferentiableAt ℝ (G.dist x y) τ) ∧
    (∀ᵐ τ, ∀ᵐ pr ∂ν, τ ∈ interior s → DifferentiableAt ℝ (G.dist pr.1 pr.2) τ) := by
  refine ⟨fun x y => G.dist_ae_differentiableAt x y
    (fun τ hτ => G.riemannianEDist_ne_top ha hτ hcont x y), ?_⟩
  have hall : ∀ pq : ℚ × ℚ, ∀ᵐ τ, Icc (pq.1 : ℝ) pq.2 ⊆ s →
      ∀ᵐ pr ∂ν, τ ∈ Ioo (pq.1 : ℝ) pq.2 → DifferentiableAt ℝ (G.dist pr.1 pr.2) τ := by
    intro pq
    by_cases h : Icc (pq.1 : ℝ) pq.2 ⊆ s
    · by_cases hpq : (pq.1 : ℝ) ≤ pq.2
      · filter_upwards [G.dist_fubini_Icc ha hcont ν hpq h] with τ hτ _ using hτ
      · refine Filter.Eventually.of_forall fun τ _ => Filter.Eventually.of_forall fun pr hτ => ?_
        exact absurd (hτ.1.le.trans hτ.2.le) hpq
    · exact Filter.Eventually.of_forall fun τ h' => absurd h' h
  rw [← ae_all_iff] at hall
  filter_upwards [hall] with τ hτ
  by_cases hint : τ ∈ interior s
  · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show τ - ε < τ by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show τ < τ + ε by linarith)
    have hsub : Icc ((p, q).1 : ℝ) (p, q).2 ⊆ s := by
      intro u hu
      dsimp only at hu
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    filter_upwards [hτ (p, q) hsub] with pr hpr _ using hpr ⟨hp2, hq1⟩
  · exact Filter.Eventually.of_forall fun pr h => absurd h hint

end TimeDistanceMetric
end CTG.ManifoldDistance
