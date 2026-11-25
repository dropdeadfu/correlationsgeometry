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

end CTG.ManifoldDistance
