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

end CTG.ManifoldDistance
