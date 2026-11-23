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

What this is NOT: no time-dependent metric tensor occurs as an object; the second step is not yet
applied to a family of norms on the tangent bundle and combined with the first; nothing on volume
growth, injectivity radius, curvature or the Laplace–Beltrami operator.
No `sorry`, no `axiom`, no `native_decide`.
-/

open Set MeasureTheory
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

end CTG.ManifoldDistance
