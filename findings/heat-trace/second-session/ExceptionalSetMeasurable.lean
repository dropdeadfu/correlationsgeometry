import Mathlib

/-!
# Measurability of exceptional sets defined by a supremum over a parameter

Paper: M. Neuberger, *From Correlations to Geometry*, Appendix G. Several statements there bound, for
random points `X_j`, a quantity uniformly in a parameter `x` of a compact space, "except on an event of
small probability". The exceptional event has the form `{ω | ∃ x, c < |g x ω|}`, an uncountable union.
This file shows that it is measurable as soon as

* `g x ω` is continuous in `x` for every `ω`,
* `g x ω` is measurable in `ω` for every `x`,
* the parameter space is separable.

The proof replaces the parameter space by a countable dense subset: for fixed `ω` the set
`{x | c < |g x ω|}` is open, so it is non-empty if and only if it meets the dense subset.

* `measurableSet_exists_lt_abs`: the general statement;
* `measurableSet_exists_lt`: the same without the absolute value;
* `measurableSet_exists_lt_abs_sum_sub`: the form used for the normalisation event,
  `{ω | ∃ x, c < |∑_{j<N} f x (X_j ω) − N|}`.

Compactness of the parameter space is not needed. Checked with the Mathlib of the root project
(`lake env lean` from the repository root); written for Mathlib v4.36, so names may differ slightly
in older versions.
-/

open MeasureTheory Set

namespace CorrelationsGeometry

variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]

/-- If `g x ω` is continuous in `x` and measurable in `ω`, and the parameter space is separable,
then `{ω | ∃ x, c < g x ω}` is measurable. -/
theorem measurableSet_exists_lt (g : E → Ω → ℝ) (hcont : ∀ ω, Continuous fun x => g x ω)
    (hmeas : ∀ x, Measurable (g x)) (c : ℝ) : MeasurableSet {ω | ∃ x, c < g x ω} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  have h : {ω | ∃ x, c < g x ω} = ⋃ x ∈ D, {ω | c < g x ω} := by
    ext ω
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨x, hx⟩
      have hopen : IsOpen {y | c < g y ω} := isOpen_lt continuous_const (hcont ω)
      obtain ⟨y, hyD, hy⟩ := hDd.exists_mem_open hopen ⟨x, hx⟩
      exact ⟨y, hyD, hy⟩
    · rintro ⟨x, -, hx⟩
      exact ⟨x, hx⟩
  rw [h]
  exact MeasurableSet.biUnion hDc fun x _ => measurableSet_lt measurable_const (hmeas x)

/-- If `g x ω` is continuous in `x` and measurable in `ω`, and the parameter space is separable,
then the exceptional set `{ω | ∃ x, c < |g x ω|}` is measurable. -/
theorem measurableSet_exists_lt_abs (g : E → Ω → ℝ) (hcont : ∀ ω, Continuous fun x => g x ω)
    (hmeas : ∀ x, Measurable (g x)) (c : ℝ) : MeasurableSet {ω | ∃ x, c < |g x ω|} :=
  measurableSet_exists_lt (fun x ω => |g x ω|) (fun ω => continuous_abs.comp (hcont ω))
    (fun x => continuous_abs.measurable.comp (hmeas x)) c

/-- **The normalisation event.** For a kernel `f x y` that is continuous in `x` and measurable in
`y`, measurable points `X_j` and a separable parameter space, the event
`{ω | ∃ x, c < |∑_{j<N} f x (X_j ω) − N|}` is measurable. -/
theorem measurableSet_exists_lt_abs_sum_sub {F : Type*} [MeasurableSpace F] (f : E → F → ℝ)
    (hcont : ∀ y, Continuous fun x => f x y) (hmeas : ∀ x, Measurable (f x))
    (X : ℕ → Ω → F) (hX : ∀ j, Measurable (X j)) (N : ℕ) (c : ℝ) :
    MeasurableSet {ω | ∃ x, c < |∑ j ∈ Finset.range N, f x (X j ω) - (N : ℝ)|} := by
  refine measurableSet_exists_lt_abs
    (fun x ω => ∑ j ∈ Finset.range N, f x (X j ω) - (N : ℝ)) ?_ ?_ c
  · intro ω
    -- `continuous_finsetSum` is called `continuous_finset_sum` in older versions of Mathlib
    exact (continuous_finsetSum _ fun j _ => hcont (X j ω)).sub continuous_const
  · intro x
    exact (Finset.measurable_sum _ fun j _ => (hmeas x).comp (hX j)).sub measurable_const

end CorrelationsGeometry
