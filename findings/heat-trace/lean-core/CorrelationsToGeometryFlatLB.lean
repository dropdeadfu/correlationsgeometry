/-
Twenty-third file (Mathlib only): the flat core of `thm:LB`.  Namespace `CTG.FlatLB`; check with
`./check_flat_lb.sh`.
For the averaging operator `A_ξ f(x) = ∫ k(z) f(x + ξ z) dμ / ∫ k` on `EuclideanSpace ℝ (Fin n)`, a kernel with
vanishing first moments and second moments `δ_ij m₂ ∫k`, and `f` with a third-order Taylor bound along lines
(structure `Taylor3`):  `|A_ξ f(x) − f(x) − (ξ²/2) m₂ Δf(x)| ≤ M₃ ξ³ μ₃/(6K₀)` (`avgOp_expansion`) and
`|(2/(m₂ ξ²))(f − A_ξ f)(x) + Δf(x)| ≤ M₃ ξ μ₃/(3 m₂ K₀)` (`flat_LB`), so `c_h = m₂`.  For radial kernels
`k(z) = h(‖z‖)` with Lebesgue measure the moment conditions are PROVED (`radial_kern`).  Difference quotients
in a parameter: `avgOp_dq_expansion`.
Here `Δf` is the sum of the second directional derivatives of the interface `Taylor3`, not Mathlib's `Laplacian`;
that a `C³` function with bounded third derivative satisfies `Taylor3` is NOT formalised.  NOT formalised:
anything on a manifold (normal coordinates, volume density, non-constant sampling density, Laplace–Beltrami).
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import Mathlib

open MeasureTheory Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatLB

/-! ### One-dimensional Taylor bound by three comparisons -/

/-- From `g(0) = 0` and `|g'(t)| ≤ c tⁿ` on `[0,1]`: `|g(t)| ≤ c/(n+1) · t^{n+1}` on `[0,1]`. -/
theorem step_bound (g g' : ℝ → ℝ) (hg : ∀ t, HasDerivAt g (g' t) t) (h0 : g 0 = 0) (c : ℝ)
    (n : ℕ) (hb : ∀ t ∈ Icc (0:ℝ) 1, |g' t| ≤ c * t ^ n) :
    ∀ t ∈ Icc (0:ℝ) 1, |g t| ≤ c / (n + 1) * t ^ (n + 1) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun t => (hg t).continuousAt
  have hB : ∀ t, HasDerivAt (fun t : ℝ => c / (n + 1) * t ^ (n + 1)) (c * t ^ n) t := fun t => by
    have h1 := (hasDerivAt_pow (n + 1) t).const_mul (c / (n + 1))
    refine h1.congr_deriv ?_
    rw [Nat.add_sub_cancel]
    push_cast
    first | (field_simp; ring) | field_simp | ring
  have hBc : Continuous fun t : ℝ => c / (n + 1) * t ^ (n + 1) := by fun_prop
  intro t ht
  have up := image_le_of_deriv_right_le_deriv_boundary (f := g) (f' := g') (a := 0) (b := 1)
    hgc.continuousOn (fun x _ => (hg x).hasDerivWithinAt)
    (B := fun t : ℝ => c / (n + 1) * t ^ (n + 1)) (B' := fun t => c * t ^ n)
    (by simp [h0]) hBc.continuousOn (fun x _ => (hB x).hasDerivWithinAt)
    (fun x hx => (le_abs_self _).trans (hb x (Ico_subset_Icc_self hx))) ht
  have lo := image_le_of_deriv_right_le_deriv_boundary (f := fun t => -g t) (f' := fun t => -g' t)
    (a := 0) (b := 1) hgc.neg.continuousOn (fun x _ => (hg x).neg.hasDerivWithinAt)
    (B := fun t : ℝ => c / (n + 1) * t ^ (n + 1)) (B' := fun t => c * t ^ n)
    (by simp [h0]) hBc.continuousOn (fun x _ => (hB x).hasDerivWithinAt)
    (fun x hx => (neg_le_abs _).trans (hb x (Ico_subset_Icc_self hx))) ht
  exact abs_le.2 ⟨by simp only at lo; linarith, up⟩

/-- **Taylor bound of order three on `[0,1]`**: `φ' = d₁`, `d₁' = d₂`, `d₂' = d₃`, `|d₃| ≤ B` on
`[0,1]` ⇒ `|φ(1) − φ(0) − d₁(0) − d₂(0)/2| ≤ B/6`. -/
theorem taylor3 (φ d₁ d₂ d₃ : ℝ → ℝ) (h1 : ∀ t, HasDerivAt φ (d₁ t) t)
    (h2 : ∀ t, HasDerivAt d₁ (d₂ t) t) (h3 : ∀ t, HasDerivAt d₂ (d₃ t) t) (B : ℝ)
    (hB : ∀ t ∈ Icc (0:ℝ) 1, |d₃ t| ≤ B) :
    |φ 1 - φ 0 - d₁ 0 - d₂ 0 / 2| ≤ B / 6 := by
  have s1 := step_bound (fun t => d₂ t - d₂ 0) d₃ (fun t => (h3 t).sub_const _) (by simp) B 0
    (fun t ht => by simpa using hB t ht)
  have s2 := step_bound (fun t => d₁ t - d₁ 0 - t * d₂ 0) (fun t => d₂ t - d₂ 0)
    (fun t => (((h2 t).sub_const (d₁ 0)).sub ((hasDerivAt_id t).mul_const (d₂ 0))).congr_deriv
      (by simp)) (by simp) (B / (0 + 1)) 1 (fun t ht => by
        have := s1 t ht; norm_num at this ⊢; linarith)
  have s3 := step_bound (fun t => φ t - φ 0 - t * d₁ 0 - t ^ 2 / 2 * d₂ 0)
    (fun t => d₁ t - d₁ 0 - t * d₂ 0)
    (fun t => by
      have h := (((h1 t).sub_const (φ 0)).sub ((hasDerivAt_id t).mul_const (d₁ 0))).sub
        (((hasDerivAt_pow 2 t).div_const 2).mul_const (d₂ 0))
      exact h.congr_deriv (by first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp))
      (by simp) (B / (0 + 1) / (1 + 1)) 2 (fun t ht => by
        have := s2 t ht; norm_num at this ⊢; linarith)
  have := s3 1 ⟨zero_le_one, le_rfl⟩
  have e : φ 1 - φ 0 - 1 * d₁ 0 - 1 ^ 2 / 2 * d₂ 0 = φ 1 - φ 0 - d₁ 0 - d₂ 0 / 2 := by ring
  simp only at this
  rw [e] at this
  refine this.trans (le_of_eq ?_)
  first | (norm_num; ring) | norm_num

/-! ### Functions with three directional derivatives -/

/-- HYPOTHESES on `f`: directional derivatives along lines up to order three, with the first two
given by a gradient `g` and a Hessian `H`, and `|D³f(y)[v,v,v]| ≤ M₃ |v|³`. -/
structure Taylor3 (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (M₃ : ℝ) where
  g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ
  H : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ
  D3 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ
  cont : Continuous f
  d1 : ∀ x v t, HasDerivAt (fun s : ℝ => f (x + s • v)) (∑ i, v i * g i (x + t • v)) t
  d2 : ∀ x v t, HasDerivAt (fun s : ℝ => ∑ i, v i * g i (x + s • v))
    (∑ i, ∑ j, v i * v j * H i j (x + t • v)) t
  d3 : ∀ x v t, HasDerivAt (fun s : ℝ => ∑ i, ∑ j, v i * v j * H i j (x + s • v))
    (D3 (x + t • v) v) t
  bd3 : ∀ y v, |D3 y v| ≤ M₃ * ‖v‖ ^ 3

variable {n : ℕ}

/-- The Laplacian of `f`: the sum of the second directional derivatives along the coordinate vectors. -/
def lapl {f : EuclideanSpace ℝ (Fin n) → ℝ} {M₃ : ℝ} (T : Taylor3 n f M₃)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, T.H i i x

/-- Pointwise Taylor bound: `|f(x+v) − f(x) − Df(x)v − ½D²f(x)[v,v]| ≤ M₃|v|³/6`. -/
theorem Taylor3.pointwise {f : EuclideanSpace ℝ (Fin n) → ℝ} {M₃ : ℝ} (T : Taylor3 n f M₃)
    (x v : EuclideanSpace ℝ (Fin n)) :
    |f (x + v) - f x - ∑ i, v i * T.g i x - (∑ i, ∑ j, v i * v j * T.H i j x) / 2|
      ≤ M₃ * ‖v‖ ^ 3 / 6 := by
  have h := taylor3 (fun s => f (x + s • v)) (fun t => ∑ i, v i * T.g i (x + t • v))
    (fun t => ∑ i, ∑ j, v i * v j * T.H i j (x + t • v)) (fun t => T.D3 (x + t • v) v)
    (T.d1 x v) (T.d2 x v) (T.d3 x v) (M₃ * ‖v‖ ^ 3) (fun t _ => T.bd3 _ _)
  simpa using h

/-- The averaging operator `A_ξ f(x) = ∫ k(z) f(x + ξz) dμ / ∫ k dμ`. -/
def avgOp (μ : Measure (EuclideanSpace ℝ (Fin n))) (k : EuclideanSpace ℝ (Fin n) → ℝ) (ξ : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∫ z, k z * f (x + ξ • z) ∂μ) / ∫ z, k z ∂μ

/-- HYPOTHESES on the kernel: measurable, `≥ 0`, integrable with mass `K₀ > 0`, the moment functions
`z_i k`, `z_i z_j k`, `|z|³ k` integrable, first moments zero, second moments `δ_ij m₂ K₀`. -/
structure Kern (n : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (k : EuclideanSpace ℝ (Fin n) → ℝ) (K₀ m₂ μ₃ : ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ k z
  int0 : Integrable k μ
  int1 : ∀ i, Integrable (fun z => z i * k z) μ
  int2 : ∀ i j, Integrable (fun z => z i * z j * k z) μ
  int3 : Integrable (fun z => ‖z‖ ^ 3 * k z) μ
  mass : ∫ z, k z ∂μ = K₀
  mass_pos : 0 < K₀
  mom1 : ∀ i, ∫ z, z i * k z ∂μ = 0
  mom2 : ∀ i j, ∫ z, z i * z j * k z ∂μ = if i = j then m₂ * K₀ else 0
  mom3 : ∫ z, ‖z‖ ^ 3 * k z ∂μ = μ₃

theorem integral_first {μ : Measure (EuclideanSpace ℝ (Fin n))} {k : EuclideanSpace ℝ (Fin n) → ℝ}
    {K₀ m₂ μ₃ : ℝ} (hk : Kern n μ k K₀ m₂ μ₃) (c : Fin n → ℝ) :
    Integrable (fun z => ∑ i, c i * (z i * k z)) μ ∧ ∫ z, ∑ i, c i * (z i * k z) ∂μ = 0 := by
  refine ⟨integrable_finset_sum _ fun i _ => (hk.int1 i).const_mul _, ?_⟩
  rw [integral_finset_sum _ fun i _ => (hk.int1 i).const_mul _]
  exact Finset.sum_eq_zero fun i _ => by rw [integral_const_mul, hk.mom1 i, mul_zero]

theorem integral_second {μ : Measure (EuclideanSpace ℝ (Fin n))} {k : EuclideanSpace ℝ (Fin n) → ℝ}
    {K₀ m₂ μ₃ : ℝ} (hk : Kern n μ k K₀ m₂ μ₃) (c : Fin n → Fin n → ℝ) :
    Integrable (fun z => ∑ i, ∑ j, c i j * (z i * z j * k z)) μ
    ∧ ∫ z, ∑ i, ∑ j, c i j * (z i * z j * k z) ∂μ = m₂ * K₀ * ∑ i, c i i := by
  have hi : ∀ i, Integrable (fun z => ∑ j, c i j * (z i * z j * k z)) μ := fun i =>
    integrable_finset_sum _ fun j _ => (hk.int2 i j).const_mul _
  refine ⟨integrable_finset_sum _ fun i _ => hi i, ?_⟩
  rw [integral_finset_sum _ fun i _ => hi i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => (hk.int2 i j).const_mul _]
  simp only [integral_const_mul, hk.mom2, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  ring

/-- **(1) Flat `thm:LB`, second-order expansion of the averaging operator.** -/
theorem avgOp_expansion {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {K₀ m₂ μ₃ : ℝ} (hk : Kern n μ k K₀ m₂ μ₃)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M₃ : ℝ} (T : Taylor3 n f M₃) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun z => k z * f (x + ξ • z)) μ ∧
    |avgOp μ k ξ f x - f x - ξ ^ 2 / 2 * m₂ * lapl T x| ≤ M₃ * ξ ^ 3 * μ₃ / (6 * K₀) := by
  have hK₀ := hk.mass_pos
  -- the polynomial part and the remainder
  set P : EuclideanSpace ℝ (Fin n) → ℝ := fun z => k z * f x
    + ξ * ∑ i, T.g i x * (z i * k z) + ξ ^ 2 / 2 * ∑ i, ∑ j, T.H i j x * (z i * z j * k z) with hP
  set Q : EuclideanSpace ℝ (Fin n) → ℝ := fun z => k z * f (x + ξ • z) - P z with hQ
  have hS1 : ∀ z : EuclideanSpace ℝ (Fin n), k z * ∑ i, (ξ • z) i * T.g i x
      = ξ * ∑ i, T.g i x * (z i * k z) := fun z => by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [PiLp.smul_apply, smul_eq_mul]; ring
  have hS2 : ∀ z : EuclideanSpace ℝ (Fin n), k z * ∑ i, ∑ j, (ξ • z) i * (ξ • z) j * T.H i j x
      = ξ ^ 2 * ∑ i, ∑ j, T.H i j x * (z i * z j * k z) := fun z => by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [PiLp.smul_apply, smul_eq_mul]; ring
  have hPQ : ∀ z, P z + Q z = k z * f (x + ξ • z) := fun z => by
    show P z + (k z * f (x + ξ • z) - P z) = _
    ring
  obtain ⟨i1, e1⟩ := integral_first hk (fun i => T.g i x)
  obtain ⟨i2, e2⟩ := integral_second hk (fun i j => T.H i j x)
  have iP : Integrable P μ := ((hk.int0.mul_const (f x)).add (i1.const_mul ξ)).add
    (i2.const_mul (ξ ^ 2 / 2))
  have eP : ∫ z, P z ∂μ = K₀ * f x + ξ ^ 2 / 2 * (m₂ * K₀ * lapl T x) := by
    have hA : Integrable (fun z => k z * f x + ξ * ∑ i, T.g i x * (z i * k z)) μ :=
      (hk.int0.mul_const (f x)).add (i1.const_mul ξ)
    have hB : Integrable (fun z => ξ ^ 2 / 2 * ∑ i, ∑ j, T.H i j x * (z i * z j * k z)) μ :=
      i2.const_mul _
    calc ∫ z, P z ∂μ = ∫ z, ((k z * f x + ξ * ∑ i, T.g i x * (z i * k z))
          + ξ ^ 2 / 2 * ∑ i, ∑ j, T.H i j x * (z i * z j * k z)) ∂μ := rfl
      _ = (∫ z, (k z * f x + ξ * ∑ i, T.g i x * (z i * k z)) ∂μ)
          + ∫ z, ξ ^ 2 / 2 * ∑ i, ∑ j, T.H i j x * (z i * z j * k z) ∂μ := integral_add hA hB
      _ = K₀ * f x + ξ ^ 2 / 2 * (m₂ * K₀ * lapl T x) := by
          rw [integral_add (hk.int0.mul_const (f x)) (i1.const_mul ξ), integral_mul_const,
            integral_const_mul, integral_const_mul, e1, e2, hk.mass]
          unfold lapl; ring
  -- pointwise bound of the remainder
  have hQb : ∀ z, |Q z| ≤ M₃ * ξ ^ 3 / 6 * (‖z‖ ^ 3 * k z) := fun z => by
    have hp := T.pointwise x (ξ • z)
    have hn : ‖ξ • z‖ = ξ * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hξ]
    have e : Q z = k z * (f (x + ξ • z) - f x - ∑ i, (ξ • z) i * T.g i x
        - (∑ i, ∑ j, (ξ • z) i * (ξ • z) j * T.H i j x) / 2) := by
      show k z * f (x + ξ • z) - (k z * f x + ξ * ∑ i, T.g i x * (z i * k z)
        + ξ ^ 2 / 2 * ∑ i, ∑ j, T.H i j x * (z i * z j * k z)) = _
      linear_combination hS1 z + (1 / 2 : ℝ) * hS2 z
    rw [e, abs_mul, abs_of_nonneg (hk.nonneg z)]
    rw [hn] at hp
    have hk0 := hk.nonneg z
    calc k z * |f (x + ξ • z) - f x - ∑ i, (ξ • z) i * T.g i x
          - (∑ i, ∑ j, (ξ • z) i * (ξ • z) j * T.H i j x) / 2|
        ≤ k z * (M₃ * (ξ * ‖z‖) ^ 3 / 6) := mul_le_mul_of_nonneg_left hp hk0
      _ = M₃ * ξ ^ 3 / 6 * (‖z‖ ^ 3 * k z) := by ring
  -- measurability of `Q`
  have hQm : AEStronglyMeasurable Q μ := by
    have hc : Continuous fun z : EuclideanSpace ℝ (Fin n) => f (x + ξ • z) :=
      T.cont.comp (continuous_const.add (continuous_const.smul continuous_id))
    exact (hk.int0.aestronglyMeasurable.mul hc.aestronglyMeasurable).sub iP.aestronglyMeasurable
  have iQ : Integrable Q μ :=
    Integrable.mono' (hk.int3.const_mul (M₃ * ξ ^ 3 / 6)) hQm
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hQb z)
  have iT : Integrable (fun z => k z * f (x + ξ • z)) μ := by
    have := iP.add iQ
    refine this.congr (ae_of_all _ fun z => ?_)
    exact hPQ z
  refine ⟨iT, ?_⟩
  have eT : ∫ z, k z * f (x + ξ • z) ∂μ = ∫ z, P z ∂μ + ∫ z, Q z ∂μ := by
    rw [← integral_add iP iQ]; exact integral_congr_ae (ae_of_all _ fun z => (hPQ z).symm)
  have hQi : |∫ z, Q z ∂μ| ≤ M₃ * ξ ^ 3 / 6 * μ₃ := by
    calc |∫ z, Q z ∂μ| ≤ ∫ z, |Q z| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, M₃ * ξ ^ 3 / 6 * (‖z‖ ^ 3 * k z) ∂μ :=
          integral_mono iQ.abs (hk.int3.const_mul _) hQb
      _ = M₃ * ξ ^ 3 / 6 * μ₃ := by rw [integral_const_mul, hk.mom3]
  unfold avgOp
  rw [eT, eP, hk.mass]
  have e : (K₀ * f x + ξ ^ 2 / 2 * (m₂ * K₀ * lapl T x) + ∫ z, Q z ∂μ) / K₀ - f x
      - ξ ^ 2 / 2 * m₂ * lapl T x = (∫ z, Q z ∂μ) / K₀ := by
    first | (field_simp; ring) | field_simp | ring
  rw [e, abs_div, abs_of_pos hK₀]
  calc |∫ z, Q z ∂μ| / K₀ ≤ M₃ * ξ ^ 3 / 6 * μ₃ / K₀ := div_le_div_of_nonneg_right hQi hK₀.le
    _ = M₃ * ξ ^ 3 * μ₃ / (6 * K₀) := by first | (field_simp; ring) | field_simp | ring

/-- **(1') The normalised form**: `|(2/(m₂ ξ²))(f(x) − A_ξ f(x)) + Δf(x)| ≤ M₃ ξ μ₃/(3 m₂ K₀)`;
this is `thm:LB` for constant density in flat space with `c_h = m₂`. -/
theorem flat_LB {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {K₀ m₂ μ₃ : ℝ} (hk : Kern n μ k K₀ m₂ μ₃) (hm₂ : 0 < m₂)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M₃ : ℝ} (T : Taylor3 n f M₃) (ξ : ℝ) (hξ : 0 < ξ)
    (x : EuclideanSpace ℝ (Fin n)) :
    |2 / (m₂ * ξ ^ 2) * (f x - avgOp μ k ξ f x) + lapl T x| ≤ M₃ * ξ * μ₃ / (3 * m₂ * K₀) := by
  have h := (avgOp_expansion hk T ξ hξ.le x).2
  have hK₀ := hk.mass_pos
  have hc : 0 < 2 / (m₂ * ξ ^ 2) := by positivity
  have e : 2 / (m₂ * ξ ^ 2) * (f x - avgOp μ k ξ f x) + lapl T x
      = -(2 / (m₂ * ξ ^ 2)) * (avgOp μ k ξ f x - f x - ξ ^ 2 / 2 * m₂ * lapl T x) := by
    first | (field_simp; ring) | field_simp | ring
  rw [e, abs_mul, abs_neg, abs_of_pos hc]
  calc 2 / (m₂ * ξ ^ 2) * |avgOp μ k ξ f x - f x - ξ ^ 2 / 2 * m₂ * lapl T x|
      ≤ 2 / (m₂ * ξ ^ 2) * (M₃ * ξ ^ 3 * μ₃ / (6 * K₀)) := mul_le_mul_of_nonneg_left h hc.le
    _ = M₃ * ξ * μ₃ / (3 * m₂ * K₀) := by first | (field_simp; ring) | field_simp | ring

/-! ### Radial kernels: vanishing first moments for Lebesgue measure -/

/-- For `k(z) = h(|z|)` and Lebesgue measure on `EuclideanSpace ℝ (Fin n)`: `∫ z_i k(z) dz = 0`. -/
theorem radial_first_moment (h : ℝ → ℝ) (i : Fin n) :
    ∫ z : EuclideanSpace ℝ (Fin n), z i * h ‖z‖ = 0 := by
  set e := LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n)) with he
  have hmp : MeasurePreserving e volume volume := LinearIsometryEquiv.measurePreserving e
  have hcomp := hmp.integral_comp e.toHomeomorph.measurableEmbedding
    (fun z : EuclideanSpace ℝ (Fin n) => z i * h ‖z‖)
  have hneg : (fun z : EuclideanSpace ℝ (Fin n) => (e z) i * h ‖e z‖)
      = fun z => -(z i * h ‖z‖) := by
    funext z; simp [he]
  have h2 : ∫ z : EuclideanSpace ℝ (Fin n), (e z) i * h ‖e z‖
      = ∫ z : EuclideanSpace ℝ (Fin n), z i * h ‖z‖ := hcomp
  rw [hneg, integral_neg] at h2
  linarith

/-! ### (2) Difference quotient in a parameter, by linearity -/

/-- Linearity of `A_ξ`: `(A_ξ f_b − A_ξ f_a)/η = A_ξ((f_b − f_a)/η)` (integrability from (1)). -/
theorem avgOp_dq {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {K₀ m₂ μ₃ : ℝ} (hk : Kern n μ k K₀ m₂ μ₃)
    {fa fb : EuclideanSpace ℝ (Fin n) → ℝ} {Ma Mb : ℝ} (Ta : Taylor3 n fa Ma)
    (Tb : Taylor3 n fb Mb) (ξ : ℝ) (hξ : 0 ≤ ξ) (η : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (avgOp μ k ξ fb x - avgOp μ k ξ fa x) / η
      = avgOp μ k ξ (fun y => (fb y - fa y) / η) x := by
  have ia := (avgOp_expansion hk Ta ξ hξ x).1
  have ib := (avgOp_expansion hk Tb ξ hξ x).1
  unfold avgOp
  have e : (fun z => k z * ((fb (x + ξ • z) - fa (x + ξ • z)) / η))
      = fun z => (k z * fb (x + ξ • z) - k z * fa (x + ξ • z)) / η := by funext z; ring
  rw [e, integral_div, integral_sub ib ia]
  ring

/-- **(2) The parameter version**: if the difference quotient `F = (f_b − f_a)/η` of a family has
directional derivatives up to order three with `|D³F| ≤ M₃'|v|³` (HYPOTHESIS `TF`), then
`|Δ_η(A_ξ f) − Δ_η f − (ξ²/2) m₂ ΔF| ≤ M₃' ξ³ μ₃/(6K₀)`. -/
theorem avgOp_dq_expansion {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {k : EuclideanSpace ℝ (Fin n) → ℝ} {K₀ m₂ μ₃ : ℝ} (hk : Kern n μ k K₀ m₂ μ₃)
    {fa fb : EuclideanSpace ℝ (Fin n) → ℝ} {Ma Mb M' : ℝ} (Ta : Taylor3 n fa Ma)
    (Tb : Taylor3 n fb Mb) (η : ℝ) (TF : Taylor3 n (fun y => (fb y - fa y) / η) M')
    (ξ : ℝ) (hξ : 0 ≤ ξ) (x : EuclideanSpace ℝ (Fin n)) :
    |(avgOp μ k ξ fb x - avgOp μ k ξ fa x) / η - (fb x - fa x) / η - ξ ^ 2 / 2 * m₂ * lapl TF x|
      ≤ M' * ξ ^ 3 * μ₃ / (6 * K₀) := by
  rw [avgOp_dq hk Ta Tb ξ hξ η x]
  exact (avgOp_expansion hk TF ξ hξ x).2

/-! ### Radial kernels: isotropy of the second moments -/

theorem iso_integral (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∫ z, F (e z) = ∫ z, F z :=
  (LinearIsometryEquiv.measurePreserving e).integral_comp e.toHomeomorph.measurableEmbedding F

/-- Flip of the sign of coordinate `i`. -/
def flip (i : Fin n) : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun k => if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

theorem flip_apply (i : Fin n) (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    flip i z k = if k = i then -z k else z k := by
  unfold flip
  rw [LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> simp

/-- Swap of two coordinates. -/
def swapC (i j : Fin n) : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

theorem swapC_apply (i j : Fin n) (z : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    swapC i j z k = z (Equiv.swap i j k) := by
  unfold swapC
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Equiv.piCongrLeft', Equiv.symm_swap]

/-- Off-diagonal second moments of a radial kernel vanish. -/
theorem radial_second_offdiag (h : ℝ → ℝ) (i j : Fin n) (hij : i ≠ j) :
    ∫ z : EuclideanSpace ℝ (Fin n), z i * z j * h ‖z‖ = 0 := by
  have h1 := iso_integral (fun z : EuclideanSpace ℝ (Fin n) => z i * z j * h ‖z‖) (flip i)
  have hn : ∀ z : EuclideanSpace ℝ (Fin n), ‖flip i z‖ = ‖z‖ := fun z => (flip i).norm_map z
  have e : (fun z : EuclideanSpace ℝ (Fin n) => (flip i z) i * (flip i z) j * h ‖flip i z‖)
      = fun z => -(z i * z j * h ‖z‖) := by
    funext z
    rw [hn, flip_apply, flip_apply, if_pos rfl, if_neg (Ne.symm hij)]
    ring
  have h2 : ∫ z : EuclideanSpace ℝ (Fin n), (flip i z) i * (flip i z) j * h ‖flip i z‖
      = ∫ z : EuclideanSpace ℝ (Fin n), z i * z j * h ‖z‖ := h1
  rw [e, integral_neg] at h2
  linarith

/-- Diagonal second moments of a radial kernel are equal. -/
theorem radial_second_diag (h : ℝ → ℝ) (i j : Fin n) :
    ∫ z : EuclideanSpace ℝ (Fin n), z i * z i * h ‖z‖
      = ∫ z : EuclideanSpace ℝ (Fin n), z j * z j * h ‖z‖ := by
  have h1 := iso_integral (fun z : EuclideanSpace ℝ (Fin n) => z i * z i * h ‖z‖) (swapC i j)
  have hn : ∀ z : EuclideanSpace ℝ (Fin n), ‖swapC i j z‖ = ‖z‖ :=
    fun z => (swapC i j).norm_map z
  have e : (fun z : EuclideanSpace ℝ (Fin n) =>
      (swapC i j z) i * (swapC i j z) i * h ‖swapC i j z‖)
      = fun z => z j * z j * h ‖z‖ := by
    funext z
    rw [hn, swapC_apply, Equiv.swap_apply_left]
  have h2 : ∫ z : EuclideanSpace ℝ (Fin n), (swapC i j z) i * (swapC i j z) i * h ‖swapC i j z‖
      = ∫ z : EuclideanSpace ℝ (Fin n), z i * z i * h ‖z‖ := h1
  rw [e] at h2
  exact h2.symm

/-- **A radial kernel satisfies the moment HYPOTHESES of `Kern`** (Lebesgue measure), given
`h ≥ 0`, integrability of `k`, `|z| k`, `|z|² k`, `|z|³ k` and positive mass; `m₂` is the second
moment of the first coordinate divided by the mass. -/
theorem radial_kern (h : ℝ → ℝ) (hh0 : ∀ t, 0 ≤ h t) (i₀ : Fin n)
    (hm : Measurable fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖)
    (hi0 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => h ‖z‖))
    (hi1 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ * h ‖z‖))
    (hi2 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 * h ‖z‖))
    (hi3 : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 3 * h ‖z‖))
    (hpos : 0 < ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖) :
    Kern n volume (fun z => h ‖z‖) (∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖)
      ((∫ z : EuclideanSpace ℝ (Fin n), z i₀ * z i₀ * h ‖z‖) / ∫ z : EuclideanSpace ℝ (Fin n), h ‖z‖)
      (∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 3 * h ‖z‖) where
  nonneg := fun z => hh0 _
  int0 := hi0
  int1 := fun i => by
    refine hi1.mono' (((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).mul
      hm).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hh0 _)]
    exact mul_le_mul_of_nonneg_right (by
      simpa using PiLp.norm_apply_le z i) (hh0 _)
  int2 := fun i j => by
    have hc : Continuous fun z : EuclideanSpace ℝ (Fin n) => z i * z j :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.mul (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
    refine hi2.mono' (hc.measurable.mul hm).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hh0 _), sq]
    have hi : |z i| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z i
    have hj : |z j| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z j
    exact mul_le_mul_of_nonneg_right (mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)) (hh0 _)
  int3 := hi3
  mass := rfl
  mass_pos := hpos
  mom1 := fun i => radial_first_moment h i
  mom2 := fun i j => by
    split_ifs with hij
    · subst hij
      rw [radial_second_diag h i i₀]
      field_simp
    · exact radial_second_offdiag h i j hij
  mom3 := rfl

end CTG.FlatLB
