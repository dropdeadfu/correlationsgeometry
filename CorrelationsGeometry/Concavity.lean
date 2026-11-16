import Mathlib

/-!
# Concavity of the ground-state energy and `λ ≤ 1` (Propositions 9.4 and 9.5 of the paper)

Paper: M. Neuberger, *From Correlations to Geometry* (November 2026).

Proposition 9.4 considers a Hamiltonian that is linear in the shift, `H(β) = H₀ + ∫ β · P`, on a
Hilbert space that does not depend on `β`. Its ground-state energy is

  `E₀(β) = inf_ψ ⟨ψ, H(β) ψ⟩`,

an infimum of functions that are affine in `β`. The abstract content is formalised here:

* `concaveOn_iInf_affine`: an infimum of affine functions is concave;
* `ConcaveOn.add_neg_le`: a concave function satisfies `E(β) + E(−β) ≤ 2 E(0)`;
* `second_order_nonpos`: its second-order coefficient along any direction is `≤ 0`;
* `sum_response_eq_zero_iff`: the responses of finitely many species cancel only if each vanishes;
* `lam_le_one`, `lam_eq_one_iff`: Proposition 9.5, `λ = 1 − ℓ/a ≤ 1`, with equality iff `ℓ = 0`.

In the dictionary with the paper, the index `i` ranges over the normalised states `ψ`,
`e i = ⟨ψ, H₀ ψ⟩` and `L i β = ⟨ψ, (∫ β · P) ψ⟩`.

Not formalised: that a quantum Hamiltonian of this kind has a ground-state energy given by this
infimum, and that an isotropic local quadratic form in the shift has the shape (9.9). These are the
inputs.
-/

open Topology

namespace CorrelationsGeometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Proposition 9.4, first step.** An infimum of affine functions `β ↦ e i + L i β` that is
bounded below at every point is a concave function of `β`. -/
theorem concaveOn_iInf_affine {ι : Type*} [Nonempty ι] (e : ι → ℝ) (L : ι → V →ₗ[ℝ] ℝ)
    (hbdd : ∀ β, BddBelow (Set.range fun i => e i + L i β)) :
    ConcaveOn ℝ Set.univ (fun β => ⨅ i, (e i + L i β)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  refine le_ciInf fun i => ?_
  have hx : (⨅ j, (e j + L j x)) ≤ e i + L i x := ciInf_le (hbdd x) i
  have hy : (⨅ j, (e j + L j y)) ≤ e i + L i y := ciInf_le (hbdd y) i
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  have he : e i = a * e i + b * e i := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul, map_add, map_smul]
  linarith

/-- A concave function on a real vector space satisfies `E(β) + E(−β) ≤ 2 E(0)`: the average of
the energies for the shifts `β` and `−β` never exceeds the energy without shift. -/
theorem ConcaveOn.add_neg_le {E : V → ℝ} (hE : ConcaveOn ℝ Set.univ E) (β : V) :
    E β + E (-β) ≤ 2 * E 0 := by
  have h := hE.2 (Set.mem_univ β) (Set.mem_univ (-β)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hz : (1 / 2 : ℝ) • β + (1 / 2 : ℝ) • (-β) = 0 := by
    rw [smul_neg, add_neg_cancel]
  rw [hz] at h
  simp only [smul_eq_mul] at h
  linarith

/-- If the energy is concave and invariant under `β ↦ −β` (time reversal), a shift never raises
it: `E(β) ≤ E(0)`. -/
theorem energy_le_of_even {E : V → ℝ} (hE : ConcaveOn ℝ Set.univ E)
    (heven : ∀ β, E (-β) = E β) (β : V) : E β ≤ E 0 := by
  have h := ConcaveOn.add_neg_le hE β
  rw [heven β] at h
  linarith

/-- **Proposition 9.4, non-positivity of the second-order change.** If the energy is concave and
`E(tβ) = E(0) + c t + q t² + o(t²)` as `t → 0`, then `q ≤ 0`. -/
theorem second_order_nonpos {E : V → ℝ} (hE : ConcaveOn ℝ Set.univ E) (β : V) (c q : ℝ)
    (h : (fun t : ℝ => E (t • β) - E 0 - c * t - q * t ^ 2) =o[𝓝 0] fun t : ℝ => t ^ 2) :
    q ≤ 0 := by
  by_contra hq'
  have hq : 0 < q := not_le.mp hq'
  have hev := h.def (half_pos hq)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  have ht : (0 : ℝ) < δ / 2 := half_pos hδ
  have hd1 : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]; linarith
  have hd2 : dist (-(δ / 2)) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos ht]; linarith
  have b1 := hball hd1
  have b2 := hball hd2
  simp only [Real.norm_eq_abs] at b1 b2
  have hsq : |(δ / 2) ^ 2| = (δ / 2) ^ 2 := abs_of_nonneg (sq_nonneg _)
  have hsq' : |(-(δ / 2)) ^ 2| = (δ / 2) ^ 2 := by
    rw [neg_sq]; exact hsq
  rw [hsq] at b1
  rw [hsq'] at b2
  have c1 := (abs_le.mp b1).1
  have c2 := (abs_le.mp b2).1
  have hconc := ConcaveOn.add_neg_le hE ((δ / 2) • β)
  rw [← neg_smul] at hconc
  have hpos : 0 < (δ / 2) ^ 2 := pow_pos ht 2
  have hnegsq : (-(δ / 2)) ^ 2 = (δ / 2) ^ 2 := neg_sq _
  rw [hnegsq] at c2
  nlinarith [mul_pos hq hpos]

/-- **Proposition 9.4, no cancellation between species.** For finitely many species whose energies
are concave and even in the shift, the total response to a shift vanishes if and only if the
response of every species vanishes. -/
theorem sum_response_eq_zero_iff {S : Type*} (s : Finset S) (E : S → V → ℝ)
    (hconc : ∀ i ∈ s, ConcaveOn ℝ Set.univ (E i))
    (heven : ∀ i ∈ s, ∀ β, E i (-β) = E i β) (β : V) :
    (∑ i ∈ s, (E i β - E i 0)) = 0 ↔ ∀ i ∈ s, E i β = E i 0 := by
  have hnonpos : ∀ i ∈ s, E i β - E i 0 ≤ 0 := fun i hi =>
    sub_nonpos.mpr (energy_le_of_even (hconc i hi) (heven i hi) β)
  rw [Finset.sum_eq_zero_iff_of_nonpos hnonpos]
  constructor
  · intro h i hi
    exact sub_eq_zero.mp (h i hi)
  · intro h i hi
    exact sub_eq_zero.mpr (h i hi)

/-- **Proposition 9.4, the same statement at second order.** For finitely many species with concave
energies and expansions `Eᵢ(tβ) = Eᵢ(0) + cᵢ t + qᵢ t² + o(t²)`, the second-order coefficients are
all `≤ 0`, so their sum vanishes if and only if every one of them vanishes. -/
theorem sum_second_order_eq_zero_iff {S : Type*} (s : Finset S) (E : S → V → ℝ) (β : V)
    (c q : S → ℝ) (hconc : ∀ i ∈ s, ConcaveOn ℝ Set.univ (E i))
    (hexp : ∀ i ∈ s, (fun t : ℝ => E i (t • β) - E i 0 - c i * t - q i * t ^ 2)
      =o[𝓝 0] fun t : ℝ => t ^ 2) :
    (∑ i ∈ s, q i) = 0 ↔ ∀ i ∈ s, q i = 0 :=
  Finset.sum_eq_zero_iff_of_nonpos fun i hi =>
    second_order_nonpos (hconc i hi) β (c i) (q i) (hexp i hi)

/-! ## Proposition 9.5: the kinetic coupling

By (9.9) the second-order change of the energy is `E₂ = −(a/4) C − ℓ Dv`, where
`C = ∫ |∂ₐβ_b − ∂_bβₐ|²` and `Dv = ∫ (∂ₐβₐ)²`. -/

/-- A transverse shift (`Dv = 0`, `C > 0`) with non-positive response gives `a ≥ 0`. -/
theorem a_nonneg_of_transverse {a C : ℝ} (hC : 0 < C) (h : -(a / 4) * C ≤ 0) : 0 ≤ a := by
  by_contra ha'
  have ha : a < 0 := not_le.mp ha'
  nlinarith [mul_pos (neg_pos.mpr ha) hC]

/-- A longitudinal shift (`C = 0`, `Dv > 0`) with non-positive response gives `ℓ ≥ 0`. -/
theorem l_nonneg_of_longitudinal {l Dv : ℝ} (hD : 0 < Dv) (h : -l * Dv ≤ 0) : 0 ≤ l := by
  by_contra hl'
  have hl : l < 0 := not_le.mp hl'
  nlinarith [mul_pos (neg_pos.mpr hl) hD]

/-- With `∫ K_ab K^ab = C/4 + Dv` and `∫ K² = Dv`, the Lagrangian `−E₂ = (a/4) C + ℓ Dv` is
`a (∫ K_ab K^ab − λ ∫ K²)` with `λ = 1 − ℓ/a`: the form (9.8). -/
theorem kinetic_form {a l C Dv KK K2 : ℝ} (ha : a ≠ 0) (hKK : KK = C / 4 + Dv) (hK2 : K2 = Dv) :
    a / 4 * C + l * Dv = a * (KK - (1 - l / a) * K2) := by
  rw [hKK, hK2]
  field_simp
  ring

/-- **Proposition 9.5.** `λ = 1 − ℓ/a ≤ 1` whenever `a > 0` and `ℓ ≥ 0`. -/
theorem lam_le_one {a l : ℝ} (ha : 0 < a) (hl : 0 ≤ l) : 1 - l / a ≤ 1 := by
  have : 0 ≤ l / a := div_nonneg hl ha.le
  linarith

/-- **Proposition 9.5, equality case.** `λ = 1` if and only if `ℓ = 0`, i.e. a longitudinal shift
does not change the energy. -/
theorem lam_eq_one_iff {a l : ℝ} (ha : 0 < a) : 1 - l / a = 1 ↔ l = 0 := by
  constructor
  · intro h
    have h0 : l / a = 0 := by linarith
    rcases div_eq_zero_iff.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 ha.ne'
  · intro h
    rw [h, zero_div, sub_zero]

/-- **Equation (9.10).** For the scalar field with a momentum cutoff, `a = 2c` and
`ℓ = (D² − 1) c` give `λ = (3 − D²)/2`. -/
theorem lam_scalar (D c : ℝ) (hc : c ≠ 0) : 1 - (D ^ 2 - 1) * c / (2 * c) = (3 - D ^ 2) / 2 := by
  field_simp
  ring

/-- **Equation (9.10), `D = 3`:** `λ = −3`. -/
theorem lam_scalar_three (c : ℝ) (hc : c ≠ 0) : 1 - ((3 : ℝ) ^ 2 - 1) * c / (2 * c) = -3 := by
  rw [lam_scalar 3 c hc]; norm_num

/-- **Proposition 9.9 (i).** For the Dirac field `ℓ = (1 − 1/D) a`, hence `λ = 1/D`. -/
theorem lam_dirac (D a : ℝ) (ha : a ≠ 0) : 1 - (1 - 1 / D) * a / a = 1 / D := by
  field_simp
  ring

end CorrelationsGeometry
