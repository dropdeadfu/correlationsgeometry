/-
Thirty-fifth file: at least `2l+1` eigenvalues of the sample matrix on `S²` near `s_l`, for RANDOM points.
Imports `CorrelationsToGeometryFunkHeckeSampleMult` (compiled module under `.tools/leanbuild`); namespace
`CTG.FunkHecke.SampleMultProb`; check with `./check_funk_hecke_sample_mult_prob.sh`.
`sample_mult_gen`: independent points with the normalised surface measure, `m` continuous eigenfunctions of the
population walk with value `s`, bounded by `F ≥ 1`, with a lower bound `γ0` of their `L²` Gram form; for `N ≥ 2`,
`0 < η ≤ sphZ ξ/4`, `δ > 0`, `m δ < γ0`, outside an event of probability at most
`m·4N exp(−(N−1)η²/(2F²)) + 2N exp(−(N−1)η²/2) + m²·2 exp(−(Nδ)²/(2 N F⁴))` at least `m` eigenvalues of
`Smat = D^{-1/2} K D^{-1/2}` (indices of the eigenbasis; self-loops included) lie within
`N·errE·F·√m / ((N−1) sphZ/4 · (γ0 − m δ))` of `s`.
`sample_multiplicity`: for every `ξ`, `l` this holds with `m = 2l+1`, `s = sphS ξ l` and constants `F`, `γ0 > 0`
that EXIST (they come from a choice of `2l+1` independent eigenfunctions and compactness, and are not computed).
NOT formalised: exactly `2l+1`, that every eigenvalue of the sample matrix is near some `s_l`, an almost-sure
version, a rate in `ξ`, measurability of the exceptional set.  Fixed scale `ξ`.
No sorry, no axiom, no native_decide.  Written by an AI session on 26/27 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSampleMult

/-!
# A146: at least `2l+1` eigenvalues of the sample matrix on `S²` near `s_l`, for random points
-/

open MeasureTheory ProbabilityTheory Set Metric Real Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal

namespace CTG.FunkHecke.SampleMultProb

open CTG.FunkHecke CTG.FunkHecke.Sample CTG.FunkHecke.SampleEig CTG.FunkHecke.SampleMult

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Multiplicity for random points, general family.** Independent points with law `sigma`; `e_1..e_m`
continuous, bounded by `F ≥ 1`, eigenfunctions of the population walk with the value `s`, with a lower bound
`γ0` of their `L²` Gram form; `N ≥ 2`, `0 < η ≤ sphZ ξ/4`, `δ > 0` with `m δ < γ0`.  Outside an event of the
stated probability, at least `m` eigenvalues of `Smat` (indices of the eigenbasis) lie within the stated
radius of `s`. -/
theorem sample_mult_gen (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) {m : ℕ} (e : Fin m → S2 → ℝ)
    (he : ∀ r, Continuous (e r)) (s : ℝ) (heig : ∀ r x, Pinf (gk ξ) (e r) x = s * e r x)
    {F : ℝ} (hF1 : 1 ≤ F) (hb : ∀ r y, |e r y| ≤ F) {γ0 : ℝ}
    (hγ : ∀ c : Fin m → ℝ, γ0 * ∑ r, c r ^ 2 ≤ gramQ e c)
    {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4)
    {δ : ℝ} (hδ : 0 < δ) (hmδ : (m:ℝ) * δ < γ0) :
    μ.real {ω | ¬ (m ≤ (Finset.univ.filter (fun j : Fin N =>
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - s|
          ≤ N * errE ξ F η N * F * √(m:ℝ)
              / ((((N:ℝ) - 1) * sphZ ξ / 4) * (γ0 - m * δ)))).card)}
      ≤ (m:ℝ) * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)))
        + 2 * N * Real.exp (-((N - 1) * η ^ 2) / 2)
        + (m:ℝ) * (m:ℝ) * (2 * Real.exp (-(N * δ) ^ 2 / (2 * ((Finset.range N).card * (F ^ 2) ^ 2)))) := by
  have hF : 0 < F := by linarith
  have hZ : 0 < sphZ ξ := sphZ_pos ξ
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hN1 : (0:ℝ) ≤ (N:ℝ) - 1 := by linarith
  set A : Fin m → Set Ω := fun r => {ω | ∃ i < N, 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk ξ (e r) X N ω i - Pinf (gk ξ) (e r) (X i ω)|} with hAdef
  set B : Set Ω := {ω | ∃ i < N, ∑ j ∈ Finset.range N, Kx ξ (X i ω) (X j ω) < (N - 1) * sphZ ξ / 4}
    with hBdef
  set G : Fin m × Fin m → Set Ω := fun p => {ω | (N:ℝ) * δ ≤
      |∑ j ∈ Finset.range N, ((fun y => e p.1 y * e p.2 y) (X j ω)
        - ∫ z, (fun y => e p.1 y * e p.2 y) z ∂sigma)|} with hGdef
  have hA : ∀ r, μ.real (A r) ≤ 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := fun r =>
    walk_one_step X hind hX hlaw ξ (e r) (he r) hF1 (hb r) hN hη hηb
  have hB : μ.real B ≤ 2 * N * Real.exp (-((N - 1) * η ^ 2) / 2) :=
    deg_event X hind hX hlaw ξ hN hη hηb
  have hG : ∀ p, μ.real (G p)
      ≤ 2 * Real.exp (-(N * δ) ^ 2 / (2 * ((Finset.range N).card * (F ^ 2) ^ 2))) := by
    intro p
    have hbd : ∀ z, |(fun y => e p.1 y * e p.2 y) z| ≤ F ^ 2 := by
      intro z
      show |e p.1 z * e p.2 z| ≤ F ^ 2
      rw [abs_mul, sq]
      exact mul_le_mul (hb p.1 z) (hb p.2 z) (abs_nonneg _) hF.le
    exact hoeffding_fn X hind hX hlaw (fun y => e p.1 y * e p.2 y)
      ((he p.1).mul (he p.2)).measurable (by positivity) hbd (Finset.range N)
      (by positivity)
  set UA : Set Ω := ⋃ r ∈ (Finset.univ : Finset (Fin m)), A r with hUA
  set UG : Set Ω := ⋃ p ∈ (Finset.univ : Finset (Fin m × Fin m)), G p with hUG
  have hsub : {ω | ¬ (m ≤ (Finset.univ.filter (fun j : Fin N =>
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - s|
          ≤ N * errE ξ F η N * F * √(m:ℝ)
              / ((((N:ℝ) - 1) * sphZ ξ / 4) * (γ0 - m * δ)))).card)} ⊆ UA ∪ B ∪ UG := by
    intro ω hω
    by_contra hnot
    have hnA : ∀ r, ω ∉ A r := fun r hr =>
      hnot (Or.inl (Or.inl (Set.mem_biUnion (Finset.mem_univ r) hr)))
    have hnB : ω ∉ B := fun hb' => hnot (Or.inl (Or.inr hb'))
    have hnG : ∀ p, ω ∉ G p := fun p hp => hnot (Or.inr (Set.mem_biUnion (Finset.mem_univ p) hp))
    apply hω
    have hE : 0 ≤ errE ξ F η N := by
      unfold errE
      have h2 : 0 ≤ 2 * F / ((N:ℝ) - 1) := div_nonneg (by linarith) hN1
      have h3 : 0 ≤ η * (1 + F) := mul_nonneg hη.le (by linarith)
      exact div_nonneg (by linarith) hZ.le
    have hd : 0 < ((N:ℝ) - 1) * sphZ ξ / 4 := by
      have : (0:ℝ) < (N:ℝ) - 1 := by linarith
      positivity
    have hg : 0 < γ0 - m * δ := by linarith
    have hdeg : ∀ i : Fin N, ((N:ℝ) - 1) * sphZ ξ / 4 ≤ deg ξ (fun i : Fin N => X i ω) i := by
      intro i
      have h1 : ((N:ℝ) - 1) * sphZ ξ / 4 ≤ ∑ j ∈ Finset.range N, Kx ξ (X i ω) (X j ω) := by
        by_contra h
        exact hnB ⟨i, i.2, not_le.mp h⟩
      show ((N:ℝ) - 1) * sphZ ξ / 4 ≤ ∑ j : Fin N, Kx ξ (X i ω) (X j ω)
      rw [← Finset.sum_range (fun j => Kx ξ (X i ω) (X j ω))]
      exact h1
    have herr : ∀ (r : Fin m) (i : Fin N),
        |(∑ j, Kx ξ ((fun i : Fin N => X i ω) i) ((fun i : Fin N => X i ω) j)
            * e r ((fun i : Fin N => X i ω) j)) / deg ξ (fun i : Fin N => X i ω) i
          - s * e r ((fun i : Fin N => X i ω) i)| ≤ errE ξ F η N := by
      intro r i
      have h1 : |walk ξ (e r) X N ω i - Pinf (gk ξ) (e r) (X i ω)|
          ≤ 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ := by
        by_contra h
        exact hnA r ⟨i, i.2, not_le.mp h⟩
      have hw : walk ξ (e r) X N ω i
          = (∑ j : Fin N, Kx ξ (X i ω) (X j ω) * e r (X j ω))
              / ∑ j : Fin N, Kx ξ (X i ω) (X j ω) := by
        unfold walk
        rw [Finset.sum_range (fun j => Kx ξ (X i ω) (X j ω) * e r (X j ω)),
          Finset.sum_range (fun j => Kx ξ (X i ω) (X j ω))]
      show |(∑ j : Fin N, Kx ξ (X i ω) (X j ω) * e r (X j ω))
            / (∑ j : Fin N, Kx ξ (X i ω) (X j ω)) - s * e r (X i ω)| ≤ errE ξ F η N
      rw [← hw, ← heig r (X i ω)]
      unfold errE
      exact h1
    have hGs : ∀ r s', |∑ j ∈ Finset.range N,
        (e r ((fun j => X j ω) j) * e s' ((fun j => X j ω) j) - ∫ y, e r y * e s' y ∂sigma)|
          < N * δ := by
      intro r s'
      by_contra h
      exact hnG (r, s') (not_lt.mp h)
    have hgram : ∀ c : Fin m → ℝ, (N:ℝ) * (γ0 - m * δ) * ∑ r, c r ^ 2
        ≤ ∑ i : Fin N, (∑ r, c r * e r ((fun i : Fin N => X i ω) i)) ^ 2 := by
      intro c
      have h := sample_gram_det e he hγ hδ.le (fun j => X j ω) hGs c
      rw [Finset.sum_range (fun j => (∑ r, c r * e r (X j ω)) ^ 2)] at h
      exact h
    exact mult_det (by omega) ξ (fun i : Fin N => X i ω) e s hE hF hd hg hdeg herr hb hgram
  have hUAle : μ.real UA ≤ (m:ℝ) * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2))) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun r _ => hA r).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hUGle : μ.real UG ≤ (m:ℝ) * (m:ℝ)
      * (2 * Real.exp (-(N * δ) ^ 2 / (2 * ((Finset.range N).card * (F ^ 2) ^ 2)))) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => hG p).trans_eq ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_mul]
  calc _ ≤ μ.real (UA ∪ B ∪ UG) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (UA ∪ B) + μ.real UG := measureReal_union_le _ _
    _ ≤ μ.real UA + μ.real B + μ.real UG := by linarith [measureReal_union_le (μ := μ) UA B]
    _ ≤ _ := by linarith

/-- **At least `2l+1` eigenvalues of the sample matrix near `s_l`.** For every `ξ` and `l` there are
constants `F ≥ 1`, `γ0 > 0` (depending on `ξ`, `l` only through the chosen eigenfunctions) such that for
independent points with law `sigma`, `N ≥ 2`, `0 < η ≤ sphZ ξ/4`, `δ > 0` with `(2l+1) δ < γ0`, outside an
event of the stated probability at least `2l+1` eigenvalues of `Smat` lie within the stated radius of
`sphS ξ l`. -/
theorem sample_multiplicity (ξ : ℝ) (l : ℕ) :
    ∃ F γ0 : ℝ, 1 ≤ F ∧ 0 < γ0 ∧
      ∀ (X : ℕ → Ω → S2), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = sigma) →
      ∀ {N : ℕ}, 2 ≤ N → ∀ {η : ℝ}, 0 < η → η ≤ sphZ ξ / 4 → ∀ {δ : ℝ}, 0 < δ →
        ((2 * l + 1 : ℕ) : ℝ) * δ < γ0 →
        μ.real {ω | ¬ (2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N =>
            |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
              ≤ N * errE ξ F η N * F * √((2 * l + 1 : ℕ) : ℝ)
                  / ((((N:ℝ) - 1) * sphZ ξ / 4) * (γ0 - ((2 * l + 1 : ℕ) : ℝ) * δ)))).card)}
          ≤ ((2 * l + 1 : ℕ) : ℝ) * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)))
            + 2 * N * Real.exp (-((N - 1) * η ^ 2) / 2)
            + ((2 * l + 1 : ℕ) : ℝ) * ((2 * l + 1 : ℕ) : ℝ)
              * (2 * Real.exp (-(N * δ) ^ 2 / (2 * ((Finset.range N).card * (F ^ 2) ^ 2)))) := by
  obtain ⟨e, hli, hc, heig⟩ := Pinf_multiplicity_cont ξ l
  obtain ⟨γ0, hγ0, hγ⟩ := gram_lower e hc hli
  have hbd : ∀ r, ∃ C : ℝ, ∀ y, |e r y| ≤ C := by
    intro r
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hc r).continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  choose C hC using hbd
  refine ⟨1 + ∑ r, |C r|, γ0, ?_, hγ0, ?_⟩
  · have : 0 ≤ ∑ r, |C r| := Finset.sum_nonneg fun r _ => abs_nonneg _
    linarith
  · intro X hind hX hlaw N hN η hη hηb δ hδ hmδ
    have hF1 : 1 ≤ 1 + ∑ r, |C r| := by
      have : 0 ≤ ∑ r, |C r| := Finset.sum_nonneg fun r _ => abs_nonneg _
      linarith
    have hb : ∀ r y, |e r y| ≤ 1 + ∑ r, |C r| := by
      intro r y
      have h1 : |e r y| ≤ |C r| := (hC r y).trans (le_abs_self _)
      have h2 : |C r| ≤ ∑ r, |C r| :=
        Finset.single_le_sum (fun r _ => abs_nonneg (C r)) (Finset.mem_univ r)
      linarith
    exact sample_mult_gen X hind hX hlaw ξ e hc (sphS ξ l) heig hF1 hb hγ hN hη hηb hδ hmδ

end CTG.FunkHecke.SampleMultProb
