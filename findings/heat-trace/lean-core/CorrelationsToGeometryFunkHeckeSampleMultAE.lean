/-
Thirty-sixth file: almost-sure multiplicity for the sample matrix on `S²` at fixed scale.  Imports
`CorrelationsToGeometryFunkHeckeSampleMultProb` (compiled module under `.tools/leanbuild`); namespace
`CTG.FunkHecke.SampleMultAE`; check with `./check_funk_hecke_sample_mult_ae.sh`.
Independent points with the normalised surface measure, nested sample (the first `N` points of one sequence),
`Smat` with self-loops, eigenvalues counted as indices of Mathlib's eigenbasis.
`sample_multiplicity_ae`: almost surely, for every `ε > 0`, eventually in `N`, at least `2l+1` eigenvalues lie
within `ε` of `sphS ξ l`.  `sample_multiplicity_all_ae`: the same for all degrees `l ≤ L0` on one null set.
`sample_spectrum_count_ae`, `sample_spectrum_clusters_ae`: under the HYPOTHESIS `hdist` that the values
`sphS ξ l`, `l ≤ L0`, are pairwise distinct (NOT proved; false for `ξ = 0`), the `ε`-clusters are disjoint for
small `ε` and together contain at least `(L0+1)²` eigenvalues.
NOT formalised: EXACTLY `2l+1` (needs completeness of the spherical harmonics, the addition theorem and an
operator-norm comparison of the sample matrix with a finite-rank kernel matrix), `hdist`, a rate in `N`,
measurability.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 26 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSampleMultProb

open MeasureTheory ProbabilityTheory Set Metric Real Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal

namespace CTG.FunkHecke.SampleMultAE

open CTG.FunkHecke CTG.FunkHecke.Sample CTG.FunkHecke.SampleEig CTG.FunkHecke.SampleMult
  CTG.FunkHecke.SampleMultProb

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

set_option maxHeartbeats 800000 in
/-- **Almost surely, at least `2l+1` eigenvalues of `S_N` converge to `s_l`**: for every `ε > 0`, eventually
in `N`, at least `2l+1` indices of the eigenbasis of `S_N` (first `N` points, WITH self-loop, fixed `ξ`) have
their eigenvalue within `ε` of `sphS ξ l`. -/
theorem sample_multiplicity_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (l : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop,
      2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N =>
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l| ≤ ε)).card := by
  obtain ⟨F, γ0, hF1, hγ0, hmain⟩ := sample_multiplicity (μ := μ) ξ l
  have hF : 0 < F := by linarith
  set Z := sphZ ξ with hZd
  have hZ : 0 < Z := sphZ_pos ξ
  set m : ℝ := ((2 * l + 1 : ℕ) : ℝ) with hmd
  have hm1 : (1:ℝ) ≤ m := by
    simp only [hmd]; exact_mod_cast (by omega : 1 ≤ 2 * l + 1)
  have hm0 : 0 < m := by linarith
  set δ : ℝ := γ0 / (2 * m) with hδd
  have hδ : 0 < δ := by positivity
  have hmδe : m * δ = γ0 / 2 := by simp only [hδd]; field_simp
  have hmδ : m * δ < γ0 := by rw [hmδe]; linarith
  have hg : 0 < γ0 - m * δ := by linarith
  set κ : ℝ := 2 * F * √m / ((Z / 4) * (γ0 - m * δ)) with hκd
  have hden : 0 < (Z / 4) * (γ0 - m * δ) := mul_pos (by positivity) hg
  have hκ : 0 ≤ κ := div_nonneg (by positivity) hden.le
  have hκe : κ * ((Z / 4) * (γ0 - m * δ)) = 2 * F * √m := by
    simp only [hκd]; exact div_mul_cancel₀ _ hden.ne'
  set ηq : ℕ → ℝ := fun q => min (Z / 4) (1 / ((q:ℝ) + 1)) with hηqd
  have hηq : ∀ q, 0 < ηq q := fun q => lt_min (by positivity) (by positivity)
  have hone : ∀ q, ∀ᵐ ω ∂μ, ∀ᶠ N in atTop,
      2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N =>
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
          ≤ N * errE ξ F (ηq q) N * F * √m
              / ((((N:ℝ) - 1) * Z / 4) * (γ0 - m * δ)))).card := by
    intro q
    set η := ηq q with hηd
    have hη : 0 < η := hηq q
    set a1 : ℝ := η ^ 2 / (2 * F ^ 2) with ha1
    set a2 : ℝ := η ^ 2 / 2 with ha2
    set a3 : ℝ := δ ^ 2 / (2 * F ^ 4) with ha3
    set c : ℝ := min (min a1 a2) a3
    have hc : 0 < c := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have hca1 : c ≤ a1 := (min_le_left _ _).trans (min_le_left _ _)
    have hca2 : c ≤ a2 := (min_le_left _ _).trans (min_le_right _ _)
    have hca3 : c ≤ a3 := min_le_right _ _
    have h := bc_lin (μ := μ) (fun N => {ω | ¬ (2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N =>
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
          ≤ N * errE ξ F η N * F * √m
              / ((((N:ℝ) - 1) * Z / 4) * (γ0 - m * δ)))).card)})
      (C := m * (4 * Real.exp a1) + 2 * Real.exp a2 + m * m * 2) (by positivity) hc (fun N hN => by
        have hP := hmain X hind hX hlaw hN hη (min_le_left _ _) hδ hmδ
        refine hP.trans ?_
        rw [Finset.card_range]
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        have hNne : (N:ℝ) ≠ 0 := by linarith
        have hec : 0 ≤ Real.exp (-(c * N)) := (Real.exp_pos _).le
        have e1 : Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2))
            ≤ Real.exp a1 * Real.exp (-(c * N)) := by
          rw [show -((N - 1) * η ^ 2) / (2 * F ^ 2) = -(((N:ℝ) - 1) * a1) by
            simp only [ha1]; field_simp, exp_shift]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (neg_le_neg (mul_le_mul_of_nonneg_right hca1 hN0))) (Real.exp_pos _).le
        have e2 : Real.exp (-((N - 1) * η ^ 2) / 2) ≤ Real.exp a2 * Real.exp (-(c * N)) := by
          rw [show -((N - 1) * η ^ 2) / 2 = -(((N:ℝ) - 1) * a2) by
            simp only [ha2]; ring, exp_shift]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (neg_le_neg (mul_le_mul_of_nonneg_right hca2 hN0))) (Real.exp_pos _).le
        have hexp : -((N:ℝ) * δ) ^ 2 / (2 * ((N:ℝ) * (F ^ 2) ^ 2)) = -(a3 * N) := by
          simp only [ha3]
          rw [div_eq_iff (by positivity)]
          field_simp
        have e3 : Real.exp (-((N:ℝ) * δ) ^ 2 / (2 * ((N:ℝ) * (F ^ 2) ^ 2)))
            ≤ N * Real.exp (-(c * N)) := by
          rw [hexp]
          calc Real.exp (-(a3 * N)) ≤ Real.exp (-(c * N)) :=
                Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hca3 hN0))
            _ ≤ N * Real.exp (-(c * N)) := le_mul_of_one_le_left hec hN1
        have h1 := mul_le_mul_of_nonneg_left e1 (show (0:ℝ) ≤ m * (4 * N) by positivity)
        have h2 := mul_le_mul_of_nonneg_left e2 (show (0:ℝ) ≤ 2 * N by positivity)
        have h3 := mul_le_mul_of_nonneg_left e3 (show (0:ℝ) ≤ m * m * 2 by positivity)
        calc _ = m * (4 * N) * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2))
              + 2 * N * Real.exp (-((N - 1) * η ^ 2) / 2)
              + m * m * 2 * Real.exp (-((N:ℝ) * δ) ^ 2 / (2 * ((N:ℝ) * (F ^ 2) ^ 2))) := by ring
          _ ≤ m * (4 * N) * (Real.exp a1 * Real.exp (-(c * N)))
              + 2 * N * (Real.exp a2 * Real.exp (-(c * N)))
              + m * m * 2 * (N * Real.exp (-(c * N))) := add_le_add (add_le_add h1 h2) h3
          _ = _ := by ring)
    filter_upwards [h] with ω hω
    filter_upwards [hω] with N hN
    by_contra hc'
    exact hN hc'
  have hall := ae_all_iff.mpr hone
  filter_upwards [hall] with ω hω
  intro ε hε
  obtain ⟨q, M, hqM⟩ := small_errE ξ hF1 hκ hε
  filter_upwards [hω q, eventually_ge_atTop (M + 2)] with N hN hNM
  refine hN.trans (Finset.card_le_card ?_)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  refine hj.trans ?_
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  have hE : 0 ≤ errE ξ F (ηq q) N := by
    unfold errE
    have h2 : 0 ≤ 2 * F / ((N:ℝ) - 1) := div_nonneg (by linarith) hN1.le
    have h3 : 0 ≤ ηq q * (1 + F) := mul_nonneg (hηq q).le (by linarith)
    exact div_nonneg (by linarith) hZ.le
  have hP : 0 ≤ errE ξ F (ηq q) N * F * √m :=
    mul_nonneg (mul_nonneg hE hF.le) (Real.sqrt_nonneg m)
  have hd : 0 < (((N:ℝ) - 1) * Z / 4) * (γ0 - m * δ) := mul_pos (by positivity) hg
  have hstep : N * errE ξ F (ηq q) N * F * √m / ((((N:ℝ) - 1) * Z / 4) * (γ0 - m * δ))
      ≤ κ * errE ξ F (ηq q) N := by
    rw [div_le_iff₀ hd]
    have hk : κ * errE ξ F (ηq q) N * ((((N:ℝ) - 1) * Z / 4) * (γ0 - m * δ))
        = (2 * ((N:ℝ) - 1)) * (errE ξ F (ηq q) N * F * √m) := by
      rw [show κ * errE ξ F (ηq q) N * ((((N:ℝ) - 1) * Z / 4) * (γ0 - m * δ))
          = errE ξ F (ηq q) N * ((N:ℝ) - 1) * (κ * ((Z / 4) * (γ0 - m * δ))) by ring, hκe]
      ring
    rw [hk]
    have h0 := mul_nonneg (show (0:ℝ) ≤ (N:ℝ) - 2 by linarith) hP
    have h1 : N * errE ξ F (ηq q) N * F * √m = (2 * ((N:ℝ) - 1)) * (errE ξ F (ηq q) N * F * √m)
        - ((N:ℝ) - 2) * (errE ξ F (ηq q) N * F * √m) := by ring
    rw [h1]; linarith
  exact hstep.trans (hqM N hNM)

/-- One null set for all degrees: almost surely, for every `ε > 0` and every `L0`, eventually in `N`, for
every `l ≤ L0` at least `2l+1` indices have their eigenvalue within `ε` of `sphS ξ l`. -/
theorem sample_multiplicity_all_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ L0 : ℕ, ∀ᶠ N in atTop, ∀ l ≤ L0,
      2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N =>
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l| ≤ ε)).card := by
  have hall := ae_all_iff.mpr (fun l => sample_multiplicity_ae X hind hX hlaw ξ l)
  filter_upwards [hall] with ω hω
  intro ε hε L0
  have h2 := (Filter.eventually_all_finset (Finset.range (L0 + 1))).mpr
    (fun l _ => hω l ε hε)
  filter_upwards [h2] with N hN l hl
  exact hN l (Finset.mem_range.mpr (by omega))

/-! ## Counting over several degrees -/

theorem sum_odd (n : ℕ) : ∑ l ∈ Finset.range n, (2 * l + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- If two centres are more than `2ε` apart, their `ε`-clusters are disjoint. -/
theorem nbhd_disjoint {N : ℕ} (v : Fin N → ℝ) {a b ε : ℝ} (hab : 2 * ε < |a - b|) :
    Disjoint (Finset.univ.filter (fun j : Fin N => |v j - a| ≤ ε))
      (Finset.univ.filter (fun j : Fin N => |v j - b| ≤ ε)) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
  have h := abs_sub_le a (v j) b
  rw [abs_sub_comm a (v j)] at h
  linarith

/-- A positive separation of finitely many pairwise different values. -/
theorem exists_sep (s : ℕ → ℝ) (L0 : ℕ)
    (hdist : ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → s l ≠ s l') :
    ∃ ε0 > 0, ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → 2 * ε0 < |s l - s l'| := by
  classical
  set P := ((Finset.range (L0 + 1)) ×ˢ (Finset.range (L0 + 1))).filter
    (fun p : ℕ × ℕ => p.1 ≠ p.2) with hPd
  have hmem : ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → (l, l') ∈ P := by
    intro l hl l' hl' hne
    simp only [hPd, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨by omega, by omega⟩, hne⟩
  by_cases hP : P.Nonempty
  · obtain ⟨p, hp, hmin⟩ := P.exists_min_image (fun p => |s p.1 - s p.2|) hP
    have hp' := hp
    simp only [hPd, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp'
    have hpos : 0 < |s p.1 - s p.2| :=
      abs_pos.mpr (sub_ne_zero.mpr (hdist p.1 (by omega) p.2 (by omega) hp'.2))
    refine ⟨|s p.1 - s p.2| / 3, by positivity, fun l hl l' hl' hne => ?_⟩
    have h : |s p.1 - s p.2| ≤ |s l - s l'| := hmin (l, l') (hmem l hl l' hl' hne)
    linarith
  · refine ⟨1, one_pos, fun l hl l' hl' hne => ?_⟩
    exact absurd ⟨(l, l'), hmem l hl l' hl' hne⟩ hP

open Classical in
/-- Deterministic count: separated centres `s_0, …, s_{L0}` and at least `2l+1` values in the `ε`-cluster of
`s_l` give at least `(L0+1)²` values in the union of the clusters. -/
theorem count_det {N : ℕ} (v : Fin N → ℝ) (s : ℕ → ℝ) (L0 : ℕ) {ε : ℝ}
    (hsep : ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → 2 * ε < |s l - s l'|)
    (hc : ∀ l ≤ L0, 2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N => |v j - s l| ≤ ε)).card) :
    (L0 + 1) ^ 2 ≤ (Finset.univ.filter (fun j : Fin N => ∃ l ≤ L0, |v j - s l| ≤ ε)).card := by
  have hU : Finset.univ.filter (fun j : Fin N => ∃ l ≤ L0, |v j - s l| ≤ ε)
      = (Finset.range (L0 + 1)).biUnion
          (fun l => Finset.univ.filter (fun j : Fin N => |v j - s l| ≤ ε)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Nat.lt_succ_iff]
  rw [hU, Finset.card_biUnion, ← sum_odd]
  · exact Finset.sum_le_sum fun l hl => hc l (by have := Finset.mem_range.mp hl; omega)
  · intro l hl l' hl' hne
    have hl2 : l < L0 + 1 := by simpa using hl
    have hl2' : l' < L0 + 1 := by simpa using hl'
    exact nbhd_disjoint v (hsep l (by omega) l' (by omega) hne)

open Classical in
/-- **At least `(L0+1)²` eigenvalues near the first `L0+1` population values.**
HYPOTHESIS `hdist`: the values `sphS ξ l`, `l ≤ L0`, are pairwise different (not proven in these files).
Almost surely, for every `ε > 0`, eventually in `N`, at least `(L0+1)²` indices of the eigenbasis of `S_N`
have their eigenvalue within `ε` of some `sphS ξ l` with `l ≤ L0`. -/
theorem sample_spectrum_count_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (L0 : ℕ)
    (hdist : ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → sphS ξ l ≠ sphS ξ l') :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop,
      (L0 + 1) ^ 2 ≤ (Finset.univ.filter (fun j : Fin N => ∃ l ≤ L0,
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l| ≤ ε)).card := by
  obtain ⟨ε0, hε0, hsep0⟩ := exists_sep (fun l => sphS ξ l) L0 hdist
  filter_upwards [sample_multiplicity_all_ae X hind hX hlaw ξ] with ω hω
  intro ε hε
  have hε' : 0 < min ε ε0 := lt_min hε hε0
  filter_upwards [hω (min ε ε0) hε' L0] with N hN
  have hsep : ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → 2 * min ε ε0 < |sphS ξ l - sphS ξ l'| := by
    intro l hl l' hl' hne
    have := hsep0 l hl l' hl' hne
    have h2 : min ε ε0 ≤ ε0 := min_le_right _ _
    linarith
  have hcount := count_det (fun j : Fin N =>
    (Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j) (fun l => sphS ξ l) L0 hsep hN
  refine hcount.trans (Finset.card_le_card ?_)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨l, hl, h⟩ := hj
  exact ⟨l, hl, h.trans (min_le_left _ _)⟩

open Classical in
/-- **Disjoint clusters.** HYPOTHESIS `hdist` as above.  There is `ε0 > 0` such that almost surely, for every
`0 < ε ≤ ε0`: the `ε`-clusters of the `sphS ξ l`, `l ≤ L0`, are pairwise disjoint for every `N`, and eventually
in `N` the cluster of `sphS ξ l` has at least `2l+1` indices for every `l ≤ L0` and the union of the clusters
has at least `(L0+1)²` indices. -/
theorem sample_spectrum_clusters_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (L0 : ℕ)
    (hdist : ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → sphS ξ l ≠ sphS ξ l') :
    ∃ ε0 > 0, ∀ᵐ ω ∂μ, ∀ ε, 0 < ε → ε ≤ ε0 →
      (∀ N : ℕ, ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' →
        Disjoint (Finset.univ.filter (fun j : Fin N =>
            |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l| ≤ ε))
          (Finset.univ.filter (fun j : Fin N =>
            |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l'| ≤ ε))) ∧
      ∀ᶠ N in atTop,
        (∀ l ≤ L0, 2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N =>
          |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l| ≤ ε)).card) ∧
        (L0 + 1) ^ 2 ≤ (Finset.univ.filter (fun j : Fin N => ∃ l ≤ L0,
          |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l| ≤ ε)).card := by
  obtain ⟨ε0, hε0, hsep0⟩ := exists_sep (fun l => sphS ξ l) L0 hdist
  refine ⟨ε0, hε0, ?_⟩
  filter_upwards [sample_multiplicity_all_ae X hind hX hlaw ξ] with ω hω
  intro ε hε hεle
  have hsep : ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → 2 * ε < |sphS ξ l - sphS ξ l'| := by
    intro l hl l' hl' hne
    have := hsep0 l hl l' hl' hne
    linarith
  refine ⟨fun N l hl l' hl' hne => nbhd_disjoint _ (hsep l hl l' hl' hne), ?_⟩
  filter_upwards [hω ε hε L0] with N hN
  exact ⟨hN, count_det (fun j : Fin N =>
    (Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j) (fun l => sphS ξ l) L0 hsep hN⟩

end CTG.FunkHecke.SampleMultAE

