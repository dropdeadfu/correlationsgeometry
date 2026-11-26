/-
Thirty-ninth file: the values `s_l` are strictly decreasing, hence pairwise distinct, for low degrees and small
`ξ`.  Imports `CorrelationsToGeometryFunkHeckeLink` (which loads the seventh file) and
`CorrelationsToGeometryFunkHeckeSampleMultAE` (compiled modules under `.tools/leanbuild`); namespace
`CTG.FunkHecke.Distinct`; check with `./check_funk_hecke_distinct.sh`.
Condition (C): `0 < ξ ≤ 1/20`, `ξ² L(L+1) ≤ 1` and `ξ⁴ L² (L+1)³ ≤ 3`.  Under (C): `sphS_succ_lt`
(`s_{l+1} < s_l` for `l+1 ≤ L`), `sphS_strictAnti`, `sphS_distinct`; `sphS_zero` (`s_0 = 1`), `sphS_ge`
(`s_l ≥ 2/5`); the same for the copy of the definitions in the Funk–Hecke file (`fh_*`); and
`sample_spectrum_count_ae'`, `sample_spectrum_clusters_ae'`: the cluster statements of the thirty-sixth file
WITHOUT the hypothesis `hdist`, under (C) with `L = L0`.
The second condition of (C) comes from the absolute Taylor remainder of `sphere_F1_true`; e.g. `ξ = 0.05`
allows `L0 ≤ 13`.  NOT formalised: distinctness or monotonicity of `s_l` for all `l`; exactly `2l+1`.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 26/27 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeLink
import CorrelationsToGeometryFunkHeckeSampleMultAE

open MeasureTheory ProbabilityTheory Filter

namespace CTG.FunkHecke.Distinct

open CTG.Reals2.SphereOneDim (sphere_F1_true sphere_constants sphSigma sphM sphere_gap)

/-- Arithmetic core: two-sided Taylor bounds at `A = r(r+1)` and `B = (r+1)(r+2)` with
`0 ≤ a ≤ (51/100)σ²`, `0 ≤ b ≤ (27/50)σ³`, `σ B ≤ 1/2`, `(σB)²(r+2) ≤ 4/5` give `s1 < s0`. -/
theorem step_arith {σ a b r s0 s1 : ℝ} (hσ : 0 < σ) (hr : 0 ≤ r)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 51 / 100 * σ ^ 2) (hb0 : 0 ≤ b) (hb1 : b ≤ 27 / 50 * σ ^ 3)
    (h0 : |s0 - 1 + σ * (r * (r + 1)) - a * (r * (r + 1)) ^ 2| ≤ b * (r * (r + 1)) ^ 3)
    (h1 : |s1 - 1 + σ * ((r + 1) * (r + 1 + 1)) - a * ((r + 1) * (r + 1 + 1)) ^ 2|
      ≤ b * ((r + 1) * (r + 1 + 1)) ^ 3)
    (hv : σ * ((r + 1) * (r + 2)) ≤ 1 / 2)
    (hw : (σ * ((r + 1) * (r + 2))) ^ 2 * (r + 2) ≤ 4 / 5) : s1 < s0 := by
  set A := r * (r + 1) with hA
  set B := (r + 1) * (r + 2) with hB
  have hB' : (r + 1) * (r + 1 + 1) = B := by rw [hB]; ring
  rw [hB'] at h1
  rw [abs_le] at h0 h1
  have hA0 : 0 ≤ A := by positivity
  have hAB : A ≤ B := by rw [hA, hB]; nlinarith
  have hdiff : s0 - s1 ≥ σ * (B - A) - a * (B ^ 2 - A ^ 2) - b * (A ^ 3 + B ^ 3) := by
    nlinarith [h0.1, h0.2, h1.1, h1.2]
  have hsq : 0 ≤ B ^ 2 - A ^ 2 := by nlinarith
  have e1 : a * (B ^ 2 - A ^ 2) ≤ 51 / 100 * σ ^ 2 * (B ^ 2 - A ^ 2) :=
    mul_le_mul_of_nonneg_right ha1 hsq
  have hA3 : A ^ 3 ≤ B ^ 3 := pow_le_pow_left₀ hA0 hAB 3
  have hcub : 0 ≤ A ^ 3 + B ^ 3 := by positivity
  have e2 : b * (A ^ 3 + B ^ 3) ≤ 27 / 50 * σ ^ 3 * (A ^ 3 + B ^ 3) :=
    mul_le_mul_of_nonneg_right hb1 hcub
  have e3 : 27 / 50 * σ ^ 3 * (A ^ 3 + B ^ 3) ≤ 27 / 50 * σ ^ 3 * (2 * B ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- with p = r+1
  set p := r + 1 with hp
  have hp1 : 1 ≤ p := by rw [hp]; linarith
  have hBA : B - A = 2 * p := by rw [hA, hB, hp]; ring
  have hB2 : B ^ 2 - A ^ 2 = 4 * p ^ 3 := by rw [hA, hB, hp]; ring
  have hB3 : B ^ 3 = p ^ 3 * (r + 2) ^ 3 := by rw [hB, hp]; ring
  -- σ p² ≤ σ B ≤ 1/2
  have hσp2 : σ * p ^ 2 ≤ 1 / 2 := by
    have : σ * p ^ 2 ≤ σ * B := mul_le_mul_of_nonneg_left (by rw [hB, hp]; nlinarith) hσ.le
    linarith
  have hσp : 0 < σ * p := by positivity
  have t1 : 51 / 100 * σ ^ 2 * (4 * p ^ 3) ≤ 51 / 25 * (σ * p) * (1 / 2) := by
    have : 51 / 100 * σ ^ 2 * (4 * p ^ 3) = 51 / 25 * (σ * p) * (σ * p ^ 2) := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hσp2 (by positivity)
  have t2 : 27 / 50 * σ ^ 3 * (2 * B ^ 3) ≤ 27 / 25 * (σ * p) * (4 / 5) := by
    have : 27 / 50 * σ ^ 3 * (2 * B ^ 3) = 27 / 25 * (σ * p) * ((σ * B) ^ 2 * (r + 2)) := by
      rw [hB3, hB]; ring
    rw [this]; exact mul_le_mul_of_nonneg_left hw (by positivity)
  rw [hBA, hB2] at hdiff
  rw [hB2] at e1
  nlinarith

/-- `(l+1)(l+2)`-type monotonicity of products of casts. -/
theorem prod_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : x * (x + 1) ≤ y * (y + 1) := by
  nlinarith

/-- **The population eigenvalues on `S²` decrease strictly at low degrees.**  For `0 < ξ ≤ 1/20`,
`l + 1 ≤ L`, `ξ²·L(L+1) ≤ 1` and `ξ⁴·L²(L+1)³ ≤ 3`: `s_{l+1} < s_l`. -/
theorem sphS_succ_lt {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {L l : ℕ} (hl : l + 1 ≤ L)
    (hL1 : ξ ^ 2 * ((L : ℝ) * (L + 1)) ≤ 1) (hL2 : ξ ^ 4 * ((L : ℝ) ^ 2 * (L + 1) ^ 3) ≤ 3) :
    CTG.Reals2.SphereOneDim.sphS ξ (l + 1) < CTG.Reals2.SphereOneDim.sphS ξ l := by
  obtain ⟨hσ0, hσ1, hb0, hb1, hc0, hc1⟩ := sphere_constants hξ hξ1
  have hS : sphSigma ξ = sphM ξ 2 / 4 + sphM ξ 4 / 96 := rfl
  set σ := sphSigma ξ with hσd
  have hD2 : 0 < 32 * σ ^ 2 := by positivity
  have hD3 : 0 < 720 * σ ^ 3 := by positivity
  have ha0 : 0 ≤ sphM ξ 4 / 64 := by
    have := (le_div_iff₀ hD2).mp hb0; rw [zero_mul] at this; positivity
  have ha1 : sphM ξ 4 / 64 ≤ 51 / 100 * σ ^ 2 := by
    have := (div_le_iff₀ hD2).mp hb1; linarith
  have hb0' : 0 ≤ sphM ξ 6 / 720 := by
    have := (le_div_iff₀ hD3).mp hc0; rw [zero_mul] at this; positivity
  have hb1' : sphM ξ 6 / 720 ≤ 27 / 50 * σ ^ 3 := by
    have := (div_le_iff₀ hD3).mp hc1; linarith
  have h0 := sphere_F1_true ξ l
  have h1 := sphere_F1_true ξ (l + 1)
  rw [← hS] at h0 h1
  push_cast at h1
  set r : ℝ := (l : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg l
  have hrL : r + 1 ≤ (L : ℝ) := by rw [hr]; exact_mod_cast hl
  have hB : (r + 1) * (r + 2) ≤ (L : ℝ) * (L + 1) := by
    have := prod_le (by linarith : (0:ℝ) ≤ r + 1) hrL
    linarith
  have hBnn : 0 ≤ (r + 1) * (r + 2) := by positivity
  have hv1 : σ * ((r + 1) * (r + 2)) ≤ ξ ^ 2 / 2 * ((L : ℝ) * (L + 1)) :=
    mul_le_mul hσ1 hB hBnn (by positivity)
  have hv : σ * ((r + 1) * (r + 2)) ≤ 1 / 2 := by linarith
  have hv0 : 0 ≤ σ * ((r + 1) * (r + 2)) := by positivity
  have hsq : (σ * ((r + 1) * (r + 2))) ^ 2 ≤ (ξ ^ 2 / 2 * ((L : ℝ) * (L + 1))) ^ 2 :=
    pow_le_pow_left₀ hv0 hv1 2
  have hw : (σ * ((r + 1) * (r + 2))) ^ 2 * (r + 2) ≤ 4 / 5 := by
    have h3 : (σ * ((r + 1) * (r + 2))) ^ 2 * (r + 2)
        ≤ (ξ ^ 2 / 2 * ((L : ℝ) * (L + 1))) ^ 2 * ((L : ℝ) + 1) :=
      mul_le_mul hsq (by linarith) (by linarith) (by positivity)
    have e : (ξ ^ 2 / 2 * ((L : ℝ) * (L + 1))) ^ 2 * ((L : ℝ) + 1)
        = ξ ^ 4 * ((L : ℝ) ^ 2 * (L + 1) ^ 3) / 4 := by ring
    rw [e] at h3; linarith
  exact step_arith hσ0 hr0 ha0 ha1 hb0' hb1' h0 h1 hv hw

/-- Strict decrease on `0, …, L`. -/
theorem sphS_strictAnti {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {L : ℕ}
    (hL1 : ξ ^ 2 * ((L : ℝ) * (L + 1)) ≤ 1) (hL2 : ξ ^ 4 * ((L : ℝ) ^ 2 * (L + 1) ^ 3) ≤ 3)
    {l l' : ℕ} (hll' : l < l') (hl' : l' ≤ L) : CTG.Reals2.SphereOneDim.sphS ξ l' < CTG.Reals2.SphereOneDim.sphS ξ l := by
  obtain ⟨k, rfl⟩ : ∃ k, l' = l + k + 1 := ⟨l' - l - 1, by omega⟩
  induction k with
  | zero => exact sphS_succ_lt hξ hξ1 (by omega) hL1 hL2
  | succ k ih =>
    have h1 : CTG.Reals2.SphereOneDim.sphS ξ (l + k + 1) < CTG.Reals2.SphereOneDim.sphS ξ l := ih (by omega) (by omega)
    have h2 : CTG.Reals2.SphereOneDim.sphS ξ (l + (k + 1) + 1) < CTG.Reals2.SphereOneDim.sphS ξ (l + k + 1) :=
      sphS_succ_lt hξ hξ1 (L := L) (l := l + k + 1) (by omega) hL1 hL2
    linarith

/-- **`hdist` for `SphereOneDim.sphS`.** -/
theorem sphS_distinct {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {L0 : ℕ}
    (hL1 : ξ ^ 2 * ((L0 : ℝ) * (L0 + 1)) ≤ 1) (hL2 : ξ ^ 4 * ((L0 : ℝ) ^ 2 * (L0 + 1) ^ 3) ≤ 3) :
    ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → CTG.Reals2.SphereOneDim.sphS ξ l ≠ CTG.Reals2.SphereOneDim.sphS ξ l' := by
  intro l hl l' hl' hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact (sphS_strictAnti hξ hξ1 hL1 hL2 h hl').ne'
  · exact (sphS_strictAnti hξ hξ1 hL1 hL2 h hl).ne

/-- `s_0 = 1` for every `ξ`. -/
theorem sphS_zero (ξ : ℝ) : CTG.Reals2.SphereOneDim.sphS ξ 0 = 1 := by
  have h := sphere_F1_true ξ 0
  simp at h
  linarith

/-- **Positivity at low degrees:** `2/5 ≤ s_l` for `l ≤ L`, `0 < ξ ≤ 1/20`, `ξ²·L(L+1) ≤ 1`. -/
theorem sphS_ge {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {L l : ℕ} (hl : l ≤ L)
    (hL1 : ξ ^ 2 * ((L : ℝ) * (L + 1)) ≤ 1) : 2 / 5 ≤ CTG.Reals2.SphereOneDim.sphS ξ l := by
  obtain ⟨hσ0, hσ1, -⟩ := sphere_constants hξ hξ1
  have hlL : (l : ℝ) ≤ L := by exact_mod_cast hl
  have hB := prod_le (Nat.cast_nonneg l) hlL
  have hu : sphSigma ξ * ((l : ℝ) * (l + 1)) ≤ 1 / 2 := by
    have := mul_le_mul hσ1 hB (by positivity) (by positivity)
    linarith
  exact ((sphere_gap hξ hξ1 l).1 hu).1

/-! ## The same for the copy `CTG.FunkHecke.sphS` -/

theorem fh_sphS_distinct {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {L0 : ℕ}
    (hL1 : ξ ^ 2 * ((L0 : ℝ) * (L0 + 1)) ≤ 1) (hL2 : ξ ^ 4 * ((L0 : ℝ) ^ 2 * (L0 + 1) ^ 3) ≤ 3) :
    ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' → CTG.FunkHecke.sphS ξ l ≠ CTG.FunkHecke.sphS ξ l' := by
  intro l hl l' hl' hne
  rw [CTG.FunkHeckeLink.sphS_eq, CTG.FunkHeckeLink.sphS_eq]
  exact sphS_distinct hξ hξ1 hL1 hL2 l hl l' hl' hne

theorem fh_sphS_strictAnti {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {L : ℕ}
    (hL1 : ξ ^ 2 * ((L : ℝ) * (L + 1)) ≤ 1) (hL2 : ξ ^ 4 * ((L : ℝ) ^ 2 * (L + 1) ^ 3) ≤ 3)
    {l l' : ℕ} (hll' : l < l') (hl' : l' ≤ L) :
    CTG.FunkHecke.sphS ξ l' < CTG.FunkHecke.sphS ξ l := by
  rw [CTG.FunkHeckeLink.sphS_eq, CTG.FunkHeckeLink.sphS_eq]
  exact sphS_strictAnti hξ hξ1 hL1 hL2 hll' hl'

theorem fh_sphS_zero (ξ : ℝ) : CTG.FunkHecke.sphS ξ 0 = 1 := by
  rw [CTG.FunkHeckeLink.sphS_eq]; exact sphS_zero ξ

theorem fh_sphS_ge {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 20) {L l : ℕ} (hl : l ≤ L)
    (hL1 : ξ ^ 2 * ((L : ℝ) * (L + 1)) ≤ 1) : 2 / 5 ≤ CTG.FunkHecke.sphS ξ l := by
  rw [CTG.FunkHeckeLink.sphS_eq]; exact sphS_ge hξ hξ1 hl hL1

/-! ## The almost-sure cluster statements without `hdist` -/

open CTG.FunkHecke.Sample CTG.FunkHecke.SampleEig CTG.FunkHecke.SampleMult
  CTG.FunkHecke.SampleMultProb CTG.FunkHecke.SampleMultAE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

open Classical in
/-- `sample_spectrum_count_ae` with `hdist` discharged: for `0 < ξ ≤ 1/20`, `ξ² L0(L0+1) ≤ 1`,
`ξ⁴ L0²(L0+1)³ ≤ 3`, almost surely, for every `ε > 0`, eventually in `N`, at least `(L0+1)²` indices of
the eigenbasis of `S_N` have their eigenvalue within `ε` of some `sphS ξ l`, `l ≤ L0`. -/
theorem sample_spectrum_count_ae' (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 20) (L0 : ℕ)
    (hL1 : ξ ^ 2 * ((L0 : ℝ) * (L0 + 1)) ≤ 1) (hL2 : ξ ^ 4 * ((L0 : ℝ) ^ 2 * (L0 + 1) ^ 3) ≤ 3) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop,
      (L0 + 1) ^ 2 ≤ (Finset.univ.filter (fun j : Fin N => ∃ l ≤ L0,
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - CTG.FunkHecke.sphS ξ l| ≤ ε)).card :=
  sample_spectrum_count_ae X hind hX hlaw ξ L0 (fh_sphS_distinct hξ hξ1 hL1 hL2)

open Classical in
/-- `sample_spectrum_clusters_ae` with `hdist` discharged (same conditions on `ξ`, `L0`). -/
theorem sample_spectrum_clusters_ae' (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) {ξ : ℝ} (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1 / 20) (L0 : ℕ)
    (hL1 : ξ ^ 2 * ((L0 : ℝ) * (L0 + 1)) ≤ 1) (hL2 : ξ ^ 4 * ((L0 : ℝ) ^ 2 * (L0 + 1) ^ 3) ≤ 3) :
    ∃ ε0 > 0, ∀ᵐ ω ∂μ, ∀ ε, 0 < ε → ε ≤ ε0 →
      (∀ N : ℕ, ∀ l ≤ L0, ∀ l' ≤ L0, l ≠ l' →
        Disjoint (Finset.univ.filter (fun j : Fin N =>
            |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - CTG.FunkHecke.sphS ξ l| ≤ ε))
          (Finset.univ.filter (fun j : Fin N =>
            |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - CTG.FunkHecke.sphS ξ l'| ≤ ε))) ∧
      ∀ᶠ N in atTop,
        (∀ l ≤ L0, 2 * l + 1 ≤ (Finset.univ.filter (fun j : Fin N =>
          |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - CTG.FunkHecke.sphS ξ l| ≤ ε)).card) ∧
        (L0 + 1) ^ 2 ≤ (Finset.univ.filter (fun j : Fin N => ∃ l ≤ L0,
          |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - CTG.FunkHecke.sphS ξ l| ≤ ε)).card :=
  sample_spectrum_clusters_ae X hind hX hlaw ξ L0 (fh_sphS_distinct hξ hξ1 hL1 hL2)

end CTG.FunkHecke.Distinct
