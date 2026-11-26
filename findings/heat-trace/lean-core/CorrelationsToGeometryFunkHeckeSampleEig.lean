/-
Thirty-first file: an eigenvalue of the sample matrix on the sphere `S²` near `s_l`, at fixed scale.  Imports
`CorrelationsToGeometryFunkHeckeSample` (compiled module under `.tools/leanbuild`); namespace
`CTG.FunkHecke.SampleEig`; check with `./check_funk_hecke_sample_eig.sh`.
`Smat = D^{-1/2} K D^{-1/2}` on `Fin N` for independent uniform points and the kernel `gk ξ ⟨x,y⟩`, with
self-loops.  `spectral_near` (approximate eigenvector of a real symmetric matrix ⇒ an eigenvalue nearby),
`Smat_mulVec` (link with the sampled walk), `deg_event`, `sq_event`, `mE_pos`, `sample_eigenvalue`: for every `l`,
outside an event of explicit probability there is an eigenvalue of `Smat` within `4·errE/√(sphZ·m)` of `sphS ξ l`;
`sample_eigenvalue_ae`: almost surely, for every `ε`, eventually in `N`.
EXISTENCE only.  NOT formalised: multiplicities (`2l+1` eigenvalues near `s_l`), that every eigenvalue of the
sample matrix is near some `s_l`, an assignment of indices (Mathlib's unordered `eigenvalues` is used), the walk
without self-loops, a rate in `ξ`, measurability of the exceptional sets.  Nested sample.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSample

/-!
# A142: an eigenvalue of the symmetrised sample matrix near `s_l` (sphere, FIXED scale)

Scratch block (namespace `CTG.FunkHecke.SampleEig`), importing Mathlib and the Lean file
`CorrelationsToGeometryFunkHeckeSample`.

* `parseval`, `spectral_near`: for a real symmetric matrix, `∑ (S u - λ u)_i² ≤ ε² ∑ u_i²`,
  `u ≠ 0` ⇒ some eigenvalue is within `ε` of `λ` (via `Matrix.IsHermitian.eigenvectorBasis`).
* `Kmat`, `deg`, `Smat` (`S_N = D^{-1/2} K D^{-1/2}` on `Fin N`, WITH self-loop), `Smat_hermitian`,
  `Smat_mulVec` (exact link to the walk: `(S u - s u)_i = √D_i ((P g)_i - s g_i)`, `u = √D g`),
  `eig_det` (deterministic).
* `deg_event` (degrees `≥ (N-1) sphZ ξ / 4` for all `i < N`), `sq_event`
  (`∑_{j<N} f(X_j)² ≥ N m / 2`), `fE`, `mE`, `mE_pos` (`m = ∫ f² dσ > 0` for
  `f = Re (a·y)^l`, `a = e₁ + i e₂`, concretely).
* `sample_eigenvalue`: with probability at least
  `1 - 4N e^{-(N-1)η²/(2F²)} - 2N e^{-(N-1)η²/2} - 2 e^{-N m²/(8F⁴)}`, `S_N` has an eigenvalue
  within `4 errE / √(sphZ ξ · m)` of `s_l = sphS ξ l`, `errE = 4(η(1+F) + 2F/(N-1))/sphZ ξ`.
* `sample_eigenvalue_ae`: almost surely, for every `ε > 0`, eventually in `N`, `S_N` has an
  eigenvalue within `ε` of `s_l`.
Only existence: no multiplicity, no assignment of indices.
-/

open MeasureTheory ProbabilityTheory Set Metric Real Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal

namespace CTG.FunkHecke.SampleEig

open CTG.FunkHecke CTG.FunkHecke.Sample

/-! ## Spectral lemma -/

theorem parseval {n : Type*} [Fintype n] (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n))
    (x : n → ℝ) : ∑ j, (⇑(b j) ⬝ᵥ x) ^ 2 = ∑ i, x i ^ 2 := by
  have h := b.sum_sq_norm_inner_right (WithLp.toLp 2 x)
  rw [EuclideanSpace.real_norm_sq_eq] at h
  have e : ∀ j, ‖⟪b j, WithLp.toLp 2 x⟫‖ ^ 2 = (⇑(b j) ⬝ᵥ x) ^ 2 := fun j => by
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    first
      | (have h3 : ⟪b j, WithLp.toLp 2 x⟫ = x ⬝ᵥ star ⇑(b j) := rfl
         rw [h3, star_trivial, dotProduct_comm])
      | (simp only [PiLp.inner_apply, dotProduct]
         refine Finset.sum_congr rfl fun i _ => ?_
         exact (RCLike.inner_apply _ _).trans (by simp))
  rw [Finset.sum_congr rfl (fun j _ => e j)] at h
  exact h

/-- **Approximate eigenvector ⇒ nearby eigenvalue** (real symmetric matrices). -/
theorem spectral_near {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (u : n → ℝ) (hu : ∃ i, u i ≠ 0) (lam ε : ℝ) (hε : 0 ≤ ε)
    (h : ∑ i, ((A *ᵥ u) i - lam * u i) ^ 2 ≤ ε ^ 2 * ∑ i, u i ^ 2) :
    ∃ j, |hA.eigenvalues j - lam| ≤ ε := by
  by_contra hne
  push_neg at hne
  set b := hA.eigenvectorBasis
  set c : n → ℝ := fun j => ⇑(b j) ⬝ᵥ u
  have hT : Aᵀ = A := by
    have := hA.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have key : ∀ j, ⇑(b j) ⬝ᵥ (fun i => (A *ᵥ u) i - lam * u i)
      = (hA.eigenvalues j - lam) * c j := by
    intro j
    have h1 : ⇑(b j) ⬝ᵥ (A *ᵥ u) = hA.eigenvalues j * c j := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hT, hA.mulVec_eigenvectorBasis, smul_dotProduct,
        smul_eq_mul]
    have h2 : (fun i => (A *ᵥ u) i - lam * u i) = A *ᵥ u - lam • u := by
      funext i; simp [Pi.sub_apply, Pi.smul_apply]
    rw [h2, dotProduct_sub, dotProduct_smul, h1, smul_eq_mul]
    simp only [c]; ring
  have hP1 := parseval b (fun i => (A *ᵥ u) i - lam * u i)
  have hP2 := parseval b u
  have hP1' : ∑ j, ((hA.eigenvalues j - lam) * c j) ^ 2 = ∑ i, ((A *ᵥ u) i - lam * u i) ^ 2 := by
    rw [← hP1]; exact Finset.sum_congr rfl fun j _ => (congrArg (fun t => t ^ 2) (key j)).symm
  have hpos : 0 < ∑ i, u i ^ 2 := by
    obtain ⟨i, hi⟩ := hu
    exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun j _ => sq_nonneg (u j))
      (Finset.mem_univ i))
  have hcs : ∑ j, c j ^ 2 = ∑ i, u i ^ 2 := hP2
  have hc : ∃ j, c j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : ∑ j, c j ^ 2 = 0 := Finset.sum_eq_zero fun j _ => by rw [hc j]; ring
    rw [hcs] at this; linarith
  obtain ⟨j0, hj0⟩ := hc
  have hlt : ε ^ 2 * ∑ j, c j ^ 2 < ∑ j, ((hA.eigenvalues j - lam) * c j) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro j _
      rw [mul_pow]
      have : ε ^ 2 ≤ (hA.eigenvalues j - lam) ^ 2 := by
        have := hne j; nlinarith [abs_nonneg (hA.eigenvalues j - lam), sq_abs (hA.eigenvalues j - lam)]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      rw [mul_pow]
      have : ε ^ 2 < (hA.eigenvalues j0 - lam) ^ 2 := by
        have := hne j0; nlinarith [abs_nonneg (hA.eigenvalues j0 - lam), sq_abs (hA.eigenvalues j0 - lam)]
      exact mul_lt_mul_of_pos_right this (by positivity)
  rw [hcs, hP1'] at hlt
  linarith

/-! ## The symmetrised sample matrix -/

theorem Kx_symm (ξ : ℝ) (x y : S2) : Kx ξ x y = Kx ξ y x := by
  unfold Kx; rw [real_inner_comm]

/-- Degree `D_i = ∑_j K(y_i, y_j)` (with self-loop). -/
noncomputable def deg {N : ℕ} (ξ : ℝ) (y : Fin N → S2) (i : Fin N) : ℝ :=
  ∑ j, Kx ξ (y i) (y j)

/-- `S_N = D^{-1/2} K D^{-1/2}`. -/
noncomputable def Smat {N : ℕ} (ξ : ℝ) (y : Fin N → S2) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => Kx ξ (y i) (y j) / (√(deg ξ y i) * √(deg ξ y j))

theorem deg_pos {N : ℕ} (ξ : ℝ) (y : Fin N → S2) (i : Fin N) : 0 < deg ξ y i :=
  Finset.sum_pos (fun j _ => Kx_pos ξ _ _) ⟨i, Finset.mem_univ _⟩

theorem deg_le {N : ℕ} (ξ : ℝ) (y : Fin N → S2) (i : Fin N) : deg ξ y i ≤ N := by
  unfold deg
  calc ∑ j, Kx ξ (y i) (y j) ≤ ∑ _j : Fin N, (1:ℝ) :=
        Finset.sum_le_sum fun j _ => Kx_le_one ξ _ _
    _ = N := by simp

theorem Smat_hermitian {N : ℕ} (ξ : ℝ) (y : Fin N → S2) : (Smat ξ y).IsHermitian := by
  show (Smat ξ y)ᴴ = Smat ξ y
  ext i j
  rw [conjTranspose_apply, star_trivial]
  unfold Smat
  rw [Kx_symm, mul_comm (√(deg ξ y j))]

/-- Exact link with the walk: `(S u - s u)_i = √D_i ((∑_j K_ij g_j)/D_i - s g_i)`, `u = √D g`. -/
theorem Smat_mulVec {N : ℕ} (ξ : ℝ) (y : Fin N → S2) (g : Fin N → ℝ) (s : ℝ) (i : Fin N) :
    (Smat ξ y *ᵥ (fun j => √(deg ξ y j) * g j)) i - s * (√(deg ξ y i) * g i)
      = √(deg ξ y i) * ((∑ j, Kx ξ (y i) (y j) * g j) / deg ξ y i - s * g i) := by
  have hsq : ∀ j, 0 < √(deg ξ y j) := fun j => Real.sqrt_pos.mpr (deg_pos ξ y j)
  have e1 : (Smat ξ y *ᵥ (fun j => √(deg ξ y j) * g j)) i
      = (∑ j, Kx ξ (y i) (y j) * g j) / √(deg ξ y i) := by
    simp only [mulVec, dotProduct, Smat]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hsq i; have := hsq j
    field_simp
  rw [e1]
  have hD : deg ξ y i = √(deg ξ y i) ^ 2 := (Real.sq_sqrt (deg_pos ξ y i).le).symm
  set a := √(deg ξ y i) with ha
  have hapos : 0 < a := hsq i
  rw [hD]
  field_simp

/-- **Deterministic eigenvalue estimate.** -/
theorem eig_det {N : ℕ} (ξ : ℝ) (y : Fin N → S2) (g : Fin N → ℝ) (s : ℝ) {E dmin : ℝ}
    (hE : 0 ≤ E) (hd : 0 < dmin) (hdeg : ∀ i, dmin ≤ deg ξ y i)
    (herr : ∀ i, |(∑ j, Kx ξ (y i) (y j) * g j) / deg ξ y i - s * g i| ≤ E)
    (hG : 0 < ∑ i, g i ^ 2) :
    ∃ j, |(Smat_hermitian ξ y).eigenvalues j - s| ≤ N * E / √(dmin * ∑ i, g i ^ 2) := by
  set G := ∑ i, g i ^ 2
  have hdG : 0 < dmin * G := mul_pos hd hG
  set ε := N * E / √(dmin * G)
  have hε : 0 ≤ ε := by positivity
  apply spectral_near _ (Smat_hermitian ξ y) (fun j => √(deg ξ y j) * g j) _ s ε hε
  · simp_rw [Smat_mulVec]
    have h1 : ∑ i, (√(deg ξ y i) * ((∑ j, Kx ξ (y i) (y j) * g j) / deg ξ y i - s * g i)) ^ 2
        ≤ ∑ _i : Fin N, (N:ℝ) * E ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (deg_pos ξ y i).le]
      have hsq : ((∑ j, Kx ξ (y i) (y j) * g j) / deg ξ y i - s * g i) ^ 2 ≤ E ^ 2 := by
        have := herr i
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      exact mul_le_mul (deg_le ξ y i) hsq (sq_nonneg _) (Nat.cast_nonneg _)
    have h2 : dmin * G ≤ ∑ i, (√(deg ξ y i) * g i) ^ 2 := by
      simp only [G]; rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (deg_pos ξ y i).le]
      exact mul_le_mul_of_nonneg_right (hdeg i) (sq_nonneg _)
    have hε2 : ε ^ 2 * (dmin * G) = (N:ℝ) * ((N:ℝ) * E ^ 2) := by
      simp only [ε]
      rw [div_pow, Real.sq_sqrt hdG.le]
      field_simp
    calc _ ≤ ∑ _i : Fin N, (N:ℝ) * E ^ 2 := h1
      _ = (N:ℝ) * ((N:ℝ) * E ^ 2) := by simp
      _ = ε ^ 2 * (dmin * G) := hε2.symm
      _ ≤ ε ^ 2 * ∑ i, (√(deg ξ y i) * g i) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  · by_contra hc
    push_neg at hc
    have : G = 0 := Finset.sum_eq_zero fun i _ => by
      have h := hc i
      have : g i = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (Real.sqrt_pos.mpr (deg_pos ξ y i)).ne'
        · exact h'
      rw [this]; ring
    linarith

/-! ## Events -/

section Events

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem card_erase_range {N i : ℕ} (hi : i < N) :
    (((Finset.range N).erase i).card : ℝ) = (N : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hi), Finset.card_range,
    Nat.cast_sub (by omega)]
  simp

/-- **Degree event.** For `N ≥ 2`, `0 < η ≤ sphZ ξ / 4`: all degrees of the first `N` points are
`≥ (N-1) sphZ ξ / 4`, outside an event of probability at most `2 N exp(-(N-1) η² / 2)`. -/
theorem deg_event (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη : 0 < η)
    (hηb : η ≤ sphZ ξ / 4) :
    μ.real {ω | ∃ i < N, ∑ j ∈ Finset.range N, Kx ξ (X i ω) (X j ω) < (N - 1) * sphZ ξ / 4}
      ≤ 2 * N * Real.exp (-((N - 1) * η ^ 2) / 2) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set ε : ℝ := ((N:ℝ) - 1) * η
  have hε : 0 ≤ ε := by positivity
  set E : ℕ → Set Ω := fun i => {ω | ε ≤ |∑ j ∈ (Finset.range N).erase i,
    (Kx ξ (X i ω) (X j ω) - ∫ z, Kx ξ (X i ω) z ∂sigma)|}
  have hP : ∀ i ∈ Finset.range N, μ.real (E i) ≤ 2 * Real.exp (-((N - 1) * η ^ 2) / 2) := by
    intro i hi
    have := cond_one X hind hX hlaw (fun x z => Kx ξ x z) (Kx_continuous ξ) zero_le_one
      (fun x z => by rw [abs_of_pos (Kx_pos ξ x z)]; exact Kx_le_one ξ x z) i
      ((Finset.range N).erase i) (Finset.notMem_erase i _) hε
    refine this.trans (le_of_eq ?_)
    rw [card_erase_range (Finset.mem_range.mp hi)]
    congr 2
    simp only [ε]
    have : (0:ℝ) < (N:ℝ) - 1 := by linarith
    field_simp
  have hsub : {ω | ∃ i < N, ∑ j ∈ Finset.range N, Kx ξ (X i ω) (X j ω) < (N - 1) * sphZ ξ / 4}
      ⊆ ⋃ i ∈ Finset.range N, E i := by
    intro ω hω
    obtain ⟨i, hi, hlt⟩ := hω
    have hiN : i ∈ Finset.range N := Finset.mem_range.mpr hi
    simp only [Set.mem_iUnion]
    refine ⟨i, hiN, ?_⟩
    by_contra hnot
    simp only [E, Set.mem_setOf_eq, not_le] at hnot
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      card_erase_range hi, degree_eq] at hnot
    have hsplit := (Finset.sum_erase_add _ (fun j => Kx ξ (X i ω) (X j ω)) hiN).symm
    have hKii := Kx_pos ξ (X i ω) (X i ω)
    have := (abs_lt.mp hnot).1
    simp only [ε] at this
    nlinarith
  calc _ ≤ μ.real (⋃ i ∈ Finset.range N, E i) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.range N, μ.real (E i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, 2 * Real.exp (-((N - 1) * η ^ 2) / 2) := Finset.sum_le_sum hP
    _ = 2 * N * Real.exp (-((N - 1) * η ^ 2) / 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **Empirical second moment.** For measurable `f` with `|f| ≤ F` and `m = ∫ f² dσ`:
`∑_{j<N} f(X_j)² ≥ N m / 2` outside an event of probability at most `2 exp(-N m²/(8 F⁴))`. -/
theorem sq_event (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (f : S2 → ℝ) (hf : Measurable f) {F : ℝ} (hF : 0 < F)
    (hfF : ∀ y, |f y| ≤ F) (N : ℕ) (hN : 1 ≤ N) :
    μ.real {ω | ∑ j ∈ Finset.range N, f (X j ω) ^ 2 < N * (∫ y, f y ^ 2 ∂sigma) / 2}
      ≤ 2 * Real.exp (-(N * (∫ y, f y ^ 2 ∂sigma) ^ 2) / (8 * F ^ 4)) := by
  set m := ∫ y, f y ^ 2 ∂sigma
  have hm : 0 ≤ m := integral_nonneg fun y => sq_nonneg _
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hB : ∀ z, |f z ^ 2| ≤ F ^ 2 := fun z => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfF z) 2
  have H := hoeffding_fn X hind hX hlaw (fun z => f z ^ 2) (hf.pow_const 2) (sq_nonneg F) hB
    (Finset.range N) (ε := N * m / 2) (by positivity)
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (H.trans (le_of_eq ?_))
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [abs_sub_comm, le_abs]
    left; linarith
  · rw [Finset.card_range]
    congr 2
    field_simp
    ring

end Events

/-! ## The concrete eigenfunction `Re (a·y)^l`, `a = e₁ + i e₂` -/

/-- `e₁`, `e₂` (indices `1`, `2` of `ℝ³`). -/
noncomputable abbrev pE : E3 := EuclideanSpace.single 1 1
noncomputable abbrev qE : E3 := EuclideanSpace.single 2 1

noncomputable def fE (l : ℕ) (y : S2) : ℝ := (cdot pE qE (y : E3) ^ l).re

noncomputable def mE (l : ℕ) : ℝ := ∫ y, fE l y ^ 2 ∂sigma

instance : sigma.IsOpenPosMeasure := ⟨fun U hU hne => by
  have h0 : sigma0 U ≠ 0 := by unfold sigma0; exact MeasureTheory.Measure.IsOpenPosMeasure.open_pos U hU hne
  rw [sigma, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (Real.toNNReal_pos.mpr (by positivity)).ne') h0⟩

theorem mE_pos (l : ℕ) : 0 < mE l := by
  have hc : Continuous (fun y : S2 => fE l y ^ 2) := (harm_cont pE qE l).pow 2
  set y0 : S2 := ⟨EuclideanSpace.single 1 1, by rw [mem_sphere_zero_iff_norm]; simp⟩
  have h1 : fE l y0 = 1 := by simp [fE, y0, cdot, inner3]
  exact integral_pos_of_integrable_nonneg_nonzero (x := y0) hc (integrable_cont _ hc)
    (fun y => sq_nonneg _) (by rw [h1]; norm_num)

/-! ## The eigenvalue theorem -/

section Main

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The one-step error of the walk. -/
noncomputable def errE (ξ F η : ℝ) (N : ℕ) : ℝ := 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ

/-- **An eigenvalue of `S_N` near `s_l`.** For `N ≥ 2`, `0 < η ≤ sphZ ξ / 4`, `F = harmF e₁ e₂ l`,
`m = mE l > 0`: outside an event of probability at most
`4N exp(-(N-1)η²/(2F²)) + 2N exp(-(N-1)η²/2) + 2 exp(-N m²/(8F⁴))`, the matrix
`S_N = D^{-1/2} K D^{-1/2}` of the first `N` points has an eigenvalue `λ` with
`|λ - sphS ξ l| ≤ 4 errE / √(sphZ ξ · m)`. -/
theorem sample_eigenvalue (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (l : ℕ) {N : ℕ} (hN : 2 ≤ N)
    {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) :
    μ.real {ω | ¬ ∃ j : Fin N,
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
          ≤ 4 * errE ξ (harmF pE qE l) η N / √(sphZ ξ * mE l)}
      ≤ 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * harmF pE qE l ^ 2))
        + 2 * N * Real.exp (-((N - 1) * η ^ 2) / 2)
        + 2 * Real.exp (-(N * mE l ^ 2) / (8 * harmF pE qE l ^ 4)) := by
  set F := harmF pE qE l
  have hF1 : 1 ≤ F := one_le_harmF pE qE l
  have hF : 0 < F := by linarith
  set m := mE l
  have hm : 0 < m := mE_pos l
  set Z := sphZ ξ
  have hZ : 0 < Z := sphZ_pos ξ
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  set A : Set Ω := {ω | ∃ i < N,
      4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk ξ (fun y => (cdot pE qE (y : E3) ^ l).re) X N ω i
            - sphS ξ l * (cdot pE qE (X i ω : E3) ^ l).re|}
  set B : Set Ω := {ω | ∃ i < N, ∑ j ∈ Finset.range N, Kx ξ (X i ω) (X j ω) < (N - 1) * sphZ ξ / 4}
  set C : Set Ω := {ω | ∑ j ∈ Finset.range N, fE l (X j ω) ^ 2 < N * (∫ y, fE l y ^ 2 ∂sigma) / 2}
  have hA := walk_harmonic X hind hX hlaw ξ pE qE isotropic_e12 l hN hη hηb
  have hB := deg_event X hind hX hlaw ξ hN hη hηb
  have hC := sq_event X hind hX hlaw (fE l) (harm_cont pE qE l).measurable hF
    (harm_bound pE qE l) N (by omega)
  have hsub : {ω | ¬ ∃ j : Fin N,
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
          ≤ 4 * errE ξ F η N / √(Z * m)} ⊆ A ∪ B ∪ C := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨hnA, hnB⟩, hnC⟩ := hnot
    apply hω
    set y : Fin N → S2 := fun i => X i ω
    set g : Fin N → ℝ := fun i => fE l (X i ω)
    set E := errE ξ F η N
    set dmin : ℝ := ((N:ℝ) - 1) * Z / 4
    have hE : 0 ≤ E := by
      simp only [E, errE]
      have : (0:ℝ) ≤ (N:ℝ) - 1 := by linarith
      positivity
    have hd : 0 < dmin := by
      have : (0:ℝ) < (N:ℝ) - 1 := by linarith
      simp only [dmin]
      positivity
    have hdeg : ∀ i, dmin ≤ deg ξ y i := by
      intro i
      simp only [B, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hnB
      have := hnB i i.2
      unfold deg
      rw [← Finset.sum_range (fun j => Kx ξ (X i ω) (X j ω))]
      exact this
    have herr : ∀ i, |(∑ j, Kx ξ (y i) (y j) * g j) / deg ξ y i - sphS ξ l * g i| ≤ E := by
      intro i
      simp only [A, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hnA
      have := hnA i i.2
      have hw : walk ξ (fun y => (cdot pE qE (y : E3) ^ l).re) X N ω i
          = (∑ j, Kx ξ (y i) (y j) * g j) / deg ξ y i := by
        unfold walk deg
        rw [Finset.sum_range (fun j => Kx ξ (X i ω) (X j ω) * (cdot pE qE (X j ω : E3) ^ l).re),
          Finset.sum_range (fun j => Kx ξ (X i ω) (X j ω))]
        rfl
      rw [hw] at this
      exact this
    have hGge : (N:ℝ) * m / 2 ≤ ∑ i, g i ^ 2 := by
      simp only [C, Set.mem_setOf_eq, not_lt] at hnC
      rw [← Finset.sum_range (fun j => fE l (X j ω) ^ 2)]
      exact hnC
    have hG : 0 < ∑ i, g i ^ 2 := lt_of_lt_of_le (by positivity) hGge
    obtain ⟨j, hj⟩ := eig_det ξ y g (sphS ξ l) hE hd hdeg herr hG
    refine ⟨j, hj.trans ?_⟩
    -- N E / √(dmin G) ≤ 4 E / √(Z m)
    have hlow : (N:ℝ) ^ 2 * (Z * m) / 16 ≤ dmin * ∑ i, g i ^ 2 := by
      have h1 : (N:ℝ) ^ 2 * (Z * m) / 16 ≤ dmin * ((N:ℝ) * m / 2) := by
        have h0 : 0 ≤ (N:ℝ) * ((N:ℝ) - 2) * (Z * m) := by
          have := mul_pos hZ hm
          have : (0:ℝ) ≤ (N:ℝ) - 2 := by linarith
          positivity
        simp only [dmin]; nlinarith [h0]
      exact h1.trans (mul_le_mul_of_nonneg_left hGge hd.le)
    have hs : √((N:ℝ) ^ 2 * (Z * m) / 16) = N * √(Z * m) / 4 := by
      rw [show (N:ℝ) ^ 2 * (Z * m) / 16 = ((N:ℝ) / 4) ^ 2 * (Z * m) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
      ring
    have hZm : 0 < √(Z * m) := Real.sqrt_pos.mpr (mul_pos hZ hm)
    have hN0 : (0:ℝ) < N := by linarith
    calc (N:ℝ) * E / √(dmin * ∑ i, g i ^ 2) ≤ N * E / (N * √(Z * m) / 4) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          rw [← hs]; exact Real.sqrt_le_sqrt hlow
      _ = 4 * E / √(Z * m) := by field_simp
  calc _ ≤ μ.real (A ∪ B ∪ C) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (A ∪ B) + μ.real C := measureReal_union_le _ _
    _ ≤ μ.real A + μ.real B + μ.real C := by linarith [measureReal_union_le (μ := μ) A B]
    _ ≤ _ := by
        have hC' : μ.real C ≤ 2 * Real.exp (-(N * m ^ 2) / (8 * F ^ 4)) := hC
        linarith

end Main

/-! ## Almost surely -/

/-- Deterministic smallness of `κ · errE` along the list `η_q = min (sphZ ξ / 4) (1/(q+1))`. -/
theorem small_errE (ξ : ℝ) {F : ℝ} (hF1 : 1 ≤ F) {κ : ℝ} (hκ : 0 ≤ κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ M : ℕ, ∀ N : ℕ, M + 2 ≤ N →
      κ * errE ξ F (min (sphZ ξ / 4) (1 / ((q:ℝ) + 1))) N ≤ ε := by
  set Z := sphZ ξ with hZd
  have hZ : 0 < Z := sphZ_pos ξ
  set ε' : ℝ := ε / (κ + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨q, hq⟩ := exists_nat_gt (8 * (1 + F) / (Z * ε'))
  obtain ⟨M, hM⟩ := exists_nat_gt (16 * F / (Z * ε') + 1)
  refine ⟨q, M, fun N hNM => ?_⟩
  set η := min (Z / 4) (1 / ((q:ℝ) + 1))
  have hq1 : (0:ℝ) < (q:ℝ) + 1 := by positivity
  have hη1 : η * ((q:ℝ) + 1) ≤ 1 := by
    have : η ≤ 1 / ((q:ℝ) + 1) := min_le_right _ _
    rwa [le_div_iff₀ hq1] at this
  have hkZ : 8 * (1 + F) < ((q:ℝ) + 1) * (Z * ε') := by
    rw [div_lt_iff₀ (by positivity)] at hq; nlinarith
  have hNr : (M:ℝ) + 2 ≤ N := by exact_mod_cast hNM
  have hMZ : 16 * F < ((M:ℝ) - 1 + 1) * (Z * ε') := by
    have : 16 * F / (Z * ε') < M := by linarith
    rw [div_lt_iff₀ (by positivity)] at this; nlinarith
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  have e : errE ξ F η N = 4 * η * (1 + F) / Z + 8 * F / (((N:ℝ) - 1) * Z) := by
    unfold errE; rw [← hZd]; field_simp; ring
  have t1 : 4 * η * (1 + F) / Z ≤ ε' / 2 := by
    rw [div_le_iff₀ hZ]
    refine le_of_mul_le_mul_left ?_ hq1
    have := mul_le_mul_of_nonneg_left hη1 (show (0:ℝ) ≤ 4 * (1 + F) by linarith)
    nlinarith
  have t2 : 8 * F / (((N:ℝ) - 1) * Z) ≤ ε' / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : ((M:ℝ) - 1 + 1) * (Z * ε') ≤ ((N:ℝ) - 1) * (Z * ε') :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith
  have hE : errE ξ F η N ≤ ε' := by rw [e]; linarith
  calc κ * errE ξ F η N ≤ κ * ε' := mul_le_mul_of_nonneg_left hE hκ
    _ ≤ ε := by
        simp only [ε']
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith

section AE

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exp_shift (a N : ℝ) : Real.exp (-((N - 1) * a)) = Real.exp a * Real.exp (-(a * N)) := by
  rw [← Real.exp_add]; congr 1; ring

/-- **Almost surely, `S_N` has eigenvalues converging to `s_l`**: for every `ε > 0`, eventually in
`N`, some eigenvalue of `S_N` (first `N` points, WITH self-loop, fixed `ξ`) lies within `ε` of
`sphS ξ l`. -/
theorem sample_eigenvalue_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (l : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∃ j : Fin N,
      |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l| ≤ ε := by
  set F := harmF pE qE l
  have hF1 : 1 ≤ F := one_le_harmF pE qE l
  have hF : 0 < F := by linarith
  set m := mE l
  have hm : 0 < m := mE_pos l
  set Z := sphZ ξ
  have hZ : 0 < Z := sphZ_pos ξ
  set κ : ℝ := 4 / √(Z * m)
  have hκ : 0 ≤ κ := by positivity
  set ηq : ℕ → ℝ := fun q => min (Z / 4) (1 / ((q:ℝ) + 1))
  have hηq : ∀ q, 0 < ηq q := fun q => lt_min (by positivity) (by positivity)
  have hone : ∀ q, ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ∃ j : Fin N,
      |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
        ≤ 4 * errE ξ F (ηq q) N / √(Z * m) := by
    intro q
    set η := ηq q
    have hη : 0 < η := hηq q
    set a1 : ℝ := η ^ 2 / (2 * F ^ 2)
    set a2 : ℝ := η ^ 2 / 2
    set a3 : ℝ := m ^ 2 / (8 * F ^ 4)
    set c : ℝ := min (min a1 a2) a3
    have hc : 0 < c := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have hca1 : c ≤ a1 := (min_le_left _ _).trans (min_le_left _ _)
    have hca2 : c ≤ a2 := (min_le_left _ _).trans (min_le_right _ _)
    have hca3 : c ≤ a3 := min_le_right _ _
    have h := bc_lin (μ := μ) (fun N => {ω | ¬ ∃ j : Fin N,
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
          ≤ 4 * errE ξ F η N / √(Z * m)})
      (C := 4 * Real.exp a1 + 2 * Real.exp a2 + 2) (by positivity) hc (fun N hN => by
        have hP := sample_eigenvalue X hind hX hlaw ξ l hN hη (min_le_left _ _)
        refine hP.trans ?_
        have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
        have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
        have hec : Real.exp (-(c * N)) ≥ 0 := (Real.exp_pos _).le
        have e1 : Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2))
            ≤ Real.exp a1 * Real.exp (-(c * N)) := by
          rw [show -((N - 1) * η ^ 2) / (2 * F ^ 2) = -(((N:ℝ) - 1) * a1) by
            simp only [a1]; field_simp, exp_shift]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
            (Real.exp_pos _).le
        have e2 : Real.exp (-((N - 1) * η ^ 2) / 2) ≤ Real.exp a2 * Real.exp (-(c * N)) := by
          rw [show -((N - 1) * η ^ 2) / 2 = -(((N:ℝ) - 1) * a2) by
            simp only [a2]; ring, exp_shift]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
            (Real.exp_pos _).le
        have e3 : Real.exp (-(N * m ^ 2) / (8 * F ^ 4)) ≤ N * Real.exp (-(c * N)) := by
          rw [show -(N * m ^ 2) / (8 * F ^ 4) = -(a3 * N) by simp only [a3]; field_simp]
          calc Real.exp (-(a3 * N)) ≤ Real.exp (-(c * N)) :=
                Real.exp_le_exp.mpr (by nlinarith)
            _ ≤ N * Real.exp (-(c * N)) := by nlinarith
        have h1 := mul_le_mul_of_nonneg_left e1 (show (0:ℝ) ≤ 4 * N by positivity)
        have h2 := mul_le_mul_of_nonneg_left e2 (show (0:ℝ) ≤ 2 * N by positivity)
        nlinarith)
    filter_upwards [h] with ω hω
    filter_upwards [hω] with N hN
    by_contra hc'
    exact hN hc'
  have hall := ae_all_iff.mpr hone
  filter_upwards [hall] with ω hω
  intro ε hε
  obtain ⟨q, M, hqM⟩ := small_errE ξ hF1 hκ hε
  filter_upwards [hω q, eventually_ge_atTop (M + 2)] with N hN hNM
  obtain ⟨j, hj⟩ := hN
  refine ⟨j, hj.trans ?_⟩
  have := hqM N hNM
  calc 4 * errE ξ F (ηq q) N / √(Z * m) = κ * errE ξ F (ηq q) N := by simp only [κ]; ring
    _ ≤ ε := this

end AE

end CTG.FunkHecke.SampleEig
