/-
Twenty-ninth file: iterates of the sampled walk on the sphere `S²` at fixed scale.  Imports
`CorrelationsToGeometryFunkHeckeSample` (compiled module under `.tools/leanbuild`); namespace
`CTG.FunkHecke.Powers`; check with `./check_funk_hecke_powers.sh`.
`P_N^k` is the `k`-fold ITERATED application of the sampled walk to the vector `(f(X_j))_j` (that this equals the
`k`-th matrix power is not stated), with self-loops (`loopS`) or without (`noloopS`).  `pow_det` (telescope and
sup-norm contraction), `pow_step` / `pow_step0`: for continuous `f` and every `k`,
`max_i |(P_N^k f)(X_i) − (P_∞^k f)(X_i)| ≤ k·errN` outside an event of probability `k·4N exp(−(N−1)η²/(2F²))`;
`pow_ae` / `pow_ae0` (almost surely, fixed `k`); `pinfPow_harmonic`: `P_∞^k Re(a·y)^l = s_l^k Re(a·y)^l`;
`pow_harmonic(0)`, `pow_harmonic_ae(0)`: the sampled harmonics under the iterated sampled walk.
NOT formalised: the trace and the eigenvalues of the sample matrix (plan in the hand-over notes), a joint limit
in `N`, `ξ`, `k`, measurability of the exceptional sets.  The error grows linearly in `k`; nested sample.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSample

/-!
# A140: powers of the sample walk on the sphere at FIXED scale

Scratch block (namespace `CTG.FunkHecke.Powers`), importing Mathlib and the Lean file
`CorrelationsToGeometryFunkHeckeSample` (which imports `CorrelationsToGeometryFunkHecke`).

Form of `P_N^k`: ITERATED APPLICATION of the walk operator `wOp S ξ X ω` to the vector
`v = (f(X_j))_{j ∈ ℕ}` (only the entries `j < N` enter), i.e. `(wOp S ξ X ω)^[k] v`; `S i` is the
index set of row `i`: `range N` (walk WITH self-loop, `S = loopS N`) or `(range N).erase i`
(WITHOUT self-loop, `S = noloopS N`). That this equals the `k`-th power of the `N × N` matrix is
not stated in this file.

* `wOp_sub`, `wOp_contract`: linearity and contraction in the sup norm over the sample points.
* `pinfPow`, `pinfPow_continuous`, `pinfPow_bound`: iterates of the population walk `P_∞`.
* `pow_det`: deterministic telescope: one-step errors `≤ δ` for `P_∞^m f`, `m < k` ⇒ error `≤ k δ`.
* `pow_step` (with self-loop), `pow_step0` (without): with probability at least
  `1 - 4 k N exp(-(N-1) η²/(2F²))`, for ALL `i < N`,
  `|(P_N^k f)(X_i) - (P_∞^k f)(X_i)| ≤ k · 4 (η (1+F) + 2F/(N-1)) / sphZ ξ`.
* `pow_ae`, `pow_ae0`: almost surely, for every `ε > 0`, eventually in `N`, error `≤ ε` (fixed `k`).
* `pinfPow_harmonic`, `pow_harmonic`, `pow_harmonic_ae` (and `…0` without self-loop):
  `|(P_N^k f)(X_i) - s_l^k f(X_i)|` for `f = Re (a·y)^l`, `a` isotropic.
No hypotheses beyond independence, measurability and law `σ` of the points, continuity and a
bound `|f| ≤ F` with `1 ≤ F`, `N ≥ 2`, `0 < η ≤ sphZ ξ / 4`.
-/

open MeasureTheory ProbabilityTheory Set Metric Real Filter
open scoped RealInnerProductSpace ENNReal NNReal

namespace CTG.FunkHecke.Powers

open CTG.FunkHecke CTG.FunkHecke.Sample

/-! ## The walk operator on vectors indexed by the sample -/

/-- Row `i` of the walk with index sets `S`: `(wOp S ξ X ω v)_i = ∑_{j∈S i} K(X_i,X_j) v_j / ∑_{j∈S i} K(X_i,X_j)`. -/
noncomputable def wOp {Ω : Type*} (S : ℕ → Finset ℕ) (ξ : ℝ) (X : ℕ → Ω → S2) (ω : Ω)
    (v : ℕ → ℝ) (i : ℕ) : ℝ :=
  (∑ j ∈ S i, Kx ξ (X i ω) (X j ω) * v j) / ∑ j ∈ S i, Kx ξ (X i ω) (X j ω)

/-- With self-loop. -/
def loopS (N : ℕ) : ℕ → Finset ℕ := fun _ => Finset.range N

/-- Without self-loop. -/
def noloopS (N : ℕ) : ℕ → Finset ℕ := fun i => (Finset.range N).erase i

/-- The walk without self-loop applied to a function. -/
noncomputable def walk0 {Ω : Type*} (ξ : ℝ) (f : S2 → ℝ) (X : ℕ → Ω → S2) (N : ℕ) (ω : Ω)
    (i : ℕ) : ℝ := wOp (noloopS N) ξ X ω (fun j => f (X j ω)) i

theorem wOp_loop {Ω : Type*} (ξ : ℝ) (f : S2 → ℝ) (X : ℕ → Ω → S2) (N : ℕ) (ω : Ω) (i : ℕ) :
    wOp (loopS N) ξ X ω (fun j => f (X j ω)) i = walk ξ f X N ω i := rfl

theorem wOp_sub {Ω : Type*} (S : ℕ → Finset ℕ) (ξ : ℝ) (X : ℕ → Ω → S2) (ω : Ω)
    (u w : ℕ → ℝ) (i : ℕ) :
    wOp S ξ X ω (fun j => u j - w j) i = wOp S ξ X ω u i - wOp S ξ X ω w i := by
  unfold wOp
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Contraction: if `|v_j| ≤ c` on the (nonempty) row set, then `|(wOp v)_i| ≤ c`. -/
theorem wOp_contract {Ω : Type*} (S : ℕ → Finset ℕ) (ξ : ℝ) (X : ℕ → Ω → S2) (ω : Ω)
    (v : ℕ → ℝ) (i : ℕ) (hS : (S i).Nonempty) {c : ℝ} (hv : ∀ j ∈ S i, |v j| ≤ c) :
    |wOp S ξ X ω v i| ≤ c := by
  unfold wOp
  have hD : 0 < ∑ j ∈ S i, Kx ξ (X i ω) (X j ω) :=
    Finset.sum_pos (fun j _ => Kx_pos ξ _ _) hS
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, Finset.mul_sum]
  calc |∑ j ∈ S i, Kx ξ (X i ω) (X j ω) * v j|
      ≤ ∑ j ∈ S i, |Kx ξ (X i ω) (X j ω) * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ S i, c * Kx ξ (X i ω) (X j ω) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [abs_mul, abs_of_pos (Kx_pos ξ _ _), mul_comm]
        exact mul_le_mul_of_nonneg_right (hv j hj) (Kx_pos ξ _ _).le

/-! ## Iterates of the population walk -/

/-- `P_∞^m f`. -/
noncomputable def pinfPow (ξ : ℝ) (m : ℕ) (f : S2 → ℝ) : S2 → ℝ := (Pinf (gk ξ))^[m] f

theorem Pinf_eq (ξ : ℝ) (f : S2 → ℝ) (x : S2) :
    Pinf (gk ξ) f x = (∫ z, Kx ξ x z * f z ∂sigma) / ((1/2) * sphZ ξ) := by
  unfold Pinf; rw [zonal_eq, zonalOp_one]

theorem Pinf_continuous (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f) {F : ℝ}
    (hfF : ∀ y, |f y| ≤ F) : Continuous (Pinf (gk ξ) f) := by
  have hK := Kx_continuous ξ
  have h : Continuous (fun x => ∫ z, Kx ξ x z * f z ∂sigma) :=
    param_continuous (fun x z => Kx ξ x z * f z) (hK.mul (hf.comp continuous_snd))
      (B := F) (fun x z => by
        rw [abs_mul, abs_of_pos (Kx_pos ξ x z)]
        calc Kx ξ x z * |f z| ≤ 1 * |f z| :=
              mul_le_mul_of_nonneg_right (Kx_le_one ξ x z) (abs_nonneg _)
          _ ≤ F := by rw [one_mul]; exact hfF z)
  have e : Pinf (gk ξ) f = fun x => (∫ z, Kx ξ x z * f z ∂sigma) / ((1/2) * sphZ ξ) :=
    funext (Pinf_eq ξ f)
  rw [e]; exact h.div_const _

theorem Pinf_bound (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f) {F : ℝ}
    (hfF : ∀ y, |f y| ≤ F) (x : S2) : |Pinf (gk ξ) f x| ≤ F := by
  have hq := degree_pos ξ x
  unfold Pinf
  rw [zonalOp_one, ← degree_eq ξ x, abs_div, abs_of_pos hq, div_le_iff₀ hq]
  exact abs_zonal_le ξ f hf hfF x

theorem pinfPow_succ (ξ : ℝ) (m : ℕ) (f : S2 → ℝ) :
    pinfPow ξ (m + 1) f = Pinf (gk ξ) (pinfPow ξ m f) := by
  unfold pinfPow; rw [Function.iterate_succ_apply']

theorem pinfPow_props (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f) {F : ℝ}
    (hfF : ∀ y, |f y| ≤ F) (m : ℕ) :
    Continuous (pinfPow ξ m f) ∧ ∀ y, |pinfPow ξ m f y| ≤ F := by
  induction m with
  | zero => exact ⟨hf, hfF⟩
  | succ m ih =>
    rw [pinfPow_succ]
    exact ⟨Pinf_continuous ξ _ ih.1 ih.2, Pinf_bound ξ _ ih.1 ih.2⟩

/-! ## Deterministic telescope -/

/-- **Telescope.** If the row sets are nonempty and contained in `range N`, and for every `m < k`
the one-step error of `P_∞^m f` is `≤ δ` at all sample points, then the error of the `k`-th
iterate is `≤ k δ` at all sample points. -/
theorem pow_det {Ω : Type*} (S : ℕ → Finset ℕ) (ξ : ℝ) (X : ℕ → Ω → S2) (ω : Ω) (N : ℕ)
    (hSN : ∀ i < N, S i ⊆ Finset.range N) (hSne : ∀ i < N, (S i).Nonempty)
    (f : S2 → ℝ) (k : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hstep : ∀ m < k, ∀ i < N,
      |wOp S ξ X ω (fun j => pinfPow ξ m f (X j ω)) i - pinfPow ξ (m + 1) f (X i ω)| ≤ δ) :
    ∀ i < N, |(wOp S ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω)| ≤ k * δ := by
  induction k with
  | zero => intro i _; simp [pinfPow]
  | succ k ih =>
    intro i hi
    have ih' := ih (fun m hm => hstep m (by omega))
    rw [Function.iterate_succ_apply']
    set u := (wOp S ξ X ω)^[k] (fun j => f (X j ω))
    set w : ℕ → ℝ := fun j => pinfPow ξ k f (X j ω)
    have e : wOp S ξ X ω u i - pinfPow ξ (k + 1) f (X i ω)
        = wOp S ξ X ω (fun j => u j - w j) i
          + (wOp S ξ X ω w i - pinfPow ξ (k + 1) f (X i ω)) := by
      rw [wOp_sub]; ring
    rw [e]
    have h1 : |wOp S ξ X ω (fun j => u j - w j) i| ≤ k * δ :=
      wOp_contract S ξ X ω _ i (hSne i hi) fun j hj =>
        ih' j (Finset.mem_range.mp (hSN i hi hj))
    have h2 := hstep k (by omega) i hi
    calc _ ≤ |wOp S ξ X ω (fun j => u j - w j) i|
          + |wOp S ξ X ω w i - pinfPow ξ (k + 1) f (X i ω)| := abs_add_le _ _
      _ ≤ k * δ + δ := add_le_add h1 h2
      _ = ((k + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-! ## Walk without self-loop: one step -/

section Walk0

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One step WITHOUT self-loop (copy of `walk_one_step` with the row sets `(range N).erase i`;
the self term is dropped). Same bound and probability. -/
theorem walk0_one_step (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f)
    {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F) {N : ℕ} (hN : 2 ≤ N)
    {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) :
    μ.real {ω | ∃ i < N, 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk0 ξ f X N ω i - Pinf (gk ξ) f (X i ω)|}
      ≤ 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
  have hF0 : 0 ≤ F := by linarith
  have hZ := sphZ_pos ξ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  set n : ℝ := (N : ℝ) - 1 with hn
  have hnpos : 0 < n := by linarith
  set ε : ℝ := n * η
  have hε : 0 ≤ ε := by positivity
  set H1 : S2 → S2 → ℝ := fun x z => Kx ξ x z * f z
  set H2 : S2 → S2 → ℝ := fun x z => Kx ξ x z
  have hH1 : Continuous (fun p : S2 × S2 => H1 p.1 p.2) :=
    (Kx_continuous ξ).mul (hf.comp continuous_snd)
  have hH2 : Continuous (fun p : S2 × S2 => H2 p.1 p.2) := Kx_continuous ξ
  have hH1B : ∀ x z, |H1 x z| ≤ F := fun x z => by
    simp only [H1]; rw [abs_mul, abs_of_pos (Kx_pos ξ x z)]
    calc Kx ξ x z * |f z| ≤ 1 * F :=
          mul_le_mul (Kx_le_one ξ x z) (hfF z) (abs_nonneg _) zero_le_one
      _ = F := one_mul F
  have hH2B : ∀ x z, |H2 x z| ≤ F := fun x z => by
    simp only [H2]; rw [abs_of_pos (Kx_pos ξ x z)]; linarith [Kx_le_one ξ x z]
  set E1 : ℕ → Set Ω := fun i =>
    {ω | ε ≤ |∑ j ∈ (Finset.range N).erase i, (H1 (X i ω) (X j ω) - ∫ z, H1 (X i ω) z ∂sigma)|}
  set E2 : ℕ → Set Ω := fun i =>
    {ω | ε ≤ |∑ j ∈ (Finset.range N).erase i, (H2 (X i ω) (X j ω) - ∫ z, H2 (X i ω) z ∂sigma)|}
  have hcard : ∀ i ∈ Finset.range N, (((Finset.range N).erase i).card : ℝ) = n := by
    intro i hi
    rw [Finset.card_erase_of_mem hi, Finset.card_range, Nat.cast_sub (by omega)]
    simp [hn]
  have hexp : 2 * Real.exp (-ε ^ 2 / (2 * (n * F ^ 2)))
      = 2 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
    congr 2
    simp only [ε, hn]
    have : (0:ℝ) < (N:ℝ) - 1 := by linarith
    field_simp
  have hP1 : ∀ i ∈ Finset.range N, μ.real (E1 i)
      ≤ 2 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
    intro i hi
    have := cond_one X hind hX hlaw H1 hH1 hF0 hH1B i ((Finset.range N).erase i)
      (Finset.notMem_erase i _) hε
    rwa [hcard i hi, hexp] at this
  have hP2 : ∀ i ∈ Finset.range N, μ.real (E2 i)
      ≤ 2 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
    intro i hi
    have := cond_one X hind hX hlaw H2 hH2 hF0 hH2B i ((Finset.range N).erase i)
      (Finset.notMem_erase i _) hε
    rwa [hcard i hi, hexp] at this
  have hsub : {ω | ∃ i < N, 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk0 ξ f X N ω i - Pinf (gk ξ) f (X i ω)|}
      ⊆ ⋃ i ∈ Finset.range N, (E1 i ∪ E2 i) := by
    intro ω hω
    obtain ⟨i, hi, hlt⟩ := hω
    have hiN : i ∈ Finset.range N := Finset.mem_range.mpr hi
    simp only [Set.mem_iUnion]
    refine ⟨i, hiN, ?_⟩
    by_contra hnot
    simp only [Set.mem_union, E1, E2, Set.mem_setOf_eq, not_or, not_le] at hnot
    obtain ⟨h1, h2⟩ := hnot
    set x := X i ω
    set a := zonalOp (gk ξ) f x
    set b := ∫ z, Kx ξ x z ∂sigma
    have hb : b = (1/2) * sphZ ξ := degree_eq ξ x
    have hbpos : 0 < b := degree_pos ξ x
    have hbq : zonalOp (gk ξ) (fun _ => 1) x = b := by rw [zonalOp_one, hb]
    have hT : ∀ (g : ℕ → ℝ), ∑ j ∈ Finset.range N, g j
        = ∑ j ∈ (Finset.range N).erase i, g j + g i := fun g =>
      (Finset.sum_erase_add _ _ hiN).symm
    set AT := ∑ j ∈ (Finset.range N).erase i, Kx ξ x (X j ω) * f (X j ω)
    set BT := ∑ j ∈ (Finset.range N).erase i, Kx ξ x (X j ω)
    have hA : |AT - n * a| ≤ n * η := by
      have e : ∑ j ∈ (Finset.range N).erase i, (H1 x (X j ω) - ∫ z, H1 x z ∂sigma)
          = AT - n * a := by
        have ha : ∫ z, H1 x z ∂sigma = a := (zonal_eq ξ f x).symm
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard i hiN, ha]
      rw [← e]; exact h1.le
    have hB : |BT - n * b| ≤ n * η := by
      have e : ∑ j ∈ (Finset.range N).erase i, (H2 x (X j ω) - ∫ z, H2 x z ∂sigma)
          = BT - n * b := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard i hiN]
      rw [← e]; exact h2.le
    have hwalk : walk0 ξ f X N ω i = (AT + 0 * f x) / (BT + 0) :=
      calc walk0 ξ f X N ω i = AT / BT := rfl
        _ = (AT + 0 * f x) / (BT + 0) := by ring
    have hPinf : Pinf (gk ξ) f x = a / b := by unfold Pinf; rw [hbq]
    have hfin := ratio_det hbpos hnpos hF0 (abs_zonal_le ξ f hf hfF x) le_rfl
      zero_le_one (hfF x) hA hB (by rw [hb]; linarith)
    rw [hwalk, hPinf] at hlt
    have : 2 * (η * (1 + F) + 2 * F / n) / b = 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ := by
      rw [hb, hn]; field_simp; ring
    rw [this] at hfin
    exact absurd hfin (not_le.mpr hlt)
  calc _ ≤ μ.real (⋃ i ∈ Finset.range N, (E1 i ∪ E2 i)) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ Finset.range N, μ.real (E1 i ∪ E2 i) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range N, 4 * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        calc μ.real (E1 i ∪ E2 i) ≤ μ.real (E1 i) + μ.real (E2 i) := measureReal_union_le _ _
          _ ≤ _ := by linarith [hP1 i hi, hP2 i hi]
    _ = 4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring


end Walk0

section Pow

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The one-step error bound of the files. -/
noncomputable def errN (ξ F η : ℝ) (N : ℕ) : ℝ :=
  4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ

theorem errN_nonneg (ξ : ℝ) {F η : ℝ} (hF : 0 ≤ F) (hη : 0 ≤ η) {N : ℕ} (hN : 2 ≤ N) :
    0 ≤ errN ξ F η N := by
  have : (2:ℝ) ≤ N := by exact_mod_cast hN
  have := sphZ_pos ξ
  unfold errN
  apply div_nonneg _ this.le
  have : (0:ℝ) ≤ (N:ℝ) - 1 := by linarith
  positivity

/-- Generic union step: if each `m < k` has a bad event of probability `≤ p` outside of which the
one-step bound holds, the telescope bound holds outside an event of probability `≤ k p`. -/
theorem pow_union (S : ℕ → Finset ℕ) (ξ : ℝ) (X : ℕ → Ω → S2) (N : ℕ)
    (hSN : ∀ i < N, S i ⊆ Finset.range N) (hSne : ∀ i < N, (S i).Nonempty)
    (f : S2 → ℝ) (k : ℕ) {δ p : ℝ} (hδ : 0 ≤ δ)
    (hP : ∀ m < k, μ.real {ω | ∃ i < N, δ <
      |wOp S ξ X ω (fun j => pinfPow ξ m f (X j ω)) i - Pinf (gk ξ) (pinfPow ξ m f) (X i ω)|} ≤ p) :
    μ.real {ω | ∃ i < N, k * δ <
      |(wOp S ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω)|} ≤ k * p := by
  set B : ℕ → Set Ω := fun m => {ω | ∃ i < N, δ <
      |wOp S ξ X ω (fun j => pinfPow ξ m f (X j ω)) i - Pinf (gk ξ) (pinfPow ξ m f) (X i ω)|}
  have hsub : {ω | ∃ i < N, k * δ <
      |(wOp S ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω)|}
      ⊆ ⋃ m ∈ Finset.range k, B m := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists, Finset.mem_range] at hnot
    have hstep : ∀ m < k, ∀ i < N,
        |wOp S ξ X ω (fun j => pinfPow ξ m f (X j ω)) i - pinfPow ξ (m + 1) f (X i ω)| ≤ δ := by
      intro m hm i hi
      by_contra hlt
      rw [pinfPow_succ] at hlt
      exact hnot m hm ⟨i, hi, not_le.mp hlt⟩
    obtain ⟨i, hi, hlt⟩ := hω
    exact absurd (pow_det S ξ X ω N hSN hSne f k hδ hstep i hi) (not_le.mpr hlt)
  calc _ ≤ μ.real (⋃ m ∈ Finset.range k, B m) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ m ∈ Finset.range k, μ.real (B m) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Finset.range k, p := Finset.sum_le_sum fun m hm => hP m (Finset.mem_range.mp hm)
    _ = k * p := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem loopS_props (N : ℕ) (hN : 2 ≤ N) :
    (∀ i < N, loopS N i ⊆ Finset.range N) ∧ ∀ i < N, (loopS N i).Nonempty :=
  ⟨fun _ _ => subset_rfl, fun _ _ => ⟨0, Finset.mem_range.mpr (by omega)⟩⟩

theorem noloopS_props (N : ℕ) (hN : 2 ≤ N) :
    (∀ i < N, noloopS N i ⊆ Finset.range N) ∧ ∀ i < N, (noloopS N i).Nonempty := by
  refine ⟨fun _ _ => Finset.erase_subset _ _, fun i hi => ?_⟩
  by_cases h : i = 0
  · exact ⟨1, Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩⟩
  · exact ⟨0, Finset.mem_erase.mpr ⟨fun e => h e.symm, Finset.mem_range.mpr (by omega)⟩⟩

/-- **Powers of the sample walk WITH self-loop.** For continuous `f`, `|f| ≤ F`, `1 ≤ F`, `N ≥ 2`,
`0 < η ≤ sphZ ξ / 4` and every `k`: outside an event of probability at most
`k · 4 N exp(-(N-1) η²/(2F²))`, for ALL `i < N`,
`|(P_N^k f)(X_i) - (P_∞^k f)(X_i)| ≤ k · errN`, `errN = 4 (η (1+F) + 2F/(N-1)) / sphZ ξ`;
`P_N^k f` is the `k`-fold iterated application of the walk to the vector `(f(X_j))_j`. -/
theorem pow_step (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f)
    {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F) {N : ℕ} (hN : 2 ≤ N)
    {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) (k : ℕ) :
    μ.real {ω | ∃ i < N, k * errN ξ F η N <
      |(wOp (loopS N) ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω)|}
      ≤ k * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2))) := by
  obtain ⟨h1, h2⟩ := loopS_props N hN
  refine pow_union (loopS N) ξ X N h1 h2 f k (errN_nonneg ξ (by linarith) hη.le hN) fun m _ => ?_
  obtain ⟨hc, hb⟩ := pinfPow_props ξ f hf hfF m
  exact walk_one_step X hind hX hlaw ξ _ hc hF1 hb hN hη hηb

/-- The same WITHOUT self-loop. -/
theorem pow_step0 (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f)
    {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F) {N : ℕ} (hN : 2 ≤ N)
    {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) (k : ℕ) :
    μ.real {ω | ∃ i < N, k * errN ξ F η N <
      |(wOp (noloopS N) ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω)|}
      ≤ k * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2))) := by
  obtain ⟨h1, h2⟩ := noloopS_props N hN
  refine pow_union (noloopS N) ξ X N h1 h2 f k (errN_nonneg ξ (by linarith) hη.le hN) fun m _ => ?_
  obtain ⟨hc, hb⟩ := pinfPow_props ξ f hf hfF m
  exact walk0_one_step X hind hX hlaw ξ _ hc hF1 hb hN hη hηb

/-- Deterministic smallness: for `ε > 0` and `k`, there are `η ∈ (0, sphZ ξ/4]` from the list
`ηk` and `M` with `k · errN ≤ ε` for all `N ≥ M + 2`. -/
theorem small_eventually (ξ : ℝ) {F : ℝ} (hF1 : 1 ≤ F) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ M : ℕ, ∀ N : ℕ, M + 2 ≤ N →
      k * errN ξ F (min (sphZ ξ / 4) (1 / ((q:ℝ) + 1))) N ≤ ε := by
  set Z := sphZ ξ with hZd
  have hZ : 0 < Z := sphZ_pos ξ
  set ε' : ℝ := ε / ((k:ℝ) + 1)
  have hε' : 0 < ε' := by positivity
  obtain ⟨q, hq⟩ := exists_nat_gt (8 * (1 + F) / (Z * ε'))
  obtain ⟨M, hM⟩ := exists_nat_gt (16 * F / (Z * ε') + 1)
  refine ⟨q, M, fun N hNM => ?_⟩
  set η := min (Z / 4) (1 / ((q:ℝ) + 1))
  have hq1 : (0:ℝ) < (q:ℝ) + 1 := by positivity
  have hη1 : η * ((q:ℝ) + 1) ≤ 1 := by
    have : η ≤ 1 / ((q:ℝ) + 1) := min_le_right _ _
    rwa [le_div_iff₀ hq1] at this
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  have hkZ : 8 * (1 + F) < ((q:ℝ) + 1) * (Z * ε') := by
    rw [div_lt_iff₀ (by positivity)] at hq; nlinarith
  have hNr : (M:ℝ) + 2 ≤ N := by exact_mod_cast hNM
  have hMZ : 16 * F < ((M:ℝ) - 1 + 1) * (Z * ε') := by
    have : 16 * F / (Z * ε') < M := by linarith
    rw [div_lt_iff₀ (by positivity)] at this; nlinarith
  have hN1 : (0:ℝ) < (N:ℝ) - 1 := by linarith
  have e : errN ξ F η N = 4 * η * (1 + F) / Z + 8 * F / (((N:ℝ) - 1) * Z) := by
    unfold errN; rw [← hZd]; field_simp; ring
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
  have hE : errN ξ F η N ≤ ε' := by rw [e]; linarith
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  calc (k:ℝ) * errN ξ F η N ≤ k * ε' := mul_le_mul_of_nonneg_left hE hk0
    _ ≤ ε := by
        simp only [ε']
        rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith

/-- Generic almost-sure step for a family of bad-event bounds `k · 4 N e^{-(N-1)η²/(2F²)}`. -/
theorem ae_of_bounds (ξ : ℝ) {F : ℝ} (hF1 : 1 ≤ F) (k : ℕ) (Err : ℕ → Ω → ℕ → ℝ)
    (hP : ∀ η : ℝ, 0 < η → η ≤ sphZ ξ / 4 → ∀ N : ℕ, 2 ≤ N →
      μ.real {ω | ∃ i < N, k * errN ξ F η N < |Err N ω i|}
        ≤ k * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * F ^ 2)))) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N, |Err N ω i| ≤ ε := by
  have hF : 0 < F := by linarith
  set Z := sphZ ξ
  have hZ : 0 < Z := sphZ_pos ξ
  set ηq : ℕ → ℝ := fun q => min (Z / 4) (1 / ((q:ℝ) + 1))
  have hηq : ∀ q, 0 < ηq q := fun q => lt_min (by positivity) (by positivity)
  have hone : ∀ q, ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ∀ i < N, |Err N ω i| ≤ k * errN ξ F (ηq q) N := by
    intro q
    set c : ℝ := ηq q ^ 2 / (2 * F ^ 2)
    have hc : 0 < c := by have := hηq q; positivity
    have h := bc_lin (μ := μ) (fun N => {ω | ∃ i < N, k * errN ξ F (ηq q) N < |Err N ω i|})
      (C := k * 4 * Real.exp c) (by positivity) hc (fun N hN => by
        refine (hP (ηq q) (hηq q) (min_le_left _ _) N hN).trans (le_of_eq ?_)
        have : Real.exp (-((N - 1) * ηq q ^ 2) / (2 * F ^ 2))
            = Real.exp c * Real.exp (-(c * N)) := by
          rw [← Real.exp_add]; congr 1; simp only [c]; field_simp; ring
        rw [this]; ring)
    filter_upwards [h] with ω hω
    filter_upwards [hω] with N hN
    intro i hi
    by_contra hlt
    exact hN ⟨i, hi, not_le.mp hlt⟩
  have hall := ae_all_iff.mpr hone
  filter_upwards [hall] with ω hω
  intro ε hε
  obtain ⟨q, M, hqM⟩ := small_eventually ξ hF1 k hε
  filter_upwards [hω q, eventually_ge_atTop (M + 2)] with N hN hNM
  intro i hi
  exact (hN i hi).trans (hqM N hNM)

/-- Almost surely (with self-loop, fixed `k`): for every `ε > 0`, eventually in `N`,
`|(P_N^k f)(X_i) - (P_∞^k f)(X_i)| ≤ ε` for all `i < N`. -/
theorem pow_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f)
    {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F) (k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |(wOp (loopS N) ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω)| ≤ ε :=
  ae_of_bounds ξ hF1 k
    (fun N ω i => (wOp (loopS N) ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω))
    (fun _η hη hηb _N hN => pow_step X hind hX hlaw ξ f hf hF1 hfF hN hη hηb k)

/-- The same WITHOUT self-loop. -/
theorem pow_ae0 (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (f : S2 → ℝ) (hf : Continuous f)
    {F : ℝ} (hF1 : 1 ≤ F) (hfF : ∀ y, |f y| ≤ F) (k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |(wOp (noloopS N) ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω)| ≤ ε :=
  ae_of_bounds ξ hF1 k
    (fun N ω i => (wOp (noloopS N) ξ X ω)^[k] (fun j => f (X j ω)) i - pinfPow ξ k f (X i ω))
    (fun _η hη hηb _N hN => pow_step0 X hind hX hlaw ξ f hf hF1 hfF hN hη hηb k)

/-! ## Spherical harmonics -/

theorem Pinf_smul (ξ s : ℝ) (f : S2 → ℝ) (x : S2) :
    Pinf (gk ξ) (fun y => s * f y) x = s * Pinf (gk ξ) f x := by
  rw [Pinf_eq, Pinf_eq]
  have : ∫ z, Kx ξ x z * (s * f z) ∂sigma = s * ∫ z, Kx ξ x z * f z ∂sigma := by
    rw [← integral_const_mul]; congr 1; funext z; ring
  rw [this, mul_div_assoc]

/-- `P_∞^k (Re (a·y)^l) = s_l^k Re (a·y)^l`. -/
theorem pinfPow_harmonic (ξ : ℝ) (p q : E3) (hpq : Isotropic p q) (l k : ℕ) :
    pinfPow ξ k (fun y => (cdot p q (y : E3) ^ l).re)
      = fun y : S2 => sphS ξ l ^ k * (cdot p q (y : E3) ^ l).re := by
  induction k with
  | zero => funext y; simp [pinfPow]
  | succ k ih =>
    rw [pinfPow_succ, ih]
    funext x
    rw [Pinf_smul, Pinf_harmonic ξ p q hpq l x, pow_succ]; ring

/-- **The sampled spherical harmonic under `k` steps (WITH self-loop).** -/
theorem pow_harmonic (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (p q : E3) (hpq : Isotropic p q) (l : ℕ)
    {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) (k : ℕ) :
    μ.real {ω | ∃ i < N, k * errN ξ (harmF p q l) η N <
      |(wOp (loopS N) ξ X ω)^[k] (fun j => (cdot p q (X j ω : E3) ^ l).re) i
        - sphS ξ l ^ k * (cdot p q (X i ω : E3) ^ l).re|}
      ≤ k * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * harmF p q l ^ 2))) := by
  have h := pow_step X hind hX hlaw ξ _ (harm_cont p q l) (one_le_harmF p q l)
    (harm_bound p q l) hN hη hηb k
  rw [pinfPow_harmonic ξ p q hpq l k] at h
  exact h

/-- The same WITHOUT self-loop. -/
theorem pow_harmonic0 (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (p q : E3) (hpq : Isotropic p q) (l : ℕ)
    {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη : 0 < η) (hηb : η ≤ sphZ ξ / 4) (k : ℕ) :
    μ.real {ω | ∃ i < N, k * errN ξ (harmF p q l) η N <
      |(wOp (noloopS N) ξ X ω)^[k] (fun j => (cdot p q (X j ω : E3) ^ l).re) i
        - sphS ξ l ^ k * (cdot p q (X i ω : E3) ^ l).re|}
      ≤ k * (4 * N * Real.exp (-((N - 1) * η ^ 2) / (2 * harmF p q l ^ 2))) := by
  have h := pow_step0 X hind hX hlaw ξ _ (harm_cont p q l) (one_le_harmF p q l)
    (harm_bound p q l) hN hη hηb k
  rw [pinfPow_harmonic ξ p q hpq l k] at h
  exact h

/-- **Almost surely (WITH self-loop, fixed `k`)**: for every `ε > 0`, eventually in `N`,
`|(P_N^k f)(X_i) - s_l^k f(X_i)| ≤ ε` for all `i < N`, `f = Re (a·y)^l`. -/
theorem pow_harmonic_ae (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (p q : E3) (hpq : Isotropic p q) (l k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |(wOp (loopS N) ξ X ω)^[k] (fun j => (cdot p q (X j ω : E3) ^ l).re) i
        - sphS ξ l ^ k * (cdot p q (X i ω : E3) ^ l).re| ≤ ε := by
  have h := pow_ae X hind hX hlaw ξ _ (harm_cont p q l) (one_le_harmF p q l) (harm_bound p q l) k
  rw [pinfPow_harmonic ξ p q hpq l k] at h
  exact h

/-- The same WITHOUT self-loop. -/
theorem pow_harmonic_ae0 (X : ℕ → Ω → S2) (hind : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = sigma) (ξ : ℝ) (p q : E3) (hpq : Isotropic p q) (l k : ℕ) :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∀ᶠ N in atTop, ∀ i < N,
      |(wOp (noloopS N) ξ X ω)^[k] (fun j => (cdot p q (X j ω : E3) ^ l).re) i
        - sphS ξ l ^ k * (cdot p q (X i ω : E3) ^ l).re| ≤ ε := by
  have h := pow_ae0 X hind hX hlaw ξ _ (harm_cont p q l) (one_le_harmF p q l)
    (harm_bound p q l) k
  rw [pinfPow_harmonic ξ p q hpq l k] at h
  exact h

end Pow

end CTG.FunkHecke.Powers
