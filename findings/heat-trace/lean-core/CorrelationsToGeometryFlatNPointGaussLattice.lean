/-
Forty-seventh file: sharper additional terms for the flat N-point statement with the full Gaussian profile, and the
lattice-sum kernel on the sample side.  Namespace `CTG.FlatNPointGaussLattice`; imports the forty-sixth file
(compiled module); check with `./check_flat_npoint_gauss_lattice.sh`.  Written by a sub-task of an AI session on
27 November 2026; read by nobody.  Probabilities are bounds for the outer measure (measurability not shown).
Stage A:
* `sampW_quot_perturb_avg`: as `sampW_quot_perturb`, but the kernel bound `A` is replaced by the sample
  average of the kernel itself (the term `A ε/c²` becomes `Q ε/c²`).
* `norm_event2`: the Bernstein event of `CTG.FlatNPointWindow.norm_event`, now two-sided: on its complement
  `P₀ ξⁿ/2 ≤ sampAvg ≤ (3/2) P₁ ξⁿ` at every sample point (`P₀ = K₀|det S|/a₁ⁿ`, `P₁ = K₀|det S|/a₀ⁿ`).
* `flat_npoint_kernel`: the N-point statement for ANY kernel family `K_τ` squeezed between the cut-off
  kernel and the cut-off kernel plus `ε`; additional terms `2(E_s' + E_p)/|η|` resp. `2E_s'/|η|` with
  `E_s' = errS2 m₂ ξ c Q ε B`, `Q = (3/2) P₁ ξⁿ + ε`.
* `flat_npoint_gauss_full2`: the instance for the full Gaussian, nearest image (`ε = exp(−R²/2)`).
Stage B:
* `latK`: the lattice-sum kernel `Σ_{m ∈ ℤⁿ} exp(−‖S⁻¹(fr(z−x)+m)‖² a²/(2ξ²))`; `latK_summable`,
  `nearest_le_latK`, `latK_le_nearest` (`latK ≤ nearest + latTail`, `latTail = e^{−c/2}(1+√(2π/c))ⁿ`,
  `c = a₀²/(8(‖S‖+1)²ξ²)`, for every `a ≥ a₀`).
* `flat_npoint_lattice`: the N-point statement for the lattice-sum kernel on the sample side
  (`ε = exp(−R²/2) + latTail`), population operator `Lmet gauss` (integral over `ℝⁿ`).
HAND ESTIMATE (not a statement): `c = K₀|det S|ξⁿ/(2a₁ⁿ)` and, for `ε ≤ ξⁿ`, `Q ≤ C ξⁿ`, so `Q/c = O(1)`,
`ε/c + Qε/c² = O(ε ξ^{−n})` and `E_s' = O(B ε ξ^{−n−2})` (before: `ε ξ^{−3n−2}`).  For the lattice kernel
`ε = e^{−R²/2} + O(e^{−a₀²/(16(‖S‖+1)²ξ²)})` (the factor `(1+√(2π/c))ⁿ` is `≤ 2ⁿ` once `c ≥ 2π`).
The lemmas `CTG.Reals.gauss_summable`, `CTG.Reals.gauss_tail_sum_le` of the second Lean file are reached
through the existing import chain (no new import).
No sorry, no axiom, no native_decide.
-/
import CorrelationsToGeometryFlatNPointGaussFull

open MeasureTheory ProbabilityTheory Set
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss CTG.FlatNPointGaussFull

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointGaussLattice

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Stage A (1): the sample quotient with the kernel average in place of the kernel bound -/

theorem avgN_affine (N : ℕ) (hN : 0 < N) (a b : ℝ) (u : ℕ → ℝ) :
    avgN N (fun j => a + b * u j) = a + b * avgN N u := by
  unfold avgN
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem sampAvg_le_add {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K K' : E → E → ℝ) {ε : ℝ}
    (h2 : ∀ x z, K' x z ≤ K x z + ε) (j : ℕ) (ω : Ω) :
    sampAvg X N K' j ω ≤ sampAvg X N K j ω + ε := by
  have e1 : sampAvg X N K' j ω = avgN N (fun k => K' (X j ω) (X k ω)) := rfl
  have e2 : sampAvg X N K j ω = avgN N (fun k => K (X j ω) (X k ω)) := rfl
  rw [e1, e2, ← avgN_const N hN ε, ← sub_le_iff_le_add', avgN_sub]
  exact avgN_mono N _ _ fun k _ => by linarith [h2 (X j ω) (X k ω)]

theorem sampAvg_mono {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (K K' : E → E → ℝ)
    (h1 : ∀ x z, K x z ≤ K' x z) (j : ℕ) (ω : Ω) :
    sampAvg X N K j ω ≤ sampAvg X N K' j ω := by
  simp only [sampAvg]
  gcongr with k hk; exact h1 _ _

/-- **Sample side, averaged form.**  Kernels `K ≤ K' ≤ K + ε`, `0 ≤ K`; sample normalisations of `K`
at least `c`, of `K'` at most `Q`; `|g| ≤ G`.  Then the quotients differ by at most
`2 G (ε/c + Q ε/c²) Q/c` (no pointwise bound on the kernel is used). -/
theorem sampW_quot_perturb_avg {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (K K' g : E → E → ℝ)
    (i : ℕ) (hi : i < N) (ω : Ω) {Q c ε G : ℝ}
    (hK0 : ∀ x z, 0 ≤ K x z) (h1 : ∀ x z, K x z ≤ K' x z)
    (h2 : ∀ x z, K' x z ≤ K x z + ε) (hc : 0 < c)
    (hq : ∀ j < N, c ≤ sampAvg X N K j ω) (hQ : ∀ j < N, sampAvg X N K' j ω ≤ Q)
    (hg : ∀ x z, |g x z| ≤ G) :
    |sampW X N K' g i ω / sampW X N K' (fun _ _ => 1) i ω
        - sampW X N K g i ω / sampW X N K (fun _ _ => 1) i ω|
      ≤ 2 * G * (ε / c + Q * ε / c ^ 2) / (c / Q) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i) hi
  set q := fun j => sampAvg X N K j ω with hqdef
  set q' := fun j => sampAvg X N K' j ω with hq'def
  have hε : 0 ≤ ε := by have := h1 (X 0 ω) (X 0 ω); have := h2 (X 0 ω) (X 0 ω); linarith
  have hG : 0 ≤ G := le_trans (abs_nonneg _) (hg (X 0 ω) (X 0 ω))
  have hqq' : ∀ j, q j ≤ q' j := fun j => sampAvg_mono X N K K' h1 j ω
  have hq'q : ∀ j, q' j ≤ q j + ε := fun j => sampAvg_le_add X N hN K K' h2 j ω
  have hQ0 : 0 < Q := lt_of_lt_of_le hc ((hq 0 hN).trans ((hqq' 0).trans (hQ 0 hN)))
  have hm : 0 < c / Q := div_pos hc hQ0
  have eW : ∀ (L : E → E → ℝ) (u : E → E → ℝ),
      sampW X N L u i ω = avgN N (fun j => L (X i ω) (X j ω) * u (X i ω) (X j ω)
        * (1 / sampAvg X N L j ω)) := fun _ _ => rfl
  have eA : sampAvg X N K i ω = avgN N (fun j => K (X i ω) (X j ω)) := rfl
  have hqi : q i ≤ Q := (hqq' i).trans (hQ i hi)
  -- lower bounds of the denominators
  have hb : c / Q ≤ sampW X N K (fun _ _ => 1) i ω := by
    rw [eW]
    have : avgN N (fun j => K (X i ω) (X j ω) * (1 / Q))
        ≤ avgN N (fun j => K (X i ω) (X j ω) * (fun _ _ => (1:ℝ)) (X i ω) (X j ω)
          * (1 / sampAvg X N K j ω)) := by
      refine avgN_mono N _ _ fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have hqj : 0 < q j := lt_of_lt_of_le hc (hq j hj')
      simp only [mul_one]
      gcongr
      · exact hK0 _ _
      · exact (hqq' j).trans (hQ j hj')
    refine le_trans ?_ this
    have e : avgN N (fun j => K (X i ω) (X j ω) * (1 / Q)) = sampAvg X N K i ω * (1 / Q) := by
      rw [eA]; unfold avgN; simp only [← Finset.sum_mul]; ring
    rw [e, div_eq_mul_one_div c Q]
    gcongr
    exact hq i hi
  have hb' : c / Q ≤ sampW X N K' (fun _ _ => 1) i ω := by
    rw [eW]
    have : avgN N (fun j => K (X i ω) (X j ω) * (1 / Q))
        ≤ avgN N (fun j => K' (X i ω) (X j ω) * (fun _ _ => (1:ℝ)) (X i ω) (X j ω)
          * (1 / sampAvg X N K' j ω)) := by
      refine avgN_mono N _ _ fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have hqj : 0 < q' j := lt_of_lt_of_le hc ((hq j hj').trans (hqq' j))
      simp only [mul_one]
      gcongr
      · exact le_trans (hK0 _ _) (h1 _ _)
      · exact h1 _ _
      · exact hQ j hj'
    refine le_trans ?_ this
    have e : avgN N (fun j => K (X i ω) (X j ω) * (1 / Q)) = sampAvg X N K i ω * (1 / Q) := by
      rw [eA]; unfold avgN; simp only [← Finset.sum_mul]; ring
    rw [e, div_eq_mul_one_div c Q]
    gcongr
    exact hq i hi
  have ha : |sampW X N K g i ω| ≤ G * sampW X N K (fun _ _ => 1) i ω := by
    rw [eW, eW]
    have e : G * avgN N (fun j => K (X i ω) (X j ω) * (fun _ _ => (1:ℝ)) (X i ω) (X j ω)
          * (1 / sampAvg X N K j ω))
        = avgN N (fun j => G * (K (X i ω) (X j ω) * (1 / sampAvg X N K j ω))) := by
      unfold avgN; rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    refine avgN_abs_le N _ _ fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have hqj : 0 < q j := lt_of_lt_of_le hc (hq j hj')
    have hK := hK0 (X i ω) (X j ω)
    have hw : 0 ≤ K (X i ω) (X j ω) * (1 / sampAvg X N K j ω) := mul_nonneg hK (by positivity)
    rw [show K (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N K j ω)
        = g (X i ω) (X j ω) * (K (X i ω) (X j ω) * (1 / sampAvg X N K j ω)) by ring,
      abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right (hg _ _) hw
  set δ := ε / c + Q * ε / c ^ 2 with hδ
  have hterm : ∀ j < N, |K' (X i ω) (X j ω) * (1 / q' j) - K (X i ω) (X j ω) * (1 / q j)|
      ≤ ε / c + ε / c ^ 2 * K (X i ω) (X j ω) := fun j hj => by
    have := term_perturb _ _ _ _ (K (X i ω) (X j ω)) c ε (hK0 _ _) le_rfl (h1 _ _) (h2 _ _) hc
      (hq j hj) (hqq' j) (hq'q j)
    calc _ ≤ _ := this
      _ = ε / c + ε / c ^ 2 * K (X i ω) (X j ω) := by ring
  have havg : ε / c + ε / c ^ 2 * q i ≤ δ := by
    rw [hδ]
    have : ε / c ^ 2 * q i ≤ ε / c ^ 2 * Q := mul_le_mul_of_nonneg_left hqi (by positivity)
    have e : Q * ε / c ^ 2 = ε / c ^ 2 * Q := by ring
    linarith
  have hda : |sampW X N K' g i ω - sampW X N K g i ω| ≤ G * δ := by
    rw [eW, eW, avgN_sub]
    refine (avgN_abs_le N _ (fun j => G * (ε / c) + (G * (ε / c ^ 2)) * K (X i ω) (X j ω))
      fun j hj => ?_).trans ?_
    · have hj' := Finset.mem_range.1 hj
      rw [show K' (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N K' j ω)
            - K (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N K j ω)
          = g (X i ω) (X j ω) * (K' (X i ω) (X j ω) * (1 / q' j) - K (X i ω) (X j ω) * (1 / q j))
          by simp only [hqdef, hq'def]; ring, abs_mul]
      calc |g (X i ω) (X j ω)| * |K' (X i ω) (X j ω) * (1 / q' j) - K (X i ω) (X j ω) * (1 / q j)|
          ≤ G * (ε / c + ε / c ^ 2 * K (X i ω) (X j ω)) :=
            mul_le_mul (hg _ _) (hterm j hj') (abs_nonneg _) hG
        _ = G * (ε / c) + G * (ε / c ^ 2) * K (X i ω) (X j ω) := by ring
    · rw [avgN_affine N hN, ← eA]
      calc G * (ε / c) + G * (ε / c ^ 2) * sampAvg X N K i ω
          = G * (ε / c + ε / c ^ 2 * q i) := by simp only [hqdef]; ring
        _ ≤ G * δ := mul_le_mul_of_nonneg_left havg hG
  have hdb : |sampW X N K' (fun _ _ => 1) i ω - sampW X N K (fun _ _ => 1) i ω| ≤ δ := by
    rw [eW, eW, avgN_sub]
    refine (avgN_abs_le N _ (fun j => ε / c + (ε / c ^ 2) * K (X i ω) (X j ω))
      fun j hj => ?_).trans ?_
    · have hj' := Finset.mem_range.1 hj
      rw [show K' (X i ω) (X j ω) * (fun _ _ => (1:ℝ)) (X i ω) (X j ω) * (1 / sampAvg X N K' j ω)
            - K (X i ω) (X j ω) * (fun _ _ => (1:ℝ)) (X i ω) (X j ω) * (1 / sampAvg X N K j ω)
          = K' (X i ω) (X j ω) * (1 / q' j) - K (X i ω) (X j ω) * (1 / q j)
          by simp only [hqdef, hq'def]; ring]
      exact hterm j hj'
    · rw [avgN_affine N hN, ← eA]
      exact havg
  exact quot_perturb _ _ _ _ G δ (c / Q) hm hb hb' ha hda hdb

/-! ### Stage A (2): the two-sided normalisation event -/

set_option maxHeartbeats 1600000 in
/-- The Bernstein event of `CTG.FlatNPointWindow.norm_event`, two-sided: outside an event of
probability `≤ N·2e^{−L}`, at every sample point `P₀ ξⁿ/2 ≤ sampAvg ≤ (3/2) P₁ ξⁿ`. -/
theorem norm_event2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {h : ℝ → ℝ} {K₀ m₂ μ₃ μ₄ A R Lh : ℝ} (hk : RadK n h K₀ m₂ μ₃ μ₄)
    (hP : Prof h A R) (hR : 0 ≤ R)
    {f : E → ℝ} (hfc : Continuous f) {Lip : ℝ} (hper : Per f) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (a : ℝ → ℝ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (g : ℝ) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * rLam A K₀ Lh R La a₀ a₁ Lip S ^ 14 * L ≤ N * ξ ^ n) :
    μ.real {ω | ∃ j < N, sampAvg X N (perK (kap h S (ξ / a g))) j ω
        < K₀ * dS S / a₁ ^ n * ξ ^ n / 2
        ∨ 3 / 2 * (K₀ * dS S / a₀ ^ n * ξ ^ n) < sampAvg X N (perK (kap h S (ξ / a g))) j ω}
      ≤ N * (2 * Real.exp (-L)) := by
  obtain ⟨l1, lA, lBI, lP1, lMI, lP0, lALρ, lBILρ, lP1Lρ, lMILρ⟩ :=
    rLam_bounds A K₀ Lh R La a₀ a₁ Lip S
  set Λ := rLam A K₀ Lh R La a₀ a₁ Lip S with hΛ
  set x := ξ ^ n with hx
  set δ := Real.sqrt (L / (N * x)) with hδdef
  set P1 := K₀ * dS S / a₀ ^ n with hP1
  set P0 := K₀ * dS S / a₁ ^ n with hP0
  set pg := pmass h S (a g) ξ with hpg
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hx0 : 0 < x := pow_pos hξ n
  have hx1 : x ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hd := dS_pos S
  have hK := hk.kern.mass_pos
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hP10 : 0 < P1 := by positivity
  have hP00 : 0 < P0 := by positivity
  have hA0 : 0 ≤ A := le_trans (hP.nonneg 0) (hP.le 0)
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨pg0, pg1⟩ := pmass_bounds hk S ha₀ (ha g) (ha₁ g) hξ
  have hpg0 : P0 * x ≤ pg := pg0
  have hpg1 : pg ≤ P1 * x := pg1
  have hc : 0 < pg := lt_of_lt_of_le (mul_pos hP00 hx0) pg0
  have hci : pg⁻¹ ≤ Λ * x⁻¹ := by
    calc pg⁻¹ ≤ (P0 * x)⁻¹ := inv_anti₀ (by positivity) pg0
      _ = P0⁻¹ * x⁻¹ := mul_inv _ _
      _ ≤ Λ * x⁻¹ := mul_le_mul_of_nonneg_right lP0 (by positivity)
  have hNx : (N : ℝ) * x ≠ 0 := (mul_pos hN' hx0).ne'
  have hδ : δ ^ 2 * (N * x) = L := by
    rw [hδdef, Real.sq_sqrt (div_nonneg (by linarith) (mul_pos hN' hx0).le)]; field_simp
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hPp : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * x) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ 1 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((1 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hPp] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ l1
    nlinarith
  have C : Ctx N Λ x x⁻¹ δ L :=
    { hN := hN0, hΛ := l1, hx := hx0, hx1 := hx1, hxy := mul_inv_cancel₀ hx0.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL1 }
  have hvK : A * pg ≤ Λ ^ 2 * x := by
    calc A * pg ≤ Λ * (P1 * x) := mul_le_mul lA pg1 hc.le hΛ0.le
      _ ≤ Λ * (Λ * x) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right lP1 hx0.le) hΛ0.le
      _ = Λ ^ 2 * x := by ring
  have hM' : pg ≤ Λ * x := pg1.trans (mul_le_mul_of_nonneg_right lP1 hx0.le)
  have hcD1 : (1:ℝ)⁻¹ ≤ Λ ^ 2 := by rw [inv_one]; exact one_le_pow₀ l1
  have hsmall := (C.small'_le hA0 lA (mul_nonneg hA0 hc.le) hvK hc.le hM' hc hci one_pos hcD1
    hsm).1
  have hdev : dev N A (A * pg) L ≤ pg / 2 := by
    rw [div_le_iff₀ hc] at hsmall; linarith
  have hρg := scale_le (S := S) hξ ha₀ (ha g) hR (le_refl (‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R)))
  have hsg := kap_supp hP S (div_pos hξ (hpos g)) hρg
  have hρ0 : 0 ≤ ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (div_pos hξ ha₀).le hR)
  have hAb : ∀ w, |kap h S (ξ / a g) w| ≤ A := fun w =>
    (abs_of_nonneg (hP.nonneg (‖S.symm w‖ / (ξ / a g)))).trans_le (hP.le _)
  have habs : ∫ w, |kap h S (ξ / a g) w| = ∫ w, kap h S (ξ / a g) w :=
    integral_congr_ae (ae_of_all _ fun w =>
      abs_of_nonneg (hP.nonneg (‖S.symm w‖ / (ξ / a g))))
  have hMg : ∫ w, |kap h S (ξ / a g) w| ≤ pg := habs.le
  obtain ⟨GK, -, -, -⟩ := good_per hfc hLip0 hLip hper (kap_measurable hP.meas S (ξ / a g))
    hρ0 hρh hAb hsg hMg
  have Hp := GK.prob X h_indep hX hlaw N hN0 (by linarith : 0 < L)
  refine le_trans (measureReal_mono ?_) Hp
  intro ω hω
  obtain ⟨j, hj, hlt⟩ := hω
  refine ⟨j, hj, ?_⟩
  have hpop : popAvg mT (perK (kap h S (ξ / a g))) (X j ω) = pg := popAvg_perK _ hρh hsg _
  rw [hpop]
  rcases hlt with hlt | hlt
  · have h5 : sampAvg X N (perK (kap h S (ξ / a g))) j ω < pg / 2 :=
      lt_of_lt_of_le hlt (by linarith)
    calc dev N A (A * pg) L ≤ pg / 2 := hdev
      _ < pg - sampAvg X N (perK (kap h S (ξ / a g))) j ω := by linarith
      _ ≤ |pg - sampAvg X N (perK (kap h S (ξ / a g))) j ω| := le_abs_self _
      _ = |sampAvg X N (perK (kap h S (ξ / a g))) j ω - pg| := abs_sub_comm _ _
  · calc dev N A (A * pg) L ≤ pg / 2 := hdev
      _ < sampAvg X N (perK (kap h S (ξ / a g))) j ω - pg := by linarith
      _ ≤ |sampAvg X N (perK (kap h S (ξ / a g))) j ω - pg| := le_abs_self _

/-! ### Stage A (3): the N-point statement for a squeezed kernel family -/

/-- The normalised sample operator of an arbitrary kernel `K` (as `LN`, which is the case
`K = perK (kap h S (ξ/a))`). -/
def LNK {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (K : E → E → ℝ) (m₂ ξ : ℝ) (f : E → ℝ) (i : ℕ)
    (ω : Ω) : ℝ :=
  -(2 / (m₂ * ξ ^ 2)) * (sampW X N K (gd f) i ω / sampW X N K (fun _ _ => 1) i ω)

theorem LN_eq_LNK {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (h : ℝ → ℝ) (m₂ : ℝ) (S : E ≃L[ℝ] E)
    (a ξ : ℝ) (f : E → ℝ) (i : ℕ) (ω : Ω) :
    LN X N h m₂ S a ξ f i ω = LNK X N (perK (kap h S (ξ / a))) m₂ ξ f i ω := rfl

/-- The new additional sample error `E_s' = (2/(m₂ξ²))·2·(2B)(ε/c + Qε/c²)·Q/c`. -/
def errS2 (m₂ ξ c Q ε B : ℝ) : ℝ := 2 / (m₂ * ξ ^ 2) * (2 * (2 * B) * (ε / c + Q * ε / c ^ 2) / (c / Q))

theorem LNK_sub {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (i : ℕ) (hi : i < N) (ω : Ω)
    {R : ℝ} {m₂ : ℝ} (hm₂ : 0 < m₂) (S : E ≃L[ℝ] E) {a ξ c Q₀ ε B : ℝ} (hξ : 0 < ξ) (hc : 0 < c)
    {f : E → ℝ} (hB : ∀ y, |f y| ≤ B) (K : E → E → ℝ)
    (hK1 : ∀ x z, perK (kap (gT R) S (ξ / a)) x z ≤ K x z)
    (hK2 : ∀ x z, K x z ≤ perK (kap (gT R) S (ξ / a)) x z + ε)
    (hq : ∀ j < N, c ≤ sampAvg X N (perK (kap (gT R) S (ξ / a))) j ω)
    (hQ : ∀ j < N, sampAvg X N (perK (kap (gT R) S (ξ / a))) j ω ≤ Q₀) :
    |LNK X N K m₂ ξ f i ω - LN X N (gT R) m₂ S a ξ f i ω| ≤ errS2 m₂ ξ c (Q₀ + ε) ε B := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i) hi
  have hQ' : ∀ j < N, sampAvg X N K j ω ≤ Q₀ + ε := fun j hj =>
    (sampAvg_le_add X N hN _ K hK2 j ω).trans (by linarith [hQ j hj])
  have hP := sampW_quot_perturb_avg X N (perK (kap (gT R) S (ξ / a))) K (gd f) i hi ω
    (Q := Q₀ + ε) (ε := ε) (G := 2 * B) (fun x z => gT_nonneg R _) hK1 hK2 hc hq hQ'
    (fun x z => by
      unfold gd
      calc |f z - f x| ≤ |f z| + |f x| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hB z, hB x])
  rw [LN_eq_LNK]
  unfold LNK errS2
  rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 / (m₂ * ξ ^ 2))]
  exact mul_le_mul_of_nonneg_left hP (by positivity)

set_option maxHeartbeats 3200000 in
/-- **N-point statement for a kernel family squeezed between the cut-off Gaussian kernel and the cut-off
kernel plus `ε`** (flat periodic case, rate form).  `K τ` is the kernel at time `τ`; HYPOTHESES on it:
`perK (kap (gT R) S (ξ/a τ)) ≤ K τ ≤ perK (kap (gT R) S (ξ/a τ)) + ε`.  Other hypotheses as in
`flat_npoint_gauss_full`.  Additional terms `2(E_s' + E_p)/|η|` in (i), `2 E_s'/|η|` in (ii), with
`E_s' = errS2 (gm₂ n R) ξ c Q ε B`, `c = K₀(R)|det S|ξⁿ/(2a₁ⁿ)`, `Q = (3/2)K₀(R)|det S|ξⁿ/a₀ⁿ + ε`.
Probability `≥ 1 − 34/N²`. -/
theorem flat_npoint_kernel (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n)
    (K : ℝ → E → E → ℝ) {ε : ℝ}
    (hK1 : ∀ τ x z, perK (kap (gT R) S (ξ / a τ)) x z ≤ K τ x z)
    (hK2 : ∀ τ x z, K τ x z ≤ perK (kap (gT R) S (ξ / a τ)) x z + ε) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LNK X N (K τb) (gm₂ n R) ξ f i ω - LNK X N (K τa) (gm₂ n R) ξ f i ω)
            / (τb - τa)
          - (Lmet gauss (gm₂ n R) S (a τb) ξ f (X i ω)
              - Lmet gauss (gm₂ n R) S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + 2 * (errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + ε) ε B
              + errP n (gm₂ n R) ξ R B) / |τb - τa|
      ∧ |(LNK X N (K τb) (gm₂ n R) ξ f i ω - LNK X N (K τa) (gm₂ n R) ξ f i ω)
            / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * gm₂ n R * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * gm₂ n R * gK₀ n R * a₀ ^ 5))
          + 2 * errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + ε) ε B / |τb - τa|)}
      ≤ 34 / (N : ℝ) ^ 2 := by
  set c := gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2 with hcdef
  set Q₀ := 3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) with hQ₀def
  set m₂ := gm₂ n R with hm₂def
  have hm₂ : 0 < m₂ := gm₂_pos hR hn
  have hfc : Continuous f := hf.continuous
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < c := by
    have := gK₀_pos (n := n) hR; have := dS_pos S; positivity
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hη : τb - τa ≠ 0 := sub_ne_zero.2 hne
  have hT := flat_npoint_gauss_truncated hn X h_indep hX hlaw N hN hR hf hM hM₄ hper hLip0 hLip
    S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hρh τa τb hne hNL
  have hNa := norm_event2 X h_indep hX hlaw N hN (radK_gT hR) (gT_prof hR.le)
    hR.le hfc hper hLip0 hLip S a ha₀ ha ha₁ hξ hξ1 hρh τa (FlatNPointRate.three_log_ge_one N hN) hNL
  have hNb := norm_event2 X h_indep hX hlaw N hN (radK_gT hR) (gT_prof hR.le)
    hR.le hfc hper hLip0 hLip S a ha₀ ha ha₁ hξ hξ1 hρh τb (FlatNPointRate.three_log_ge_one N hN) hNL
  have hp2 : (N : ℝ) * (2 * Real.exp (-(3 * Real.log N))) = 2 / (N : ℝ) ^ 2 := by
    rw [show (2:ℝ) / (N:ℝ) ^ 2 = 30 / (N:ℝ) ^ 2 / 15 by ring, ← prob_30 N hN]; ring
  rw [hp2] at hNa hNb
  set Bt := {ω | ∃ i < N, ¬ (
        |(LN X N (gT R) m₂ S (a τb) ξ f i ω - LN X N (gT R) m₂ S (a τa) ξ f i ω)
            / (τb - τa)
          - (Lmet (gT R) m₂ S (a τb) ξ f (X i ω)
              - Lmet (gT R) m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
      ∧ |(LN X N (gT R) m₂ S (a τb) ξ f i ω - LN X N (gT R) m₂ S (a τa) ξ f i ω)
            / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * m₂ * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * m₂ * gK₀ n R * a₀ ^ 5)))}
    with hBt
  set Na := {ω | ∃ j < N, sampAvg X N (perK (kap (gT R) S (ξ / a τa))) j ω < c
      ∨ Q₀ < sampAvg X N (perK (kap (gT R) S (ξ / a τa))) j ω} with hNadef
  set Nb := {ω | ∃ j < N, sampAvg X N (perK (kap (gT R) S (ξ / a τb))) j ω < c
      ∨ Q₀ < sampAvg X N (perK (kap (gT R) S (ξ / a τb))) j ω} with hNbdef
  have hsub : {ω | ∃ i < N, ¬ (
        |(LNK X N (K τb) m₂ ξ f i ω - LNK X N (K τa) m₂ ξ f i ω)
            / (τb - τa)
          - (Lmet gauss m₂ S (a τb) ξ f (X i ω)
              - Lmet gauss m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + 2 * (errS2 m₂ ξ c (Q₀ + ε) ε B + errP n m₂ ξ R B) / |τb - τa|
      ∧ |(LNK X N (K τb) m₂ ξ f i ω - LNK X N (K τa) m₂ ξ f i ω)
            / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * m₂ * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * m₂ * gK₀ n R * a₀ ^ 5))
          + 2 * errS2 m₂ ξ c (Q₀ + ε) ε B / |τb - τa|)} ⊆ Bt ∪ Na ∪ Nb := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨hBt', hNa'⟩, hNb'⟩ := hcon
    rw [hBt, mem_setOf_eq, not_exists] at hBt'
    simp only [hNadef, mem_setOf_eq, not_exists, not_and, not_or, not_lt] at hNa'
    simp only [hNbdef, mem_setOf_eq, not_exists, not_and, not_or, not_lt] at hNb'
    obtain ⟨i, hi, hbad⟩ := hω
    apply hbad
    have g := hBt' i
    rw [not_and, not_not] at g
    obtain ⟨g1, g2⟩ := g hi
    have sb := LNK_sub X N i hi ω hm₂ S (a := a τb) hξ hc hB (K τb) (hK1 τb) (hK2 τb)
      (fun j hj => (hNb' j hj).1) (fun j hj => (hNb' j hj).2)
    have sa := LNK_sub X N i hi ω hm₂ S (a := a τa) hξ hc hB (K τa) (hK1 τa) (hK2 τa)
      (fun j hj => (hNa' j hj).1) (fun j hj => (hNa' j hj).2)
    have pb := Lmet_gauss_sub (n := n) hR hm₂ S (hpos τb) hξ hfc hB (X i ω)
    have pa := Lmet_gauss_sub (n := n) hR hm₂ S (hpos τa) hξ hfc hB (X i ω)
    refine ⟨?_, ?_⟩
    · exact dq_perturb _ _ _ _ _ _ _ _ _ _ _ _ hη sb sa pb pa g1
    · exact dq_perturb2 _ _ _ _ _ _ _ _ hη sb sa g2
  calc _ ≤ μ.real (Bt ∪ Na ∪ Nb) := measureReal_mono hsub
    _ ≤ μ.real (Bt ∪ Na) + μ.real Nb := measureReal_union_le _ _
    _ ≤ μ.real Bt + μ.real Na + μ.real Nb := by gcongr; exact measureReal_union_le _ _
    _ ≤ 30 / (N : ℝ) ^ 2 + 2 / (N : ℝ) ^ 2 + 2 / (N : ℝ) ^ 2 := by
        linarith [hT, hNa, hNb]
    _ = 34 / (N : ℝ) ^ 2 := by ring

set_option maxHeartbeats 1600000 in
/-- **Stage A: the full Gaussian profile (nearest image) with the sharper additional term.**  As
`flat_npoint_gauss_full`, with `errS` replaced by `errS2 … Q (exp(−R²/2)) B`,
`Q = (3/2) K₀(R)|det S|ξⁿ/a₀ⁿ + exp(−R²/2)`. -/
theorem flat_npoint_gauss_full2 (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LN X N gauss (gm₂ n R) S (a τb) ξ f i ω - LN X N gauss (gm₂ n R) S (a τa) ξ f i ω)
            / (τb - τa)
          - (Lmet gauss (gm₂ n R) S (a τb) ξ f (X i ω)
              - Lmet gauss (gm₂ n R) S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + 2 * (errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + gauss R) (gauss R) B
              + errP n (gm₂ n R) ξ R B) / |τb - τa|
      ∧ |(LN X N gauss (gm₂ n R) S (a τb) ξ f i ω - LN X N gauss (gm₂ n R) S (a τa) ξ f i ω)
            / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * gm₂ n R * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * gm₂ n R * gK₀ n R * a₀ ^ 5))
          + 2 * errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + gauss R) (gauss R) B / |τb - τa|)}
      ≤ 34 / (N : ℝ) ^ 2 :=
  flat_npoint_kernel hn X h_indep hX hlaw N hN hR hf hM hM₄ hper hLip0 hLip hB S a a' hda ha₀ ha ha₁
    hLa hξ hξ1 hρh τa τb hne hNL (fun τ => perK (kap gauss S (ξ / a τ)))
    (fun τ x z => gT_le_gauss R _) (fun τ x z => gauss_le_gT_add R _)

/-! ### Stage B: the lattice-sum kernel -/

/-- The lattice vector `m ∈ ℤⁿ` in `E`. -/
def latV (m : Fin n → ℤ) : E := WithLp.toLp 2 (fun i => ((m i : ℤ) : ℝ))

theorem latV_apply (m : Fin n → ℤ) (i : Fin n) : latV m i = ((m i : ℤ) : ℝ) := rfl

theorem latV_zero : latV (0 : Fin n → ℤ) = 0 := by
  ext i; simp [latV_apply]

/-- The lattice-sum (fully periodised) Gaussian kernel at scale `ξ'`. -/
def latK (S : E ≃L[ℝ] E) (ξ' : ℝ) (x z : E) : ℝ :=
  ∑' m : Fin n → ℤ, gauss (‖S.symm (fr (z - x) + latV m)‖ / ξ')

/-- The decay constant `c = a₀²/(8(‖S‖+1)²ξ²)`. -/
def latC (S : E ≃L[ℝ] E) (ξ a₀ : ℝ) : ℝ := a₀ ^ 2 / (8 * (‖(S : E →L[ℝ] E)‖ + 1) ^ 2 * ξ ^ 2)

/-- The tail bound `e^{−c/2}(1 + √(2π/c))ⁿ`. -/
def latTail (n : ℕ) (S : E ≃L[ℝ] E) (ξ a₀ : ℝ) : ℝ :=
  Real.exp (-latC S ξ a₀ * 1 / 2) * (1 + Real.sqrt (2 * Real.pi / latC S ξ a₀)) ^ n

theorem latC_pos (S : E ≃L[ℝ] E) {ξ a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) : 0 < latC S ξ a₀ := by
  unfold latC; positivity

theorem abs_fr_le (v : E) (i : Fin n) : |fr v i| ≤ 1 / 2 := by
  rw [fr_apply]
  have h1 := Int.floor_le (v i + 1 / 2)
  have h2 := Int.lt_floor_add_one (v i + 1 / 2)
  rw [abs_le]; constructor <;> linarith

theorem coord_sq_ge (t : ℝ) (k : ℤ) (ht : |t| ≤ 1 / 2) : ((k : ℤ) : ℝ) ^ 2 / 4 ≤ (t + k) ^ 2 := by
  rw [abs_le] at ht
  obtain ⟨ht1, ht2⟩ := ht
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    nlinarith
  · subst hk; simp; positivity
  · have : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    nlinarith

theorem norm_sq_eq_sum (y : E) : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem lat_norm_ge (v : E) (hv : ∀ i, |v i| ≤ 1 / 2) (m : Fin n → ℤ) :
    (∑ i, ((m i : ℤ) : ℝ) ^ 2) / 4 ≤ ‖v + latV m‖ ^ 2 := by
  rw [norm_sq_eq_sum, Finset.sum_div]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [PiLp.add_apply, latV_apply]
  exact coord_sq_ge _ _ (hv i)

/-- One term of the lattice sum is at most `exp(−c|m|²)`, for every `a ≥ a₀`. -/
theorem lat_term_le (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (v : E) (hv : ∀ i, |v i| ≤ 1 / 2) (m : Fin n → ℤ) :
    gauss (‖S.symm (v + latV m)‖ / (ξ / a)) ≤
      Real.exp (-(latC S ξ a₀) * ∑ i, ((m i : ℤ) : ℝ) ^ 2) := by
  have hapos : 0 < a := lt_of_lt_of_le ha₀ ha
  have h1 := gauss_kap_le S (div_pos hξ hapos) (v + latV m)
  refine h1.trans (Real.exp_le_exp.2 ?_)
  set M := ‖(S : E →L[ℝ] E)‖ + 1 with hM
  have hM0 : 0 < M := by positivity
  have hy := lat_norm_ge v hv m
  set s := ∑ i, ((m i : ℤ) : ℝ) ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcoef : latC S ξ a₀ * 4 ≤ 1 / (2 * (M * (ξ / a)) ^ 2) := by
    rw [show 1 / (2 * (M * (ξ / a)) ^ 2) = a ^ 2 / (2 * M ^ 2 * ξ ^ 2) by field_simp,
      show latC S ξ a₀ * 4 = a₀ ^ 2 / (2 * M ^ 2 * ξ ^ 2) by unfold latC; rw [← hM]; field_simp; ring]
    gcongr
  have hc0 : 0 ≤ latC S ξ a₀ := (latC_pos S hξ ha₀).le
  have : latC S ξ a₀ * s ≤ 1 / (2 * (M * (ξ / a)) ^ 2) * ‖v + latV m‖ ^ 2 := by
    calc latC S ξ a₀ * s = (latC S ξ a₀ * 4) * (s / 4) := by ring
      _ ≤ 1 / (2 * (M * (ξ / a)) ^ 2) * (s / 4) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ 1 / (2 * (M * (ξ / a)) ^ 2) * ‖v + latV m‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hy (by positivity)
  linarith

theorem latK_summable (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (x z : E) :
    Summable fun m : Fin n → ℤ => gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / a)) :=
  Summable.of_nonneg_of_le (fun m => (gauss_pos _).le)
    (fun m => lat_term_le S hξ ha₀ ha _ (abs_fr_le _) m)
    (CTG.Reals.gauss_summable (latC_pos S hξ ha₀) n)

/-- The nearest image is one term of the lattice sum. -/
theorem nearest_le_latK (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (x z : E) : perK (kap gauss S (ξ / a)) x z ≤ latK S (ξ / a) x z := by
  have hs := latK_summable S hξ ha₀ ha x z
  have := hs.le_tsum 0 (fun m _ => (gauss_pos _).le)
  simpa [perK, kap, latK, latV_zero] using this

theorem one_le_sumsq (m : Fin n → ℤ) (hm : m ≠ 0) : (1 : ℝ) ≤ ∑ i, ((m i : ℤ) : ℝ) ^ 2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hm
  have hi' : m i ≠ 0 := hi
  have hk : (1 : ℤ) ≤ (m i) ^ 2 := by
    have := Int.one_le_abs hi'
    nlinarith [sq_abs (m i)]
  have hk' : (1 : ℝ) ≤ ((m i : ℤ) : ℝ) ^ 2 := by exact_mod_cast hk
  exact hk'.trans (Finset.single_le_sum (f := fun i => ((m i : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- **The lattice sum exceeds the nearest image by at most `latTail`**, for every `a ≥ a₀`. -/
theorem latK_le_nearest (S : E ≃L[ℝ] E) {ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (x z : E) : latK S (ξ / a) x z ≤ perK (kap gauss S (ξ / a)) x z + latTail n S ξ a₀ := by
  set F := fun m : Fin n → ℤ => gauss (‖S.symm (fr (z - x) + latV m)‖ / (ξ / a)) with hF
  have hs : Summable F := latK_summable S hξ ha₀ ha x z
  have hc := latC_pos S hξ ha₀
  have e := hs.tsum_eq_add_tsum_ite 0
  have e0 : F 0 = perK (kap gauss S (ξ / a)) x z := by simp [hF, perK, kap, latV_zero]
  have hs' : Summable fun m => if m = 0 then 0 else F m :=
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> simp [hF, (gauss_pos _).le])
      (fun m => by split_ifs <;> simp [hF, (gauss_pos _).le]) hs
  have htail : ∑' m, (if m = 0 then 0 else F m) ≤ latTail n S ξ a₀ := by
    refine hs'.tsum_le_of_sum_le fun T => ?_
    have e1 : ∑ m ∈ T, (if m = 0 then 0 else F m) = ∑ m ∈ T.filter (fun m => m ≠ 0), F m := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h : m = 0 <;> simp [h]
    rw [e1]
    calc ∑ m ∈ T.filter (fun m => m ≠ 0), F m
        ≤ ∑ m ∈ T.filter (fun m => m ≠ 0),
            Real.exp (-(latC S ξ a₀) * ∑ i, ((m i : ℤ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun m _ => lat_term_le S hξ ha₀ ha _ (abs_fr_le _) m
      _ ≤ Real.exp (-(latC S ξ a₀) * 1 / 2) * (1 + Real.sqrt (2 * Real.pi / latC S ξ a₀)) ^ n :=
          CTG.Reals.gauss_tail_sum_le hc n _ fun m hm =>
            one_le_sumsq m (Finset.mem_filter.1 hm).2
      _ = latTail n S ξ a₀ := rfl
  have : latK S (ξ / a) x z = ∑' m, F m := rfl
  rw [this, e, e0]
  linarith

theorem latK_ge_gT (S : E ≃L[ℝ] E) {R ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (x z : E) : perK (kap (gT R) S (ξ / a)) x z ≤ latK S (ξ / a) x z :=
  (gT_le_gauss R _).trans (nearest_le_latK S hξ ha₀ ha x z)

theorem latK_le_gT (S : E ≃L[ℝ] E) {R ξ a a₀ : ℝ} (hξ : 0 < ξ) (ha₀ : 0 < a₀) (ha : a₀ ≤ a)
    (x z : E) : latK S (ξ / a) x z
      ≤ perK (kap (gT R) S (ξ / a)) x z + (gauss R + latTail n S ξ a₀) := by
  have h1 := latK_le_nearest S hξ ha₀ ha x z
  have h2 := gauss_le_gT_add R (‖S.symm (fr (z - x))‖ / (ξ / a))
  simp only [perK, kap] at h1 h2 ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **Stage B: the N-point statement for the LATTICE-SUM Gaussian kernel on the sample side**
(`Σ_{m ∈ ℤⁿ} exp(−‖S⁻¹(fr(z−x)+m)‖² a(τ)²/(2ξ²))`), compared with the population operator `Lmet gauss`
(integral over `ℝⁿ`).  Additional sample error `errS2 … Q ε B` with `ε = exp(−R²/2) + latTail n S ξ a₀`,
`Q = (3/2)K₀(R)|det S|ξⁿ/a₀ⁿ + ε`.  Probability `≥ 1 − 34/N²`. -/
theorem flat_npoint_lattice (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hρh : ‖(S : E →L[ℝ] E)‖ * (ξ / a₀ * R) < 1 / 2)
    (τa τb : ℝ) (hne : τb ≠ τa)
    (hNL : 92416 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 14 * (3 * Real.log N) ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (gm₂ n R) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gm₂ n R) ξ f i ω) / (τb - τa)
          - (Lmet gauss (gm₂ n R) S (a τb) ξ f (X i ω)
              - Lmet gauss (gm₂ n R) S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + 2 * (errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + (gauss R + latTail n S ξ a₀))
                (gauss R + latTail n S ξ a₀) B
              + errP n (gm₂ n R) ξ R B) / |τb - τa|
      ∧ |(LNK X N (latK S (ξ / a τb)) (gm₂ n R) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gm₂ n R) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * gm₂ n R * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * gm₂ n R * gK₀ n R * a₀ ^ 5))
          + 2 * errS2 (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2)
                (3 / 2 * (gK₀ n R * dS S / a₀ ^ n * ξ ^ n) + (gauss R + latTail n S ξ a₀))
                (gauss R + latTail n S ξ a₀) B / |τb - τa|)}
      ≤ 34 / (N : ℝ) ^ 2 :=
  flat_npoint_kernel hn X h_indep hX hlaw N hN hR hf hM hM₄ hper hLip0 hLip hB S a a' hda ha₀ ha ha₁
    hLa hξ hξ1 hρh τa τb hne hNL (fun τ => latK S (ξ / a τ))
    (fun τ x z => latK_ge_gT S hξ ha₀ (ha τ) x z) (fun τ x z => latK_le_gT S hξ ha₀ (ha τ) x z)

end CTG.FlatNPointGaussLattice
