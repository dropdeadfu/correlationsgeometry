/-
Forty-sixth file: the flat N-point statement for the FULL Gaussian profile `exp(−s²/2)` with the nearest-image
periodisation, by comparison with the cut-off profile `gT R` of the thirty-eighth file.
Namespace `CTG.FlatNPointGaussFull`; imports the thirty-eighth and thirty-seventh files (compiled modules);
check with `./check_flat_npoint_gauss_full.sh`.
Stage 1: `gauss_le_gT_add` (`gT ≤ gauss ≤ gT + exp(−R²/2)`).
Stage 2: (a) sample side, abstract (`sampW_quot_perturb`): kernels `K ≤ K' ≤ K + ε`, `0 ≤ K ≤ A`, sample
normalisations of `K` at least `c`, of `K'` at most `Q` ⇒ the normalised sample quotients differ by
`≤ 2 G (ε/c + A ε/c²) Q/c`; (b) population side (`PG_gauss_sub`): the averaging operators of the two profiles
differ by `≤ 2 B ((2π)^{n/2} − K₀(R))/K₀(R)`.
Stage 3: `flat_npoint_gauss_full`: both inequalities for the full Gaussian kernel with the additional terms
`2(E_s + E_p)/|η|` resp. `2 E_s/|η|`; exceptional probability `≤ 34/N²` (outer measure; measurability not shown).
HYPOTHESIS beyond `flat_npoint_gauss_truncated`: `|f| ≤ B` (true for periodic continuous `f`, not derived here).
LIMITS (hand estimates of the sub-task, not statements): `E_s ~ exp(−R²/2) ξ^{−3n−2}` because the denominator is
bounded below only crudely; with the coupling `‖S‖ ξ R/a₀ < 1/2` the additional terms are small only for
`R ~ c₁ √(log N)` with `c₁` large, which forces `ξ ≲ 1/√(log N)` and puts powers of `log N` into `Λ`; the terms carry
`1/|η|` and are not uniform for close times.
NOT formalised: the lattice-sum kernel on the sample side (the population operator `PG` is an integral over `ℝⁿ`;
its unfolding for periodic `f` is not a statement here); `gm₂ → 1`; an explicit rate of
`((2π)^{n/2} − K₀(R))/K₀(R)` in `R`.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryFlatNPointGauss
import CorrelationsToGeometryFlatNPointWindow

open MeasureTheory ProbabilityTheory Set
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointGaussFull

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Stage 1: pointwise comparison of the profiles -/

theorem gauss_le_gT_add (R s : ℝ) : gauss s ≤ gT R s + gauss R := by
  have := gT_sub_gauss (R := R) s
  have := le_abs_self (gauss s - gT R s)
  linarith

/-! ### Stage 2 (algebra) -/

/-- Perturbation of a quotient: `|a'/b' − a/b| ≤ 2Gδ/m`. -/
theorem quot_perturb (a b a' b' G δ m : ℝ) (hm : 0 < m) (hb : m ≤ b) (hb' : m ≤ b')
    (ha : |a| ≤ G * b) (hda : |a' - a| ≤ G * δ) (hdb : |b' - b| ≤ δ) :
    |a' / b' - a / b| ≤ 2 * G * δ / m := by
  have hb0 : 0 < b := lt_of_lt_of_le hm hb
  have hb'0 : 0 < b' := lt_of_lt_of_le hm hb'
  have hG : 0 ≤ G := by
    by_contra hc; push Not at hc
    have : G * b < 0 := mul_neg_of_neg_of_pos hc hb0
    linarith [abs_nonneg a]
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hdb
  have hab : |a / b| ≤ G := by
    rw [abs_div, abs_of_pos hb0, div_le_iff₀ hb0]; exact ha
  have e : a' / b' - a / b = ((a' - a) - (a / b) * (b' - b)) / b' := by
    field_simp; ring
  have hnum : |(a' - a) - (a / b) * (b' - b)| ≤ 2 * G * δ := by
    calc |(a' - a) - (a / b) * (b' - b)| ≤ |a' - a| + |(a / b) * (b' - b)| := abs_sub _ _
      _ = |a' - a| + |a / b| * |b' - b| := by rw [abs_mul]
      _ ≤ G * δ + G * δ := by gcongr
      _ = 2 * G * δ := by ring
  rw [e, abs_div, abs_of_pos hb'0, div_le_iff₀ hb'0]
  have h2 : 0 ≤ 2 * G * δ := by positivity
  calc |(a' - a) - (a / b) * (b' - b)| ≤ 2 * G * δ := hnum
    _ = 2 * G * δ / m * m := by field_simp
    _ ≤ 2 * G * δ / m * b' := by gcongr

/-- One term: `|K'/q' − K/q| ≤ ε/c + A ε/c²`. -/
theorem term_perturb (K K' q q' A c ε : ℝ) (hK0 : 0 ≤ K) (hKA : K ≤ A) (h1 : K ≤ K')
    (h2 : K' ≤ K + ε) (hc : 0 < c) (hq : c ≤ q) (hq1 : q ≤ q') (hq2 : q' ≤ q + ε) :
    |K' * (1 / q') - K * (1 / q)| ≤ ε / c + A * ε / c ^ 2 := by
  have hq0 : 0 < q := lt_of_lt_of_le hc hq
  have hq'0 : 0 < q' := lt_of_lt_of_le hq0 hq1
  have hε : 0 ≤ ε := by linarith
  have hA : 0 ≤ A := le_trans hK0 hKA
  have e : K' * (1 / q') - K * (1 / q) = (K' - K) / q' - K * (q' - q) / (q * q') := by
    field_simp; ring
  have hx0 : 0 ≤ (K' - K) / q' := div_nonneg (by linarith) hq'0.le
  have hy0 : 0 ≤ K * (q' - q) / (q * q') := div_nonneg (mul_nonneg hK0 (by linarith)) (by positivity)
  have hx : (K' - K) / q' ≤ ε / c := by
    have : (K' - K) / q' ≤ ε / q' := by gcongr; linarith
    exact this.trans (by gcongr; linarith)
  have hy : K * (q' - q) / (q * q') ≤ A * ε / c ^ 2 := by
    have hcc : c ^ 2 ≤ q * q' := by
      rw [sq]; exact mul_le_mul hq (by linarith) hc.le hq0.le
    calc K * (q' - q) / (q * q') ≤ A * ε / (q * q') := by
          gcongr
          all_goals linarith
      _ ≤ A * ε / c ^ 2 := by gcongr
  rw [e, abs_sub_le_iff]; constructor <;> nlinarith

/-- `|avgN u| ≤ avgN v` from termwise `|u_j| ≤ v_j`. -/
theorem avgN_abs_le (N : ℕ) (u v : ℕ → ℝ) (h : ∀ j ∈ Finset.range N, |u j| ≤ v j) :
    |avgN N u| ≤ avgN N v := by
  unfold avgN
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (N:ℝ))]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)

theorem avgN_mono (N : ℕ) (u v : ℕ → ℝ) (h : ∀ j ∈ Finset.range N, u j ≤ v j) :
    avgN N u ≤ avgN N v := by
  unfold avgN
  gcongr with j hj
  exact h j hj

theorem avgN_const (N : ℕ) (hN : 0 < N) (c : ℝ) : avgN N (fun _ => c) = c := by
  unfold avgN
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem avgN_sub (N : ℕ) (u v : ℕ → ℝ) : avgN N u - avgN N v = avgN N (fun j => u j - v j) := by
  unfold avgN; rw [← mul_sub, ← Finset.sum_sub_distrib]

/-! ### Stage 2 (a): the sample quotient -/

/-- **Sample side.**  Kernels `K ≤ K' ≤ K + ε`, `0 ≤ K ≤ A`; sample normalisations of `K` at least `c`
(at every sample point), of `K'` at most `Q`; `|g| ≤ G`.  Then the quotients
`sampW(g)/sampW(1)` of the two kernels differ by at most `2 G (ε/c + A ε/c²) Q/c`. -/
theorem sampW_quot_perturb {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (K K' g : E → E → ℝ)
    (i : ℕ) (hi : i < N) (ω : Ω) {A Q c ε G : ℝ}
    (hK0 : ∀ x z, 0 ≤ K x z) (hKA : ∀ x z, K x z ≤ A) (h1 : ∀ x z, K x z ≤ K' x z)
    (h2 : ∀ x z, K' x z ≤ K x z + ε) (hc : 0 < c)
    (hq : ∀ j < N, c ≤ sampAvg X N K j ω) (hQ : ∀ j < N, sampAvg X N K' j ω ≤ Q)
    (hg : ∀ x z, |g x z| ≤ G) :
    |sampW X N K' g i ω / sampW X N K' (fun _ _ => 1) i ω
        - sampW X N K g i ω / sampW X N K (fun _ _ => 1) i ω|
      ≤ 2 * G * (ε / c + A * ε / c ^ 2) / (c / Q) := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i) hi
  set q := fun j => sampAvg X N K j ω with hqdef
  set q' := fun j => sampAvg X N K' j ω with hq'def
  have hε : 0 ≤ ε := by have := h1 (X 0 ω) (X 0 ω); have := h2 (X 0 ω) (X 0 ω); linarith
  have hqq' : ∀ j, q j ≤ q' j := fun j => by
    simp only [hqdef, hq'def, sampAvg]
    gcongr with k hk; exact h1 _ _
  have hq'q : ∀ j, q' j ≤ q j + ε := fun j => by
    have e1 : sampAvg X N K' j ω = avgN N (fun k => K' (X j ω) (X k ω)) := rfl
    have e2 : sampAvg X N K j ω = avgN N (fun k => K (X j ω) (X k ω)) := rfl
    simp only [hqdef, hq'def, e1, e2]
    rw [← avgN_const N hN ε, ← sub_le_iff_le_add', avgN_sub]
    exact avgN_mono N _ _ fun k _ => by linarith [h2 (X j ω) (X k ω)]
  have hQ0 : 0 < Q := lt_of_lt_of_le hc ((hq 0 hN).trans ((hqq' 0).trans (hQ 0 hN)))
  have hm : 0 < c / Q := div_pos hc hQ0
  -- the four averages as `avgN`
  have eW : ∀ (L : E → E → ℝ) (u : E → E → ℝ),
      sampW X N L u i ω = avgN N (fun j => L (X i ω) (X j ω) * u (X i ω) (X j ω)
        * (1 / sampAvg X N L j ω)) := fun _ _ => rfl
  have eA : sampAvg X N K i ω = avgN N (fun j => K (X i ω) (X j ω)) := rfl
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
  -- |W(g)| ≤ G W(1)
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
  set δ := ε / c + A * ε / c ^ 2 with hδ
  have hterm : ∀ j < N, |K' (X i ω) (X j ω) * (1 / q' j) - K (X i ω) (X j ω) * (1 / q j)| ≤ δ :=
    fun j hj => term_perturb _ _ _ _ A c ε (hK0 _ _) (hKA _ _) (h1 _ _) (h2 _ _) hc (hq j hj)
      (hqq' j) (hq'q j)
  have hda : |sampW X N K' g i ω - sampW X N K g i ω| ≤ G * δ := by
    rw [eW, eW, avgN_sub, ← avgN_const N hN (G * δ)]
    refine avgN_abs_le N _ _ fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [show K' (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N K' j ω)
          - K (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N K j ω)
        = g (X i ω) (X j ω) * (K' (X i ω) (X j ω) * (1 / q' j) - K (X i ω) (X j ω) * (1 / q j))
        by simp only [hqdef, hq'def]; ring, abs_mul]
    exact mul_le_mul (hg _ _) (hterm j hj') (abs_nonneg _)
      (le_trans (abs_nonneg _) (hg (X i ω) (X i ω)))
  have hdb : |sampW X N K' (fun _ _ => 1) i ω - sampW X N K (fun _ _ => 1) i ω| ≤ δ := by
    rw [eW, eW, avgN_sub, ← avgN_const N hN δ]
    refine avgN_abs_le N _ _ fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [show K' (X i ω) (X j ω) * (fun _ _ => (1:ℝ)) (X i ω) (X j ω) * (1 / sampAvg X N K' j ω)
          - K (X i ω) (X j ω) * (fun _ _ => (1:ℝ)) (X i ω) (X j ω) * (1 / sampAvg X N K j ω)
        = K' (X i ω) (X j ω) * (1 / q' j) - K (X i ω) (X j ω) * (1 / q j)
        by simp only [hqdef, hq'def]; ring]
    exact hterm j hj'
  have hda' : |sampW X N K' g i ω - sampW X N K g i ω| ≤ G * δ := hda
  have hdb' : |sampW X N K' (fun _ _ => 1) i ω - sampW X N K (fun _ _ => 1) i ω| ≤ δ := hdb
  exact quot_perturb _ _ _ _ G δ (c / Q) hm hb hb' ha hda hdb


/-! ### Stage 2 (b): the population averaging operator -/

/-- Mass of a flat kernel: `∫ h(‖S⁻¹v‖/ξ') dv = (∫ h(‖z‖) dz) |det S| ξ'ⁿ` (proof as `mass_eq`). -/
theorem kap_int (h : ℝ → ℝ) (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') :
    ∫ v, kap h S ξ' v = (∫ z : E, h ‖z‖) * dS S * ξ' ^ n := by
  have hsc : ∀ u : E, ‖ξ' • u‖ / ξ' = ‖u‖ := fun u => by
    rw [norm_smul, Real.norm_of_nonneg hξ.le]; field_simp
  have h1 := substE S (fun y => h (‖S.symm y‖ / ξ'))
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h1
  have h2 := Measure.integral_comp_smul (volume : Measure E) (fun w : E => h (‖w‖ / ξ')) ξ'
  simp only [hsc, smul_eq_mul, finrank_euclideanSpace_fin] at h2
  rw [h1] at h2
  have hp : (0:ℝ) < ξ' ^ n := pow_pos hξ n
  rw [abs_of_pos (inv_pos.2 hp)] at h2
  have hd := dS_pos S
  show ∫ v, h (‖S.symm v‖ / ξ') = _
  rw [h2]
  field_simp

/-- Gaussian domination of the flat Gaussian kernel. -/
theorem gauss_kap_le (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') (y : E) :
    gauss (‖S.symm y‖ / ξ') ≤
      Real.exp (-(1 / (2 * ((‖(S : E →L[ℝ] E)‖ + 1) * ξ') ^ 2)) * ‖y‖ ^ 2) := by
  set M := ‖(S : E →L[ℝ] E)‖ + 1 with hM
  set u := ‖S.symm y‖ with hu
  have hM0 : 0 < M := by positivity
  have hy : ‖y‖ ≤ M * u := by
    have := (S : E →L[ℝ] E).le_opNorm (S.symm y)
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at this
    nlinarith [norm_nonneg (S.symm y)]
  have hy2 : ‖y‖ ^ 2 ≤ (M * u) ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  have key : 1 / (2 * (M * ξ') ^ 2) * ‖y‖ ^ 2 ≤ (u / ξ') ^ 2 / 2 := by
    rw [show (u / ξ') ^ 2 / 2 = (M * u) ^ 2 / (2 * (M * ξ') ^ 2) by field_simp,
      div_mul_eq_mul_div, one_mul]
    gcongr
  unfold gauss
  apply Real.exp_le_exp.2
  linarith

theorem gauss_kap_integrable (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ') {φ : E → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) {k : ℝ → ℝ} (hkc : Continuous k)
    (hk0 : ∀ s, 0 ≤ k s) (hkg : ∀ s, k s ≤ gauss s) :
    Integrable (fun y : E => k (‖S.symm y‖ / ξ') * φ y) := by
  have hb : 0 < 1 / (2 * ((‖(S : E →L[ℝ] E)‖ + 1) * ξ') ^ 2) := by positivity
  refine ((expB_integrable (n := n) hb).const_mul B).mono' ?_ (ae_of_all _ fun y => ?_)
  · exact ((hkc.comp ((continuous_norm.comp S.symm.continuous).div_const ξ')).mul
      hφ).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 _), mul_comm]
    exact mul_le_mul (hB y) ((hkg _).trans (gauss_kap_le S hξ y)) (hk0 _)
      ((abs_nonneg _).trans (hB y))

/-- **Population side.**  For a continuous `f` with `|f| ≤ B`, the averaging operators of the full and of
the cut-off Gaussian profile differ by at most `2 B ((2π)^{n/2} − K₀(R))/K₀(R)`, uniformly in `S`, `ξ'`, `x`. -/
theorem PG_gauss_sub {R : ℝ} (hR : 0 < R) (S : E ≃L[ℝ] E) {ξ' : ℝ} (hξ : 0 < ξ')
    {f : E → ℝ} (hfc : Continuous f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (x : E) :
    |PG gauss S ξ' f x - PG (gT R) S ξ' f x|
      ≤ 2 * B * ((2 * Real.pi) ^ ((n : ℝ) / 2) - gK₀ n R) / gK₀ n R := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hφ : Continuous fun y : E => f (x + y) := hfc.comp (continuous_const.add continuous_id)
  have hφB : ∀ y : E, |f (x + y)| ≤ B := fun y => hB _
  have h1c : Continuous fun _ : E => (1:ℝ) := continuous_const
  have h1B : ∀ y : E, |(fun _ : E => (1:ℝ)) y| ≤ 1 := fun y => by simp
  have hgg : ∀ s, gauss s ≤ gauss s := fun s => le_rfl
  have i1 := gauss_kap_integrable S hξ hφ hφB gauss_continuous (fun s => (gauss_pos s).le) hgg
  have i2 := gauss_kap_integrable S hξ hφ hφB (gT_continuous R) (gT_nonneg R) (gT_le_gauss R)
  have i3 := gauss_kap_integrable S hξ h1c h1B gauss_continuous (fun s => (gauss_pos s).le) hgg
  have i4 := gauss_kap_integrable S hξ h1c h1B (gT_continuous R) (gT_nonneg R) (gT_le_gauss R)
  simp only [mul_one] at i3 i4
  set a := ∫ y : E, gT R (‖S.symm y‖ / ξ') * f (x + y) with ha
  set a' := ∫ y : E, gauss (‖S.symm y‖ / ξ') * f (x + y) with ha'
  set b := ∫ y : E, gT R (‖S.symm y‖ / ξ') with hb
  set b' := ∫ y : E, gauss (‖S.symm y‖ / ξ') with hb'
  have mb : b = gK₀ n R * dS S * ξ' ^ n := kap_int (gT R) S hξ
  have mb' : b' = (2 * Real.pi) ^ ((n : ℝ) / 2) * dS S * ξ' ^ n := by
    rw [hb', show (∫ y : E, gauss (‖S.symm y‖ / ξ')) = ∫ v, kap gauss S ξ' v from rfl,
      kap_int gauss S hξ, gauss_integral]
  have hK := gK₀_pos (n := n) hR
  have hd := dS_pos S
  have hp : (0:ℝ) < ξ' ^ n := pow_pos hξ n
  have hm : 0 < b := by rw [mb]; positivity
  have hbb' : b ≤ b' := integral_mono i4 i3 fun y => gT_le_gauss R _
  have hA : |a| ≤ B * b := by
    calc |a| ≤ ∫ y : E, |gT R (‖S.symm y‖ / ξ') * f (x + y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y : E, B * gT R (‖S.symm y‖ / ξ') :=
          integral_mono i2.abs (i4.const_mul B) fun y => by
            rw [abs_mul, abs_of_nonneg (gT_nonneg R _), mul_comm]
            exact mul_le_mul_of_nonneg_right (hB _) (gT_nonneg R _)
      _ = B * b := integral_const_mul B _
  have hDA : |a' - a| ≤ B * (b' - b) := by
    rw [ha', ha, ← integral_sub i1 i2, hb', hb, ← integral_sub i3 i4, ← integral_const_mul]
    refine abs_integral_le_integral_abs.trans (integral_mono (i1.sub i2).abs
      ((i3.sub i4).const_mul B) fun y => ?_)
    have hle := gT_le_gauss R (‖S.symm y‖ / ξ')
    rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB _) (by linarith)
  have hDB : |b' - b| ≤ b' - b := by rw [abs_of_nonneg (by linarith)]
  have q := quot_perturb a b a' b' B (b' - b) b hm le_rfl hbb' hA hDA hDB
  have e1 : PG gauss S ξ' f x = a' / b' := rfl
  have e2 : PG (gT R) S ξ' f x = a / b := rfl
  rw [e1, e2]
  refine q.trans (le_of_eq ?_)
  rw [mb, mb']
  field_simp

/-! ### Stage 3: the two operators at one time -/

theorem sampAvg_le_one {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K : E → E → ℝ)
    (hK : ∀ x z, K x z ≤ 1) (j : ℕ) (ω : Ω) : sampAvg X N K j ω ≤ 1 := by
  have e : sampAvg X N K j ω = avgN N (fun k => K (X j ω) (X k ω)) := rfl
  rw [e, ← avgN_const N hN 1]
  exact avgN_mono N _ _ fun k _ => hK _ _

/-- The additional sample error `E_s = (2/(m₂ξ²))·2·(2B)(ε/c + ε/c²)/c`. -/
def errS (m₂ ξ c ε B : ℝ) : ℝ := 2 / (m₂ * ξ ^ 2) * (2 * (2 * B) * (ε / c + 1 * ε / c ^ 2) / (c / 1))

/-- The additional population error `E_p = (2/(m₂ξ²))·2B((2π)^{n/2} − K₀(R))/K₀(R)`. -/
def errP (n : ℕ) (m₂ ξ R B : ℝ) : ℝ :=
  2 / (m₂ * ξ ^ 2) * (2 * B * ((2 * Real.pi) ^ ((n : ℝ) / 2) - gK₀ n R) / gK₀ n R)

theorem LN_gauss_sub {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (i : ℕ) (hi : i < N) (ω : Ω)
    {R : ℝ} {m₂ : ℝ} (hm₂ : 0 < m₂) (S : E ≃L[ℝ] E) {a ξ c B : ℝ} (hξ : 0 < ξ) (hc : 0 < c)
    {f : E → ℝ} (hB : ∀ y, |f y| ≤ B)
    (hq : ∀ j < N, c ≤ sampAvg X N (perK (kap (gT R) S (ξ / a))) j ω) :
    |LN X N gauss m₂ S a ξ f i ω - LN X N (gT R) m₂ S a ξ f i ω| ≤ errS m₂ ξ c (gauss R) B := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le i) hi
  have hQ := sampW_quot_perturb X N (perK (kap (gT R) S (ξ / a))) (perK (kap gauss S (ξ / a)))
    (gd f) i hi ω (A := 1) (Q := 1) (ε := gauss R) (G := 2 * B)
    (fun x z => gT_nonneg R _) (fun x z => gT_le_one R _) (fun x z => gT_le_gauss R _)
    (fun x z => gauss_le_gT_add R _) hc hq
    (fun j _ => sampAvg_le_one X N hN _ (fun x z => gauss_le_one _) j ω)
    (fun x z => by
      unfold gd
      calc |f z - f x| ≤ |f z| + |f x| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hB z, hB x])
  unfold LN errS
  rw [← mul_sub, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 / (m₂ * ξ ^ 2))]
  exact mul_le_mul_of_nonneg_left hQ (by positivity)

theorem Lmet_gauss_sub {R : ℝ} (hR : 0 < R) {m₂ : ℝ} (hm₂ : 0 < m₂) (S : E ≃L[ℝ] E)
    {a ξ : ℝ} (ha : 0 < a) (hξ : 0 < ξ) {f : E → ℝ} (hfc : Continuous f) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (x : E) :
    |Lmet gauss m₂ S a ξ f x - Lmet (gT R) m₂ S a ξ f x| ≤ errP n m₂ ξ R B := by
  unfold Lmet errP
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / (m₂ * ξ ^ 2)),
    show f x - PG gauss S (ξ / a) f x - (f x - PG (gT R) S (ξ / a) f x)
      = -(PG gauss S (ξ / a) f x - PG (gT R) S (ξ / a) f x) by ring, abs_neg]
  exact mul_le_mul_of_nonneg_left (PG_gauss_sub hR S (div_pos hξ ha) hfc hB x) (by positivity)

/-- Difference quotients of perturbed quantities. -/
theorem dq_perturb (xb xa yb ya xb' xa' yb' ya' η M e p : ℝ) (hη : η ≠ 0)
    (h1 : |xb' - xb| ≤ e) (h2 : |xa' - xa| ≤ e) (h3 : |yb' - yb| ≤ p) (h4 : |ya' - ya| ≤ p)
    (h : |(xb - xa) / η - (yb - ya) / η| ≤ M) :
    |(xb' - xa') / η - (yb' - ya') / η| ≤ M + 2 * (e + p) / |η| := by
  have hη' : 0 < |η| := abs_pos.2 hη
  have e0 : (xb' - xa') / η - (yb' - ya') / η
      = ((xb - xa) / η - (yb - ya) / η) + ((xb' - xb) - (xa' - xa) - (yb' - yb) + (ya' - ya)) / η := by
    field_simp; ring
  rw [e0]
  refine (abs_add_le _ _).trans (add_le_add h ?_)
  rw [abs_div]
  gcongr
  calc |(xb' - xb) - (xa' - xa) - (yb' - yb) + (ya' - ya)|
      ≤ |xb' - xb| + |xa' - xa| + |yb' - yb| + |ya' - ya| := by
        have := abs_add_le ((xb' - xb) - (xa' - xa) - (yb' - yb)) (ya' - ya)
        have := abs_sub ((xb' - xb) - (xa' - xa)) (yb' - yb)
        have := abs_sub (xb' - xb) (xa' - xa)
        linarith
    _ ≤ 2 * (e + p) := by linarith

theorem dq_perturb2 (xb xa xb' xa' η Z M e : ℝ) (hη : η ≠ 0)
    (h1 : |xb' - xb| ≤ e) (h2 : |xa' - xa| ≤ e) (h : |(xb - xa) / η + Z| ≤ M) :
    |(xb' - xa') / η + Z| ≤ M + 2 * e / |η| := by
  have hη' : 0 < |η| := abs_pos.2 hη
  have e0 : (xb' - xa') / η + Z = ((xb - xa) / η + Z) + ((xb' - xb) - (xa' - xa)) / η := by
    field_simp; ring
  rw [e0]
  refine (abs_add_le _ _).trans (add_le_add h ?_)
  rw [abs_div]
  gcongr
  calc |(xb' - xb) - (xa' - xa)| ≤ |xb' - xb| + |xa' - xa| := abs_sub _ _
    _ ≤ 2 * e := by linarith

/-! ### Stage 3: the N-point statement for the full Gaussian profile (nearest image) -/

set_option maxHeartbeats 3200000 in
/-- **`prop:dotLN-diff`, flat periodic case, rate form, for the FULL Gaussian profile `exp(−s²/2)`**
(kernel `exp(−‖S⁻¹ fr(z−x)‖² a(τ)²/(2ξ²))`, nearest image), with the normalisation `m₂ = gm₂ n R` and the
moments of the cut-off profile in the main terms; `R` is a free parameter with the coupling
`‖S‖ ξ R/a₀ < 1/2` of `flat_npoint_gauss_truncated`.  Additional terms
`2 (E_s + E_p)/|η|` in (i) and `2 E_s/|η|` in (ii), with `c = K₀(R)|det S| ξⁿ/(2 a₁ⁿ)`,
`E_s = errS (gm₂ n R) ξ c (exp(−R²/2)) B`, `E_p = errP n (gm₂ n R) ξ R B`.
HYPOTHESES as in `flat_npoint_gauss_truncated`, and `|f| ≤ B`.  Probability `≥ 1 − 34/N²`. -/
theorem flat_npoint_gauss_full (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
          + 2 * (errS (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2) (gauss R) B
              + errP n (gm₂ n R) ξ R B) / |τb - τa|
      ∧ |(LN X N gauss (gm₂ n R) S (a τb) ξ f i ω - LN X N gauss (gm₂ n R) S (a τa) ξ f i ω)
            / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / gm₂ n R
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * gm₂ n R * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * gm₂ n R * gK₀ n R * a₀ ^ 5))
          + 2 * errS (gm₂ n R) ξ (gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2) (gauss R) B / |τb - τa|)}
      ≤ 34 / (N : ℝ) ^ 2 := by
  set c := gK₀ n R * dS S / a₁ ^ n * ξ ^ n / 2 with hcdef
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
  have hNa := CTG.FlatNPointWindow.norm_event X h_indep hX hlaw N hN (radK_gT hR) (gT_prof hR.le)
    hR.le hfc hper hLip0 hLip S a ha₀ ha ha₁ hξ hξ1 hρh τa (FlatNPointRate.three_log_ge_one N hN) hNL
  have hNb := CTG.FlatNPointWindow.norm_event X h_indep hX hlaw N hN (radK_gT hR) (gT_prof hR.le)
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
  set Na := {ω | ∃ j < N, sampAvg X N (perK (kap (gT R) S (ξ / a τa))) j ω < c} with hNadef
  set Nb := {ω | ∃ j < N, sampAvg X N (perK (kap (gT R) S (ξ / a τb))) j ω < c} with hNbdef
  have hsub : {ω | ∃ i < N, ¬ (
        |(LN X N gauss m₂ S (a τb) ξ f i ω - LN X N gauss m₂ S (a τa) ξ f i ω)
            / (τb - τa)
          - (Lmet gauss m₂ S (a τb) ξ f (X i ω)
              - Lmet gauss m₂ S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + 2 * (errS m₂ ξ c (gauss R) B + errP n m₂ ξ R B) / |τb - τa|
      ∧ |(LN X N gauss m₂ S (a τb) ξ f i ω - LN X N gauss m₂ S (a τa) ξ f i ω)
            / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * rLam 1 (gK₀ n R) 1 R La a₀ a₁ Lip S ^ 20 / m₂
            * Real.sqrt (3 * Real.log N / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R
                / (6 * m₂ * gK₀ n R * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gμ₄ n R * La / (3 * m₂ * gK₀ n R * a₀ ^ 5))
          + 2 * errS m₂ ξ c (gauss R) B / |τb - τa|)} ⊆ Bt ∪ Na ∪ Nb := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨hBt', hNa'⟩, hNb'⟩ := hcon
    rw [hBt, mem_setOf_eq, not_exists] at hBt'
    simp only [hNadef, mem_setOf_eq, not_exists, not_and, not_lt] at hNa'
    simp only [hNbdef, mem_setOf_eq, not_exists, not_and, not_lt] at hNb'
    obtain ⟨i, hi, hbad⟩ := hω
    apply hbad
    have g := hBt' i
    rw [not_and, not_not] at g
    obtain ⟨g1, g2⟩ := g hi
    have sb := LN_gauss_sub X N i hi ω hm₂ S (a := a τb) hξ hc hB hNb'
    have sa := LN_gauss_sub X N i hi ω hm₂ S (a := a τa) hξ hc hB hNa'
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

end CTG.FlatNPointGaussFull
