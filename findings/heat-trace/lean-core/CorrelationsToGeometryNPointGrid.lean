/-
Twenty-second file: the N-point statement simultaneously for ALL pairs of times `(a, b)` of a window with
`|b − a| ≥ η₀`, on one event (time grid).  Namespace `CTG.NPointGrid`; imports the twentieth file (compiled
module `.tools/leanbuild/CorrelationsToGeometryNPointUniform.olean`); check with `./check_npoint_grid.sh`.
Main statements: `npoint_grid` (free `L`), `npoint_grid_log` (probability at least `1 − 1/N²`).  The bound is the
main term `C·δ'/ξ` PLUS a grid term `4·Λ_D·hw/η₀/(c_h ξ²/2)` with a free grid width `hw`; the Lipschitz constant
`Λ_D` (`gridLam`) is very crude (powers of `N`, because the sample normalisations are bounded below only by the
self term), so `hw` has to be polynomially small in `N`; this choice is NOT made in a statement.
NOT formalised: measurability of the (uncountable-union) exceptional set (`μ.real` is an outer measure here),
the limit `η₀ → 0`, Step 6.  HYPOTHESIS beyond the earlier files: `|f| ≤ B_f`.
No `sorry`, no `axiom`, no `native_decide`.  Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryNPointUniform

open Set MeasureTheory ProbabilityTheory
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.NPointUniform

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.NPointGrid

/-! ### Real-number lemmas -/

/-- One weighted term `k g/p` against `k' g/p'`. -/
theorem term_lip {k k' g p p' A Bg c e e' : ℝ} (hc : 0 < c) (hp : c ≤ p) (hp' : c ≤ p')
    (hk' : |k'| ≤ A) (hg : |g| ≤ Bg) (hkk : |k - k'| ≤ e) (hpp : |p - p'| ≤ e') :
    |k * g * (1 / p) - k' * g * (1 / p')| ≤ e * Bg * (1 / c) + A * Bg * (e' / c ^ 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le hc hp
  have hp0' : 0 < p' := lt_of_lt_of_le hc hp'
  have hBg : 0 ≤ Bg := (abs_nonneg _).trans hg
  have hA : 0 ≤ A := (abs_nonneg _).trans hk'
  have he : 0 ≤ e := (abs_nonneg _).trans hkk
  have he' : 0 ≤ e' := (abs_nonneg _).trans hpp
  have hd : 1 / p - 1 / p' = (p' - p) / (p * p') := by
    rw [div_sub_div _ _ hp0.ne' hp0'.ne']; ring
  have e1 : k * g * (1 / p) - k' * g * (1 / p')
      = (k - k') * g * (1 / p) + k' * g * ((p' - p) / (p * p')) := by
    rw [← hd]; ring
  rw [e1]
  have t1 : |(k - k') * g * (1 / p)| ≤ e * Bg * (1 / c) := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / p)]
    have h1 : 1 / p ≤ 1 / c := one_div_le_one_div_of_le hc hp
    exact mul_le_mul (mul_le_mul hkk hg (abs_nonneg _) he) h1 (by positivity) (by positivity)
  have t2 : |k' * g * ((p' - p) / (p * p'))| ≤ A * Bg * (e' / c ^ 2) := by
    rw [abs_mul, abs_mul, abs_div, abs_of_pos (mul_pos hp0 hp0')]
    have h1 : |p' - p| ≤ e' := by rw [abs_sub_comm]; exact hpp
    have h2 : c ^ 2 ≤ p * p' := by rw [sq]; exact mul_le_mul hp hp' hc.le hp0.le
    have h3 : |p' - p| / (p * p') ≤ e' / c ^ 2 :=
      calc |p' - p| / (p * p') ≤ e' / (p * p') := div_le_div_of_nonneg_right h1 (by positivity)
        _ ≤ e' / c ^ 2 := div_le_div_of_nonneg_left he' (by positivity) h2
    exact mul_le_mul (mul_le_mul hk' hg (abs_nonneg _) hA) h3 (by positivity) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add t1 t2)

/-- Quotient `u/v` against `u'/v'`. -/
theorem quot_lip {u v u' v' v₀ U eu ev : ℝ} (hv₀ : 0 < v₀) (hv : v₀ ≤ v) (hv' : v₀ ≤ v')
    (hU : |u'| ≤ U) (hu : |u - u'| ≤ eu) (hvv : |v - v'| ≤ ev) :
    |u / v - u' / v'| ≤ eu / v₀ + U * (ev / v₀ ^ 2) := by
  have h := term_lip (g := 1) (Bg := 1) hv₀ hv hv' hU (by norm_num) hu hvv
  have e : u / v - u' / v' = u * 1 * (1 / v) - u' * 1 * (1 / v') := by ring
  rw [e]
  exact h.trans (le_of_eq (by ring))

theorem avg_lip (N : ℕ) (hN : 0 < N) (a b : ℕ → ℝ) (e : ℝ) (h : ∀ j < N, |a j - b j| ≤ e) :
    |(1 / (N:ℝ)) * ∑ j ∈ Finset.range N, a j - (1 / (N:ℝ)) * ∑ j ∈ Finset.range N, b j| ≤ e := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / N)]
  have hs : |∑ j ∈ Finset.range N, (a j - b j)| ≤ ∑ j ∈ Finset.range N, e :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j hj => h j (Finset.mem_range.1 hj))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  calc 1 / (N:ℝ) * |∑ j ∈ Finset.range N, (a j - b j)| ≤ 1 / (N:ℝ) * (N * e) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = e := by rw [← mul_assoc, one_div_mul_cancel hN'.ne', one_mul]

theorem avg_abs_le (N : ℕ) (hN : 0 < N) (a : ℕ → ℝ) (e : ℝ) (h : ∀ j < N, |a j| ≤ e) :
    |(1 / (N:ℝ)) * ∑ j ∈ Finset.range N, a j| ≤ e := by
  have := avg_lip N hN a (fun _ => 0) e (fun j hj => by simpa using h j hj)
  simpa using this

theorem avg_ge_single (N : ℕ) (a : ℕ → ℝ) (h : ∀ j, 0 ≤ a j) (i : ℕ) (hi : i < N) :
    (1 / (N:ℝ)) * a i ≤ (1 / (N:ℝ)) * ∑ j ∈ Finset.range N, a j :=
  mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => h j) (Finset.mem_range.2 hi))
    (by positivity)

theorem int_lip {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (F F' : E → ℝ) (hF : Integrable F ν) (hF' : Integrable F' ν) (e : ℝ)
    (h : ∀ z, |F z - F' z| ≤ e) : |∫ z, F z ∂ν - ∫ z, F' z ∂ν| ≤ e := by
  rw [← integral_sub hF hF']
  calc |∫ z, (F z - F' z) ∂ν| ≤ ∫ z, |F z - F' z| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ z, e ∂ν := integral_mono (hF.sub hF').abs (integrable_const e) h
    _ = e := by simp

/-- **(2) Pair perturbation**: for `D` that is `Λ`-Lipschitz on `[p, q]`, the difference quotient
over `(a, b)` with `|b − a| ≥ η₀` moves by at most `4Λ hw/η₀` when both ends move by `≤ hw`. -/
theorem pair_lip (D : ℝ → ℝ) {p q Λ hw η₀ a b a' b' : ℝ}
    (hD : ∀ τ ∈ Icc p q, ∀ τ' ∈ Icc p q, |D τ - D τ'| ≤ Λ * |τ - τ'|) (hΛ : 0 ≤ Λ)
    (ha : a ∈ Icc p q) (hb : b ∈ Icc p q) (ha' : a' ∈ Icc p q) (hb' : b' ∈ Icc p q)
    (haa : |a - a'| ≤ hw) (hbb : |b - b'| ≤ hw) (hη₀ : 0 < η₀) (hη : η₀ ≤ |b - a|)
    (hne' : b' ≠ a') :
    |(D b - D a) / (b - a) - (D b' - D a') / (b' - a')| ≤ 4 * Λ * hw / η₀ := by
  have hw0 : 0 ≤ hw := (abs_nonneg _).trans haa
  have hX : 0 < |b - a| := lt_of_lt_of_le hη₀ hη
  have hX0 : b - a ≠ 0 := abs_pos.1 hX
  have hX'0 : b' - a' ≠ 0 := sub_ne_zero.2 hne'
  have hX' : 0 < |b' - a'| := abs_pos.2 hX'0
  have e1 : (D b - D a) / (b - a) - (D b' - D a') / (b' - a')
      = ((D b - D b') - (D a - D a')) / (b - a)
        + (D b' - D a') * ((b' - a') - (b - a)) / ((b - a) * (b' - a')) := by
    rw [div_add_div _ _ hX0 (mul_ne_zero hX0 hX'0), div_sub_div _ _ hX0 hX'0,
      div_eq_div_iff (mul_ne_zero hX0 hX'0) (mul_ne_zero hX0 (mul_ne_zero hX0 hX'0))]
    ring
  rw [e1]
  have h1 : |D b - D b'| ≤ Λ * hw := (hD b hb b' hb').trans (mul_le_mul_of_nonneg_left hbb hΛ)
  have h2 : |D a - D a'| ≤ Λ * hw := (hD a ha a' ha').trans (mul_le_mul_of_nonneg_left haa hΛ)
  have h3 : |D b' - D a'| ≤ Λ * |b' - a'| := hD b' hb' a' ha'
  have h4 : |(b' - a') - (b - a)| ≤ 2 * hw := by
    have : (b' - a') - (b - a) = -(b - b') + (a - a') := by ring
    rw [this]
    calc |-(b - b') + (a - a')| ≤ |-(b - b')| + |a - a'| := abs_add_le _ _
      _ = |b - b'| + |a - a'| := by rw [abs_neg]
      _ ≤ 2 * hw := by linarith
  have t1 : |((D b - D b') - (D a - D a')) / (b - a)| ≤ 2 * Λ * hw / η₀ := by
    rw [abs_div]
    have hn : |(D b - D b') - (D a - D a')| ≤ 2 * Λ * hw := by
      calc |(D b - D b') - (D a - D a')| ≤ |D b - D b'| + |D a - D a'| := abs_sub _ _
        _ ≤ 2 * Λ * hw := by linarith
    calc |(D b - D b') - (D a - D a')| / |b - a| ≤ 2 * Λ * hw / |b - a| :=
          div_le_div_of_nonneg_right hn hX.le
      _ ≤ 2 * Λ * hw / η₀ := div_le_div_of_nonneg_left (by positivity) hη₀ hη
  have t2 : |(D b' - D a') * ((b' - a') - (b - a)) / ((b - a) * (b' - a'))|
      ≤ 2 * Λ * hw / η₀ := by
    rw [abs_div, abs_mul, abs_mul]
    calc |D b' - D a'| * |(b' - a') - (b - a)| / (|b - a| * |b' - a'|)
        ≤ (Λ * |b' - a'|) * (2 * hw) / (|b - a| * |b' - a'|) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul h3 h4 (abs_nonneg _) (by positivity)
      _ = 2 * Λ * hw / |b - a| := by
          rw [div_eq_div_iff (mul_pos hX hX').ne' hX.ne']; ring
      _ ≤ 2 * Λ * hw / η₀ := div_le_div_of_nonneg_left (by positivity) hη₀ hη
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ 2 * Λ * hw / η₀ + 2 * Λ * hw / η₀ := add_le_add t1 t2
    _ = 4 * Λ * hw / η₀ := by ring

/-- **(3) Time grid**: the grid point `p + ⌊(τ − p)/hw⌋ hw` lies in `[p, τ]` within `hw` of `τ`,
and its index is at most `⌊(q − p)/hw⌋` for `τ ≤ q`. -/
theorem grid_point {p q τ hw : ℝ} (hhw : 0 < hw) (hpτ : p ≤ τ) (hτq : τ ≤ q) :
    p ≤ p + (⌊(τ - p) / hw⌋₊ : ℝ) * hw ∧ p + (⌊(τ - p) / hw⌋₊ : ℝ) * hw ≤ τ
    ∧ |τ - (p + (⌊(τ - p) / hw⌋₊ : ℝ) * hw)| ≤ hw
    ∧ ⌊(τ - p) / hw⌋₊ ≤ ⌊(q - p) / hw⌋₊ := by
  have hx : 0 ≤ (τ - p) / hw := div_nonneg (by linarith) hhw.le
  have h1 : (⌊(τ - p) / hw⌋₊ : ℝ) ≤ (τ - p) / hw := Nat.floor_le hx
  have h2 : (τ - p) / hw < ⌊(τ - p) / hw⌋₊ + 1 := Nat.lt_floor_add_one _
  have h1' : (⌊(τ - p) / hw⌋₊ : ℝ) * hw ≤ τ - p := (le_div_iff₀ hhw).1 h1
  have h2' : τ - p < ((⌊(τ - p) / hw⌋₊ : ℝ) + 1) * hw := (div_lt_iff₀ hhw).1 h2
  have h0 : (0:ℝ) ≤ (⌊(τ - p) / hw⌋₊ : ℝ) * hw := by positivity
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · rw [abs_of_nonneg (by linarith)]; nlinarith
  · exact Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hhw.le)

/-! ### (1) Time-Lipschitz bounds of the averages -/

section Avg

variable {E : Type*} [MeasurableSpace E] {Ω : Type*}

theorem sampAvg_tlip (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K K' : E → E → ℝ) (e : ℝ)
    (hK : ∀ x y, |K x y - K' x y| ≤ e) (j : ℕ) (ω : Ω) :
    |sampAvg X N K j ω - sampAvg X N K' j ω| ≤ e := by
  unfold sampAvg; exact avg_lip N hN _ _ e (fun l _ => hK _ _)

theorem sampW_tlip (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K K' g : E → E → ℝ) {A Bg c e : ℝ}
    (hc : 0 < c) (hK : ∀ x y, |K x y - K' x y| ≤ e) (hK' : ∀ x y, |K' x y| ≤ A)
    (hg : ∀ x y, |g x y| ≤ Bg) (ω : Ω) (hq : ∀ j < N, c ≤ sampAvg X N K j ω)
    (hq' : ∀ j < N, c ≤ sampAvg X N K' j ω) (i : ℕ) :
    |sampW X N K g i ω - sampW X N K' g i ω| ≤ e * Bg * (1 / c) + A * Bg * (e / c ^ 2) := by
  unfold sampW avgN
  exact avg_lip N hN _ _ _ (fun j hj => term_lip hc (hq j hj) (hq' j hj) (hK' _ _) (hg _ _)
    (hK _ _) (sampAvg_tlip X N hN K K' e hK j ω))

theorem sampW_bd (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K g : E → E → ℝ) {A Bg c : ℝ}
    (hc : 0 < c) (hKb : ∀ x y, |K x y| ≤ A) (hg : ∀ x y, |g x y| ≤ Bg) (ω : Ω)
    (hq : ∀ j < N, c ≤ sampAvg X N K j ω) (i : ℕ) :
    |sampW X N K g i ω| ≤ A * Bg * (1 / c) := by
  unfold sampW avgN
  refine avg_abs_le N hN _ _ (fun j hj => ?_)
  have hA : 0 ≤ A := (abs_nonneg _).trans (hKb (X i ω) (X i ω))
  have hBg : 0 ≤ Bg := (abs_nonneg _).trans (hg (X i ω) (X i ω))
  have hq0 : 0 < sampAvg X N K j ω := lt_of_lt_of_le hc (hq j hj)
  rw [abs_mul, abs_mul, abs_of_pos (one_div_pos.2 hq0)]
  exact mul_le_mul (mul_le_mul (hKb _ _) (hg _ _) (abs_nonneg _) hA)
    (one_div_le_one_div_of_le hc (hq j hj)) (one_div_pos.2 hq0).le (mul_nonneg hA hBg)

theorem sampAvg_ge (X : ℕ → Ω → E) (N : ℕ) (K : E → E → ℝ) {h₀ : ℝ}
    (hK0 : ∀ x y, 0 ≤ K x y) (hd : ∀ x, h₀ ≤ K x x) (ω : Ω) (j : ℕ) (hj : j < N) :
    h₀ / N ≤ sampAvg X N K j ω := by
  unfold sampAvg
  have h := avg_ge_single N (fun l => K (X j ω) (X l ω)) (fun l => hK0 _ _) j hj
  have h2 : h₀ / N ≤ 1 / (N:ℝ) * K (X j ω) (X j ω) := by
    rw [show h₀ / (N:ℝ) = 1 / (N:ℝ) * h₀ by ring]
    exact mul_le_mul_of_nonneg_left (hd _) (by positivity)
  exact h2.trans h

theorem sampAvg_le (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K : E → E → ℝ) {A : ℝ}
    (hKb : ∀ x y, |K x y| ≤ A) (ω : Ω) (j : ℕ) : sampAvg X N K j ω ≤ A := by
  unfold sampAvg
  exact (le_abs_self _).trans (avg_abs_le N hN _ _ (fun l _ => hKb _ _))

theorem sampW_one_ge (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K : E → E → ℝ) {A h₀ : ℝ}
    (hh₀ : 0 < h₀) (hK0 : ∀ x y, 0 ≤ K x y) (hKb : ∀ x y, |K x y| ≤ A)
    (hd : ∀ x, h₀ ≤ K x x) (ω : Ω) (i : ℕ) (hi : i < N) :
    h₀ / (N * A) ≤ sampW X N K (fun _ _ => 1) i ω := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hq : ∀ j < N, 0 < sampAvg X N K j ω := fun j hj =>
    lt_of_lt_of_le (by positivity) (sampAvg_ge X N K hK0 hd ω j hj)
  have hqA := sampAvg_le X N hN K hKb ω i
  have hA : 0 < A := lt_of_lt_of_le (hq i hi) hqA
  unfold sampW avgN
  have h := avg_ge_single N
    (fun j => if j < N then K (X i ω) (X j ω) * 1 * (1 / sampAvg X N K j ω) else 0)
    (fun j => by
      dsimp only
      split_ifs with hj
      · have := hq j hj; have := hK0 (X i ω) (X j ω); positivity
      · exact le_rfl) i hi
  have hsum : ∑ j ∈ Finset.range N,
        (if j < N then K (X i ω) (X j ω) * 1 * (1 / sampAvg X N K j ω) else 0)
      = ∑ j ∈ Finset.range N, K (X i ω) (X j ω) * 1 * (1 / sampAvg X N K j ω) :=
    Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.1 hj)]
  dsimp only at h
  rw [hsum, if_pos hi] at h
  refine le_trans ?_ h
  have hterm : h₀ / A ≤ K (X i ω) (X i ω) * 1 * (1 / sampAvg X N K i ω) := by
    rw [mul_one, mul_one_div, div_le_div_iff₀ hA (hq i hi)]
    exact mul_le_mul (hd _) hqA (hq i hi).le (hK0 _ _)
  calc h₀ / (N * A) = 1 / (N:ℝ) * (h₀ / A) := by rw [div_mul_div_comm, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by positivity)

variable (m : Measure E) [IsProbabilityMeasure m]

theorem popAvg_tlip (K K' : E → E → ℝ) {A e : ℝ}
    (hKm : Measurable fun p : E × E => K p.1 p.2) (hK'm : Measurable fun p : E × E => K' p.1 p.2)
    (hKb : ∀ x y, |K x y| ≤ A) (hK'b : ∀ x y, |K' x y| ≤ A)
    (hK : ∀ x y, |K x y - K' x y| ≤ e) (y : E) :
    |popAvg m K y - popAvg m K' y| ≤ e :=
  int_lip m _ _ (integrable_of_bound m K hKm hKb y) (integrable_of_bound m K' hK'm hK'b y) e
    (fun w => hK y w)

theorem wKer_integrable (K g : E → E → ℝ) {A Bg c : ℝ} (hc : 0 < c)
    (hKm : Measurable fun p : E × E => K p.1 p.2) (hgm : Measurable fun p : E × E => g p.1 p.2)
    (hKb : ∀ x y, |K x y| ≤ A) (hg : ∀ x y, |g x y| ≤ Bg) (hq : ∀ y, c ≤ popAvg m K y)
    (x : E) : Integrable (fun z => wKer m K g x z) m := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hKb x x)
  have hBg : 0 ≤ Bg := (abs_nonneg _).trans (hg x x)
  refine bdd_integrable m _ (((hKm.mul hgm).mul (inv_pop_meas (m := m) K hKm)).comp
    (measurable_const.prodMk measurable_id)) (A * Bg * (1 / c)) (fun z => ?_)
  show |K x z * g x z * (1 / popAvg m K z)| ≤ A * Bg * (1 / c)
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hKb x z) (hg x z) (abs_nonneg _) hA) (inv_pop_bd K hc hq z)
    (abs_nonneg _) (mul_nonneg hA hBg)

theorem popW_tlip (K K' g : E → E → ℝ) {A Bg c e : ℝ} (hc : 0 < c)
    (hKm : Measurable fun p : E × E => K p.1 p.2) (hK'm : Measurable fun p : E × E => K' p.1 p.2)
    (hgm : Measurable fun p : E × E => g p.1 p.2)
    (hK : ∀ x y, |K x y - K' x y| ≤ e) (hKb : ∀ x y, |K x y| ≤ A) (hK'b : ∀ x y, |K' x y| ≤ A)
    (hg : ∀ x y, |g x y| ≤ Bg) (hq : ∀ y, c ≤ popAvg m K y) (hq' : ∀ y, c ≤ popAvg m K' y)
    (x : E) :
    |popW m K g x - popW m K' g x| ≤ e * Bg * (1 / c) + A * Bg * (e / c ^ 2) :=
  int_lip m _ _ (wKer_integrable m K g hc hKm hgm hKb hg hq x)
    (wKer_integrable m K' g hc hK'm hgm hK'b hg hq' x) _
    (fun z => term_lip hc (hq z) (hq' z) (hK'b x z) (hg x z) (hK x z)
      (popAvg_tlip m K K' hKm hK'm hKb hK'b hK z))

theorem popW_bd (K g : E → E → ℝ) {A Bg c : ℝ} (hc : 0 < c)
    (hKm : Measurable fun p : E × E => K p.1 p.2) (hgm : Measurable fun p : E × E => g p.1 p.2)
    (hKb : ∀ x y, |K x y| ≤ A) (hg : ∀ x y, |g x y| ≤ Bg) (hq : ∀ y, c ≤ popAvg m K y)
    (x : E) : |popW m K g x| ≤ A * Bg * (1 / c) := by
  have hA : 0 ≤ A := (abs_nonneg _).trans (hKb x x)
  have hBg : 0 ≤ Bg := (abs_nonneg _).trans (hg x x)
  have h := int_lip m (fun z => wKer m K g x z) (fun _ => (0:ℝ))
    (wKer_integrable m K g hc hKm hgm hKb hg hq x) (integrable_const 0) (A * Bg * (1 / c))
    (fun z => by
      show |K x z * g x z * (1 / popAvg m K z) - 0| ≤ A * Bg * (1 / c)
      rw [sub_zero, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hKb x z) (hg x z) (abs_nonneg _) hA) (inv_pop_bd K hc hq z)
        (abs_nonneg _) (mul_nonneg hA hBg))
  simpa using h

end Avg

/-- The Lipschitz factor of one quotient `𝒩/𝒟` for a kernel step `e`. -/
def lrE (e A Bg c v : ℝ) : ℝ :=
  (e * Bg * (1 / c) + A * Bg * (e / c ^ 2)) / v
    + (A * Bg * (1 / c)) * ((e * 1 * (1 / c) + A * 1 * (e / c ^ 2)) / v ^ 2)

theorem lrE_mul (ℓ δ A Bg c v : ℝ) : lrE (ℓ * δ) A Bg c v = lrE ℓ A Bg c v * δ := by
  unfold lrE; ring

theorem lrE_nonneg {ℓ A Bg c v : ℝ} (hℓ : 0 ≤ ℓ) (hA : 0 ≤ A) (hBg : 0 ≤ Bg) (hc : 0 < c)
    (hv : 0 < v) : 0 ≤ lrE ℓ A Bg c v := by
  unfold lrE; positivity

/-- **(1) Time-Lipschitz bound of `D = 𝒩_N/𝒟_N − 𝒩/𝒟`** for two kernels `K`, `K'` with
`|K − K'| ≤ e` (deterministic, for one sample point `i` and one `ω`). -/
theorem D_lip {E : Type*} [MeasurableSpace E] (m : Measure E) [IsProbabilityMeasure m]
    {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (K K' g : E → E → ℝ) (i : ℕ) (ω : Ω)
    {A Bg cs vs cp vp e : ℝ} (hcs : 0 < cs) (hcp : 0 < cp) (hvs : 0 < vs) (hvp : 0 < vp)
    (hKm : Measurable fun p : E × E => K p.1 p.2) (hK'm : Measurable fun p : E × E => K' p.1 p.2)
    (hgm : Measurable fun p : E × E => g p.1 p.2)
    (hK : ∀ x y, |K x y - K' x y| ≤ e) (hKb : ∀ x y, |K x y| ≤ A) (hK'b : ∀ x y, |K' x y| ≤ A)
    (hg : ∀ x y, |g x y| ≤ Bg)
    (hqs : ∀ j < N, cs ≤ sampAvg X N K j ω) (hqs' : ∀ j < N, cs ≤ sampAvg X N K' j ω)
    (hqp : ∀ y, cp ≤ popAvg m K y) (hqp' : ∀ y, cp ≤ popAvg m K' y)
    (hws : vs ≤ sampW X N K (fun _ _ => 1) i ω) (hws' : vs ≤ sampW X N K' (fun _ _ => 1) i ω)
    (hwp : vp ≤ popW m K (fun _ _ => 1) (X i ω))
    (hwp' : vp ≤ popW m K' (fun _ _ => 1) (X i ω)) :
    |(sampW X N K g i ω / sampW X N K (fun _ _ => 1) i ω
        - popW m K g (X i ω) / popW m K (fun _ _ => 1) (X i ω))
      - (sampW X N K' g i ω / sampW X N K' (fun _ _ => 1) i ω
        - popW m K' g (X i ω) / popW m K' (fun _ _ => 1) (X i ω))|
      ≤ lrE e A Bg cs vs + lrE e A Bg cp vp := by
  have h1b : ∀ x y : E, |(fun _ _ => (1:ℝ)) x y| ≤ 1 := fun x y => by simp
  have hs := quot_lip hvs hws hws' (sampW_bd X N hN K' g hcs hK'b hg ω hqs' i)
    (sampW_tlip X N hN K K' g hcs hK hK'b hg ω hqs hqs' i)
    (sampW_tlip X N hN K K' (fun _ _ => 1) hcs hK hK'b h1b ω hqs hqs' i)
  have hp := quot_lip hvp hwp hwp' (popW_bd m K' g hcp hK'm hgm hK'b hg hqp' (X i ω))
    (popW_tlip m K K' g hcp hKm hK'm hgm hK hKb hK'b hg hqp hqp' (X i ω))
    (popW_tlip m K K' (fun _ _ => 1) hcp hKm hK'm measurable_const hK hKb hK'b h1b hqp hqp'
      (X i ω))
  have e1 : (sampW X N K g i ω / sampW X N K (fun _ _ => 1) i ω
        - popW m K g (X i ω) / popW m K (fun _ _ => 1) (X i ω))
      - (sampW X N K' g i ω / sampW X N K' (fun _ _ => 1) i ω
        - popW m K' g (X i ω) / popW m K' (fun _ _ => 1) (X i ω))
      = (sampW X N K g i ω / sampW X N K (fun _ _ => 1) i ω
          - sampW X N K' g i ω / sampW X N K' (fun _ _ => 1) i ω)
        - (popW m K g (X i ω) / popW m K (fun _ _ => 1) (X i ω)
          - popW m K' g (X i ω) / popW m K' (fun _ _ => 1) (X i ω)) := by ring
  rw [e1]
  refine (abs_sub _ _).trans (add_le_add (hs.trans (le_of_eq ?_)) (hp.trans (le_of_eq ?_))) <;>
    unfold lrE <;> ring

/-- The combined time-Lipschitz constant of `D` (sample with `c = h₀/N`, `v = h₀/(N A)`;
population with `c = c_q h₀ ξⁿ`, `v = c/A`), for the kernel step `2κA` and `B_g = 2B_f`. -/
def gridLam (κ A Bf h₀ cq ξ : ℝ) (N n : ℕ) : ℝ :=
  lrE (2 * κ * A) A (2 * Bf) (h₀ / N) (h₀ / (N * A))
    + lrE (2 * κ * A) A (2 * Bf) (cq * h₀ * ξ ^ n) (cq * h₀ * ξ ^ n / A)

section GeomGrid

open Bundle Manifold CTG.ManifoldDistance CTG.ManifoldVolume CTG.NPointGeom
open scoped Manifold ENNReal

universe u

variable {n : ℕ} {M : Type*} [EMetricSpace M] [ChartedSpace (Fin n → ℝ) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M]
  [IsContinuousRiemannianBundle (Fin n → ℝ) (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsRiemannianManifold 𝓘(ℝ, Fin n → ℝ) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [PreconnectedSpace M]

theorem tdist_self {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ τ : ℝ} (ha₀ : a₀ ∈ s)
    (hτ : τ ∈ s) (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x))) (x : M) :
    G.dist x x τ = 0 := by
  obtain ⟨C, hC, hle⟩ := G.redist_le_edist ha₀ hτ hcont
  have h := hle x x
  rw [edist_self, mul_zero] at h
  have h0 : (letI := G.norms τ; Manifold.riemannianEDist 𝓘(ℝ, Fin n → ℝ) x x) = 0 :=
    le_antisymm h (zero_le _)
  exact (congrArg ENNReal.toReal h0).trans ENNReal.toReal_zero

/-- Kernel step in time: `|K^τ − K^{τ'}| ≤ 2κA|τ − τ'|` on `[p, q] ⊆ s` with `κ(q − p) ≤ 1`. -/
theorem kern_tlip {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ p q : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (hpq : Icc p q ⊆ s) (hκ : G.κ * (q - p) ≤ 1)
    (h h' : ℝ → ℝ) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    {τ τ' : ℝ} (hτ : τ ∈ Icc p q) (hτ' : τ' ∈ Icc p q) (x y : M) :
    |kern G h ξ τ x y - kern G h ξ τ' x y| ≤ 2 * G.κ * A * |τ - τ'| := by
  by_cases hne : τ = τ'
  · subst hne; simp only [sub_self, abs_zero, mul_zero, le_refl]
  · have hd : |τ - τ'| ≤ q - p := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]
    have hab : G.κ * |τ - τ'| ≤ 1 :=
      (mul_le_mul_of_nonneg_left hd G.κ_nonneg).trans hκ
    have h1 := kernInc_abs_le G ha₀ hcont (hpq hτ') (hpq hτ) hab hne h h' A ξ hA hξ hder hbd x y
    unfold kernInc at h1
    rw [abs_div, div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 hne))] at h1
    exact h1

/-- **(5) All time pairs of a window with `|b − a| ≥ η₀` on one event.**  Reference time
`a₀ ∈ s` (metric continuous in the base point at `a₀`); window `[p, q] ⊆ s` with `κ|τ − a₀| ≤ 1` on
it and `κ(q − p) ≤ 1` (HYPOTHESES); sampling law `m₀ μH ≤ m ≤ m₁ μH`; `s₀ > 0`.  There are
`A_m, r₀, c_q, ξ₀` depending only on `G, a₀, m₀, m₁, s₀` such that for every sample, `N ≥ 1`,
`ξ ≤ ξ₀`, profile as in `npoint_step5_lip_geom_log`, measurable `f` with `|f| ≤ B_f` and
`Lip`-Lipschitz in `d_{a₀}` (HYPOTHESES), `c_h > 0`, `η₀ > 0`, grid width `0 < hw` with `2hw < η₀`,
`L ≥ 1` and `92416 Λ¹⁴ L ≤ N ξⁿ` (`Λ = lipLam n A_m r₀ A κ (c_q h₀) (e·Lip)`): with probability at
least `1 − (G+1)²·15N·2e^{−L}`, `G = ⌊(q − p)/hw⌋`, for ALL `a, b ∈ [p, q]` with `|b − a| ≥ η₀` and all
`i < N`: `|Δ_{b−a}(L_N f)(i) − Δ_{b−a}(L_ξ f)(X_i)| ≤ (2/c_h)·3 660 000 Λ²⁰ √(L/(N ξⁿ))/ξ
+ 4 Λ_D hw/η₀/(c_h ξ²/2)` with the explicit `Λ_D = gridLam κ A B_f h₀ c_q ξ N n` (crude; contains
powers of `N` and of `1/(c_q h₀ ξⁿ)`). -/
theorem npoint_grid {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] (m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁)
    (hlow : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ξ₀ ≤ 1 ∧
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 0 < N → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (h h' : ℝ → ℝ) (A h₀ : ℝ), 0 < A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
        (∀ t, 0 ≤ h t) → 0 < h₀ → (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) →
      ∀ (f : M → ℝ), Measurable f → ∀ Bf : ℝ, 0 ≤ Bf → (∀ x, |f x| ≤ Bf) → ∀ Lip : ℝ,
        0 ≤ Lip → (∀ x y, |f y - f x| ≤ Lip * G.dist x y a₀) →
      ∀ ch : ℝ, 0 < ch →
      ∀ p q : ℝ, p ≤ q → Icc p q ⊆ s → (∀ τ ∈ Icc p q, G.κ * |τ - a₀| ≤ 1) → G.κ * (q - p) ≤ 1 →
      ∀ η₀ hw : ℝ, 0 < η₀ → 0 < hw → 2 * hw < η₀ →
      ∀ L : ℝ, 1 ≤ L →
      92416 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 14 * L ≤ N * ξ ^ n →
      μ.real {ω | ∃ a ∈ Icc p q, ∃ b ∈ Icc p q, η₀ ≤ |b - a| ∧ ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (L / (N * ξ ^ n))) / ξ
          + 4 * gridLam G.κ A Bf h₀ cq ξ N n * hw / η₀ / (ch * ξ ^ 2 / 2)
        < |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω| / (ch * ξ ^ 2 / 2)}
        ≤ ((⌊(q - p) / hw⌋₊ : ℝ) + 1) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
  obtain ⟨Am, hAm, r₀, hr₀, hg⟩ := growth_window G ha₀ hcont m m₁ hm₁ hup
  obtain ⟨cq, hcq, ξ₀, hξ₀, hq⟩ := popNorm_window G ha₀ hcont m m₀ hm₀ hlow s₀ hs₀
  refine ⟨Am, hAm, r₀, hr₀, cq, hcq, min ξ₀ 1, lt_min hξ₀ one_pos, min_le_right _ _, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Bf hBf0 hBf Lip hLip hL ch hch p q hpq' hpq hwin hκ η₀ hw hη₀ hhw hη L hL1 hNL
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have hξ1 : ξ ≤ 1 := hξξ₀.trans (min_le_right _ _)
  have hξ0 : ξ ≤ ξ₀ := hξξ₀.trans (min_le_left _ _)
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  set Gn := ⌊(q - p) / hw⌋₊ with hGn
  set Kmain := 2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
    * Real.sqrt (L / (N * ξ ^ n))) / ξ with hKmain
  set Dn := ch * ξ ^ 2 / 2 with hDn
  have hDn0 : 0 < Dn := by positivity
  set ΛD := gridLam G.κ A Bf h₀ cq ξ N n with hΛD
  -- deterministic facts on the kernels
  have hK0 : ∀ τ x y, 0 ≤ kern G h ξ τ x y := fun τ x y => hh0 _
  have hKb : ∀ τ x y, |kern G h ξ τ x y| ≤ A := fun τ x y => kern_abs_le G h A ξ τ hξ hh hA.le x y
  have hKd : ∀ τ ∈ Icc p q, ∀ x, h₀ ≤ kern G h ξ τ x x := fun τ hτ x => by
    show h₀ ≤ h (G.dist x x τ / ξ)
    rw [tdist_self G ha₀ (hpq hτ) hcont, zero_div]; exact hlo 0 le_rfl hs₀.le
  have hgb : ∀ x y : M, |(fun x y => f y - f x) x y| ≤ 2 * Bf := fun x y => by
    show |f y - f x| ≤ 2 * Bf
    calc |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
      _ ≤ 2 * Bf := by linarith [hBf x, hBf y]
  have hgm : Measurable fun p : M × M => (fun x y => f y - f x) p.1 p.2 :=
    (hf.comp measurable_snd).sub (hf.comp measurable_fst)
  have hcp : 0 < cq * h₀ * ξ ^ n := by positivity
  have hpop : ∀ τ ∈ Icc p q, ∀ y, cq * h₀ * ξ ^ n ≤ popAvg m (kern G h ξ τ) y := fun τ hτ y =>
    hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo τ (hpq hτ) (hwin τ hτ) ξ hξ hξ0 y
  have hpopW : ∀ τ ∈ Icc p q, ∀ x,
      cq * h₀ * ξ ^ n / A ≤ popW m (kern G h ξ τ) (fun _ _ => 1) x := fun τ hτ x => by
    have GK := good_kern G ha₀ (hpq hτ) hcont m n Am r₀ ξ hAm hr₀ hξ
      (hg τ (hpq hτ) (hwin τ hτ)) h hhc A hA.le hh
    refine popW_one_ge' _ GK hcp (hK0 τ) (hpop τ hτ) (fun x => ?_) x
    calc ∫ z, |kern G h ξ τ x z| ∂m ≤ ∫ z, A ∂m :=
          integral_mono ((integrable_of_bound m _ GK.meas (hKb τ) x).abs) (integrable_const A)
            (fun z => hKb τ x z)
      _ = A := by simp
  -- the function `D` for one `ω`, `i`, and its time-Lipschitz bound
  have hDlip : ∀ (ω : Ω) (i : ℕ), i < N → ∀ τ ∈ Icc p q, ∀ τ' ∈ Icc p q,
      |(sampW X N (kern G h ξ τ) (fun x y => f y - f x) i ω
          / sampW X N (kern G h ξ τ) (fun _ _ => 1) i ω
        - popW m (kern G h ξ τ) (fun x y => f y - f x) (X i ω)
          / popW m (kern G h ξ τ) (fun _ _ => 1) (X i ω))
      - (sampW X N (kern G h ξ τ') (fun x y => f y - f x) i ω
          / sampW X N (kern G h ξ τ') (fun _ _ => 1) i ω
        - popW m (kern G h ξ τ') (fun x y => f y - f x) (X i ω)
          / popW m (kern G h ξ τ') (fun _ _ => 1) (X i ω))| ≤ ΛD * |τ - τ'| := by
    intro ω i hi τ hτ τ' hτ'
    have hD := D_lip m X N hN (kern G h ξ τ) (kern G h ξ τ') (fun x y => f y - f x) i ω
      (A := A) (Bg := 2 * Bf) (by positivity : (0:ℝ) < h₀ / N) hcp
      (by positivity : (0:ℝ) < h₀ / (N * A)) (by positivity : (0:ℝ) < cq * h₀ * ξ ^ n / A)
      (kern_measurable G ha₀ (hpq hτ) hcont h hhc ξ)
      (kern_measurable G ha₀ (hpq hτ') hcont h hhc ξ) hgm
      (kern_tlip G ha₀ hcont hpq hκ h h' A ξ hA.le hξ hder hbd hτ hτ') (hKb τ) (hKb τ') hgb
      (fun j hj => sampAvg_ge X N _ (hK0 τ) (hKd τ hτ) ω j hj)
      (fun j hj => sampAvg_ge X N _ (hK0 τ') (hKd τ' hτ') ω j hj)
      (hpop τ hτ) (hpop τ' hτ')
      (sampW_one_ge X N hN _ hh₀ (hK0 τ) (hKb τ) (hKd τ hτ) ω i hi)
      (sampW_one_ge X N hN _ hh₀ (hK0 τ') (hKb τ') (hKd τ' hτ') ω i hi)
      (hpopW τ hτ _) (hpopW τ' hτ' _)
    refine hD.trans (le_of_eq ?_)
    rw [hΛD]; unfold gridLam lrE; ring
  have hΛD0 : 0 ≤ ΛD := by
    rw [hΛD]; unfold gridLam
    have hκ0 := G.κ_nonneg
    exact add_nonneg (lrE_nonneg (by positivity) hA.le (by positivity) (by positivity)
      (by positivity)) (lrE_nonneg (by positivity) hA.le (by positivity) hcp (by positivity))
  -- the grid events
  set gp : ℕ → ℝ := fun k => p + (k : ℝ) * hw with hgp
  set F := (Finset.range (Gn + 1) ×ˢ Finset.range (Gn + 1)).filter (fun kl => kl.1 ≠ kl.2)
    with hF
  obtain ⟨S, hS⟩ : ∃ S : ℕ × ℕ → Set Ω, ∀ kl, S kl = {ω | ∃ i < N,
      Kmain < |qDiff X N m (kern G h ξ (gp kl.1)) (kern G h ξ (gp kl.2)) f
        (gp kl.2 - gp kl.1) i ω| / Dn} := ⟨_, fun kl => rfl⟩
  have hgrid : ∀ k ≤ Gn, gp k ∈ Icc p q := fun k hk => by
    have h1 : (k : ℝ) ≤ Gn := by exact_mod_cast hk
    have h2 : (Gn : ℝ) ≤ (q - p) / hw := Nat.floor_le (div_nonneg (by linarith) hhw.le)
    have h3 : (k : ℝ) * hw ≤ q - p := by
      have := (le_div_iff₀ hhw).1 (h1.trans h2); linarith
    have h4 : (0:ℝ) ≤ (k : ℝ) * hw := by positivity
    exact ⟨by simp only [hgp]; linarith, by simp only [hgp]; linarith⟩
  have hSj : ∀ kl ∈ F, μ.real (S kl) ≤ 15 * (N * (2 * Real.exp (-L))) := by
    intro kl hkl
    rw [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hkl
    obtain ⟨⟨hk, hl⟩, hne⟩ := hkl
    have hka := hgrid kl.1 (Nat.lt_succ_iff.1 hk)
    have hlb := hgrid kl.2 (Nat.lt_succ_iff.1 hl)
    have hne' : gp kl.2 ≠ gp kl.1 := by
      simp only [hgp]
      intro he
      have : (kl.2 : ℝ) = kl.1 := by
        have := mul_right_cancel₀ hhw.ne' (by linarith : (kl.2 : ℝ) * hw = kl.1 * hw)
        exact this
      exact hne (by exact_mod_cast this.symm)
    have hκab : G.κ * |gp kl.2 - gp kl.1| ≤ 1 := by
      have hd : |gp kl.2 - gp kl.1| ≤ q - p := by
        rw [abs_le]; constructor <;> linarith [hka.1, hka.2, hlb.1, hlb.2]
      exact (mul_le_mul_of_nonneg_left hd G.κ_nonneg).trans hκ
    rw [hS]
    exact npoint_step5_lip_norm G ha₀ hcont (hpq hka) (hpq hlb) hκab hne' m X h_indep hX hlaw N
      hN n Am r₀ ξ hAm hr₀ hξ hξ1 (hg _ (hpq hka) (hwin _ hka)) (hg _ (hpq hlb) (hwin _ hlb))
      h h' A hA hder hbd hh hh0 f hf (Lip * Real.exp 1) (by positivity)
      (lip_window G ha₀ hcont f Lip hLip hL _ (hpq hka) (hwin _ hka))
      (lip_window G ha₀ hcont f Lip hLip hL _ (hpq hlb) (hwin _ hlb)) (cq * h₀) (by positivity)
      (fun y => hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo _ (hpq hka) (hwin _ hka) ξ hξ hξ0 y)
      (fun y => hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo _ (hpq hlb) (hwin _ hlb) ξ hξ hξ0 y)
      L hL1 hNL ch hch
  -- deterministic inclusion
  have hsub : {ω | ∃ a ∈ Icc p q, ∃ b ∈ Icc p q, η₀ ≤ |b - a| ∧ ∃ i < N,
        Kmain + 4 * ΛD * hw / η₀ / Dn
        < |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω| / Dn}
      ⊆ ⋃ kl ∈ F, S kl := by
    rintro ω ⟨a, ha, b, hb, hab, i, hi, hlt⟩
    obtain ⟨-, -, hka, hkG⟩ := grid_point (q := q) hhw ha.1 ha.2
    obtain ⟨-, -, hlb, hlG⟩ := grid_point (q := q) hhw hb.1 hb.2
    set k := ⌊(a - p) / hw⌋₊ with hk
    set l := ⌊(b - p) / hw⌋₊ with hl
    have hka' : gp k ∈ Icc p q := hgrid k hkG
    have hlb' : gp l ∈ Icc p q := hgrid l hlG
    have haa : |a - gp k| ≤ hw := hka
    have hbb : |b - gp l| ≤ hw := hlb
    have hne' : gp l ≠ gp k := by
      intro he
      have : |b - a| ≤ 2 * hw := by
        have : b - a = (b - gp l) - (a - gp k) := by rw [he]; ring
        rw [this]
        calc |(b - gp l) - (a - gp k)| ≤ |b - gp l| + |a - gp k| := abs_sub _ _
          _ ≤ 2 * hw := by linarith
      linarith
    have hkl : (k, l) ∈ F := by
      rw [hF, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      refine ⟨⟨Nat.lt_succ_of_le hkG, Nat.lt_succ_of_le hlG⟩, ?_⟩
      intro hkl'
      apply hne'
      have hkl2 : k = l := hkl'
      rw [hkl2]
    refine mem_iUnion₂.2 ⟨(k, l), hkl, ?_⟩
    rw [hS]
    refine ⟨i, hi, ?_⟩
    obtain ⟨Df, hDf⟩ : ∃ Df : ℝ → ℝ, ∀ τ, Df τ =
        sampW X N (kern G h ξ τ) (fun x y => f y - f x) i ω
          / sampW X N (kern G h ξ τ) (fun _ _ => 1) i ω
        - popW m (kern G h ξ τ) (fun x y => f y - f x) (X i ω)
          / popW m (kern G h ξ τ) (fun _ _ => 1) (X i ω) := ⟨_, fun τ => rfl⟩
    have hqD : ∀ a' b', qDiff X N m (kern G h ξ a') (kern G h ξ b') f (b' - a') i ω
        = (Df b' - Df a') / (b' - a') := fun a' b' => by
      rw [hDf, hDf]; unfold qDiff; ring
    have hDl : ∀ τ ∈ Icc p q, ∀ τ' ∈ Icc p q, |Df τ - Df τ'| ≤ ΛD * |τ - τ'| :=
      fun τ hτ τ' hτ' => by rw [hDf, hDf]; exact hDlip ω i hi τ hτ τ' hτ'
    have hpl := pair_lip Df hDl hΛD0 ha hb hka' hlb' haa hbb hη₀ hab hne'
    rw [← hqD, ← hqD] at hpl
    have hle : |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω|
        ≤ |qDiff X N m (kern G h ξ (gp k)) (kern G h ξ (gp l)) f (gp l - gp k) i ω|
          + 4 * ΛD * hw / η₀ := by
      have := abs_sub_abs_le_abs_sub
        (qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω)
        (qDiff X N m (kern G h ξ (gp k)) (kern G h ξ (gp l)) f (gp l - gp k) i ω)
      linarith
    have hle' : |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω| / Dn
        ≤ |qDiff X N m (kern G h ξ (gp k)) (kern G h ξ (gp l)) f (gp l - gp k) i ω| / Dn
          + 4 * ΛD * hw / η₀ / Dn := by
      rw [← add_div]; exact div_le_div_of_nonneg_right hle hDn0.le
    show Kmain < |qDiff X N m (kern G h ξ (gp k)) (kern G h ξ (gp l)) f
        (gp l - gp k) i ω| / Dn
    linarith
  calc μ.real _ ≤ μ.real (⋃ kl ∈ F, S kl) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ kl ∈ F, μ.real (S kl) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ kl ∈ F, 15 * (N * (2 * Real.exp (-L))) := Finset.sum_le_sum hSj
    _ = F.card * (15 * (N * (2 * Real.exp (-L)))) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Gn : ℝ) + 1) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h1 : F.card ≤ (Gn + 1) * (Gn + 1) := by
          rw [hF]
          exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_product, Finset.card_range])
        have h2 : (F.card : ℝ) ≤ ((Gn + 1) * (Gn + 1) : ℕ) := by exact_mod_cast h1
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h2
        nlinarith

theorem npoint_grid_log {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a₀ : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] (m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁)
    (hlow : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ξ₀ ≤ 1 ∧
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 0 < N → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (h h' : ℝ → ℝ) (A h₀ : ℝ), 0 < A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
        (∀ t, 0 ≤ h t) → 0 < h₀ → (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) →
      ∀ (f : M → ℝ), Measurable f → ∀ Bf : ℝ, 0 ≤ Bf → (∀ x, |f x| ≤ Bf) → ∀ Lip : ℝ,
        0 ≤ Lip → (∀ x y, |f y - f x| ≤ Lip * G.dist x y a₀) →
      ∀ ch : ℝ, 0 < ch →
      ∀ p q : ℝ, p ≤ q → Icc p q ⊆ s → (∀ τ ∈ Icc p q, G.κ * |τ - a₀| ≤ 1) → G.κ * (q - p) ≤ 1 →
      ∀ η₀ hw : ℝ, 0 < η₀ → 0 < hw → 2 * hw < η₀ →
      92416 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 14
        * Real.log (30 * ((⌊(q - p) / hw⌋₊ : ℝ) + 1) ^ 2 * (N : ℝ) ^ 3) ≤ N * ξ ^ n →
      μ.real {ω | ∃ a ∈ Icc p q, ∃ b ∈ Icc p q, η₀ ≤ |b - a| ∧ ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (Real.log (30 * ((⌊(q - p) / hw⌋₊ : ℝ) + 1) ^ 2 * (N : ℝ) ^ 3)
            / (N * ξ ^ n))) / ξ
          + 4 * gridLam G.κ A Bf h₀ cq ξ N n * hw / η₀ / (ch * ξ ^ 2 / 2)
        < |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω| / (ch * ξ ^ 2 / 2)}
        ≤ 1 / (N : ℝ) ^ 2 := by
  obtain ⟨Am, hAm, r₀, hr₀, cq, hcq, ξ₀, hξ₀, hξ₀1, H⟩ :=
    npoint_grid (M := M) G ha₀ hcont m m₀ m₁ hm₀ hm₁ hlow hup s₀ hs₀
  refine ⟨Am, hAm, r₀, hr₀, cq, hcq, ξ₀, hξ₀, hξ₀1, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Bf hBf0 hBf Lip hLip hL ch hch p q hpq' hpq hwin hκ η₀ hw hη₀ hhw hη hNL
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hG1 : 1 ≤ (⌊(q - p) / hw⌋₊ : ℝ) + 1 := by
    have : (0:ℝ) ≤ (⌊(q - p) / hw⌋₊ : ℝ) := by positivity
    linarith
  have hy : 0 < 30 * ((⌊(q - p) / hw⌋₊ : ℝ) + 1) ^ 2 * (N : ℝ) ^ 3 := by positivity
  have hL1 : 1 ≤ Real.log (30 * ((⌊(q - p) / hw⌋₊ : ℝ) + 1) ^ 2 * (N : ℝ) ^ 3) := by
    rw [Real.le_log_iff_exp_le hy]
    have h1 : (1:ℝ) ≤ ((⌊(q - p) / hw⌋₊ : ℝ) + 1) ^ 2 * (N : ℝ) ^ 3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hG1)
      (one_le_pow₀ hN')
    have h2 : Real.exp 1 ≤ 30 := by
      have := Real.exp_one_lt_d9; linarith
    nlinarith
  have hP := H Ω μ X h_indep hX hlaw N (by omega) ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Bf hBf0 hBf Lip hLip hL ch hch p q hpq' hpq hwin hκ η₀ hw hη₀ hhw hη _ hL1 hNL
  refine hP.trans (le_of_eq ?_)
  rw [Real.exp_neg, Real.exp_log hy]
  have : (N : ℝ) ≠ 0 := by positivity
  have : (⌊(q - p) / hw⌋₊ : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end GeomGrid

end CTG.NPointGrid
