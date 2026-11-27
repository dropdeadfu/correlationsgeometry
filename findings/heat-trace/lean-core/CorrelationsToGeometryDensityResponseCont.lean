/-
Forty-third file (Mathlib only): the density response of the kernel graph for integral kernels.
Namespace `CTG.DensityResponseCont`; check with `./check_density_response_cont.sh`.
Finite measure `μ`, kernel `K` jointly measurable with `0 ≤ K ≤ B`, density `n_ε = n₀ exp(ε φ)`, `φ` bounded;
`q`, `W`, `D`, `P`, `S`, `A` as in the finite file, with integrals against `μ`.
(1) Exact, pointwise: `Sc_eq_conj` (`S(x,y) = A(x) K(x,y) A(y)`), `Sc_symm`, `Sc_similar`, `kpow_conj`,
`Sc_kpow_diag` (the diagonals of all iterated kernels of `S` and `P` agree).
(2) First order at `ε = 0`, pointwise in `x`, on a homogeneous background (HYPOTHESIS `κhom`:
`∫ K(x,y) dμ(y) = κ > 0` for all `x`): `hasDerivAt_log_q` (`𝒢φ`), `hasDerivAt_log_D` (`−𝒢𝒢φ`),
`hasDerivAt_log_A` (`φ/2 − 𝒢φ + 𝒢𝒢φ/2`), `hasDerivAt_log_A_eigen` (`½ (1−γ)² φ` if `𝒢φ = γφ`).
(B) Convolution kernels on an additive group with an invariant finite measure: `conv_homogeneous` (the
background is homogeneous), `conv_cos_eigen`, `hasDerivAt_log_A_conv` (for `φ = c` with the addition formula
`c(x−u) = c(x)c(u) + s(x)s(u)` as a HYPOTHESIS: derivative `½ (1−γ)² c(x)`, `γ = ∫kc/∫k`).
NOT formalised: the instance on the torus and the value `γ = e^{−ξ²a²/2}` for the Gaussian kernel; remainders
`O(φ²)`; derivatives of the iterated kernels and of traces; the summation with `1 − √(1−s)`; the coefficient
`c(a)` and its limit.  No sorry, no axiom, no native_decide.
Written by a sub-task of an AI session on 27 November 2026.
-/
import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Metric

namespace CTG.DensityResponseCont

variable {E : Type*} [MeasurableSpace E]

/-- `q(x) = ∫ K(x,y) n(y) dμ(y)`. -/
noncomputable def qc (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x : E) : ℝ := ∫ y, K x y * n y ∂μ
/-- `W(x,y) = K(x,y)/(q(x) q(y))`. -/
noncomputable def Wc (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x y : E) : ℝ :=
  K x y / (qc μ K n x * qc μ K n y)
/-- `D(x) = ∫ W(x,y) n(y) dμ(y)`. -/
noncomputable def Dc (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x : E) : ℝ := ∫ y, Wc μ K n x y * n y ∂μ
/-- The walk kernel `P(x,y) = W(x,y) n(y)/D(x)` (with respect to `μ`). -/
noncomputable def Pc (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x y : E) : ℝ :=
  Wc μ K n x y * n y / Dc μ K n x
/-- The symmetrised kernel `S(x,y) = √n(x) W(x,y) √n(y)/√(D(x)D(y))`. -/
noncomputable def Sc (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x y : E) : ℝ :=
  Real.sqrt (n x) * Wc μ K n x y * Real.sqrt (n y) / Real.sqrt (Dc μ K n x * Dc μ K n y)
/-- `A(x) = √n(x)/(q(x) √D(x))`. -/
noncomputable def Ac (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x : E) : ℝ :=
  Real.sqrt (n x) / (qc μ K n x * Real.sqrt (Dc μ K n x))
/-- `r(x) = √(n(x) D(x))`. -/
noncomputable def rc (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x : E) : ℝ :=
  Real.sqrt (n x * Dc μ K n x)
/-- `R(x) = ∫ K(x,y) n(y)/q(y) dμ(y)`, so that `D = R/q`. -/
noncomputable def Rc (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x : E) : ℝ :=
  ∫ y, K x y * n y / qc μ K n y ∂μ

/-- `D(x) = R(x)/q(x)` (no hypothesis). -/
lemma Dc_eq (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (x : E) :
    Dc μ K n x = Rc μ K n x / qc μ K n x := by
  unfold Dc Rc Wc
  rw [← integral_div]
  congr 1; funext y; ring

section Exact

variable (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ)

/-- **Claim 1, kernel form.** `S(x,y) = A(x) K(x,y) A(y)`. -/
theorem Sc_eq_conj (x y : E) (hnx : 0 < n x) (hny : 0 < n y) (hqx : 0 < qc μ K n x)
    (hqy : 0 < qc μ K n y) (hDx : 0 < Dc μ K n x) (hDy : 0 < Dc μ K n y) :
    Sc μ K n x y = Ac μ K n x * K x y * Ac μ K n y := by
  unfold Sc Ac Wc
  have h1 := Real.sqrt_pos.mpr hDx
  have h2 := Real.sqrt_pos.mpr hDy
  rw [Real.sqrt_mul hDx.le]
  field_simp

/-- Symmetry of `S` for a symmetric kernel. -/
theorem Sc_symm (hKs : ∀ x y, K x y = K y x) (x y : E) : Sc μ K n x y = Sc μ K n y x := by
  unfold Sc Wc
  rw [hKs x y, mul_comm (Dc μ K n x), mul_comm (qc μ K n x)]
  ring

/-- Similarity: `S(x,y) = r(x) P(x,y)/r(y)`. -/
theorem Sc_similar (x y : E) (hnx : 0 < n x) (hny : 0 < n y) (hDx : 0 < Dc μ K n x)
    (hDy : 0 < Dc μ K n y) :
    Sc μ K n x y = rc μ K n x * Pc μ K n x y / rc μ K n y := by
  unfold Sc rc Pc
  have h1 := Real.sqrt_pos.mpr hDx
  have h2 := Real.sqrt_pos.mpr hDy
  have h3 := Real.sqrt_pos.mpr hnx
  have h4 := Real.sqrt_pos.mpr hny
  rw [Real.sqrt_mul hDx.le, Real.sqrt_mul hnx.le, Real.sqrt_mul hny.le]
  have h5 := Real.sq_sqrt hny.le
  have h6 := Real.sq_sqrt hDx.le
  set a := Real.sqrt (n x)
  set b := Real.sqrt (n y)
  set c := Real.sqrt (Dc μ K n x)
  set d := Real.sqrt (Dc μ K n y)
  rw [← h5, ← h6]
  field_simp

end Exact

/-- Iterated kernels: `T^{(0)} = T`, `T^{(j+1)}(x,z) = ∫ T(x,y) T^{(j)}(y,z) dμ(y)`. -/
noncomputable def kpow (μ : Measure E) (T : E → E → ℝ) : ℕ → E → E → ℝ
  | 0 => T
  | j + 1 => fun x z => ∫ y, T x y * kpow μ T j y z ∂μ

/-- Conjugation passes to iterated kernels (no integrability needed). -/
theorem kpow_conj (μ : Measure E) (T P : E → E → ℝ) (r : E → ℝ) (hr : ∀ y, r y ≠ 0)
    (hT : ∀ x y, T x y = r x * P x y / r y) (j : ℕ) (x z : E) :
    kpow μ T j x z = r x * kpow μ P j x z / r z := by
  induction j generalizing x z with
  | zero => exact hT x z
  | succ j ih =>
    simp only [kpow]
    have : (fun y => T x y * kpow μ T j y z) = fun y => (r x / r z) * (P x y * kpow μ P j y z) := by
      funext y
      rw [hT x y, ih y z]
      field_simp [hr y, hr z]
    rw [this, integral_const_mul]
    field_simp [hr z]

/-- **Diagonals.** Under `S(x,y) = r(x) P(x,y)/r(y)` with `r ≠ 0`, the diagonals of all iterated kernels agree. -/
theorem kpow_diag (μ : Measure E) (T P : E → E → ℝ) (r : E → ℝ) (hr : ∀ y, r y ≠ 0)
    (hT : ∀ x y, T x y = r x * P x y / r y) (j : ℕ) (x : E) :
    kpow μ T j x x = kpow μ P j x x := by
  rw [kpow_conj μ T P r hr hT j x x]
  field_simp [hr x]

/-- The same for the density-weighted kernels `S`, `P` (positivity of `n`, `D` everywhere). -/
theorem Sc_kpow_diag (μ : Measure E) (K : E → E → ℝ) (n : E → ℝ) (hn : ∀ x, 0 < n x)
    (hD : ∀ x, 0 < Dc μ K n x) (j : ℕ) (x : E) :
    kpow μ (Sc μ K n) j x x = kpow μ (Pc μ K n) j x x :=
  kpow_diag μ _ _ (rc μ K n) (fun y => (Real.sqrt_pos.mpr (mul_pos (hn y) (hD y))).ne')
    (fun x y => Sc_similar μ K n x y (hn x) (hn y) (hD x) (hD y)) j x

/-! ## First order in `ε` on a homogeneous background -/

/-- The perturbed density `n_ε(y) = n⁰ exp(ε φ(y))`. -/
noncomputable def nε (n0 : ℝ) (φ : E → ℝ) (ε : ℝ) (y : E) : ℝ := n0 * Real.exp (ε * φ y)

/-- The smoothing operator `𝒢f(x) = (1/κ) ∫ K(x,y) f(y) dμ(y)`. -/
noncomputable def Gc (μ : Measure E) (K : E → E → ℝ) (κ : ℝ) (f : E → ℝ) (x : E) : ℝ :=
  (∫ y, K x y * f y ∂μ) / κ

/-- Derivative of `q_ε(y)` in `ε`. -/
noncomputable def qd (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  ∫ z, K y z * (n0 * (Real.exp (ε * φ z) * φ z)) ∂μ

/-- The standing hypotheses of the perturbative part. -/
structure Hyp (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 κ B C : ℝ) : Prop where
  Km : Measurable (Function.uncurry K)
  K0 : ∀ x y, 0 ≤ K x y
  KB : ∀ x y, K x y ≤ B
  φm : Measurable φ
  φC : ∀ y, |φ y| ≤ C
  C0 : 0 ≤ C
  B0 : 0 ≤ B
  n0pos : 0 < n0
  /-- HYPOTHESIS (homogeneous background): `∫ K(x,y) dμ(y) = κ` for every `x`. -/
  κhom : ∀ x, ∫ y, K x y ∂μ = κ
  κpos : 0 < κ

section Perturb

variable {μ : Measure E} [IsFiniteMeasure μ] {K : E → E → ℝ} {φ : E → ℝ} {n0 κ B C : ℝ}
  (h : Hyp μ K φ n0 κ B C)
include h

lemma meas_Kx (x : E) : Measurable (K x) := h.Km.comp measurable_prodMk_left

lemma meas_nε (ε : ℝ) : Measurable (nε n0 φ ε) := by
  unfold nε
  exact measurable_const.mul ((measurable_const.mul h.φm).exp)

/-- `y ↦ ∫ K(y,z) f(z) dμ(z)` is measurable. -/
lemma meas_int_K (f : E → ℝ) (hf : Measurable f) : Measurable (fun y => ∫ z, K y z * f z ∂μ) := by
  have hm : StronglyMeasurable (Function.uncurry fun y z => K y z * f z) :=
    (h.Km.mul (hf.comp measurable_snd)).stronglyMeasurable
  exact (hm.integral_prod_right (ν := μ)).measurable

lemma meas_q (ε : ℝ) : Measurable (qc μ K (nε n0 φ ε)) :=
  meas_int_K h _ (meas_nε h ε)

lemma int_K_mul (x : E) (f : E → ℝ) (hf : Measurable f) (M : ℝ) (hfM : ∀ y, |f y| ≤ M) :
    Integrable (fun y => K x y * f y) μ := by
  refine Integrable.of_bound ((meas_Kx h x).mul hf).aestronglyMeasurable (B * M)
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.K0 x y)]
  exact mul_le_mul (h.KB x y) (hfM y) (abs_nonneg _) h.B0

lemma int_K_const (x : E) (c : ℝ) : ∫ y, K x y * c ∂μ = c * κ := by
  rw [integral_mul_const, h.κhom x]; ring

lemma int_K_lower (x : E) (f : E → ℝ) (hf : Measurable f) (M : ℝ) (hfM : ∀ y, |f y| ≤ M)
    (c : ℝ) (hc : ∀ y, c ≤ f y) : c * κ ≤ ∫ y, K x y * f y ∂μ := by
  rw [← int_K_const h x c]
  refine integral_mono (int_K_mul h x _ measurable_const |c| fun _ => le_rfl)
    (int_K_mul h x f hf M hfM) fun y => ?_
  exact mul_le_mul_of_nonneg_left (hc y) (h.K0 x y)

lemma int_K_upper (x : E) (f : E → ℝ) (hf : Measurable f) (M : ℝ) (hfM : ∀ y, |f y| ≤ M)
    (c : ℝ) (hc : ∀ y, f y ≤ c) : ∫ y, K x y * f y ∂μ ≤ c * κ := by
  rw [← int_K_const h x c]
  refine integral_mono (int_K_mul h x f hf M hfM)
    (int_K_mul h x _ measurable_const |c| fun _ => le_rfl) fun y => ?_
  exact mul_le_mul_of_nonneg_left (hc y) (h.K0 x y)

lemma exp_le (ε L : ℝ) (hL : |ε| ≤ L) (y : E) : Real.exp (ε * φ y) ≤ Real.exp (L * C) := by
  apply Real.exp_le_exp.mpr
  calc ε * φ y ≤ |ε * φ y| := le_abs_self _
    _ = |ε| * |φ y| := abs_mul _ _
    _ ≤ L * C := mul_le_mul hL (h.φC y) (abs_nonneg _) ((abs_nonneg _).trans hL)

lemma exp_ge (ε L : ℝ) (hL : |ε| ≤ L) (y : E) : Real.exp (-(L * C)) ≤ Real.exp (ε * φ y) := by
  apply Real.exp_le_exp.mpr
  have : |ε * φ y| ≤ L * C := by
    rw [abs_mul]; exact mul_le_mul hL (h.φC y) (abs_nonneg _) ((abs_nonneg _).trans hL)
  linarith [neg_abs_le (ε * φ y)]

lemma nε_pos (ε : ℝ) (y : E) : 0 < nε n0 φ ε y := mul_pos h.n0pos (Real.exp_pos _)

lemma nε_abs_le (ε L : ℝ) (hL : |ε| ≤ L) (y : E) : |nε n0 φ ε y| ≤ n0 * Real.exp (L * C) := by
  rw [abs_of_pos (nε_pos h ε y)]; unfold nε
  exact mul_le_mul_of_nonneg_left (exp_le h ε L hL y) h.n0pos.le

lemma q_bounds (ε L : ℝ) (hL : |ε| ≤ L) (y : E) :
    n0 * Real.exp (-(L * C)) * κ ≤ qc μ K (nε n0 φ ε) y ∧
      qc μ K (nε n0 φ ε) y ≤ n0 * Real.exp (L * C) * κ := by
  constructor
  · exact int_K_lower h y _ (meas_nε h ε) _ (nε_abs_le h ε L hL) _
      fun z => mul_le_mul_of_nonneg_left (exp_ge h ε L hL z) h.n0pos.le
  · exact int_K_upper h y _ (meas_nε h ε) _ (nε_abs_le h ε L hL) _
      fun z => mul_le_mul_of_nonneg_left (exp_le h ε L hL z) h.n0pos.le

lemma q_pos (ε : ℝ) (y : E) : 0 < qc μ K (nε n0 φ ε) y :=
  lt_of_lt_of_le (mul_pos (mul_pos h.n0pos (Real.exp_pos _)) h.κpos)
    (q_bounds h ε |ε| le_rfl y).1

lemma nε_zero : nε n0 φ 0 = fun _ => n0 := by funext y; simp [nε]

lemma q_zero (y : E) : qc μ K (nε n0 φ 0) y = n0 * κ := by
  rw [nε_zero h]; unfold qc; rw [int_K_const h]

/-- Generic differentiation under the integral against `K(x,·)`. -/
lemma hasDerivAt_int_K (x : E) (g g' : ℝ → E → ℝ) (ε0 M M0 : ℝ)
    (hgm : ∀ ε, Measurable (g ε)) (hg'm : Measurable (g' ε0)) (hg0 : ∀ y, |g ε0 y| ≤ M0)
    (hd : ∀ y, ∀ ε ∈ ball ε0 1, HasDerivAt (fun e => g e y) (g' ε y) ε)
    (hb : ∀ y, ∀ ε ∈ ball ε0 1, |g' ε y| ≤ M) :
    HasDerivAt (fun ε => ∫ y, K x y * g ε y ∂μ) (∫ y, K x y * g' ε0 y ∂μ) ε0 := by
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun ε y => K x y * g ε y) (F' := fun ε y => K x y * g' ε y) (x₀ := ε0)
    (bound := fun _ => B * M) (ball_mem_nhds ε0 one_pos)
    (Eventually.of_forall fun ε => ((meas_Kx h x).mul (hgm ε)).aestronglyMeasurable)
    (int_K_mul h x (g ε0) (hgm ε0) M0 hg0)
    (((meas_Kx h x).mul hg'm).aestronglyMeasurable)
    (ae_of_all _ fun y ε hε => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.K0 x y)]
      exact mul_le_mul (h.KB x y) (hb y ε hε) (abs_nonneg _) h.B0)
    (integrable_const _)
    (ae_of_all _ fun y ε hε => (hd y ε hε).const_mul (K x y))
  exact this.2

lemma hasDerivAt_nε (ε : ℝ) (y : E) :
    HasDerivAt (fun e => nε n0 φ e y) (n0 * (Real.exp (ε * φ y) * φ y)) ε := by
  have := (((hasDerivAt_id ε).mul_const (φ y)).exp).const_mul n0
  convert this using 1; simp

lemma ball_abs (ε0 ε : ℝ) (hε : ε ∈ ball ε0 1) : |ε| ≤ |ε0| + 1 := by
  rw [mem_ball, Real.dist_eq] at hε
  have := abs_sub_abs_le_abs_sub ε ε0
  linarith

/-- Derivative of `q_ε(y)` at any `ε0`. -/
lemma hasDerivAt_q (ε0 : ℝ) (y : E) :
    HasDerivAt (fun ε => qc μ K (nε n0 φ ε) y) (qd μ K φ n0 ε0 y) ε0 := by
  unfold qc qd
  refine hasDerivAt_int_K h y (fun ε z => nε n0 φ ε z) (fun ε z => n0 * (Real.exp (ε * φ z) * φ z)) ε0
    (n0 * (Real.exp ((|ε0| + 1) * C) * C)) (n0 * Real.exp (|ε0| * C)) (meas_nε h)
    (measurable_const.mul (((measurable_const.mul h.φm).exp).mul h.φm))
    (nε_abs_le h ε0 |ε0| le_rfl) (fun z ε _ => hasDerivAt_nε h ε z) (fun z ε hε => ?_)
  rw [abs_mul, abs_of_pos h.n0pos, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul (exp_le h ε _ (ball_abs h ε0 ε hε) z) (h.φC z)
    (abs_nonneg _) (Real.exp_pos _).le) h.n0pos.le

lemma qd_zero (y : E) : qd μ K φ n0 0 y = n0 * κ * Gc μ K κ φ y := by
  unfold qd Gc
  simp only [zero_mul, Real.exp_zero, one_mul]
  rw [integral_congr_ae (g := fun z => n0 * (K y z * φ z)) (ae_of_all _ fun z => by ring),
    integral_const_mul]
  field_simp [h.κpos.ne']

lemma qd_abs_le (ε L : ℝ) (hL : |ε| ≤ L) (y : E) :
    |qd μ K φ n0 ε y| ≤ B * (n0 * (Real.exp (L * C) * C)) * μ.real Set.univ := by
  unfold qd
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.K0 y z), abs_mul, abs_of_pos h.n0pos, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul (h.KB y z) (mul_le_mul_of_nonneg_left (mul_le_mul (exp_le h ε L hL z) (h.φC z)
    (abs_nonneg _) (Real.exp_pos _).le) h.n0pos.le)
    (mul_nonneg h.n0pos.le (mul_nonneg (Real.exp_pos _).le (abs_nonneg _))) h.B0

/-- **First claim.** `d/dε log q_ε(x) = 𝒢φ(x)` at `ε = 0`. -/
theorem hasDerivAt_log_q (x : E) :
    HasDerivAt (fun ε => Real.log (qc μ K (nε n0 φ ε) x)) (Gc μ K κ φ x) 0 := by
  have hq := (hasDerivAt_q h 0 x).log (by rw [q_zero h]; exact (mul_pos h.n0pos h.κpos).ne')
  convert hq using 1
  rw [q_zero h, qd_zero h]; field_simp [h.n0pos.ne', h.κpos.ne']

end Perturb

/-- The integrand of `R`: `g_ε(y) = n_ε(y)/q_ε(y)`. -/
noncomputable def gR (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  nε n0 φ ε y / qc μ K (nε n0 φ ε) y

/-- Its derivative in `ε`. -/
noncomputable def gR' (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  (n0 * (Real.exp (ε * φ y) * φ y) * qc μ K (nε n0 φ ε) y - nε n0 φ ε y * qd μ K φ n0 ε y) /
    qc μ K (nε n0 φ ε) y ^ 2

section Perturb2

variable {μ : Measure E} [IsFiniteMeasure μ] {K : E → E → ℝ} {φ : E → ℝ} {n0 κ B C : ℝ}
  (h : Hyp μ K φ n0 κ B C)
include h

lemma meas_qd (ε : ℝ) : Measurable (qd μ K φ n0 ε) :=
  meas_int_K h _ (measurable_const.mul (((measurable_const.mul h.φm).exp).mul h.φm))

lemma meas_gR (ε : ℝ) : Measurable (gR μ K φ n0 ε) := (meas_nε h ε).div (meas_q h ε)

lemma meas_gR' (ε : ℝ) : Measurable (gR' μ K φ n0 ε) :=
  (((measurable_const.mul (((measurable_const.mul h.φm).exp).mul h.φm)).mul (meas_q h ε)).sub
    ((meas_nε h ε).mul (meas_qd h ε))).div ((meas_q h ε).pow_const 2)

lemma gR_bounds (ε L : ℝ) (hL : |ε| ≤ L) (y : E) :
    Real.exp (-(L * C)) / (Real.exp (L * C) * κ) ≤ gR μ K φ n0 ε y ∧
      gR μ K φ n0 ε y ≤ Real.exp (L * C) / (Real.exp (-(L * C)) * κ) := by
  obtain ⟨hlo, hhi⟩ := q_bounds h ε L hL y
  have hq := q_pos h ε y
  have hn0 := h.n0pos
  have he1 := exp_le h ε L hL y
  have he2 := exp_ge h ε L hL y
  have hnv : nε n0 φ ε y = n0 * Real.exp (ε * φ y) := rfl
  have hκ0 := h.κpos
  unfold gR
  rw [hnv]
  constructor
  · rw [div_le_div_iff₀ (mul_pos (Real.exp_pos _) h.κpos) hq]
    calc Real.exp (-(L * C)) * qc μ K (nε n0 φ ε) y
        ≤ Real.exp (-(L * C)) * (n0 * Real.exp (L * C) * κ) :=
          mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le
      _ = n0 * Real.exp (-(L * C)) * (Real.exp (L * C) * κ) := by ring
      _ ≤ n0 * Real.exp (ε * φ y) * (Real.exp (L * C) * κ) := by
          gcongr
  · rw [div_le_div_iff₀ hq (mul_pos (Real.exp_pos _) h.κpos)]
    calc n0 * Real.exp (ε * φ y) * (Real.exp (-(L * C)) * κ)
        ≤ n0 * Real.exp (L * C) * (Real.exp (-(L * C)) * κ) := by gcongr
      _ = Real.exp (L * C) * (n0 * Real.exp (-(L * C)) * κ) := by ring
      _ ≤ Real.exp (L * C) * qc μ K (nε n0 φ ε) y :=
          mul_le_mul_of_nonneg_left hlo (Real.exp_pos _).le

lemma gR_abs_le (ε L : ℝ) (hL : |ε| ≤ L) (y : E) :
    |gR μ K φ n0 ε y| ≤ Real.exp (L * C) / (Real.exp (-(L * C)) * κ) := by
  obtain ⟨h1, h2⟩ := gR_bounds h ε L hL y
  rw [abs_of_pos (lt_of_lt_of_le (by have := h.κpos; positivity) h1)]; exact h2

lemma R_pos (ε : ℝ) (x : E) : 0 < Rc μ K (nε n0 φ ε) x := by
  have h1 := int_K_lower h x _ (meas_gR h ε) _ (gR_abs_le h ε |ε| le_rfl) _
    (fun y => (gR_bounds h ε |ε| le_rfl y).1)
  have : 0 < Real.exp (-(|ε| * C)) / (Real.exp (|ε| * C) * κ) * κ := by
    have := h.κpos; positivity
  unfold Rc; unfold gR at h1
  simp_rw [mul_div_assoc]
  exact lt_of_lt_of_le this h1

lemma D_pos (ε : ℝ) (x : E) : 0 < Dc μ K (nε n0 φ ε) x := by
  rw [Dc_eq]; exact div_pos (R_pos h ε x) (q_pos h ε x)

lemma gR'_abs_le (ε : ℝ) (hε : |ε| ≤ 1) (y : E) :
    |gR' μ K φ n0 ε y| ≤ (n0 * (Real.exp C * C) * (n0 * Real.exp C * κ) +
      n0 * Real.exp C * (B * (n0 * (Real.exp C * C)) * μ.real Set.univ)) /
        (n0 * Real.exp (-C) * κ) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := q_bounds h ε 1 hε y
  simp only [one_mul] at hlo hhi
  have hq := q_pos h ε y
  have hn := nε_abs_le h ε 1 hε y
  have hd := qd_abs_le h ε 1 hε y
  simp only [one_mul] at hn hd
  have ha : |n0 * (Real.exp (ε * φ y) * φ y)| ≤ n0 * (Real.exp C * C) := by
    rw [abs_mul, abs_of_pos h.n0pos, abs_mul, abs_of_pos (Real.exp_pos _)]
    have := exp_le h ε 1 hε y; simp only [one_mul] at this
    exact mul_le_mul_of_nonneg_left (mul_le_mul this (h.φC y) (abs_nonneg _)
      (Real.exp_pos _).le) h.n0pos.le
  have hlo0 : 0 < n0 * Real.exp (-C) * κ := by have := h.n0pos; have := h.κpos; positivity
  unfold gR'
  rw [abs_div, abs_of_pos (pow_pos hq 2)]
  have hnum : |n0 * (Real.exp (ε * φ y) * φ y) * qc μ K (nε n0 φ ε) y -
      nε n0 φ ε y * qd μ K φ n0 ε y| ≤ n0 * (Real.exp C * C) * (n0 * Real.exp C * κ) +
      n0 * Real.exp C * (B * (n0 * (Real.exp C * C)) * μ.real Set.univ) := by
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_pos hq]
      exact mul_le_mul ha hhi hq.le ((abs_nonneg _).trans ha)
    · rw [abs_mul]
      exact mul_le_mul hn hd (abs_nonneg _) ((abs_nonneg _).trans hn)
  calc _ ≤ (n0 * (Real.exp C * C) * (n0 * Real.exp C * κ) +
      n0 * Real.exp C * (B * (n0 * (Real.exp C * C)) * μ.real Set.univ)) /
        qc μ K (nε n0 φ ε) y ^ 2 := div_le_div_of_nonneg_right hnum (pow_pos hq 2).le
    _ ≤ _ := div_le_div_of_nonneg_left ((abs_nonneg _).trans hnum) (pow_pos hlo0 2)
        (pow_le_pow_left₀ hlo0.le hlo 2)

lemma hasDerivAt_gR (ε : ℝ) (y : E) :
    HasDerivAt (fun e => gR μ K φ n0 e y) (gR' μ K φ n0 ε y) ε :=
  (hasDerivAt_nε h ε y).div (hasDerivAt_q h ε y) (q_pos h ε y).ne'

lemma gR'_zero (y : E) : gR' μ K φ n0 0 y = (φ y - Gc μ K κ φ y) / κ := by
  unfold gR'
  rw [q_zero h, qd_zero h, nε_zero h]
  simp only [zero_mul, Real.exp_zero, one_mul]
  field_simp [h.n0pos.ne', h.κpos.ne']

lemma Gc_abs_le (f : E → ℝ) (M : ℝ) (hfM : ∀ y, |f y| ≤ M) (x : E) :
    |Gc μ K κ f x| ≤ B * M * μ.real Set.univ / κ := by
  unfold Gc
  rw [abs_div, abs_of_pos h.κpos]
  refine div_le_div_of_nonneg_right ?_ h.κpos.le
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.K0 x z)]
  exact mul_le_mul (h.KB x z) (hfM z) (abs_nonneg _) h.B0

lemma meas_Gc (f : E → ℝ) (hf : Measurable f) : Measurable (Gc μ K κ f) :=
  (meas_int_K h f hf).div_const κ

lemma R_zero (x : E) : Rc μ K (nε n0 φ 0) x = 1 := by
  unfold Rc
  have : (fun y => K x y * nε n0 φ 0 y / qc μ K (nε n0 φ 0) y) = fun y => K x y * (1 / κ) := by
    funext y; rw [q_zero h, nε_zero h]; field_simp [h.n0pos.ne', h.κpos.ne']
  rw [this, int_K_const h]; field_simp [h.κpos.ne']

/-- Derivative of `R` at `ε = 0`: `𝒢φ − 𝒢²φ`. -/
lemma hasDerivAt_R (x : E) :
    HasDerivAt (fun ε => Rc μ K (nε n0 φ ε) x)
      (Gc μ K κ φ x - Gc μ K κ (Gc μ K κ φ) x) 0 := by
  have hd := hasDerivAt_int_K h x (gR μ K φ n0) (gR' μ K φ n0) 0 _ _ (meas_gR h) (meas_gR' h 0)
    (gR_abs_le h 0 0 (by simp)) (fun y ε _ => hasDerivAt_gR h ε y)
    (fun y ε hε => gR'_abs_le h ε (by rw [mem_ball, Real.dist_eq, sub_zero] at hε; exact hε.le) y)
  have heq : (fun ε => Rc μ K (nε n0 φ ε) x) = fun ε => ∫ y, K x y * gR μ K φ n0 ε y ∂μ := by
    funext ε; unfold Rc gR; congr 1; funext y; ring
  rw [heq]
  convert hd using 1
  have hGφ := Gc_abs_le h φ C h.φC
  rw [integral_congr_ae (g := fun y => (K x y * φ y - K x y * Gc μ K κ φ y) / κ)
    (ae_of_all _ fun y => by simp only; rw [gR'_zero h]; ring), integral_div,
    integral_sub (int_K_mul h x φ h.φm C h.φC)
      (int_K_mul h x _ (meas_Gc h φ h.φm) _ hGφ)]
  rw [show Gc μ K κ (Gc μ K κ φ) x = (∫ y, K x y * Gc μ K κ φ y ∂μ) / κ from rfl,
    show Gc μ K κ φ x = (∫ y, K x y * φ y ∂μ) / κ from rfl]
  ring

/-- **Second claim.** `d/dε log D_ε(x) = −𝒢²φ(x)` at `ε = 0`. -/
theorem hasDerivAt_log_D (x : E) :
    HasDerivAt (fun ε => Real.log (Dc μ K (nε n0 φ ε) x)) (-Gc μ K κ (Gc μ K κ φ) x) 0 := by
  have heq : (fun ε => Real.log (Dc μ K (nε n0 φ ε) x)) =
      fun ε => Real.log (Rc μ K (nε n0 φ ε) x) - Real.log (qc μ K (nε n0 φ ε) x) := by
    funext ε
    rw [Dc_eq, Real.log_div (R_pos h ε x).ne' (q_pos h ε x).ne']
  rw [heq]
  have hR := (hasDerivAt_R h x).log (by rw [R_zero h]; exact one_ne_zero)
  have hq := hasDerivAt_log_q h x
  convert hR.sub hq using 1
  rw [R_zero h]; ring

/-- **Third claim.** `d/dε log A_ε(x) = ½φ(x) − 𝒢φ(x) + ½𝒢²φ(x)` at `ε = 0`. -/
theorem hasDerivAt_log_A (x : E) :
    HasDerivAt (fun ε => Real.log (Ac μ K (nε n0 φ ε) x))
      (φ x / 2 - Gc μ K κ φ x + Gc μ K κ (Gc μ K κ φ) x / 2) 0 := by
  have heq : (fun ε => Real.log (Ac μ K (nε n0 φ ε) x)) = fun ε =>
      (Real.log n0 + ε * φ x) / 2 - Real.log (qc μ K (nε n0 φ ε) x)
        - Real.log (Dc μ K (nε n0 φ ε) x) / 2 := by
    funext ε
    have hD := D_pos h ε x
    have hq := q_pos h ε x
    have hn := nε_pos h ε x
    unfold Ac
    rw [Real.log_div (Real.sqrt_pos.mpr hn).ne' (mul_pos hq (Real.sqrt_pos.mpr hD)).ne',
      Real.log_mul hq.ne' (Real.sqrt_pos.mpr hD).ne', Real.log_sqrt hn.le, Real.log_sqrt hD.le]
    unfold nε
    rw [Real.log_mul h.n0pos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [heq]
  have hlin : HasDerivAt (fun ε : ℝ => (Real.log n0 + ε * φ x) / 2) (φ x / 2) 0 := by
    have := (((hasDerivAt_id (0:ℝ)).mul_const (φ x)).const_add (Real.log n0)).div_const 2
    convert this using 1; simp
  convert (hlin.sub (hasDerivAt_log_q h x)).sub ((hasDerivAt_log_D h x).div_const 2) using 1
  ring

/-- **Eigenfunction case.** If `𝒢φ = γφ`, then `d/dε log A_ε(x) = ½(1−γ)² φ(x)` at `ε = 0`. -/
theorem hasDerivAt_log_A_eigen (γ : ℝ) (hγ : ∀ y, Gc μ K κ φ y = γ * φ y) (x : E) :
    HasDerivAt (fun ε => Real.log (Ac μ K (nε n0 φ ε) x)) ((1 - γ) ^ 2 / 2 * φ x) 0 := by
  have hG2 : Gc μ K κ (Gc μ K κ φ) x = γ * (γ * φ x) := by
    have h1 : Gc μ K κ (Gc μ K κ φ) x = Gc μ K κ (fun y => γ * φ y) x := by
      congr 1; funext y; exact hγ y
    have h2 : Gc μ K κ (fun y => γ * φ y) x = γ * Gc μ K κ φ x := by
      unfold Gc
      simp_rw [mul_left_comm (K x _) γ]
      rw [integral_const_mul]; ring
    rw [h1, h2, hγ x]
  convert hasDerivAt_log_A h x using 1
  rw [hG2, hγ x]; ring

end Perturb2

/-! ## Translation-invariant kernels (frame (B), abstract group form) -/

section Group

variable {G : Type*} [MeasurableSpace G] [AddCommGroup G] [MeasurableAdd G] [MeasurableNeg G]
  (ν : Measure G) [ν.IsAddLeftInvariant] [ν.IsNegInvariant]

/-- For `K(x,y) = k(x−y)` and a translation- and reflection-invariant measure the background is
automatically homogeneous: `∫ k(x−y) dν(y) = ∫ k`. -/
theorem conv_homogeneous (k : G → ℝ) (x : G) : ∫ y, k (x - y) ∂ν = ∫ u, k u ∂ν :=
  integral_sub_left_eq_self k ν x

/-- Cosine-type eigenfunctions of a convolution with an even kernel: if `c(x−u) = c(x)c(u) + s(x)s(u)`
with `s` odd and `k` even, then `∫ k(x−y) c(y) dν(y) = (∫ k c) · c(x)`. -/
theorem conv_cos_eigen (k c s : G → ℝ) (hk : ∀ u, k (-u) = k u) (hs : ∀ u, s (-u) = -s u)
    (hadd : ∀ x u, c (x - u) = c x * c u + s x * s u)
    (hkc : Integrable (fun u => k u * c u) ν) (hks : Integrable (fun u => k u * s u) ν) (x : G) :
    ∫ y, k (x - y) * c y ∂ν = (∫ u, k u * c u ∂ν) * c x := by
  have h1 : ∫ y, k (x - y) * c y ∂ν = ∫ u, k u * c (x - u) ∂ν := by
    have := integral_sub_left_eq_self (fun u => k u * c (x - u)) ν x
    simp only [sub_sub_cancel] at this
    exact this
  have h2 : ∫ u, k u * s u ∂ν = 0 := by
    have := integral_neg_eq_self (fun u => k u * s u) ν
    simp only [hk, hs, mul_neg, integral_neg] at this
    linarith
  rw [h1, integral_congr_ae (g := fun u => c x * (k u * c u) + s x * (k u * s u))
    (ae_of_all _ fun u => by simp only; rw [hadd]; ring),
    integral_add (hkc.const_mul _) (hks.const_mul _), integral_const_mul, integral_const_mul, h2]
  ring

/-- **Frame (B).** For a translation-invariant kernel `K(x,y) = k(x−y)` with `k` even, bounded,
`∫ k > 0`, and a cosine-type mode `φ = c`, the derivative of `log A_ε(x)` at `ε = 0` is
`½(1−γ)² c(x)` with `γ = (∫ k c)/(∫ k)` (the normalised Fourier coefficient of `k`). -/
theorem hasDerivAt_log_A_conv [MeasurableSub₂ G] [IsFiniteMeasure ν]
    (k c s : G → ℝ) (n0 B C : ℝ) (hkm : Measurable k) (hk0 : ∀ u, 0 ≤ k u) (hkB : ∀ u, k u ≤ B)
    (hB : 0 ≤ B) (hcm : Measurable c) (hcC : ∀ y, |c y| ≤ C) (hC : 0 ≤ C) (hn0 : 0 < n0)
    (hκ : 0 < ∫ u, k u ∂ν)
    (hk : ∀ u, k (-u) = k u) (hs : ∀ u, s (-u) = -s u)
    (hadd : ∀ x u, c (x - u) = c x * c u + s x * s u)
    (hks : Integrable (fun u => k u * s u) ν) (x : G) :
    HasDerivAt (fun ε => Real.log (Ac ν (fun x y => k (x - y)) (nε n0 c ε) x))
      ((1 - (∫ u, k u * c u ∂ν) / (∫ u, k u ∂ν)) ^ 2 / 2 * c x) 0 := by
  have h : Hyp ν (fun x y => k (x - y)) c n0 (∫ u, k u ∂ν) B C :=
    { Km := hkm.comp measurable_sub
      K0 := fun x y => hk0 _
      KB := fun x y => hkB _
      φm := hcm
      φC := hcC
      C0 := hC
      B0 := hB
      n0pos := hn0
      κhom := fun x => conv_homogeneous ν k x
      κpos := hκ }
  have hkc : Integrable (fun u => k u * c u) ν := by
    refine Integrable.of_bound (hkm.mul hcm).aestronglyMeasurable (B * C) (ae_of_all _ fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 u)]
    exact mul_le_mul (hkB u) (hcC u) (abs_nonneg _) hB
  refine hasDerivAt_log_A_eigen h _ (fun y => ?_) x
  unfold Gc
  rw [conv_cos_eigen ν k c s hk hs hadd hkc hks y]
  field_simp

end Group

end CTG.DensityResponseCont
