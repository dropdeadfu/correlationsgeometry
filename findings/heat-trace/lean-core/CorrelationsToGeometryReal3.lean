/-
From Correlations to Geometry -- seventh Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the third file `CorrelationsToGeometryReal2.lean` unchanged (and through it the second
and the core file) and continues it; it exists only because a check of the third file takes about
fifty minutes.  Check with `cd lean && ./check_real3.sh` (against the COMPILED third file).
No `sorry`, no `axiom`, no `native_decide`.  Every statement is a FORM of a statement of
Appendix G of the paper with the constants and exceptional events of these files; none of them is
"the theorem of the paper, machine-checked".  See the comments at the namespaces.
-/
import CorrelationsToGeometryReal2
import Mathlib.Probability.StrongLaw

open MeasureTheory ProbabilityTheory CTG.Reals Matrix

namespace CTG.Reals2

/-! ## Rates for the kernel and the subtracted heat trace in the joint regime
(`cor:kernel-trace`, the statement "both right-hand sides are at most
`C (log N (1 + ξ² log N) / (N ξ^{d+2}))^{1/2}`" and "if moreover `N ξ^{d+6}/log N → ∞`, they are
`o(ξ²)`").

Conventions of this file (they differ from the paper): `σ` is the VARIANCE of the periodised
Gaussian kernel, `σ = ξ²` (the paper writes `σ = ξ²/2` for the heat time of one step); `M = p_σ(0)`,
`δ' = √(M log N / N)`; `σ^{d/2}` is written `(√σ)^d`. The rate quantity is
`rateQ d σ N = log N (1 + σ log N) / (N σ^{d/2} σ)`, with `σ = ξ²` this is
`log N (1 + ξ² log N) / (N ξ^{d+2})`.

What is proven here:
* Stage 1 (deterministic, fixed `N ≥ 2`, `0 < σ ≤ 1`): the two right-hand sides of the corollary
  (in the form of the Lean statements `kernel_theorem_G28`, `heat_trace_G29_ratio`) are bounded by
  explicit constants times `√rateQ0 ≤ √rateQ` resp. `√rateQ` plus a term LINEAR in `rateQ` (the
  Poisson tail `4M/N²`); the latter is `≤ √rateQ` as soon as `rateQ ≤ 1`.
* Stage 2 (almost surely, for all large `N`), under `N σ_N^{d/2+1}/log N → ∞`: the kernel entries,
  `Tr P^k / m_k` for `1 ≤ k ≤ ⌈c/σ_N⌉` and the relative subtracted heat trace for ALL
  `2 ≤ τ ≤ c/σ_N` deviate by at most `C(d,c) √rateQ`.
* Stage 3, under `N σ_N^{d/2+3}/log N → ∞` (with `σ = ξ²`: `N ξ^{d+6}/log N → ∞`): for every
  `η > 0` these bounds are eventually `≤ η σ_N`, i.e. they are `o(σ_N) = o(ξ_N²)`.

What is NOT proven here: the comparison of `poissonMean` (`= ∑_{j≥1} w_j m_j`, the right-hand side of
`thm:rate`(i)) with `Tr e^{tΔ}`, the sharp coefficient `d(d+2)/(8τ)`, the last display of the
corollary. The constants are those of the Lean files (`kernelC1`), not `C_1` of the paper; the
exceptional events are those of `kernel_theorem_G28` / `heat_trace_G29_uniform`; the sample is
nested (the first `N` points of one sequence); `τ` is a free real parameter (the paper has
`τ = 2t/ξ²`, `t ∈ [ξ², 1]`, which is `2 ≤ τ ≤ 2/σ`, the case `c = 2`; the range `k ≤ 20 ξ⁻²` of the
paper is `c = 20`). -/

namespace TraceRates

open Filter Topology
open CTG.Reals.TraceG29 CTG.Reals.Assembled Regime

/-- The rate quantity `log N (1 + σ log N) / (N σ^{d/2} σ)` (with `σ = ξ²`:
    `log N (1 + ξ² log N) / (N ξ^{d+2})`). -/
noncomputable def rateQ (d : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  Real.log N * (1 + σ * Real.log N) / ((N : ℝ) * Real.sqrt σ ^ d * σ)

/-- The smaller quantity `log N / (N σ^{d/2} σ)` (enough for the kernel and for `Tr P^k`). -/
noncomputable def rateQ0 (d : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  Real.log N / ((N : ℝ) * Real.sqrt σ ^ d * σ)

/-- The constant of the trace rate: `C₁ √(2^d (3c+2)) + 4·2^d`. -/
noncomputable def traceRateC (d : ℕ) (c : ℝ) : ℝ :=
  kernelC1 d * Real.sqrt (2 ^ d * (3 * c + 2)) + 4 * 2 ^ d

/-- The constant of the kernel rate: `C₁ √(2^d (c+1))`. -/
noncomputable def kernelRateC (d : ℕ) (c : ℝ) : ℝ :=
  kernelC1 d * Real.sqrt (2 ^ d * (c + 1))

theorem traceRateC_nonneg (d : ℕ) (c : ℝ) : 0 ≤ traceRateC d c := by
  unfold traceRateC
  have h1 := mul_nonneg (kernelC1_nonneg d) (Real.sqrt_nonneg (2 ^ d * (3 * c + 2)))
  have h2 : (0 : ℝ) ≤ 4 * 2 ^ d := by positivity
  linarith

theorem kernelRateC_nonneg (d : ℕ) (c : ℝ) : 0 ≤ kernelRateC d c := by
  unfold kernelRateC
  exact mul_nonneg (kernelC1_nonneg d) (Real.sqrt_nonneg _)

/-! ### Stage 1: deterministic bounds -/

/-- For `N ≥ 2`: `log N > 0` and `log N · N ≥ 1`. -/
theorem log_facts {N : ℕ} (hN : 2 ≤ N) : 0 < Real.log N ∧ 1 ≤ Real.log N * N := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := Real.log_two_gt_d9
  have hL : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN'
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log N - 0.69)
    (by linarith : (0 : ℝ) ≤ (N : ℝ) - 2)]

theorem rateQ_pos (d : ℕ) {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 2 ≤ N) : 0 < rateQ d σ N := by
  have hL := (log_facts hN).1
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt σ ^ d := pow_pos (Real.sqrt_pos.mpr hσ) d
  have h1 : 0 < 1 + σ * Real.log N := by nlinarith [mul_pos hσ hL]
  unfold rateQ
  exact div_pos (mul_pos hL h1) (mul_pos (mul_pos hN' hs) hσ)

theorem rateQ0_nonneg (d : ℕ) {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 2 ≤ N) : 0 ≤ rateQ0 d σ N := by
  have hL := (log_facts hN).1
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt σ ^ d := pow_pos (Real.sqrt_pos.mpr hσ) d
  unfold rateQ0
  exact (div_pos hL (mul_pos (mul_pos hN' hs) hσ)).le

theorem rateQ0_le_rateQ (d : ℕ) {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 2 ≤ N) :
    rateQ0 d σ N ≤ rateQ d σ N := by
  have hL := (log_facts hN).1
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt σ ^ d := pow_pos (Real.sqrt_pos.mpr hσ) d
  have h1 : Real.log N ≤ Real.log N * (1 + σ * Real.log N) := by
    nlinarith [mul_nonneg hL.le (mul_pos hσ hL).le]
  unfold rateQ0 rateQ
  exact div_le_div_of_nonneg_right h1 (mul_pos (mul_pos hN' hs) hσ).le

/-- `⌈c/σ⌉ ≤ (c+1)/σ` for `0 < σ ≤ 1`, `c > 0`. -/
theorem nat_ceil_le_div {σ c : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : 0 < c) :
    ((⌈c / σ⌉₊ : ℕ) : ℝ) ≤ (c + 1) * 1 / σ := by
  have hcσ : 0 < c / σ := div_pos hc hσ
  have h5 := (Nat.ceil_lt_add_one hcσ.le).le
  have h6 : (1 : ℝ) ≤ 1 / σ := (one_le_div hσ).mpr hσ1
  have h7 : (c + 1) * 1 / σ = c / σ + 1 / σ := by ring
  linarith

/-- `⌈3c/σ + 2L⌉ ≤ (3c+2)(1 + σL)/σ` for `0 < σ ≤ 1`, `c > 0`, `L > 0`. -/
theorem ceil_trace_le {σ c L : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : 0 < c) (hL : 0 < L) :
    ((⌈3 * c / σ + 2 * L⌉₊ : ℕ) : ℝ) ≤ (3 * c + 2) * (1 + σ * L) / σ := by
  have hcσ : 0 < 3 * c / σ := div_pos (by linarith) hσ
  have harg : 0 < 3 * c / σ + 2 * L := by linarith
  have h5 := (Nat.ceil_lt_add_one harg.le).le
  have h6 : (1 : ℝ) ≤ 1 / σ := (one_le_div hσ).mpr hσ1
  have h7 : (3 * c + 2) * (1 + σ * L) / σ = 3 * c / σ + 2 * (1 / σ) + (3 * c + 2) * L := by
    field_simp
  have h8 : 0 ≤ c * L := (mul_pos hc hL).le
  rw [h7]
  nlinarith

/-- Core (real numbers only): from `M ≤ 2^d/s` and `K ≤ A W/σ`,
    `C √(M L/n) √K ≤ C √(2^d A) √(L W/(n s σ))`. -/
theorem rate_core {C M L n s σ K A W : ℝ} (d : ℕ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hM : M ≤ 2 ^ d / s) (hs : 0 < s) (hσ : 0 < σ) (hL : 0 < L) (hn : 0 < n)
    (hK0 : 0 ≤ K) (hK : K ≤ A * W / σ) :
    C * Real.sqrt (M * L / n) * Real.sqrt K
      ≤ C * Real.sqrt (2 ^ d * A) * Real.sqrt (L * W / (n * s * σ)) := by
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hx : M * L / n * K ≤ 2 ^ d * A * (L * W / (n * s * σ)) := by
    have h1 : M * L / n * K ≤ 2 ^ d / s * L / n * K :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hM hL.le) hn.le) hK0
    have h0 : 0 ≤ 2 ^ d / s * L / n := by positivity
    have h2 : 2 ^ d / s * L / n * K ≤ 2 ^ d / s * L / n * (A * W / σ) :=
      mul_le_mul_of_nonneg_left hK h0
    have h3 : 2 ^ d / s * L / n * (A * W / σ) = 2 ^ d * A * (L * W / (n * s * σ)) := by
      field_simp
    linarith
  calc C * Real.sqrt (M * L / n) * Real.sqrt K
      = C * (Real.sqrt (M * L / n) * Real.sqrt K) := mul_assoc _ _ _
    _ = C * Real.sqrt (M * L / n * K) := by rw [Real.sqrt_mul' _ hK0]
    _ ≤ C * Real.sqrt (2 ^ d * A * (L * W / (n * s * σ))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) hC
    _ = C * (Real.sqrt (2 ^ d * A) * Real.sqrt (L * W / (n * s * σ))) := by
        rw [Real.sqrt_mul (mul_nonneg h2d hA)]
    _ = C * Real.sqrt (2 ^ d * A) * Real.sqrt (L * W / (n * s * σ)) := (mul_assoc _ _ _).symm

/-- Core for the Poisson-tail term: `4M/n² ≤ 4·2^d · L(1+σL)/(n s σ)` when `M ≤ 2^d/s`, `σ ≤ 1`
    and `L n ≥ 1` (LINEAR in the rate quantity, not its square root). -/
theorem tail_rate_core {M L n s σ : ℝ} (d : ℕ) (hM : M ≤ 2 ^ d / s) (hs : 0 < s) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hL : 0 < L) (hn : 0 < n) (hLn : 1 ≤ L * n) :
    4 * M / n ^ 2 ≤ 4 * 2 ^ d * (L * (1 + σ * L) / (n * s * σ)) := by
  have hn2 : 0 < n ^ 2 := pow_pos hn 2
  have h1 : 4 * M / n ^ 2 ≤ 4 * (2 ^ d / s) / n ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) hn2.le
  have hσL : 0 < σ * L := mul_pos hσ hL
  have key : 1 / (s * n ^ 2) ≤ L * (1 + σ * L) / (n * s * σ) := by
    rw [div_le_div_iff₀ (mul_pos hs hn2) (mul_pos (mul_pos hn hs) hσ)]
    have h3 : σ ≤ L * n * (1 + σ * L) := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ L * n) hσL.le]
    nlinarith [mul_nonneg (mul_pos hs hn).le (sub_nonneg.2 h3)]
  have h2 : 4 * (2 ^ d / s) / n ^ 2 = 4 * 2 ^ d * (1 / (s * n ^ 2)) := by
    field_simp
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left key (by positivity))

/-- **Stage 1, kernel.** For `0 < σ ≤ 1`, `c > 0`, `N ≥ 2` and every `k ≤ ⌈c/σ⌉`:
    `C₁ δ' √k ≤ C₁ √(2^d (c+1)) · (log N / (N σ^{d/2+1}))^{1/2}`. -/
theorem kernel_rate_det (d : ℕ) {σ c : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : 0 < c) {N : ℕ}
    (hN : 2 ≤ N) {k : ℕ} (hk : k ≤ ⌈c / σ⌉₊) :
    kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ) 0 * Real.log N / N)
        * Real.sqrt k
      ≤ kernelRateC d c * Real.sqrt (rateQ0 d σ N) := by
  have hL := (log_facts hN).1
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt σ ^ d := pow_pos (Real.sqrt_pos.mpr hσ) d
  have hk' : (k : ℝ) ≤ (c + 1) * 1 / σ :=
    (by exact_mod_cast hk : (k : ℝ) ≤ ((⌈c / σ⌉₊ : ℕ) : ℝ)).trans (nat_ceil_le_div hσ hσ1 hc)
  have h := rate_core (K := (k : ℝ)) d (kernelC1_nonneg d) (by linarith : (0 : ℝ) ≤ c + 1)
    (heatM_bound hσ hσ1 d) hs hσ hL hN' (Nat.cast_nonneg k) hk'
  rw [mul_one] at h
  unfold kernelRateC rateQ0
  exact h

/-- **Stage 1, trace.** For `0 < σ ≤ 1`, `c > 0`, `N ≥ 2` and `J = ⌈3c/σ + 2 log N⌉`:
    `C₁ δ' √J + 4M/N² ≤ C₁ √(2^d (3c+2)) √Q + 4·2^d Q` with `Q = rateQ d σ N`. -/
theorem trace_rate_det (d : ℕ) {σ c : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : 0 < c) {N : ℕ}
    (hN : 2 ≤ N) :
    kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ) 0 * Real.log N / N)
          * Real.sqrt ((⌈3 * c / σ + 2 * Real.log N⌉₊ : ℕ) : ℝ)
        + 4 * heatTorus d (2 * Real.pi ^ 2 * σ) 0 / (N : ℝ) ^ 2
      ≤ kernelC1 d * Real.sqrt (2 ^ d * (3 * c + 2)) * Real.sqrt (rateQ d σ N)
        + 4 * 2 ^ d * rateQ d σ N := by
  have hL := (log_facts hN).1
  have hLN := (log_facts hN).2
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt σ ^ d := pow_pos (Real.sqrt_pos.mpr hσ) d
  have h := rate_core (K := ((⌈3 * c / σ + 2 * Real.log N⌉₊ : ℕ) : ℝ)) d (kernelC1_nonneg d)
    (by linarith : (0 : ℝ) ≤ 3 * c + 2) (heatM_bound hσ hσ1 d) hs hσ hL hN'
    (Nat.cast_nonneg _) (ceil_trace_le hσ hσ1 hc hL)
  have h2 := tail_rate_core d (heatM_bound hσ hσ1 d) hs hσ hσ1 hL hN' hLN
  unfold rateQ
  exact add_le_add h h2

/-- `x ≤ √x` for `0 ≤ x ≤ 1`. -/
theorem sqrt_ge_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ Real.sqrt x := by
  have hs := Real.sqrt_nonneg x
  have hs1 : Real.sqrt x ≤ 1 := (Real.sqrt_le_sqrt h1).trans_eq Real.sqrt_one
  have e : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt h0
  nlinarith [mul_nonneg hs (sub_nonneg.2 hs1)]

/-- **Stage 1, trace, closed form.** If moreover `rateQ d σ N ≤ 1`, then
    `C₁ δ' √J + 4M/N² ≤ (C₁ √(2^d (3c+2)) + 4·2^d) · √(rateQ d σ N)`. -/
theorem trace_rate_det' (d : ℕ) {σ c : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hc : 0 < c) {N : ℕ}
    (hN : 2 ≤ N) (hQ : rateQ d σ N ≤ 1) :
    kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ) 0 * Real.log N / N)
          * Real.sqrt ((⌈3 * c / σ + 2 * Real.log N⌉₊ : ℕ) : ℝ)
        + 4 * heatTorus d (2 * Real.pi ^ 2 * σ) 0 / (N : ℝ) ^ 2
      ≤ traceRateC d c * Real.sqrt (rateQ d σ N) := by
  have h := trace_rate_det d hσ hσ1 hc hN
  have hq := sqrt_ge_self (rateQ_pos d hσ hN).le hQ
  have h2 : (0 : ℝ) ≤ 4 * 2 ^ d := by positivity
  have h3 := mul_le_mul_of_nonneg_left hq h2
  have e : traceRateC d c * Real.sqrt (rateQ d σ N)
      = kernelC1 d * Real.sqrt (2 ^ d * (3 * c + 2)) * Real.sqrt (rateQ d σ N)
        + 4 * 2 ^ d * Real.sqrt (rateQ d σ N) := by
    unfold traceRateC
    ring
  rw [e]
  linarith

/-- If `b ≤ N σ^{d/2} σ / (log N (1 + σ log N)) · w`, then `rateQ · b ≤ w`. -/
theorem rateQ_mul_le (d : ℕ) {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 2 ≤ N) {b w : ℝ}
    (hb : b ≤ (N : ℝ) * Real.sqrt σ ^ d * σ / (Real.log N * (1 + σ * Real.log N)) * w) :
    rateQ d σ N * b ≤ w := by
  have hL := (log_facts hN).1
  have hN' : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt σ ^ d := pow_pos (Real.sqrt_pos.mpr hσ) d
  have h1 : 0 < 1 + σ * Real.log N := by nlinarith [mul_pos hσ hL]
  have hX : 0 < (N : ℝ) * Real.sqrt σ ^ d * σ := mul_pos (mul_pos hN' hs) hσ
  have hY : 0 < Real.log N * (1 + σ * Real.log N) := mul_pos hL h1
  rw [div_mul_eq_mul_div, le_div_iff₀ hY] at hb
  unfold rateQ
  rw [div_mul_eq_mul_div, div_le_iff₀ hX]
  nlinarith [hb]

/-- Under `N σ_N^{d/2+1}/log N → ∞` the rate quantity is eventually `≤ 1`. -/
theorem eventually_rateQ_le_one (d : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᶠ N : ℕ in atTop, rateQ d (σ N) N ≤ 1 := by
  filter_upwards [hσ, (regime_log d σ hσ hreg).eventually_ge_atTop 1, eventually_ge_atTop 2]
    with N h1 h2 h4
  have h5 : (1 : ℝ) ≤ (N : ℝ) * Real.sqrt (σ N) ^ d * σ N
      / (Real.log N * (1 + σ N * Real.log N)) * 1 := by
    rw [mul_one]; exact h2
  have h6 := rateQ_mul_le d h1.1 h4 h5
  linarith

/-! ### Stage 2: almost sure statements with a rate -/

/-- **Kernel with a rate, almost surely.** Independent uniform points on the flat torus of
    dimension `d ≥ 1`, kernel variance `σ_N` (`σ = ξ²`), fixed `c > 0`. If eventually `0 < σ_N ≤ 1`
    and `N σ_N^{d/2+1}/log N → ∞`, then almost surely, for all large `N`, all `1 ≤ k ≤ ⌈c/σ_N⌉` and
    all entries, `|N P^k(a,i) - p_{kσ_N}(x_a - x_i)| ≤ C₁ √(2^d (c+1)) (log N/(N σ_N^{d/2+1}))^{1/2} m_k`. -/
theorem kernel_rate {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ ⌈c / σ N⌉₊ → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k) a i
            - heatP d (σ N) k (X a ω - X i ω)|
          ≤ kernelRateC d c * Real.sqrt (rateQ0 d (σ N) N)
            * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 := by
  have hK : ∀ᶠ N in atTop, 0 < ⌈c / σ N⌉₊ := by
    filter_upwards [hσ] with N h1
    exact Nat.ceil_pos.mpr (div_pos hc h1.1)
  filter_upwards [kernel_theorem_G28_regime d hd X h_indep hX hlaw σ (fun N => ⌈c / σ N⌉₊)
      hσ hK (regime_ceil d σ hc hσ hreg)] with ω hω
  filter_upwards [hω, hσ, eventually_ge_atTop 2] with N h1 h3 h4 k hk1 hk2 a i
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hσ0 := h3.1
  have hm : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 :=
    (heatTorus_zero_pos (by positivity) d).le
  exact (h1 k hk1 hk2 a i).trans
    (mul_le_mul_of_nonneg_right (kernel_rate_det d h3.1 h3.2 hc h4 hk2) hm)

/-- From the diagonal entries to the ratio `Tr B / m`. -/
theorem ratio_from_entries {N : ℕ} (hN : 0 < N) (B : Matrix (Fin N) (Fin N) ℝ) {m E : ℝ}
    (hm : 0 < m) (h : ∀ a : Fin N, |(N : ℝ) * B a a - m| ≤ E * m) :
    |B.trace / m - 1| ≤ E := by
  have ht := trace_from_diagonal hN B h
  have hm0 := hm.ne'
  have e : B.trace / m - 1 = (B.trace - m) / m := by
    field_simp
  rw [e, abs_div, abs_of_pos hm, div_le_iff₀ hm]
  exact ht

/-- **First display of `cor:kernel-trace` with a rate, almost surely.** Same hypotheses. Almost
    surely, for all large `N` and all `1 ≤ k ≤ ⌈c/σ_N⌉`:
    `|Tr P^k / m_k - 1| ≤ C₁ √(2^d (c+1)) (log N/(N σ_N^{d/2+1}))^{1/2}`, `m_k = p_{kσ_N}(0)`. -/
theorem kernel_trace_rate {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ ⌈c / σ N⌉₊ →
        |((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k).trace
            / heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 - 1|
          ≤ kernelRateC d c * Real.sqrt (rateQ0 d (σ N) N) := by
  filter_upwards [kernel_rate d hd X h_indep hX hlaw σ hc hσ hreg] with ω hω
  filter_upwards [hω, hσ, eventually_ge_atTop 2] with N h1 h3 h4 k hk1 hk2
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hσ0 := h3.1
  have hm : 0 < heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 :=
    heatTorus_zero_pos (by positivity) d
  refine ratio_from_entries (by omega) _ hm (fun a => ?_)
  have h := h1 k hk1 hk2 a a
  rw [sub_self, heatP_of_ne d (σ N) (by omega : k ≠ 0)] at h
  exact h

/-- **Second display of `cor:kernel-trace` with a rate, almost surely.** Independent uniform points
    on the flat torus of dimension `d ≥ 1`, kernel variance `σ_N` (`σ = ξ²`), fixed `c > 0`. If
    eventually `0 < σ_N ≤ 1` and `N σ_N^{d/2+1}/log N → ∞` (with `σ = ξ²`: `N ξ^{d+2}/log N → ∞`),
    then almost surely, for all large `N` and ALL real `τ` with `2 ≤ τ ≤ c/σ_N`:
    `|(Tr exp(τ(S-1)) - N e^{-τ})/T(τ) - 1| ≤ (C₁ √(2^d (3c+2)) + 4·2^d) · √(rateQ d σ_N N)`,
    `rateQ = log N (1 + σ_N log N)/(N σ_N^{d/2+1})`, `T(τ) = poissonMean = ∑_{j≥1} w_j(τ) m_j`.
    (The range of `τ` is empty unless `σ_N ≤ c/2`.) -/
theorem heat_trace_rate {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      ∀ τ : ℝ, 2 ≤ τ → τ ≤ c / σ N →
        |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d (σ N) τ - 1|
          ≤ traceRateC d c * Real.sqrt (rateQ d (σ N) N) := by
  have hreg' := regime_ceil_trace d σ hc hσ (regime_log d σ hσ hreg)
  filter_upwards [heat_trace_G29_regime d hd X h_indep hX hlaw σ
    (fun N => ⌈3 * c / σ N + 2 * Real.log N⌉₊) hσ (ceil_trace_ge_two σ hc hσ) hreg'] with ω hω
  filter_upwards [hω 1 one_pos, hσ, eventually_rateQ_le_one d σ hσ hreg, eventually_ge_atTop 2]
    with N h1 h3 hQ h4 τ hτ1 hτ2
  have hσ0 := h3.1
  have h5 : 3 * τ ≤ 3 * c / σ N := by
    have : 3 * c / σ N = 3 * (c / σ N) := by ring
    linarith
  have h6 := Nat.le_ceil (3 * c / σ N + 2 * Real.log N)
  have key : 3 * τ + 2 * Real.log N
      ≤ ((⌈3 * c / σ N + 2 * Real.log N⌉₊ : ℕ) : ℝ) + 1 := by linarith
  exact (h1 τ hτ1 key).1.trans (trace_rate_det' d h3.1 h3.2 hc h4 hQ)

/-! ### Stage 3: the bounds are `o(σ_N)` under `N σ_N^{d/2+3}/log N → ∞` -/

/-- Core of: `N σ^{d/2+3}/log N` large and `N/(log N)^{d+4}` large imply
    `σ² · N σ^{d/2+1}/(log N (1 + σ log N))` large. -/
theorem log_core3 {n σ L b : ℝ} (d : ℕ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hL : 1 ≤ L) (hn : 0 < n)
    (h1 : 2 * b ≤ n * Real.sqrt σ ^ d * σ ^ 3 / L) (h2 : 2 * b ≤ n / L ^ (d + 4)) :
    b ≤ n * Real.sqrt σ ^ d * σ / (L * (1 + σ * L)) * σ ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hr0 : 0 < Real.sqrt σ := Real.sqrt_pos.mpr hσ
  have hr1 : Real.sqrt σ ≤ 1 := (Real.sqrt_le_sqrt hσ1).trans_eq Real.sqrt_one
  have hsd : 0 < Real.sqrt σ ^ d := pow_pos hr0 d
  have hX : 0 ≤ n * Real.sqrt σ ^ d * σ ^ 3 :=
    (mul_pos (mul_pos hn hsd) (pow_pos hσ 3)).le
  have hden0 : 0 < L * (1 + σ * L) := mul_pos hL0 (by nlinarith [mul_pos hσ hL0])
  have e0 : n * Real.sqrt σ ^ d * σ / (L * (1 + σ * L)) * σ ^ 2
      = n * Real.sqrt σ ^ d * σ ^ 3 / (L * (1 + σ * L)) := by ring
  rw [e0]
  by_cases h : σ * L ≤ 1
  · have hden : L * (1 + σ * L) ≤ 2 * L := by
      nlinarith [mul_nonneg hL0.le (sub_nonneg.2 h)]
    calc b ≤ n * Real.sqrt σ ^ d * σ ^ 3 / L / 2 := by linarith
      _ = n * Real.sqrt σ ^ d * σ ^ 3 / (2 * L) := by rw [div_div, mul_comm L 2]
      _ ≤ n * Real.sqrt σ ^ d * σ ^ 3 / (L * (1 + σ * L)) :=
          div_le_div_of_nonneg_left hX hden0 hden
  · rw [not_le] at h
    have hσr : σ ≤ Real.sqrt σ := by
      have hr2 : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
      nlinarith [mul_nonneg hr0.le (sub_nonneg.2 hr1)]
    have hσL : 1 / L ≤ σ := ((div_lt_iff₀ hL0).2 h).le
    have hs : 1 / L ^ d ≤ Real.sqrt σ ^ d := by
      rw [← _root_.one_div_pow]
      exact pow_le_pow_left₀ (div_pos one_pos hL0).le (hσL.trans hσr) d
    have hs2 : (1 / L) ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ (div_pos one_pos hL0).le hσL 2
    have hden : L * (1 + σ * L) ≤ 2 * σ * L ^ 2 := by
      nlinarith [mul_nonneg hL0.le (by linarith : (0 : ℝ) ≤ σ * L - 1)]
    have hLd : (0 : ℝ) < L ^ d := pow_pos hL0 d
    have h00 : (0 : ℝ) ≤ (1 / L) ^ 2 := _root_.sq_nonneg _
    have hmid : n * (1 / L ^ d) * (1 / L) ^ 2 ≤ n * Real.sqrt σ ^ d * σ ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs hn.le) hs2 h00 (mul_pos hn hsd).le
    have e : n / L ^ (d + 4) / 2 = n * (1 / L ^ d) * (1 / L) ^ 2 * σ / (2 * σ * L ^ 2) := by
      rw [pow_add]
      field_simp
    have hden2 : 0 < 2 * σ * L ^ 2 := mul_pos (mul_pos two_pos hσ) (pow_pos hL0 2)
    calc b ≤ n / L ^ (d + 4) / 2 := by linarith
      _ = n * (1 / L ^ d) * (1 / L) ^ 2 * σ / (2 * σ * L ^ 2) := e
      _ ≤ n * Real.sqrt σ ^ d * σ ^ 2 * σ / (2 * σ * L ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmid hσ.le) hden2.le
      _ = n * Real.sqrt σ ^ d * σ ^ 3 / (2 * σ * L ^ 2) := by ring
      _ ≤ n * Real.sqrt σ ^ d * σ ^ 3 / (L * (1 + σ * L)) :=
          div_le_div_of_nonneg_left hX hden0 hden

/-- The regime `N σ^{d/2+3}/log N → ∞` implies the regime `N σ^{d/2+1}/log N → ∞` (as `σ ≤ 1`). -/
theorem regime_of_regime3 (d : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ hreg3
  filter_upwards [hσ, eventually_ge_atTop 2] with N h1 h4
  have hL := (log_facts h4).1
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs : 0 ≤ Real.sqrt (σ N) ^ d := pow_nonneg (Real.sqrt_nonneg _) d
  have h0 := h1.1
  have h01 := h1.2
  have h3 : σ N ^ 3 ≤ σ N := by
    nlinarith [mul_pos h0 h0, mul_nonneg (mul_pos h0 h0).le (sub_nonneg.2 h01),
      mul_nonneg h0.le (sub_nonneg.2 h01)]
  show (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N
      ≤ (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (mul_nonneg hN' hs)) hL.le

/-- `N σ^{d/2+3}/log N → ∞` implies `σ² · N σ^{d/2+1}/(log N (1 + σ log N)) → ∞`, i.e.
    `rateQ / σ² → 0`. -/
theorem regime_log3 (d : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N
      / (Real.log N * (1 + σ N * Real.log N)) * σ N ^ 2) atTop atTop := by
  refine tendsto_atTop.2 (fun b => ?_)
  filter_upwards [hσ, hreg3.eventually_ge_atTop (2 * b),
    (tendsto_nat_div_log_pow (d + 4)).eventually_ge_atTop (2 * b),
    eventually_ge_atTop 3] with N h1 h2 h3 h4
  have hN : (3 : ℝ) ≤ N := by exact_mod_cast h4
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  exact log_core3 d h1.1 h1.2 hL (by linarith) h2 h3

/-- Core: `Q b ≤ σ²` and `C²/η² ≤ b` imply `C √Q ≤ η σ`. -/
theorem rate_small_core {C η Q σ b : ℝ} (hC : 0 ≤ C) (hη : 0 < η) (hσ : 0 < σ) (hQ0 : 0 ≤ Q)
    (hQ : Q * b ≤ σ ^ 2) (hb : C ^ 2 / η ^ 2 ≤ b) : C * Real.sqrt Q ≤ η * σ := by
  have hη2 : 0 < η ^ 2 := pow_pos hη 2
  have h1 : C ^ 2 ≤ b * η ^ 2 := (div_le_iff₀ hη2).1 hb
  have h2 : C ^ 2 * Q ≤ (η * σ) ^ 2 := by
    have h3 : C ^ 2 * Q ≤ b * η ^ 2 * Q := mul_le_mul_of_nonneg_right h1 hQ0
    have h4 : η ^ 2 * (Q * b) ≤ η ^ 2 * σ ^ 2 := mul_le_mul_of_nonneg_left hQ hη2.le
    nlinarith [h3, h4]
  have e : C * Real.sqrt Q = Real.sqrt (C ^ 2 * Q) := by
    rw [Real.sqrt_mul (_root_.sq_nonneg C), Real.sqrt_sq hC]
  rw [e]
  exact (Real.sqrt_le_sqrt h2).trans_eq (Real.sqrt_sq (mul_pos hη hσ).le)

/-- **The rate is `o(σ_N)`.** If eventually `0 < σ_N ≤ 1` and `N σ_N^{d/2+3}/log N → ∞` (with
    `σ = ξ²`: `N ξ^{d+6}/log N → ∞`), then for every `C ≥ 0` and `η > 0`, eventually
    `C √(rateQ d σ_N N) ≤ η σ_N`. -/
theorem eventually_rate_small (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, C * Real.sqrt (rateQ d (σ N) N) ≤ η * σ N := by
  filter_upwards [hσ, (regime_log3 d σ hσ hreg3).eventually_ge_atTop (C ^ 2 / η ^ 2),
    eventually_ge_atTop 2] with N h1 h2 h4
  exact rate_small_core hC hη h1.1 (rateQ_pos d h1.1 h4).le (rateQ_mul_le d h1.1 h4 h2) le_rfl

/-- **Second display, `o(σ_N)`, almost surely.** If eventually `0 < σ_N ≤ 1` and
    `N σ_N^{d/2+3}/log N → ∞` (with `σ = ξ²`: `N ξ^{d+6}/log N → ∞`), then almost surely, for every
    `η > 0`, for all large `N` and ALL real `τ` with `2 ≤ τ ≤ c/σ_N`:
    `|(Tr exp(τ(S-1)) - N e^{-τ})/T(τ) - 1| ≤ traceRateC · √rateQ` and `traceRateC · √rateQ ≤ η σ_N`.
    (Comparison with `Tr e^{tΔ}` and the coefficient `d(d+2)/(8τ)` are NOT part of this.) -/
theorem heat_trace_rate_small {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
      ∀ τ : ℝ, 2 ≤ τ → τ ≤ c / σ N →
        |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d (σ N) τ - 1|
          ≤ traceRateC d c * Real.sqrt (rateQ d (σ N) N)
        ∧ traceRateC d c * Real.sqrt (rateQ d (σ N) N) ≤ η * σ N := by
  filter_upwards [heat_trace_rate d hd X h_indep hX hlaw σ hc hσ
    (regime_of_regime3 d σ hσ hreg3)] with ω hω
  intro η hη
  filter_upwards [hω, eventually_rate_small d (traceRateC_nonneg d c) σ hσ hreg3 hη]
    with N h1 h2 τ hτ1 hτ2
  exact ⟨h1 τ hτ1 hτ2, h2⟩

/-- **First display, `o(σ_N)`, almost surely.** Under `N σ_N^{d/2+3}/log N → ∞`, almost surely, for
    every `η > 0`, for all large `N` and all `1 ≤ k ≤ ⌈c/σ_N⌉`:
    `|Tr P^k/m_k - 1| ≤ kernelRateC · √rateQ0` and `kernelRateC · √rateQ0 ≤ η σ_N`. -/
theorem kernel_trace_rate_small {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ ⌈c / σ N⌉₊ →
        |((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k).trace
            / heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 - 1|
          ≤ kernelRateC d c * Real.sqrt (rateQ0 d (σ N) N)
        ∧ kernelRateC d c * Real.sqrt (rateQ0 d (σ N) N) ≤ η * σ N := by
  filter_upwards [kernel_trace_rate d hd X h_indep hX hlaw σ hc hσ
    (regime_of_regime3 d σ hσ hreg3)] with ω hω
  intro η hη
  filter_upwards [hω, hσ, eventually_ge_atTop 2,
    eventually_rate_small d (kernelRateC_nonneg d c) σ hσ hreg3 hη]
    with N h1 h3 h4 h2 k hk1 hk2
  refine ⟨h1 k hk1 hk2, le_trans ?_ h2⟩
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (rateQ0_le_rateQ d h3.1 h4)) (kernelRateC_nonneg d c)

end TraceRates

/-! ### The population side of the sharp rate: the exactly solvable case (`thm:rate`) -/

namespace PopulationRate

/-!
Conventions. In this block `σ` is the `σ` of the PAPER (`P_σ = e^{σΔ}`, `σ = c_h ξ²/2`), `t` is the
time of the paper and `τ = t/σ`. (The `σ` of the other Lean files is `ξ² = 2σ`; see `subTr_torus`.)
The statements are about an abstract "spectrum" `lam : ι → ℝ` with `lam ≥ 0` and
`∑_k e^{-s lam_k} < ∞` for every `s > 0` (`IsSpectrum`), and are then instantiated for the flat
torus, `lam_n = 4π²|n|²`, `n ∈ ℤ^d` (`torusLam`). With
* `heatTr lam s = ∑_k e^{-s lam_k}` (the heat trace `Θ(s)`),
* `heatMom lam p s = ∑_k lam_k^p e^{-s lam_k}` (`= (-1)^p Θ^{(p)}(s)`: `heatMom_hasDerivAt`),
* `subTr lam σ t = ∑_k [e^{-τ(1 - e^{-σ lam_k})} - e^{-τ}]` (`T_σ(t)`, equation `eq:Tsigma`),
the block proves, without hypotheses other than `IsSpectrum`:
* `rate_i`: `T_σ(t) = ∑_{j≥1} e^{-τ} τ^j/j! Θ(jσ)` (`thm:rate`(i), first statement);
* `rate_ii`: `thm:rate`(ii), with the constants of the paper, for all `σ, t > 0`;
* `rate_iii`: `thm:rate`(iii), with the constants of the paper, for `t ≥ σ > 0`;
* `rate_iii_simple`, `rate_ratio`: the same with the derivatives at `t/2` bounded by `Θ(t/4)`,
  and divided by `Θ(t)`.
For the torus (no hypothesis at all):
* `subTr_torus`: `T_σ(t) = TraceG29.poissonMean d (2σ) (t/σ)`; `heatTr_torus`:
  `Θ(s) = heatTorus d (4π² s) 0`;
* `jacobi_lat`, `jacobi_first`, `jacobi_second`: the Jacobi identity
  `∑ e^{-c|n|²} = (π/c)^{d/2} ∑ e^{-(π²/c)|n|²}` and its first two derivatives in `c`;
* `torus_moment_ratio`: `|t² Θ''(t)/Θ(t) - d(d+2)/4| ≤ (2d+12) e^{-1/(16t)} (1 + √(16πt))^d`;
* `rate_exact_torus`, `rate_exact_torus_explicit`: the expansion `eq:rateexact`,
  `T_σ(t)/Θ(t) = 1 + d(d+2)/(8τ) + remainder`, with an explicit remainder for `0 < σ ≤ t ≤ 1`.

NOT proved here and NOT claimed:
* nothing about a manifold, a Laplacian or an operator `e^{σΔ}`: the "closed Riemannian manifold" of
  `thm:rate` enters only through its list of eigenvalues, and the second statement of (i),
  `Tr P_σ^k = Θ(kσ)`, appears only as `heatTr_pow` (`∑_k (e^{-σ lam_k})^j = Θ(jσ)`);
* `eq:rateexact` for a general manifold (it needs the heat-trace asymptotics
  `Θ(t) = (4πt)^{-d/2}(Vol + O(t))` with derivatives); only the flat torus `ℝ^d/ℤ^d` is treated;
* the constants of `rate_exact_torus_explicit` are far from sharp (the remainder `832·6^d/τ²` is
  below the main term `d(d+2)/(8τ)` only for `τ` of the order `10^4·6^{d-1}` and larger);
* the sentence of the paper "of the order `σ/t` ... and not smaller" is NOT a consequence of the
  expansion for `t` of order one: the term written `O(σ)` in `eq:rateexact` is
  `(σ/2t)(t²Θ''(t)/Θ(t) - d(d+2)/4)`, and on the unit torus `t²Θ''(t)/Θ(t)` tends to `0`, not to
  `d(d+2)/4`, as `t` grows (it is within `(2d+12) 9^d e^{-1/(16t)}` of `d(d+2)/4` only for small `t`).
-/

/-! #### Stage A: one mode -/

/-- `walk_mode_ge` of the core file for the real exponential: `b ≤ a`. -/
theorem real_walk_mode_ge {τ : ℝ} (hτ : 0 ≤ τ) (u : ℝ) :
    Real.exp (-(τ * u)) ≤ Real.exp (-(τ * (1 - Real.exp (-u)))) :=
  CTG.HeatTrace.walk_mode_ge real_isExp hτ u

/-- `walk_mode_le` of the core file for the real exponential (low mode, `0 ≤ u ≤ 1`). -/
theorem real_walk_mode_le {τ u : ℝ} (hτ : 0 ≤ τ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-(τ * u))
      ≤ τ * u * u / 2 * Real.exp (-(τ * u / 2)) :=
  CTG.HeatTrace.walk_mode_le real_isExp2 hτ hu0 hu1

/-- `walk_high_mode` of the core file for the real exponential. -/
theorem real_walk_high_mode {τ s s0 : ℝ} (hτ : 0 ≤ τ) (hs0 : 0 ≤ s) (hs : s ≤ s0) :
    Real.exp (-τ) * (Real.exp (τ * s) - 1) ≤ τ * s * Real.exp (-(τ * (1 - s0))) :=
  CTG.HeatTrace.walk_high_mode real_isExp hτ hs0 hs

/-- `walk_mode_second` of the core file for the real exponential (low mode, `0 ≤ u ≤ 1`). -/
theorem real_walk_mode_second {τ u : ℝ} (hτ : 0 ≤ τ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    -(τ * u * u * u / 6 * Real.exp (-(τ * u)))
        ≤ Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-(τ * u))
            - τ * u * u / 2 * Real.exp (-(τ * u)) ∧
    Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-(τ * u))
            - τ * u * u / 2 * Real.exp (-(τ * u))
        ≤ (τ * u * u / 2) * (τ * u * u / 2) / 2 * Real.exp (-(τ * u / 2)) :=
  CTG.HeatTrace.walk_mode_second real_isExp3 hτ hu0 hu1

theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-1 : ℝ)]

theorem quarter_le_exp_neg_one : 1 / 4 ≤ Real.exp (-1) := by
  have h1 := exp_one_le_four
  have h2 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (-1 : ℝ)]

/-- The graph mode minus the high-frequency constant: `0 ≤ a - e^{-τ} ≤ τ e^{-u}`. -/
theorem mode_sub_bounds {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    0 ≤ Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-τ) ∧
    Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-τ) ≤ τ * Real.exp (-u) := by
  have hEu := Real.exp_pos (-u)
  have k2 : Real.exp (-(τ * (1 - Real.exp (-u))))
      = Real.exp (-τ) * Real.exp (τ * Real.exp (-u)) := by
    rw [← Real.exp_add]; congr 1; ring
  constructor
  · have : Real.exp (-τ) ≤ Real.exp (-(τ * (1 - Real.exp (-u)))) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ hEu.le])
    linarith
  · have k1 := real_walk_high_mode (s := Real.exp (-u)) (s0 := 1) hτ hEu.le
      (Real.exp_le_one_iff.2 (by linarith))
    have k3 : Real.exp (-(τ * (1 - 1))) = 1 := by norm_num
    rw [k3] at k1
    rw [k2]; linarith

/-- Lower bound of `thm:rate`(ii) for one mode, low or high (`u = σλ`, `τu = tλ`):
    `a - e^{-τ} - b ≥ -(e^{1-τ} e^{-u} + e^{-τ/2} e^{-τu/2})`. -/
theorem mode_lower {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    -(Real.exp (1 - τ) * Real.exp (-u) + Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2)))
      ≤ Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-τ) - Real.exp (-(τ * u)) := by
  have hEu := Real.exp_pos (-u)
  rcases le_total u 1 with h | h
  · have h1 := real_walk_mode_ge hτ u
    have h2 : Real.exp (-τ) ≤ Real.exp (1 - τ) * Real.exp (-u) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have h3 : 0 ≤ Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2)) := by positivity
    linarith
  · have h1 := (mode_sub_bounds hτ hu).1
    have h2 : Real.exp (-(τ * u)) ≤ Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ (sub_nonneg.2 h)])
    have h3 : 0 ≤ Real.exp (1 - τ) * Real.exp (-u) := by positivity
    linarith

/-- Upper bound of `thm:rate`(ii) for one mode, low or high:
    `a - e^{-τ} - b ≤ (τu²/2) e^{-τu/2} + τ e^{-u} e^{-(1-1/e)τ}`. -/
theorem mode_upper {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-τ) - Real.exp (-(τ * u))
      ≤ τ * u * u / 2 * Real.exp (-(τ * u / 2))
        + τ * Real.exp (-u) * Real.exp (-(τ * (1 - Real.exp (-1)))) := by
  have hEu := Real.exp_pos (-u)
  rcases le_total u 1 with h | h
  · have h1 := real_walk_mode_le hτ hu h
    have h3 : 0 ≤ τ * Real.exp (-u) * Real.exp (-(τ * (1 - Real.exp (-1)))) := by positivity
    linarith [Real.exp_pos (-τ)]
  · have h1 := real_walk_high_mode (s := Real.exp (-u)) (s0 := Real.exp (-1))
      hτ hEu.le (Real.exp_le_exp.2 (by linarith))
    have h2 : Real.exp (-(τ * (1 - Real.exp (-u))))
        = Real.exp (-τ) * Real.exp (τ * Real.exp (-u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : 0 ≤ τ * u * u / 2 * Real.exp (-(τ * u / 2)) := by positivity
    rw [h2]
    linarith [Real.exp_pos (-(τ * u))]

theorem high_aux {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) * (1 + x ^ 2 / 2) ≤ 5 * Real.exp (-(x / 2)) := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ x / 2 by linarith)
  have h2 : Real.exp (-(x / 2)) * Real.exp (x / 2) = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : 1 + x ^ 2 / 2 ≤ 5 * Real.exp (x / 2) := by nlinarith [h1, hx, pow_two_nonneg x]
  have hp := Real.exp_pos (-(x / 2))
  rw [h3]
  calc Real.exp (-(x / 2)) * Real.exp (-(x / 2)) * (1 + x ^ 2 / 2)
      ≤ Real.exp (-(x / 2)) * Real.exp (-(x / 2)) * (5 * Real.exp (x / 2)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 5 * Real.exp (-(x / 2)) * (Real.exp (-(x / 2)) * Real.exp (x / 2)) := by ring
    _ = 5 * Real.exp (-(x / 2)) := by rw [h2]; ring

/-- `thm:rate`(iii) for one mode, low or high, for `τ ≥ 1`:
    `|a - e^{-τ} - b - (τu²/2) b| ≤ ((τu²/2)²/2 + τu³/6) e^{-τu/2}
       + 3(1+τ) e^{-τ/4} (e^{-u} + e^{-τu/4})`. -/
theorem mode_third {τ u : ℝ} (hτ : 1 ≤ τ) (hu : 0 ≤ u) :
    |Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-τ) - Real.exp (-(τ * u))
        - τ * u * u / 2 * Real.exp (-(τ * u))|
      ≤ (τ * u * u / 2 * (τ * u * u / 2) / 2 + τ * u * u * u / 6) * Real.exp (-(τ * u / 2))
        + 3 * (1 + τ) * Real.exp (-(τ / 4)) * (Real.exp (-u) + Real.exp (-(τ * u / 4))) := by
  have hτ0 : 0 ≤ τ := by linarith
  have hE4 := Real.exp_pos (-(τ / 4))
  have hEu := Real.exp_pos (-u)
  have hEx4 := Real.exp_pos (-(τ * u / 4))
  have hEx2 := Real.exp_pos (-(τ * u / 2))
  have hEx := Real.exp_pos (-(τ * u))
  have hEt := Real.exp_pos (-τ)
  have h5 : 0 ≤ τ * u * u * u / 6 := by positivity
  have h6 : 0 ≤ τ * u * u / 2 * (τ * u * u / 2) / 2 := by positivity
  have hc : 0 ≤ τ * u * u / 2 := by positivity
  have q5 : 0 ≤ τ * u * u * u / 6 * Real.exp (-(τ * u / 2)) := mul_nonneg h5 hEx2.le
  have q6 : 0 ≤ τ * u * u / 2 * (τ * u * u / 2) / 2 * Real.exp (-(τ * u / 2)) :=
    mul_nonneg h6 hEx2.le
  have q7 : 0 ≤ 3 * (1 + τ) * Real.exp (-(τ / 4)) * Real.exp (-(τ * u / 4)) := by positivity
  have q8 : 0 ≤ 3 * (1 + τ) * Real.exp (-(τ / 4)) * Real.exp (-u) := by positivity
  rcases le_total u 1 with h | h
  · obtain ⟨l1, l2⟩ := real_walk_mode_second hτ0 hu h
    have h1 : Real.exp (-τ) ≤ Real.exp (-(τ / 4)) := Real.exp_le_exp.2 (by linarith)
    have h2 : 1 / 4 ≤ Real.exp (-u) :=
      le_trans quarter_le_exp_neg_one (Real.exp_le_exp.2 (by linarith))
    have h3 : Real.exp (-τ) ≤ 3 * (1 + τ) * Real.exp (-(τ / 4)) * Real.exp (-u) := by
      have a1 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 3 * (1 + τ) by linarith)
      have a2 : Real.exp (-(τ / 4)) * 1 ≤ Real.exp (-(τ / 4)) * (3 * (1 + τ) * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left (by linarith) hE4.le
      linarith
    have h4 : Real.exp (-(τ * u)) ≤ Real.exp (-(τ * u / 2)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ0 hu])
    have h4' := mul_le_mul_of_nonneg_left h4 h5
    rw [abs_le]
    constructor
    · linarith
    · linarith
  · have hx : 0 ≤ τ * u := mul_nonneg hτ0 hu
    have k0 := mode_sub_bounds hτ0 hu
    have k1 := real_walk_high_mode (s := Real.exp (-u)) (s0 := Real.exp (-1))
      hτ0 hEu.le (Real.exp_le_exp.2 (by linarith))
    have k2 : Real.exp (-(τ * (1 - Real.exp (-u))))
        = Real.exp (-τ) * Real.exp (τ * Real.exp (-u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have k3 : Real.exp (-(τ * (1 - Real.exp (-1)))) ≤ Real.exp (-(τ / 4)) :=
      Real.exp_le_exp.2 (by nlinarith [exp_neg_one_le_half])
    have k4 : Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-τ)
        ≤ τ * Real.exp (-u) * Real.exp (-(τ / 4)) := by
      have := mul_le_mul_of_nonneg_left k3 (show 0 ≤ τ * Real.exp (-u) by positivity)
      rw [k2]; linarith
    have k5 : τ * u * u / 2 ≤ (τ * u) ^ 2 / 2 := by
      nlinarith [mul_nonneg (mul_nonneg hx hu) (show 0 ≤ τ - 1 by linarith)]
    have k6 := high_aux hx
    have k7 : Real.exp (-(τ * u / 2)) ≤ Real.exp (-(τ / 4)) * Real.exp (-(τ * u / 4)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ0 (sub_nonneg.2 h)])
    have k8 : Real.exp (-(τ * u)) + τ * u * u / 2 * Real.exp (-(τ * u))
        ≤ 5 * (Real.exp (-(τ / 4)) * Real.exp (-(τ * u / 4))) := by
      have := mul_le_mul_of_nonneg_left k5 hEx.le
      linarith
    have q1 : 0 ≤ (3 + 2 * τ) * (Real.exp (-(τ / 4)) * Real.exp (-u)) := by positivity
    have q2 : 0 ≤ (3 * (1 + τ) - 5) * (Real.exp (-(τ / 4)) * Real.exp (-(τ * u / 4))) :=
      mul_nonneg (by linarith) (by positivity)
    have q3 : 0 ≤ τ * u * u / 2 * Real.exp (-(τ * u)) := mul_nonneg hc hEx.le
    rw [abs_le]
    constructor
    · linarith [k0.1]
    · linarith [k0.1]

/-- The same in the variables of the paper: `τ = t/σ`, `u = σ l`, for `t ≥ σ > 0`, `l ≥ 0`. -/
theorem mode_third_scaled {σ t l : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) (hl : 0 ≤ l) :
    |Real.exp (-(t / σ * (1 - Real.exp (-(σ * l))))) - Real.exp (-(t / σ)) - Real.exp (-(t * l))
        - σ * t / 2 * (l ^ 2 * Real.exp (-(t * l)))|
      ≤ (σ / t) ^ 2 * (t ^ 4 / 8 * (l ^ 4 * Real.exp (-(t / 2 * l)))
            + t ^ 3 / 6 * (l ^ 3 * Real.exp (-(t / 2 * l))))
        + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4))
            * (Real.exp (-(σ * l)) + Real.exp (-(t / 4 * l))) := by
  have hσ' : σ ≠ 0 := hσ.ne'
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have ht' : t ≠ 0 := ht.ne'
  have key := mode_third (τ := t / σ) (u := σ * l) (by rw [le_div_iff₀ hσ]; linarith)
    (mul_nonneg hσ.le hl)
  have e1 : t / σ * (σ * l) = t * l := by field_simp
  have e2 : t / σ * (σ * l) * (σ * l) / 2 = σ * t / 2 * l ^ 2 := by field_simp
  have e3 : t / σ * (σ * l) * (σ * l) * (σ * l) / 6 = (σ / t) ^ 2 * (t ^ 3 / 6 * l ^ 3) := by
    field_simp
  have e4 : t * l / 2 = t / 2 * l := by ring
  have e5 : t * l / 4 = t / 4 * l := by ring
  have e6 : σ * t / 2 * l ^ 2 * (σ * t / 2 * l ^ 2) / 2 = (σ / t) ^ 2 * (t ^ 4 / 8 * l ^ 4) := by
    field_simp; ring
  rw [e2, e3, e1, e4, e5, e6] at key
  have el : Real.exp (-(t / σ * (1 - Real.exp (-(σ * l))))) - Real.exp (-(t / σ))
        - Real.exp (-(t * l)) - σ * t / 2 * (l ^ 2 * Real.exp (-(t * l)))
      = Real.exp (-(t / σ * (1 - Real.exp (-(σ * l))))) - Real.exp (-(t / σ))
        - Real.exp (-(t * l)) - σ * t / 2 * l ^ 2 * Real.exp (-(t * l)) := by ring
  rw [el]
  refine key.trans (le_of_eq ?_)
  ring

/-! #### Stage B: summation over a spectrum -/

section Spectrum

variable {ι : Type*} (lam : ι → ℝ)

/-- The heat trace `Θ(s) = ∑_k e^{-s λ_k}`. -/
noncomputable def heatTr (s : ℝ) : ℝ := ∑' k, Real.exp (-(s * lam k))

/-- The moments `∑_k λ_k^p e^{-s λ_k}` (`= (-1)^p Θ^{(p)}(s)`). -/
noncomputable def heatMom (p : ℕ) (s : ℝ) : ℝ := ∑' k, lam k ^ p * Real.exp (-(s * lam k))

/-- The subtracted trace of the exactly solvable walk, equation `eq:Tsigma`, with `τ = t/σ`:
    `T_σ(t) = ∑_k [e^{-τ(1 - e^{-σ λ_k})} - e^{-τ}]`. -/
noncomputable def subTr (σ t : ℝ) : ℝ :=
  ∑' k, (Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k))))) - Real.exp (-(t / σ)))

/-- What is used of the list of eigenvalues: they are non-negative and every heat sum converges. -/
structure IsSpectrum : Prop where
  nonneg : ∀ k, 0 ≤ lam k
  summable : ∀ s : ℝ, 0 < s → Summable fun k => Real.exp (-(s * lam k))

variable {lam}

theorem heatTr_hasSum (h : IsSpectrum lam) {s : ℝ} (hs : 0 < s) :
    HasSum (fun k => Real.exp (-(s * lam k))) (heatTr lam s) := (h.summable s hs).hasSum

theorem heatTr_nonneg (s : ℝ) : 0 ≤ heatTr lam s := tsum_nonneg fun _ => (Real.exp_pos _).le

/-- The heat trace decreases. -/
theorem heatTr_anti (h : IsSpectrum lam) {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') :
    heatTr lam s' ≤ heatTr lam s :=
  hasSum_le (fun k => Real.exp_le_exp.2
      (by nlinarith [mul_nonneg (sub_nonneg.2 hss) (h.nonneg k)]))
    (heatTr_hasSum h (lt_of_lt_of_le hs hss)) (heatTr_hasSum h hs)

/-- All moments of the heat sums converge. -/
theorem mom_summable (h : IsSpectrum lam) (p : ℕ) {s : ℝ} (hs : 0 < s) :
    Summable fun k => lam k ^ p * Real.exp (-(s * lam k)) := by
  have hs2 : 0 < s / 2 := by linarith
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (h.nonneg k) p) (Real.exp_pos _).le) (fun k => ?_)
    ((h.summable (s / 2) hs2).mul_left ((p.factorial : ℝ) / (s / 2) ^ p))
  have hy : 0 ≤ s / 2 * lam k := mul_nonneg hs2.le (h.nonneg k)
  have h1 := Real.pow_div_factorial_le_exp (x := s / 2 * lam k) hy p
  have hf : (0 : ℝ) < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hsp : 0 < (s / 2) ^ p := pow_pos hs2 p
  have h2 : lam k ^ p ≤ (p.factorial : ℝ) / (s / 2) ^ p * Real.exp (s / 2 * lam k) := by
    rw [div_le_iff₀ hf, mul_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hsp]
    linarith
  have h3 : Real.exp (s / 2 * lam k) * Real.exp (-(s * lam k)) = Real.exp (-(s / 2 * lam k)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc lam k ^ p * Real.exp (-(s * lam k))
      ≤ (p.factorial : ℝ) / (s / 2) ^ p * Real.exp (s / 2 * lam k) * Real.exp (-(s * lam k)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (p.factorial : ℝ) / (s / 2) ^ p * Real.exp (-(s / 2 * lam k)) := by rw [mul_assoc, h3]

theorem heatMom_hasSum (h : IsSpectrum lam) (p : ℕ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun k => lam k ^ p * Real.exp (-(s * lam k))) (heatMom lam p s) :=
  (mom_summable h p hs).hasSum

theorem heatMom_nonneg (h : IsSpectrum lam) (p : ℕ) (s : ℝ) : 0 ≤ heatMom lam p s :=
  tsum_nonneg fun k => mul_nonneg (pow_nonneg (h.nonneg k) p) (Real.exp_pos _).le

theorem heatMom_zero (s : ℝ) : heatMom lam 0 s = heatTr lam s := by
  unfold heatMom heatTr
  exact tsum_congr fun k => by simp

/-- The series `eq:Tsigma` converges (for `σ > 0`, `t ≥ 0`). -/
theorem subTr_hasSum (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    HasSum (fun k => Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k))))) - Real.exp (-(t / σ)))
      (subTr lam σ t) := by
  have hτ : 0 ≤ t / σ := div_nonneg ht hσ.le
  refine (Summable.of_nonneg_of_le
    (fun k => (mode_sub_bounds hτ (mul_nonneg hσ.le (h.nonneg k))).1)
    (fun k => (mode_sub_bounds hτ (mul_nonneg hσ.le (h.nonneg k))).2)
    ((h.summable σ hσ).mul_left (t / σ))).hasSum

theorem subTr_nonneg (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    0 ≤ subTr lam σ t :=
  tsum_nonneg fun k =>
    (mode_sub_bounds (div_nonneg ht hσ.le) (mul_nonneg hσ.le (h.nonneg k))).1

/-- **`thm:rate`(ii).** For `σ > 0`, `t > 0`, `τ = t/σ`:
    `-e^{1-τ} Θ(σ) - e^{-τ/2} Θ(t/2) ≤ T_σ(t) - Θ(t) ≤ (σt/2) Θ''(t/2) + τ e^{-(1-1/e)τ} Θ(σ)`,
    with `Θ'' = heatMom lam 2`. No condition `t ≥ σ` is needed. -/
theorem rate_ii (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    -(Real.exp (1 - t / σ) * heatTr lam σ + Real.exp (-(t / σ / 2)) * heatTr lam (t / 2))
        ≤ subTr lam σ t - heatTr lam t ∧
    subTr lam σ t - heatTr lam t
        ≤ σ * t / 2 * heatMom lam 2 (t / 2)
          + t / σ * Real.exp (-(t / σ * (1 - Real.exp (-1)))) * heatTr lam σ := by
  have hτ : 0 ≤ t / σ := div_nonneg ht.le hσ.le
  have hσ' : σ ≠ 0 := hσ.ne'
  have ht2 : 0 < t / 2 := by linarith
  have hD := (subTr_hasSum h hσ ht.le).sub (heatTr_hasSum h ht)
  have hL := (((heatTr_hasSum h hσ).mul_left (Real.exp (1 - t / σ))).add
    ((heatTr_hasSum h ht2).mul_left (Real.exp (-(t / σ / 2))))).neg
  have hU := ((heatMom_hasSum h 2 ht2).mul_left (σ * t / 2)).add
    ((heatTr_hasSum h hσ).mul_left (t / σ * Real.exp (-(t / σ * (1 - Real.exp (-1))))))
  have e1 : ∀ k, t / σ * (σ * lam k) = t * lam k := fun k => by field_simp
  constructor
  · refine hasSum_le (fun k => ?_) hL hD
    have key := mode_lower hτ (mul_nonneg hσ.le (h.nonneg k))
    rw [e1 k, show t * lam k / 2 = t / 2 * lam k by ring] at key
    exact key
  · refine hasSum_le (fun k => ?_) hD hU
    have key := mode_upper hτ (mul_nonneg hσ.le (h.nonneg k))
    have e2 : t / σ * (σ * lam k) * (σ * lam k) / 2 = σ * t / 2 * lam k ^ 2 := by
      field_simp
    rw [e2, e1 k, show t * lam k / 2 = t / 2 * lam k by ring] at key
    refine key.trans (le_of_eq ?_)
    ring

/-- **`thm:rate`(iii).** For `t ≥ σ > 0`, `τ = t/σ`:
    `|T_σ(t) - Θ(t) - (σt/2) Θ''(t)| ≤ (σ/t)² [t⁴ Θ''''(t/2)/8 + t³ |Θ'''(t/2)|/6]
        + 3(1+τ) e^{-τ/4} [Θ(σ) + Θ(t/4)]`,
    with `Θ'' = heatMom lam 2`, `|Θ'''| = heatMom lam 3`, `Θ'''' = heatMom lam 4`. -/
theorem rate_iii (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    |subTr lam σ t - heatTr lam t - σ * t / 2 * heatMom lam 2 t|
      ≤ (σ / t) ^ 2 * (t ^ 4 / 8 * heatMom lam 4 (t / 2) + t ^ 3 / 6 * heatMom lam 3 (t / 2))
        + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4)) * (heatTr lam σ + heatTr lam (t / 4)) := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have ht2 : 0 < t / 2 := by linarith
  have ht4 : 0 < t / 4 := by linarith
  have hE := ((subTr_hasSum h hσ ht.le).sub (heatTr_hasSum h ht)).sub
    ((heatMom_hasSum h 2 ht).mul_left (σ * t / 2))
  have hR := ((((heatMom_hasSum h 4 ht2).mul_left (t ^ 4 / 8)).add
      ((heatMom_hasSum h 3 ht2).mul_left (t ^ 3 / 6))).mul_left ((σ / t) ^ 2)).add
    (((heatTr_hasSum h hσ).add (heatTr_hasSum h ht4)).mul_left
      (3 * (1 + t / σ) * Real.exp (-(t / σ / 4))))
  have pt := fun k => abs_le.1 (mode_third_scaled hσ hts (h.nonneg k))
  rw [abs_le]
  constructor
  · have := hasSum_le (fun k => (pt k).1) hR.neg hE
    exact this
  · exact hasSum_le (fun k => (pt k).2) hE hR

end Spectrum

/-! #### Part (i): the Poisson representation, for a spectrum -/

section PartI

variable {ι : Type*} {lam : ι → ℝ}

/-- `∑_{j ≥ 1} w_j(τ) x^j = e^{-τ} e^{τ x} - e^{-τ}`. -/
theorem pw_pow_shift_hasSum (τ x : ℝ) :
    HasSum (fun j : ℕ => TraceG29.pw τ (j + 1) * x ^ (j + 1))
      (Real.exp (-τ) * Real.exp (τ * x) - Real.exp (-τ)) := by
  have h : HasSum (fun j : ℕ => TraceG29.pw τ j * x ^ j) (Real.exp (-τ) * Real.exp (τ * x)) := by
    have h0 := (real_hasSum_exp (τ * x)).mul_left (Real.exp (-τ))
    have e : (fun j : ℕ => TraceG29.pw τ j * x ^ j)
        = fun j : ℕ => Real.exp (-τ) * ((τ * x) ^ j / (j.factorial : ℝ)) := funext fun j => by
      unfold TraceG29.pw
      rw [mul_pow]
      ring
    rw [e]
    exact h0
  have h1 := (hasSum_nat_add_iff' 1).2 h
  rw [Finset.sum_range_one, pow_zero, mul_one, TraceG29.pw_zero] at h1
  exact h1

/-- `∑_k s_k^j = Θ(jσ)` for `s_k = e^{-σ λ_k}`, `j ≥ 1`. -/
theorem heatTr_pow (h : IsSpectrum lam) {σ : ℝ} (hσ : 0 < σ) (j : ℕ) :
    HasSum (fun k => Real.exp (-(σ * lam k)) ^ (j + 1))
      (heatTr lam (((j + 1 : ℕ) : ℝ) * σ)) := by
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.succ_pos j)
  have h1 := heatTr_hasSum h (mul_pos hj hσ)
  have e : (fun k => Real.exp (-(σ * lam k)) ^ (j + 1))
      = fun k => Real.exp (-(((j + 1 : ℕ) : ℝ) * σ * lam k)) :=
    funext fun k => by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [e]
  exact h1

/-- **`thm:rate`(i), first statement.** `T_σ(t) = e^{-τ} ∑_{j ≥ 1} τ^j/j! · Θ(jσ)`, `τ = t/σ`
    (`TraceG29.pw τ j = e^{-τ} τ^j/j!`). The second statement of (i), `Tr P_σ^k = Θ(kσ)`, is the
    lemma `heatTr_pow` for the eigenvalues `s_k = e^{-σ λ_k}`; no operator occurs here. -/
theorem rate_i (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    HasSum (fun j : ℕ => TraceG29.pw (t / σ) (j + 1) * heatTr lam (((j + 1 : ℕ) : ℝ) * σ))
      (subTr lam σ t) := by
  have hτ : 0 ≤ t / σ := div_nonneg ht hσ.le
  let term : ℕ → ι → ℝ :=
    fun j k => TraceG29.pw (t / σ) (j + 1) * Real.exp (-(σ * lam k)) ^ (j + 1)
  have hmodes : ∀ j, HasSum (fun k => term j k)
      (TraceG29.pw (t / σ) (j + 1) * heatTr lam (((j + 1 : ℕ) : ℝ) * σ)) :=
    fun j => (heatTr_pow h hσ j).mul_left _
  have hsteps : ∀ k, HasSum (fun j => term j k)
      (Real.exp (-(t / σ)) * Real.exp (t / σ * Real.exp (-(σ * lam k))) - Real.exp (-(t / σ))) :=
    fun k => pw_pow_shift_hasSum (t / σ) _
  have hnn : ∀ p : ℕ × ι, 0 ≤ Function.uncurry term p := fun p =>
    mul_nonneg (TraceG29.pw_nonneg hτ _) (pow_nonneg (Real.exp_pos _).le _)
  have houter : Summable (fun j : ℕ =>
      TraceG29.pw (t / σ) (j + 1) * heatTr lam (((j + 1 : ℕ) : ℝ) * σ)) := by
    refine Summable.of_nonneg_of_le
      (fun j => mul_nonneg (TraceG29.pw_nonneg hτ _) (heatTr_nonneg _)) (fun j => ?_)
      ((TraceG29.pw_shift_hasSum (t / σ)).summable.mul_right (heatTr lam σ))
    refine mul_le_mul_of_nonneg_left (heatTr_anti h hσ ?_) (TraceG29.pw_nonneg hτ _)
    have h1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    nlinarith
  have hs : Summable (Function.uncurry term) := by
    refine (summable_prod_of_nonneg hnn).2 ⟨fun j => (hmodes j).summable, ?_⟩
    have e : (fun j : ℕ => ∑' k, Function.uncurry term (j, k))
        = fun j : ℕ => TraceG29.pw (t / σ) (j + 1) * heatTr lam (((j + 1 : ℕ) : ℝ) * σ) :=
      funext fun j => (hmodes j).tsum_eq
    rw [e]
    exact houter
  have hval : subTr lam σ t
      = ∑' j : ℕ, TraceG29.pw (t / σ) (j + 1) * heatTr lam (((j + 1 : ℕ) : ℝ) * σ) :=
    calc subTr lam σ t
        = ∑' k, (Real.exp (-(t / σ)) * Real.exp (t / σ * Real.exp (-(σ * lam k)))
            - Real.exp (-(t / σ))) := by
          unfold subTr
          refine tsum_congr fun k => ?_
          have e : -(t / σ * (1 - Real.exp (-(σ * lam k))))
              = -(t / σ) + t / σ * Real.exp (-(σ * lam k)) := by ring
          rw [e, Real.exp_add]
      _ = ∑' (k : ι) (j : ℕ), term j k := tsum_congr fun k => (hsteps k).tsum_eq.symm
      _ = ∑' (j : ℕ) (k : ι), term j k := hs.tsum_comm
      _ = ∑' j : ℕ, TraceG29.pw (t / σ) (j + 1) * heatTr lam (((j + 1 : ℕ) : ℝ) * σ) :=
          tsum_congr fun j => (hmodes j).tsum_eq
  rw [hval]
  exact houter.hasSum

end PartI

/-! #### The flat torus -/

/-- The eigenvalues of `-Δ` on the flat torus `ℝ^d/ℤ^d` as a list: `λ_n = 4π²|n|²`, `n ∈ ℤ^d`
    (that these are the eigenvalues of a Laplacian is not a statement of this block; see the file
    `CorrelationsToGeometrySpectrum.lean` for the classical eigenfunctions). -/
noncomputable def torusLam (d : ℕ) (n : Fin d → ℤ) : ℝ :=
  4 * Real.pi ^ 2 * ∑ i, ((n i : ℤ) : ℝ) ^ 2

theorem torus_isSpectrum (d : ℕ) : IsSpectrum (torusLam d) where
  nonneg := fun n => by unfold torusLam; positivity
  summable := fun s hs => by
    have hc : 0 < 4 * Real.pi ^ 2 * s := by positivity
    refine (gauss_summable hc d).congr (fun n => ?_)
    unfold torusLam
    congr 1
    ring

/-- The heat trace of the torus is the heat kernel of the second file at the origin. -/
theorem heatTr_torus (d : ℕ) (s : ℝ) :
    heatTr (torusLam d) s = heatTorus d (4 * Real.pi ^ 2 * s) 0 := by
  unfold heatTr heatTorus
  rw [cosSeries_zero]
  refine tsum_congr fun n => ?_
  unfold torusLam
  congr 1
  ring

/-- **The mode sum `eq:Tsigma` on the torus is the Poisson mean of the other files:**
    `T_σ(t) = poissonMean d (2σ) (t/σ)` (their `σ` is `ξ² = 2σ`). -/
theorem subTr_torus (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    subTr (torusLam d) σ t = TraceG29.poissonMean d (2 * σ) (t / σ) := by
  have h1 := rate_i (torus_isSpectrum d) hσ ht
  have h2 := TraceG29.poissonMean_hasSum (show 0 < 2 * σ by linarith) d (div_nonneg ht hσ.le)
  have e : (fun j : ℕ => TraceG29.pw (t / σ) (j + 1) * heatTr (torusLam d) (((j + 1 : ℕ) : ℝ) * σ))
      = fun j : ℕ => TraceG29.pw (t / σ) (j + 1) * TraceG29.heatMode d (2 * σ) (j + 1) :=
    funext fun j => by
      rw [heatTr_torus]
      unfold TraceG29.heatMode
      congr 2
      ring
  rw [e] at h1
  exact h1.unique h2

/-! #### Simplified remainder and the ratio form -/

section Ratio

variable {ι : Type*} {lam : ι → ℝ}

/-- `t^p ∑ λ^p e^{-tλ/2} ≤ p! 4^p ∑ e^{-tλ/4}`. -/
theorem mom_le_heatTr (h : IsSpectrum lam) (p : ℕ) {t : ℝ} (ht : 0 < t) :
    t ^ p * heatMom lam p (t / 2) ≤ (p.factorial : ℝ) * 4 ^ p * heatTr lam (t / 4) := by
  have ht2 : 0 < t / 2 := by linarith
  have ht4 : 0 < t / 4 := by linarith
  refine hasSum_le (fun k => ?_) ((heatMom_hasSum h p ht2).mul_left (t ^ p))
    ((heatTr_hasSum h ht4).mul_left ((p.factorial : ℝ) * 4 ^ p))
  have hy : 0 ≤ t / 4 * lam k := mul_nonneg ht4.le (h.nonneg k)
  have h1 := Real.pow_div_factorial_le_exp (x := t / 4 * lam k) hy p
  have hf : (0 : ℝ) < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have h2 : t ^ p * lam k ^ p ≤ (p.factorial : ℝ) * 4 ^ p * Real.exp (t / 4 * lam k) := by
    rw [div_le_iff₀ hf] at h1
    have e : t ^ p * lam k ^ p = 4 ^ p * (t / 4 * lam k) ^ p := by
      rw [← mul_pow, ← mul_pow]; congr 1; ring
    rw [e]
    nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) p]
  have h3 : Real.exp (t / 4 * lam k) * Real.exp (-(t / 2 * lam k)) = Real.exp (-(t / 4 * lam k)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc t ^ p * (lam k ^ p * Real.exp (-(t / 2 * lam k)))
      = t ^ p * lam k ^ p * Real.exp (-(t / 2 * lam k)) := by ring
    _ ≤ (p.factorial : ℝ) * 4 ^ p * Real.exp (t / 4 * lam k) * Real.exp (-(t / 2 * lam k)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = (p.factorial : ℝ) * 4 ^ p * Real.exp (-(t / 4 * lam k)) := by rw [mul_assoc, h3]

/-- `thm:rate`(iii) with the derivatives at `t/2` bounded by the heat trace at `t/4`:
    `|T_σ(t) - Θ(t) - (σt/2)Θ''(t)| ≤ 832 (σ/t)² Θ(t/4) + 3(1+τ)e^{-τ/4}[Θ(σ) + Θ(t/4)]`. -/
theorem rate_iii_simple (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    |subTr lam σ t - heatTr lam t - σ * t / 2 * heatMom lam 2 t|
      ≤ 832 * (σ / t) ^ 2 * heatTr lam (t / 4)
        + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4)) * (heatTr lam σ + heatTr lam (t / 4)) := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have h3 := mom_le_heatTr h 3 ht
  have h4 := mom_le_heatTr h 4 ht
  have e3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [e3] at h3
  rw [e4] at h4
  have hq : 0 ≤ (σ / t) ^ 2 := by positivity
  have h5 : (σ / t) ^ 2 * (t ^ 4 / 8 * heatMom lam 4 (t / 2) + t ^ 3 / 6 * heatMom lam 3 (t / 2))
      ≤ (σ / t) ^ 2 * (832 * heatTr lam (t / 4)) :=
    mul_le_mul_of_nonneg_left (by linarith) hq
  have := rate_iii h hσ hts
  linarith

/-- **Ratio form.** For `t ≥ σ > 0` and `Θ(t) > 0`, with `m₂ = t² Θ''(t)/Θ(t)` and `τ = t/σ`:
    `|T_σ(t)/Θ(t) - 1 - m₂/(2τ)| ≤ [832 (σ/t)² Θ(t/4) + 3(1+τ)e^{-τ/4}(Θ(σ) + Θ(t/4))]/Θ(t)`. -/
theorem rate_ratio (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t)
    (hpos : 0 < heatTr lam t) :
    |subTr lam σ t / heatTr lam t - 1 - σ / (2 * t) * (t ^ 2 * heatMom lam 2 t / heatTr lam t)|
      ≤ (832 * (σ / t) ^ 2 * heatTr lam (t / 4)
          + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4)) * (heatTr lam σ + heatTr lam (t / 4)))
        / heatTr lam t := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have ht0 : t ≠ 0 := ht.ne'
  have hΘ0 : heatTr lam t ≠ 0 := hpos.ne'
  have key := rate_iii_simple h hσ hts
  have e : subTr lam σ t / heatTr lam t - 1 - σ / (2 * t) * (t ^ 2 * heatMom lam 2 t / heatTr lam t)
      = (subTr lam σ t - heatTr lam t - σ * t / 2 * heatMom lam 2 t) / heatTr lam t := by
    field_simp
  rw [e, abs_div, abs_of_pos hpos]
  exact div_le_div_of_nonneg_right key hpos.le

end Ratio

/-! #### Stage C: the moments are derivatives; the moment ratio on the torus -/

section Derivatives

variable {ι : Type*} {lam : ι → ℝ}

/-- **The moments are the derivatives of the heat trace:**
    `d/ds ∑ λ^p e^{-sλ} = -∑ λ^{p+1} e^{-sλ}` for `s > 0`. Hence `heatMom lam 2 = Θ''`,
    `heatMom lam 3 = -Θ'''`, `heatMom lam 4 = Θ''''`. -/
theorem heatMom_hasDerivAt (h : IsSpectrum lam) (p : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (heatMom lam p) (-heatMom lam (p + 1) s) s := by
  have hs2 : 0 < s / 2 := by linarith
  have hu := mom_summable h (p + 1) hs2
  have hg : ∀ (k : ι) (y : ℝ), y ∈ Set.Ioi (s / 2) →
      HasDerivAt (fun y : ℝ => lam k ^ p * Real.exp (-(y * lam k)))
        (-(lam k ^ (p + 1) * Real.exp (-(y * lam k)))) y := by
    intro k y _
    have h1 : HasDerivAt (fun y : ℝ => -(y * lam k)) (-(1 * lam k)) y :=
      ((hasDerivAt_id' y).mul_const (lam k)).neg
    have h2 := (h1.exp).const_mul (lam k ^ p)
    exact h2.congr_deriv (by ring)
  have hg' : ∀ (k : ι) (y : ℝ), y ∈ Set.Ioi (s / 2) →
      ‖-(lam k ^ (p + 1) * Real.exp (-(y * lam k)))‖
        ≤ lam k ^ (p + 1) * Real.exp (-(s / 2 * lam k)) := by
    intro k y hy
    have hy' : s / 2 < y := hy
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg (h.nonneg k) _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg (h.nonneg k) (sub_nonneg.2 hy'.le)]))
      (pow_nonneg (h.nonneg k) _)
  have key := hasDerivAt_tsum_of_isPreconnected (y₀ := s) (y := s) hu isOpen_Ioi
    isPreconnected_Ioi hg hg' (Set.mem_Ioi.2 (by linarith)) (mom_summable h p hs)
    (Set.mem_Ioi.2 (by linarith))
  have e : (∑' k, -(lam k ^ (p + 1) * Real.exp (-(s * lam k)))) = -heatMom lam (p + 1) s := by
    unfold heatMom
    rw [tsum_neg]
  rw [e] at key
  exact key

theorem heatTr_hasDerivAt (h : IsSpectrum lam) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (heatTr lam) (-heatMom lam 1 s) s := by
  have e : heatTr lam = heatMom lam 0 := funext fun s => (heatMom_zero s).symm
  rw [e]
  exact heatMom_hasDerivAt h 0 hs

/-- With a spectral gap (`λ_k = 0` or `λ_k ≥ 1`), for `p ≥ 1` and `b > 0`:
    `b^p ∑ λ^p e^{-bλ} ≤ p! 2^p e^{-b/4} ∑ e^{-(b/4)λ}`. -/
theorem mom_gap (h : IsSpectrum lam) (hgap : ∀ k, lam k = 0 ∨ 1 ≤ lam k) {p : ℕ} (hp : 1 ≤ p)
    {b : ℝ} (hb : 0 < b) :
    b ^ p * heatMom lam p b
      ≤ (p.factorial : ℝ) * 2 ^ p * (Real.exp (-(b / 4)) * heatTr lam (b / 4)) := by
  have hb4 : 0 < b / 4 := by linarith
  refine hasSum_le (fun k => ?_) ((heatMom_hasSum h p hb).mul_left (b ^ p))
    (((heatTr_hasSum h hb4).mul_left (Real.exp (-(b / 4)))).mul_left ((p.factorial : ℝ) * 2 ^ p))
  have hf : (0 : ℝ) < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  rcases hgap k with h0 | h1
  · rw [h0, zero_pow (by omega : p ≠ 0)]
    simp only [zero_mul, mul_zero]
    positivity
  · have hy : 0 ≤ b / 2 * lam k := mul_nonneg (by linarith) (h.nonneg k)
    have q1 := Real.pow_div_factorial_le_exp (x := b / 2 * lam k) hy p
    have q2 : b ^ p * lam k ^ p ≤ (p.factorial : ℝ) * 2 ^ p * Real.exp (b / 2 * lam k) := by
      rw [div_le_iff₀ hf] at q1
      have e : b ^ p * lam k ^ p = 2 ^ p * (b / 2 * lam k) ^ p := by
        rw [← mul_pow, ← mul_pow]; congr 1; ring
      rw [e]
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) p]
    have q3 : Real.exp (b / 2 * lam k) * Real.exp (-(b * lam k))
        ≤ Real.exp (-(b / 4)) * Real.exp (-(b / 4 * lam k)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hb.le (sub_nonneg.2 h1)])
    calc b ^ p * (lam k ^ p * Real.exp (-(b * lam k)))
        = b ^ p * lam k ^ p * Real.exp (-(b * lam k)) := by ring
      _ ≤ (p.factorial : ℝ) * 2 ^ p * Real.exp (b / 2 * lam k) * Real.exp (-(b * lam k)) :=
          mul_le_mul_of_nonneg_right q2 (Real.exp_pos _).le
      _ = (p.factorial : ℝ) * 2 ^ p * (Real.exp (b / 2 * lam k) * Real.exp (-(b * lam k))) := by
          ring
      _ ≤ (p.factorial : ℝ) * 2 ^ p * (Real.exp (-(b / 4)) * Real.exp (-(b / 4 * lam k))) :=
          mul_le_mul_of_nonneg_left q3 (by positivity)

end Derivatives

/-! ##### The integer lattice and the Jacobi identity -/

/-- `|n|²` on `ℤ^d`. -/
noncomputable def latLam (d : ℕ) (n : Fin d → ℤ) : ℝ := ∑ i, ((n i : ℤ) : ℝ) ^ 2

theorem lat_isSpectrum (d : ℕ) : IsSpectrum (latLam d) where
  nonneg := fun n => by unfold latLam; positivity
  summable := fun s hs => by
    refine (gauss_summable hs d).congr (fun n => ?_)
    unfold latLam
    congr 1
    ring

theorem lat_gap (d : ℕ) (n : Fin d → ℤ) : latLam d n = 0 ∨ 1 ≤ latLam d n := by
  have e : latLam d n = ((∑ i, (n i) ^ 2 : ℤ) : ℝ) := by
    simp [latLam]
  have h0 : (0 : ℤ) ≤ ∑ i, (n i) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  rcases h0.eq_or_lt with h | h
  · left
    rw [e, ← h]
    simp
  · right
    rw [e]
    exact_mod_cast h

theorem heatTr_lat (d : ℕ) (c : ℝ) : heatTr (latLam d) c = heatTorus d c 0 := by
  unfold heatTr heatTorus
  rw [cosSeries_zero]
  refine tsum_congr fun n => ?_
  unfold latLam
  congr 1
  ring

theorem heatTr_torus_lat (d : ℕ) (s : ℝ) :
    heatTr (torusLam d) s = heatTr (latLam d) (4 * Real.pi ^ 2 * s) := by
  rw [heatTr_torus, heatTr_lat]

theorem heatMom_torus_lat (d p : ℕ) (s : ℝ) :
    heatMom (torusLam d) p s = (4 * Real.pi ^ 2) ^ p * heatMom (latLam d) p (4 * Real.pi ^ 2 * s) := by
  unfold heatMom
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have e : torusLam d n = 4 * Real.pi ^ 2 * latLam d n := rfl
  rw [e, mul_pow]
  have e2 : -(s * (4 * Real.pi ^ 2 * latLam d n)) = -(4 * Real.pi ^ 2 * s * latLam d n) := by ring
  rw [e2]
  ring

/-- The amplitude `(π/c)^{d/2}` of the Jacobi identity, in the form of `perGauss`. -/
noncomputable def jacA (d : ℕ) (c : ℝ) : ℝ := (1 / (c / Real.pi) ^ (1 / 2 : ℝ)) ^ d

theorem jacA_pos (d : ℕ) {c : ℝ} (hc : 0 < c) : 0 < jacA d c := by
  have hpi := Real.pi_pos
  unfold jacA
  positivity

theorem heatTorus_zero_pow {c : ℝ} (hc : 0 < c) (d : ℕ) :
    heatTorus d c 0 = perGauss c 0 ^ d := by
  have e : (0 : FlatTorus d) = fun i => (((fun _ : Fin d => (0 : ℝ)) i : ℝ) : UnitAddCircle) := by
    funext i; simp
  rw [e, heatTorus_eq_prod hc d (fun _ => 0), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- One variable: `∑_n e^{-b n²} = perGauss b 0` (Poisson summation at the origin). -/
theorem gauss_int_eq_perGauss {b : ℝ} (hb : 0 < b) :
    ∑' j : ℤ, Real.exp (-b * (j : ℝ) ^ 2) = perGauss b 0 := by
  have h := theta_factor_eq hb 0
  have hf : ∀ j : ℤ, (fourier j (((0 : ℝ)) : UnitAddCircle) : ℂ) = 1 := by
    intro j
    rw [fourier_coe_apply]
    simp
  simp_rw [hf, mul_one] at h
  rw [← Complex.ofReal_tsum] at h
  exact Complex.ofReal_injective h

theorem perGauss_zero_dual {c : ℝ} (hc : 0 < c) :
    perGauss c 0 = 1 / (c / Real.pi) ^ (1 / 2 : ℝ) * perGauss (Real.pi ^ 2 * c⁻¹) 0 := by
  have hpi := Real.pi_pos
  have hb : 0 < Real.pi ^ 2 * c⁻¹ := by positivity
  rw [← gauss_int_eq_perGauss hb]
  conv_lhs => unfold perGauss
  congr 1
  refine tsum_congr fun n => ?_
  congr 1
  have hpi0 : Real.pi ≠ 0 := hpi.ne'
  have hc0 : c ≠ 0 := hc.ne'
  simp only [sub_zero]
  field_simp

/-- **Jacobi identity for the heat trace of `ℤ^d`:**
    `∑_n e^{-c|n|²} = (π/c)^{d/2} ∑_n e^{-(π²/c)|n|²}`. -/
theorem jacobi_lat (d : ℕ) {c : ℝ} (hc : 0 < c) :
    heatTr (latLam d) c = jacA d c * heatTr (latLam d) (Real.pi ^ 2 * c⁻¹) := by
  have hpi := Real.pi_pos
  have hb : 0 < Real.pi ^ 2 * c⁻¹ := by positivity
  rw [heatTr_lat, heatTr_lat, heatTorus_zero_pow hc, heatTorus_zero_pow hb, perGauss_zero_dual hc,
    mul_pow]
  rfl

/-- The derivative of one factor of the amplitude. -/
theorem jacA_one_hasDerivAt {c : ℝ} (hc : 0 < c) :
    HasDerivAt (fun y : ℝ => 1 / (y / Real.pi) ^ (1 / 2 : ℝ))
      (-(1 / 2 * c⁻¹) * (1 / (c / Real.pi) ^ (1 / 2 : ℝ))) c := by
  have hpi := Real.pi_pos
  have hx : 0 < c / Real.pi := div_pos hc hpi
  have h1 : HasDerivAt (fun y : ℝ => y / Real.pi) (1 / Real.pi) c :=
    (hasDerivAt_id' c).div_const Real.pi
  have h2 := h1.rpow_const (p := (1 / 2 : ℝ)) (Or.inl hx.ne')
  have hr0 : (c / Real.pi) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have h3 : HasDerivAt (fun y : ℝ => ((y / Real.pi) ^ (1 / 2 : ℝ))⁻¹) _ c := h2.inv hr0
  have e1 : (fun y : ℝ => 1 / (y / Real.pi) ^ (1 / 2 : ℝ))
      = fun y : ℝ => ((y / Real.pi) ^ (1 / 2 : ℝ))⁻¹ := funext fun y => one_div _
  rw [e1]
  refine h3.congr_deriv ?_
  rw [Real.rpow_sub_one hx.ne']
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (c / Real.pi) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hr]; exact Real.rpow_pos_of_pos hx _
  have hr2 : r ^ 2 = c / Real.pi := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have hpi0 : Real.pi ≠ 0 := hpi.ne'
  have hr0' : r ≠ 0 := hrpos.ne'
  have hc' : c = Real.pi * r ^ 2 := by rw [hr2]; field_simp
  rw [← hr]
  rw [hc']
  field_simp

theorem jacA_hasDerivAt (d : ℕ) {c : ℝ} (hc : 0 < c) :
    HasDerivAt (jacA d) (-((d : ℝ) / 2 * c⁻¹) * jacA d c) c := by
  have h1 := (jacA_one_hasDerivAt hc).fun_pow d
  refine HasDerivAt.congr_deriv (f := jacA d) h1 ?_
  unfold jacA
  cases d with
  | zero => simp
  | succ n =>
    rw [Nat.add_sub_cancel]
    push_cast
    ring

/-- First derivative of the Jacobi identity:
    `M₁(c) = (d/2c) Θ(c) - (π²/c²) A(c) M₁(π²/c)` for the lattice `ℤ^d`. -/
theorem jacobi_first (d : ℕ) {c : ℝ} (hc : 0 < c) :
    heatMom (latLam d) 1 c
      = (d : ℝ) / 2 * c⁻¹ * heatTr (latLam d) c
        - Real.pi ^ 2 * (c⁻¹ * c⁻¹) * (jacA d c * heatMom (latLam d) 1 (Real.pi ^ 2 * c⁻¹)) := by
  have hpi := Real.pi_pos
  have hZ := lat_isSpectrum d
  have hb : 0 < Real.pi ^ 2 * c⁻¹ := by positivity
  have hΘ := heatTr_hasDerivAt hZ hc
  have hbd : HasDerivAt (fun y : ℝ => Real.pi ^ 2 * y⁻¹) (Real.pi ^ 2 * -(c ^ 2)⁻¹) c :=
    (hasDerivAt_inv hc.ne').const_mul (Real.pi ^ 2)
  have hΘb := HasDerivAt.comp c (heatTr_hasDerivAt hZ hb) hbd
  have hprod : HasDerivAt
      (fun y => jacA d y * (heatTr (latLam d) ∘ fun y : ℝ => Real.pi ^ 2 * y⁻¹) y) _ c :=
    (jacA_hasDerivAt d hc).mul hΘb
  have heq : Filter.EventuallyEq (nhds c) (heatTr (latLam d))
      (fun y => jacA d y * (heatTr (latLam d) ∘ fun y : ℝ => Real.pi ^ 2 * y⁻¹) y) :=
    (eventually_gt_nhds hc).mono fun y hy => jacobi_lat d hy
  have huniq := hΘ.unique (hprod.congr_of_eventuallyEq heq)
  simp only [Function.comp_apply] at huniq
  rw [jacobi_lat d hc]
  linear_combination (-1 : ℝ) * huniq

/-- Second derivative of the Jacobi identity:
    `M₂(c) = d(d+2)/(4c²) Θ(c) - (d+2)(π²/c³) A(c) M₁(π²/c) + (π⁴/c⁴) A(c) M₂(π²/c)`. -/
theorem jacobi_second (d : ℕ) {c : ℝ} (hc : 0 < c) :
    heatMom (latLam d) 2 c
      = (d : ℝ) * ((d : ℝ) + 2) / 4 * (c⁻¹ * c⁻¹) * heatTr (latLam d) c
        - ((d : ℝ) + 2) * Real.pi ^ 2 * (c⁻¹ * c⁻¹ * c⁻¹)
            * (jacA d c * heatMom (latLam d) 1 (Real.pi ^ 2 * c⁻¹))
        + Real.pi ^ 4 * (c⁻¹ * c⁻¹ * c⁻¹ * c⁻¹)
            * (jacA d c * heatMom (latLam d) 2 (Real.pi ^ 2 * c⁻¹)) := by
  have hpi := Real.pi_pos
  have hZ := lat_isSpectrum d
  have hb : 0 < Real.pi ^ 2 * c⁻¹ := by positivity
  have hΘ := heatTr_hasDerivAt hZ hc
  have hM1 := heatMom_hasDerivAt hZ 1 hc
  have hinv := hasDerivAt_inv hc.ne'
  have hbd : HasDerivAt (fun y : ℝ => Real.pi ^ 2 * y⁻¹) (Real.pi ^ 2 * -(c ^ 2)⁻¹) c :=
    hinv.const_mul (Real.pi ^ 2)
  have hM1b := HasDerivAt.comp c (heatMom_hasDerivAt hZ 1 hb) hbd
  have hQ := (jacA_hasDerivAt d hc).mul hM1b
  have hii : HasDerivAt (fun y : ℝ => y⁻¹ * y⁻¹) _ c := hinv.mul hinv
  have h1 : HasDerivAt (fun y : ℝ => (d : ℝ) / 2 * y⁻¹ * heatTr (latLam d) y) _ c :=
    (hinv.const_mul ((d : ℝ) / 2)).mul hΘ
  have hQ' : HasDerivAt
      (fun y => jacA d y * (heatMom (latLam d) 1 ∘ fun y : ℝ => Real.pi ^ 2 * y⁻¹) y) _ c := hQ
  have h2 : HasDerivAt (fun y : ℝ => Real.pi ^ 2 * (y⁻¹ * y⁻¹)
      * (jacA d y * (heatMom (latLam d) 1 ∘ fun y : ℝ => Real.pi ^ 2 * y⁻¹) y)) _ c :=
    (hii.const_mul (Real.pi ^ 2)).mul hQ'
  have hR : HasDerivAt (fun y : ℝ => (d : ℝ) / 2 * y⁻¹ * heatTr (latLam d) y
        - Real.pi ^ 2 * (y⁻¹ * y⁻¹)
          * (jacA d y * (heatMom (latLam d) 1 ∘ fun y : ℝ => Real.pi ^ 2 * y⁻¹) y)) _ c :=
    h1.sub h2
  have heq : Filter.EventuallyEq (nhds c) (heatMom (latLam d) 1)
      (fun y => (d : ℝ) / 2 * y⁻¹ * heatTr (latLam d) y
        - Real.pi ^ 2 * (y⁻¹ * y⁻¹)
          * (jacA d y * (heatMom (latLam d) 1 ∘ fun y : ℝ => Real.pi ^ 2 * y⁻¹) y)) :=
    (eventually_gt_nhds hc).mono fun y hy => jacobi_first d hy
  have huniq := hM1.unique (hR.congr_of_eventuallyEq heq)
  simp only [Function.comp_apply] at huniq
  have e1 := jacobi_first d hc
  linear_combination (-1 : ℝ) * huniq + ((d : ℝ) / 2 * c⁻¹) * e1

theorem jac_alg {c k D q A Tb N1 N2 : ℝ} (hc : c ≠ 0) (hA : A ≠ 0) (hT : Tb ≠ 0) :
    c ^ 2 * (k * (c⁻¹ * c⁻¹) * (A * Tb) - D * q ^ 2 * (c⁻¹ * c⁻¹ * c⁻¹) * (A * N1)
        + q ^ 4 * (c⁻¹ * c⁻¹ * c⁻¹ * c⁻¹) * (A * N2)) / (A * Tb) - k
      = (-(D * (q ^ 2 * c⁻¹ * N1)) + (q ^ 2 * c⁻¹) ^ 2 * N2) / Tb := by
  field_simp; ring

/-- **The moment ratio of the lattice heat trace:** with `b = π²/c`,
    `|c² M₂(c)/Θ(c) - d(d+2)/4| ≤ (2d + 12) e^{-b/4} Θ(b/4)`; the proof gives the exact identity
    `c² M₂(c)/Θ(c) = d(d+2)/4 - (d+2) b M₁(b)/Θ(b) + b² M₂(b)/Θ(b)`. -/
theorem lat_moment_ratio (d : ℕ) {c : ℝ} (hc : 0 < c) :
    |c ^ 2 * heatMom (latLam d) 2 c / heatTr (latLam d) c - (d : ℝ) * ((d : ℝ) + 2) / 4|
      ≤ (2 * (d : ℝ) + 12) * (Real.exp (-(Real.pi ^ 2 * c⁻¹ / 4))
          * heatTr (latLam d) (Real.pi ^ 2 * c⁻¹ / 4)) := by
  have hpi := Real.pi_pos
  have hZ := lat_isSpectrum d
  have hb : 0 < Real.pi ^ 2 * c⁻¹ := by positivity
  have hA := jacA_pos d hc
  have hΘb : 1 ≤ heatTr (latLam d) (Real.pi ^ 2 * c⁻¹) := by
    rw [heatTr_lat]; exact heatTorus_zero_ge_one hb d
  have hΘbpos : 0 < heatTr (latLam d) (Real.pi ^ 2 * c⁻¹) := by linarith
  have key : c ^ 2 * heatMom (latLam d) 2 c / heatTr (latLam d) c - (d : ℝ) * ((d : ℝ) + 2) / 4
      = (-(((d : ℝ) + 2) * (Real.pi ^ 2 * c⁻¹ * heatMom (latLam d) 1 (Real.pi ^ 2 * c⁻¹)))
          + (Real.pi ^ 2 * c⁻¹) ^ 2 * heatMom (latLam d) 2 (Real.pi ^ 2 * c⁻¹))
        / heatTr (latLam d) (Real.pi ^ 2 * c⁻¹) := by
    rw [jacobi_second d hc, jacobi_lat d hc]
    exact jac_alg hc.ne' hA.ne' hΘbpos.ne'
  rw [key]
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Real.pi ^ 2 * c⁻¹ := ⟨_, rfl⟩
  rw [← hbdef] at hb hΘb hΘbpos ⊢
  have hM1 := heatMom_nonneg hZ 1 b
  have hM2 := heatMom_nonneg hZ 2 b
  have g1 := mom_gap hZ (lat_gap d) (p := 1) (le_refl 1) hb
  have g2 := mom_gap hZ (lat_gap d) (p := 2) (by norm_num) hb
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = Real.exp (-(b / 4)) * heatTr (latLam d) (b / 4) := ⟨_, rfl⟩
  rw [← hX] at g1 g2 ⊢
  have g1' : b * heatMom (latLam d) 1 b ≤ 2 * X := by
    have e : ((Nat.factorial 1 : ℕ) : ℝ) * 2 ^ 1 * X = 2 * X := by norm_num [Nat.factorial]
    rw [e, pow_one] at g1
    exact g1
  have g2' : b ^ 2 * heatMom (latLam d) 2 b ≤ 8 * X := by
    have e : ((Nat.factorial 2 : ℕ) : ℝ) * 2 ^ 2 * X = 8 * X := by norm_num [Nat.factorial]
    rw [e] at g2
    exact g2
  rw [abs_div, abs_of_pos hΘbpos, div_le_iff₀ hΘbpos]
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd2 : (0 : ℝ) ≤ (d : ℝ) + 2 := by linarith
  have hbM1 : 0 ≤ b * heatMom (latLam d) 1 b := mul_nonneg hb.le hM1
  have hbM2 : 0 ≤ b ^ 2 * heatMom (latLam d) 2 b := mul_nonneg (by positivity) hM2
  have hX0 : 0 ≤ X := by rw [hX]; exact mul_nonneg (Real.exp_pos _).le (heatTr_nonneg _)
  have hp1 : 0 ≤ ((d : ℝ) + 2) * (b * heatMom (latLam d) 1 b) := mul_nonneg hd2 hbM1
  have habs : |-(((d : ℝ) + 2) * (b * heatMom (latLam d) 1 b)) + b ^ 2 * heatMom (latLam d) 2 b|
      ≤ ((d : ℝ) + 2) * (b * heatMom (latLam d) 1 b) + b ^ 2 * heatMom (latLam d) 2 b := by
    rw [abs_le]
    constructor <;> linarith
  have hfin : ((d : ℝ) + 2) * (b * heatMom (latLam d) 1 b) + b ^ 2 * heatMom (latLam d) 2 b
      ≤ (2 * (d : ℝ) + 12) * X := by
    have := mul_le_mul_of_nonneg_left g1' hd2
    linarith
  have hXΘ : (2 * (d : ℝ) + 12) * X ≤ (2 * (d : ℝ) + 12) * X * heatTr (latLam d) b := by
    have h0 : 0 ≤ (2 * (d : ℝ) + 12) * X := mul_nonneg (by linarith) hX0
    have := mul_le_mul_of_nonneg_left hΘb h0
    linarith
  linarith

/-! ##### The torus: moment ratio and the expansion `eq:rateexact` -/

/-- **Moment ratio of the heat trace of the flat torus:** for `t > 0`,
    `|t² Θ''(t)/Θ(t) - d(d+2)/4| ≤ (2d + 12) e^{-1/(16t)} (1 + √(16πt))^d`. -/
theorem torus_moment_ratio (d : ℕ) {t : ℝ} (ht : 0 < t) :
    |t ^ 2 * heatMom (torusLam d) 2 t / heatTr (torusLam d) t - (d : ℝ) * ((d : ℝ) + 2) / 4|
      ≤ (2 * (d : ℝ) + 12)
          * (Real.exp (-(1 / (16 * t))) * (1 + Real.sqrt (16 * Real.pi * t)) ^ d) := by
  have hpi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := hpi.ne'
  have ht0 : t ≠ 0 := ht.ne'
  have hc : 0 < 4 * Real.pi ^ 2 * t := by positivity
  have h := lat_moment_ratio d hc
  have eb : Real.pi ^ 2 * (4 * Real.pi ^ 2 * t)⁻¹ / 4 = 1 / (16 * t) := by
    field_simp; ring
  rw [eb] at h
  rw [heatMom_torus_lat, heatTr_torus_lat]
  have e : t ^ 2 * ((4 * Real.pi ^ 2) ^ 2 * heatMom (latLam d) 2 (4 * Real.pi ^ 2 * t))
        / heatTr (latLam d) (4 * Real.pi ^ 2 * t)
      = (4 * Real.pi ^ 2 * t) ^ 2 * heatMom (latLam d) 2 (4 * Real.pi ^ 2 * t)
        / heatTr (latLam d) (4 * Real.pi ^ 2 * t) := by ring
  rw [e]
  refine h.trans ?_
  have h16 : 0 < 1 / (16 * t) := by positivity
  have hup : heatTr (latLam d) (1 / (16 * t)) ≤ (1 + Real.sqrt (16 * Real.pi * t)) ^ d := by
    rw [heatTr_lat]
    have := heatTorus_le h16 d 0
    have e2 : Real.pi / (1 / (16 * t)) = 16 * Real.pi * t := by field_simp
    rwa [e2] at this
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le) (by positivity)

/-- **The expansion `eq:rateexact` on the flat torus, with explicit remainder.** For
    `0 < σ ≤ t`, `τ = t/σ`, `Θ = heatTr (torusLam d)`, `T_σ = subTr (torusLam d) σ`:
    `|T_σ(t)/Θ(t) - 1 - d(d+2)/(8τ)|
       ≤ [832 (σ/t)² Θ(t/4) + 3(1+τ)e^{-τ/4}(Θ(σ) + Θ(t/4))]/Θ(t)
         + (σ/2t) (2d + 12) e^{-1/(16t)} (1 + √(16πt))^d`. -/
theorem rate_exact_torus (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    |subTr (torusLam d) σ t / heatTr (torusLam d) t - 1 - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / t)|
      ≤ (832 * (σ / t) ^ 2 * heatTr (torusLam d) (t / 4)
          + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4))
              * (heatTr (torusLam d) σ + heatTr (torusLam d) (t / 4)))
          / heatTr (torusLam d) t
        + σ / (2 * t) * ((2 * (d : ℝ) + 12)
            * (Real.exp (-(1 / (16 * t))) * (1 + Real.sqrt (16 * Real.pi * t)) ^ d)) := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hpi := Real.pi_pos
  have hpos : 0 < heatTr (torusLam d) t := by
    rw [heatTr_torus]
    exact lt_of_lt_of_le zero_lt_one (heatTorus_zero_ge_one (by positivity) d)
  have h1 := abs_le.1 (rate_ratio (torus_isSpectrum d) hσ hts hpos)
  have h2 := abs_le.1 (torus_moment_ratio d ht)
  have hs : 0 ≤ σ / (2 * t) := by positivity
  have p1 := mul_le_mul_of_nonneg_left h2.1 hs
  have p2 := mul_le_mul_of_nonneg_left h2.2 hs
  have e : (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / t) = σ / (2 * t) * ((d : ℝ) * ((d : ℝ) + 2) / 4) := by
    ring
  rw [e, abs_le]
  constructor <;> linarith

/-- Comparison of the heat trace of the torus at two times: if `t/s ≤ r²` then
    `Θ(s) ≤ (√(4πt) + r)^d Θ(t)` (upper bound `(1 + (4πs)^{-1/2})^d`, lower bound `(4πt)^{-d/2}`). -/
theorem torus_heat_compare (d : ℕ) {s t r : ℝ} (hs : 0 < s) (ht : 0 < t) (hr : 0 ≤ r)
    (hsr : t / s ≤ r ^ 2) :
    heatTr (torusLam d) s ≤ (Real.sqrt (4 * Real.pi * t) + r) ^ d * heatTr (torusLam d) t := by
  have hpi := Real.pi_pos
  have hpi0 : Real.pi ≠ 0 := hpi.ne'
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Real.sqrt (4 * Real.pi * t) := ⟨_, rfl⟩
  rw [← hw]
  have hwpos : 0 < w := by rw [hw]; exact Real.sqrt_pos.2 (by positivity)
  have hw0 : w ≠ 0 := hwpos.ne'
  have hw2 : w ^ 2 = 4 * Real.pi * t := by rw [hw]; exact Real.sq_sqrt (by positivity)
  have hlow : (1 / w) ^ d ≤ heatTr (torusLam d) t := by
    rw [heatTr_torus]
    have h := heatTorus_zero_ge (show 0 < 4 * Real.pi ^ 2 * t by positivity) d
    have e : (4 * Real.pi ^ 2 * t / Real.pi) ^ (1 / 2 : ℝ) = w := by
      rw [hw, Real.sqrt_eq_rpow]
      congr 1
      field_simp
    rwa [e] at h
  have hup : heatTr (torusLam d) s ≤ (1 + r / w) ^ d := by
    rw [heatTr_torus]
    refine (heatTorus_le (show 0 < 4 * Real.pi ^ 2 * s by positivity) d 0).trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have hsr' : t ≤ r ^ 2 * s := (div_le_iff₀ hs).1 hsr
    have h1 : Real.sqrt (Real.pi / (4 * Real.pi ^ 2 * s)) ≤ r / w := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      rw [div_pow, hw2, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hsr' (show 0 ≤ 4 * Real.pi ^ 2 by positivity)]
    linarith
  calc heatTr (torusLam d) s ≤ (1 + r / w) ^ d := hup
    _ = (w + r) ^ d * (1 / w) ^ d := by
        rw [← mul_pow]
        congr 1
        field_simp
    _ ≤ (w + r) ^ d * heatTr (torusLam d) t :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **`eq:rateexact` on the flat torus with all constants explicit.** For `0 < σ ≤ t ≤ 1`,
    `τ = t/σ`:
    `|T_σ(t)/Θ(t) - 1 - d(d+2)/(8τ)|
       ≤ 832·6^d/τ² + 3(1+τ) e^{-τ/4} ((4 + √τ)^d + 6^d) + (1/2τ)(2d+12) 9^d e^{-1/(16t)}`.
    The last term is the `O(σ)` of the paper on the torus; it is NOT small compared with
    `d(d+2)/(8τ)` unless `t` is small (for `t` of order one the two cancel). -/
theorem rate_exact_torus_explicit (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) (ht1 : t ≤ 1) :
    |subTr (torusLam d) σ t / heatTr (torusLam d) t - 1 - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / t)|
      ≤ 832 * 6 ^ d * (σ / t) ^ 2
        + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4)) * ((4 + Real.sqrt (t / σ)) ^ d + 6 ^ d)
        + σ / (2 * t) * ((2 * (d : ℝ) + 12) * (9 ^ d * Real.exp (-(1 / (16 * t))))) := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hpi := Real.pi_pos
  have ht0 : t ≠ 0 := ht.ne'
  have base := rate_exact_torus d hσ hts
  have hpos : 0 < heatTr (torusLam d) t := by
    rw [heatTr_torus]
    exact lt_of_lt_of_le zero_lt_one (heatTorus_zero_ge_one (by positivity) d)
  have hpt : Real.pi * t ≤ 4 * 1 := mul_le_mul Real.pi_le_four ht1 ht.le (by norm_num)
  have hw4 : Real.sqrt (4 * Real.pi * t) ≤ 4 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have hw8 : Real.sqrt (16 * Real.pi * t) ≤ 8 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
  have hw0 : 0 ≤ Real.sqrt (4 * Real.pi * t) := Real.sqrt_nonneg _
  have hτ0 : 0 ≤ t / σ := div_nonneg ht.le hσ.le
  have hr0 : 0 ≤ Real.sqrt (t / σ) := Real.sqrt_nonneg _
  have c1 := torus_heat_compare d (s := t / 4) (r := 2) (by linarith) ht (by norm_num)
    (by rw [show t / (t / 4) = 4 by field_simp]; norm_num)
  have c2 := torus_heat_compare d (s := σ) (r := Real.sqrt (t / σ)) hσ ht hr0
    (le_of_eq (Real.sq_sqrt hτ0).symm)
  have d1 : heatTr (torusLam d) (t / 4) ≤ 6 ^ d * heatTr (torusLam d) t :=
    c1.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith) (by linarith) d) hpos.le)
  have d2 : heatTr (torusLam d) σ ≤ (4 + Real.sqrt (t / σ)) ^ d * heatTr (torusLam d) t :=
    c2.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by linarith) (by linarith) d) hpos.le)
  have hq : 0 ≤ 832 * (σ / t) ^ 2 := by positivity
  have hE : 0 ≤ 3 * (1 + t / σ) * Real.exp (-(t / σ / 4)) := by positivity
  have first : (832 * (σ / t) ^ 2 * heatTr (torusLam d) (t / 4)
          + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4))
              * (heatTr (torusLam d) σ + heatTr (torusLam d) (t / 4)))
          / heatTr (torusLam d) t
      ≤ 832 * 6 ^ d * (σ / t) ^ 2
        + 3 * (1 + t / σ) * Real.exp (-(t / σ / 4)) * ((4 + Real.sqrt (t / σ)) ^ d + 6 ^ d) := by
    rw [div_le_iff₀ hpos]
    have a1 := mul_le_mul_of_nonneg_left d1 hq
    have a2 := mul_le_mul_of_nonneg_left (add_le_add d2 d1) hE
    linarith
  have second : σ / (2 * t) * ((2 * (d : ℝ) + 12)
            * (Real.exp (-(1 / (16 * t))) * (1 + Real.sqrt (16 * Real.pi * t)) ^ d))
      ≤ σ / (2 * t) * ((2 * (d : ℝ) + 12) * (9 ^ d * Real.exp (-(1 / (16 * t))))) := by
    have h9 : (1 + Real.sqrt (16 * Real.pi * t)) ^ d ≤ 9 ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have a3 := mul_le_mul_of_nonneg_left h9 (Real.exp_pos (-(1 / (16 * t)))).le
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
    linarith
  linarith

end PopulationRate

/-! ## The sharp rate for the sampled graph on the flat torus
(last display of `cor:kernel-trace`; the same display with `cor:secondstage-alld` on the sample side)

This block only COMPOSES accepted statements; it contains no new estimate on the sample:
* sample side: `TraceRates.heat_trace_rate_small` (almost surely, regime `N σ_N^{d/2+3}/log N → ∞`,
  i.e. `N ξ^{d+6}/log N → ∞`, uniformly in `2 ≤ τ ≤ c/σ_N`) and `SecondStageLimit.second_stage_limit`
  (in probability, regime `N σ_N^{d/2+2}/log N → ∞`, i.e. `N ξ^{d+4}/log N → ∞`, one sequence `τ_N`);
* population side: `PopulationRate.subTr_torus`, `rate_exact_torus_explicit` (`eq:rateexact` on the
  flat torus with explicit remainder).

Conventions (as in `TraceRates`): `σ N` is the VARIANCE of the kernel, `σ_N = ξ_N²`; the `σ` of the
paper is `σ N / 2`; `t` is the time of the paper, `τ = t/(σ_N/2) = 2 t/σ_N` the Poisson time,
`t ∈ [ξ_N², 1]` is `σ N ≤ t ≤ 1`. `Θ(t) = heatTr (torusLam d) t = ∑_{n ∈ ℤ^d} e^{-4π²|n|² t}`
(`= heatTorus d (4π² t) 0` by `heatTr_torus`). The sample quantity is
`Tr exp(τ(S - 1)) - N e^{-τ}` with `S = symGraph …` (graph WITH self-loops, nested sample).

What is proven (every statement for the flat torus `ℝ^d/ℤ^d`, `d ≥ 1`, uniform points):
* `combine`: the deterministic combination lemma.
* `sharp_rate_ae_explicit`: almost surely, for every `η > 0`, for all large `N` and ALL
  `t ∈ [σ_N, 1]`:
  `|(Tr exp(τ(S-1)) - N e^{-τ})/Θ(t) - 1 - d(d+2)/8 · (σ_N/2)/t|
     ≤ η σ_N (1 + d(d+2)/8·(σ_N/2)/t + popRem) + popRem`,
  `popRem d (σ_N/2) t` being the explicit population remainder of `rate_exact_torus_explicit`.
* `sharp_rate_ae`: the same with the remainder in the form of the paper,
  `≤ sharpC2 d · ((σ_N/2)/t)² + sharpC1 d · (σ_N/2) + η σ_N`
  (`O(τ^{-2}) + O(ξ²) + o(ξ²)` with explicit constants in the two `O`).
* `sharp_rate_ae_small_time`: if moreover `t` is restricted to `[σ_N, Tm_N]` with `Tm_N → 0`:
  `≤ sharpC2 d · ((σ_N/2)/t)² + η · (σ_N/2)/t`.
* `sharp_rate_prob_explicit`, `sharp_rate_prob`, `sharp_rate_prob_small_time`: the same three
  statements in probability (the probability that the bound fails tends to `0`), for ONE sequence
  `t_N ∈ [σ_N, 1]`, under the weaker regime `N σ_N^{d/2+2}/log N → ∞`.

HONEST READING, not to be hidden:
* The term `sharpC1 d · (σ_N/2)` (the `O(ξ²)` of the paper; it comes from
  `(σ/2t)(2d+12) 9^d e^{-1/(16t)}`) is of the SAME order `σ` as the main term
  `d(d+2)/8 · (σ_N/2)/t` when `t` is of order one. For such `t` the statements do NOT show that the
  deviation is of the size of the main term (and it is not: on the unit torus `T_σ/Θ - 1` is then
  much smaller than `d(d+2)/(8τ)`, the "remainder" cancels the main term; see
  `scripts/rate_exact_large_t.py`). The main term is identified only in `…_small_time`
  (`t ≤ Tm_N → 0`), and even there it dominates the bound only where additionally
  `sharpC2 d · (σ_N/2)/t` is small against `d(d+2)/8`, i.e. for `τ = 2t/σ_N` much larger than
  `8·sharpC2 d/(d(d+2))`; `sharpC2 d = 832·6^d + 12·3^d·4^{d+3}·(d+3)!` is far from sharp.
* The constants are those of these files, not constants of the paper; the exceptional null set /
  events are those of `heat_trace_rate_small` / `second_stage_limit`; the sample is nested (the
  first `N` points of one sequence); `Θ` is the sum over the list `4π²|n|²` (no Laplace operator);
  the sample quantity is `Tr exp(τ(S-1)) - N e^{-τ}`, not literally `Tr e^{-tL} - N e^{-τ}`
  (`L = (2/ξ²)(1 - S)` up to conjugation is not a statement of this block); `ξ_N → 0` is not
  assumed (only eventually `0 < σ_N ≤ 1`).
* The statements in probability are for one deterministic sequence `t_N`, not uniform in `t`, and
  measurability of the events is not shown here (`μ.real` of the sets as written). -/

namespace SharpRate

open Filter Topology
open CTG.Reals.TraceG29 TraceRates PopulationRate SecondStageLimit

/-! ### Stage 1: deterministic -/

/-- **Combination lemma.** From `|A/T - 1| ≤ ε` and `|T/Θ - 1 - κ| ≤ ρ` (`T, Θ ≠ 0`):
    `|A/Θ - 1 - κ| ≤ ε (1 + |κ| + ρ) + ρ`. -/
theorem combine {A T Θ κ ε ρ : ℝ} (hT : T ≠ 0) (hΘ : Θ ≠ 0)
    (h1 : |A / T - 1| ≤ ε) (h2 : |T / Θ - 1 - κ| ≤ ρ) :
    |A / Θ - 1 - κ| ≤ ε * (1 + |κ| + ρ) + ρ := by
  have e : A / Θ - 1 - κ = (A / T - 1) * (T / Θ) + (T / Θ - 1 - κ) := by
    field_simp
    ring
  have h3 : |T / Θ| ≤ 1 + |κ| + ρ := by
    have e3 : T / Θ = ((T / Θ - 1 - κ) + 1) + κ := by ring
    have a1 := abs_add_le ((T / Θ - 1 - κ) + 1) κ
    have a2 := abs_add_le (T / Θ - 1 - κ) 1
    rw [abs_one] at a2
    rw [← e3] at a1
    linarith
  have h4 : |(A / T - 1) * (T / Θ)| ≤ ε * (1 + |κ| + ρ) := by
    rw [abs_mul]
    exact mul_le_mul h1 h3 (abs_nonneg _) ((abs_nonneg _).trans h1)
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add h4 h2)

/-- The explicit population remainder of `rate_exact_torus_explicit` (`s` is the `σ` of the paper,
    `τ = t/s`): `832·6^d/τ² + 3(1+τ) e^{-τ/4}((4+√τ)^d + 6^d) + (1/2τ)(2d+12) 9^d e^{-1/(16t)}`. -/
noncomputable def popRem (d : ℕ) (s t : ℝ) : ℝ :=
  832 * 6 ^ d * (s / t) ^ 2
    + 3 * (1 + t / s) * Real.exp (-(t / s / 4)) * ((4 + Real.sqrt (t / s)) ^ d + 6 ^ d)
    + s / (2 * t) * ((2 * (d : ℝ) + 12) * (9 ^ d * Real.exp (-(1 / (16 * t)))))

/-- **Deterministic sharp rate, explicit remainder.** `σ` is the variance of the kernel (`ξ²`),
    `σ ≤ t ≤ 1`, `x` any real number (the subtracted trace of the sample). If
    `|x / T_{σ/2}(t) - 1| ≤ ε` (with `T_{σ/2}(t) = poissonMean d σ (2t/σ)`), then
    `|x/Θ(t) - 1 - d(d+2)/8·(σ/2)/t| ≤ ε (1 + d(d+2)/8·(σ/2)/t + popRem) + popRem`. -/
theorem sharp_det (d : ℕ) {σ t x ε : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) (ht1 : t ≤ 1)
    (h : |x / poissonMean d σ (2 * t / σ) - 1| ≤ ε) :
    |x / heatTr (torusLam d) t - 1 - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / 2 / t)|
      ≤ ε * (1 + (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / 2 / t) + popRem d (σ / 2) t)
        + popRem d (σ / 2) t := by
  unfold popRem
  have hs : 0 < σ / 2 := by linarith
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hst : σ / 2 ≤ t := by linarith
  have e1 : 2 * (σ / 2) = σ := by ring
  have e2 : t / (σ / 2) = 2 * t / σ := by rw [div_div_eq_mul_div]; ring
  have hT : subTr (torusLam d) (σ / 2) t = poissonMean d σ (2 * t / σ) := by
    rw [subTr_torus d hs ht.le, e1, e2]
  have hτ : 0 < 2 * t / σ := by positivity
  have hTpos : 0 < poissonMean d σ (2 * t / σ) := by
    have h1 := poissonMean_ge hσ d hτ.le
    have h2 : Real.exp (-(2 * t / σ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hpop := rate_exact_torus_explicit d hs hst ht1
  rw [hT] at hpop
  have hκ : 0 ≤ (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / 2 / t) := by positivity
  have hΘ : heatTr (torusLam d) t ≠ 0 := by
    have h1 : 0 < heatTr (torusLam d) t := by
      rw [heatTr_torus]
      exact lt_of_lt_of_le zero_lt_one (heatTorus_zero_ge_one (by positivity) d)
    exact h1.ne'
  have key := combine hTpos.ne' hΘ h hpop
  rwa [abs_of_nonneg hκ] at key

/-- The constant of the exponentially small term: `12·3^d·4^{d+3}·(d+3)!`. -/
noncomputable def sharpK (d : ℕ) : ℝ := 12 * 3 ^ d * (4 ^ (d + 3) * ((d + 3).factorial : ℝ))

/-- The exponentially small term of `popRem` is `O(τ^{-2})` for `τ ≥ 2`. -/
theorem exp_tail_le (d : ℕ) {τ : ℝ} (hτ : 2 ≤ τ) :
    3 * (1 + τ) * Real.exp (-(τ / 4)) * ((4 + Real.sqrt τ) ^ d + 6 ^ d)
      ≤ sharpK d * (1 / τ) ^ 2 := by
  have hτ0 : 0 < τ := by linarith
  have hsq : Real.sqrt τ ≤ τ := Real.sqrt_le_iff.2 ⟨hτ0.le, by nlinarith⟩
  have hs0 : 0 ≤ Real.sqrt τ := Real.sqrt_nonneg τ
  have h4 : (4 + Real.sqrt τ) ^ d ≤ (3 * τ) ^ d :=
    pow_le_pow_left₀ (by linarith) (by linarith) d
  have h6 : (6 : ℝ) ^ d ≤ (3 * τ) ^ d := pow_le_pow_left₀ (by norm_num) (by linarith) d
  have he : 0 ≤ Real.exp (-(τ / 4)) := (Real.exp_pos _).le
  have hfpos : (0 : ℝ) < ((d + 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (d + 3)
  have hfac := Real.pow_div_factorial_le_exp (x := τ / 4) (by positivity) (d + 3)
  rw [div_le_iff₀ hfpos] at hfac
  have hexp : Real.exp (-(τ / 4)) * Real.exp (τ / 4) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpw : τ ^ (d + 3) = 4 ^ (d + 3) * (τ / 4) ^ (d + 3) := by
    rw [← mul_pow]
    congr 1
    ring
  have hE : Real.exp (-(τ / 4)) * τ ^ (d + 3) ≤ 4 ^ (d + 3) * ((d + 3).factorial : ℝ) := by
    rw [hpw]
    have a1 := mul_le_mul_of_nonneg_left hfac
      (mul_nonneg he (by positivity : (0 : ℝ) ≤ 4 ^ (d + 3)))
    have a2 : Real.exp (-(τ / 4)) * 4 ^ (d + 3)
          * (Real.exp (τ / 4) * ((d + 3).factorial : ℝ))
        = 4 ^ (d + 3) * ((d + 3).factorial : ℝ)
          * (Real.exp (-(τ / 4)) * Real.exp (τ / 4)) := by ring
    rw [a2, hexp, mul_one] at a1
    linarith
  have a1 : (4 + Real.sqrt τ) ^ d + 6 ^ d ≤ 2 * (3 * τ) ^ d := by linarith
  have a2 : 3 * (1 + τ) * Real.exp (-(τ / 4)) ≤ 6 * τ * Real.exp (-(τ / 4)) :=
    mul_le_mul_of_nonneg_right (by linarith) he
  have a3 : 3 * (1 + τ) * Real.exp (-(τ / 4)) * ((4 + Real.sqrt τ) ^ d + 6 ^ d)
      ≤ 6 * τ * Real.exp (-(τ / 4)) * (2 * (3 * τ) ^ d) :=
    mul_le_mul a2 a1 (by positivity) (by positivity)
  have hid : τ ^ (d + 3) * (1 / τ) ^ 2 = τ ^ d * τ := by
    rw [pow_add]
    field_simp
  have a4 : 6 * τ * Real.exp (-(τ / 4)) * (2 * (3 * τ) ^ d)
      = 12 * 3 ^ d * (Real.exp (-(τ / 4)) * τ ^ (d + 3)) * (1 / τ) ^ 2 := by
    rw [mul_pow]
    linear_combination (-(12 * 3 ^ d * Real.exp (-(τ / 4)))) * hid
  have a5 : 12 * 3 ^ d * (Real.exp (-(τ / 4)) * τ ^ (d + 3)) * (1 / τ) ^ 2
      ≤ 12 * 3 ^ d * (4 ^ (d + 3) * ((d + 3).factorial : ℝ)) * (1 / τ) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
  rw [a4] at a3
  unfold sharpK
  exact a3.trans a5

/-- The constant of the `O(τ^{-2})` term: `832·6^d + 12·3^d·4^{d+3}·(d+3)!`. -/
noncomputable def sharpC2 (d : ℕ) : ℝ := 832 * 6 ^ d + sharpK d

/-- The constant of the `O(σ)` term (with `σ` of the paper): `16 (d+6) 9^d`. -/
noncomputable def sharpC1 (d : ℕ) : ℝ := 16 * ((d : ℝ) + 6) * 9 ^ d

/-- The constant that absorbs `1 + κ + popRem`: `1 + d(d+2)/16 + sharpC2/4 + sharpC1/2`. -/
noncomputable def sharpB (d : ℕ) : ℝ :=
  1 + (d : ℝ) * ((d : ℝ) + 2) / 16 + sharpC2 d / 4 + sharpC1 d / 2

theorem sharpC2_nonneg (d : ℕ) : 0 ≤ sharpC2 d := by
  unfold sharpC2 sharpK
  positivity

theorem sharpC1_nonneg (d : ℕ) : 0 ≤ sharpC1 d := by
  unfold sharpC1
  positivity

theorem sharpB_pos (d : ℕ) : 0 < sharpB d := by
  have h1 := sharpC2_nonneg d
  have h2 := sharpC1_nonneg d
  have h3 : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) + 2) / 16 := by positivity
  unfold sharpB
  linarith

/-- **The population remainder in the form of `eq:rateexact`:** for `0 < 2s ≤ t` (`τ = t/s ≥ 2`),
    `popRem d s t ≤ sharpC2 d · (s/t)² + sharpC1 d · s`, i.e. `O(τ^{-2}) + O(σ)`. The second term
    uses only `e^{-1/(16t)} ≤ 16 t`; it is NOT small against the main term `d(d+2)/8·(s/t)` unless
    `t` is small. -/
theorem popRem_le (d : ℕ) {s t : ℝ} (hs : 0 < s) (hst : 2 * s ≤ t) :
    popRem d s t ≤ sharpC2 d * (s / t) ^ 2 + sharpC1 d * s := by
  have ht : 0 < t := by linarith
  have hτ : 2 ≤ t / s := by
    rw [le_div_iff₀ hs]
    linarith
  have h2 := exp_tail_le d hτ
  rw [one_div_div] at h2
  have h3 : Real.exp (-(1 / (16 * t))) ≤ 16 * t := by
    have hx : 0 < 1 / (16 * t) := by positivity
    have h := Real.add_one_le_exp (1 / (16 * t))
    have hE := Real.exp_pos (1 / (16 * t))
    rw [Real.exp_neg, inv_le_comm₀ hE (by positivity)]
    have e : (16 * t)⁻¹ = 1 / (16 * t) := (one_div _).symm
    rw [e]
    linarith
  have h4 : s / (2 * t) * ((2 * (d : ℝ) + 12) * (9 ^ d * Real.exp (-(1 / (16 * t)))))
      ≤ s / (2 * t) * ((2 * (d : ℝ) + 12) * (9 ^ d * (16 * t))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity))
      (by positivity)
  have e4 : s / (2 * t) * ((2 * (d : ℝ) + 12) * (9 ^ d * (16 * t))) = sharpC1 d * s := by
    unfold sharpC1
    field_simp
    ring
  rw [e4] at h4
  unfold popRem sharpC2
  linarith

/-- **Deterministic sharp rate in the form of the paper:** under the hypotheses of `sharp_det`
    and `ε ≥ 0`:
    `|x/Θ(t) - 1 - d(d+2)/8·(σ/2)/t| ≤ sharpC2 ((σ/2)/t)² + sharpC1 (σ/2) + ε · sharpB`. -/
theorem sharp_det_O (d : ℕ) {σ t x ε : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) (ht1 : t ≤ 1)
    (hε : 0 ≤ ε) (h : |x / poissonMean d σ (2 * t / σ) - 1| ≤ ε) :
    |x / heatTr (torusLam d) t - 1 - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / 2 / t)|
      ≤ sharpC2 d * (σ / 2 / t) ^ 2 + sharpC1 d * (σ / 2) + ε * sharpB d := by
  have h1 := sharp_det d hσ hts ht1 h
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hr : σ / 2 / t ≤ 1 / 2 := by
    rw [div_le_iff₀ ht]
    linarith
  have hr0 : 0 ≤ σ / 2 / t := by positivity
  have hp := popRem_le d (s := σ / 2) (t := t) (by linarith) (by linarith)
  have hC2 := sharpC2_nonneg d
  have hC1 := sharpC1_nonneg d
  have hsq : (σ / 2 / t) ^ 2 ≤ 1 / 4 := by nlinarith
  have a := mul_le_mul_of_nonneg_left hsq hC2
  have b := mul_le_mul_of_nonneg_left (by linarith : σ / 2 ≤ 1 / 2) hC1
  have hκ : (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / 2 / t) ≤ (d : ℝ) * ((d : ℝ) + 2) / 16 := by
    have := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ (d : ℝ) * ((d : ℝ) + 2) / 8)
    linarith
  have hB : 1 + (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / 2 / t) + popRem d (σ / 2) t ≤ sharpB d := by
    unfold sharpB
    linarith
  have c := mul_le_mul_of_nonneg_left hB hε
  linarith

/-- **Deterministic sharp rate for small times:** if moreover `t ≤ Tm` and the sample error is
    `ε = e σ` (`e ≥ 0`), then
    `|x/Θ(t) - 1 - d(d+2)/8·(σ/2)/t| ≤ sharpC2 ((σ/2)/t)² + (σ/2)/t · Tm (sharpC1 + 2 e sharpB)`. -/
theorem sharp_det_small (d : ℕ) {σ t x e Tm : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) (ht1 : t ≤ 1)
    (htT : t ≤ Tm) (he : 0 ≤ e) (h : |x / poissonMean d σ (2 * t / σ) - 1| ≤ e * σ) :
    |x / heatTr (torusLam d) t - 1 - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ / 2 / t)|
      ≤ sharpC2 d * (σ / 2 / t) ^ 2 + σ / 2 / t * (Tm * (sharpC1 d + 2 * e * sharpB d)) := by
  have h1 := sharp_det_O d hσ hts ht1 (mul_nonneg he hσ.le) h
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hr0 : 0 ≤ σ / 2 / t := by positivity
  have e1 : σ / 2 = σ / 2 / t * t := by field_simp
  have h2 : σ / 2 ≤ σ / 2 / t * Tm := by
    have := mul_le_mul_of_nonneg_left htT hr0
    linarith
  have hK : 0 ≤ sharpC1 d + 2 * e * sharpB d := by
    have := sharpC1_nonneg d
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) he) (sharpB_pos d).le
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 hK
  nlinarith

/-! ### Stage 2: almost surely, uniformly in `t ∈ [σ_N, 1]` (regime `N ξ^{d+6}/log N → ∞`) -/

/-- **Sharp rate, almost surely, explicit remainder.** Independent uniform points on the flat
    torus of dimension `d ≥ 1` (nested sample), kernel variance `σ_N = ξ_N²`, graph with
    self-loops. If eventually `0 < σ_N ≤ 1` and `N σ_N^{d/2+3}/log N → ∞` (`N ξ^{d+6}/log N → ∞`),
    then almost surely, for every `η > 0`, for all large `N` and ALL `t` with `σ_N ≤ t ≤ 1`, with
    `τ = 2t/σ_N`, `Θ(t) = ∑_n e^{-4π²|n|²t}`:
    `|(Tr exp(τ(S-1)) - N e^{-τ})/Θ(t) - 1 - d(d+2)/8·(σ_N/2)/t|
       ≤ η σ_N (1 + d(d+2)/8·(σ_N/2)/t + popRem d (σ_N/2) t) + popRem d (σ_N/2) t`.
    (`d(d+2)/8·(σ_N/2)/t = d(d+2)/(8τ)`.) -/
theorem sharp_rate_ae_explicit {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, σ N ≤ t → t ≤ 1 →
      |((NormedSpace.exp ((2 * t / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t / σ N))) / heatTr (torusLam d) t - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t)|
        ≤ η * σ N * (1 + (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t) + popRem d (σ N / 2) t)
          + popRem d (σ N / 2) t := by
  filter_upwards [heat_trace_rate_small d hd X h_indep hX hlaw σ (c := 2) two_pos hσ hreg3]
    with ω hω
  intro η hη
  filter_upwards [hω η hη, hσ] with N h1 h3 t ht1 ht2
  have hσ0 := h3.1
  have hτ1 : 2 ≤ 2 * t / σ N := by
    rw [le_div_iff₀ hσ0]
    linarith
  have hτ2 : 2 * t / σ N ≤ 2 / σ N := div_le_div_of_nonneg_right (by linarith) hσ0.le
  have h := h1 (2 * t / σ N) hτ1 hτ2
  exact sharp_det d hσ0 ht1 ht2 (h.1.trans h.2)

/-- **Sharp rate, almost surely (last display of `cor:kernel-trace`, uniformly in `t`).** Under
    the hypotheses of `sharp_rate_ae_explicit`: almost surely, for every `η > 0`, for all large
    `N` and ALL `t` with `σ_N ≤ t ≤ 1` (`τ = 2t/σ_N`):
    `|(Tr exp(τ(S-1)) - N e^{-τ})/Θ(t) - 1 - d(d+2)/(8τ)|
       ≤ sharpC2 d · τ^{-2} + sharpC1 d · (σ_N/2) + η σ_N`
    (written with `1/τ = (σ_N/2)/t`). The middle term is of the order of the main term when `t` is
    of order one: see the remarks at the head of the block. -/
theorem sharp_rate_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, σ N ≤ t → t ≤ 1 →
      |((NormedSpace.exp ((2 * t / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t / σ N))) / heatTr (torusLam d) t - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t)|
        ≤ sharpC2 d * (σ N / 2 / t) ^ 2 + sharpC1 d * (σ N / 2) + η * σ N := by
  filter_upwards [heat_trace_rate_small d hd X h_indep hX hlaw σ (c := 2) two_pos hσ hreg3]
    with ω hω
  intro η hη
  have hB := sharpB_pos d
  filter_upwards [hω (η / sharpB d) (div_pos hη hB), hσ] with N h1 h3 t ht1 ht2
  have hσ0 := h3.1
  have hτ1 : 2 ≤ 2 * t / σ N := by
    rw [le_div_iff₀ hσ0]
    linarith
  have hτ2 : 2 * t / σ N ≤ 2 / σ N := div_le_div_of_nonneg_right (by linarith) hσ0.le
  have h := h1 (2 * t / σ N) hτ1 hτ2
  have key := sharp_det_O d hσ0 ht1 ht2
    (mul_nonneg (div_pos hη hB).le hσ0.le) (h.1.trans h.2)
  have e : η / sharpB d * σ N * sharpB d = η * σ N := by
    field_simp
  rw [e] at key
  exact key

/-- **Sharp rate for small times, almost surely: the main term is identified.** Under the
    hypotheses of `sharp_rate_ae_explicit`, and for a sequence `Tm_N → 0`: almost surely, for
    every `η > 0`, for all large `N` and ALL `t` with `σ_N ≤ t ≤ Tm_N` (`τ = 2t/σ_N`):
    `|(Tr exp(τ(S-1)) - N e^{-τ})/Θ(t) - 1 - d(d+2)/(8τ)| ≤ sharpC2 d · τ^{-2} + η · τ^{-1}`
    (written with `1/τ = (σ_N/2)/t`). The right-hand side is small against the main term
    `d(d+2)/(8τ)` where moreover `τ` is large against `sharpC2 d`. -/
theorem sharp_rate_ae_small_time {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ Tm : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg3 : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop) (hTm : Tendsto Tm atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, σ N ≤ t → t ≤ Tm N →
      |((NormedSpace.exp ((2 * t / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t / σ N))) / heatTr (torusLam d) t - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t)|
        ≤ sharpC2 d * (σ N / 2 / t) ^ 2 + η * (σ N / 2 / t) := by
  filter_upwards [heat_trace_rate_small d hd X h_indep hX hlaw σ (c := 2) two_pos hσ hreg3]
    with ω hω
  intro η hη
  have hK : 0 < sharpC1 d + 2 * 1 * sharpB d := by
    have := sharpC1_nonneg d
    have := sharpB_pos d
    linarith
  filter_upwards [hω 1 one_pos, hσ,
    (tendsto_order.1 hTm).2 (min 1 (η / (sharpC1 d + 2 * 1 * sharpB d)))
      (lt_min one_pos (div_pos hη hK))] with N h1 h3 h4 t ht1 ht2
  have hσ0 := h3.1
  have hT1 : Tm N ≤ 1 := (h4.trans_le (min_le_left _ _)).le
  have hT2 : Tm N * (sharpC1 d + 2 * 1 * sharpB d) ≤ η :=
    ((lt_div_iff₀ hK).1 (h4.trans_le (min_le_right _ _))).le
  have ht3 : t ≤ 1 := ht2.trans hT1
  have hτ1 : 2 ≤ 2 * t / σ N := by
    rw [le_div_iff₀ hσ0]
    linarith
  have hτ2 : 2 * t / σ N ≤ 2 / σ N := div_le_div_of_nonneg_right (by linarith) hσ0.le
  have h := h1 (2 * t / σ N) hτ1 hτ2
  have key := sharp_det_small d hσ0 ht1 ht3 ht2 zero_le_one (h.1.trans h.2)
  have hr0 : 0 ≤ σ N / 2 / t := by
    have : 0 < t := lt_of_lt_of_le hσ0 ht1
    positivity
  have := mul_le_mul_of_nonneg_left hT2 hr0
  linarith

/-! ### Stage 3: in probability, for one sequence `t_N` (regime `N ξ^{d+4}/log N → ∞`) -/

/-- The Poisson times `τ_N = 2 t_N/σ_N` of a sequence `t_N ∈ [σ_N, 1]` lie in `[2, 2/σ_N]`. -/
theorem tau_range (σ t : ℕ → ℝ) (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (ht : ∀ᶠ N in atTop, σ N ≤ t N ∧ t N ≤ 1) :
    ∀ᶠ N in atTop, 2 ≤ (fun N => 2 * t N / σ N) N ∧ (fun N => 2 * t N / σ N) N ≤ 2 / σ N := by
  filter_upwards [hσ, ht] with N h1 h2
  refine ⟨?_, div_le_div_of_nonneg_right (by linarith [h2.2]) h1.1.le⟩
  show 2 ≤ 2 * t N / σ N
  rw [le_div_iff₀ h1.1]
  linarith [h2.1]

/-- **Sharp rate in probability, explicit remainder.** Independent uniform points on the flat
    torus of dimension `d ≥ 1` (nested sample), kernel variance `σ_N = ξ_N²`, graph with
    self-loops. If eventually `0 < σ_N ≤ 1` and `σ_N ≤ t_N ≤ 1`, and `N σ_N^{d/2+2}/log N → ∞`
    (`N ξ^{d+4}/log N → ∞`), then for every `η > 0`, with `τ_N = 2t_N/σ_N`, the probability of
    `|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/Θ(t_N) - 1 - d(d+2)/8·(σ_N/2)/t_N|
       > η σ_N (1 + d(d+2)/8·(σ_N/2)/t_N + popRem) + popRem`
    tends to `0` (`popRem = popRem d (σ_N/2) t_N`). -/
theorem sharp_rate_prob_explicit {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ t : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (ht : ∀ᶠ N in atTop, σ N ≤ t N ∧ t N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N)
      atTop atTop) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      μ.real {ω | η * σ N * (1 + (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)
            + popRem d (σ N / 2) (t N)) + popRem d (σ N / 2) (t N)
        < |((NormedSpace.exp ((2 * t N / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t N / σ N))) / heatTr (torusLam d) (t N) - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)|})
      atTop (𝓝 0) := by
  have h0 := second_stage_limit d hd X h_indep hX hlaw σ (fun N => 2 * t N / σ N) two_pos hσ
    (tau_range σ t hσ ht) hreg hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall (fun N => measureReal_nonneg)) ?_
  filter_upwards [hσ, ht] with N h1 h2
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  rw [not_lt] at hcon
  have key := sharp_det d h1.1 h2.1 h2.2 hcon
  linarith

/-- **Sharp rate in probability (the last display of `cor:kernel-trace` with the sample side of
    `cor:secondstage-alld`).** Under the hypotheses of `sharp_rate_prob_explicit`, for every
    `η > 0` the probability of
    `|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/Θ(t_N) - 1 - d(d+2)/(8τ_N)|
       > sharpC2 d · τ_N^{-2} + sharpC1 d · (σ_N/2) + η σ_N`
    tends to `0` (written with `1/τ_N = (σ_N/2)/t_N`). The middle term is of the order of the main
    term when `t_N` is of order one: see the remarks at the head of the block. -/
theorem sharp_rate_prob {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ t : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (ht : ∀ᶠ N in atTop, σ N ≤ t N ∧ t N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N)
      atTop atTop) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      μ.real {ω | sharpC2 d * (σ N / 2 / t N) ^ 2 + sharpC1 d * (σ N / 2) + η * σ N
        < |((NormedSpace.exp ((2 * t N / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t N / σ N))) / heatTr (torusLam d) (t N) - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)|})
      atTop (𝓝 0) := by
  have hB := sharpB_pos d
  have h0 := second_stage_limit d hd X h_indep hX hlaw σ (fun N => 2 * t N / σ N) two_pos hσ
    (tau_range σ t hσ ht) hreg (div_pos hη hB)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall (fun N => measureReal_nonneg)) ?_
  filter_upwards [hσ, ht] with N h1 h2
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  rw [not_lt] at hcon
  have key := sharp_det_O d h1.1 h2.1 h2.2 (mul_nonneg (div_pos hη hB).le h1.1.le) hcon
  have e : η / sharpB d * σ N * sharpB d = η * σ N := by
    field_simp
  rw [e] at key
  linarith

/-- **Sharp rate in probability for small times: the main term is identified.** Under the
    hypotheses of `sharp_rate_prob_explicit` and `t_N → 0`, for every `η > 0` the probability of
    `|(Tr exp(τ_N(S-1)) - N e^{-τ_N})/Θ(t_N) - 1 - d(d+2)/(8τ_N)|
       > sharpC2 d · τ_N^{-2} + η · τ_N^{-1}`
    tends to `0` (written with `1/τ_N = (σ_N/2)/t_N`). -/
theorem sharp_rate_prob_small_time {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ t : ℕ → ℝ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1)
    (ht : ∀ᶠ N in atTop, σ N ≤ t N ∧ t N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 2 / Real.log N)
      atTop atTop) (ht0 : Tendsto t atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      μ.real {ω | sharpC2 d * (σ N / 2 / t N) ^ 2 + η * (σ N / 2 / t N)
        < |((NormedSpace.exp ((2 * t N / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t N / σ N))) / heatTr (torusLam d) (t N) - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)|})
      atTop (𝓝 0) := by
  have hK : 0 < sharpC1 d + 2 * 1 * sharpB d := by
    have := sharpC1_nonneg d
    have := sharpB_pos d
    linarith
  have h0 := second_stage_limit d hd X h_indep hX hlaw σ (fun N => 2 * t N / σ N) two_pos hσ
    (tau_range σ t hσ ht) hreg one_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall (fun N => measureReal_nonneg)) ?_
  filter_upwards [hσ, ht, (tendsto_order.1 ht0).2 (η / (sharpC1 d + 2 * 1 * sharpB d))
    (div_pos hη hK)] with N h1 h2 h4
  have hT2 : t N * (sharpC1 d + 2 * 1 * sharpB d) ≤ η := ((lt_div_iff₀ hK).1 h4).le
  have hr0 : 0 ≤ σ N / 2 / t N := by
    have : 0 < t N := lt_of_lt_of_le h1.1 h2.1
    have := h1.1
    positivity
  have hm := mul_le_mul_of_nonneg_left hT2 hr0
  refine measureReal_mono ?_ (measure_ne_top μ _)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  rw [not_lt] at hcon
  have key := sharp_det_small d h1.1 h2.1 h2.2 le_rfl zero_le_one hcon
  linarith

end SharpRate

/-! ### The corrected estimator in the exactly solvable case (`thm:corrected`) and the subtracted
term of the graph without self-loops (last sentence of `cor:kernel-noloops`) -/

namespace CorrectedRate

/-!
Conventions. As in `PopulationRate`, `σ` is the `σ` of the PAPER (`P_σ = e^{σΔ}`, `σ = c_h ξ²/2`),
`t` is the time of the paper and `τ = t/σ`. The `σ` of the second and third Lean files is
`ξ² = 2σ`; the two statements that connect with those files (`corrected_torus_corrSeries`,
`noloop_subtraction_lean`) say so explicitly.

Part (A), `thm:corrected`, for an abstract spectrum `lam` (`IsSpectrum`, nothing else):
* `subTr1 lam σ t`, `subTr2 lam σ t`: the series of the first and second derivatives in `t` of
  the terms of `T_σ(t) = subTr lam σ t`;
* `subTr_hasDerivAt`, `subTr1_hasDerivAt`, `subTr_deriv2`: for `σ > 0`, `t > 0` they ARE the
  derivatives, `deriv (deriv (subTr lam σ)) t = subTr2 lam σ t` ("`T_σ` is twice differentiable");
* `corrected_series` / `corrected_deriv`: the display of `thm:corrected` with the constants of the
  paper, for ALL `σ > 0`, `t > 0` (the condition `t ≥ σ` of the paper is not needed);
* `corrected_simple`: the same with the moments at `t/2` bounded by `Θ(t/4)`.
For the flat torus `ℝ^d/ℤ^d` (no hypothesis):
* `heatTr_torus_scale`: `Θ(s) ≤ (t/s)^{d/2} Θ(t)` for `0 < s ≤ t` (constant one, every `t`);
* `corrected_torus`, `corrected_torus_deriv`: relative error
  `≤ 1728·2^d (σ/t)² + 4(1+τ)² e^{-τ/2} (τ^{d/2} + 2^{d/2})` for `0 < σ ≤ t`, every `t`
  (the paper says "for `t ≤ 1` ... `O(τ^{-2})`"; on the torus no upper bound on `t` is needed);
* `poissonMean_deriv2`, `corrected_torus_corrSeries`: the corrected quantity equals
  `Corrected.corrSeries (t/σ) (heatMode d (2σ))` of the third file (chain rule
  `(σt/2) ∂_t² = (τ/2) ∂_τ²`).

Part (B), last sentence of `cor:kernel-noloops`, deterministic, flat torus:
* `noloop_subtraction`: `τ e^{-τ} M ≤ τ^{1+d/2} e^{-τ} Θ(t)` with `M = Θ(σ) = p_{ξ²}(0)`, for
  `0 < σ ≤ t`: the constant `C` of the paper is `1`, and `t ≤ 1` is not needed;
* `noloop_subtraction_rate`: hence `τ e^{-τ} M ≤ (d+3)! (σ/t)² Θ(t)`;
* `noloop_subtraction_lean`: the same for the term `pw τ 1 * heatTorus d (2π²σ') 0` subtracted in
  `NoLoopsTrace.noloop_heat_trace_ratio` (there `σ' = ξ²`).

NOT proved here and NOT claimed:
* nothing about a manifold or an operator; "closed Riemannian manifold" enters only through the
  list of eigenvalues, as in `PopulationRate`;
* the sentence "for `t ≤ 1` the relative error is `O(τ^{-2})`" for a general manifold (it needs
  `Θ(t/4) ≤ C Θ(t)` and `Θ(σ) ≤ C τ^{d/2} Θ(t)`); only the flat torus is treated;
* nothing about the sampled graph: the corrected estimator of the sample is `Corrected.corrected_G30`
  (third file), the graph without self-loops is `NoLoopsTrace` (third file); no statement here
  combines them with the bounds of this block. In particular the comparison of the subtracted
  term with `T_σ(t)` (the denominator of `noloop_heat_trace_ratio`) instead of `Θ(t)` is not
  written out, and neither is "the statements of `cor:kernel-trace` on the rate hold for the graph
  without self-loops".
-/

open Filter Topology
open PopulationRate CTG.Reals.TraceG29 Corrected CorrectedPopulation

/-! #### (A) One mode -/

/-- **`thm:corrected` for one mode, low or high** (`u = σλ`, `τu = tλ`), for all `τ ≥ 0`, `u ≥ 0`:
    `|a(1 - τw²/2) - e^{-τ}(1 - τ/2) - b| ≤ (τu³/2 + (τu²/2)²) e^{-τu/2}
        + 4(1+τ)² e^{-τ/2} (e^{-u} + e^{-τu/2})`,
    `w = 1 - e^{-u}`, `a = e^{-τw}`, `b = e^{-τu}`. Low modes: `walk_mode_corrected` of the core
    file; high modes: `corrected_high_mode` of the core file. -/
theorem mode_corrected {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    |Real.exp (-(τ * (1 - Real.exp (-u))))
          * (1 - τ * (1 - Real.exp (-u)) * (1 - Real.exp (-u)) / 2)
        - Real.exp (-τ) * (1 - τ / 2) - Real.exp (-(τ * u))|
      ≤ (τ * u * u * u / 2 + τ * u * u / 2 * (τ * u * u / 2)) * Real.exp (-(τ * u / 2))
        + 4 * (1 + τ) ^ 2 * Real.exp (-(τ / 2)) * (Real.exp (-u) + Real.exp (-(τ * u / 2))) := by
  have hEu := Real.exp_pos (-u)
  have hE2 := Real.exp_pos (-(τ / 2))
  have hEx2 := Real.exp_pos (-(τ * u / 2))
  have hEt := Real.exp_pos (-τ)
  have hF : 0 ≤ (τ * u * u * u / 2 + τ * u * u / 2 * (τ * u * u / 2))
      * Real.exp (-(τ * u / 2)) := by positivity
  have hq1 : 0 ≤ 4 * (1 + τ) ^ 2 * Real.exp (-(τ / 2)) * Real.exp (-u) := by positivity
  have hq2 : 0 ≤ 4 * (1 + τ) ^ 2 * Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2)) := by positivity
  rcases le_total u 1 with h | h
  · obtain ⟨l1, l2⟩ := real_walk_mode_corrected hτ hu h
    have h1 : Real.exp (-τ) ≤ Real.exp (-(τ / 2)) := Real.exp_le_exp.2 (by linarith)
    have h2 : 1 / 4 ≤ Real.exp (-u) :=
      le_trans quarter_le_exp_neg_one (Real.exp_le_exp.2 (by linarith))
    have h3 : Real.exp (-τ) * (1 + τ / 2)
        ≤ 4 * (1 + τ) ^ 2 * Real.exp (-(τ / 2)) * Real.exp (-u) := by
      have a1 : Real.exp (-τ) * (1 + τ / 2) ≤ Real.exp (-(τ / 2)) * (1 + τ) ^ 2 :=
        mul_le_mul h1 (by nlinarith) (by linarith) hE2.le
      have a2 : Real.exp (-(τ / 2)) * (1 + τ) ^ 2 * 1
          ≤ Real.exp (-(τ / 2)) * (1 + τ) ^ 2 * (4 * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have h5 : |Real.exp (-τ) * (1 - τ / 2)| ≤ Real.exp (-τ) * (1 + τ / 2) := by
      rw [abs_mul, abs_of_pos hEt]
      exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith) hEt.le
    obtain ⟨h6, h7⟩ := abs_le.1 h5
    rw [abs_le]
    constructor
    · linarith
    · linarith
  · have hs0 : Real.exp (-u) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    obtain ⟨k1, k2⟩ := CTG.HeatTrace.corrected_high_mode real_isExp (tau := τ)
      (s := Real.exp (-u)) (s0 := Real.exp (-1)) hτ hEu.le hs0
      (by have := exp_neg_one_le_half; linarith)
    have k3 : Real.exp (-(τ * (1 - Real.exp (-1)))) ≤ Real.exp (-(τ / 2)) :=
      Real.exp_le_exp.2 (by nlinarith [exp_neg_one_le_half])
    have ea : Real.exp (-(τ * (1 - Real.exp (-u))))
        = Real.exp (-τ) * Real.exp (τ * Real.exp (-u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have k4 : τ * Real.exp (-u) * (2 + τ / 2) * Real.exp (-(τ * (1 - Real.exp (-1))))
        ≤ 4 * (1 + τ) ^ 2 * Real.exp (-(τ / 2)) * Real.exp (-u) := by
      have b1 : τ * Real.exp (-u) * (2 + τ / 2) * Real.exp (-(τ * (1 - Real.exp (-1))))
          ≤ τ * Real.exp (-u) * (2 + τ / 2) * Real.exp (-(τ / 2)) :=
        mul_le_mul_of_nonneg_left k3 (by positivity)
      have b2 : τ * (2 + τ / 2) * (Real.exp (-u) * Real.exp (-(τ / 2)))
          ≤ 4 * (1 + τ) ^ 2 * (Real.exp (-u) * Real.exp (-(τ / 2))) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
      linarith
    have k5 : Real.exp (-(τ * u)) ≤ Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ (sub_nonneg.2 h)])
    have k6 : Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2))
        ≤ 4 * (1 + τ) ^ 2 * Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2)) := by
      have c1 : (1 : ℝ) ≤ 4 * (1 + τ) ^ 2 := by nlinarith
      have c2 := mul_le_mul_of_nonneg_right c1
        (show 0 ≤ Real.exp (-(τ / 2)) * Real.exp (-(τ * u / 2)) by positivity)
      linarith
    have e : Real.exp (-(τ * (1 - Real.exp (-u))))
          * (1 - τ * (1 - Real.exp (-u)) * (1 - Real.exp (-u)) / 2)
          - Real.exp (-τ) * (1 - τ / 2)
        = Real.exp (-τ) * (Real.exp (τ * Real.exp (-u))
            * (1 - τ * (1 - Real.exp (-u)) * (1 - Real.exp (-u)) / 2) - 1 + τ / 2) := by
      rw [ea]; ring
    have hb := Real.exp_pos (-(τ * u))
    rw [e, abs_le]
    constructor
    · linarith
    · linarith

theorem corr_alg {σ t A E B w : ℝ} :
    (A - E) - σ * t / 2 * ((w / σ) ^ 2 * A - (1 / σ) ^ 2 * E) - B
      = A * (1 - t / σ * w * w / 2) - E * (1 - t / σ / 2) - B := by
  by_cases hσ : σ = 0
  · subst hσ; simp
  · field_simp
    ring

/-- The same in the variables of the paper, `τ = t/σ`, `u = σ l`: the term of
    `T_σ - (σt/2) T_σ''` minus the heat mode `e^{-t l}`. -/
theorem mode_corrected_scaled {σ t l : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hl : 0 ≤ l) :
    |(Real.exp (-(t / σ * (1 - Real.exp (-(σ * l))))) - Real.exp (-(t / σ)))
        - σ * t / 2 * (((1 - Real.exp (-(σ * l))) / σ) ^ 2
              * Real.exp (-(t / σ * (1 - Real.exp (-(σ * l)))))
            - (1 / σ) ^ 2 * Real.exp (-(t / σ)))
        - Real.exp (-(t * l))|
      ≤ (σ / t) ^ 2 * (t ^ 3 / 2 * (l ^ 3 * Real.exp (-(t / 2 * l)))
            + t ^ 4 / 4 * (l ^ 4 * Real.exp (-(t / 2 * l))))
        + 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2))
            * (Real.exp (-(σ * l)) + Real.exp (-(t / 2 * l))) := by
  have hσ' : σ ≠ 0 := hσ.ne'
  have ht' : t ≠ 0 := ht.ne'
  have key := mode_corrected (τ := t / σ) (u := σ * l) (div_nonneg ht.le hσ.le)
    (mul_nonneg hσ.le hl)
  have e1 : t / σ * (σ * l) = t * l := by field_simp
  have e3 : t / σ * (σ * l) * (σ * l) * (σ * l) / 2 = (σ / t) ^ 2 * (t ^ 3 / 2 * l ^ 3) := by
    field_simp
  have e6 : t / σ * (σ * l) * (σ * l) / 2 * (t / σ * (σ * l) * (σ * l) / 2)
      = (σ / t) ^ 2 * (t ^ 4 / 4 * l ^ 4) := by
    field_simp; ring
  have e4 : t * l / 2 = t / 2 * l := by ring
  rw [e6, e3, e1, e4] at key
  rw [corr_alg]
  refine key.trans (le_of_eq ?_)
  ring

/-- First derivative of a mode, up to the factor `1/σ`: `|-w a + e^{-τ}| ≤ (τ+1) e^{-u}`. -/
theorem d1_bound {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    |-(1 - Real.exp (-u)) * Real.exp (-(τ * (1 - Real.exp (-u)))) + Real.exp (-τ)|
      ≤ (τ + 1) * Real.exp (-u) := by
  have hs0 := (Real.exp_pos (-u)).le
  have hs1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have ha0 := (Real.exp_pos (-(τ * (1 - Real.exp (-u))))).le
  have ha1 : Real.exp (-(τ * (1 - Real.exp (-u)))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hτ (sub_nonneg.2 hs1)])
  obtain ⟨m1, m2⟩ := mode_sub_bounds hτ hu
  have p1 := mul_nonneg hs0 ha0
  have p2 := mul_nonneg hs0 (sub_nonneg.2 ha1)
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- Second derivative of a mode, up to the factor `1/σ²`: `|w² a - e^{-τ}| ≤ (τ+2) e^{-u}`. -/
theorem d2_bound {τ u : ℝ} (hτ : 0 ≤ τ) (hu : 0 ≤ u) :
    |(1 - Real.exp (-u)) ^ 2 * Real.exp (-(τ * (1 - Real.exp (-u)))) - Real.exp (-τ)|
      ≤ (τ + 2) * Real.exp (-u) := by
  have hs0 := (Real.exp_pos (-u)).le
  have hs1 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have ha0 := (Real.exp_pos (-(τ * (1 - Real.exp (-u))))).le
  have ha1 : Real.exp (-(τ * (1 - Real.exp (-u)))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hτ (sub_nonneg.2 hs1)])
  obtain ⟨m1, m2⟩ := mode_sub_bounds hτ hu
  have p1 := mul_nonneg hs0 ha0
  have p2 := mul_nonneg hs0 (sub_nonneg.2 ha1)
  have p3 := mul_nonneg p1 (sub_nonneg.2 hs1)
  have p4 := mul_nonneg hs0 p1
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-! #### (A) Summation over a spectrum; the series are the derivatives -/

section Spectrum

variable {ι : Type*} (lam : ι → ℝ)

/-- The series of the first derivatives in `t` of the terms of `T_σ(t)` (`eq:Tsigma`):
    `∑_k [-μ_k e^{-tμ_k} + σ^{-1} e^{-t/σ}]`, `μ_k = (1 - e^{-σλ_k})/σ`. -/
noncomputable def subTr1 (σ t : ℝ) : ℝ :=
  ∑' k, (-((1 - Real.exp (-(σ * lam k))) / σ)
            * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k)))))
          + 1 / σ * Real.exp (-(t / σ)))

/-- The series of the second derivatives in `t` of the terms of `T_σ(t)`:
    `∑_k [μ_k² e^{-tμ_k} - σ^{-2} e^{-t/σ}]`. By `subTr_deriv2` this is `T_σ''(t)` for `t > 0`. -/
noncomputable def subTr2 (σ t : ℝ) : ℝ :=
  ∑' k, (((1 - Real.exp (-(σ * lam k))) / σ) ^ 2
            * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k)))))
          - (1 / σ) ^ 2 * Real.exp (-(t / σ)))

variable {lam}

theorem subTr1_term_bound (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (k : ι) :
    ‖-((1 - Real.exp (-(σ * lam k))) / σ) * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k)))))
        + 1 / σ * Real.exp (-(t / σ))‖
      ≤ 1 / σ * (t / σ + 1) * Real.exp (-(σ * lam k)) := by
  have key := d1_bound (div_nonneg ht hσ.le) (mul_nonneg hσ.le (h.nonneg k))
  have e : -((1 - Real.exp (-(σ * lam k))) / σ)
          * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k))))) + 1 / σ * Real.exp (-(t / σ))
      = 1 / σ * (-(1 - Real.exp (-(σ * lam k)))
          * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k))))) + Real.exp (-(t / σ))) := by ring
  have hpos : (0 : ℝ) ≤ 1 / σ := by positivity
  rw [Real.norm_eq_abs, e, abs_mul, abs_of_nonneg hpos, mul_assoc]
  exact mul_le_mul_of_nonneg_left key hpos

theorem subTr2_term_bound (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) (k : ι) :
    ‖((1 - Real.exp (-(σ * lam k))) / σ) ^ 2
          * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k)))))
        - (1 / σ) ^ 2 * Real.exp (-(t / σ))‖
      ≤ (1 / σ) ^ 2 * (t / σ + 2) * Real.exp (-(σ * lam k)) := by
  have key := d2_bound (div_nonneg ht hσ.le) (mul_nonneg hσ.le (h.nonneg k))
  have e : ((1 - Real.exp (-(σ * lam k))) / σ) ^ 2
          * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k)))))
          - (1 / σ) ^ 2 * Real.exp (-(t / σ))
      = (1 / σ) ^ 2 * ((1 - Real.exp (-(σ * lam k))) ^ 2
          * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k))))) - Real.exp (-(t / σ))) := by ring
  have hpos : (0 : ℝ) ≤ (1 / σ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, e, abs_mul, abs_of_nonneg hpos, mul_assoc]
  exact mul_le_mul_of_nonneg_left key hpos

theorem subTr1_hasSum (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    HasSum (fun k => -((1 - Real.exp (-(σ * lam k))) / σ)
            * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k)))))
          + 1 / σ * Real.exp (-(t / σ))) (subTr1 lam σ t) :=
  (Summable.of_norm_bounded ((h.summable σ hσ).mul_left (1 / σ * (t / σ + 1)))
    (fun k => subTr1_term_bound h hσ ht k)).hasSum

theorem subTr2_hasSum (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    HasSum (fun k => ((1 - Real.exp (-(σ * lam k))) / σ) ^ 2
            * Real.exp (-(t / σ * (1 - Real.exp (-(σ * lam k)))))
          - (1 / σ) ^ 2 * Real.exp (-(t / σ))) (subTr2 lam σ t) :=
  (Summable.of_norm_bounded ((h.summable σ hσ).mul_left ((1 / σ) ^ 2 * (t / σ + 2)))
    (fun k => subTr2_term_bound h hσ ht k)).hasSum

/-- `T_σ` is differentiable in `t` for `t > 0`, with the termwise derivative. -/
theorem subTr_hasDerivAt (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (subTr lam σ) (subTr1 lam σ t) t := by
  have hu : Summable fun k => 1 / σ * ((t + 1) / σ + 1) * Real.exp (-(σ * lam k)) :=
    (h.summable σ hσ).mul_left _
  have hg : ∀ (k : ι) (y : ℝ), y ∈ Set.Ioo (0 : ℝ) (t + 1) →
      HasDerivAt (fun y : ℝ => Real.exp (-(y / σ * (1 - Real.exp (-(σ * lam k)))))
          - Real.exp (-(y / σ)))
        (-((1 - Real.exp (-(σ * lam k))) / σ)
            * Real.exp (-(y / σ * (1 - Real.exp (-(σ * lam k)))))
          + 1 / σ * Real.exp (-(y / σ))) y := by
    intro k y _
    have h1 : HasDerivAt (fun y : ℝ => -(y / σ * (1 - Real.exp (-(σ * lam k)))))
        (-(1 / σ * (1 - Real.exp (-(σ * lam k))))) y :=
      (((hasDerivAt_id' y).div_const σ).mul_const _).neg
    have h2 : HasDerivAt (fun y : ℝ => -(y / σ)) (-(1 / σ)) y :=
      ((hasDerivAt_id' y).div_const σ).neg
    exact (h1.exp.sub h2.exp).congr_deriv (by ring)
  have hg' : ∀ (k : ι) (y : ℝ), y ∈ Set.Ioo (0 : ℝ) (t + 1) →
      ‖-((1 - Real.exp (-(σ * lam k))) / σ)
            * Real.exp (-(y / σ * (1 - Real.exp (-(σ * lam k)))))
          + 1 / σ * Real.exp (-(y / σ))‖
        ≤ 1 / σ * ((t + 1) / σ + 1) * Real.exp (-(σ * lam k)) := by
    intro k y hy
    refine (subTr1_term_bound h hσ hy.1.le k).trans ?_
    have hy2 : y / σ ≤ (t + 1) / σ := div_le_div_of_nonneg_right hy.2.le hσ.le
    have hpos : (0 : ℝ) ≤ 1 / σ := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hpos)
      (Real.exp_pos _).le
  exact hasDerivAt_tsum_of_isPreconnected (y₀ := t) (y := t) hu isOpen_Ioo
    isPreconnected_Ioo hg hg' ⟨ht, by linarith⟩ (subTr_hasSum h hσ ht.le).summable
    ⟨ht, by linarith⟩

/-- The termwise first derivative is differentiable in `t` for `t > 0`, with the termwise
    second derivative. -/
theorem subTr1_hasDerivAt (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    HasDerivAt (subTr1 lam σ) (subTr2 lam σ t) t := by
  have hu : Summable fun k => (1 / σ) ^ 2 * ((t + 1) / σ + 2) * Real.exp (-(σ * lam k)) :=
    (h.summable σ hσ).mul_left _
  have hg : ∀ (k : ι) (y : ℝ), y ∈ Set.Ioo (0 : ℝ) (t + 1) →
      HasDerivAt (fun y : ℝ => -((1 - Real.exp (-(σ * lam k))) / σ)
            * Real.exp (-(y / σ * (1 - Real.exp (-(σ * lam k)))))
          + 1 / σ * Real.exp (-(y / σ)))
        (((1 - Real.exp (-(σ * lam k))) / σ) ^ 2
            * Real.exp (-(y / σ * (1 - Real.exp (-(σ * lam k)))))
          - (1 / σ) ^ 2 * Real.exp (-(y / σ))) y := by
    intro k y _
    have h1 : HasDerivAt (fun y : ℝ => -(y / σ * (1 - Real.exp (-(σ * lam k)))))
        (-(1 / σ * (1 - Real.exp (-(σ * lam k))))) y :=
      (((hasDerivAt_id' y).div_const σ).mul_const _).neg
    have h2 : HasDerivAt (fun y : ℝ => -(y / σ)) (-(1 / σ)) y :=
      ((hasDerivAt_id' y).div_const σ).neg
    exact ((h1.exp.const_mul (-((1 - Real.exp (-(σ * lam k))) / σ))).add
      (h2.exp.const_mul (1 / σ))).congr_deriv (by ring)
  have hg' : ∀ (k : ι) (y : ℝ), y ∈ Set.Ioo (0 : ℝ) (t + 1) →
      ‖((1 - Real.exp (-(σ * lam k))) / σ) ^ 2
            * Real.exp (-(y / σ * (1 - Real.exp (-(σ * lam k)))))
          - (1 / σ) ^ 2 * Real.exp (-(y / σ))‖
        ≤ (1 / σ) ^ 2 * ((t + 1) / σ + 2) * Real.exp (-(σ * lam k)) := by
    intro k y hy
    refine (subTr2_term_bound h hσ hy.1.le k).trans ?_
    have hy2 : y / σ ≤ (t + 1) / σ := div_le_div_of_nonneg_right hy.2.le hσ.le
    have hpos : (0 : ℝ) ≤ (1 / σ) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hpos)
      (Real.exp_pos _).le
  exact hasDerivAt_tsum_of_isPreconnected (y₀ := t) (y := t) hu isOpen_Ioo
    isPreconnected_Ioo hg hg' ⟨ht, by linarith⟩ (subTr1_hasSum h hσ ht.le).summable
    ⟨ht, by linarith⟩

/-- **`T_σ` is twice differentiable in `t`** (first sentence of `thm:corrected`): for `σ > 0`,
    `t > 0` the second derivative of `t ↦ T_σ(t)` is the series `subTr2`. -/
theorem subTr_deriv2 (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    deriv (deriv (subTr lam σ)) t = subTr2 lam σ t := by
  have h1 : deriv (subTr lam σ) =ᶠ[𝓝 t] subTr1 lam σ := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact (subTr_hasDerivAt h hσ hy).deriv
  rw [Filter.EventuallyEq.deriv_eq h1]
  exact (subTr1_hasDerivAt h hσ ht).deriv

/-- **`thm:corrected`, the display, with the constants of the paper.** For `σ > 0`, `t > 0`,
    `τ = t/σ` (the condition `t ≥ σ` of the paper is not needed):
    `|T_σ(t) - (σt/2) T_σ''(t) - Θ(t)| ≤ (σ/t)² [t³|Θ'''(t/2)|/2 + t⁴ Θ''''(t/2)/4]
        + 4(1+τ)² e^{-τ/2} [Θ(σ) + Θ(t/2)]`,
    with `T_σ'' = subTr2` (`subTr_deriv2`), `|Θ'''| = heatMom lam 3`, `Θ'''' = heatMom lam 4`
    (`heatMom_hasDerivAt`). -/
theorem corrected_series (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    |subTr lam σ t - σ * t / 2 * subTr2 lam σ t - heatTr lam t|
      ≤ (σ / t) ^ 2 * (t ^ 3 / 2 * heatMom lam 3 (t / 2) + t ^ 4 / 4 * heatMom lam 4 (t / 2))
        + 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2)) * (heatTr lam σ + heatTr lam (t / 2)) := by
  have ht2 : 0 < t / 2 := by linarith
  have hE := ((subTr_hasSum h hσ ht.le).sub ((subTr2_hasSum h hσ ht.le).mul_left (σ * t / 2))).sub
    (heatTr_hasSum h ht)
  have hR := ((((heatMom_hasSum h 3 ht2).mul_left (t ^ 3 / 2)).add
      ((heatMom_hasSum h 4 ht2).mul_left (t ^ 4 / 4))).mul_left ((σ / t) ^ 2)).add
    (((heatTr_hasSum h hσ).add (heatTr_hasSum h ht2)).mul_left
      (4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2))))
  have pt := fun k => abs_le.1 (mode_corrected_scaled hσ ht (h.nonneg k))
  rw [abs_le]
  constructor
  · have := hasSum_le (fun k => (pt k).1) hR.neg hE
    exact this
  · exact hasSum_le (fun k => (pt k).2) hE hR

/-- `thm:corrected` with the second derivative of the function `t ↦ T_σ(t)` itself. -/
theorem corrected_deriv (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    |subTr lam σ t - σ * t / 2 * deriv (deriv (subTr lam σ)) t - heatTr lam t|
      ≤ (σ / t) ^ 2 * (t ^ 3 / 2 * heatMom lam 3 (t / 2) + t ^ 4 / 4 * heatMom lam 4 (t / 2))
        + 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2)) * (heatTr lam σ + heatTr lam (t / 2)) := by
  rw [subTr_deriv2 h hσ ht]
  exact corrected_series h hσ ht

/-- `thm:corrected` with the derivatives at `t/2` bounded by the heat trace at `t/4`
    (`mom_le_heatTr`): the first term is at most `1728 (σ/t)² Θ(t/4)`. -/
theorem corrected_simple (h : IsSpectrum lam) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    |subTr lam σ t - σ * t / 2 * subTr2 lam σ t - heatTr lam t|
      ≤ 1728 * (σ / t) ^ 2 * heatTr lam (t / 4)
        + 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2)) * (heatTr lam σ + heatTr lam (t / 2)) := by
  have h3 := mom_le_heatTr h 3 ht
  have h4 := mom_le_heatTr h 4 ht
  have e3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  have e4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [e3] at h3
  rw [e4] at h4
  have hq : 0 ≤ (σ / t) ^ 2 := by positivity
  have h5 : (σ / t) ^ 2 * (t ^ 3 / 2 * heatMom lam 3 (t / 2) + t ^ 4 / 4 * heatMom lam 4 (t / 2))
      ≤ (σ / t) ^ 2 * (1728 * heatTr lam (t / 4)) :=
    mul_le_mul_of_nonneg_left (by linarith) hq
  have := corrected_series h hσ ht
  linarith

end Spectrum

/-! #### The flat torus: comparison of heat traces at two times -/

theorem jacA_scale (d : ℕ) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c') :
    jacA d c = Real.sqrt (c' / c) ^ d * jacA d c' := by
  have hpi := Real.pi_pos
  have h1 : Real.sqrt (c / Real.pi) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have h2 : Real.sqrt (c' / c) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have e : c' / Real.pi = c' / c * (c / Real.pi) := by field_simp
  unfold jacA
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← mul_pow]
  congr 1
  rw [e, Real.sqrt_mul (by positivity)]
  field_simp

/-- **On the flat torus `(4πs)^{d/2} Θ(s)` increases with `s`** (Jacobi identity):
    `Θ(s) ≤ (t/s)^{d/2} Θ(t)` for `0 < s ≤ t`. No upper bound on `t`, constant one. -/
theorem heatTr_torus_scale (d : ℕ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    heatTr (torusLam d) s ≤ Real.sqrt (t / s) ^ d * heatTr (torusLam d) t := by
  have hpi := Real.pi_pos
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hcs : 0 < 4 * Real.pi ^ 2 * s := by positivity
  have hct : 0 < 4 * Real.pi ^ 2 * t := by positivity
  have e : 4 * Real.pi ^ 2 * t / (4 * Real.pi ^ 2 * s) = t / s := by field_simp
  have hmono : Real.pi ^ 2 * (4 * Real.pi ^ 2 * t)⁻¹ ≤ Real.pi ^ 2 * (4 * Real.pi ^ 2 * s)⁻¹ :=
    mul_le_mul_of_nonneg_left
      (inv_anti₀ hcs (mul_le_mul_of_nonneg_left hst (by positivity))) (by positivity)
  have hanti := heatTr_anti (lat_isSpectrum d)
    (show 0 < Real.pi ^ 2 * (4 * Real.pi ^ 2 * t)⁻¹ by positivity) hmono
  calc heatTr (torusLam d) s
      = jacA d (4 * Real.pi ^ 2 * s)
          * heatTr (latLam d) (Real.pi ^ 2 * (4 * Real.pi ^ 2 * s)⁻¹) := by
        rw [heatTr_torus_lat, jacobi_lat d hcs]
    _ = Real.sqrt (t / s) ^ d * (jacA d (4 * Real.pi ^ 2 * t)
          * heatTr (latLam d) (Real.pi ^ 2 * (4 * Real.pi ^ 2 * s)⁻¹)) := by
        rw [jacA_scale d hcs hct, e, mul_assoc]
    _ ≤ Real.sqrt (t / s) ^ d * (jacA d (4 * Real.pi ^ 2 * t)
          * heatTr (latLam d) (Real.pi ^ 2 * (4 * Real.pi ^ 2 * t)⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hanti (jacA_pos d hct).le) (by positivity)
    _ = Real.sqrt (t / s) ^ d * heatTr (torusLam d) t := by
        rw [heatTr_torus_lat d t, jacobi_lat d hct]

theorem heatTr_torus_pos (d : ℕ) {t : ℝ} (ht : 0 < t) : 1 ≤ heatTr (torusLam d) t := by
  have hpi := Real.pi_pos
  rw [heatTr_torus]
  exact heatTorus_zero_ge_one (by positivity) d

/-- **`thm:corrected` on the flat torus, relative to the heat trace.** For `0 < σ ≤ t`
    (no upper bound on `t`), `τ = t/σ`:
    `|(T_σ(t) - (σt/2) T_σ''(t))/Θ(t) - 1| ≤ 1728·2^d (σ/t)² + 4(1+τ)² e^{-τ/2} (τ^{d/2} + 2^{d/2})`.
    The second term is exponentially small in `τ`; that it is `O(τ^{-2})` is not stated as a
    separate inequality. -/
theorem corrected_torus (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    |(subTr (torusLam d) σ t - σ * t / 2 * subTr2 (torusLam d) σ t) / heatTr (torusLam d) t - 1|
      ≤ 1728 * 2 ^ d * (σ / t) ^ 2
        + 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2))
            * (Real.sqrt (t / σ) ^ d + Real.sqrt 2 ^ d) := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have ht0 : t ≠ 0 := ht.ne'
  have hpos : 0 < heatTr (torusLam d) t := lt_of_lt_of_le zero_lt_one (heatTr_torus_pos d ht)
  have key := corrected_simple (torus_isSpectrum d) hσ ht
  have e4 : t / (t / 4) = 4 := by field_simp
  have e2 : t / (t / 2) = 2 := by field_simp
  have s4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have g4 := heatTr_torus_scale d (show 0 < t / 4 by linarith) (show t / 4 ≤ t by linarith)
  have g2 := heatTr_torus_scale d (show 0 < t / 2 by linarith) (show t / 2 ≤ t by linarith)
  have gσ := heatTr_torus_scale d hσ hts
  rw [e4, s4] at g4
  rw [e2] at g2
  have hq : 0 ≤ 1728 * (σ / t) ^ 2 := by positivity
  have hK : 0 ≤ 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2)) := by positivity
  have r1 := mul_le_mul_of_nonneg_left g4 hq
  have r2 := mul_le_mul_of_nonneg_left (add_le_add gσ g2) hK
  have e : (subTr (torusLam d) σ t - σ * t / 2 * subTr2 (torusLam d) σ t) / heatTr (torusLam d) t
        - 1
      = (subTr (torusLam d) σ t - σ * t / 2 * subTr2 (torusLam d) σ t - heatTr (torusLam d) t)
        / heatTr (torusLam d) t := by
    field_simp
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  refine key.trans ?_
  nlinarith [r1, r2]

/-- The same with the second derivative of the function `t ↦ T_σ(t)`. -/
theorem corrected_torus_deriv (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    |(subTr (torusLam d) σ t - σ * t / 2 * deriv (deriv (subTr (torusLam d) σ)) t)
          / heatTr (torusLam d) t - 1|
      ≤ 1728 * 2 ^ d * (σ / t) ^ 2
        + 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2))
            * (Real.sqrt (t / σ) ^ d + Real.sqrt 2 ^ d) := by
  rw [subTr_deriv2 (torus_isSpectrum d) hσ (lt_of_lt_of_le hσ hts)]
  exact corrected_torus d hσ hts

/-! #### Connection with the Poisson mean of the other files (`σ' = 2σ`, derivatives in `τ`) -/

/-- Chain rule: the second derivative in `τ` of `τ ↦ poissonMean d (2σ) τ` (`= T_σ(στ)`,
    `subTr_torus`) is `σ² T_σ''(στ)`, for `σ > 0`, `τ > 0`. -/
theorem poissonMean_deriv2 (d : ℕ) {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) :
    deriv (deriv (fun x : ℝ => poissonMean d (2 * σ) x)) τ
      = σ ^ 2 * subTr2 (torusLam d) σ (σ * τ) := by
  have hZ := torus_isSpectrum d
  have hE : ∀ x : ℝ, 0 < x → poissonMean d (2 * σ) x = subTr (torusLam d) σ (σ * x) := by
    intro x hx
    rw [subTr_torus d hσ (mul_pos hσ hx).le]
    congr 1
    field_simp
  have hD1 : ∀ x : ℝ, 0 < x → HasDerivAt (fun x : ℝ => poissonMean d (2 * σ) x)
      (σ * subTr1 (torusLam d) σ (σ * x)) x := by
    intro x hx
    have hin : HasDerivAt (fun y : ℝ => σ * y) σ x := by
      simpa using (hasDerivAt_id' x).const_mul σ
    have hc := HasDerivAt.comp x (subTr_hasDerivAt hZ hσ (mul_pos hσ hx)) hin
    refine (hc.congr_of_eventuallyEq ?_).congr_deriv (by ring)
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hE y hy
  have hD2 : HasDerivAt (fun x : ℝ => σ * subTr1 (torusLam d) σ (σ * x))
      (σ ^ 2 * subTr2 (torusLam d) σ (σ * τ)) τ := by
    have hin : HasDerivAt (fun y : ℝ => σ * y) σ τ := by
      simpa using (hasDerivAt_id' τ).const_mul σ
    have hc := HasDerivAt.comp τ (subTr1_hasDerivAt hZ hσ (mul_pos hσ hτ)) hin
    exact (hc.const_mul σ).congr_deriv (by ring)
  have h1 : deriv (fun x : ℝ => poissonMean d (2 * σ) x)
      =ᶠ[𝓝 τ] fun x : ℝ => σ * subTr1 (torusLam d) σ (σ * x) := by
    filter_upwards [Ioi_mem_nhds hτ] with y hy
    exact (hD1 y hy).deriv
  rw [Filter.EventuallyEq.deriv_eq h1]
  exact hD2.deriv

/-- **Connection with the third file.** On the torus, for `σ > 0`, `t > 0`, the corrected
    quantity `T_σ(t) - (σt/2) T_σ''(t)` of the paper is the series
    `Corrected.corrSeries (t/σ) (heatMode d (2σ))` of `Corrected.corrected_G30` (whose `σ` is
    `ξ² = 2σ`): `(σt/2) ∂_t² = (τ/2) ∂_τ²` at `τ = t/σ`. -/
theorem corrected_torus_corrSeries (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    subTr (torusLam d) σ t - σ * t / 2 * subTr2 (torusLam d) σ t
      = corrSeries (t / σ) (heatMode d (2 * σ)) := by
  have hτ : 0 < t / σ := div_pos ht hσ
  have h := corrected_population (show 0 < 2 * σ by linarith) d (t / σ)
  rw [poissonMean_deriv2 d hσ hτ, ← subTr_torus d hσ ht.le] at h
  have e : σ * (t / σ) = t := by field_simp
  rw [e] at h
  rw [← h]
  field_simp

/-- Hence the population side of `Corrected.corrected_G30` is within the bound of `thm:corrected`
    of the heat trace: for `0 < σ ≤ t`, `τ = t/σ`,
    `|corrSeries τ (heatMode d (2σ))/Θ(t) - 1| ≤ 1728·2^d/τ² + 4(1+τ)² e^{-τ/2}(τ^{d/2} + 2^{d/2})`. -/
theorem corrSeries_torus (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    |corrSeries (t / σ) (heatMode d (2 * σ)) / heatTr (torusLam d) t - 1|
      ≤ 1728 * 2 ^ d * (σ / t) ^ 2
        + 4 * (1 + t / σ) ^ 2 * Real.exp (-(t / σ / 2))
            * (Real.sqrt (t / σ) ^ d + Real.sqrt 2 ^ d) := by
  rw [← corrected_torus_corrSeries d hσ (lt_of_lt_of_le hσ hts)]
  exact corrected_torus d hσ hts

/-! #### (B) The subtracted term of the graph without self-loops -/

/-- **Last sentence of `cor:kernel-noloops`, with `C = 1`.** On the flat torus, with
    `M = p_{ξ²}(0) = Θ(σ)` (`σ = ξ²/2` the `σ` of the paper, `heatTr_torus`), `τ = t/σ` and
    `0 < σ ≤ t` (no upper bound on `t`):
    `τ e^{-τ} M ≤ τ · τ^{d/2} · e^{-τ} · Θ(t)`. -/
theorem noloop_subtraction (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    t / σ * Real.exp (-(t / σ)) * heatTr (torusLam d) σ
      ≤ t / σ * Real.sqrt (t / σ) ^ d * Real.exp (-(t / σ)) * heatTr (torusLam d) t := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have h := mul_le_mul_of_nonneg_left (heatTr_torus_scale d hσ hts)
    (show 0 ≤ t / σ * Real.exp (-(t / σ)) by positivity)
  refine h.trans (le_of_eq ?_)
  ring

/-- Hence the subtracted term is of relative order `τ^{-2}`:
    `τ e^{-τ} M ≤ (d+3)! (σ/t)² Θ(t)` for `0 < σ ≤ t`. -/
theorem noloop_subtraction_rate (d : ℕ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) :
    t / σ * Real.exp (-(t / σ)) * heatTr (torusLam d) σ
      ≤ ((d + 3).factorial : ℝ) * (σ / t) ^ 2 * heatTr (torusLam d) t := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hτ1 : 1 ≤ t / σ := by rw [le_div_iff₀ hσ]; linarith
  have hτ0 : 0 < t / σ := by linarith
  have hΘ : 0 ≤ heatTr (torusLam d) t := heatTr_nonneg _
  have hsq : Real.sqrt (t / σ) ≤ t / σ := Real.sqrt_le_iff.2 ⟨hτ0.le, by nlinarith⟩
  have hsqd : Real.sqrt (t / σ) ^ d ≤ (t / σ) ^ d :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq d
  have hf : (0 : ℝ) < ((d + 3).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (d + 3)
  have h1 : (t / σ) ^ (d + 3) ≤ ((d + 3).factorial : ℝ) * Real.exp (t / σ) := by
    have := Real.pow_div_factorial_le_exp (x := t / σ) hτ0.le (d + 3)
    rwa [div_le_iff₀ hf, mul_comm] at this
  have h2 : (t / σ) ^ (d + 1) * Real.exp (-(t / σ)) ≤ ((d + 3).factorial : ℝ) * (σ / t) ^ 2 := by
    have e : ((d + 3).factorial : ℝ) * (σ / t) ^ 2 = ((d + 3).factorial : ℝ) / (t / σ) ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)]
    calc (t / σ) ^ (d + 1) * Real.exp (-(t / σ)) * (t / σ) ^ 2
        = (t / σ) ^ (d + 3) * Real.exp (-(t / σ)) := by ring
      _ ≤ ((d + 3).factorial : ℝ) * Real.exp (t / σ) * Real.exp (-(t / σ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = ((d + 3).factorial : ℝ) := by
          rw [mul_assoc, ← Real.exp_add]; simp
  have h3 : t / σ * Real.sqrt (t / σ) ^ d * Real.exp (-(t / σ))
      ≤ (t / σ) ^ (d + 1) * Real.exp (-(t / σ)) := by
    have := mul_le_mul_of_nonneg_left hsqd hτ0.le
    have e : t / σ * (t / σ) ^ d = (t / σ) ^ (d + 1) := by ring
    rw [e] at this
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  calc t / σ * Real.exp (-(t / σ)) * heatTr (torusLam d) σ
      ≤ t / σ * Real.sqrt (t / σ) ^ d * Real.exp (-(t / σ)) * heatTr (torusLam d) t :=
        noloop_subtraction d hσ hts
    _ ≤ ((d + 3).factorial : ℝ) * (σ / t) ^ 2 * heatTr (torusLam d) t :=
        mul_le_mul_of_nonneg_right (h3.trans h2) hΘ

/-- The same for the term subtracted in `NoLoopsTrace.noloop_heat_trace_ratio` of the third file,
    in the convention of that file (`σ' = ξ²`, `M = heatTorus d (2π²σ') 0`, `w_1 = pw τ 1`): for
    `σ' > 0`, `τ ≥ 1`, with `Θ` at the time `t = τσ'/2` of the paper,
    `w_1(τ) M ≤ τ · τ^{d/2} e^{-τ} Θ(τσ'/2)` and `w_1(τ) M ≤ (d+3)!/τ² · Θ(τσ'/2)`. -/
theorem noloop_subtraction_lean (d : ℕ) {σ' τ : ℝ} (hσ : 0 < σ') (hτ : 1 ≤ τ) :
    pw τ 1 * heatTorus d (2 * Real.pi ^ 2 * σ') 0
        ≤ τ * Real.sqrt τ ^ d * Real.exp (-τ) * heatTr (torusLam d) (τ * σ' / 2) ∧
    pw τ 1 * heatTorus d (2 * Real.pi ^ 2 * σ') 0
        ≤ ((d + 3).factorial : ℝ) * (1 / τ) ^ 2 * heatTr (torusLam d) (τ * σ' / 2) := by
  have hτ0 : 0 < τ := by linarith
  have hs : 0 < σ' / 2 := by linarith
  have hts : σ' / 2 ≤ τ * σ' / 2 := by nlinarith
  have eτ : τ * σ' / 2 / (σ' / 2) = τ := by field_simp
  have eM : heatTr (torusLam d) (σ' / 2) = heatTorus d (2 * Real.pi ^ 2 * σ') 0 := by
    rw [heatTr_torus]
    congr 1
    ring
  have ew : pw τ 1 = τ * Real.exp (-τ) := by
    unfold pw
    simp
    ring
  have a1 := noloop_subtraction d hs hts
  have a2 := noloop_subtraction_rate d hs hts
  have eq2 : σ' / 2 / (τ * σ' / 2) = 1 / τ := by field_simp
  rw [eτ, eM] at a1
  rw [eτ, eM, eq2] at a2
  rw [ew]
  exact ⟨a1, a2⟩

end CorrectedRate

/-! ## Measurability of further exceptional sets (seventh file and third file)

For the theorems named below the set `{ω | …}` whose `μ.real` is bounded (or tends to zero) is
shown to be measurable, VERBATIM as in the statement (the set expressions were copied by a script
from the statements and compared token by token). Hypotheses: only `σ > 0` (resp. `0 < σ N`) and
measurability of the `X j`.

* seventh file, `SharpRate`: `sharp_rate_prob`, `sharp_rate_prob_small_time`,
  `sharp_rate_prob_explicit` (for each `N` with `σ_N > 0`);
* third file: `SecondStageLimit.second_stage_ceil`, `second_stage_OP`, `second_stage_tight`,
  `second_stage_limit_eventually`; `SecondStageTrace.second_stage_trace`,
  `second_stage_trace_scaled`; `SecondStageTrace2.second_stage_trace2`;
  `NoLoopsTrace.noloop_heat_trace_sample`, `noloop_heat_trace_ratio_small`;
  `Corrected.corrected_G30_tail`; `EigenvaluesL1.eig_l1_sample`;
  `TorusReductionL1.torus_reduction_sample_l1` (quantifier over arbitrary families `ĥ`);
  `EigenspaceFinal.eigspace_final_sample`, `eigspace_final_sample'`, `eigspace_final_sample''`
  (statements about the eigenbasis chosen by Mathlib; measurable because the separation of the
  cluster is part of the statement).

Not covered: `EigenspaceSample.eigspace_sample` (there the cluster need not be separated and the
projection `specProj` depends on the chosen basis); the sets of intermediate theorems. -/

namespace Reals3Sets

open Filter Topology

open CTG.Reals.ExceptionalSets AssembledSets Reals2Sets

/-! ### (1) The sharp rate in probability (seventh file, `SharpRate`) -/

section SharpRateSets

open CTG.Reals.TraceG29 TraceRates PopulationRate SecondStageLimit SharpRate

/-- The set in `SharpRate.sharp_rate_prob` (for each `N` with `σ_N > 0`), verbatim, is
    measurable. -/
theorem sharp_rate_prob_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ t : ℕ → ℝ) (η : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | sharpC2 d * (σ N / 2 / t N) ^ 2 + sharpC1 d * (σ N / 2) + η * σ N
        < |((NormedSpace.exp ((2 * t N / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t N / σ N))) / heatTr (torusLam d) (t N) - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)|} := by
  exact measurableSet_lt measurable_const
    ((((((heat_trace_sample_measurable hσ d X hX N (2 * t N / σ N)).sub
      measurable_const).div_const _).sub measurable_const).sub measurable_const).abs)

/-- The set in `SharpRate.sharp_rate_prob_small_time` (for each `N` with `σ_N > 0`), verbatim,
    is measurable. -/
theorem sharp_rate_prob_small_time_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ t : ℕ → ℝ) (η : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | sharpC2 d * (σ N / 2 / t N) ^ 2 + η * (σ N / 2 / t N)
        < |((NormedSpace.exp ((2 * t N / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t N / σ N))) / heatTr (torusLam d) (t N) - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)|} := by
  exact measurableSet_lt measurable_const
    ((((((heat_trace_sample_measurable hσ d X hX N (2 * t N / σ N)).sub
      measurable_const).div_const _).sub measurable_const).sub measurable_const).abs)

/-- The set in `SharpRate.sharp_rate_prob_explicit` (for each `N` with `σ_N > 0`), verbatim, is
    measurable. -/
theorem sharp_rate_prob_explicit_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ t : ℕ → ℝ) (η : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | η * σ N * (1 + (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)
            + popRem d (σ N / 2) (t N)) + popRem d (σ N / 2) (t N)
        < |((NormedSpace.exp ((2 * t N / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t N / σ N))) / heatTr (torusLam d) (t N) - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t N)|} := by
  exact measurableSet_lt measurable_const
    ((((((heat_trace_sample_measurable hσ d X hX N (2 * t N / σ N)).sub
      measurable_const).div_const _).sub measurable_const).sub measurable_const).abs)

end SharpRateSets

/-! ### (2a) The second stage: limit forms and the unscaled trace forms (third file) -/

section SecondStageSets3

open CTG.Reals.TorusReduction CTG.Reals.TraceG29 TorusReductionL1 H5 PiBound SecondStage

/-- The set in `SecondStageLimit.second_stage_ceil` (for each `N` with `σ_N > 0` and each `s`),
    verbatim, is measurable. -/
theorem second_stage_ceil_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ τ : ℕ → ℝ) (s : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | (redC d
              * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N) ^ 2
            + s * piC d * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / N)) * τ N
          + 14 * (normC d
              * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)) ^ 2
          + 7 * s * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / N)
          + 4 * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / (N : ℝ) ^ 2)
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N (τ N)).sub measurable_const).div_const _).sub
      measurable_const).abs)

/-- The set in `SecondStageLimit.second_stage_OP` (for each `N` with `σ_N > 0`), verbatim, is
    measurable. -/
theorem second_stage_OP_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ τ : ℕ → ℝ) (s : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | (redC d + 14 * normC d ^ 2 + 4 + s * (piC d + 7))
            * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N) * τ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N (τ N)).sub measurable_const).div_const _).sub
      measurable_const).abs)

/-- The set in `SecondStageLimit.second_stage_tight` (for each `N` with `σ_N > 0` and each
    constant `C`), verbatim, is measurable. -/
theorem second_stage_tight_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ τ : ℕ → ℝ) (C : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | C * (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N) * τ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N (τ N)).sub measurable_const).div_const _).sub
      measurable_const).abs)

/-- The set in `SecondStageLimit.second_stage_limit_eventually` (for each `N` with `σ_N > 0`),
    verbatim, is measurable. (It is the same expression as the set of `second_stage_limit`.) -/
theorem second_stage_limit_eventually_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (σ τ : ℕ → ℝ) (η : ℝ) (N : ℕ)
    (hσ : 0 < σ N) :
    MeasurableSet {ω | η * σ N
        < |((NormedSpace.exp (τ N • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ N)) / poissonMean d (σ N) (τ N) - 1|} := by
  exact measurableSet_lt measurable_const
    (((((heat_trace_sample_measurable hσ d X hX N (τ N)).sub measurable_const).div_const _).sub
      measurable_const).abs)

/-- The exceptional set of `SecondStageTrace.second_stage_trace`, verbatim, is measurable. -/
theorem second_stage_trace_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp τ t : ℝ) :
    MeasurableSet {ω | kernelC1 d * δp * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1) + t
        < |(NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|} := by
  exact measurableSet_lt measurable_const
    ((((heat_trace_sample_measurable hσ d X hX N τ).sub measurable_const).sub
      measurable_const).abs)

/-- The exceptional set of `SecondStageTrace.second_stage_trace_scaled`, verbatim, is
    measurable. -/
theorem second_stage_trace_scaled_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp τ s : ℝ) :
    MeasurableSet {ω | kernelC1 d * δp * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1)
          + s * (piC d * (Mp / N)
              * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ k))
        < |(NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|} := by
  exact measurableSet_lt measurable_const
    ((((heat_trace_sample_measurable hσ d X hX N τ).sub measurable_const).sub
      measurable_const).abs)

/-- The exceptional set of `SecondStageTrace2.second_stage_trace2`, verbatim, is measurable. -/
theorem second_stage_trace2_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp τ t : ℝ) :
    MeasurableSet {ω | 14 * (normC d * δp) ^ 2 * (pw τ 1 * Mp)
          + redC d * δp ^ 2 * ∑ k ∈ Finset.Icc 1 J, pw τ (k + 1) * ((k : ℝ) * torusM d σ (k + 1))
          + 3 * Mp * ptail τ (J + 1) + t
        < |(NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - poissonMean d σ τ|} := by
  exact measurableSet_lt measurable_const
    ((((heat_trace_sample_measurable hσ d X hX N τ).sub measurable_const).sub
      measurable_const).abs)

end SecondStageSets3

/-! ### (2b) The graph without self-loops: heat trace -/

section NoLoopsTraceSets3

open NoLoopsTrace CTG.Reals.TraceG29

/-- The trace of the heat operator of the graph without self-loops is a measurable function of
    the sample. -/
theorem noloop_trace_exp_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N : ℕ)
    (τ : ℝ) :
    Measurable fun ω =>
      (NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  have hK : ∀ a b : Fin N, Measurable fun ω => noloopK d σ N (fun j => X j ω) a b := by
    intro a b
    show Measurable fun ω =>
      (if a = b then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X b ω))
    by_cases h : a = b
    · simp only [if_pos h]
      exact measurable_const
    · simp only [if_neg h]
      exact heatTorus_sample_measurable hc d X hX a b
  have hR : ∀ a : Fin N, Measurable fun ω => noloopRho d σ N (fun j => X j ω) a := by
    intro a
    show Measurable fun ω =>
      heatRho d σ N (fun j => X j ω) a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N
    exact (heatRho_sample_measurable hσ d X hX N a).sub_const _
  have hsym : ∀ (ω : Ω) (i j : Fin N),
      noloopK d σ N (fun j => X j ω) i j = noloopK d σ N (fun j => X j ω) j i := by
    intro ω i j
    show (if i = j then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
      = (if j = i then (0 : ℝ) else heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X i ω))
    by_cases h : i = j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h), ← heatTorus_even d _ (X j ω - X i ω), neg_sub]
  exact trace_exp_measurable (fun ω => noloopSym d σ N (fun j => X j ω))
    (fun a b => symGraph_entry_measurable
      (fun ω => noloopK d σ N (fun j => X j ω)) (fun ω => noloopRho d σ N (fun j => X j ω))
      hK hR a b)
    (fun ω => symGraph_isHermitian _ _ (hsym ω)) τ

/-- The exceptional set of `NoLoopsTrace.noloop_heat_trace_sample`, verbatim, is measurable. -/
theorem noloop_heat_trace_sample_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp τ : ℝ) :
    MeasurableSet {ω | ¬ |(NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - (poissonMean d σ τ - pw τ 1 * Mp)|
          ≤ kernelC1 d * δp * Real.sqrt J * (poissonMean d σ τ - pw τ 1 * Mp)
            + 96 * (Mp / N) * Mp * (τ * (1 - Real.exp (-τ)))
            + (3 * Mp + 192 * (Mp / N) * Mp) * ptail τ J} := by
  refine MeasurableSet.compl ?_
  exact measurableSet_le
    ((((noloop_trace_exp_measurable hσ d X hX N τ).sub measurable_const).sub
      measurable_const).abs) measurable_const

/-- The exceptional set of `NoLoopsTrace.noloop_heat_trace_ratio_small`, verbatim, is
    measurable. -/
theorem noloop_heat_trace_ratio_small_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (N J : ℕ) (Mp δp τ : ℝ) :
    MeasurableSet {ω | ¬ |((NormedSpace.exp (τ • (noloopSym d σ N (fun j => X j ω) - 1))).trace
            - (N : ℝ) * Real.exp (-τ) - (poissonMean d σ τ - pw τ 1 * Mp)) / poissonMean d σ τ|
          ≤ (kernelC1 d + 96) * δp * Real.sqrt J + 5 * Mp / (N : ℝ) ^ 2} := by
  refine MeasurableSet.compl ?_
  exact measurableSet_le
    (((((noloop_trace_exp_measurable hσ d X hX N τ).sub measurable_const).sub
      measurable_const).div_const _).abs) measurable_const

end NoLoopsTraceSets3

/-! ### (2c) The corrected estimator with the explicit tail: `Corrected.corrected_G30_tail` -/

section CorrectedSets3

open Corrected CTG.Reals.TraceG29

/-- The exceptional set of `Corrected.corrected_G30_tail`, verbatim, is measurable. -/
theorem corrected_G30_tail_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ τ : ℝ, 2 ≤ τ → 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1 →
        |corrSeries τ (fun k : ℕ => ((symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace)
            - corrSeries τ (heatMode d σ)|
          ≤ (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ)) * poissonMean d σ τ
            + (3 + 6 * τ) * Mp / (N : ℝ) ^ 2} := by
  refine MeasurableSet.compl ?_
  refine MeasurableSet.congr (forall_param_measurable'
    (p := fun τ : ℝ => 2 ≤ τ ∧ 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1)
    (h := fun ω τ => |corrSeries τ (fun k : ℕ => ((symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace)
            - corrSeries τ (heatMode d σ)|)
    (g := fun τ => (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ))
            * poissonMean d σ τ
            + (3 + 6 * τ) * Mp / (N : ℝ) ^ 2) ?_ ?_ ?_) ?_
  · intro τ
    exact ((corrSeries_trace_measurable
      (fun ω => symGraph
        (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
        (fun a : Fin N => heatRho d σ N (fun j => X j ω) a))
      (fun a b => symGraph_rho_entry_measurable hσ d X hX N a b)
      (fun ω => symGraph_rho_isHermitian d N X ω) τ).sub measurable_const).abs
  · intro ω B
    have hsub : {τ : ℝ | (2 ≤ τ ∧ 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1) ∧ τ ≤ B}
        ⊆ Set.Icc 0 B := fun τ hτ => ⟨le_trans (by norm_num) hτ.1.1, hτ.2⟩
    have hS : Continuous fun τ : ℝ => corrSeries τ (fun k : ℕ => ((symGraph
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
          (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace) := by
      have e := fun τ : ℝ => corrSeries_matrix (symGraph
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
          (fun a : Fin N => heatRho d σ N (fun j => X j ω) a))
        (symGraph_rho_isHermitian d N X ω) τ
      rw [funext e]
      fun_prop
    exact (hS.continuousOn.sub ((corrSeries_heatMode_continuousOn hσ d B).mono hsub)).abs
  · intro B
    have hsub : {τ : ℝ | (2 ≤ τ ∧ 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1) ∧ τ ≤ B}
        ⊆ Set.Icc 0 B := fun τ hτ => ⟨le_trans (by norm_num) hτ.1.1, hτ.2⟩
    have hT := (poissonMean_continuousOn hσ d B).mono hsub
    have h1 : Continuous fun τ : ℝ =>
        (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ)) := by fun_prop
    have h2 : Continuous fun τ : ℝ => (3 + 6 * τ) * Mp / (N : ℝ) ^ 2 := by fun_prop
    exact (h1.continuousOn.mul hT).add h2.continuousOn
  · exact Set.ext fun ω => ⟨fun H τ h1 h2 => H τ ⟨h1, h2⟩, fun H τ h => H τ h.1 h.2⟩

end CorrectedSets3

/-! ### (2d) Eigenvalues against the kernel matrix: `EigenvaluesL1.eig_l1_sample` -/

section EigL1Sets

open EigenvaluesL1

theorem eigTot_eq' {N : ℕ} (A : Fin N → Fin N → ℝ) (h : (Matrix.of A).IsHermitian)
    (j : Fin (Fintype.card (Fin N))) : eigTot N j A = h.eigenvalues₀ j := by
  unfold eigTot
  exact dif_pos h

/-- The exceptional set of `EigenvaluesL1.eig_l1_sample`, verbatim, is measurable (two symmetric
    matrices: the graph matrix and the kernel matrix). -/
theorem eig_l1_sample_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N K : ℕ)
    (δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (hQ : (Matrix.of fun a i : Fin N =>
              heatP d σ k (X a ω - X i ω) / (N : ℝ)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          |hS.eigenvalues₀ j ^ k - hQ.eigenvalues₀ j| ≤ eigL1C d * δp * Real.sqrt k} := by
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp ?_)
  have hS0 : ∀ ω, (Matrix.of fun a b : Fin N => symGraph
      (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
      (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) a b).IsHermitian := fun ω =>
    symGraph_rho_isHermitian d N X ω
  have hQ0 : ∀ ω, (Matrix.of fun a i : Fin N =>
      heatP d σ k (X a ω - X i ω) / (N : ℝ)).IsHermitian := by
    intro ω
    refine Matrix.IsHermitian.ext fun a i => ?_
    show star (heatP d σ k (X i ω - X a ω) / (N : ℝ)) = heatP d σ k (X a ω - X i ω) / (N : ℝ)
    rw [star_trivial, ← heatP_neg_eq d σ k (X a ω - X i ω), neg_sub]
  have hmS : Measurable fun ω => (fun a b : Fin N => symGraph
      (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
      (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) a b) :=
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b =>
      symGraph_rho_entry_measurable hσ d X hX N a b
  have hmQ : Measurable fun ω => (fun a i : Fin N =>
      heatP d σ k (X a ω - X i ω) / (N : ℝ)) :=
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i =>
      (heatP_sample_measurable hσ d X hX k a i).div_const _
  refine MeasurableSet.congr (ms_forall fun j : Fin (Fintype.card (Fin N)) => measurableSet_le
    ((((eigTot_measurable_comp j _ hmS hS0).pow_const k).sub
      (eigTot_measurable_comp j _ hmQ hQ0)).abs)
    (measurable_const (a := eigL1C d * δp * Real.sqrt k))) ?_
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h hS hQ j
    have h1 := h j
    rw [eigTot_eq' _ (hS0 ω) j, eigTot_eq' _ (hQ0 ω) j] at h1
    exact h1
  · intro h j
    rw [eigTot_eq' _ (hS0 ω) j, eigTot_eq' _ (hQ0 ω) j]
    exact h (hS0 ω) (hQ0 ω) j

end EigL1Sets

/-! ### (2e) The reduction with an arbitrary family `ĥ`: `TorusReductionL1.torus_reduction_sample_l1`

The set quantifies over all constants `cα, cβ ≥ 0` and ALL families `hh : ℕ → Fin N → Fin N → ℝ`.
Only the members `hh m`, `m ≤ k`, enter, so the quantifier runs over a finite-dimensional
(`σ`-compact) parameter space; the hypotheses (H5a)--(H5d) are closed conditions and the failure
of the conclusion is an open condition in (data, parameters), all depending continuously on
finitely many measurable real functions of the sample. The bad set is therefore the preimage of
a projection of `closed ∩ open` along a `σ`-compact factor (`proj_measurable`). -/

section ReductionL1Sets

open CTG.Reals.TorusReduction TorusReductionL1

/-- Extension by zero of a family indexed by `Fin n` to all of `ℕ`. -/
def ext0 {α : Type*} [Zero α] (n : ℕ) (p : Fin n → α) (m : ℕ) : α :=
  if h : m < n then p ⟨m, h⟩ else 0

theorem ext0_restrict {α : Type*} [Zero α] {n : ℕ} (f : ℕ → α) {m : ℕ} (h : m < n) :
    ext0 n (fun m' : Fin n => f m') m = f m := by
  unfold ext0
  exact dif_pos h

theorem ext0_continuous {n N : ℕ} (m : ℕ) (i b : Fin N) :
    Continuous fun p : Fin n → Fin N → Fin N → ℝ => ext0 n p m i b := by
  unfold ext0
  by_cases h : m < n
  · simp only [dif_pos h]
    fun_prop
  · simp only [dif_neg h]
    exact continuous_const

/-- The four hypotheses (H5a)--(H5d) with abstract defect `D` and abstract bounds. -/
def H5Like (N k : ℕ) (D hh : ℕ → Fin N → Fin N → ℝ) (b1 b2 b3 b4 : ℕ → ℝ) : Prop :=
  (∀ m, 1 ≤ m → m ≤ k → ∀ i b : Fin N, |D m i b - hh m i b| ≤ b1 m) ∧
  (∀ m, 1 ≤ m → m ≤ k → ∀ i : Fin N, ∑ b : Fin N, |D m i b - hh m i b| ≤ b2 m) ∧
  (∀ m, 1 ≤ m → m ≤ k → ∀ i b : Fin N, |hh m i b| ≤ b3 m) ∧
  (∀ m, 1 ≤ m → m ≤ k → ∀ i : Fin N, ∑ b : Fin N, |hh m i b| ≤ b4 m)

theorem H5Like_of_congr {N k : ℕ} {D D' hh hh' : ℕ → Fin N → Fin N → ℝ} {b1 b2 b3 b4 : ℕ → ℝ}
    (hD : ∀ m, m ≤ k → D m = D' m) (hh0 : ∀ m, m ≤ k → hh m = hh' m)
    (H : H5Like N k D hh b1 b2 b3 b4) : H5Like N k D' hh' b1 b2 b3 b4 := by
  obtain ⟨a, b, c, e⟩ := H
  refine ⟨fun m h1 h2 => ?_, fun m h1 h2 => ?_, fun m h1 h2 => ?_, fun m h1 h2 => ?_⟩
  · rw [← hD m h2, ← hh0 m h2]
    exact a m h1 h2
  · rw [← hD m h2, ← hh0 m h2]
    exact b m h1 h2
  · rw [← hh0 m h2]
    exact c m h1 h2
  · rw [← hh0 m h2]
    exact e m h1 h2

/-- The statistic `Π_k` with abstract first term `A` and abstract kernels `Q`. -/
noncomputable def piLike (N k : ℕ) (A : ℝ) (Q hh : ℕ → Fin N → Fin N → ℝ) : ℝ :=
  A + ∑ m ∈ Finset.Icc 1 (k - 1),
        1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N, Q (k - m) i b * hh m i b
    + 1 / (N : ℝ) * ∑ i : Fin N, hh k i i

theorem piLike_congr {N k : ℕ} {A : ℝ} {Q Q' hh hh' : ℕ → Fin N → Fin N → ℝ}
    (hQ : ∀ m, m ≤ k → Q m = Q' m) (hh0 : ∀ m, m ≤ k → hh m = hh' m) :
    piLike N k A Q hh = piLike N k A Q' hh' := by
  unfold piLike
  rw [hh0 k le_rfl]
  congr 2
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_Icc] at hm
  rw [hQ (k - m) (Nat.sub_le _ _), hh0 m (by omega)]

/-- Data space and parameter space of the projection argument. -/
abbrev RedY (N k : ℕ) : Type :=
  ℝ × ℝ × (Fin (k + 1) → Fin N → Fin N → ℝ) × (Fin (k + 1) → Fin N → Fin N → ℝ)

abbrev RedP (N k : ℕ) : Type := ℝ × ℝ × (Fin (k + 1) → Fin N → Fin N → ℝ)

/-- A bound for `|T - Π_k(hh)|` for ALL constants `cα, cβ ≥ 0` and ALL families `hh` satisfying
    (H5a)--(H5d) is a measurable condition, if the data `T`, `A`, `D`, `Q` are measurable and
    the bounds are continuous in the constants. -/
theorem reduction_param_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} (k : ℕ)
    (T A : Ω → ℝ) (D Q : Ω → ℕ → Fin N → Fin N → ℝ) (hT : Measurable T) (hA : Measurable A)
    (hD : ∀ (m : ℕ) (i b : Fin N), Measurable fun ω => D ω m i b)
    (hQ : ∀ (m : ℕ) (i b : Fin N), Measurable fun ω => Q ω m i b)
    (b1 b2 b3 b4 : ℝ → ℕ → ℝ) (hb1 : ∀ m, Continuous fun c => b1 c m)
    (hb2 : ∀ m, Continuous fun c => b2 c m) (hb3 : ∀ m, Continuous fun c => b3 c m)
    (hb4 : ∀ m, Continuous fun c => b4 c m) (F : ℝ → ℝ → ℝ)
    (hF : Continuous fun q : ℝ × ℝ => F q.1 q.2) :
    MeasurableSet {ω | ∀ (cα cβ : ℝ) (hh : ℕ → Fin N → Fin N → ℝ), 0 ≤ cα → 0 ≤ cβ →
      H5Like N k (D ω) hh (b1 cα) (b2 cα) (b3 cβ) (b4 cβ) →
      |T ω - piLike N k (A ω) (Q ω) hh| ≤ F cα cβ} := by
  have cT : Continuous fun q : RedY N k × RedP N k => q.1.1 := by fun_prop
  have cA : Continuous fun q : RedY N k × RedP N k => q.1.2.1 := by fun_prop
  have cα : Continuous fun q : RedY N k × RedP N k => q.2.1 := by fun_prop
  have cβ : Continuous fun q : RedY N k × RedP N k => q.2.2.1 := by fun_prop
  have cD : ∀ (m : ℕ) (i b : Fin N), Continuous fun q : RedY N k × RedP N k =>
      ext0 (k + 1) q.1.2.2.1 m i b := fun m i b =>
    (ext0_continuous m i b).comp (by fun_prop)
  have cQ : ∀ (m : ℕ) (i b : Fin N), Continuous fun q : RedY N k × RedP N k =>
      ext0 (k + 1) q.1.2.2.2 m i b := fun m i b =>
    (ext0_continuous m i b).comp (by fun_prop)
  have cH : ∀ (m : ℕ) (i b : Fin N), Continuous fun q : RedY N k × RedP N k =>
      ext0 (k + 1) q.2.2.2 m i b := fun m i b =>
    (ext0_continuous m i b).comp (by fun_prop)
  have hC : IsClosed {q : RedY N k × RedP N k | 0 ≤ q.2.1 ∧ 0 ≤ q.2.2.1 ∧
      H5Like N k (ext0 (k + 1) q.1.2.2.1) (ext0 (k + 1) q.2.2.2)
        (b1 q.2.1) (b2 q.2.1) (b3 q.2.2.1) (b4 q.2.2.1)} := by
    unfold H5Like
    refine IsClosed.inter (isClosed_le continuous_const cα) ?_
    refine IsClosed.inter (isClosed_le continuous_const cβ) ?_
    refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
    · exact isClosed_setOf_forall fun m => isClosed_setOf_forall fun _ =>
        isClosed_setOf_forall fun _ => isClosed_setOf_forall fun i =>
        isClosed_setOf_forall fun b =>
          isClosed_le ((cD m i b).sub (cH m i b)).abs ((hb1 m).comp cα)
    · exact isClosed_setOf_forall fun m => isClosed_setOf_forall fun _ =>
        isClosed_setOf_forall fun _ => isClosed_setOf_forall fun i =>
          isClosed_le (continuous_finset_sum _ fun b _ => ((cD m i b).sub (cH m i b)).abs)
            ((hb2 m).comp cα)
    · exact isClosed_setOf_forall fun m => isClosed_setOf_forall fun _ =>
        isClosed_setOf_forall fun _ => isClosed_setOf_forall fun i =>
        isClosed_setOf_forall fun b => isClosed_le (cH m i b).abs ((hb3 m).comp cβ)
    · exact isClosed_setOf_forall fun m => isClosed_setOf_forall fun _ =>
        isClosed_setOf_forall fun _ => isClosed_setOf_forall fun i =>
          isClosed_le (continuous_finset_sum _ fun b _ => (cH m i b).abs) ((hb4 m).comp cβ)
  have hU : IsOpen {q : RedY N k × RedP N k | F q.2.1 q.2.2.1
      < |q.1.1 - piLike N k q.1.2.1 (ext0 (k + 1) q.1.2.2.2) (ext0 (k + 1) q.2.2.2)|} := by
    unfold piLike
    refine isOpen_lt (hF.comp (cα.prodMk cβ)) ?_
    exact (cT.sub ((cA.add (continuous_finset_sum _ fun m _ => continuous_const.mul
      (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun b _ =>
        (cQ (k - m) i b).mul (cH m i b)))).add
      (continuous_const.mul (continuous_finset_sum _ fun i _ => cH k i i)))).abs
  have hD' : Measurable fun ω => (fun (m : Fin (k + 1)) => D ω m) :=
    measurable_pi_lambda _ fun m => measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun b => hD m i b
  have hQ' : Measurable fun ω => (fun (m : Fin (k + 1)) => Q ω m) :=
    measurable_pi_lambda _ fun m => measurable_pi_lambda _ fun i =>
      measurable_pi_lambda _ fun b => hQ m i b
  have hΦ : Measurable fun ω => ((T ω, A ω, (fun (m : Fin (k + 1)) => D ω m),
      (fun (m : Fin (k + 1)) => Q ω m)) : RedY N k) :=
    hT.prodMk (hA.prodMk (hD'.prodMk hQ'))
  haveI i1 : OpensMeasurableSpace
      ((Fin (k + 1) → Fin N → Fin N → ℝ) × (Fin (k + 1) → Fin N → Fin N → ℝ)) := inferInstance
  haveI i2 : OpensMeasurableSpace
      (ℝ × (Fin (k + 1) → Fin N → Fin N → ℝ) × (Fin (k + 1) → Fin N → Fin N → ℝ)) :=
    inferInstance
  haveI i3 : OpensMeasurableSpace (RedY N k) := Prod.opensMeasurableSpace
  refine (MeasurableSet.compl (hΦ (proj_measurable hC hU))).congr ?_
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage]
  constructor
  · intro h cα' cβ' hh h0 h1 hR
    by_contra hcon
    refine h ⟨(cα', cβ', fun (m : Fin (k + 1)) => hh m), ⟨h0, h1, ?_⟩, ?_⟩
    · exact H5Like_of_congr (fun m hm => (ext0_restrict (D ω) (by omega)).symm)
        (fun m hm => (ext0_restrict hh (by omega)).symm) hR
    · rw [piLike_congr (Q' := Q ω) (hh' := hh)
        (fun m hm => ext0_restrict (Q ω) (by omega))
        (fun m hm => ext0_restrict hh (by omega))]
      exact not_le.1 hcon
  · rintro h ⟨⟨cα', cβ', p⟩, ⟨h0, h1, hR⟩, hu⟩
    have hb := h cα' cβ' (ext0 (k + 1) p) h0 h1
      (H5Like_of_congr (fun m hm => ext0_restrict (D ω) (by omega)) (fun m hm => rfl) hR)
    rw [piLike_congr (Q' := Q ω) (hh' := ext0 (k + 1) p)
      (fun m hm => ext0_restrict (Q ω) (by omega)) (fun m hm => rfl)] at hu
    exact absurd hu (not_lt.2 hb)

/-- The exceptional set of `TorusReductionL1.torus_reduction_sample_l1`, verbatim (with the
    quantifier over arbitrary families `hh`), is measurable. -/
theorem torus_reduction_sample_l1_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N K : ℕ)
    (δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (cα cβ : ℝ) (hh : ℕ → Fin N → Fin N → ℝ),
          0 ≤ cα → 0 ≤ cβ →
          RemainingH5 d σ N (fun j => X j ω) k hh cα cβ δp →
          |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)
              - torusPi d σ N (fun j => X j ω) k hh|
            ≤ (Real.sqrt 2) ^ d
                * (2 * (4 * normC d) * kernelC1 d + 2 * (14 * normC d ^ 2) + cα
                    + 2 * (2 * (Real.sqrt 2) ^ d * cα + cα
                        + (Real.sqrt 2) ^ d * kernelC1 d * cβ + h4C d * cβ))
                * δp ^ 2 * k * torusM d σ (k + 1)} := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by
    have := Real.pi_pos; positivity
  have hK : ∀ a j : Fin N, Measurable fun ω => torusK d σ N (fun j => X j ω) a j := fun a j =>
    heatTorus_sample_measurable hc d X hX a j
  have hR : ∀ a : Fin N, Measurable fun ω => torusRho d σ N (fun j => X j ω) a := fun a =>
    heatRho_sample_measurable hσ d X hX N a
  have hQ : ∀ (s : ℕ) (a b : Fin N), Measurable fun ω => torusQ d σ N (fun j => X j ω) s a b :=
    fun s a b => heatP_sample_measurable hσ d X hX s a b
  have hTh : ∀ b i : Fin N, Measurable fun ω => torusTheta1 d σ N (fun j => X j ω) b i := by
    intro b i
    unfold torusTheta1 ShellAndWalk.walkTheta1
    exact ((((hR i).sub_const 1).neg).sub ((hR b).sub_const 1)).add
      ((Finset.measurable_sum _ fun j _ => (hK b j).mul ((hR j).sub_const 1)).div_const _)
  have hW : ∀ a b : Fin N, Measurable fun ω => torusWalk d σ N (fun j => X j ω) a b :=
    fun a b => walk_entry_measurable hσ d X hX N a b
  refine MeasurableSet.compl ?_
  refine ms_forall fun k => ms_imp (ms_imp ?_)
  exact reduction_param_measurable k
    (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1))
    (fun ω => 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ b : Fin N,
      torusQ d σ N (fun j => X j ω) k i b * torusQ d σ N (fun j => X j ω) 1 b i
        * torusTheta1 d σ N (fun j => X j ω) b i)
    (fun ω m i b => (∑ j : Fin N, torusWalk d σ N (fun j => X j ω) b j
        * torusQ d σ N (fun j => X j ω) m j i) - torusQ d σ N (fun j => X j ω) (m + 1) b i)
    (fun ω => torusQ d σ N (fun j => X j ω))
    ((pow_trace_measurable (fun ω => torusWalk d σ N (fun j => X j ω)) hW (k + 1)).sub
      measurable_const)
    ((Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun b _ =>
      ((hQ k i b).mul (hQ 1 b i)).mul (hTh b i)).const_mul _)
    (fun m i b => (Finset.measurable_sum _ fun j _ => (hW b j).mul (hQ m j i)).sub
      (hQ (m + 1) b i))
    (fun m i b => hQ m i b)
    (fun c m => c * δp ^ 2 * (1 / Real.sqrt m) * torusM d σ (6 * m))
    (fun c m => (N : ℝ) * (c * δp ^ 2 * (1 / Real.sqrt m)))
    (fun c m => c * δp * (1 / Real.sqrt m) * torusM d σ (6 * m))
    (fun c m => (N : ℝ) * (c * δp * (1 / Real.sqrt m)))
    (fun m => by fun_prop) (fun m => by fun_prop) (fun m => by fun_prop) (fun m => by fun_prop)
    (fun cα cβ => (Real.sqrt 2) ^ d
                * (2 * (4 * normC d) * kernelC1 d + 2 * (14 * normC d ^ 2) + cα
                    + 2 * (2 * (Real.sqrt 2) ^ d * cα + cα
                        + (Real.sqrt 2) ^ d * kernelC1 d * cβ + h4C d * cβ))
                * δp ^ 2 * k * torusM d σ (k + 1))
    (by fun_prop)

end ReductionL1Sets

/-! ### (3) Eigenspaces: `EigenspaceFinal.eigspace_final_sample`, `'`, `''`

The sets contain `specProj` and `evec`, i.e. vectors of the eigenbasis chosen by Mathlib. For
`EigenspaceSample.eigspace_sample` this was an obstacle, because there the projection may split
an eigenspace. Here the first clause of `EigspaceConcl` is the separation of the cluster, and
where the cluster is separated the matrix `Π_J = ∑_{i∈J} v_i v_iᵀ` is the spectral projection,
a function of the matrix alone. Its entries are obtained as the limit of entries of polynomials
of the matrix with measurable coefficients: with `g(x) = ∏_{i'∉J} (x - λ_{i'})²` and
`c = 1 + ∑_i g(λ_i)`, `1 - (1 - g(λ_i)/c)^n → 1_{i∈J}` on the separated set. -/

section SpectralProjection

open EigenspaceSteps EigenspaceSample

/-- `∑_i β_i v_i(a) v_i(b)`: the entries of `β(A)` in the eigenbasis of Mathlib. -/
noncomputable def funMat {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (β : Fin N → ℝ) (a b : Fin N) : ℝ := ∑ i, β i * evec hA i a * evec hA i b

theorem evec_complete {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (a b : Fin N) : ∑ i, evec hA i a * evec hA i b = if a = b then 1 else 0 := by
  have h1 : (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ)
      * star (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    Unitary.coe_mul_star_self _
  have h2 := congrFun (congrFun h1 a) b
  rw [Matrix.one_apply] at h2
  rw [← h2, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  simp only [Matrix.mul_apply, transpose_apply, unitary_apply]

theorem funMat_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (a b : Fin N) :
    funMat hA (fun _ => 1) a b = if a = b then 1 else 0 := by
  unfold funMat
  simp only [one_mul]
  exact evec_complete A hA a b

theorem funMat_eig {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (a b : Fin N) :
    funMat hA hA.eigenvalues a b = A a b := by
  have h1 : A a b = ∑ c, A a c * ∑ i, evec hA i c * evec hA i b := by
    simp only [evec_complete A hA, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [h1]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold funMat
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ∑ c, A a c * evec hA i c = hA.eigenvalues i * evec hA i a := by
    have := congrFun (mulVec_evec A hA i) a
    simpa [mulVec, dotProduct] using this
  rw [← h2, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem funMat_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (β γ : Fin N → ℝ) (a b : Fin N) :
    ∑ c, funMat hA β a c * funMat hA γ c b = funMat hA (fun i => β i * γ i) a b := by
  unfold funMat
  simp only [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  have h : ∀ j, ∑ c, β i * evec hA i a * evec hA i c * (γ j * evec hA j c * evec hA j b)
      = β i * evec hA i a * (γ j * evec hA j b) * (if i = j then 1 else 0) := by
    intro j
    rw [← evec_orthonormal A hA i j]
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

/-- `Π_J w` through the entries `∑_{i∈J} v_i(a) v_i(b)`. -/
theorem specProj_eq_funMat {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (J : Finset (Fin N)) (w : Fin N → ℝ) (a : Fin N) :
    specProj hA J w a = ∑ b, funMat hA (fun i => if i ∈ J then (1 : ℝ) else 0) a b * w b := by
  have h : ∀ i, ∑ b, (if i ∈ J then (1 : ℝ) else 0) * evec hA i a * evec hA i b * w b
      = if i ∈ J then (evec hA i ⬝ᵥ w) * evec hA i a else 0 := by
    intro i
    by_cases hi : i ∈ J
    · simp only [if_pos hi, one_mul, dotProduct]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => by ring
    · simp only [if_neg hi, zero_mul, Finset.sum_const_zero]
  unfold specProj funMat
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The eigenvalues (in the indexing of the eigenbasis) of a measurable family of symmetric
    matrices are measurable. -/
theorem eigenvalue_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    (M : Ω → Matrix (Fin N) (Fin N) ℝ) (hM : ∀ a b, Measurable fun ω => M ω a b)
    (hH : ∀ ω, (M ω).IsHermitian) (i : Fin N) :
    Measurable fun ω => (hH ω).eigenvalues i := by
  have e : (fun ω => (hH ω).eigenvalues i)
      = fun ω => eigTot N (ord N i) (fun a b => M ω a b) := by
    funext ω
    rw [eigTot_eq (M ω) (hH ω)]
    rfl
  rw [e]
  exact eigTot_measurable_comp _ (fun ω a b => M ω a b)
    (measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hM a b) (fun ω => hH ω)

/-- A family of spectral weights `β_i(ω)` for which the entries of `β(M ω)` are measurable. -/
def GoodFam {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hH : ∀ ω, (M ω).IsHermitian) (β : Ω → Fin N → ℝ) : Prop :=
  ∀ a b, Measurable fun ω => funMat (hH ω) (β ω) a b

theorem good_const {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hH : ∀ ω, (M ω).IsHermitian) (c : Ω → ℝ) (hc : Measurable c) :
    GoodFam M hH (fun ω _ => c ω) := by
  intro a b
  have e : (fun ω => funMat (hH ω) (fun _ => c ω) a b)
      = fun ω => c ω * (if a = b then 1 else 0) := by
    funext ω
    rw [← funMat_one (M ω) (hH ω) a b]
    unfold funMat
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact hc.mul_const _

theorem good_eig {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hM : ∀ a b, Measurable fun ω => M ω a b) (hH : ∀ ω, (M ω).IsHermitian) :
    GoodFam M hH (fun ω => (hH ω).eigenvalues) := by
  intro a b
  have e : (fun ω => funMat (hH ω) (hH ω).eigenvalues a b) = fun ω => M ω a b :=
    funext fun ω => funMat_eig (M ω) (hH ω) a b
  rw [e]
  exact hM a b

theorem good_sub {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hH : ∀ ω, (M ω).IsHermitian) {β γ : Ω → Fin N → ℝ} (hβ : GoodFam M hH β)
    (hγ : GoodFam M hH γ) : GoodFam M hH (fun ω i => β ω i - γ ω i) := by
  intro a b
  have e : (fun ω => funMat (hH ω) (fun i => β ω i - γ ω i) a b)
      = fun ω => funMat (hH ω) (β ω) a b - funMat (hH ω) (γ ω) a b := by
    funext ω
    unfold funMat
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact (hβ a b).sub (hγ a b)

theorem good_mul {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hH : ∀ ω, (M ω).IsHermitian) {β γ : Ω → Fin N → ℝ} (hβ : GoodFam M hH β)
    (hγ : GoodFam M hH γ) : GoodFam M hH (fun ω i => β ω i * γ ω i) := by
  intro a b
  have e : (fun ω => funMat (hH ω) (fun i => β ω i * γ ω i) a b)
      = fun ω => ∑ c, funMat (hH ω) (β ω) a c * funMat (hH ω) (γ ω) c b :=
    funext fun ω => (funMat_mul (M ω) (hH ω) (β ω) (γ ω) a b).symm
  rw [e]
  exact Finset.measurable_sum _ fun c _ => (hβ a c).mul (hγ c b)

theorem good_pow {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hH : ∀ ω, (M ω).IsHermitian) {β : Ω → Fin N → ℝ} (hβ : GoodFam M hH β) (n : ℕ) :
    GoodFam M hH (fun ω i => β ω i ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact good_const M hH (fun _ => 1) measurable_const
  | succ n ih =>
    simp only [pow_succ]
    exact good_mul M hH ih hβ

theorem good_prod {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Ω → Matrix (Fin N) (Fin N) ℝ)
    (hH : ∀ ω, (M ω).IsHermitian) {κ : Type*} (s : Finset κ) (β : κ → Ω → Fin N → ℝ)
    (hβ : ∀ j ∈ s, GoodFam M hH (β j)) : GoodFam M hH (fun ω i => ∏ j ∈ s, β j ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact good_const M hH (fun _ => 1) measurable_const
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact good_mul M hH (hβ j (Finset.mem_insert_self j s))
      (ih fun j' hj' => hβ j' (Finset.mem_insert_of_mem hj'))

/-- `g(λ_i) = ∏_{i' ∉ J} (λ_i - λ_{i'})²`. -/
noncomputable def clusterG {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (J : Finset (Fin N)) (i : Fin N) : ℝ :=
  ∏ i' ∈ Jᶜ, (hA.eigenvalues i - hA.eigenvalues i') ^ 2

/-- `1/c`, `c = 1 + ∑_i g(λ_i)`. -/
noncomputable def clusterC {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian)
    (J : Finset (Fin N)) : ℝ := (1 + ∑ i, clusterG hA J i)⁻¹

/-- Separation of a cluster `J` of indices of the eigenbasis: the eigenvalues with index in `J`
    differ from all others (the first clause of `EigspaceConcl`). -/
def Sep {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.IsHermitian) (J : Finset (Fin N)) :
    Prop := ∀ i ∈ J, ∀ i', i' ∉ J → hA.eigenvalues i ≠ hA.eigenvalues i'

theorem cluster_tendsto {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (J : Finset (Fin N)) (hsep : Sep hA J) (i : Fin N) :
    Tendsto (fun n : ℕ => 1 - (1 - clusterC hA J * clusterG hA J i) ^ n) atTop
      (𝓝 (if i ∈ J then 1 else 0)) := by
  have hG0 : ∀ i, 0 ≤ clusterG hA J i := fun i => Finset.prod_nonneg fun i' _ => sq_nonneg _
  have hS0 : 0 ≤ ∑ i, clusterG hA J i := Finset.sum_nonneg fun i _ => hG0 i
  have hpos : 0 < 1 + ∑ i, clusterG hA J i := by linarith
  have hle : clusterG hA J i ≤ ∑ i, clusterG hA J i :=
    Finset.single_le_sum (fun i _ => hG0 i) (Finset.mem_univ i)
  by_cases hi : i ∈ J
  · rw [if_pos hi]
    have hGi : 0 < clusterG hA J i := Finset.prod_pos fun i' hi' => by
      have hne := hsep i hi i' (Finset.mem_compl.1 hi')
      have : hA.eigenvalues i - hA.eigenvalues i' ≠ 0 := sub_ne_zero.2 hne
      positivity
    have hx0 : 0 < clusterC hA J * clusterG hA J i := mul_pos (inv_pos.2 hpos) hGi
    have hx1 : clusterC hA J * clusterG hA J i < 1 := by
      unfold clusterC
      rw [inv_mul_lt_iff₀ hpos, mul_one]
      linarith
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
      (r := 1 - clusterC hA J * clusterG hA J i) (by linarith) (by linarith)
    have h2 := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).sub ht
    rw [sub_zero] at h2
    exact h2
  · rw [if_neg hi]
    have hGi : clusterG hA J i = 0 :=
      Finset.prod_eq_zero (Finset.mem_compl.2 hi) (by simp)
    simp only [hGi, mul_zero, sub_zero, one_pow, sub_self]
    exact tendsto_const_nhds

/-- **The spectral projection of a separated cluster is measurable.** For a measurable family of
    symmetric matrices and a set `J` of indices of the eigenbasis: the set where the cluster is
    separated is measurable, and on it the entries `∑_{i∈J} v_i(a) v_i(b)` are measurable
    (indicator form). -/
theorem specProj_entry_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    (M : Ω → Matrix (Fin N) (Fin N) ℝ) (hM : ∀ a b, Measurable fun ω => M ω a b)
    (hH : ∀ ω, (M ω).IsHermitian) (J : Finset (Fin N)) :
    MeasurableSet {ω | Sep (hH ω) J} ∧ ∀ a b : Fin N,
      Measurable (Set.indicator {ω | Sep (hH ω) J}
        (fun ω => funMat (hH ω) (fun i => if i ∈ J then (1 : ℝ) else 0) a b)) := by
  classical
  have hlam := fun i => eigenvalue_measurable M hM hH i
  have hO : MeasurableSet {ω | Sep (hH ω) J} := by
    unfold Sep
    exact ms_forall fun i => ms_imp (ms_forall fun i' => ms_imp
      ((measurableSet_eq_fun (hlam i) (hlam i')).compl))
  refine ⟨hO, fun a b => ?_⟩
  have hGm : ∀ i, Measurable fun ω => clusterG (hH ω) J i := fun i =>
    Finset.measurable_prod _ fun i' _ => ((hlam i).sub (hlam i')).pow_const 2
  have hGgood : GoodFam M hH (fun ω => clusterG (hH ω) J) :=
    good_prod M hH Jᶜ
      (fun i' ω i => ((hH ω).eigenvalues i - (hH ω).eigenvalues i') ^ 2)
      (fun i' _ => good_pow M hH
        (good_sub M hH (good_eig M hM hH) (good_const M hH _ (hlam i'))) 2)
  have hcm : Measurable fun ω => clusterC (hH ω) J :=
    (measurable_const.add (Finset.measurable_sum _ fun i _ => hGm i)).inv
  have hβ : ∀ n : ℕ, GoodFam M hH
      (fun ω i => 1 - (1 - clusterC (hH ω) J * clusterG (hH ω) J i) ^ n) := fun n =>
    good_sub M hH (good_const M hH (fun _ => 1) measurable_const)
      (good_pow M hH (good_sub M hH (good_const M hH (fun _ => 1) measurable_const)
        (good_mul M hH (good_const M hH _ hcm) hGgood)) n)
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) => Set.indicator {ω | Sep (hH ω) J} (fun ω => funMat (hH ω)
      (fun i => 1 - (1 - clusterC (hH ω) J * clusterG (hH ω) J i) ^ n) a b))
    (fun n => (hβ n a b).indicator hO) (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ {ω | Sep (hH ω) J}
  · simp only [Set.indicator_of_mem hω]
    unfold funMat
    refine tendsto_finset_sum _ fun i _ => ?_
    exact ((cluster_tendsto (M ω) (hH ω) J hω i).mul_const _).mul_const _
  · simp only [Set.indicator_of_notMem hω]
    exact tendsto_const_nhds

end SpectralProjection

section EigspaceSets

open EigenspaceSteps EigenspaceSample EigenspaceFinal

/-- `P w` for an array `P` of matrix entries. -/
def projAct {N : ℕ} (P : Fin N → Fin N → ℝ) (w : Fin N → ℝ) : Fin N → ℝ :=
  fun a => ∑ b, P a b * w b

/-- `‖w - P w‖²`. -/
def resid {N : ℕ} (P : Fin N → Fin N → ℝ) (w : Fin N → ℝ) : ℝ :=
  (w - projAct P w) ⬝ᵥ (w - projAct P w)

theorem resid_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}
    (P : Ω → Fin N → Fin N → ℝ) (w : Ω → Fin N → ℝ)
    (hP : ∀ a b, Measurable fun ω => P ω a b) (hw : ∀ a, Measurable fun ω => w ω a) :
    Measurable fun ω => resid (P ω) (w ω) := by
  unfold resid projAct
  simp only [dotProduct, Pi.sub_apply]
  exact Finset.measurable_sum _ fun a _ =>
    ((hw a).sub (Finset.measurable_sum _ fun b _ => (hP a b).mul (hw b))).mul
      ((hw a).sub (Finset.measurable_sum _ fun b _ => (hP a b).mul (hw b)))

theorem resid_continuous {Y : Type*} [TopologicalSpace Y] {N : ℕ}
    (P : Y → Fin N → Fin N → ℝ) (w : Y → Fin N → ℝ)
    (hP : ∀ a b, Continuous fun y => P y a b) (hw : ∀ a, Continuous fun y => w y a) :
    Continuous fun y => resid (P y) (w y) := by
  unfold resid projAct
  simp only [dotProduct, Pi.sub_apply]
  exact continuous_finset_sum _ fun a _ =>
    ((hw a).sub (continuous_finset_sum _ fun b _ => (hP a b).mul (hw b))).mul
      ((hw a).sub (continuous_finset_sum _ fun b _ => (hP a b).mul (hw b)))

theorem ms_imp_dep {α : Type*} [MeasurableSpace α] {P Q : α → Prop}
    (hP : MeasurableSet {x | P x}) (hQ : MeasurableSet {x | Q x}) :
    MeasurableSet {x | P x → Q x} := by
  refine (hP.compl.union hQ).congr ?_
  ext x
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_setOf_eq]
  exact ⟨fun h hp => h.resolve_left (not_not.2 hp), fun h => by
    by_cases hp : P x
    · exact Or.inr (h hp)
    · exact Or.inl hp⟩

/-- An upper bound for a measurable real function by all members of an ARBITRARY family of
    constants (no countability) is a measurable condition. -/
theorem ms_param_le {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (hf : Measurable f)
    {ι : Sort*} (C : ι → Prop) (t : ι → ℝ) : MeasurableSet {ω | ∀ i, C i → f ω ≤ t i} := by
  have h : IsClosed {x : ℝ | ∀ i, C i → x ≤ t i} :=
    isClosed_setOf_forall fun i => isClosed_setOf_forall fun _ => isClosed_Iic
  exact hf h.measurableSet

/-- Linear independence of a finite measurable family of vectors is a measurable condition. -/
theorem li_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} {F : Type} [Fintype F]
    (w : Ω → F → Fin N → ℝ) (hw : ∀ p a, Measurable fun ω => w ω p a) :
    MeasurableSet {ω | LinearIndependent ℝ (w ω)} := by
  have hC : IsClosed {q : (F → Fin N → ℝ) × (F → ℝ) | ∀ a, ∑ p, q.2 p * q.1 p a = 0} :=
    isClosed_setOf_forall fun a => isClosed_eq
      (continuous_finset_sum _ fun p _ => ((continuous_apply p).comp continuous_snd).mul
        ((continuous_apply a).comp ((continuous_apply p).comp continuous_fst)))
      continuous_const
  have hU : IsOpen {q : (F → Fin N → ℝ) × (F → ℝ) | ∃ p, q.2 p ≠ 0} := by
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun p =>
      isOpen_ne_fun ((continuous_apply p).comp continuous_snd) continuous_const
  have hF : Measurable fun ω => (fun p a => w ω p a : F → Fin N → ℝ) :=
    measurable_pi_lambda _ fun p => measurable_pi_lambda _ fun a => hw p a
  refine (MeasurableSet.compl (hF (proj_measurable hC hU))).congr ?_
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage]
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h g hg p
    by_contra hp
    refine h ⟨g, fun a => ?_, p, hp⟩
    have h1 := congrFun hg a
    rw [Finset.sum_apply] at h1
    simpa [smul_eq_mul] using h1
  · rintro h ⟨g, hg1, p, hp⟩
    refine hp (h g ?_ p)
    funext a
    rw [Finset.sum_apply]
    simpa [smul_eq_mul] using hg1 a

/-- A quadratic bound `‖u - P u‖² ≤ κ ‖u‖²` for all `u` in the span of a finite family and all
    members `κ` of an ARBITRARY family of constants is a measurable condition (closed in the
    data). -/
theorem ms_param_quad {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} {F : Type} [Fintype F]
    (P : Ω → Fin N → Fin N → ℝ) (w : Ω → F → Fin N → ℝ)
    (hP : ∀ a b, Measurable fun ω => P ω a b) (hw : ∀ p a, Measurable fun ω => w ω p a)
    {ι : Sort*} (C : ι → Prop) (κ : ι → ℝ) :
    MeasurableSet {ω | ∀ i, C i → ∀ c : F → ℝ,
      resid (P ω) (comb (w ω) c) ≤ κ i * (comb (w ω) c ⬝ᵥ comb (w ω) c)} := by
  have hcomb : ∀ (c : F → ℝ) (a : Fin N),
      Continuous fun y : (Fin N → Fin N → ℝ) × (F → Fin N → ℝ) => comb y.2 c a := by
    intro c a
    simp only [comb]
    exact continuous_finset_sum _ fun f _ => continuous_const.mul
      ((continuous_apply a).comp ((continuous_apply f).comp continuous_snd))
  have hdot : ∀ c : F → ℝ,
      Continuous fun y : (Fin N → Fin N → ℝ) × (F → Fin N → ℝ) =>
        comb y.2 c ⬝ᵥ comb y.2 c := by
    intro c
    simp only [dotProduct]
    exact continuous_finset_sum _ fun a _ => (hcomb c a).mul (hcomb c a)
  have hC : IsClosed {y : (Fin N → Fin N → ℝ) × (F → Fin N → ℝ) | ∀ i, C i → ∀ c : F → ℝ,
      resid y.1 (comb y.2 c) ≤ κ i * (comb y.2 c ⬝ᵥ comb y.2 c)} :=
    isClosed_setOf_forall fun i => isClosed_setOf_forall fun _ => isClosed_setOf_forall fun c =>
      isClosed_le
        (resid_continuous (fun y : (Fin N → Fin N → ℝ) × (F → Fin N → ℝ) => y.1)
          (fun y => comb y.2 c)
          (fun a b => (continuous_apply b).comp ((continuous_apply a).comp continuous_fst))
          (hcomb c))
        (continuous_const.mul (hdot c))
  have hΦ : Measurable fun ω => ((fun a b => P ω a b, fun p a => w ω p a) :
      (Fin N → Fin N → ℝ) × (F → Fin N → ℝ)) :=
    (measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hP a b).prodMk
      (measurable_pi_lambda _ fun p => measurable_pi_lambda _ fun a => hw p a)
  exact hΦ hC.measurableSet

/-- Membership of a column of `P` in the span of the vectors `P w_p` is a measurable
    condition. -/
theorem ms_exists_coeff {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} {F : Type} [Fintype F]
    (P : Ω → Fin N → Fin N → ℝ) (w : Ω → F → Fin N → ℝ)
    (hP : ∀ a b, Measurable fun ω => P ω a b) (hw : ∀ p a, Measurable fun ω => w ω p a)
    (a : Fin N) :
    MeasurableSet {ω | ∃ c : F → ℝ, ∀ a' : Fin N,
      P ω a' a = ∑ p, c p * projAct (P ω) (w ω p) a'} := by
  have hC : IsClosed {q : ((Fin N → Fin N → ℝ) × (F → Fin N → ℝ)) × (F → ℝ) |
      ∀ a' : Fin N, q.1.1 a' a = ∑ p, q.2 p * projAct q.1.1 (q.1.2 p) a'} := by
    refine isClosed_setOf_forall fun a' => isClosed_eq
      ((continuous_apply a).comp ((continuous_apply a').comp
        (continuous_fst.comp continuous_fst))) ?_
    simp only [projAct]
    have c1 : ∀ b : Fin N, Continuous
        fun q : ((Fin N → Fin N → ℝ) × (F → Fin N → ℝ)) × (F → ℝ) => q.1.1 a' b :=
      fun b => by fun_prop
    have c2 : ∀ (p : F) (b : Fin N), Continuous
        fun q : ((Fin N → Fin N → ℝ) × (F → Fin N → ℝ)) × (F → ℝ) => q.1.2 p b :=
      fun p b => by fun_prop
    have c3 : ∀ p : F, Continuous
        fun q : ((Fin N → Fin N → ℝ) × (F → Fin N → ℝ)) × (F → ℝ) => q.2 p :=
      fun p => by fun_prop
    exact continuous_finset_sum _ fun p _ =>
      (c3 p).mul (continuous_finset_sum _ fun b _ => (c1 b).mul (c2 p b))
  have hΦ : Measurable fun ω => ((fun a b => P ω a b, fun p a => w ω p a) :
      (Fin N → Fin N → ℝ) × (F → Fin N → ℝ)) :=
    (measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hP a b).prodMk
      (measurable_pi_lambda _ fun p => measurable_pi_lambda _ fun a => hw p a)
  refine (hΦ (proj_measurable hC isOpen_univ)).congr ?_
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, and_true]

theorem sum_ind_mul {N : ℕ} (J : Finset (Fin N)) (f : Fin N → ℝ) :
    ∑ i, (if i ∈ J then (1 : ℝ) else 0) * f i = ∑ i : J, f i.1 := by
  have h : ∀ i, (if i ∈ J then (1 : ℝ) else 0) * f i = if i ∈ J then f i else 0 := by
    intro i
    by_cases hi : i ∈ J
    · simp only [if_pos hi, one_mul]
    · simp only [if_neg hi, zero_mul]
  simp only [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_coe_sort]

theorem specProj_evec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (J : Finset (Fin N)) {i : Fin N} (hi : i ∈ J) : specProj hA J (evec hA i) = evec hA i := by
  funext a
  unfold specProj
  simp only [evec_orthonormal, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos hi]

/-- The span clause of `EigspaceConcl` through the entries of `Π_J`: the projected vectors span
    the span of the eigenvectors of the cluster iff every column of `Π_J` is a combination of
    them. -/
theorem specProj_span_iff {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian)
    (J : Finset (Fin N)) {F : Type} [Fintype F] (w : F → Fin N → ℝ) :
    Submodule.span ℝ (Set.range fun p => specProj hA J (w p))
        = Submodule.span ℝ (Set.range fun i : J => evec hA i.1)
      ↔ ∀ a : Fin N, ∃ c : F → ℝ, ∀ a' : Fin N,
          funMat hA (fun i => if i ∈ J then (1 : ℝ) else 0) a' a
            = ∑ p, c p * specProj hA J (w p) a' := by
  classical
  have hcol : ∀ a : Fin N,
      (fun a' => funMat hA (fun i => if i ∈ J then (1 : ℝ) else 0) a' a)
        = ∑ i : J, evec hA i.1 a • evec hA i.1 := by
    intro a
    funext a'
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold funMat
    rw [← sum_ind_mul J (fun i => evec hA i a * evec hA i a')]
    exact Finset.sum_congr rfl fun i _ => by ring
  have f1 : ∀ w' : Fin N → ℝ, specProj hA J w'
      ∈ Submodule.span ℝ (Set.range fun i : J => evec hA i.1) := by
    intro w'
    have e : specProj hA J w' = ∑ i : J, (evec hA i.1 ⬝ᵥ w') • evec hA i.1 := by
      funext a
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      unfold specProj
      rw [Finset.sum_coe_sort J (fun i => (evec hA i ⬝ᵥ w') * evec hA i a)]
    rw [e]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have f2 : ∀ a : Fin N, (fun a' => funMat hA (fun i => if i ∈ J then (1 : ℝ) else 0) a' a)
      ∈ Submodule.span ℝ (Set.range fun i : J => evec hA i.1) := by
    intro a
    rw [hcol a]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have f3 : ∀ i ∈ J, evec hA i = ∑ a, evec hA i a
      • (fun a' => funMat hA (fun i => if i ∈ J then (1 : ℝ) else 0) a' a) := by
    intro i hi
    funext a'
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have h1 := congrFun (specProj_evec A hA J hi) a'
    rw [specProj_eq_funMat] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun b _ => by ring
  constructor
  · intro h a
    have h1 := f2 a
    rw [← h, Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    refine ⟨c, fun a' => ?_⟩
    have h2 := congrFun hc a'
    rw [Finset.sum_apply] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact h2.symm
  · intro h
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨p, rfl⟩
      exact f1 (w p)
    · rintro _ ⟨i, rfl⟩
      show evec hA i.1 ∈ Submodule.span ℝ (Set.range fun p => specProj hA J (w p))
      rw [f3 i.1 i.2]
      refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
      obtain ⟨c, hc⟩ := h a
      have e : (fun a' => funMat hA (fun i => if i ∈ J then (1 : ℝ) else 0) a' a)
          = ∑ p, c p • specProj hA J (w p) := by
        funext a'
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hc a'
      rw [e]
      exact Submodule.sum_mem _ fun p _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The matrix of the eigenspace statements is symmetric. -/
theorem sGraph_herm {Ω : Type*} (d N : ℕ) (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    (sGraph d σ N (fun j => X j ω)).IsHermitian :=
  symGraph_sample_isHermitian d N X ω

/-- The pairs (shell parameter, `ϑ`) admitted by a hypothesis `Hyp` on `(r, r⁻, r⁺, gap)`. -/
def ParSet (d : ℕ) (σ δp : ℝ)
    (Hyp : ℝ → ℝ → ℝ → ℝ → Finset (Fin d → ℤ) → Finset (Fin d → ℤ) → Prop)
    (Hlt Hle : Finset (Fin d → ℤ)) : Set (ℝ × ℝ) :=
  {q | ∃ rm rp gap : ℝ, Hyp q.1 rm rp gap Hlt Hle ∧ q.2 = eigTheta d σ δp q.1 gap}

/-- **Normal form of the eigenspace statement at a point tuple.** For fixed `Hlt`, `Hle` the
    statement "`EigspaceConcl` for all admitted `(r, r⁻, r⁺, gap)`" is equivalent to: the cluster
    is separated (if some parameter is admitted), and then four statements in which the vectors
    of the eigenbasis enter only through an array `P` that agrees with the entries of the
    spectral projection on the separated set. -/
theorem concl_iff (d N : ℕ) (σ : ℝ) (x : ℕ → FlatTorus d) (hS : (sGraph d σ N x).IsHermitian)
    (H0 : Finset (Fin d → ℤ)) (γ δp : ℝ)
    (Hyp : ℝ → ℝ → ℝ → ℝ → Finset (Fin d → ℤ) → Finset (Fin d → ℤ) → Prop)
    (Hlt Hle : Finset (Fin d → ℤ)) (P : Fin N → Fin N → ℝ)
    (hP : Sep hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) → ∀ a b, P a b
      = funMat hS (fun i => if i ∈ shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)
          then (1 : ℝ) else 0) a b) :
    (∀ r rm rp gap : ℝ, Hyp r rm rp gap Hlt Hle →
      EigspaceConcl d N σ x hS H0 γ r (eigTheta d σ δp r gap) Hlt Hle)
    ↔ ((ParSet d σ δp Hyp Hlt Hle).Nonempty →
          Sep hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)))
      ∧ (Sep hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) →
        (∀ (n : Fin d → ℤ) (b : Bool) (q : ℝ × ℝ),
          (q ∈ ParSet d σ δp Hyp Hlt Hle ∧ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = q.1) →
          resid P (sMode d N x (some (n, b))) ≤ q.2 ^ 2)
        ∧ ((∃ q ∈ ParSet d σ δp Hyp Hlt Hle,
              (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 = q.1 → n ∈ H0)
              ∧ ((2 * (Hle.card - Hlt.card) : ℕ) : ℝ) * γ ≤ 1 / 2) →
            LinearIndependent ℝ (shellModes d N x Hlt Hle))
        ∧ (∀ q : ℝ × ℝ, (q ∈ ParSet d σ δp Hyp Hlt Hle
              ∧ (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 = q.1 → n ∈ H0)
              ∧ ((2 * (Hle.card - Hlt.card) : ℕ) : ℝ) * γ ≤ 1 / 2) →
            ∀ c : ↥(Hle \ Hlt) × Bool → ℝ,
              resid P (comb (shellModes d N x Hlt Hle) c)
                ≤ 2 * (((2 * (Hle.card - Hlt.card) : ℕ) : ℝ) * q.2 ^ 2)
                  * (comb (shellModes d N x Hlt Hle) c ⬝ᵥ comb (shellModes d N x Hlt Hle) c))
        ∧ ((∃ q ∈ ParSet d σ δp Hyp Hlt Hle,
              (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 = q.1 → n ∈ H0)
              ∧ ((2 * (Hle.card - Hlt.card) : ℕ) : ℝ) * γ ≤ 1 / 2
              ∧ 2 * (((2 * (Hle.card - Hlt.card) : ℕ) : ℝ) * q.2 ^ 2) < 1) →
            (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)).card = 2 * (Hle.card - Hlt.card)
            ∧ ∀ a : Fin N, ∃ c : ↥(Hle \ Hlt) × Bool → ℝ, ∀ a' : Fin N,
                P a' a = ∑ p, c p * projAct P (shellModes d N x Hlt Hle p) a')) := by
  have hrw : Sep hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) → ∀ w : Fin N → ℝ,
      specProj hS (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) w = projAct P w := by
    intro hs w
    funext a
    rw [specProj_eq_funMat]
    unfold projAct
    exact Finset.sum_congr rfl fun b _ => by rw [hP hs a b]
  constructor
  · intro H
    refine ⟨fun ⟨q, rm, rp, gap, hy, _⟩ => (H q.1 rm rp gap hy).1, fun hs => ⟨?_, ?_, ?_, ?_⟩⟩
    · rintro n b q ⟨⟨rm, rp, gap, hy, hq⟩, hl, hsq⟩
      have h := (H q.1 rm rp gap hy).2.1 n hl hsq b
      rw [hrw hs, ← hq] at h
      exact h
    · rintro ⟨q, ⟨rm, rp, gap, hy, hq⟩, hh1, hh2⟩
      exact ((H q.1 rm rp gap hy).2.2 hh1 hh2).1
    · rintro q ⟨⟨rm, rp, gap, hy, hq⟩, hh1, hh2⟩ c
      have h := ((H q.1 rm rp gap hy).2.2 hh1 hh2).2.1 c
      rw [hrw hs, ← hq] at h
      exact h
    · rintro ⟨q, ⟨rm, rp, gap, hy, hq⟩, hh1, hh2, hh3⟩
      have h := ((H q.1 rm rp gap hy).2.2 hh1 hh2).2.2 (by rw [← hq]; exact hh3)
      refine ⟨h.1, fun a => ?_⟩
      obtain ⟨c, hc⟩ := (specProj_span_iff (sGraph d σ N x) hS
        (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) (shellModes d N x Hlt Hle)).1 h.2 a
      refine ⟨c, fun a' => ?_⟩
      rw [hP hs a' a, hc a']
      simp only [hrw hs]
  · rintro ⟨HA, HB⟩ r rm rp gap hy
    have hq : ((r, eigTheta d σ δp r gap) : ℝ × ℝ) ∈ ParSet d σ δp Hyp Hlt Hle :=
      ⟨rm, rp, gap, hy, rfl⟩
    have hs := HA ⟨_, hq⟩
    obtain ⟨R1, R2, R3, R4⟩ := HB hs
    refine ⟨hs, fun n hl hsq b => ?_, fun hh1 hh2 =>
      ⟨R2 ⟨_, hq, hh1, hh2⟩, fun c => ?_, fun hh3 => ?_⟩⟩
    · have h := R1 n b _ ⟨hq, hl, hsq⟩
      rw [hrw hs]
      exact h
    · have h := R3 _ ⟨hq, hh1, hh2⟩ c
      rw [hrw hs]
      exact h
    · obtain ⟨hc, hsp⟩ := R4 ⟨_, hq, hh1, hh2, hh3⟩
      refine ⟨hc, (specProj_span_iff (sGraph d σ N x) hS
        (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) (shellModes d N x Hlt Hle)).2 fun a => ?_⟩
      obtain ⟨c, hcc⟩ := hsp a
      refine ⟨c, fun a' => ?_⟩
      rw [← hP hs a' a, hcc a']
      simp only [hrw hs]

/-- The entries of the spectral projection of the cluster `J` of the sample graph, set to zero
    where the cluster is not separated. -/
noncomputable def sPm {Ω : Type*} (d N : ℕ) (σ : ℝ) (X : ℕ → Ω → FlatTorus d)
    (J : Finset (Fin N)) (ω : Ω) (a b : Fin N) : ℝ :=
  Set.indicator {ω | Sep (sGraph_herm d N σ X ω) J}
    (fun ω => funMat (sGraph_herm d N σ X ω) (fun i => if i ∈ J then (1 : ℝ) else 0) a b) ω

/-- The eigenspace statement for fixed `Hlt`, `Hle` and all admitted `(r, r⁻, r⁺, gap)` is a
    measurable condition on the sample. -/
theorem eigspace_shell_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ} (hσ : 0 < σ)
    (d N : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (H0 : Finset (Fin d → ℤ)) (γ δp : ℝ)
    (Hyp : ℝ → ℝ → ℝ → ℝ → Finset (Fin d → ℤ) → Finset (Fin d → ℤ) → Prop)
    (Hlt Hle : Finset (Fin d → ℤ)) :
    MeasurableSet {ω | ∀ r rm rp gap : ℝ, Hyp r rm rp gap Hlt Hle →
      EigspaceConcl d N σ (fun j => X j ω) (sGraph_herm d N σ X ω) H0 γ r
        (eigTheta d σ δp r gap) Hlt Hle} := by
  classical
  have hM : ∀ a b : Fin N, Measurable fun ω => sGraph d σ N (fun j => X j ω) a b := fun a b =>
    symGraph_fin_entry_measurable hσ d X hX N a b
  have hsp := specProj_entry_measurable (fun ω => sGraph d σ N (fun j => X j ω)) hM
    (fun ω => sGraph_herm d N σ X ω) (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card))
  have hPm : ∀ a b : Fin N, Measurable fun ω =>
      sPm d N σ X (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) ω a b := fun a b => hsp.2 a b
  have hmode : ∀ (f : Option ((Fin d → ℤ) × Bool)) (a : Fin N),
      Measurable fun ω => sMode d N (fun j => X j ω) f a := fun f a =>
    ((torusMode_measurable d f).comp (hX a)).div_const _
  have hshell : ∀ (p : ↥(Hle \ Hlt) × Bool) (a : Fin N),
      Measurable fun ω => shellModes d N (fun j => X j ω) Hlt Hle p a := fun p a =>
    hmode (some (p.1.1, p.2)) a
  have key : ∀ ω, _ ↔ _ := fun ω => concl_iff d N σ (fun j => X j ω) (sGraph_herm d N σ X ω)
    H0 γ δp Hyp Hlt Hle (sPm d N σ X (shellSet N (1 + 2 * Hlt.card) (2 * Hle.card)) ω)
    (fun hs a b => Set.indicator_of_mem hs _)
  refine (congrArg MeasurableSet (congrArg setOf (funext fun ω => propext (key ω)))).mpr ?_
  refine ms_and (ms_imp hsp.1) (ms_imp_dep hsp.1 (ms_and ?_ (ms_and ?_ (ms_and ?_ ?_))))
  · exact ms_forall fun n => ms_forall fun b => ms_param_le
      (resid_measurable _ _ hPm (hmode (some (n, b)))) _ _
  · exact ms_imp (li_measurable (fun ω => shellModes d N (fun j => X j ω) Hlt Hle) hshell)
  · exact ms_param_quad _ (fun ω => shellModes d N (fun j => X j ω) Hlt Hle) hPm hshell _ _
  · exact ms_imp (ms_and (MeasurableSet.const _) (ms_forall fun a =>
      ms_exists_coeff _ (fun ω => shellModes d N (fun j => X j ω) Hlt Hle) hPm hshell a))

/-- The eigenspace statement for ALL shells admitted by a hypothesis `Hyp` is a measurable
    condition on the sample. -/
theorem eigspace_concl_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ} (hσ : 0 < σ)
    (d N : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (H0 : Finset (Fin d → ℤ)) (γ δp : ℝ)
    (Hyp : ℝ → ℝ → ℝ → ℝ → Finset (Fin d → ℤ) → Finset (Fin d → ℤ) → Prop) :
    MeasurableSet {ω | ∀ (hS : (sGraph d σ N (fun j => X j ω)).IsHermitian) (r rm rp gap : ℝ)
        (Hlt Hle : Finset (Fin d → ℤ)), Hyp r rm rp gap Hlt Hle →
      EigspaceConcl d N σ (fun j => X j ω) hS H0 γ r (eigTheta d σ δp r gap) Hlt Hle} := by
  refine MeasurableSet.congr (ms_forall fun Hlt => ms_forall fun Hle =>
    eigspace_shell_measurable hσ d N X hX H0 γ δp Hyp Hlt Hle) ?_
  ext ω
  exact ⟨fun h hS r rm rp gap Hlt Hle hy => h Hlt Hle r rm rp gap hy,
    fun h Hlt Hle r rm rp gap hy => h (sGraph_herm d N σ X ω) r rm rp gap Hlt Hle hy⟩

/-- The exceptional set of `EigenspaceFinal.eigspace_final_sample`, verbatim, is measurable. -/
theorem eigspace_final_sample_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d N K : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (H0 : Finset (Fin d → ℤ)) (γ δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ (hS : (sGraph d σ N (fun j => X j ω)).IsHermitian) (r rm rp gap : ℝ),
        0 ≤ rm → rm < r → r < rp → 0 < gap → gap ≤ r - rm → gap ≤ rp - r →
        4 * Real.pi ^ 2 * σ * r ≤ 1 → 1 ≤ (K : ℝ) * (2 * Real.pi ^ 2 * σ * r) →
        (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
            ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) →
        ∀ Hlt Hle : Finset (Fin d → ℤ),
        (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
        (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
        eigTheta d σ δp r gap ≤ 1 →
        EigspaceConcl d N σ (fun j => X j ω) hS H0 γ r (eigTheta d σ δp r gap) Hlt Hle} := by
  refine MeasurableSet.compl ?_
  refine MeasurableSet.congr (eigspace_concl_measurable hσ d N X hX H0 γ δp
    (fun r rm rp gap Hlt Hle => 0 ≤ rm ∧ rm < r ∧ r < rp ∧ 0 < gap ∧ gap ≤ r - rm ∧ gap ≤ rp - r
      ∧ 4 * Real.pi ^ 2 * σ * r ≤ 1 ∧ 1 ≤ (K : ℝ) * (2 * Real.pi ^ 2 * σ * r)
      ∧ (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
            ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ∧ (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r)
      ∧ (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r)
      ∧ eigTheta d σ δp r gap ≤ 1)) ?_
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h hS r rm rp gap a1 a2 a3 a4 a5 a6 a7 a8 a9 Hlt Hle b1 b2 b3
    exact h hS r rm rp gap Hlt Hle ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩
  · rintro h hS r rm rp gap Hlt Hle ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩
    exact h hS r rm rp gap a1 a2 a3 a4 a5 a6 a7 a8 a9 Hlt Hle b1 b2 b3

/-- The exceptional set of `EigenspaceFinal.eigspace_final_sample'`, verbatim, is measurable. -/
theorem eigspace_final_sample'_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d N : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (H0 : Finset (Fin d → ℤ)) (γ δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ (hS : (sGraph d σ N (fun j => X j ω)).IsHermitian) (r rm rp gap : ℝ),
        0 ≤ rm → rm < r → r < rp → 0 < gap → gap ≤ r - rm → gap ≤ rp - r →
        4 * Real.pi ^ 2 * σ * r ≤ 1 → 1 ≤ r →
        (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
            ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) →
        ∀ Hlt Hle : Finset (Fin d → ℤ),
        (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
        (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
        eigTheta d σ δp r gap ≤ 1 →
        EigspaceConcl d N σ (fun j => X j ω) hS H0 γ r (eigTheta d σ δp r gap) Hlt Hle} := by
  refine MeasurableSet.compl ?_
  refine MeasurableSet.congr (eigspace_concl_measurable hσ d N X hX H0 γ δp
    (fun r rm rp gap Hlt Hle => 0 ≤ rm ∧ rm < r ∧ r < rp ∧ 0 < gap ∧ gap ≤ r - rm ∧ gap ≤ rp - r
      ∧ 4 * Real.pi ^ 2 * σ * r ≤ 1 ∧ 1 ≤ r
      ∧ (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
            ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ∧ (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r)
      ∧ (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r)
      ∧ eigTheta d σ δp r gap ≤ 1)) ?_
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h hS r rm rp gap a1 a2 a3 a4 a5 a6 a7 a8 a9 Hlt Hle b1 b2 b3
    exact h hS r rm rp gap Hlt Hle ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩
  · rintro h hS r rm rp gap Hlt Hle ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩
    exact h hS r rm rp gap a1 a2 a3 a4 a5 a6 a7 a8 a9 Hlt Hle b1 b2 b3

/-- The exceptional set of `EigenspaceFinal.eigspace_final_sample''`, verbatim, is measurable. -/
theorem eigspace_final_sample''_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d N : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (δp : ℝ) (m a : ℕ) (R : ℝ) :
    MeasurableSet {ω | ¬ ∀ (hS : (sGraph d σ N (fun j => X j ω)).IsHermitian) (r rm rp gap : ℝ),
        0 ≤ rm → rm < r → r < rp → 0 < gap → gap ≤ r - rm → gap ≤ rp - r →
        4 * Real.pi ^ 2 * σ * r ≤ 1 → 1 ≤ r →
        (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
            ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2) →
        ∀ Hlt Hle : Finset (Fin d → ℤ),
        (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
        (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
        eigTheta d σ δp r gap ≤ 1 →
        EigspaceConcl d N σ (fun j => X j ω) hS (halfFreq d m R)
          (Real.sqrt (8 * (3 + 2 * (a : ℝ))) * δp) r (eigTheta d σ δp r gap) Hlt Hle} := by
  refine MeasurableSet.compl ?_
  refine MeasurableSet.congr (eigspace_concl_measurable hσ d N X hX (halfFreq d m R)
    (Real.sqrt (8 * (3 + 2 * (a : ℝ))) * δp) δp
    (fun r rm rp gap Hlt Hle => 0 ≤ rm ∧ rm < r ∧ r < rp ∧ 0 < gap ∧ gap ≤ r - rm ∧ gap ≤ rp - r
      ∧ 4 * Real.pi ^ 2 * σ * r ≤ 1 ∧ 1 ≤ r
      ∧ (∀ n, lexPos d n → ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ rm ∨ ∑ i, ((n i : ℤ) : ℝ) ^ 2 = r
            ∨ rp ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
      ∧ (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r)
      ∧ (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r)
      ∧ eigTheta d σ δp r gap ≤ 1)) ?_
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h hS r rm rp gap a1 a2 a3 a4 a5 a6 a7 a8 a9 Hlt Hle b1 b2 b3
    exact h hS r rm rp gap Hlt Hle ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩
  · rintro h hS r rm rp gap Hlt Hle ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, b1, b2, b3⟩
    exact h hS r rm rp gap a1 a2 a3 a4 a5 a6 a7 a8 a9 Hlt Hle b1 b2 b3

end EigspaceSets

end Reals3Sets

namespace WeightedConsistency

/-!
## The consistency lemma with a pointwise weight (`lem:consistency`(i)--(iii))

What is proved here (all for the flat torus `FlatTorus d`, independent uniform points, the heat
kernel `heatTorus d (2π²σ)` of variance `σ = ξ²` as walk kernel, self-loops included):

* `heatDefBound_weighted` (deterministic): the pointwise defect bound `heatDefBound` of the second
  file is at most `(explicit number)/√m · p_{12mσ}(u)`, for EVERY `m ≥ 1` (no restriction
  `mσ ≤ 1`), with constants that do not depend on the time `mσ`.
* `weighted_consistency_g3`, `weighted_consistency_paper` (sample statements): except on an event of
  probability at most `2/N³`, simultaneously
  (i)   `|ρ_j - 1| ≤ c_δ δ'` for all `j`,
  (ii)  `|h_m^{(i)}(b)| ≤ C δ' m^{-1/2} p_{12mσ}(x_b - x_i)` for all `b, i < N`, `1 ≤ m ≤ K`,
  (iii) `(1/N) ∑_b p_{12mσ}(x_b - x_i) ≤ 1 + c_δ δ'` for all `i`, `1 ≤ m ≤ K`.

What is NOT proved: the weight `p_{6m}` of the paper.  The weight here is `p_{12m}` (twice the
time).  Reason: the variance bound of the second file (`torus_variance`) carries the weight
`p_{6s}` where the paper has `p^{(2s)}(0) p^{(3s)}(z)`; taking the square root with (P5)
(`heatTorus_sqrt_le`) doubles the time once more.  Since `p_{6m} ≤ 2^{d/2} p_{12m}`, the estimate
here is implied by the one of the paper and not conversely.  For the two uses of the lemma in the
paper (supremum over `b`, mean over `b`) the weight `p_{12m}` serves equally well.
(P3) and the Gaussian Poincaré inequality are not used (explicit Gaussian integrals instead).
-/

/-- The heat kernel of the circle is at least `1/2` at parameters `c ≥ 8`. -/
theorem pC_ge_half {c : ℝ} (hc : 8 ≤ c) (u : UnitAddCircle) : 1 / 2 ≤ pC c u := by
  have hc0 : 0 < c := by linarith
  have hpi := Real.pi_pos
  have hT : ∀ n : Fin 1 → ℤ, n ∉ ({0} : Finset (Fin 1 → ℤ)) →
      (1 : ℝ) ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := by
    intro n hn
    have hn0 : n 0 ≠ 0 := by
      intro h0
      apply hn
      rw [Finset.mem_singleton]
      funext i
      rw [Fin.eq_zero i]
      simpa using h0
    have h1 := Int.one_le_abs hn0
    have h2 : (1 : ℤ) ≤ (n 0) ^ 2 := by
      nlinarith [sq_abs (n 0), mul_self_nonneg (|n 0| - 1)]
    rw [Fin.sum_univ_one]
    exact_mod_cast h2
  have h := heatTorus_truncation hc0 1 ({0} : Finset (Fin 1 → ℤ)) hT (fun _ => u)
  rw [Finset.sum_singleton, torusChar_zero] at h
  simp only [Pi.zero_apply, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, mul_zero, Real.exp_zero, Complex.one_re, mul_one,
    pow_one] at h
  have he : Real.exp (-c / 2) ≤ 1 / 5 := by
    have h1 := Real.add_one_le_exp (c / 2)
    have h2 : Real.exp (-c / 2) = (Real.exp (c / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h2, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have hs : Real.sqrt (2 * Real.pi / c) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    rw [div_le_one hc0]
    linarith [Real.pi_le_four]
  have hb : Real.exp (-c / 2) * (1 + Real.sqrt (2 * Real.pi / c)) ≤ 1 / 2 := by
    have h0 := Real.sqrt_nonneg (2 * Real.pi / c)
    have h1 : Real.exp (-c / 2) * (1 + Real.sqrt (2 * Real.pi / c)) ≤ 1 / 5 * 2 :=
      mul_le_mul he (by linarith) (by linarith) (by norm_num)
    linarith
  have h3 := (abs_le.mp (h.trans hb)).1
  unfold pC
  linarith

/-- The heat kernel of the torus is at least `2^{-d}` at parameters `c ≥ 8`. -/
theorem heatTorus_ge_half_pow {c : ℝ} (hc : 8 ≤ c) (d : ℕ) (x : FlatTorus d) :
    (1 / 2 : ℝ) ^ d ≤ heatTorus d c x := by
  rw [heatTorus_eq_prod_pC (by linarith) d x]
  calc (1 / 2 : ℝ) ^ d = ∏ _i : Fin d, (1 / 2 : ℝ) := by simp
    _ ≤ ∏ i, pC c (x i) :=
        Finset.prod_le_prod (fun _ _ => by norm_num) (fun i _ => pC_ge_half hc (x i))

/-- (P1) towards the time `12 s`: `p_τ ≤ (√12)^d p_{12s}` for `s ≤ τ ≤ 12 s`. -/
theorem heatTorus_to_twelve {s τ : ℝ} (hs : 0 < s) (h1 : s ≤ τ) (h2 : τ ≤ 12 * s) (d : ℕ)
    (u : FlatTorus d) :
    heatTorus d (2 * Real.pi ^ 2 * τ) u
      ≤ Real.sqrt 12 ^ d * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u := by
  have hpi := Real.pi_pos
  have hτ : 0 < τ := lt_of_lt_of_le hs h1
  have hca : 0 < 2 * Real.pi ^ 2 * τ := by positivity
  have hct : 0 < 2 * Real.pi ^ 2 * (12 * s) := by positivity
  have hle : 2 * Real.pi ^ 2 * τ ≤ 2 * Real.pi ^ 2 * (12 * s) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h := heatTorus_P1 hca hle d u
  have hp := heatTorus_nonneg hct d u
  have hr : 2 * Real.pi ^ 2 * (12 * s) / (2 * Real.pi ^ 2 * τ) ≤ 12 := by
    rw [div_le_iff₀ hca]
    have : 2 * Real.pi ^ 2 * (12 * s) = 12 * (2 * Real.pi ^ 2 * s) := by ring
    rw [this]
    have h3 : 2 * Real.pi ^ 2 * s ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  have hq : (2 * Real.pi ^ 2 * (12 * s) / (2 * Real.pi ^ 2 * τ)) ^ (1 / 2 : ℝ) ≤ Real.sqrt 12 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (by positivity) hr (by norm_num)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact pow_le_pow_left₀ (by positivity) hq d

/-- The first-moment term of the defect bound, times `s ≤ 1`: with (P5),
    `√(heatCV) √(p_{6s}(u)) ≤ rateRA √(σ/s) p_{12s}(u)`. -/
theorem wc_Z_small {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : s ≤ 1) (d : ℕ) (u : FlatTorus d) :
    Real.sqrt (heatCV d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u)
      ≤ rateRA d * Real.sqrt (σ / s) * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u := by
  have hpi := Real.pi_pos
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  have hc6 : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * s) := by positivity
  have hc12 : (0 : ℝ) < 2 * Real.pi ^ 2 * (12 * s) := by positivity
  have hCV := heatCV_nonneg hσ hs d
  have hQ := heatQ_nonneg hc6 d
  have hp12 := heatTorus_nonneg hc12 d u
  have h5 := heatTorus_sqrt_le hc6 d u
  rw [show 2 * (2 * Real.pi ^ 2 * (6 * s)) = 2 * Real.pi ^ 2 * (12 * s) by ring] at h5
  have hcq := heatCV_heatQ hσ hσs hs1 d
  have hc := cvConst_nonneg
  have hR : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
      * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  have e1 : Real.sqrt (heatCV d σ s) * heatQ d (2 * Real.pi ^ 2 * (6 * s))
      = Real.sqrt (heatCV d σ s * heatQ d (2 * Real.pi ^ 2 * (6 * s)) ^ 2) := by
    rw [Real.sqrt_mul hCV, Real.sqrt_sq hQ]
  have e2 : Real.sqrt (heatCV d σ s) * heatQ d (2 * Real.pi ^ 2 * (6 * s))
      ≤ rateRA d * Real.sqrt (σ / s) := by
    rw [e1]; unfold rateRA
    rw [← Real.sqrt_mul hR]
    exact Real.sqrt_le_sqrt hcq
  calc Real.sqrt (heatCV d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u)
      ≤ Real.sqrt (heatCV d σ s)
          * (heatQ d (2 * Real.pi ^ 2 * (6 * s)) * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u) :=
        mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
    _ = Real.sqrt (heatCV d σ s) * heatQ d (2 * Real.pi ^ 2 * (6 * s))
          * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u := by ring
    _ ≤ rateRA d * Real.sqrt (σ / s) * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u :=
        mul_le_mul_of_nonneg_right e2 hp12

/-- The first-moment term of the defect bound, times `s ≥ 1` (where the kernel is of order one):
    `√(heatCV) √(p_{6s}(u)) ≤ rateRA √(σ/s) 4^d p_{12s}(u)`. -/
theorem wc_Z_large {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : 1 ≤ s) (d : ℕ) (u : FlatTorus d) :
    Real.sqrt (heatCV d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u)
      ≤ rateRA d * Real.sqrt (σ / s) * (4 ^ d * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u) := by
  have hpi := Real.pi_pos
  have hpi2 := Real.two_le_pi
  have hpis : 1 ≤ Real.pi * s := by nlinarith
  have hpps : Real.pi ≤ Real.pi * (Real.pi * s) := le_mul_of_one_le_right hpi.le hpis
  have hs : 0 < s := by linarith
  have hc6 : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * s) := by positivity
  have hc12 : (0 : ℝ) < 2 * Real.pi ^ 2 * (12 * s) := by positivity
  have hc := cvConst_nonneg
  have hR : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
      * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  have hp12 := heatTorus_nonneg hc12 d u
  have e2 : Real.sqrt (heatCV d σ s) ≤ rateRA d * Real.sqrt (σ / s) := by
    unfold rateRA
    rw [← Real.sqrt_mul hR]
    exact Real.sqrt_le_sqrt (heatCV_le_large hσ hσs hs1 d)
  have h8 : (8 : ℝ) ≤ 2 * Real.pi ^ 2 * (12 * s) := by
    have : 2 * Real.pi ^ 2 * (12 * s) = 24 * (Real.pi * (Real.pi * s)) := by ring
    rw [this]; linarith
  have hlow := heatTorus_ge_half_pow h8 d u
  have hup : heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u ≤ 2 ^ d := by
    refine (heatTorus_le hc6 d u).trans (pow_le_pow_left₀ (by positivity) ?_ d)
    have : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * (6 * s))) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      apply Real.sqrt_le_sqrt
      rw [div_le_one hc6]
      have : 2 * Real.pi ^ 2 * (6 * s) = 12 * (Real.pi * (Real.pi * s)) := by ring
      rw [this]; linarith
    linarith
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hsq : Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u) ≤ 2 ^ d := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h4 : (2 : ℝ) ^ d = 4 ^ d * (1 / 2) ^ d := by
    rw [← mul_pow]; norm_num
  have hq : Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u)
      ≤ 4 ^ d * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u := by
    refine hsq.trans ?_
    rw [h4]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hr0 : 0 ≤ rateRA d := by unfold rateRA; exact Real.sqrt_nonneg _
  exact mul_le_mul e2 hq (Real.sqrt_nonneg _) (mul_nonneg hr0 (Real.sqrt_nonneg _))

/-- The first-moment term at every time `s ≥ σ`. -/
theorem wc_Z {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (d : ℕ) (u : FlatTorus d) :
    Real.sqrt (heatCV d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u)
      ≤ rateRA d * Real.sqrt (σ / s) * (4 ^ d * heatTorus d (2 * Real.pi ^ 2 * (12 * s)) u) := by
  have hpi := Real.pi_pos
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  rcases le_total s 1 with h | h
  · refine (wc_Z_small hσ hσs h d u).trans ?_
    have hp12 := heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (12 * s)) d u
    have h4 : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ rateRA d * Real.sqrt (σ / s) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hr
    nlinarith
  · exact wc_Z_large hσ hσs h d u

/-- Algebra of the pointwise bound, with free variables. -/
theorem wc_assemble {N L δ S kbM G p θ rr sm : ℝ} (hN : 0 < N) (hsm : 0 < sm) (hδ : 0 ≤ δ)
    (hGp : 0 ≤ G * p) (hθ : (2 * L + 2) * kbM * sm ≤ θ * N) :
    3 / N * ((1 + 2 * δ) * ((2 * L + 2) * (kbM * (G * p)) + 2 * S * (rr / sm * p))
        + 2 * δ * N * (rr / sm * p))
      ≤ 3 * ((1 + 2 * δ) * (G * θ + 2 * (S / N) * rr) + 2 * δ * rr) / sm * p := by
  have key : (2 * L + 2) * kbM / N ≤ θ / sm := by
    rw [div_le_div_iff₀ hN hsm]; linarith
  have e1 : 3 / N * ((1 + 2 * δ) * ((2 * L + 2) * (kbM * (G * p)) + 2 * S * (rr / sm * p))
        + 2 * δ * N * (rr / sm * p))
      = 3 * ((1 + 2 * δ) * ((2 * L + 2) * kbM / N * (G * p) + 2 * (S / N) * rr * (p / sm))
          + 2 * δ * rr * (p / sm)) := by
    field_simp
  have e2 : 3 * ((1 + 2 * δ) * (G * θ + 2 * (S / N) * rr) + 2 * δ * rr) / sm * p
      = 3 * ((1 + 2 * δ) * (θ / sm * (G * p) + 2 * (S / N) * rr * (p / sm))
          + 2 * δ * rr * (p / sm)) := by
    field_simp
  rw [e1, e2]
  have h1 := mul_le_mul_of_nonneg_right key hGp
  have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + 2 * δ)
  linarith

/-- **The pointwise defect bound with a weight and time-independent constants (deterministic).**
    For every `m ≥ 1` (no restriction on `mσ`), `σ ≤ 1` and every `u`:
    `heatDefBound(u) ≤ 3[(1+2δ)(√12^d θ + 2 (√(NML)/N) 4^d r) + 2δ 4^d r] / √m · p_{12mσ}(u)`,
    `r = rateRA d`. HYPOTHESIS `hθ`: `(2L+2)(heatKbar + M) √m ≤ θ N` (the range of `m`). -/
theorem heatDefBound_weighted {σ M L δ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (d N : ℕ) (hN : 0 < N) (m : ℕ) (hm : 1 ≤ m)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N) (u : FlatTorus d) :
    heatDefBound d σ N m M L δ u
      ≤ 3 * ((1 + 2 * δ) * (Real.sqrt 12 ^ d * θ
              + 2 * (Real.sqrt (N * M * L) / N) * (4 ^ d * rateRA d))
            + 2 * δ * (4 ^ d * rateRA d)) / Real.sqrt m
        * heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) u := by
  have hpi := Real.pi_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have r1 : σ ≤ (m : ℝ) * σ := by nlinarith
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hKB : heatKB d σ ((m : ℝ) * σ) ≤ heatKbar d σ := by
    unfold heatKbar; exact heatKB_le hσ r1 hσ1 d
  have hKB0 := heatKB_nonneg hσ hs d
  have hCV := heatCV_nonneg hσ hs d
  have hc12 : (0 : ℝ) < 2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ)) := by positivity
  have hp12 := heatTorus_nonneg hc12 d u
  have ha := heatTorus_to_twelve hs (by nlinarith : (m : ℝ) * σ ≤ (m : ℝ) * σ + 2 * σ)
    (by nlinarith : (m : ℝ) * σ + 2 * σ ≤ 12 * ((m : ℝ) * σ)) d u
  have hb := heatTorus_to_twelve hs (by nlinarith : (m : ℝ) * σ ≤ σ + (m : ℝ) * σ)
    (by nlinarith : σ + (m : ℝ) * σ ≤ 12 * ((m : ℝ) * σ)) d u
  have hz := wc_Z hσ r1 d u
  have hpa0 := heatTorus_nonneg
    (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) d u
  have hpb0 := heatTorus_nonneg
    (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) d u
  have eσ : Real.sqrt (σ / ((m : ℝ) * σ)) = 1 / Real.sqrt m := by
    have : σ / ((m : ℝ) * σ) = 1 / m := by field_simp
    rw [this, Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [eσ] at hz
  rw [heatDefBound_eq_num hσ hM hL d N m hm δ u]
  unfold heatDefNum
  obtain ⟨pa, hpa⟩ : ∃ pa : ℝ, pa = heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) u :=
    ⟨_, rfl⟩
  obtain ⟨pb, hpb⟩ : ∃ pb : ℝ, pb = heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) u :=
    ⟨_, rfl⟩
  obtain ⟨p6, hp6⟩ : ∃ p6 : ℝ, p6 = heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u :=
    ⟨_, rfl⟩
  obtain ⟨p12, hp12d⟩ :
      ∃ p12 : ℝ, p12 = heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) u := ⟨_, rfl⟩
  obtain ⟨KB, hKBd⟩ : ∃ KB : ℝ, KB = heatKB d σ ((m : ℝ) * σ) := ⟨_, rfl⟩
  obtain ⟨CV, hCVd⟩ : ∃ CV : ℝ, CV = heatCV d σ ((m : ℝ) * σ) := ⟨_, rfl⟩
  obtain ⟨kb, hkbd⟩ : ∃ kb : ℝ, kb = heatKbar d σ := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = rateRA d := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = Real.sqrt 12 ^ d := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F : ℝ, F = (4 : ℝ) ^ d := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hGd]; positivity
  have hF0 : 0 ≤ F := by rw [hFd]; positivity
  have hr0 : 0 ≤ r := by rw [hrd]; exact Real.sqrt_nonneg _
  rw [← hpa, ← hpb, ← hp6, ← hKBd, ← hCVd, ← hp12d, ← hrd, ← hGd, ← hFd]
  rw [← hpa, ← hp12d, ← hGd] at ha
  rw [← hpb, ← hp12d, ← hGd] at hb
  rw [← hp6, ← hp12d, ← hCVd, ← hrd, ← hFd] at hz
  rw [← hpa] at hpa0
  rw [← hpb] at hpb0
  rw [← hp12d] at hp12
  rw [← hKBd, ← hkbd] at hKB
  rw [← hKBd] at hKB0
  rw [← hCVd] at hCV
  rw [← hkbd] at hθ hkb0
  have hX : KB * pa + M * pb ≤ (kb + M) * (G * p12) := by
    have h1 : KB * pa ≤ kb * (G * p12) := mul_le_mul hKB ha hpa0 hkb0
    have h2 : M * pb ≤ M * (G * p12) := mul_le_mul_of_nonneg_left hb hM
    linarith
  have hZ : Real.sqrt CV * Real.sqrt p6 ≤ F * r / Real.sqrt m * p12 := by
    refine hz.trans (le_of_eq ?_)
    field_simp
  have eT : Real.sqrt (N * (M * CV) * L) = Real.sqrt (N * M * L) * Real.sqrt CV := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; ring
  have hT : Real.sqrt (N * (M * CV) * L) * Real.sqrt p6
      ≤ Real.sqrt (N * M * L) * (F * r / Real.sqrt m * p12) := by
    rw [eT, mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)
  refine (defect_closed_core hNpos hL hδ hX hT hZ).trans ?_
  have hfin := wc_assemble (N := N) (L := L) (δ := δ) (S := Real.sqrt (N * M * L)) (kbM := kb + M)
    (G := G) (p := p12) (θ := θ) (rr := F * r) (sm := Real.sqrt m) hNpos hsm hδ
    (mul_nonneg hG0 hp12) hθ
  exact hfin

/-- The constant of the weighted consistency estimate against the `δ'` of the second file
    (`δ' = √(M log N/N)`, `M = (1 + (2πσ)^{-1/2})^d`). It depends only on `d`. -/
noncomputable def wcC (d : ℕ) : ℝ :=
  3 * ((5 / 4) * (16 * (rateCK d + 1) * Real.sqrt 12 ^ d
          + 2 * Real.sqrt 7 * (4 ^ d * rateRA d))
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * (4 ^ d * rateRA d))

theorem wcC_nonneg (d : ℕ) : 0 ≤ wcC d := by
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  unfold wcC; positivity

set_option maxHeartbeats 6400000 in
/-- The parameters of the sample statement (grid `N³`, tolerance `ε = 3√(N M T)`, level
    `L = log(4 K N⁵)`), with the numerical facts used below; the computation is the one in the
    proof of `H5.h5_g3` (third file), stated once as a lemma. -/
theorem wc_params {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * M * Real.log N)))
    (hsmall : rateCfin3 d * δp * Real.sqrt K ≤ 1) :
    ∃ L ε δ0 θ : ℝ, 0 < L ∧ 0 < ε
      ∧ ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤ N / 8
      ∧ δ0 = (ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ))) / N
      ∧ 0 ≤ δ0 ∧ δ0 ≤ 1 / 8 ∧ δ0 ≤ 6 * Real.sqrt (3 * (d : ℝ) + 5) * δp
      ∧ 0 ≤ θ ∧ θ ≤ 16 * (rateCK d + 1) * δp
      ∧ (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N
      ∧ Real.sqrt (N * M * L) / N ≤ Real.sqrt 7 * δp
      ∧ 0 ≤ δp ∧ 0 < M
      ∧ (2 + 4 * (K : ℝ)) * (((N : ℝ) ^ 3) ^ d
            * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))) ≤ 1 / (N : ℝ) ^ 3
      ∧ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) = 1 / (2 * (N : ℝ) ^ 3) := by
  have hN : 0 < N := by omega
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hpi := Real.pi_pos
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hc := cvConst_nonneg
  -- logarithms
  obtain ⟨lg, hlg⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  rw [← hlg] at hδp hLipc
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log ((2 + 4 * K) * (2 * ((N ^ 3 : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (4 * K * (N : ℝ) ^ 5) := ⟨_, rfl⟩
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hg3 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; rfl
  have hNd : (1 : ℝ) ≤ ((N : ℝ) ^ 3) ^ d := one_le_pow₀ hN3
  rw [hg3] at hT
  have hargpos : 0 < (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3 := by positivity
  have hTle : T ≤ (3 * (d : ℝ) + 5) * lg := by
    have h1 : (2 + 4 * (K : ℝ)) * 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (3 * d + 5) := by
      calc (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3
          = ((2 + 4 * (K : ℝ)) * 2) * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (3 * d + 5) := by rw [← pow_mul]; ring
    rw [hT, hlg]
    calc Real.log ((2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3)
        ≤ Real.log ((N : ℝ) ^ (3 * d + 5)) := Real.log_le_log hargpos h2
      _ = (3 * (d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hTge : lg ≤ T := by
    rw [hT, hlg]
    refine Real.log_le_log hNpos ?_
    have h6 : (6 : ℝ) ≤ 2 + 4 * K := by linarith
    have h2 : (2 : ℝ) ≤ 2 * ((N : ℝ) ^ 3) ^ d := by linarith
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (N : ℝ)]
    have h12 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * ((N : ℝ) ^ 3) ^ d) := by nlinarith
    have h13 := mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
    linarith
  have hLle : L ≤ 7 * lg := by
    have h1 : 4 * (K : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 7 := by
      calc 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ 7 := by ring
    rw [hL, hlg]
    calc Real.log (4 * (K : ℝ) * (N : ℝ) ^ 5) ≤ Real.log ((N : ℝ) ^ 7) :=
          Real.log_le_log (by positivity) h2
      _ = 7 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos
    have : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hTpos : 0 < T := by linarith
  -- δ' and the square roots
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * M * lg) := ⟨_, rfl⟩
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hQeq : Q = δp * N := by
    have hsq : (δp * N) ^ 2 = N * M * lg := by
      rw [mul_pow, hδp, Real.sq_sqrt (by positivity)]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt (3 * (d : ℝ) + 5) := ⟨_, rfl⟩
  have hAa0 : 0 ≤ Aa := by rw [hAa]; exact Real.sqrt_nonneg _
  have hAa1 : 1 ≤ Aa := by
    rw [hAa, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hsqT : Real.sqrt (N * M * T) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ N * M)
    exact this.trans (le_of_eq (by ring))
  have hsqTge : Q ≤ Real.sqrt (N * M * T) := by
    rw [hQ]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTge (by positivity))
  -- the constant
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = rateCfin3 d := ⟨_, rfl⟩
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  rw [← hCf] at hsmall
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hCf48 : 48 * Aa ≤ Cf := by rw [hCf, hAa]; exact (rateCfin3_ge d).1
  have hCf0 : 0 ≤ Cf := by linarith
  have h48 : 48 * Aa * δp ≤ 1 := by
    have h1 : 48 * Aa * δp ≤ Cf * δp := mul_le_mul_of_nonneg_right hCf48 hδp0
    have h2 : Cf * δp ≤ Cf * δp * Real.sqrt K :=
      le_mul_of_one_le_right (mul_nonneg hCf0 hδp0) hsK1
    linarith
  have hδK : δp * Real.sqrt K ≤ 1 := by
    have h1 : 1 * (δp * Real.sqrt K) ≤ Cf * (δp * Real.sqrt K) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : Cf * (δp * Real.sqrt K) = Cf * δp * Real.sqrt K := by ring
    linarith
  -- the parameters of the explicit theorem
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 6 * Real.sqrt (N * M * T) / N := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K / N := ⟨_, rfl⟩
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδle : δ ≤ 6 * Aa * δp := by
    rw [hδ, div_le_iff₀ hNpos]
    calc 6 * Real.sqrt (N * M * T) ≤ 6 * (Aa * Q) := by linarith
      _ = 6 * Aa * δp * N := by rw [hQeq]; ring
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hsm : 6 * Real.sqrt (N * M * T) ≤ N / 8 := by
    have : 6 * Real.sqrt (N * M * T) = δ * N := by rw [hδ]; field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hδ8 hNpos.le
    linarith
  have hgc : 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤ 3 * Real.sqrt (N * M * T) := by
    rw [hg3]
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have e : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ) ^ 3) = 2 * Lip / (N : ℝ) ^ 2 := by field_simp
    rw [e, div_le_iff₀ hN2]
    calc 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Q) := by rw [hQ]; exact hLipc
      _ ≤ 3 * Real.sqrt (N * M * T) * (N : ℝ) ^ 2 := by nlinarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθle : θ ≤ 16 * (rateCK d + 1) * δp := by
    have hkb := heatKbar_le_M hσ d
    rw [← hMdef] at hkb
    have h1 : 2 * L + 2 ≤ 16 * lg := by linarith
    have h2 : heatKbar d σ + M ≤ (rateCK d + 1) * M := by linarith
    have h3 : (2 * L + 2) * (heatKbar d σ + M) ≤ 16 * lg * ((rateCK d + 1) * M) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have hδp2 : δp ^ 2 = M * lg / N := by rw [hδp, Real.sq_sqrt (by positivity)]
    rw [hθ, div_le_iff₀ hNpos]
    calc (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K
        ≤ 16 * lg * ((rateCK d + 1) * M) * Real.sqrt K :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = 16 * (rateCK d + 1) * (δp ^ 2 * N) * Real.sqrt K := by rw [hδp2]; field_simp
      _ = 16 * (rateCK d + 1) * δp * N * (δp * Real.sqrt K) := by ring
      _ ≤ 16 * (rateCK d + 1) * δp * N * 1 :=
          mul_le_mul_of_nonneg_left hδK (by positivity)
      _ = 16 * (rateCK d + 1) * δp * N := by ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (N * M * L) / N := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hSle : S ≤ Real.sqrt 7 * δp := by
    rw [hS, div_le_iff₀ hNpos]
    calc Real.sqrt (N * M * L) ≤ Real.sqrt (7 * (N * M * lg)) := by
          apply Real.sqrt_le_sqrt
          have := mul_le_mul_of_nonneg_left hLle (by positivity : (0 : ℝ) ≤ N * M)
          exact this.trans (le_of_eq (by ring))
      _ = Real.sqrt 7 * Q := by rw [hQ, Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 7 * δp * N := by rw [hQeq]; ring
  -- the parameters of the `ℓ¹` theorem
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * M * T) := ⟨_, rfl⟩
  have hsq : 0 < Real.sqrt (N * M * T) := Real.sqrt_pos.mpr (by positivity)
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε2 : ε ^ 2 = 9 * (N * M * T) := by
    rw [hεdef, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  obtain ⟨δ0, hδ0def⟩ :
      ∃ δ0 : ℝ, δ0 = (ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ))) / N := ⟨_, rfl⟩
  have hgc0 : 0 ≤ 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) := by positivity
  have hδ00 : 0 ≤ δ0 := by
    rw [hδ0def]
    exact div_nonneg (by linarith) hNpos.le
  have hδ0le : δ0 ≤ δ := by
    rw [hδ0def, hδ]
    exact div_le_div_of_nonneg_right (by rw [hεdef]; linarith) hNpos.le
  have hδ0le' : δ0 ≤ 6 * Aa * δp := hδ0le.trans hδle
  have hδ08 : δ0 ≤ 1 / 8 := hδ0le.trans hδ8
  have hsmall' : ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤ N / 8 := by
    rw [hεdef]; linarith
  have hθ' : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N := by
    rw [hθ, div_mul_cancel₀ _ hNpos.ne']
  have hTcond : T * (4 * (N * M) + 2 * M * ε) ≤ ε ^ 2 := by
    rw [hε2]
    have h1 : 2 * M * ε * T ≤ 5 * (N * M * T) := by
      have : ε ≤ 5 * N / 2 := by rw [hεdef]; linarith
      have hMT : 0 ≤ M * T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hMT]
    nlinarith
  obtain ⟨Gd, hGd⟩ : ∃ Gd : ℝ, Gd = ((N : ℝ) ^ 3) ^ d := ⟨_, rfl⟩
  rw [← hGd] at hT
  have hGdpos : 0 < Gd := by rw [hGd]; positivity
  have hKpos : (0 : ℝ) < K := by linarith
  obtain ⟨Ar, hAr⟩ : ∃ Ar : ℝ, Ar = (2 + 4 * (K : ℝ)) * (2 * Gd) * (N : ℝ) ^ 3 := ⟨_, rfl⟩
  have hArpos : 0 < Ar := by rw [hAr]; positivity
  have hD : 0 < 4 * (N * M) + 2 * M * ε := by positivity
  have hTA : T = Real.log Ar := by rw [hAr]; exact hT
  rw [hTA] at hTcond
  have he1 : Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ 1 / Ar := by
    have h1 : -ε ^ 2 / (4 * (N * M) + 2 * M * ε) ≤ -Real.log Ar := by
      rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD]; exact hTcond
    calc Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ Real.exp (-Real.log Ar) :=
          Real.exp_le_exp.mpr h1
      _ = 1 / Ar := by rw [Real.exp_neg, Real.exp_log hArpos, one_div]
  have hN5pos : (0 : ℝ) < 4 * K * (N : ℝ) ^ 5 := by positivity
  have he2 : Real.exp (-L) = 1 / (4 * K * (N : ℝ) ^ 5) := by
    rw [hL, Real.exp_neg, Real.exp_log hN5pos, one_div]
  have hp : (2 + 4 * (K : ℝ)) * (Gd * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
      ≤ 1 / (N : ℝ) ^ 3 := by
    calc (2 + 4 * (K : ℝ)) * (Gd * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
        ≤ (2 + 4 * (K : ℝ)) * (Gd * (2 * (1 / Ar))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) hGdpos.le
      _ = 1 / (N : ℝ) ^ 3 := by
          rw [hAr]
          have h2K : (2 + 4 * (K : ℝ)) ≠ 0 := by positivity
          have hGd0 : Gd ≠ 0 := hGdpos.ne'
          have hN30 : (N : ℝ) ^ 3 ≠ 0 := by positivity
          field_simp
  have hq : (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) = 1 / (2 * (N : ℝ) ^ 3) := by
    rw [he2]
    have hK0 : (K : ℝ) ≠ 0 := hKpos.ne'
    have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
    first | (field_simp; done) | (field_simp; ring)
  refine ⟨L, ε, δ0, θ, hLpos, hε, hsmall', hδ0def, hδ00, hδ08, ?_, hθ0, hθle, hθ', ?_, hδp0,
    hMpos, ?_, hq⟩
  · rw [← hAa]; exact hδ0le'
  · rw [← hS]; exact hSle
  · rw [← hGd]; exact hp

/-- The three conclusions of the consistency lemma for points `x_0, …, x_{N-1}`, with the weight
    `p_{12mσ}`: (i) normalisation, (ii) the pointwise weighted bound for the one-step defect
    `h_m^{(i)}(b) = heatDefect d σ N m x b i`, (iii) the mean of the weight over the points. -/
def WeightedGood (d : ℕ) (σ : ℝ) (N K : ℕ) (cδ c : ℝ) (x : ℕ → FlatTorus d) : Prop :=
  (∀ j, |heatRho d σ N x j - 1| ≤ cδ) ∧
  ∀ m, 1 ≤ m → m ≤ K →
    (∀ b, b < N → ∀ i, i < N →
      |heatDefect d σ N m x b i|
        ≤ c * (1 / Real.sqrt m)
          * heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i)) ∧
    (∀ i, ∑ b ∈ Finset.range N,
        heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i) ≤ N * (1 + cδ))

/-- Monotonicity in the two constants. -/
theorem WeightedGood.mono {d : ℕ} {σ : ℝ} (hσ : 0 < σ) {N K : ℕ} {cδ c cδ' c' : ℝ}
    {x : ℕ → FlatTorus d} (h : WeightedGood d σ N K cδ c x) (h1 : cδ ≤ cδ') (h2 : c ≤ c') :
    WeightedGood d σ N K cδ' c' x := by
  have hpi := Real.pi_pos
  refine ⟨fun j => (h.1 j).trans h1, fun m hm hmK => ⟨fun b hb i hi => ?_, fun i => ?_⟩⟩
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hp := heatTorus_nonneg
      (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) d (x b - x i)
    refine ((h.2 m hm hmK).1 b hb i hi).trans (mul_le_mul_of_nonneg_right ?_ hp)
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  · refine ((h.2 m hm hmK).2 i).trans (mul_le_mul_of_nonneg_left (by linarith) ?_)
    exact Nat.cast_nonneg N

/-- The mean form stated after the lemma in the paper, for the weight `p_{12m}`:
    the sum over `b` of the defect is at most `N c (1 + c_δ)/√m` (mean form). -/
theorem WeightedGood.mean {d : ℕ} {σ : ℝ} {N K : ℕ} {cδ c : ℝ} (hc : 0 ≤ c)
    {x : ℕ → FlatTorus d} (h : WeightedGood d σ N K cδ c x) {m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K)
    {i : ℕ} (hi : i < N) :
    ∑ b ∈ Finset.range N, |heatDefect d σ N m x b i|
      ≤ c * (1 / Real.sqrt m) * (N * (1 + cδ)) := by
  obtain ⟨h1, h2⟩ := h.2 m hm hmK
  calc ∑ b ∈ Finset.range N, |heatDefect d σ N m x b i|
      ≤ ∑ b ∈ Finset.range N, c * (1 / Real.sqrt m)
          * heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i) :=
        Finset.sum_le_sum fun b hb => h1 b (Finset.mem_range.mp hb) i hi
    _ = c * (1 / Real.sqrt m) * ∑ b ∈ Finset.range N,
          heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) (x b - x i) := by
        rw [Finset.mul_sum]
    _ ≤ c * (1 / Real.sqrt m) * (N * (1 + cδ)) :=
        mul_le_mul_of_nonneg_left (h2 i) (by positivity)

/-- The supremum form: the defect is at most `c m^{-1/2} p_{12mσ}(0)`. -/
theorem WeightedGood.sup {d : ℕ} {σ : ℝ} (hσ : 0 < σ) {N K : ℕ} {cδ c : ℝ} (hc : 0 ≤ c)
    {x : ℕ → FlatTorus d} (h : WeightedGood d σ N K cδ c x) {m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K)
    {b i : ℕ} (hb : b < N) (hi : i < N) :
    |heatDefect d σ N m x b i|
      ≤ c * (1 / Real.sqrt m) * heatTorus d (2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) 0 := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc12 : (0 : ℝ) < 2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ)) := by positivity
  exact ((h.2 m hm hmK).1 b hb i hi).trans
    (mul_le_mul_of_nonneg_left (TorusReduction.heatTorus_le_zero hc12 d _) (by positivity))

set_option maxHeartbeats 3200000 in
/-- **The consistency lemma with the weight `p_{12m}`, against the `δ'` of the second file**
    (`M = (1 + (2πσ)^{-1/2})^d`, `δ' = √(M log N/N)`), under the hypotheses of `H5.h5_g3`:
    except on an event of probability at most `2/N³`, `WeightedGood` holds with
    `c_δ = h5cD d · δ'` and `c = wcC d · δ'`, for all `1 ≤ m ≤ K` (no restriction `mσ ≤ 1`). -/
theorem weighted_consistency_g3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * M * Real.log N)))
    (hsmall : rateCfin3 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ WeightedGood d σ N K (H5.h5cD d * δp) (wcC d * δp) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  obtain ⟨L, ε, δ0, θ, hLpos, hε, hsmall', hδ0def, hδ00, hδ08, hδ0le, hθ0, hθle, hθ', hSle, hδp0,
    hMpos, hp, hq⟩ := wc_params hσ d N K hN12 hK hKN hMdef hLipdef hδp hLipc hsmall
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hg : 0 < N ^ 3 := pow_pos hN 3
  have hg3 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; rfl
  have hconst : ∀ τ, σ ≤ τ →
      (∀ u, heatTorus d (2 * Real.pi ^ 2 * τ) u ≤ M)
      ∧ (∀ u u', |heatTorus d (2 * Real.pi ^ 2 * τ) u - heatTorus d (2 * Real.pi ^ 2 * τ) u'|
          ≤ Lip * dist u u') := by
    intro τ hτ
    have hcτ : 0 < 2 * Real.pi ^ 2 * τ := by have := lt_of_lt_of_le hσ hτ; positivity
    have hcc : 2 * Real.pi ^ 2 * σ ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    obtain ⟨a1, a2⟩ := heat_consts_anti hcσ hcc d
    constructor
    · intro u; rw [hMdef]; exact (heatTorus_le hcτ d u).trans a1
    · intro u u'; rw [hLipdef]
      exact (heatTorus_lipschitz hcτ d u u').trans (mul_le_mul_of_nonneg_right a2 dist_nonneg)
  obtain ⟨epsn, hepsn⟩ :
      ∃ epsn : ℝ, epsn = ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨pn, hpn⟩ : ∃ pn : ℝ, pn = (((N ^ 3 : ℕ) : ℝ)) ^ d
      * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))) := ⟨_, rfl⟩
  have hpn0 : 0 ≤ pn := by rw [hpn]; positivity
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : ℝ → Set Ω, Bn = fun τ => {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} := ⟨_, rfl⟩
  have hBnP : ∀ τ, σ ≤ τ → μ.real (Bn τ) ≤ pn := by
    intro τ hτ
    rw [hBnd, hpn, hepsn]
    exact heat_normalisation_whp (lt_of_lt_of_le hσ hτ) d X h_indep hX hlaw N hg
      (hconst τ hτ).1 (hconst τ hτ).2 hLip0 hε
  have hBnc : ∀ τ ω, ω ∉ Bn τ → ∀ y : FlatTorus d,
      |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (y - X j ω) - N| ≤ epsn := by
    intro τ ω hω y
    by_contra h
    rw [hBnd] at hω
    exact hω ⟨y, not_le.mp h⟩
  obtain ⟨E, hEd⟩ : ∃ E : Set Ω, E = {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N,
      ∃ i ∈ Finset.range N,
        heatDefBound d σ N m M L ((ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ))) / N)
            (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|} := ⟨_, rfl⟩
  have hEP : μ.real E ≤ pn + (1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3)) := by
    rw [hEd, hpn, ← hq]
    exact heat_defect_sample hσ d X h_indep hX hlaw N K hN hg hMdef hLipdef hLpos hε
      (by linarith)
  have hUP : μ.real (⋃ m ∈ Finset.Icc 1 K, Bn (12 * ((m : ℝ) * σ))) ≤ (K : ℝ) * pn := by
    calc μ.real (⋃ m ∈ Finset.Icc 1 K, Bn (12 * ((m : ℝ) * σ)))
        ≤ ∑ m ∈ Finset.Icc 1 K, μ.real (Bn (12 * ((m : ℝ) * σ))) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, pn := by
          refine Finset.sum_le_sum fun m hm => hBnP _ ?_
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
          nlinarith
      _ = (K : ℝ) * pn := by simp
  have hsub : {ω | ¬ WeightedGood d σ N K (H5.h5cD d * δp) (wcC d * δp) (fun j => X j ω)}
      ⊆ Bn σ ∪ E ∪ ⋃ m ∈ Finset.Icc 1 K, Bn (12 * ((m : ℝ) * σ)) := by
    intro ω hbad
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨hn, hE⟩, hAm⟩ := hcon
    apply hbad
    have hcD : H5.h5cD d * δp = 6 * Real.sqrt (3 * (d : ℝ) + 5) * δp := by
      unfold H5.h5cD; rfl
    have hδN : epsn / N = δ0 := by rw [hδ0def, hepsn]
    have hmem : ∀ m, 1 ≤ m → m ≤ K → m ∈ Finset.Icc 1 K := fun m h1 h2 =>
      Finset.mem_Icc.mpr ⟨h1, h2⟩
    refine WeightedGood.mono hσ (cδ := δ0) (c := wcC d * δp) ⟨?_, ?_⟩ (by rw [hcD]; exact hδ0le)
      le_rfl
    · intro j
      have h := hBnc σ ω hn (X j ω)
      have e : heatRho d σ N (fun j => X j ω) j - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos, ← hδN]
      exact div_le_div_of_nonneg_right h hNpos.le
    · intro m hm hmK
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
      refine ⟨fun b hb i hi => ?_, fun i => ?_⟩
      · have h1 : |heatDefect d σ N m (fun j => X j ω) b i|
            ≤ heatDefBound d σ N m M L δ0 (X b ω - X i ω) := by
          by_contra h
          rw [hEd] at hE
          rw [hδ0def] at h
          exact hE ⟨m, hmem m hm hmK, b, Finset.mem_range.mpr hb, i, Finset.mem_range.mpr hi,
            not_le.mp h⟩
        have hθm : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N := by
          have h1 : Real.sqrt m ≤ Real.sqrt K := Real.sqrt_le_sqrt (by exact_mod_cast hmK)
          have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
          have h2 : 0 ≤ (2 * L + 2) * (heatKbar d σ + M) := by positivity
          exact (mul_le_mul_of_nonneg_left h1 h2).trans hθ'
        have h2 := heatDefBound_weighted hσ hσ1 hMpos.le hLpos.le hδ00 d N hN m hm hθm
          (X b ω - X i ω)
        have hp12 := heatTorus_nonneg
          (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (12 * ((m : ℝ) * σ))) d (X b ω - X i ω)
        have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
        have hRA0 : 0 ≤ rateRA d := by unfold rateRA; exact Real.sqrt_nonneg _
        have hG0 : (0 : ℝ) ≤ Real.sqrt 12 ^ d := by positivity
        have hθG : Real.sqrt 12 ^ d * θ ≤ 16 * (rateCK d + 1) * Real.sqrt 12 ^ d * δp := by
          have := mul_le_mul_of_nonneg_left hθle hG0
          linarith
        have hab := (rate_ab_bound (δ := δ0) (θ := Real.sqrt 12 ^ d * θ)
          (S := Real.sqrt (N * M * L) / N) (r := 4 ^ d * rateRA d) (δp := δp)
          (θ1 := 16 * (rateCK d + 1) * Real.sqrt 12 ^ d) (Aa := Real.sqrt (3 * (d : ℝ) + 5))
          hδ00 hδ08 hδ0le (by positivity) hθG (by positivity) hSle (by positivity) hδp0
          (by positivity) (Real.sqrt_nonneg _)).2
        have hcst : 3 * ((1 + 2 * δ0) * (Real.sqrt 12 ^ d * θ
              + 2 * (Real.sqrt (N * M * L) / N) * (4 ^ d * rateRA d))
            + 2 * δ0 * (4 ^ d * rateRA d)) ≤ wcC d * δp := by
          unfold wcC; exact hab
        refine h1.trans (h2.trans (mul_le_mul_of_nonneg_right ?_ hp12))
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right hcst (by positivity)
      · have hA' := hAm m (hmem m hm hmK)
        have h3 := norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA') i
        rw [hδN] at h3
        exact h3
  have v1 := measureReal_union_le (μ := μ) (Bn σ ∪ E)
    (⋃ m ∈ Finset.Icc 1 K, Bn (12 * ((m : ℝ) * σ)))
  have v2 := measureReal_union_le (μ := μ) (Bn σ) E
  have v0 : μ.real {ω | ¬ WeightedGood d σ N K (H5.h5cD d * δp) (wcC d * δp) (fun j => X j ω)}
      ≤ μ.real (Bn σ ∪ E ∪ ⋃ m ∈ Finset.Icc 1 K, Bn (12 * ((m : ℝ) * σ))) :=
    measureReal_mono hsub (measure_ne_top μ _)
  have hb := hBnP σ le_rfl
  rw [hg3] at hpn
  rw [← hpn] at hp
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have e3 : 2 / (N : ℝ) ^ 3
      = 1 / (N : ℝ) ^ 3 + (1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3)) := by
    field_simp; norm_num
  have hKpn : 0 ≤ (K : ℝ) * pn := by positivity
  rw [e3]
  nlinarith

/-- **The consistency lemma with the weight `p_{12m}`, in the quantities of the paper**
    (`lem:consistency`(i)--(iii) with `p_{12m}` in place of `p_{6m}`): `d ≥ 1`, `σ = ξ² ≤ 1`,
    `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`, `kernelC1 d · δ' · √K ≤ 1`. Except on an event of
    probability at most `2/N³`, for all `1 ≤ m ≤ K` and all `b, i < N`:
    `|ρ_j - 1| ≤ c_δ δ'`, `|h_m^{(i)}(b)| ≤ C δ' m^{-1/2} p_{12mσ}(X_b - X_i)` and
    `∑_b p_{12mσ}(X_b - X_i) ≤ N (1 + c_δ δ')`, with `c_δ = h5cD d (1 + √(2π))^d` and
    `C = wcC d (1 + √(2π))^d`, both depending only on `d`. No further hypothesis. -/
theorem weighted_consistency_paper {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ WeightedGood d σ N K (H5.h5cD d * (1 + Real.sqrt (2 * Real.pi)) ^ d * δp)
        (wcC d * (1 + Real.sqrt (2 * Real.pi)) ^ d * δp) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  obtain ⟨ML, Lip, δL, hML, hLip, hδL, hN12, hKN, hLipc, hsmallL, hδLle, hδL0, hδp0⟩ :=
    H5.h5_setup hσ hσ1 d hd N K hN2 hK hMp hδp hrange
  have h := weighted_consistency_g3 hσ hσ1 d X h_indep hX hlaw N K hN12 hK hKN hML hLip hδL
    hLipc hsmallL
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  have hD0 := (H5.h5c_nonneg d).1
  have hC0 := wcC_nonneg d
  refine WeightedGood.mono hσ hgood ?_ ?_
  · have := mul_le_mul_of_nonneg_left hδLle hD0
    linarith
  · have := mul_le_mul_of_nonneg_left hδLle hC0
    linarith

end WeightedConsistency

namespace SharpVariance

/-!
## The variance bound of the consistency lemma with the weight `p^{(3s)}` (`eq:cons-v`), and the
## consistency lemma with the weight `p_{6m}` of the paper

Contents.
* `torus_variance_sharp`: the variance bound on the flat torus with the factor `σ/s` and the weight
  `p_{3s}` (kernel of variance `3s`), as in `eq:cons-v`; before: `p_{6s}` (`torus_variance`).
* `heat_defect_sample3`: the pointwise bound `heatDefBound3` for the one-step defect of the sampled
  walk, with probability; the chain of the second file repeated with the new variance quantity.
* `heatDefBound_weighted3` (deterministic): `heatDefBound3(u) ≤ (explicit number)/√m · p_{6mσ}(u)`.
* `weighted_consistency_g3_w3`, `weighted_consistency_paper_w3`: the three estimates of
  `lem:consistency` with the weight `p_{6m}` (before: `p_{12m}`, `WeightedConsistency`), except on
  an event of probability at most `2/N³`.
Not proved: the lemma of the paper with its own constants, range `m ≤ δ'^{-2}` and event; (P3);
the Gaussian Poincaré inequality; measurability of the exceptional sets.

The variance bound `torus_variance` of the second file carries the kernel of variance `6s` as
weight, because `gauss_shift_cost` pays a factor two in the exponent when the centre
`x + (n+n')/2` of a lattice-pair term is moved to the lattice point `x + n`. Here the centre is
moved to the NEARER of the two points `x + n`, `x + n'` (`gauss_shift_two`), which costs nothing in
the exponent, and the double series is summed twice. The result is the bound with the kernel of
variance `3s`, the weight of `eq:cons-v` in the paper.
-/

/-- Moving the centre of a Gaussian from the midpoint `v - k/2` of `v` and `v - k` to the nearer of
    the two points, without loss in the exponent:
    `e^{-(v - k/2)²/(6s)} ≤ e^{k²/(24s)} (e^{-v²/(6s)} + e^{-(v-k)²/(6s)})`. -/
theorem gauss_shift_two {s : ℝ} (hs : 0 < s) (v k : ℝ) :
    Real.exp (-((v - k / 2) ^ 2) / (6 * s))
      ≤ Real.exp (k ^ 2 / (24 * s))
        * (Real.exp (-(v ^ 2) / (6 * s)) + Real.exp (-((v - k) ^ 2) / (6 * s))) := by
  have hE := Real.exp_pos (k ^ 2 / (24 * s))
  have key : ∀ a : ℝ, a ^ 2 ≤ (v - k / 2) ^ 2 + k ^ 2 / 4 →
      Real.exp (-((v - k / 2) ^ 2) / (6 * s))
        ≤ Real.exp (k ^ 2 / (24 * s)) * Real.exp (-(a ^ 2) / (6 * s)) := by
    intro a ha
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : k ^ 2 / (24 * s) + -(a ^ 2) / (6 * s) = -(a ^ 2 - k ^ 2 / 4) / (6 * s) := by
      field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  rcases le_total (v ^ 2) ((v - k) ^ 2) with h | h
  · calc _ ≤ Real.exp (k ^ 2 / (24 * s)) * Real.exp (-(v ^ 2) / (6 * s)) :=
          key v (by nlinarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (Real.exp_pos _).le) hE.le
  · calc _ ≤ Real.exp (k ^ 2 / (24 * s)) * Real.exp (-((v - k) ^ 2) / (6 * s)) :=
          key (v - k) (by nlinarith)
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (Real.exp_pos _).le) hE.le

/-- **One lattice-pair term of the periodised variance, sharp weight.** For `0 < σ ≤ s`, with
    `v = x + n`, `k = n - n'` (so `v - k = x + n'`), the term
    `e^{-k²/(4s)} M₂(v - k/2) - e^{-k²/(4(s+σ))} M₁²(v - k/2)` is at most
    `(σ/s) · 4/(π s) · e^{-k²/(12s)} (e^{-v²/(6s)} + e^{-(v-k)²/(6s)})`. -/
theorem pair_variance_term_sharp {s σ : ℝ} (hs : 0 < s) (hσ : 0 < σ) (hσs : σ ≤ s) (v k : ℝ) :
    Real.exp (-(k ^ 2) / (4 * s))
        * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
            * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ)))
      - Real.exp (-(k ^ 2) / (4 * (s + σ)))
        * (1 / (2 * Real.pi * (s + σ)) * Real.exp (-((v - k / 2) ^ 2) / (s + σ)))
      ≤ σ / s * (4 / (Real.pi * s))
        * (Real.exp (-(k ^ 2) / (12 * s))
          * (Real.exp (-(v ^ 2) / (6 * s)) + Real.exp (-((v - k) ^ 2) / (6 * s)))) := by
  have hpi := Real.pi_pos
  have hcore := gauss_variance_core hs hσ hσs (v - k / 2)
  have hM2 : 0 ≤ 1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
      * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ)) := by positivity
  have hk : Real.exp (-(k ^ 2) / (4 * s)) ≤ Real.exp (-(k ^ 2) / (4 * (s + σ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (_root_.sq_nonneg k) (by positivity) (by linarith)
  have hk2 : Real.exp (-(k ^ 2) / (4 * (s + σ))) ≤ Real.exp (-(k ^ 2) / (8 * s)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (_root_.sq_nonneg k) (by positivity) (by linarith)
  have hshift := gauss_shift_two hs v k
  have hcomb : Real.exp (-(k ^ 2) / (8 * s)) * Real.exp (k ^ 2 / (24 * s))
      = Real.exp (-(k ^ 2) / (12 * s)) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hE := Real.exp_pos (-(k ^ 2) / (4 * (s + σ)))
  have hc0 : 0 ≤ σ / s * (4 / (Real.pi * s)) := by positivity
  calc _ ≤ Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
              * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ)))
        - Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * (s + σ)) * Real.exp (-((v - k / 2) ^ 2) / (s + σ))) := by
        have := mul_le_mul_of_nonneg_right hk hM2
        linarith
    _ = Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * Real.sqrt (s * (s + 2 * σ)))
              * Real.exp (-((v - k / 2) ^ 2) / (s + 2 * σ))
            - 1 / (2 * Real.pi * (s + σ)) * Real.exp (-((v - k / 2) ^ 2) / (s + σ))) := by ring
    _ ≤ Real.exp (-(k ^ 2) / (4 * (s + σ)))
          * (σ / s * (4 / (Real.pi * s)) * Real.exp (-((v - k / 2) ^ 2) / (6 * s))) :=
        mul_le_mul_of_nonneg_left hcore hE.le
    _ ≤ Real.exp (-(k ^ 2) / (8 * s))
          * (σ / s * (4 / (Real.pi * s))
            * (Real.exp (k ^ 2 / (24 * s))
              * (Real.exp (-(v ^ 2) / (6 * s)) + Real.exp (-((v - k) ^ 2) / (6 * s))))) := by
        refine mul_le_mul hk2 (mul_le_mul_of_nonneg_left hshift hc0) (by positivity) (by positivity)
    _ = σ / s * (4 / (Real.pi * s))
          * (Real.exp (-(k ^ 2) / (12 * s))
            * (Real.exp (-(v ^ 2) / (6 * s)) + Real.exp (-((v - k) ^ 2) / (6 * s)))) := by
        rw [← hcomb]; ring

/-- The bounding double series with two different rates, in the coordinates `(n, n')`, weight at
    the first lattice point:
    `∑_{n,n'} e^{-a(n+x)²} e^{-b(n-n')²} ≤ (1 + √(π/b)) ∑_n e^{-a(n+x)²}`. -/
theorem pair_bound_first {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Summable (fun p : ℤ × ℤ => Real.exp (-a * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) ∧
    ∑' p : ℤ × ℤ, Real.exp (-a * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)
      ≤ (1 + Real.sqrt (Real.pi / b)) * ∑' n : ℤ, Real.exp (-a * ((n : ℝ) - (-x)) ^ 2) := by
  have hf := gauss_shift_summable ha (-x)
  have hg := gauss_summable_int hb
  have hfg := Summable.mul_of_nonneg hf hg (fun n => (Real.exp_pos _).le)
    (fun n => (Real.exp_pos _).le)
  have hle : ∑' p : ℤ × ℤ, Real.exp (-a * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (p.2 : ℝ) ^ 2)
      ≤ (1 + Real.sqrt (Real.pi / b)) * ∑' n : ℤ, Real.exp (-a * ((n : ℝ) - (-x)) ^ 2) := by
    rw [← hf.tsum_mul_tsum hg hfg, mul_comm]
    exact mul_le_mul_of_nonneg_right (gauss_tsum_int_le hb)
      (tsum_nonneg fun n => (Real.exp_pos _).le)
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (p.1, p.1 - p.2), invFun := fun p => (p.1, p.1 - p.2),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  refine ⟨(Equiv.summable_iff e).mpr hfg, ?_⟩
  have h := Equiv.tsum_eq e (fun p : ℤ × ℤ => Real.exp (-a * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (p.2 : ℝ) ^ 2))
  exact (le_of_eq h).trans hle

/-- The same double series with the weight at the second lattice point. -/
theorem pair_bound_second {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    Summable (fun p : ℤ × ℤ => Real.exp (-a * ((p.2 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) ∧
    ∑' p : ℤ × ℤ, Real.exp (-a * ((p.2 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)
      ≤ (1 + Real.sqrt (Real.pi / b)) * ∑' n : ℤ, Real.exp (-a * ((n : ℝ) - (-x)) ^ 2) := by
  obtain ⟨hs1, hle⟩ := pair_bound_first ha hb x
  have hfun : (fun p : ℤ × ℤ => Real.exp (-a * ((p.2 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2))
      = (fun p : ℤ × ℤ => Real.exp (-a * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) ∘ (Equiv.prodComm ℤ ℤ) := by
    funext p
    simp only [Function.comp_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    congr 2
    push_cast
    ring
  rw [hfun]
  refine ⟨(Equiv.summable_iff (Equiv.prodComm ℤ ℤ)).mpr hs1, ?_⟩
  exact (le_of_eq (Equiv.tsum_eq (Equiv.prodComm ℤ ℤ)
    (fun p : ℤ × ℤ => Real.exp (-a * ((p.1 : ℝ) - (-x)) ^ 2)
        * Real.exp (-b * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)))).trans hle

/-- **Variance of the periodised Gaussian under a Gaussian, one variable, with the factor `σ/s`
    and the sharp weight:** for `0 < σ ≤ s` and `g = ∑_n γ_s(· + n)`,
    `∫ γ_σ(x - y) g(y)² dy - (∫ γ_σ(x - y) g(y) dy)²
      ≤ (σ/s) · 4/(πs) · 2 (1 + √(12πs)) · ∑_n e^{-(x+n)²/(6s)}`.
    The right-hand side is a multiple of the periodised Gaussian of variance `3s` (in
    `per_variance_line` of the second file it is the one of variance `6s`). -/
theorem per_variance_line_sharp {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x : ℝ) :
    (∫ y : ℝ, gaussR σ (x - y) * (∑' n : ℤ, gaussR s (y + n)) ^ 2)
      - (∫ y : ℝ, gaussR σ (x - y) * ∑' n : ℤ, gaussR s (y + n)) ^ 2
      ≤ σ / s * (4 / (Real.pi * s)) * (2 * (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ∑' n : ℤ, Real.exp (-(1 / (6 * s)) * ((n : ℝ) - (-x)) ^ 2)) := by
  have hpi := Real.pi_pos
  have hτ : 0 < σ + s := by positivity
  rw [per_second_moment hσ hs hσs, per_first_moment hσ hs]
  have hf := gaussR_shift_summable hτ x
  have hprod := Summable.mul_of_nonneg hf hf (fun n => gaussR_nonneg _ _)
    (fun n => gaussR_nonneg _ _)
  rw [_root_.sq, hf.tsum_mul_tsum hf hprod, ← (pairVal_summable hσ hs hσs x).tsum_sub hprod]
  have ha : (0 : ℝ) < 1 / (6 * s) := by positivity
  have hb : (0 : ℝ) < 1 / (12 * s) := by positivity
  obtain ⟨hs1, hle1⟩ := pair_bound_first ha hb x
  obtain ⟨hs2, hle2⟩ := pair_bound_second ha hb x
  have hc0 : 0 ≤ σ / s * (4 / (Real.pi * s)) := by positivity
  have hterm : ∀ p : ℤ × ℤ, pairVal σ s x p - gaussR (σ + s) (x + p.1) * gaussR (σ + s) (x + p.2)
      ≤ σ / s * (4 / (Real.pi * s))
        * (Real.exp (-(1 / (6 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
            * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)
          + Real.exp (-(1 / (6 * s)) * ((p.2 : ℝ) - (-x)) ^ 2)
            * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) := by
    intro p
    have h := pair_variance_term_sharp hs hσ hσs (x + p.1) ((p.1 : ℝ) - p.2)
    have e1 : x + (p.1 : ℝ) - ((p.1 : ℝ) - p.2) / 2 = x + ((p.1 : ℝ) + p.2) / 2 := by ring
    have hQ : gaussR (σ + s) (x + p.1) * gaussR (σ + s) (x + p.2)
        = Real.exp (-(((p.1 : ℝ) - p.2) ^ 2) / (4 * (s + σ)))
          * (1 / (2 * Real.pi * (s + σ))
            * Real.exp (-((x + ((p.1 : ℝ) + p.2) / 2) ^ 2) / (s + σ))) := by
      have := gauss_first_pair hτ x (p.1 : ℝ) (p.2 : ℝ)
      unfold gaussR
      rw [this, add_comm σ s]
    rw [e1] at h
    rw [hQ]
    unfold pairVal
    have e2 : Real.exp (-(1 / (6 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
        = Real.exp (-((x + (p.1 : ℝ)) ^ 2) / (6 * s)) := by congr 1; ring
    have e2' : Real.exp (-(1 / (6 * s)) * ((p.2 : ℝ) - (-x)) ^ 2)
        = Real.exp (-((x + (p.1 : ℝ) - ((p.1 : ℝ) - p.2)) ^ 2) / (6 * s)) := by congr 1; ring
    have e3 : Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)
        = Real.exp (-(((p.1 : ℝ) - p.2) ^ 2) / (12 * s)) := by
      congr 1; push_cast; ring
    rw [e2, e2', e3]
    calc _ ≤ σ / s * (4 / (Real.pi * s))
          * (Real.exp (-(((p.1 : ℝ) - p.2) ^ 2) / (12 * s))
            * (Real.exp (-((x + (p.1 : ℝ)) ^ 2) / (6 * s))
              + Real.exp (-((x + (p.1 : ℝ) - ((p.1 : ℝ) - p.2)) ^ 2) / (6 * s)))) := h
      _ = _ := by ring
  have hdiffsum : Summable fun p : ℤ × ℤ =>
      pairVal σ s x p - gaussR (σ + s) (x + p.1) * gaussR (σ + s) (x + p.2) :=
    (pairVal_summable hσ hs hσs x).sub hprod
  calc _ ≤ ∑' p : ℤ × ℤ, σ / s * (4 / (Real.pi * s))
          * (Real.exp (-(1 / (6 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
              * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)
            + Real.exp (-(1 / (6 * s)) * ((p.2 : ℝ) - (-x)) ^ 2)
              * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) :=
        hdiffsum.tsum_le_tsum hterm ((hs1.add hs2).mul_left _)
    _ = σ / s * (4 / (Real.pi * s))
          * ((∑' p : ℤ × ℤ, Real.exp (-(1 / (6 * s)) * ((p.1 : ℝ) - (-x)) ^ 2)
              * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2))
            + ∑' p : ℤ × ℤ, Real.exp (-(1 / (6 * s)) * ((p.2 : ℝ) - (-x)) ^ 2)
              * Real.exp (-(1 / (12 * s)) * (((p.1 - p.2 : ℤ) : ℝ)) ^ 2)) := by
        rw [tsum_mul_left, hs1.tsum_add hs2]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        linarith


/-- **Variance bound on the circle, with the factor `σ/s` and the sharp weight.** For `0 < σ ≤ s`, with `P_σ`, `P_s`
    the heat kernels of the circle at times `σ`, `s` (`c = 2π²τ`) and real `x, w`,
    `∫ P_σ(x - u) P_s(u - w)² du - (∫ P_σ(x - u) P_s(u - w) du)²
      ≤ (σ/s) · 4/(πs) · 2 (1 + √(12πs)) · ∑_n e^{-(x - w + n)²/(6s)}`. -/
theorem circle_variance_sharp {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x w : ℝ) :
    (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
      - (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) ^ 2
      ≤ σ / s * (4 / (Real.pi * s)) * (2 * (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ∑' n : ℤ, Real.exp (-(1 / (6 * s)) * ((n : ℝ) - (-(x - w))) ^ 2)) := by
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hG : Continuous fun u : UnitAddCircle => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) :=
    (pC_continuous hcs).comp (continuous_id.sub continuous_const)
  have hGb : ∀ u : UnitAddCircle, |pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))|
      ≤ (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1 := fun u => by
    rw [abs_of_nonneg (pC_nonneg hcs _)]; exact pC_le hcs _
  have hval : ∀ y : ℝ, pC (2 * Real.pi ^ 2 * s) ((y : UnitAddCircle) - (w : UnitAddCircle))
      = ∑' n : ℤ, gaussR s (y - w + n) := fun y => by
    rw [← AddCircle.coe_sub, pC_coe hcs, perGauss_eq_tsum_gaussR hs]
  have h2 := circle_gauss_integral hσ x
    (fun u => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2) (hG.pow 2).measurable
    (B := ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1) ^ 2) (fun u => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hGb u) 2)
  have h1 := circle_gauss_integral hσ x
    (fun u => pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))) hG.measurable hGb
  simp only [hval] at h1 h2
  rw [h1, h2]
  have t2 := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => gaussR σ (x - y) * (∑' n : ℤ, gaussR s (y - w + n)) ^ 2) w
  have t1 := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => gaussR σ (x - y) * ∑' n : ℤ, gaussR s (y - w + n)) w
  have e : ∀ y : ℝ, x - (y + w) = (x - w) - y := fun y => by ring
  have e' : ∀ y : ℝ, y + w - w = y := fun y => by ring
  simp only [e, e'] at t1 t2
  rw [← t1, ← t2]
  exact per_variance_line_sharp hσ hs hσs (x - w)

/-- **Variance bound on the circle with the weight of the paper:** for `0 < σ ≤ s`,
    `∫ P_σ(x - u) P_s(u - w)² du - (∫ P_σ(x - u) P_s(u - w) du)²
      ≤ (σ/s) · 4/(πs) · 2 (1 + √(12πs)) · (6πs)^{1/2} · P_{3s}(x - w)`:
    the weight is the heat kernel of the circle at time `3s`, as in `eq:cons-v` of the paper. -/
theorem circle_variance_weight_sharp {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (x w : ℝ) :
    (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle)) ^ 2
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
      - (∫ u, pC (2 * Real.pi ^ 2 * σ) ((x : UnitAddCircle) - u)
          * pC (2 * Real.pi ^ 2 * s) (u - (w : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) ^ 2
      ≤ σ / s * (4 / (Real.pi * s)) * (2 * (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
        * ((2 * Real.pi * (3 * s)) ^ (1 / 2 : ℝ)
          * pC (2 * Real.pi ^ 2 * (3 * s)) ((x : UnitAddCircle) - (w : UnitAddCircle)))) := by
  have h := circle_variance_sharp hσ hs hσs x w
  have h6 : (0 : ℝ) < 3 * s := by positivity
  have e := gauss_sum_eq_pC h6 (-(x - w))
  have e1 : (1 : ℝ) / (2 * (3 * s)) = 1 / (6 * s) := by rw [← mul_assoc]; norm_num
  rw [e1] at e
  rw [e] at h
  have e2 : (((-(x - w) : ℝ)) : UnitAddCircle) = -((x : UnitAddCircle) - (w : UnitAddCircle)) := by
    rw [AddCircle.coe_neg, AddCircle.coe_sub]
  rw [e2, pC_even] at h
  exact h

/-- **Variance bound on the flat torus of dimension `d`, with the factor `σ/s` and the weight
    `p^{(3s)}` of `eq:cons-v`.** For `0 < σ ≤ s`, with `p_τ` the heat kernel of the torus at time `τ`
    (`heatTorus d (2π²τ)`) and points `X, W` of the torus with real coordinates,
    `∫ p_σ(X - y) p_s(y - W)² dy - (∫ p_σ(X - y) p_s(y - W) dy)² ≤ d · ε · α^{d-1} · p_{3s}(X - W)`,
    where `ε = (σ/s) · 4/(πs) · 2 (1 + √(12πs)) · (6πs)^{1/2}` carries the factor `σ/s = 1/m` and
    `α = (1 + √(π/c_s)) · (3s/(σ+s))^{1/2}`. Compared with `torus_variance` of the second file the
    weight is the kernel at time `3s` instead of `6s`. The constants depend on `s`; for `s ≤ 1` they
    are of the size `(σ/s) s^{-d/2}`, i.e. `(1/m) p^{(2s)}(0)` of the paper up to a constant (this
    last comparison is not a statement of the file). No Gaussian Poincaré inequality is used. -/
theorem torus_variance_sharp {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : Fin d → ℝ) :
    (∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle)) ^ 2
        ∂flatTorusMeasure d)
      - (∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
        ∂flatTorusMeasure d) ^ 2
      ≤ (d : ℝ) * (σ / s * (4 / (Real.pi * s)) * (2 * (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
            * (2 * Real.pi * (3 * s)) ^ (1 / 2 : ℝ)))
          * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
            * ((2 * Real.pi ^ 2 * (3 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)) ^ (d - 1)
          * heatTorus d (2 * Real.pi ^ 2 * (3 * s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)) := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hcτ : 0 < 2 * Real.pi ^ 2 * (σ + s) := by positivity
  have hc3 : 0 < 2 * Real.pi ^ 2 * (3 * s) := by positivity
  have hτ3 : 2 * Real.pi ^ 2 * (σ + s) ≤ 2 * Real.pi ^ 2 * (3 * s) := by
    have : 0 ≤ 2 * Real.pi ^ 2 := by positivity
    nlinarith
  set S : ℝ := (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1 with hS
  set ρ : ℝ := ((2 * Real.pi ^ 2 * (3 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ) with hρ
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have e2 : ∀ y : FlatTorus d,
      heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle)) ^ 2
        = ∏ i, (pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - y i)
            * pC (2 * Real.pi ^ 2 * s) (y i - ((w i : ℝ) : UnitAddCircle)) ^ 2) := by
    intro y
    rw [heatTorus_eq_prod_pC hcσ, heatTorus_eq_prod_pC hcs, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    rfl
  have e1 : ∀ y : FlatTorus d,
      heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
        = ∏ i, (pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - y i)
            * pC (2 * Real.pi ^ 2 * s) (y i - ((w i : ℝ) : UnitAddCircle))) := by
    intro y
    rw [heatTorus_eq_prod_pC hcσ, heatTorus_eq_prod_pC hcs, ← Finset.prod_mul_distrib]
    rfl
  simp_rw [e2, e1]
  rw [flatTorus_integral_prod d (fun i u => pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle)) ^ 2),
    flatTorus_integral_prod d (fun i u => pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle))),
    ← Finset.prod_pow, heatTorus_eq_prod_pC hc3]
  have hfirst : ∀ i : Fin d, ∫ u, pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)
      = pC (2 * Real.pi ^ 2 * (σ + s)) (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)) :=
    fun i => circle_first_moment hσ hs (x i) (w i)
  have hτle : ∀ z : UnitAddCircle, pC (2 * Real.pi ^ 2 * (σ + s)) z
      ≤ ρ * pC (2 * Real.pi ^ 2 * (3 * s)) z := fun z => pC_P1 hcτ hτ3 z
  have hτS : ∀ z : UnitAddCircle, pC (2 * Real.pi ^ 2 * (σ + s)) z ≤ S := by
    intro z
    refine (pC_le hcτ z).trans ?_
    rw [hS, pow_one, pow_one]
    have : Real.pi / (2 * Real.pi ^ 2 * (σ + s)) ≤ Real.pi / (2 * Real.pi ^ 2 * s) :=
      div_le_div_of_nonneg_left hpi.le hcs (by nlinarith [_root_.sq_nonneg Real.pi])
    linarith [Real.sqrt_le_sqrt this]
  have h := prod_sub_prod_le (Finset.univ : Finset (Fin d))
    (fun i => ∫ u, pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle)) ^ 2
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
    (fun i => (∫ u, pC (2 * Real.pi ^ 2 * σ) (((x i : ℝ) : UnitAddCircle) - u)
        * pC (2 * Real.pi ^ 2 * s) (u - ((w i : ℝ) : UnitAddCircle))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) ^ 2)
    (fun i => pC (2 * Real.pi ^ 2 * (3 * s))
        (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)))
    (α := S * ρ)
    (ε := σ / s * (4 / (Real.pi * s)) * (2 * (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
            * (2 * Real.pi * (3 * s)) ^ (1 / 2 : ℝ)))
    (mul_nonneg hS0 hρ0) (by positivity)
    (fun i => integral_nonneg fun u => mul_nonneg (pC_nonneg hcσ _) (_root_.sq_nonneg _))
    (fun i => _root_.sq_nonneg _)
    (fun i => by
      beta_reduce
      rw [hfirst i]
      have a1 := hτS (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      have a2 := hτle (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      have a0 := pC_nonneg hcτ (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      calc _ = pC (2 * Real.pi ^ 2 * (σ + s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
            * pC (2 * Real.pi ^ 2 * (σ + s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)) := _root_.sq _
        _ ≤ S * (ρ * pC (2 * Real.pi ^ 2 * (3 * s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))) :=
            mul_le_mul a1 a2 a0 hS0
        _ = _ := by ring)
    (fun i => by
      have a2 := hτle (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))
      calc _ ≤ S * pC (2 * Real.pi ^ 2 * (σ + s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle)) :=
            circle_second_le hσ hs (x i) (w i)
        _ ≤ S * (ρ * pC (2 * Real.pi ^ 2 * (3 * s))
              (((x i : ℝ) : UnitAddCircle) - ((w i : ℝ) : UnitAddCircle))) :=
            mul_le_mul_of_nonneg_left a2 hS0
        _ = _ := by ring)
    (fun i => by
      have := circle_variance_weight_sharp hσ hs hσs (x i) (w i)
      calc _ ≤ _ := this
        _ = _ := by ring)
    (fun i => pC_nonneg hc3 _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

/-!
## The consistency lemma with the weight `p_{6m}` of the paper

The chain of the second file from the variance bound to the defect of the sampled walk
(`heatV`, `heatThr`, `heatDefBound`, `heat_consistency_*`, `heat_abs_consistency_*`,
`heat_defect_*`) is repeated below with the variance quantity `heatV3`, which carries the weight
`p_{3s}`; the names of the repeated statements end in `3`. Their proofs are the proofs of the second
file with `torus_variance_w3` in place of `torus_variance`. To reuse the closed bounds of the second
file for the coefficient, `heatV3` is defined with the coefficient `heatCV3 = 2 · heatCV` (an upper
bound for the coefficient of `torus_variance_sharp`, see `sharp_const_le`).
-/

open WeightedConsistency

/-- Algebra for `sharp_const_le`, with free variables. -/
theorem sharp_const_alg {dd c A r3 r6 q3 q6 : ℝ} (n : ℕ) (hd : 0 ≤ dd) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hr3 : 0 ≤ r3) (hr : r3 ≤ r6) (hq3 : 0 ≤ q3) (hq : q3 ≤ q6) :
    dd * (c * (2 * A * r3)) * q3 ^ n ≤ 2 * (dd * (c * (A * r6)) * q6 ^ n) := by
  have hpow := pow_le_pow_left₀ hq3 hq n
  have h1 : dd * (c * (A * r3)) ≤ dd * (c * (A * r6)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hA) hc) hd
  have h2 : dd * (c * (A * r3)) * q3 ^ n ≤ dd * (c * (A * r6)) * q6 ^ n :=
    mul_le_mul h1 hpow (pow_nonneg hq3 n)
      (mul_nonneg hd (mul_nonneg hc (mul_nonneg hA (hr3.trans hr))))
  calc dd * (c * (2 * A * r3)) * q3 ^ n = 2 * (dd * (c * (A * r3)) * q3 ^ n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- The coefficient of `p_{3s}` in `torus_variance_sharp` is at most twice the coefficient
    `heatCV` of `p_{6s}` in `torus_variance`. -/
theorem sharp_const_le {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) :
    (d : ℝ) * (σ / s * (4 / (Real.pi * s)) * (2 * (1 + Real.sqrt (Real.pi / (1 / (12 * s))))
            * (2 * Real.pi * (3 * s)) ^ (1 / 2 : ℝ)))
          * ((1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1
            * ((2 * Real.pi ^ 2 * (3 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)) ^ (d - 1)
      ≤ 2 * heatCV d σ s := by
  have hpi := Real.pi_pos
  have h1 : (2 * Real.pi * (3 * s)) ^ (1 / 2 : ℝ) ≤ (2 * Real.pi * (6 * s)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by norm_num)
  have h2 : ((2 * Real.pi ^ 2 * (3 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ)
      ≤ ((2 * Real.pi ^ 2 * (6 * s)) / (2 * Real.pi ^ 2 * (σ + s))) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by positivity)) (by norm_num)
  have hS : (0 : ℝ) ≤ (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * s))) ^ 1 := by positivity
  unfold heatCV
  exact sharp_const_alg (d - 1) (Nat.cast_nonneg d) (by positivity) (by positivity)
    (by positivity) h1 (by positivity) (mul_le_mul_of_nonneg_left h2 hS)

/-- Coefficient of `p_{3s}` in the variance bound `heatV3`: twice the coefficient `heatCV` of the
    second file. -/
noncomputable def heatCV3 (d : ℕ) (σ s : ℝ) : ℝ := 2 * heatCV d σ s

theorem heatCV3_nonneg {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) : 0 ≤ heatCV3 d σ s := by
  unfold heatCV3
  have := heatCV_nonneg hσ hs d
  linarith

/-- The variance bound with the weight `p_{3s}`, as a function of `u = x - w`. -/
noncomputable def heatV3 (d : ℕ) (σ s : ℝ) (u : FlatTorus d) : ℝ :=
  heatCV3 d σ s * heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u

theorem heatV3_nonneg {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (u : FlatTorus d) :
    0 ≤ heatV3 d σ s u := by
  unfold heatV3
  have hpi := Real.pi_pos
  exact mul_nonneg (heatCV3_nonneg hσ hs d)
    (heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (3 * s)) d u)

theorem heatV3_eq (d : ℕ) (σ s : ℝ) (u : FlatTorus d) :
    heatV3 d σ s u = heatCV3 d σ s * heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u := rfl

/-- **The variance bound on the torus with the weight `p_{3s}` and the coefficient `heatCV3`**
    (`torus_variance_sharp` with its coefficient bounded by `sharp_const_le`). -/
theorem torus_variance_w3 {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : Fin d → ℝ) :
    (∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle)) ^ 2
        ∂flatTorusMeasure d)
      - (∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - y)
          * heatTorus d (2 * Real.pi ^ 2 * s) (y - fun i => ((w i : ℝ) : UnitAddCircle))
        ∂flatTorusMeasure d) ^ 2
      ≤ heatCV3 d σ s * heatTorus d (2 * Real.pi ^ 2 * (3 * s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)) := by
  have hpi := Real.pi_pos
  refine (torus_variance_sharp hσ hs hσs d x w).trans ?_
  unfold heatCV3
  exact mul_le_mul_of_nonneg_right (sharp_const_le hσ hs d)
    (heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (3 * s)) d _)


/-- **Consistency at fixed points with the sharp variance (Bernstein step of the consistency
    lemma).** Independent uniform points `X_j` on the flat torus; fixed points `x, w` (real
    coordinates), times `0 < σ ≤ s`; `Y(z) = p_σ(x - z) (p_s(z - w) - p_{σ+s}(x - w))`. If
    `|Y| ≤ Bb` (HYPOTHESIS, to be supplied by (P4)) and `p_σ ≤ Mσ`, then for every finite index set
    `T`,
    `P(|∑_{j ∈ T} Y(X_j)| ≥ eps) ≤ 2 exp(-eps² / (4 |T| Mσ V + 2 Bb eps))`,
    where `V = heatCV3 · p_{3s}(x - w)` is the bound of `torus_variance_w3`, which carries the
    factor `σ/s = 1/m` and the weight `p_{3s}`. -/
theorem heat_consistency_fixed3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : Fin d → ℝ) (T : Finset ℕ)
    {Bb Mσ ε : ℝ} (hBb : 0 < Bb)
    (hY : ∀ z : FlatTorus d,
      |heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - z)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (z - fun i => ((w i : ℝ) : UnitAddCircle))
          - heatTorus d (2 * Real.pi ^ 2 * (σ + s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)))| ≤ Bb)
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T,
        heatTorus d (2 * Real.pi ^ 2 * σ) ((fun i => ((x i : ℝ) : UnitAddCircle)) - X j ω)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (X j ω - fun i => ((w i : ℝ) : UnitAddCircle))
          - heatTorus d (2 * Real.pi ^ 2 * (σ + s))
              ((fun i => ((x i : ℝ) : UnitAddCircle)) - fun i => ((w i : ℝ) : UnitAddCircle)))|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * (Mσ
          * (heatCV3 d σ s * heatTorus d (2 * Real.pi ^ 2 * (3 * s))
                  ((fun i => ((x i : ℝ) : UnitAddCircle))
                    - fun i => ((w i : ℝ) : UnitAddCircle))))) + 2 * Bb * ε)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  set X0 : FlatTorus d := fun i => ((x i : ℝ) : UnitAddCircle) with hX0
  set W0 : FlatTorus d := fun i => ((w i : ℝ) : UnitAddCircle) with hW0
  set c : ℝ := heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) with hc
  have hK : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) :=
    (heatTorus_continuous hcσ d).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) :=
    (heatTorus_continuous hcs d).comp (continuous_id.sub continuous_const)
  have hYc : Continuous fun z : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) := hK.mul (hG.sub continuous_const)
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmass : ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) ∂flatTorusMeasure d = 1 := by
    rw [integral_sub_left_eq_self (heatTorus d (2 * Real.pi ^ 2 * σ)) (flatTorusMeasure d) X0]
    exact heatTorus_mass hcσ d
  have hfirst : ∫ y, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y)
      * heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) ∂flatTorusMeasure d = c :=
    torus_first_moment hσ hs d x w
  -- transfer of integrals to the law
  have htr : ∀ (j : ℕ) (f : FlatTorus d → ℝ), Continuous f →
      ∫ ω, f (X j ω) ∂μ = ∫ z, f z ∂flatTorusMeasure d := fun j f hf => by
    rw [← hlaw j, integral_map (hX j).aemeasurable hf.measurable.aestronglyMeasurable]
  refine bernstein_two_sided_fn (μ := μ) X h_indep hX
    (fun z => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) hYc.measurable T hBb hY
    (fun j _ => ?_) (fun j _ => ?_) hε
  · -- mean zero
    rw [htr j _ hYc]
    have e : ∀ z : FlatTorus d, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)
        = heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) * heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)
          - c * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) := fun z => by ring
    simp_rw [e]
    have I1 : Integrable (fun z : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * heatTorus d (2 * Real.pi ^ 2 * s) (z - W0)) (flatTorusMeasure d) := hint _ (hK.mul hG)
    have I2 : Integrable (fun z : FlatTorus d => c * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))
        (flatTorusMeasure d) := (hint _ hK).const_mul _
    rw [integral_sub I1 I2, integral_const_mul, hfirst, hmass]
    ring
  · -- variance
    rw [htr j (fun z => (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) ^ 2) (hYc.pow 2)]
    have hle : ∫ z, (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) ^ 2 ∂flatTorusMeasure d
        ≤ ∫ z, Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2) ∂flatTorusMeasure d := by
      refine integral_mono (hint _ (hYc.pow 2))
        ((hint _ (hK.mul ((hG.sub continuous_const).pow 2))).const_mul _) (fun z => ?_)
      have h0 := heatTorus_nonneg hcσ d (X0 - z)
      have h1 := hMσ (X0 - z)
      have h2 : 0 ≤ (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2 := _root_.sq_nonneg _
      show (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
            * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c)) ^ 2
          ≤ Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
            * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2)
      rw [mul_pow, _root_.sq (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))]
      nlinarith [mul_nonneg h0 h2, mul_le_mul_of_nonneg_right h1 (mul_nonneg h0 h2)]
    have hM0 : 0 ≤ Mσ := (heatTorus_nonneg hcσ d 0).trans (hMσ 0)
    have hvar := torus_variance_w3 hσ hs hσs d x w
    rw [torus_first_moment hσ hs d x w] at hvar
    refine hle.trans ?_
    rw [integral_const_mul, torus_centered_second hσ hs d x w]
    exact mul_le_mul_of_nonneg_left hvar hM0


/-- The Bernstein step at arbitrary fixed points of the torus, with the bound `B` from (P4). -/
theorem heat_consistency_fixed_all3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : FlatTorus d) (T : Finset ℕ)
    {Mσ ε : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T, heatY d σ s x w (X j ω)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * (Mσ * heatV3 d σ s (x - w)))
          + 2 * heatB d σ s Mσ (x - w) * ε)) := by
  obtain ⟨tx, rfl⟩ := flatTorus_lift d x
  obtain ⟨tw, rfl⟩ := flatTorus_lift d w
  have hM : 0 < Mσ :=
    lt_of_lt_of_le (heatTorus_pos (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * σ) d 0) (hMσ 0)
  exact heat_consistency_fixed3 hσ hs hσs d X h_indep hX hlaw tx tw T
    (heatB_pos hσ hs hM d _) (fun z => heat_Y_bound hσ hs d _ _ z hMσ) hMσ hε

/-- **Weighted consistency at a pair of sample points (estimate (ii) of the consistency lemma for
    one pair and one index set, without the exceptional terms).** Independent uniform points on
    the flat torus, indices `b, i` outside the finite index set `T`, `0 < σ ≤ s`, `p_σ ≤ Mσ`,
    `L > 0`. With the threshold
    `θ(x, w) = 2 B(x - w) L + 2 √(|T| Mσ V(x - w) L)`,
    where `V` carries the factor `σ/s` and the weight `p_{3s}` and `B` is the bound from (P4),
    `P(θ(X_b, X_i) ≤ |∑_{j ∈ T} Y(X_b, X_i, X_j)|) ≤ 2 e^{-L}`. -/
theorem heat_consistency_pair3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (b i : ℕ) (T : Finset ℕ)
    (hbT : b ∉ T) (hiT : i ∉ T) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | 2 * heatB d σ s Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (T.card * (Mσ * heatV3 d σ s (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ T, heatY d σ s (X b ω) (X i ω) (X j ω)|}
      ≤ 2 * Real.exp (-L) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  have hcτ : 0 < 2 * Real.pi ^ 2 * (σ + s) := by positivity
  have hc3 : 0 < 2 * Real.pi ^ 2 * (3 * s) := by positivity
  have hc2 : 0 < 2 * Real.pi ^ 2 * (s + 2 * σ) := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  have hYc : Continuous fun p : FlatTorus d × FlatTorus d × FlatTorus d =>
      heatY d σ s p.1 p.2.1 p.2.2 := by
    unfold heatY
    exact ((heatTorus_continuous hcσ d).comp (continuous_fst.sub (continuous_snd.comp continuous_snd))).mul
      (((heatTorus_continuous hcs d).comp
          ((continuous_snd.comp continuous_snd).sub (continuous_fst.comp continuous_snd))).sub
        ((heatTorus_continuous hcτ d).comp (continuous_fst.sub (continuous_fst.comp continuous_snd))))
  have hVc : Continuous fun u : FlatTorus d => heatV3 d σ s u := by
    unfold heatV3
    exact continuous_const.mul (heatTorus_continuous hc3 d)
  have hBc : Continuous fun u : FlatTorus d => heatB d σ s Mσ u := by
    unfold heatB
    exact ((continuous_const.mul (heatTorus_continuous hc2 d)).div_const _).add
      (continuous_const.mul (heatTorus_continuous hcτ d))
  have hsub : Continuous fun p : FlatTorus d × FlatTorus d => p.1 - p.2 :=
    continuous_fst.sub continuous_snd
  have hthr : Continuous fun p : FlatTorus d × FlatTorus d =>
      2 * heatB d σ s Mσ (p.1 - p.2) * L
        + 2 * Real.sqrt (T.card * (Mσ * heatV3 d σ s (p.1 - p.2)) * L) :=
    ((continuous_const.mul (hBc.comp hsub)).mul continuous_const).add
      (continuous_const.mul (Real.continuous_sqrt.comp
        ((continuous_const.mul (continuous_const.mul (hVc.comp hsub))).mul continuous_const)))
  refine cond_pair_bound (μ := μ) X h_indep hX b i T hbT hiT (heatY d σ s) hYc.measurable
    (fun x w => 2 * heatB d σ s Mσ (x - w) * L
      + 2 * Real.sqrt (T.card * (Mσ * heatV3 d σ s (x - w)) * L)) hthr.measurable
    (by positivity) (fun x w => ?_)
  have hA : 0 ≤ (T.card : ℝ) * (Mσ * heatV3 d σ s (x - w)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hM.le (heatV3_nonneg hσ hs d _))
  obtain ⟨hε, hexp⟩ := bern_threshold (heatB_pos hσ hs hM d (x - w)) hA hL
  have h := heat_consistency_fixed_all3 hσ hs hσs d X h_indep hX hlaw x w T hMσ hε
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left hexp (by norm_num)


/-- **Weighted consistency simultaneously for all pairs of sample points.** Independent uniform
    points on the flat torus, `0 < σ ≤ s`, `p_σ ≤ Mσ`, `L > 0`. With probability at least
    `1 - 2 N² e^{-L}`, for all `b, i < N`, the sum of `Y(X_b, X_i, X_j)` over the other indices
    `j < N`, `j ∉ {b, i}`, is smaller in absolute value than
    `2 B(X_b - X_i) L + 2 √(N Mσ V(X_b - X_i) L)`. -/
theorem heat_consistency_all_pairs3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ s Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV3 d σ s (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ s (X b ω) (X i ω) (X j ω)|}
      ≤ (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  set E : ℕ × ℕ → Set Ω := fun p => {ω |
      2 * heatB d σ s Mσ (X p.1 ω - X p.2 ω) * L
        + 2 * Real.sqrt ((((Finset.range N).erase p.1).erase p.2).card
            * (Mσ * heatV3 d σ s (X p.1 ω - X p.2 ω)) * L)
      ≤ |∑ j ∈ ((Finset.range N).erase p.1).erase p.2,
          heatY d σ s (X p.1 ω) (X p.2 ω) (X j ω)|} with hE
  have hsub : {ω | ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ s Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV3 d σ s (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ s (X b ω) (X i ω) (X j ω)|}
      ⊆ ⋃ p ∈ Finset.range N ×ˢ Finset.range N, E p := by
    rintro ω ⟨b, hb, i, hi, h⟩
    simp only [Set.mem_iUnion, Finset.mem_product]
    refine ⟨(b, i), ⟨hb, hi⟩, ?_⟩
    simp only [hE, Set.mem_setOf_eq]
    refine le_trans ?_ h
    have hcard : ((((Finset.range N).erase b).erase i).card : ℝ) ≤ N := by
      have h1 := Finset.card_erase_le (s := (Finset.range N).erase b) (a := i)
      have h2 := Finset.card_erase_le (s := Finset.range N) (a := b)
      rw [Finset.card_range] at h2
      exact_mod_cast h1.trans h2
    have hV := heatV3_nonneg hσ hs d (X b ω - X i ω)
    have hmono : ((((Finset.range N).erase b).erase i).card : ℝ)
          * (Mσ * heatV3 d σ s (X b ω - X i ω)) * L
        ≤ N * (Mσ * heatV3 d σ s (X b ω - X i ω)) * L :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (mul_nonneg hM.le hV)) hL.le
    linarith [Real.sqrt_le_sqrt hmono]
  have hone : ∀ p ∈ Finset.range N ×ˢ Finset.range N, μ.real (E p) ≤ 2 * Real.exp (-L) := by
    intro p _
    exact heat_consistency_pair3 hσ hs hσs d X h_indep hX hlaw p.1 p.2
      (((Finset.range N).erase p.1).erase p.2)
      (fun h => Finset.notMem_erase p.1 _ (Finset.mem_of_mem_erase h))
      (Finset.notMem_erase p.2 _) hMσ hL
  calc μ.real _ ≤ μ.real (⋃ p ∈ Finset.range N ×ˢ Finset.range N, E p) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, μ.real (E p) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ Finset.range N ×ˢ Finset.range N, 2 * Real.exp (-L) := Finset.sum_le_sum hone
    _ = (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_range, nsmul_eq_mul]
        push_cast; ring


/-- **Weighted consistency simultaneously for all pairs of sample points and all numbers of steps
    `1 ≤ m ≤ K`.** Kernel time `σ`, times `s = m σ`. With probability at least
    `1 - 2 K N² e^{-L}`, for all `1 ≤ m ≤ K` and all `b, i < N`, the sum of
    `Y_m(X_b, X_i, X_j)` over `j < N`, `j ∉ {b, i}`, is smaller in absolute value than
    `2 B_m(X_b - X_i) L + 2 √(N Mσ V_m(X_b - X_i) L)`. -/
theorem heat_consistency_all_steps3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV3 d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
  set E : ℕ → Set Ω := fun m => {ω | ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV3 d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} with hE
  have hsub : {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
          + 2 * Real.sqrt (N * (Mσ * heatV3 d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ⊆ ⋃ m ∈ Finset.Icc 1 K, E m := by
    rintro ω ⟨m, hm, h⟩
    simp only [Set.mem_iUnion]
    exact ⟨m, hm, h⟩
  have hone : ∀ m ∈ Finset.Icc 1 K, μ.real (E m) ≤ (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := by
    intro m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hs : 0 < (m : ℝ) * σ := by positivity
    have hσs : σ ≤ (m : ℝ) * σ := by nlinarith
    exact heat_consistency_all_pairs3 hσ hs hσs d X h_indep hX hlaw N hMσ hL
  calc μ.real _ ≤ μ.real (⋃ m ∈ Finset.Icc 1 K, E m) :=
        measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ m ∈ Finset.Icc 1 K, μ.real (E m) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 K, (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := Finset.sum_le_sum hone
    _ = (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp


/-- **Second moment of the summand `Y` under the uniform law:**
    `∫ Y(x, w, z)² dz ≤ Mσ V(x - w)`. -/
theorem heatY_sq_integral_le3 {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : FlatTorus d) {Mσ : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) :
    ∫ z, heatY d σ s x w z ^ 2 ∂flatTorusMeasure d ≤ Mσ * heatV3 d σ s (x - w) := by
  obtain ⟨tx, rfl⟩ := flatTorus_lift d x
  obtain ⟨tw, rfl⟩ := flatTorus_lift d w
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  set X0 : FlatTorus d := fun i => ((tx i : ℝ) : UnitAddCircle) with hX0
  set W0 : FlatTorus d := fun i => ((tw i : ℝ) : UnitAddCircle) with hW0
  set c : ℝ := heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) with hc
  have hK : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) :=
    (heatTorus_continuous hcσ d).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) :=
    (heatTorus_continuous hcs d).comp (continuous_id.sub continuous_const)
  have hYc := heatY_continuous hσ hs d X0 W0
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hle : ∫ z, heatY d σ s X0 W0 z ^ 2 ∂flatTorusMeasure d
      ≤ ∫ z, Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2) ∂flatTorusMeasure d := by
    refine integral_mono (hint _ (hYc.pow 2))
      ((hint _ (hK.mul ((hG.sub continuous_const).pow 2))).const_mul _) (fun z => ?_)
    have h0 := heatTorus_nonneg hcσ d (X0 - z)
    have h1 := hMσ (X0 - z)
    have h2 : 0 ≤ (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2 := _root_.sq_nonneg _
    show heatY d σ s X0 W0 z ^ 2
        ≤ Mσ * (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2)
    unfold heatY
    rw [mul_pow, _root_.sq (heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))]
    nlinarith [mul_nonneg h0 h2, mul_le_mul_of_nonneg_right h1 (mul_nonneg h0 h2)]
  have hM0 : 0 ≤ Mσ := (heatTorus_nonneg hcσ d 0).trans (hMσ 0)
  have hvar := torus_variance_w3 hσ hs hσs d tx tw
  rw [torus_first_moment hσ hs d tx tw] at hvar
  refine hle.trans ?_
  rw [integral_const_mul, torus_centered_second hσ hs d tx tw]
  unfold heatV3
  exact mul_le_mul_of_nonneg_left hvar hM0

/-- **First absolute moment of `Y`, sharp form:** `∫ |Y(x, w, z)| dz ≤ √(V(x - w))`, without the
    factor `Mσ` (Cauchy–Schwarz with respect to the probability density `p_σ(x - ·)`). -/
theorem heatY_abs_integral_sharp3 {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (x w : FlatTorus d) :
    ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d ≤ Real.sqrt (heatV3 d σ s (x - w)) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  obtain ⟨tx, rfl⟩ := flatTorus_lift d x
  obtain ⟨tw, rfl⟩ := flatTorus_lift d w
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hcs : 0 < 2 * Real.pi ^ 2 * s := by positivity
  set X0 : FlatTorus d := fun i => ((tx i : ℝ) : UnitAddCircle) with hX0
  set W0 : FlatTorus d := fun i => ((tw i : ℝ) : UnitAddCircle) with hW0
  set c : ℝ := heatTorus d (2 * Real.pi ^ 2 * (σ + s)) (X0 - W0) with hc
  have hK : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - y) :=
    (heatTorus_continuous hcσ d).comp (continuous_const.sub continuous_id)
  have hG : Continuous fun y : FlatTorus d => heatTorus d (2 * Real.pi ^ 2 * s) (y - W0) :=
    (heatTorus_continuous hcs d).comp (continuous_id.sub continuous_const)
  have hYc := heatY_continuous hσ hs d X0 W0
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = ∫ z, |heatY d σ s X0 W0 z| ∂flatTorusMeasure d := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; exact integral_nonneg fun z => abs_nonneg _
  have hYabs : ∀ z, |heatY d σ s X0 W0 z|
      = heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * |heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c| := fun z => by
    unfold heatY
    rw [abs_mul, abs_of_nonneg (heatTorus_nonneg hcσ d _)]
  have hnn : 0 ≤ ∫ z, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (|heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c| - e) ^ 2 ∂flatTorusMeasure d :=
    integral_nonneg fun z => mul_nonneg (heatTorus_nonneg hcσ d _) (_root_.sq_nonneg _)
  have hexp : ∀ z, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
        * (|heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c| - e) ^ 2
      = heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
          * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2
        - 2 * e * |heatY d σ s X0 W0 z|
        + e ^ 2 * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) := fun z => by
    rw [hYabs z, sub_sq, sq_abs]; ring
  simp_rw [hexp] at hnn
  have I1 : Integrable (fun z => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2) (flatTorusMeasure d) :=
    hint _ (hK.mul ((hG.sub continuous_const).pow 2))
  have I2 : Integrable (fun z => 2 * e * |heatY d σ s X0 W0 z|) (flatTorusMeasure d) :=
    (hint _ hYc.abs).const_mul _
  have I3 : Integrable (fun z => e ^ 2 * heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z))
      (flatTorusMeasure d) := (hint _ hK).const_mul _
  have hmass : ∫ z, heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z) ∂flatTorusMeasure d = 1 := by
    rw [integral_sub_left_eq_self (heatTorus d (2 * Real.pi ^ 2 * σ)) (flatTorusMeasure d) X0,
      heatTorus_mass hcσ d]
  have I12 : Integrable (fun z => heatTorus d (2 * Real.pi ^ 2 * σ) (X0 - z)
      * (heatTorus d (2 * Real.pi ^ 2 * s) (z - W0) - c) ^ 2 - 2 * e * |heatY d σ s X0 W0 z|)
      (flatTorusMeasure d) := I1.sub I2
  rw [integral_add I12 I3, integral_sub I1 I2, integral_const_mul, integral_const_mul,
    hmass, torus_centered_second hσ hs d tx tw, ← he] at hnn
  have hvar := torus_variance_w3 hσ hs hσs d tx tw
  rw [torus_first_moment hσ hs d tx tw] at hvar
  have hsq : e ^ 2 ≤ heatV3 d σ s (X0 - W0) := by
    unfold heatV3
    nlinarith
  rw [← he]
  calc e = Real.sqrt (e ^ 2) := (Real.sqrt_sq he0).symm
    _ ≤ Real.sqrt (heatV3 d σ s (X0 - W0)) := Real.sqrt_le_sqrt hsq

/-- **Bernstein step for `|Y| - E|Y|` at fixed points.** With `e = ∫ |Y(x, w, z)| dz`,
    `P(|∑_{j ∈ T} (|Y(x, w, X_j)| - e)| ≥ eps) ≤ 2 exp(-eps² / (4 |T| Mσ V + 2 B eps))`. -/
theorem heat_abs_consistency_fixed_all3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : FlatTorus d) (T : Finset ℕ)
    {Mσ ε : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ |∑ j ∈ T, (|heatY d σ s x w (X j ω)|
        - ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d)|}
      ≤ 2 * Real.exp (-ε ^ 2 / (4 * (T.card * (Mσ * heatV3 d σ s (x - w)))
          + 2 * heatB d σ s Mσ (x - w) * ε)) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  have hYc := heatY_continuous hσ hs d x w
  have hint : ∀ f : FlatTorus d → ℝ, Continuous f → Integrable f (flatTorusMeasure d) := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set e : ℝ := ∫ z, |heatY d σ s x w z| ∂flatTorusMeasure d with he
  have he0 : 0 ≤ e := integral_nonneg fun z => abs_nonneg _
  have hB := heatB_pos hσ hs hM d (x - w)
  have hYB : ∀ z, |heatY d σ s x w z| ≤ heatB d σ s Mσ (x - w) :=
    fun z => heatY_abs_le hσ hs d x w z hMσ
  have heB : e ≤ heatB d σ s Mσ (x - w) := by
    have h := integral_mono (hint _ hYc.abs) (integrable_const (heatB d σ s Mσ (x - w))) hYB
    simpa using h
  have hfc : Continuous fun z : FlatTorus d => |heatY d σ s x w z| - e :=
    hYc.abs.sub continuous_const
  have htr : ∀ (j : ℕ) (f : FlatTorus d → ℝ), Continuous f →
      ∫ ω, f (X j ω) ∂μ = ∫ z, f z ∂flatTorusMeasure d := fun j f hf => by
    rw [← hlaw j, integral_map (hX j).aemeasurable hf.measurable.aestronglyMeasurable]
  refine bernstein_two_sided_fn (μ := μ) X h_indep hX
    (fun z => |heatY d σ s x w z| - e) hfc.measurable T hB (fun z => ?_)
    (fun j _ => ?_) (fun j _ => ?_) hε
  · rw [abs_le]
    constructor <;> linarith [hYB z, abs_nonneg (heatY d σ s x w z)]
  · rw [htr j _ hfc, integral_sub (hint _ hYc.abs) (integrable_const _), integral_const]
    simp [he]
  · rw [htr j (fun z => (|heatY d σ s x w z| - e) ^ 2) (hfc.pow 2)]
    have hexp : ∀ z, (|heatY d σ s x w z| - e) ^ 2
        = heatY d σ s x w z ^ 2 - 2 * e * |heatY d σ s x w z| + e ^ 2 := fun z => by
      rw [sub_sq, sq_abs]; ring
    simp_rw [hexp]
    have I1 : Integrable (fun z => heatY d σ s x w z ^ 2) (flatTorusMeasure d) := hint _ (hYc.pow 2)
    have I2 : Integrable (fun z => 2 * e * |heatY d σ s x w z|) (flatTorusMeasure d) :=
      (hint _ hYc.abs).const_mul _
    have I12 : Integrable (fun z => heatY d σ s x w z ^ 2 - 2 * e * |heatY d σ s x w z|)
        (flatTorusMeasure d) := I1.sub I2
    rw [integral_add I12 (integrable_const _), integral_sub I1 I2, integral_const_mul,
      integral_const]
    simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
    have h2 := heatY_sq_integral_le3 hσ hs hσs d x w hMσ
    nlinarith [_root_.sq_nonneg e]


/-- The threshold of the weighted consistency estimates. -/
noncomputable def heatThr3 (d : ℕ) (σ s Mσ L A : ℝ) (u : FlatTorus d) : ℝ :=
  2 * heatB d σ s Mσ u * L + 2 * Real.sqrt (A * (Mσ * heatV3 d σ s u) * L)

/-- Continuity of the threshold in the two points. -/
theorem heatThr_continuous3 {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (d : ℕ) (Mσ L A : ℝ) :
    Continuous fun p : FlatTorus d × FlatTorus d => heatThr3 d σ s Mσ L A (p.1 - p.2) := by
  have hVc : Continuous fun u : FlatTorus d => heatV3 d σ s u := by
    unfold heatV3
    exact continuous_const.mul (heatTorus_continuous (by positivity) d)
  have hBc : Continuous fun u : FlatTorus d => heatB d σ s Mσ u := by
    unfold heatB
    exact ((continuous_const.mul (heatTorus_continuous (by positivity) d)).div_const _).add
      (continuous_const.mul (heatTorus_continuous (by positivity) d))
  have hsub : Continuous fun p : FlatTorus d × FlatTorus d => p.1 - p.2 :=
    continuous_fst.sub continuous_snd
  unfold heatThr3
  exact ((continuous_const.mul (hBc.comp hsub)).mul continuous_const).add
    (continuous_const.mul (Real.continuous_sqrt.comp
      ((continuous_const.mul (continuous_const.mul (hVc.comp hsub))).mul continuous_const)))

/-- The Bernstein step for the centred absolute summand at fixed points, with the threshold. -/
theorem heatYc_fixed3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (x w : FlatTorus d) (T : Finset ℕ)
    {Mσ L : ℝ} (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | heatThr3 d σ s Mσ L T.card (x - w) ≤ |∑ j ∈ T, heatYc d σ s x w (X j ω)|}
      ≤ 2 * Real.exp (-L) := by
  have hM : 0 < Mσ :=
    lt_of_lt_of_le (heatTorus_pos (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * σ) d 0) (hMσ 0)
  have hA : 0 ≤ (T.card : ℝ) * (Mσ * heatV3 d σ s (x - w)) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hM.le (heatV3_nonneg hσ hs d _))
  obtain ⟨hε, hexp⟩ := bern_threshold (heatB_pos hσ hs hM d (x - w)) hA hL
  have h := heat_abs_consistency_fixed_all3 hσ hs hσs d X h_indep hX hlaw x w T hMσ hε
  unfold heatThr3 heatYc
  simp only [heatYmean_eq]
  exact h.trans (mul_le_mul_of_nonneg_left hexp (by norm_num))

/-- **Weighted bound for the absolute summand at a pair of sample points.** As
    `heat_consistency_pair3`, for the centred absolute summand `|Y| - E|Y|`. -/
theorem heat_abs_consistency_pair3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ s : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hσs : σ ≤ s) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (b i : ℕ) (T : Finset ℕ)
    (hbT : b ∉ T) (hiT : i ∉ T) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | heatThr3 d σ s Mσ L T.card (X b ω - X i ω)
        ≤ |∑ j ∈ T, heatYc d σ s (X b ω) (X i ω) (X j ω)|}
      ≤ 2 * Real.exp (-L) :=
  cond_pair_bound (μ := μ) X h_indep hX b i T hbT hiT (heatYc d σ s)
    (heatYc_joint_continuous hσ hs d).measurable
    (fun x w => heatThr3 d σ s Mσ L T.card (x - w))
    (heatThr_continuous3 hσ hs d Mσ L T.card).measurable (by positivity)
    (fun x w => heatYc_fixed3 hσ hs hσs d X h_indep hX hlaw x w T hMσ hL)


/-- The threshold is monotone in the size parameter. -/
theorem heatThr_mono3 {σ s Mσ L A A' : ℝ} (hσ : 0 < σ) (hs : 0 < s) (hM : 0 ≤ Mσ) (hL : 0 ≤ L)
    (hAA : A ≤ A') (d : ℕ) (u : FlatTorus d) :
    heatThr3 d σ s Mσ L A u ≤ heatThr3 d σ s Mσ L A' u := by
  unfold heatThr3
  have hV := heatV3_nonneg hσ hs d u
  have h : A * (Mσ * heatV3 d σ s u) * L ≤ A' * (Mσ * heatV3 d σ s u) * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA (mul_nonneg hM hV)) hL
  linarith [Real.sqrt_le_sqrt h]

/-- **The centred absolute summand, simultaneously for all pairs of sample points and all numbers
    of steps `1 ≤ m ≤ K`.** With probability at least `1 - 2 K N² e^{-L}`, for all `1 ≤ m ≤ K` and
    `b, i < N`, the sum of `|Y_m(X_b, X_i, X_j)| - E|Y_m|` over `j < N`, `j ∉ {b, i}`, is smaller in
    absolute value than the threshold `2 B_m L + 2 √(N Mσ V_m L)` at `X_b - X_i`. -/
theorem heat_abs_consistency_all_steps3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) {Mσ L : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatThr3 d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  set I : Finset (ℕ × ℕ × ℕ) := Finset.Icc 1 K ×ˢ (Finset.range N ×ˢ Finset.range N) with hI
  set E : ℕ × ℕ × ℕ → Set Ω := fun q => {ω |
      heatThr3 d σ ((q.1 : ℝ) * σ) Mσ L
          ((((Finset.range N).erase q.2.1).erase q.2.2).card : ℝ) (X q.2.1 ω - X q.2.2 ω)
        ≤ |∑ j ∈ ((Finset.range N).erase q.2.1).erase q.2.2,
            heatYc d σ ((q.1 : ℝ) * σ) (X q.2.1 ω) (X q.2.2 ω) (X j ω)|} with hE
  have hsub : {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatThr3 d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω)
        ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
            heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|}
      ⊆ ⋃ q ∈ I, E q := by
    rintro ω ⟨m, hm, b, hb, i, hi, h⟩
    simp only [Set.mem_iUnion]
    refine ⟨(m, b, i), by simp [hI, Finset.mem_product, hm, hb, hi], ?_⟩
    simp only [hE, Set.mem_setOf_eq]
    refine le_trans ?_ h
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hcard : ((((Finset.range N).erase b).erase i).card : ℝ) ≤ N := by
      have h1 := Finset.card_erase_le (s := (Finset.range N).erase b) (a := i)
      have h2 := Finset.card_erase_le (s := Finset.range N) (a := b)
      rw [Finset.card_range] at h2
      exact_mod_cast h1.trans h2
    exact heatThr_mono3 hσ (by positivity) hM.le hL.le hcard d _
  have hone : ∀ q ∈ I, μ.real (E q) ≤ 2 * Real.exp (-L) := by
    intro q hq
    have hm := (Finset.mem_product.mp hq).1
    have hm1 : (1 : ℝ) ≤ q.1 := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hs : 0 < (q.1 : ℝ) * σ := by positivity
    have hσs : σ ≤ (q.1 : ℝ) * σ := by nlinarith
    exact heat_abs_consistency_pair3 hσ hs hσs d X h_indep hX hlaw q.2.1 q.2.2
      (((Finset.range N).erase q.2.1).erase q.2.2)
      (fun h => Finset.notMem_erase q.2.1 _ (Finset.mem_of_mem_erase h))
      (Finset.notMem_erase q.2.2 _) hMσ hL
  calc μ.real _ ≤ μ.real (⋃ q ∈ I, E q) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ q ∈ I, μ.real (E q) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ I, 2 * Real.exp (-L) := Finset.sum_le_sum hone
    _ = (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) := by
        rw [Finset.sum_const, hI, Finset.card_product, Finset.card_product, Nat.card_Icc,
          Finset.card_range, nsmul_eq_mul]
        push_cast
        ring


/-- The bound for the defect on the good event, as a function of `u = x_b - x_i`. -/
noncomputable def heatDefBound3 (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ : ℝ) (u : FlatTorus d) : ℝ :=
  ((heatThr3 d σ ((m : ℝ) * σ) Mσ L N u + 2 * heatB d σ ((m : ℝ) * σ) Mσ u)
      + 2 * δ * (N * Real.sqrt (heatV3 d σ ((m : ℝ) * σ) u)
          + heatThr3 d σ ((m : ℝ) * σ) Mσ L N u + 2 * heatB d σ ((m : ℝ) * σ) Mσ u))
    / (N * (1 / 3))

/-- **The defect of the sampled walk on the good event (deterministic).** Points `x_0, …, x_{N-1}`
    of the flat torus, `m ≥ 1`. If the estimated normalisations are within `δ ≤ 1/2` of one and the
    two Bernstein bounds hold for the pair `(b, i)`, then
    `|h_m^{(i)}(b)| ≤ heatDefBound3(x_b - x_i)`. -/
theorem heat_defect_det3 {σ : ℝ} (hσ : 0 < σ) (d N m : ℕ) (hN : 0 < N) (hm : 1 ≤ m)
    (x : ℕ → FlatTorus d) (b i : ℕ) (hb : b ∈ Finset.range N) {Mσ L δ : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hρ : ∀ j, |heatRho d σ N x j - 1| ≤ δ)
    (H1 : |∑ j ∈ ((Finset.range N).erase b).erase i, heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
      ≤ heatThr3 d σ ((m : ℝ) * σ) Mσ L N (x b - x i))
    (H2 : |∑ j ∈ ((Finset.range N).erase b).erase i, heatYc d σ ((m : ℝ) * σ) (x b) (x i) (x j)|
      ≤ heatThr3 d σ ((m : ℝ) * σ) Mσ L N (x b - x i)) :
    |heatDefect d σ N m x b i| ≤ heatDefBound3 d σ N m Mσ L δ (x b - x i) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hσs : σ ≤ (m : ℝ) * σ := by nlinarith
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : 0 < Mσ := lt_of_lt_of_le (heatTorus_pos hcσ d 0) (hMσ 0)
  have hinv := fun j => inv_near_one hδ0 hδ (hρ j)
  have hPt : ∀ j, 0 ≤ heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / N :=
    fun j => div_nonneg (heatTorus_nonneg hcσ d _) hNpos.le
  -- lower bound for the row normalisation
  have hr : (1 : ℝ) / 3 ≤ ∑ l ∈ Finset.range N,
      (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (1 / heatRho d σ N x l) := by
    have h1 : ∑ l ∈ Finset.range N, (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (2 / 3)
        ≤ ∑ l ∈ Finset.range N,
          (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (1 / heatRho d σ N x l) :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hinv l).2 (hPt l)
    have h2 : ∑ l ∈ Finset.range N, (heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) / N) * (2 / 3)
        = heatRho d σ N x b * (2 / 3) := by
      unfold heatRho
      rw [← Finset.sum_mul, Finset.sum_div]
    have h3 := abs_le.mp (hρ b)
    nlinarith [h3.1]
  have hB := fun z => heatY_abs_le hσ hs d (x b) (x i) z hMσ
  have he := heatY_abs_integral_sharp3 hσ hs hσs d (x b) (x i)
  have he0 : 0 ≤ heatYmean d σ ((m : ℝ) * σ) (x b) (x i) := by
    rw [heatYmean_eq]; exact integral_nonneg fun z => abs_nonneg _
  have H2' : |∑ j ∈ ((Finset.range N).erase b).erase i,
      (|heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j)| - heatYmean d σ ((m : ℝ) * σ) (x b) (x i))|
      ≤ heatThr3 d σ ((m : ℝ) * σ) Mσ L N (x b - x i) := H2
  have key := defect_from_bounds N hN
    (fun j => heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x j) / N)
    (fun j => 1 / heatRho d σ N x j)
    (fun j => heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ)) (x j - x i))
    (fun j => heatY d σ ((m : ℝ) * σ) (x b) (x i) (x j))
    (heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) (x b - x i)) (2 * δ) (1 / 3)
    (heatThr3 d σ ((m : ℝ) * σ) Mσ L N (x b - x i)) (heatB d σ ((m : ℝ) * σ) Mσ (x b - x i))
    (heatYmean d σ ((m : ℝ) * σ) (x b) (x i))
    hPt (fun j => (hinv j).1) (by positivity) (by norm_num) hr
    (fun j => by unfold heatY; field_simp) b i he0 H1 H2' (hB _) (hB _)
  have hthr0 : 0 ≤ heatThr3 d σ ((m : ℝ) * σ) Mσ L N (x b - x i) := (abs_nonneg _).trans H1
  have hB0 : 0 ≤ heatB d σ ((m : ℝ) * σ) Mσ (x b - x i) :=
    (heatB_pos hσ hs hM d _).le
  rw [heatYmean_eq] at he0
  unfold heatDefect heatDefBound3
  refine key.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hmono : (N : ℝ) * heatYmean d σ ((m : ℝ) * σ) (x b) (x i)
      ≤ N * Real.sqrt (heatV3 d σ ((m : ℝ) * σ) (x b - x i)) := by
    rw [heatYmean_eq]; exact mul_le_mul_of_nonneg_left he hNpos.le
  nlinarith [mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 2 * δ)]


/-- **The one-step defect of the sampled walk on the torus, with its probability (estimate (ii) of
    the consistency lemma with explicit, time-dependent constants).** Independent uniform points
    on the flat torus; kernel time `σ`, `p_σ ≤ Mσ`, `L > 0`, `N > 0`. HYPOTHESIS `hBn`: the
    probability `pn` of the normalisation event (a conclusion of
    `uniform_concentration_bernstein`), with `epsn ≤ N/2`. Then, except on an event of probability
    at most `pn + 4 K N² e^{-L}`, for all `1 ≤ m ≤ K` and all `b, i < N`,
    `|h_m^{(i)}(b)| ≤ heatDefBound3(X_b - X_i)` with `δ = epsn/N`. -/
theorem heat_defect_whp3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {Mσ L epsn pn : ℝ}
    (hMσ : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ Mσ) (hL : 0 < L)
    (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 2)
    (hBn : μ.real {ω | ∃ x : FlatTorus d,
        epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} ≤ pn) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatDefBound3 d σ N m Mσ L (epsn / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|}
      ≤ pn + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  set Bn : Set Ω := {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|} with hBnd
  set E1 : Set Ω := {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
      2 * heatB d σ ((m : ℝ) * σ) Mσ (X b ω - X i ω) * L
        + 2 * Real.sqrt (N * (Mσ * heatV3 d σ ((m : ℝ) * σ) (X b ω - X i ω)) * L)
      ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} with hE1
  set E2 : Set Ω := {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
      heatThr3 d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω)
      ≤ |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|} with hE2
  have hP1 : μ.real E1 ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) :=
    heat_consistency_all_steps3 hσ d X h_indep hX hlaw N K hMσ hL
  have hP2 : μ.real E2 ≤ (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) :=
    heat_abs_consistency_all_steps3 hσ d X h_indep hX hlaw N K hMσ hL
  have hsub : {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatDefBound3 d σ N m Mσ L (epsn / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|}
      ⊆ Bn ∪ (E1 ∪ E2) := by
    rintro ω ⟨m, hm, b, hb, i, hi, hbad⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨hn, h1, h2⟩ := hcon
    have hρ : ∀ j, |heatRho d σ N (fun j => X j ω) j - 1| ≤ epsn / N := by
      intro j
      have h : |∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N|
          ≤ epsn := by
        by_contra h; exact hn ⟨X j ω, not_le.mp h⟩
      have e : heatRho d σ N (fun j => X j ω) j - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le
    have H1 : |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatY d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|
        ≤ heatThr3 d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω) := by
      by_contra h
      exact h1 ⟨m, hm, b, hb, i, hi, (not_le.mp h).le⟩
    have H2 : |∑ j ∈ ((Finset.range N).erase b).erase i,
          heatYc d σ ((m : ℝ) * σ) (X b ω) (X i ω) (X j ω)|
        ≤ heatThr3 d σ ((m : ℝ) * σ) Mσ L N (X b ω - X i ω) := by
      by_contra h
      exact h2 ⟨m, hm, b, hb, i, hi, (not_le.mp h).le⟩
    have hdet := heat_defect_det3 hσ d N m hN (Finset.mem_Icc.mp hm).1 (fun j => X j ω) b i hb hMσ hL
      (div_nonneg hepsn0 hNpos.le) (by rw [div_le_iff₀ hNpos]; linarith) hρ H1 H2
    exact absurd hbad (not_lt.mpr hdet)
  calc μ.real _ ≤ μ.real (Bn ∪ (E1 ∪ E2)) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ μ.real Bn + μ.real (E1 ∪ E2) := measureReal_union_le _ _
    _ ≤ μ.real Bn + (μ.real E1 + μ.real E2) := by
        have := measureReal_union_le (μ := μ) E1 E2
        linarith
    _ ≤ _ := by linarith


/-- **Estimate (ii) of the consistency lemma for random samples on the torus, with explicit
    time-dependent constants and no hypothesis beyond those on the sample.** With
    `M = (1 + √(π/c_σ))^d`, the Lipschitz constant `Lip` of the kernel and a grid parameter `g`:
    except on an event of probability at most
    `2 g^d exp(-eps²/(4NM + 2M eps)) + 4 K N² e^{-L}`, for all `1 ≤ m ≤ K` and `b, i < N`,
    `|h_m^{(i)}(b)| ≤ heatDefBound3(X_b - X_i)` with `δ = (eps + 2 N Lip / g)/N`. -/
theorem heat_defect_sample3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN : 0 < N) {g : ℕ} (hg : 0 < g)
    {M Lip L ε : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hL : 0 < L) (hε : 0 < ε) (hsmall : ε + 2 * (N * Lip) * (1 / g) ≤ N / 2) :
    μ.real {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N, ∃ i ∈ Finset.range N,
        heatDefBound3 d σ N m M L ((ε + 2 * (N * Lip) * (1 / g)) / N) (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)))
        + ((K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))
          + (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L)))) := by
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M := fun u => by
    rw [hMdef]; exact heatTorus_le hcσ d u
  have hLip : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u
      - heatTorus d (2 * Real.pi ^ 2 * σ) u'| ≤ Lip * dist u u' := fun u u' => by
    rw [hLipdef]; exact heatTorus_lipschitz hcσ d u u'
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hBn := heat_normalisation_whp hσ d X h_indep hX hlaw N hg hM hLip hLip0 hε
  exact heat_defect_whp3 hσ d X h_indep hX hlaw N K hN hM hL (by positivity) hsmall hBn


/-- The defect bound as a function of three numbers `pa, pb, q` standing for `p_{s+2σ}(u)`,
    `p_{σ+s}(u)` and `√(p_{3s}(u))`; it is linear in them with nonnegative coefficients. -/
noncomputable def heatDefNum3 (d : ℕ) (σ : ℝ) (N m : ℕ) (Mσ L δ pa pb q : ℝ) : ℝ :=
  (((2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb) * L
        + 2 * (Real.sqrt (N * (Mσ * heatCV3 d σ ((m : ℝ) * σ)) * L) * q))
      + 2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb))
    + 2 * δ * (N * (Real.sqrt (heatCV3 d σ ((m : ℝ) * σ)) * q)
        + (2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb) * L
          + 2 * (Real.sqrt (N * (Mσ * heatCV3 d σ ((m : ℝ) * σ)) * L) * q))
        + 2 * (heatKB d σ ((m : ℝ) * σ) * pa + Mσ * pb)))
    / (N * (1 / 3))

/-- The defect bound at a point is the numeric function at the three kernel quantities. -/
theorem heatDefBound_eq_num3 {σ Mσ L : ℝ} (hσ : 0 < σ) (hM : 0 ≤ Mσ) (hL : 0 ≤ L) (d N m : ℕ)
    (hm : 1 ≤ m) (δ : ℝ) (u : FlatTorus d) :
    heatDefBound3 d σ N m Mσ L δ u
      = heatDefNum3 d σ N m Mσ L δ
          (heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) u)
          (heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) u)
          (Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * ((m : ℝ) * σ))) u)) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hC := heatCV3_nonneg hσ hs d
  have hp3 := heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (3 * ((m : ℝ) * σ))) d u
  have e1 : Real.sqrt (N * (Mσ * (heatCV3 d σ ((m : ℝ) * σ)
        * heatTorus d (2 * Real.pi ^ 2 * (3 * ((m : ℝ) * σ))) u)) * L)
      = Real.sqrt (N * (Mσ * heatCV3 d σ ((m : ℝ) * σ)) * L)
        * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * ((m : ℝ) * σ))) u) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; ring
  have e2 : Real.sqrt (heatCV3 d σ ((m : ℝ) * σ)
        * heatTorus d (2 * Real.pi ^ 2 * (3 * ((m : ℝ) * σ))) u)
      = Real.sqrt (heatCV3 d σ ((m : ℝ) * σ))
        * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * ((m : ℝ) * σ))) u) :=
    Real.sqrt_mul hC _
  unfold heatDefBound3 heatThr3 heatDefNum3
  rw [heatB_eq, heatV3_eq, e1, e2]

/-- (P1) towards the time `6 s`: `p_τ ≤ (√12)^d p_{6s}` for `s ≤ τ ≤ 6 s` (the constant `√12` is
    kept, instead of `√6`, so that the constants of `WeightedConsistency` can be reused). -/
theorem heatTorus_to_six {s τ : ℝ} (hs : 0 < s) (h1 : s ≤ τ) (h2 : τ ≤ 6 * s) (d : ℕ)
    (u : FlatTorus d) :
    heatTorus d (2 * Real.pi ^ 2 * τ) u
      ≤ Real.sqrt 12 ^ d * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u := by
  have hpi := Real.pi_pos
  have hτ : 0 < τ := lt_of_lt_of_le hs h1
  have hca : 0 < 2 * Real.pi ^ 2 * τ := by positivity
  have hct : 0 < 2 * Real.pi ^ 2 * (6 * s) := by positivity
  have hle : 2 * Real.pi ^ 2 * τ ≤ 2 * Real.pi ^ 2 * (6 * s) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h := heatTorus_P1 hca hle d u
  have hp := heatTorus_nonneg hct d u
  have hr : 2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * τ) ≤ 12 := by
    rw [div_le_iff₀ hca]
    have : 2 * Real.pi ^ 2 * (6 * s) = 6 * (2 * Real.pi ^ 2 * s) := by ring
    rw [this]
    have h3 : 2 * Real.pi ^ 2 * s ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 0 ≤ 2 * Real.pi ^ 2 * s := by positivity
    linarith
  have hq : (2 * Real.pi ^ 2 * (6 * s) / (2 * Real.pi ^ 2 * τ)) ^ (1 / 2 : ℝ) ≤ Real.sqrt 12 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow (by positivity) hr (by norm_num)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hp)
  exact pow_le_pow_left₀ (by positivity) hq d

/-- The square of the base of `heatQ` at `c = 2π²·3s`, in terms of `w = √(2πs)`. -/
theorem heatQ_base_sq3 {s : ℝ} (hs : 0 < s) :
    (Real.sqrt (1 / Real.sqrt (2 * Real.pi ^ 2 * (3 * s) / Real.pi))
        / (1 / Real.sqrt (2 * (2 * Real.pi ^ 2 * (3 * s)) / Real.pi))) ^ 2
      = 2 * Real.sqrt 3 * Real.sqrt (2 * Real.pi * s) := by
  have hpi := Real.pi_pos
  obtain ⟨w, hw⟩ : ∃ w, w = Real.sqrt (2 * Real.pi * s) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact Real.sqrt_pos.mpr (by positivity)
  have hww : w * w = 2 * Real.pi * s := by rw [hw]; exact Real.mul_self_sqrt (by positivity)
  have e1 : 2 * Real.pi ^ 2 * (3 * s) / Real.pi = 3 * (w * w) := by rw [hww]; field_simp
  have e2 : 2 * (2 * Real.pi ^ 2 * (3 * s)) / Real.pi = 6 * (w * w) := by
    rw [hww]; field_simp; ring
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have s1 : Real.sqrt (3 * (w * w)) = Real.sqrt 3 * w := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul_self hw0.le]
  rw [e1, e2, ← hw, div_pow, Real.sq_sqrt (by positivity), s1, div_pow, one_pow,
    Real.sq_sqrt (by positivity)]
  field_simp
  nlinarith [h3]

/-- `heatQ(2π²·3s)² ≤ heatQ(2π²·6s)²`. -/
theorem heatQ_sq_three_le {s : ℝ} (hs : 0 < s) (d : ℕ) :
    heatQ d (2 * Real.pi ^ 2 * (3 * s)) ^ 2 ≤ heatQ d (2 * Real.pi ^ 2 * (6 * s)) ^ 2 := by
  have hpi := Real.pi_pos
  have hw0 : 0 ≤ Real.sqrt (2 * Real.pi * s) := Real.sqrt_nonneg _
  have e3 : heatQ d (2 * Real.pi ^ 2 * (3 * s)) ^ 2
      = (2 * Real.sqrt 3 * Real.sqrt (2 * Real.pi * s)) ^ d := by
    unfold heatQ
    simp only [← Real.sqrt_eq_rpow]
    rw [← pow_mul, mul_comm d 2, pow_mul, heatQ_base_sq3 hs]
  have e6 : heatQ d (2 * Real.pi ^ 2 * (6 * s)) ^ 2
      = (2 * Real.sqrt 6 * Real.sqrt (2 * Real.pi * s)) ^ d := by
    unfold heatQ
    simp only [← Real.sqrt_eq_rpow]
    rw [← pow_mul, mul_comm d 2, pow_mul, heatQ_base_sq hs]
  rw [e3, e6]
  have h36 : Real.sqrt 3 ≤ Real.sqrt 6 := Real.sqrt_le_sqrt (by norm_num)
  exact pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_right (by linarith) hw0) d

/-- The constant `r` of the weighted bound for the weight `p_{6m}`: `√2 · rateRA`. -/
noncomputable def rateRA3 (d : ℕ) : ℝ := Real.sqrt 2 * rateRA d

theorem rateRA3_nonneg (d : ℕ) : 0 ≤ rateRA3 d := by
  unfold rateRA3 rateRA
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Square root of a doubled coefficient. -/
theorem sqrt_cv3_le {cv R x : ℝ} (hR : 0 ≤ R) (hx : 0 ≤ x) (h : cv ≤ R * x) :
    Real.sqrt (2 * cv) ≤ Real.sqrt 2 * Real.sqrt R * Real.sqrt x := by
  calc Real.sqrt (2 * cv) ≤ Real.sqrt (2 * (R * x)) := Real.sqrt_le_sqrt (by linarith)
    _ = Real.sqrt 2 * Real.sqrt R * Real.sqrt x := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hR, mul_assoc]


/-- The first-moment term of the defect bound, times `s ≤ 1`: with (P5),
    `√(heatCV3) √(p_{3s}(u)) ≤ rateRA3 √(σ/s) p_{6s}(u)`. -/
theorem wc_Z_small3 {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : s ≤ 1) (d : ℕ) (u : FlatTorus d) :
    Real.sqrt (heatCV3 d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u)
      ≤ rateRA3 d * Real.sqrt (σ / s) * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u := by
  have hpi := Real.pi_pos
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  have hc3 : (0 : ℝ) < 2 * Real.pi ^ 2 * (3 * s) := by positivity
  have hc6' : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * s) := by positivity
  have hCV := heatCV3_nonneg hσ hs d
  have hQ := heatQ_nonneg hc3 d
  have hp6' := heatTorus_nonneg hc6' d u
  have h5 := heatTorus_sqrt_le hc3 d u
  rw [show 2 * (2 * Real.pi ^ 2 * (3 * s)) = 2 * Real.pi ^ 2 * (6 * s) by ring] at h5
  have hcq := heatCV_heatQ hσ hσs hs1 d
  have hq3 := heatQ_sq_three_le hs d
  have hCV0 := heatCV_nonneg hσ hs d
  have h1 : heatCV d σ s * heatQ d (2 * Real.pi ^ 2 * (3 * s)) ^ 2
      ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
          * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) * (σ / s) :=
    (mul_le_mul_of_nonneg_left hq3 hCV0).trans hcq
  have e1' : heatCV3 d σ s * heatQ d (2 * Real.pi ^ 2 * (3 * s)) ^ 2
      = 2 * (heatCV d σ s * heatQ d (2 * Real.pi ^ 2 * (3 * s)) ^ 2) := by
    unfold heatCV3; ring
  have hc := cvConst_nonneg
  have hR : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
      * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  have e1 : Real.sqrt (heatCV3 d σ s) * heatQ d (2 * Real.pi ^ 2 * (3 * s))
      = Real.sqrt (heatCV3 d σ s * heatQ d (2 * Real.pi ^ 2 * (3 * s)) ^ 2) := by
    rw [Real.sqrt_mul hCV, Real.sqrt_sq hQ]
  have e2 : Real.sqrt (heatCV3 d σ s) * heatQ d (2 * Real.pi ^ 2 * (3 * s))
      ≤ rateRA3 d * Real.sqrt (σ / s) := by
    rw [e1, e1']; unfold rateRA3 rateRA
    exact sqrt_cv3_le hR (by positivity) h1
  calc Real.sqrt (heatCV3 d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u)
      ≤ Real.sqrt (heatCV3 d σ s)
          * (heatQ d (2 * Real.pi ^ 2 * (3 * s)) * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u) :=
        mul_le_mul_of_nonneg_left h5 (Real.sqrt_nonneg _)
    _ = Real.sqrt (heatCV3 d σ s) * heatQ d (2 * Real.pi ^ 2 * (3 * s))
          * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u := by ring
    _ ≤ rateRA3 d * Real.sqrt (σ / s) * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u :=
        mul_le_mul_of_nonneg_right e2 hp6'

/-- The first-moment term of the defect bound, times `s ≥ 1` (where the kernel is of order one):
    `√(heatCV3) √(p_{3s}(u)) ≤ rateRA3 √(σ/s) 4^d p_{6s}(u)`. -/
theorem wc_Z_large3 {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (hs1 : 1 ≤ s) (d : ℕ) (u : FlatTorus d) :
    Real.sqrt (heatCV3 d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u)
      ≤ rateRA3 d * Real.sqrt (σ / s) * (4 ^ d * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u) := by
  have hpi := Real.pi_pos
  have hpi2 := Real.two_le_pi
  have hpis : 1 ≤ Real.pi * s := by nlinarith
  have hpps : Real.pi ≤ Real.pi * (Real.pi * s) := le_mul_of_one_le_right hpi.le hpis
  have hs : 0 < s := by linarith
  have hc3 : (0 : ℝ) < 2 * Real.pi ^ 2 * (3 * s) := by positivity
  have hc6' : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * s) := by positivity
  have hc := cvConst_nonneg
  have hR : 0 ≤ (d : ℝ) * cvConst * (2 * Real.sqrt 6)
      * (12 * (1 + Real.sqrt (2 * Real.pi))) ^ (d - 1) := by positivity
  have hp6' := heatTorus_nonneg hc6' d u
  have e2 : Real.sqrt (heatCV3 d σ s) ≤ rateRA3 d * Real.sqrt (σ / s) := by
    unfold rateRA3 rateRA heatCV3
    exact sqrt_cv3_le hR (by positivity) (heatCV_le_large hσ hσs hs1 d)
  have h8 : (8 : ℝ) ≤ 2 * Real.pi ^ 2 * (6 * s) := by
    have : 2 * Real.pi ^ 2 * (6 * s) = 12 * (Real.pi * (Real.pi * s)) := by ring
    rw [this]; linarith
  have hlow := heatTorus_ge_half_pow h8 d u
  have hup : heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u ≤ 2 ^ d := by
    refine (heatTorus_le hc3 d u).trans (pow_le_pow_left₀ (by positivity) ?_ d)
    have : Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * (3 * s))) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      apply Real.sqrt_le_sqrt
      rw [div_le_one hc3]
      have : 2 * Real.pi ^ 2 * (3 * s) = 6 * (Real.pi * (Real.pi * s)) := by ring
      rw [this]; linarith
    linarith
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hsq : Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u) ≤ 2 ^ d := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have h4 : (2 : ℝ) ^ d = 4 ^ d * (1 / 2) ^ d := by
    rw [← mul_pow]; norm_num
  have hq : Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u)
      ≤ 4 ^ d * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u := by
    refine hsq.trans ?_
    rw [h4]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hr0 : 0 ≤ rateRA3 d := rateRA3_nonneg d
  exact mul_le_mul e2 hq (Real.sqrt_nonneg _) (mul_nonneg hr0 (Real.sqrt_nonneg _))

/-- The first-moment term at every time `s ≥ σ`. -/
theorem wc_Z3 {σ s : ℝ} (hσ : 0 < σ) (hσs : σ ≤ s) (d : ℕ) (u : FlatTorus d) :
    Real.sqrt (heatCV3 d σ s) * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * (3 * s)) u)
      ≤ rateRA3 d * Real.sqrt (σ / s) * (4 ^ d * heatTorus d (2 * Real.pi ^ 2 * (6 * s)) u) := by
  have hpi := Real.pi_pos
  have hs : 0 < s := lt_of_lt_of_le hσ hσs
  rcases le_total s 1 with h | h
  · refine (wc_Z_small3 hσ hσs h d u).trans ?_
    have hp6' := heatTorus_nonneg (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * s)) d u
    have h4 : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    have hr : 0 ≤ rateRA3 d * Real.sqrt (σ / s) :=
      mul_nonneg (rateRA3_nonneg d) (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ hr
    nlinarith
  · exact wc_Z_large3 hσ hσs h d u

/-- **The pointwise defect bound with a weight and time-independent constants (deterministic).**
    For every `m ≥ 1` (no restriction on `mσ`), `σ ≤ 1` and every `u`:
    `heatDefBound3(u) ≤ 3[(1+2δ)(√12^d θ + 2 (√(NML)/N) 4^d r) + 2δ 4^d r] / √m · p_{6mσ}(u)`,
    `r = rateRA3 d`. HYPOTHESIS `hθ`: `(2L+2)(heatKbar + M) √m ≤ θ N` (the range of `m`). -/
theorem heatDefBound_weighted3 {σ M L δ θ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (hδ : 0 ≤ δ) (d N : ℕ) (hN : 0 < N) (m : ℕ) (hm : 1 ≤ m)
    (hθ : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N) (u : FlatTorus d) :
    heatDefBound3 d σ N m M L δ u
      ≤ 3 * ((1 + 2 * δ) * (Real.sqrt 12 ^ d * θ
              + 2 * (Real.sqrt (N * M * L) / N) * (4 ^ d * rateRA3 d))
            + 2 * δ * (4 ^ d * rateRA3 d)) / Real.sqrt m
        * heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u := by
  have hpi := Real.pi_pos
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have r1 : σ ≤ (m : ℝ) * σ := by nlinarith
  have hs : 0 < (m : ℝ) * σ := by positivity
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hKB : heatKB d σ ((m : ℝ) * σ) ≤ heatKbar d σ := by
    unfold heatKbar; exact heatKB_le hσ r1 hσ1 d
  have hKB0 := heatKB_nonneg hσ hs d
  have hCV := heatCV3_nonneg hσ hs d
  have hc6' : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)) := by positivity
  have hp6' := heatTorus_nonneg hc6' d u
  have ha := heatTorus_to_six hs (by nlinarith : (m : ℝ) * σ ≤ (m : ℝ) * σ + 2 * σ)
    (by nlinarith : (m : ℝ) * σ + 2 * σ ≤ 6 * ((m : ℝ) * σ)) d u
  have hb := heatTorus_to_six hs (by nlinarith : (m : ℝ) * σ ≤ σ + (m : ℝ) * σ)
    (by nlinarith : σ + (m : ℝ) * σ ≤ 6 * ((m : ℝ) * σ)) d u
  have hz := wc_Z3 hσ r1 d u
  have hpa0 := heatTorus_nonneg
    (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) d u
  have hpb0 := heatTorus_nonneg
    (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) d u
  have eσ : Real.sqrt (σ / ((m : ℝ) * σ)) = 1 / Real.sqrt m := by
    have : σ / ((m : ℝ) * σ) = 1 / m := by field_simp
    rw [this, Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [eσ] at hz
  rw [heatDefBound_eq_num3 hσ hM hL d N m hm δ u]
  unfold heatDefNum3
  obtain ⟨pa, hpa⟩ : ∃ pa : ℝ, pa = heatTorus d (2 * Real.pi ^ 2 * ((m : ℝ) * σ + 2 * σ)) u :=
    ⟨_, rfl⟩
  obtain ⟨pb, hpb⟩ : ∃ pb : ℝ, pb = heatTorus d (2 * Real.pi ^ 2 * (σ + (m : ℝ) * σ)) u :=
    ⟨_, rfl⟩
  obtain ⟨p3, hp3⟩ : ∃ p3 : ℝ, p3 = heatTorus d (2 * Real.pi ^ 2 * (3 * ((m : ℝ) * σ))) u :=
    ⟨_, rfl⟩
  obtain ⟨p6', hp6d⟩ :
      ∃ p6' : ℝ, p6' = heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) u := ⟨_, rfl⟩
  obtain ⟨KB, hKBd⟩ : ∃ KB : ℝ, KB = heatKB d σ ((m : ℝ) * σ) := ⟨_, rfl⟩
  obtain ⟨CV, hCVd⟩ : ∃ CV : ℝ, CV = heatCV3 d σ ((m : ℝ) * σ) := ⟨_, rfl⟩
  obtain ⟨kb, hkbd⟩ : ∃ kb : ℝ, kb = heatKbar d σ := ⟨_, rfl⟩
  obtain ⟨r, hrd⟩ : ∃ r : ℝ, r = rateRA3 d := ⟨_, rfl⟩
  obtain ⟨G, hGd⟩ : ∃ G : ℝ, G = Real.sqrt 12 ^ d := ⟨_, rfl⟩
  obtain ⟨F, hFd⟩ : ∃ F : ℝ, F = (4 : ℝ) ^ d := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hGd]; positivity
  have hF0 : 0 ≤ F := by rw [hFd]; positivity
  have hr0 : 0 ≤ r := by rw [hrd]; exact rateRA3_nonneg d
  rw [← hpa, ← hpb, ← hp3, ← hKBd, ← hCVd, ← hp6d, ← hrd, ← hGd, ← hFd]
  rw [← hpa, ← hp6d, ← hGd] at ha
  rw [← hpb, ← hp6d, ← hGd] at hb
  rw [← hp3, ← hp6d, ← hCVd, ← hrd, ← hFd] at hz
  rw [← hpa] at hpa0
  rw [← hpb] at hpb0
  rw [← hp6d] at hp6'
  rw [← hKBd, ← hkbd] at hKB
  rw [← hKBd] at hKB0
  rw [← hCVd] at hCV
  rw [← hkbd] at hθ hkb0
  have hX : KB * pa + M * pb ≤ (kb + M) * (G * p6') := by
    have h1 : KB * pa ≤ kb * (G * p6') := mul_le_mul hKB ha hpa0 hkb0
    have h2 : M * pb ≤ M * (G * p6') := mul_le_mul_of_nonneg_left hb hM
    linarith
  have hZ : Real.sqrt CV * Real.sqrt p3 ≤ F * r / Real.sqrt m * p6' := by
    refine hz.trans (le_of_eq ?_)
    field_simp
  have eT : Real.sqrt (N * (M * CV) * L) = Real.sqrt (N * M * L) * Real.sqrt CV := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1; ring
  have hT : Real.sqrt (N * (M * CV) * L) * Real.sqrt p3
      ≤ Real.sqrt (N * M * L) * (F * r / Real.sqrt m * p6') := by
    rw [eT, mul_assoc]
    exact mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)
  refine (defect_closed_core hNpos hL hδ hX hT hZ).trans ?_
  have hfin := wc_assemble (N := N) (L := L) (δ := δ) (S := Real.sqrt (N * M * L)) (kbM := kb + M)
    (G := G) (p := p6') (θ := θ) (rr := F * r) (sm := Real.sqrt m) hNpos hsm hδ
    (mul_nonneg hG0 hp6') hθ
  exact hfin

/-- The constant of the weighted consistency estimate against the `δ'` of the second file
    (`δ' = √(M log N/N)`, `M = (1 + (2πσ)^{-1/2})^d`). It depends only on `d`. -/
noncomputable def wcC3 (d : ℕ) : ℝ :=
  3 * ((5 / 4) * (16 * (rateCK d + 1) * Real.sqrt 12 ^ d
          + 2 * Real.sqrt 7 * (4 ^ d * rateRA3 d))
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * (4 ^ d * rateRA3 d))

theorem wcC3_nonneg (d : ℕ) : 0 ≤ wcC3 d := by
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA3 d := rateRA3_nonneg d
  unfold wcC3; positivity

/-- The three conclusions of the consistency lemma for points `x_0, …, x_{N-1}`, with the weight
    `p_{6mσ}`: (i) normalisation, (ii) the pointwise weighted bound for the one-step defect
    `h_m^{(i)}(b) = heatDefect d σ N m x b i`, (iii) the mean of the weight over the points. -/
def WeightedGood3 (d : ℕ) (σ : ℝ) (N K : ℕ) (cδ c : ℝ) (x : ℕ → FlatTorus d) : Prop :=
  (∀ j, |heatRho d σ N x j - 1| ≤ cδ) ∧
  ∀ m, 1 ≤ m → m ≤ K →
    (∀ b, b < N → ∀ i, i < N →
      |heatDefect d σ N m x b i|
        ≤ c * (1 / Real.sqrt m)
          * heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i)) ∧
    (∀ i, ∑ b ∈ Finset.range N,
        heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i) ≤ N * (1 + cδ))

/-- Monotonicity in the two constants. -/
theorem WeightedGood3.mono {d : ℕ} {σ : ℝ} (hσ : 0 < σ) {N K : ℕ} {cδ c cδ' c' : ℝ}
    {x : ℕ → FlatTorus d} (h : WeightedGood3 d σ N K cδ c x) (h1 : cδ ≤ cδ') (h2 : c ≤ c') :
    WeightedGood3 d σ N K cδ' c' x := by
  have hpi := Real.pi_pos
  refine ⟨fun j => (h.1 j).trans h1, fun m hm hmK => ⟨fun b hb i hi => ?_, fun i => ?_⟩⟩
  · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hp := heatTorus_nonneg
      (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) d (x b - x i)
    refine ((h.2 m hm hmK).1 b hb i hi).trans (mul_le_mul_of_nonneg_right ?_ hp)
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  · refine ((h.2 m hm hmK).2 i).trans (mul_le_mul_of_nonneg_left (by linarith) ?_)
    exact Nat.cast_nonneg N

/-- The mean form stated after the lemma in the paper, for the weight `p_{6m}`:
    the sum over `b` of the defect is at most `N c (1 + c_δ)/√m` (mean form). -/
theorem WeightedGood3.mean {d : ℕ} {σ : ℝ} {N K : ℕ} {cδ c : ℝ} (hc : 0 ≤ c)
    {x : ℕ → FlatTorus d} (h : WeightedGood3 d σ N K cδ c x) {m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K)
    {i : ℕ} (hi : i < N) :
    ∑ b ∈ Finset.range N, |heatDefect d σ N m x b i|
      ≤ c * (1 / Real.sqrt m) * (N * (1 + cδ)) := by
  obtain ⟨h1, h2⟩ := h.2 m hm hmK
  calc ∑ b ∈ Finset.range N, |heatDefect d σ N m x b i|
      ≤ ∑ b ∈ Finset.range N, c * (1 / Real.sqrt m)
          * heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i) :=
        Finset.sum_le_sum fun b hb => h1 b (Finset.mem_range.mp hb) i hi
    _ = c * (1 / Real.sqrt m) * ∑ b ∈ Finset.range N,
          heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) (x b - x i) := by
        rw [Finset.mul_sum]
    _ ≤ c * (1 / Real.sqrt m) * (N * (1 + cδ)) :=
        mul_le_mul_of_nonneg_left (h2 i) (by positivity)

/-- The supremum form: the defect is at most `c m^{-1/2} p_{6mσ}(0)`. -/
theorem WeightedGood3.sup {d : ℕ} {σ : ℝ} (hσ : 0 < σ) {N K : ℕ} {cδ c : ℝ} (hc : 0 ≤ c)
    {x : ℕ → FlatTorus d} (h : WeightedGood3 d σ N K cδ c x) {m : ℕ} (hm : 1 ≤ m) (hmK : m ≤ K)
    {b i : ℕ} (hb : b < N) (hi : i < N) :
    |heatDefect d σ N m x b i|
      ≤ c * (1 / Real.sqrt m) * heatTorus d (2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) 0 := by
  have hpi := Real.pi_pos
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc6' : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ)) := by positivity
  exact ((h.2 m hm hmK).1 b hb i hi).trans
    (mul_le_mul_of_nonneg_left (TorusReduction.heatTorus_le_zero hc6' d _) (by positivity))

set_option maxHeartbeats 3200000 in
/-- **The consistency lemma with the weight `p_{6m}`, against the `δ'` of the second file**
    (`M = (1 + (2πσ)^{-1/2})^d`, `δ' = √(M log N/N)`), under the hypotheses of `H5.h5_g3`:
    except on an event of probability at most `2/N³`, `WeightedGood3` holds with
    `c_δ = h5cD d · δ'` and `c = wcC3 d · δ'`, for all `1 ≤ m ≤ K` (no restriction `mσ ≤ 1`). -/
theorem weighted_consistency_g3_w3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * M * Real.log N)))
    (hsmall : rateCfin3 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ WeightedGood3 d σ N K (H5.h5cD d * δp) (wcC3 d * δp) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  obtain ⟨L, ε, δ0, θ, hLpos, hε, hsmall', hδ0def, hδ00, hδ08, hδ0le, hθ0, hθle, hθ', hSle, hδp0,
    hMpos, hp, hq⟩ := wc_params hσ d N K hN12 hK hKN hMdef hLipdef hδp hLipc hsmall
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hg : 0 < N ^ 3 := pow_pos hN 3
  have hg3 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; rfl
  have hconst : ∀ τ, σ ≤ τ →
      (∀ u, heatTorus d (2 * Real.pi ^ 2 * τ) u ≤ M)
      ∧ (∀ u u', |heatTorus d (2 * Real.pi ^ 2 * τ) u - heatTorus d (2 * Real.pi ^ 2 * τ) u'|
          ≤ Lip * dist u u') := by
    intro τ hτ
    have hcτ : 0 < 2 * Real.pi ^ 2 * τ := by have := lt_of_lt_of_le hσ hτ; positivity
    have hcc : 2 * Real.pi ^ 2 * σ ≤ 2 * Real.pi ^ 2 * τ :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    obtain ⟨a1, a2⟩ := heat_consts_anti hcσ hcc d
    constructor
    · intro u; rw [hMdef]; exact (heatTorus_le hcτ d u).trans a1
    · intro u u'; rw [hLipdef]
      exact (heatTorus_lipschitz hcτ d u u').trans (mul_le_mul_of_nonneg_right a2 dist_nonneg)
  obtain ⟨epsn, hepsn⟩ :
      ∃ epsn : ℝ, epsn = ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  obtain ⟨pn, hpn⟩ : ∃ pn : ℝ, pn = (((N ^ 3 : ℕ) : ℝ)) ^ d
      * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))) := ⟨_, rfl⟩
  have hpn0 : 0 ≤ pn := by rw [hpn]; positivity
  obtain ⟨Bn, hBnd⟩ : ∃ Bn : ℝ → Set Ω, Bn = fun τ => {ω | ∃ x : FlatTorus d,
      epsn < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (x - X j ω) - N|} := ⟨_, rfl⟩
  have hBnP : ∀ τ, σ ≤ τ → μ.real (Bn τ) ≤ pn := by
    intro τ hτ
    rw [hBnd, hpn, hepsn]
    exact heat_normalisation_whp (lt_of_lt_of_le hσ hτ) d X h_indep hX hlaw N hg
      (hconst τ hτ).1 (hconst τ hτ).2 hLip0 hε
  have hBnc : ∀ τ ω, ω ∉ Bn τ → ∀ y : FlatTorus d,
      |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * τ) (y - X j ω) - N| ≤ epsn := by
    intro τ ω hω y
    by_contra h
    rw [hBnd] at hω
    exact hω ⟨y, not_le.mp h⟩
  obtain ⟨E, hEd⟩ : ∃ E : Set Ω, E = {ω | ∃ m ∈ Finset.Icc 1 K, ∃ b ∈ Finset.range N,
      ∃ i ∈ Finset.range N,
        heatDefBound3 d σ N m M L ((ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ))) / N)
            (X b ω - X i ω)
          < |heatDefect d σ N m (fun j => X j ω) b i|} := ⟨_, rfl⟩
  have hEP : μ.real E ≤ pn + (1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3)) := by
    rw [hEd, hpn, ← hq]
    exact heat_defect_sample3 hσ d X h_indep hX hlaw N K hN hg hMdef hLipdef hLpos hε
      (by linarith)
  have hUP : μ.real (⋃ m ∈ Finset.Icc 1 K, Bn (6 * ((m : ℝ) * σ))) ≤ (K : ℝ) * pn := by
    calc μ.real (⋃ m ∈ Finset.Icc 1 K, Bn (6 * ((m : ℝ) * σ)))
        ≤ ∑ m ∈ Finset.Icc 1 K, μ.real (Bn (6 * ((m : ℝ) * σ))) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, pn := by
          refine Finset.sum_le_sum fun m hm => hBnP _ ?_
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
          nlinarith
      _ = (K : ℝ) * pn := by simp
  have hsub : {ω | ¬ WeightedGood3 d σ N K (H5.h5cD d * δp) (wcC3 d * δp) (fun j => X j ω)}
      ⊆ Bn σ ∪ E ∪ ⋃ m ∈ Finset.Icc 1 K, Bn (6 * ((m : ℝ) * σ)) := by
    intro ω hbad
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨⟨hn, hE⟩, hAm⟩ := hcon
    apply hbad
    have hcD : H5.h5cD d * δp = 6 * Real.sqrt (3 * (d : ℝ) + 5) * δp := by
      unfold H5.h5cD; rfl
    have hδN : epsn / N = δ0 := by rw [hδ0def, hepsn]
    have hmem : ∀ m, 1 ≤ m → m ≤ K → m ∈ Finset.Icc 1 K := fun m h1 h2 =>
      Finset.mem_Icc.mpr ⟨h1, h2⟩
    refine WeightedGood3.mono hσ (cδ := δ0) (c := wcC3 d * δp) ⟨?_, ?_⟩ (by rw [hcD]; exact hδ0le)
      le_rfl
    · intro j
      have h := hBnc σ ω hn (X j ω)
      have e : heatRho d σ N (fun j => X j ω) j - 1
          = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
        unfold heatRho; field_simp
      rw [e, abs_div, abs_of_pos hNpos, ← hδN]
      exact div_le_div_of_nonneg_right h hNpos.le
    · intro m hm hmK
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
      refine ⟨fun b hb i hi => ?_, fun i => ?_⟩
      · have h1 : |heatDefect d σ N m (fun j => X j ω) b i|
            ≤ heatDefBound3 d σ N m M L δ0 (X b ω - X i ω) := by
          by_contra h
          rw [hEd] at hE
          rw [hδ0def] at h
          exact hE ⟨m, hmem m hm hmK, b, Finset.mem_range.mpr hb, i, Finset.mem_range.mpr hi,
            not_le.mp h⟩
        have hθm : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt m ≤ θ * N := by
          have h1 : Real.sqrt m ≤ Real.sqrt K := Real.sqrt_le_sqrt (by exact_mod_cast hmK)
          have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
          have h2 : 0 ≤ (2 * L + 2) * (heatKbar d σ + M) := by positivity
          exact (mul_le_mul_of_nonneg_left h1 h2).trans hθ'
        have h2 := heatDefBound_weighted3 hσ hσ1 hMpos.le hLpos.le hδ00 d N hN m hm hθm
          (X b ω - X i ω)
        have hp6' := heatTorus_nonneg
          (by positivity : (0 : ℝ) < 2 * Real.pi ^ 2 * (6 * ((m : ℝ) * σ))) d (X b ω - X i ω)
        have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
        have hRA0 : 0 ≤ rateRA3 d := rateRA3_nonneg d
        have hG0 : (0 : ℝ) ≤ Real.sqrt 12 ^ d := by positivity
        have hθG : Real.sqrt 12 ^ d * θ ≤ 16 * (rateCK d + 1) * Real.sqrt 12 ^ d * δp := by
          have := mul_le_mul_of_nonneg_left hθle hG0
          linarith
        have hab := (rate_ab_bound (δ := δ0) (θ := Real.sqrt 12 ^ d * θ)
          (S := Real.sqrt (N * M * L) / N) (r := 4 ^ d * rateRA3 d) (δp := δp)
          (θ1 := 16 * (rateCK d + 1) * Real.sqrt 12 ^ d) (Aa := Real.sqrt (3 * (d : ℝ) + 5))
          hδ00 hδ08 hδ0le (by positivity) hθG (by positivity) hSle (by positivity) hδp0
          (by positivity) (Real.sqrt_nonneg _)).2
        have hcst : 3 * ((1 + 2 * δ0) * (Real.sqrt 12 ^ d * θ
              + 2 * (Real.sqrt (N * M * L) / N) * (4 ^ d * rateRA3 d))
            + 2 * δ0 * (4 ^ d * rateRA3 d)) ≤ wcC3 d * δp := by
          unfold wcC3; exact hab
        refine h1.trans (h2.trans (mul_le_mul_of_nonneg_right ?_ hp6'))
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right hcst (by positivity)
      · have hA' := hAm m (hmem m hm hmK)
        have h3 := norm_event_sum hN (fun j => X j ω) (hBnc _ ω hA') i
        rw [hδN] at h3
        exact h3
  have v1 := measureReal_union_le (μ := μ) (Bn σ ∪ E)
    (⋃ m ∈ Finset.Icc 1 K, Bn (6 * ((m : ℝ) * σ)))
  have v2 := measureReal_union_le (μ := μ) (Bn σ) E
  have v0 : μ.real {ω | ¬ WeightedGood3 d σ N K (H5.h5cD d * δp) (wcC3 d * δp) (fun j => X j ω)}
      ≤ μ.real (Bn σ ∪ E ∪ ⋃ m ∈ Finset.Icc 1 K, Bn (6 * ((m : ℝ) * σ))) :=
    measureReal_mono hsub (measure_ne_top μ _)
  have hb := hBnP σ le_rfl
  rw [hg3] at hpn
  rw [← hpn] at hp
  have hN3 : (0 : ℝ) < (N : ℝ) ^ 3 := by positivity
  have e3 : 2 / (N : ℝ) ^ 3
      = 1 / (N : ℝ) ^ 3 + (1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3)) := by
    field_simp; norm_num
  have hKpn : 0 ≤ (K : ℝ) * pn := by positivity
  rw [e3]
  nlinarith

/-- **The consistency lemma with the weight `p_{6m}`, in the quantities of the paper**
    (the estimates `lem:consistency`(i)--(iii) with the weight `p_{6m}` of the lemma; here
    `heatTorus d (2π²·6mσ)` is the kernel of variance `6mσ = 6mξ²`, the `p_{6m}` of the paper): `d ≥ 1`, `σ = ξ² ≤ 1`,
    `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`, `kernelC1 d · δ' · √K ≤ 1`. Except on an event of
    probability at most `2/N³`, for all `1 ≤ m ≤ K` and all `b, i < N`:
    `|ρ_j - 1| ≤ c_δ δ'`, `|h_m^{(i)}(b)| ≤ C δ' m^{-1/2} p_{6mσ}(X_b - X_i)` and
    `∑_b p_{6mσ}(X_b - X_i) ≤ N (1 + c_δ δ')`, with `c_δ = h5cD d (1 + √(2π))^d` and
    `C = wcC3 d (1 + √(2π))^d`, both depending only on `d`. No further hypothesis.
    This is NOT the lemma of the paper word for word: the range is `m ≤ K` with
    `kernelC1 d · δ' · √K ≤ 1` (paper: `m ≤ δ'^{-2}`), the constants are those of this file (not
    `6δ'` in (i), not `1 + 9δ'` in (iii)), the exceptional event is the one constructed here
    (probability `≤ 2/N³`, it depends on `K`; not shown measurable), and the proof uses explicit
    Gaussian integrals instead of the Gaussian Poincaré inequality and (P3). -/
theorem weighted_consistency_paper_w3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ WeightedGood3 d σ N K (H5.h5cD d * (1 + Real.sqrt (2 * Real.pi)) ^ d * δp)
        (wcC3 d * (1 + Real.sqrt (2 * Real.pi)) ^ d * δp) (fun j => X j ω)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  obtain ⟨ML, Lip, δL, hML, hLip, hδL, hN12, hKN, hLipc, hsmallL, hδLle, hδL0, hδp0⟩ :=
    H5.h5_setup hσ hσ1 d hd N K hN2 hK hMp hδp hrange
  have h := weighted_consistency_g3_w3 hσ hσ1 d X h_indep hX hlaw N K hN12 hK hKN hML hLip hδL
    hLipc hsmallL
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  have hD0 := (H5.h5c_nonneg d).1
  have hC0 := wcC3_nonneg d
  refine WeightedGood3.mono hσ hgood ?_ ?_
  · have := mul_le_mul_of_nonneg_left hδLle hD0
    linarith
  · have := mul_le_mul_of_nonneg_left hδLle hC0
    linarith




end SharpVariance

namespace OlderParts

open PopulationRate

/-!
Older parts of Appendix G (`thm:profile`, `prop:discrete`, `prop:heatbounds`) as statements about
sums over a list of eigenvalues or about real symmetric matrices. Contents: Part B (`thm:profile`,
this comment), a negative control for (F2), Part A (`prop:discrete`, deterministic part) and
Part C (`prop:heatbounds` for matrices); Parts A and C have their own comments below.

Conventions. As in `PopulationRate`, `σ` is the `σ` of the PAPER (`σ = c_h ξ²/2`; the `σ` of the
second and third Lean files is `ξ² = 2σ`), `t` is the time of the paper and `τ = t/σ`. A "closed
Riemannian manifold" enters only through a list `lam : ι → ℝ` with `PopulationRate.IsSpectrum lam`
(`lam ≥ 0`, every heat sum `∑ e^{-s lam_k}` converges); `heatTr lam s = Θ(s)`,
`heatMom lam p s = ∑ lam^p e^{-s lam} = (-1)^p Θ^{(p)}(s)`.

Part B (`thm:profile`, "Other profiles"). For a profile function `F : ℝ → ℝ` the operator
`P = F(-σΔ)` is represented by its eigenvalues `F(σ lam_k)`;
* `profTr F lam σ t = ∑_k [e^{-τ(1 - F(σ lam_k))} - e^{-τ}]` is `T^F_σ(t)`,
* `discTr F lam σ n = ∑_k F(σ lam_k)^n` is `Tr P^n`,
* `powSum lam p σ = ∑_k (1 + σ lam_k)^{-p}` is `N_p(σ)` (real exponent `p`).
The hypotheses on `F` are collected in `ProfileHyp F β c3 u1 δ CF p`: (F1) on `[0, u1]`, (F2) in
the form `|F| ≤ 1 - δ` on `[u1, ∞)`, (F3), and the smallness condition
`(5|β| + 9 c3 + 18) u1 ≤ 1` on the threshold `u1` between low and high modes.  Proved:
* `profile_i`: `thm:profile`(i) with explicit constants;
* `profile_ii`: `thm:profile`(ii) with explicit constants, for every `n ≥ 1` (the paper: `k ≥ 2`);
* `profile_hyp_of_paper`: the hypotheses (F1) on `[0, u0]`, the SECOND part of (F2) of the
  corrected statement (`sup_{u ≥ u1} |F(u)| < 1` for every `u1 > 0`, written as
  `∀ u1 > 0, ∃ δ > 0, ∀ u ≥ u1, |F u| ≤ 1 - δ`) and (F3) give `ProfileHyp` with
  `u1 = min u0 (1/(5|β| + 9 c3 + 18))`; the FIRST part of (F2) (`|F| ≤ 1 - δ` for `u ≥ u0`) is
  not used at all;
* `profile_paper`: the statement of the theorem in the form "there are constants `c, C > 0` such
  that for every spectrum, `t ≥ σ > 0` ... (i) and (ii) hold with the remainder `𝓡`".
* `profileHyp_gauss`: `ProfileHyp` is satisfiable (Gaussian profile `F(u) = e^{-u}`, `β = 1`);
* `profile_F2_fails`: a formal negative control: for `F(u) = 1 - u + 5u² - (9/2)u³` on `[0,1]`,
  `F = 0` on `(1, ∞)`, which satisfies (F1) on `[0,1]` (with `β = 10`, `c3 = 9/2`), the FIRST part
  of (F2) with `u0 = 1`, `δ = 1/2`, and (F3), the conclusion (i) fails for every choice of the
  constants `c, C` (one mode with `σ lam = 3/5`).

NOT proved and NOT claimed:
* nothing about a manifold, an operator `F(-σΔ)` or its trace: only the eigenvalue sums;
* the convergence of `N_p(σ)` is a HYPOTHESIS (`hNp`); on a manifold it follows from Weyl's law
  and `p > d/2`, which is not formalised (the condition `p > d/2` does not occur here);
* the last sentence of the theorem (relative deviations `β d(d+2)/8τ`, `(β-1) d(d+2)/8τ` up to
  `O(τ^{-2}) + O(σ)`), which needs the heat-trace asymptotics;
* the paragraph after the theorem (walks with independent steps on the torus, `eq:beta`);
* the dependence of the constants "only on ..." is visible from the explicit constants
  `profB`, `profCt`, `profB2`, `profK`, `profK2`, `profc`, not stated as a theorem;
* the explicit constants are far from sharp: `c = min(δ, u₁/4)` with `u₁ ≤ 1/18`, so the term
  `K(1+τ)e^{-cτ}[N_p(σ) + Θ(t/4)]` is small only for `τ` much larger than `1/c ≥ 72`.
Deviations from the proof of the paper: the logarithm in (ii) is estimated with
`|ln(1-v) + v + v²/2| ≤ v³/(1-v) ≤ 2v³` (Mathlib) instead of `≤ v³`; the number of low modes is
bounded through `1 ≤ 2^p (1+u)^{-p}` for `u ≤ 1`; `y² ≤ (|β|/2 + c₃)² x⁴/τ²` instead of
`β²x⁴/2τ² + 2c₃²u₀²x⁴/τ²`.
-/

/-! #### Constants -/

/-- `|β|/2 + c₃`. -/
noncomputable def profB (β c3 : ℝ) : ℝ := |β| / 2 + c3

/-- The constant `c̃` of the proof of (ii): `|ln F(u) + u - (β-1)u²/2| ≤ c̃ u³` on low modes. -/
noncomputable def profCt (β c3 : ℝ) : ℝ := 4 + c3 + 9 / 8 * profB β c3

/-- `|β - 1|/2 + c̃`. -/
noncomputable def profB2 (β c3 : ℝ) : ℝ := |β - 1| / 2 + profCt β c3

/-- The constant in front of the exponentially small terms in (i). -/
noncomputable def profK (β CF p : ℝ) : ℝ := (2 : ℝ) ^ p + CF + 5 * (1 + |β|)

/-- The constant in front of the exponentially small terms in (ii). -/
noncomputable def profK2 (β CF : ℝ) : ℝ := 4 * CF + 5 * (1 + |β - 1|)

/-- The exponential rate `c = min(δ, u₁/4)`. -/
noncomputable def profc (u1 δ : ℝ) : ℝ := min δ (u1 / 4)

theorem profB_nonneg {β c3 : ℝ} (hc : 0 ≤ c3) : 0 ≤ profB β c3 :=
  add_nonneg (div_nonneg (abs_nonneg β) (by norm_num)) hc

theorem profCt_nonneg {β c3 : ℝ} (hc : 0 ≤ c3) : 0 ≤ profCt β c3 := by
  have := profB_nonneg (β := β) hc
  unfold profCt
  linarith

theorem profB2_nonneg {β c3 : ℝ} (hc : 0 ≤ c3) : 0 ≤ profB2 β c3 :=
  add_nonneg (div_nonneg (abs_nonneg _) (by norm_num)) (profCt_nonneg hc)

theorem small_consequences {β c3 u1 : ℝ} (hc : 0 ≤ c3) (hu1 : 0 ≤ u1)
    (hU : (5 * |β| + 9 * c3 + 18) * u1 ≤ 1) :
    u1 ≤ 1 / 18 ∧ profB β c3 * u1 ≤ 1 / 4 ∧ profB2 β c3 * u1 ≤ 1 / 4 := by
  have hβ := abs_nonneg β
  have h1 := mul_nonneg hβ hu1
  have h2 := mul_nonneg hc hu1
  have h3 : |β - 1| ≤ |β| + 1 :=
    abs_le.2 ⟨by linarith [neg_abs_le β], by linarith [le_abs_self β]⟩
  have h4 := mul_le_mul_of_nonneg_right h3 hu1
  unfold profB2 profCt profB
  refine ⟨by linarith, by linarith, by linarith⟩

/-! #### One mode -/

/-- `exp_mode_expansion` of the core file for the real exponential, as an absolute value. -/
theorem mode_expansion_abs {x y p r Y : ℝ} (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hyp : |y - p| ≤ r) (hy : |y| ≤ x / 4) (hY : y * y ≤ Y) :
    |Real.exp (-x + y) - Real.exp (-x) - p * Real.exp (-x)|
      ≤ (Y / 2 + r) * Real.exp (-(x / 2)) := by
  obtain ⟨a1, a2⟩ := abs_le.1 hyp
  obtain ⟨b1, b2⟩ := abs_le.1 hy
  obtain ⟨l, u⟩ := CTG.HeatTrace.exp_mode_expansion real_isExp2 hx hr a1 a2 b1 b2
  have hE := Real.exp_pos (-(x / 2))
  have h1 : (y * y / 2 + r) * Real.exp (-(x / 2)) ≤ (Y / 2 + r) * Real.exp (-(x / 2)) :=
    mul_le_mul_of_nonneg_right (by linarith) hE.le
  have h2 : 0 ≤ Y * Real.exp (-(x / 2)) :=
    mul_nonneg ((_root_.mul_self_nonneg y).trans hY) hE.le
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- (F1) at one point: `|F(u) - 1 + u| ≤ (|β|/2 + c₃) u² ≤ u/4`. -/
theorem w_bound {u s β c3 u1 : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ u1) (h1 : u1 ≤ 1) (hc : 0 ≤ c3)
    (hB : profB β c3 * u1 ≤ 1 / 4)
    (hF : |s - (1 - u + β * u ^ 2 / 2)| ≤ c3 * u ^ 3) :
    |s - 1 + u| ≤ profB β c3 * u ^ 2 ∧ |s - 1 + u| ≤ u / 4 := by
  obtain ⟨f1, f2⟩ := abs_le.1 hF
  have hu2 : 0 ≤ u ^ 2 := pow_two_nonneg u
  have hb1 : β * u ^ 2 ≤ |β| * u ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self β) hu2
  have hb2 : -(|β| * u ^ 2) ≤ β * u ^ 2 := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le β) hu2
    linarith
  have h3 : c3 * u ^ 3 ≤ c3 * u ^ 2 := by
    have h : u ^ 3 ≤ u ^ 2 :=
      calc u ^ 3 = u ^ 2 * u := by ring
        _ ≤ u ^ 2 * 1 := mul_le_mul_of_nonneg_left (hu1.trans h1) hu2
        _ = u ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left h hc
  have hB0 := profB_nonneg (β := β) hc
  have key : |s - 1 + u| ≤ profB β c3 * u ^ 2 := by
    unfold profB
    rw [abs_le]
    constructor
    · linarith
    · linarith
  refine ⟨key, key.trans ?_⟩
  have h5 : profB β c3 * u ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hu1 hB0).trans hB
  calc profB β c3 * u ^ 2 = u * (profB β c3 * u) := by ring
    _ ≤ u * (1 / 4) := mul_le_mul_of_nonneg_left h5 hu
    _ = u / 4 := by ring

/-- `thm:profile`(i), one low mode (`u = σλ ≤ u₁`, `x = τu = tλ`, `s = F(u)`). -/
theorem prof_low {τ u s β c3 u1 x : ℝ} (hx : τ * u = x) (hτ : 0 ≤ τ) (hu : 0 ≤ u)
    (hu1 : u ≤ u1) (h1 : u1 ≤ 1) (hc : 0 ≤ c3) (hB : profB β c3 * u1 ≤ 1 / 4)
    (hF : |s - (1 - u + β * u ^ 2 / 2)| ≤ c3 * u ^ 3) :
    |Real.exp (-(τ * (1 - s))) - Real.exp (-x) - β * (x * u / 2) * Real.exp (-x)|
      ≤ (profB β c3 ^ 2 * (x * u) ^ 2 / 2 + c3 * (x * u * u)) * Real.exp (-(x / 2)) := by
  subst hx
  obtain ⟨w1, w2⟩ := w_bound hu hu1 h1 hc hB hF
  have hxx : 0 ≤ τ * u := mul_nonneg hτ hu
  have key := mode_expansion_abs (x := τ * u) (y := τ * (s - 1 + u))
    (p := β * (τ * u * u / 2)) (r := c3 * (τ * u * u * u))
    (Y := profB β c3 ^ 2 * (τ * u * u) ^ 2) hxx
    (mul_nonneg hc (mul_nonneg (mul_nonneg hxx hu) hu)) ?_ ?_ ?_
  · have e : -(τ * u) + τ * (s - 1 + u) = -(τ * (1 - s)) := by ring
    rw [e] at key
    exact key
  · have e : τ * (s - 1 + u) - β * (τ * u * u / 2) = τ * (s - (1 - u + β * u ^ 2 / 2)) := by
      ring
    rw [e, abs_mul, abs_of_nonneg hτ]
    calc τ * |s - (1 - u + β * u ^ 2 / 2)| ≤ τ * (c3 * u ^ 3) :=
          mul_le_mul_of_nonneg_left hF hτ
      _ = c3 * (τ * u * u * u) := by ring
  · rw [abs_mul, abs_of_nonneg hτ]
    calc τ * |s - 1 + u| ≤ τ * (u / 4) := mul_le_mul_of_nonneg_left w2 hτ
      _ = τ * u / 4 := by ring
  · have h := mul_self_le_mul_self (abs_nonneg (s - 1 + u)) w1
    rw [abs_mul_abs_self] at h
    have h' := mul_le_mul_of_nonneg_left h (_root_.mul_self_nonneg τ)
    calc τ * (s - 1 + u) * (τ * (s - 1 + u)) = τ * τ * ((s - 1 + u) * (s - 1 + u)) := by ring
      _ ≤ τ * τ * (profB β c3 * u ^ 2 * (profB β c3 * u ^ 2)) := h'
      _ = profB β c3 ^ 2 * (τ * u * u) ^ 2 := by ring

/-- The continuum part of a high mode (`u ≥ u₁`, `τ ≥ 1`):
    `b + |γ| (τu²/2) b ≤ 5(1+|γ|) e^{-u₁τ/4} e^{-τu/4}`. -/
theorem high_b {τ u u1 γ x : ℝ} (hx : τ * u = x) (hτ : 1 ≤ τ) (hu1 : 0 ≤ u1) (hu : u1 ≤ u) :
    Real.exp (-x) + |γ| * (x * u / 2) * Real.exp (-x)
      ≤ 5 * (1 + |γ|) * (Real.exp (-(u1 * τ / 4)) * Real.exp (-(x / 4))) := by
  subst hx
  have hτ0 : 0 ≤ τ := by linarith
  have hu0 : 0 ≤ u := hu1.trans hu
  have hxx : 0 ≤ τ * u := mul_nonneg hτ0 hu0
  have hγ := abs_nonneg γ
  have hE := Real.exp_pos (-(τ * u))
  have k5 : τ * u * u / 2 ≤ (τ * u) ^ 2 / 2 := by
    nlinarith [mul_nonneg (mul_nonneg hxx hu0) (show 0 ≤ τ - 1 by linarith)]
  have k6 := high_aux hxx
  have k7 : Real.exp (-(τ * u / 2)) ≤ Real.exp (-(u1 * τ / 4)) * Real.exp (-(τ * u / 4)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ0 (sub_nonneg.2 hu)])
  have p1 : |γ| * (τ * u * u / 2) * Real.exp (-(τ * u))
      ≤ |γ| * ((τ * u) ^ 2 / 2) * Real.exp (-(τ * u)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left k5 hγ) hE.le
  have p2 : 0 ≤ Real.exp (-(τ * u)) * ((τ * u) ^ 2 / 2) := mul_nonneg hE.le (by positivity)
  have p3 : 0 ≤ |γ| * Real.exp (-(τ * u)) := mul_nonneg hγ hE.le
  have p4 : (1 + |γ|) * (Real.exp (-(τ * u)) * (1 + (τ * u) ^ 2 / 2))
      ≤ (1 + |γ|) * (5 * (Real.exp (-(u1 * τ / 4)) * Real.exp (-(τ * u / 4)))) :=
    mul_le_mul_of_nonneg_left (k6.trans (by linarith)) (by linarith)
  linarith

/-- `thm:profile`(i), one high mode (`u ≥ u₁`, `|s| ≤ 1 - δ`, `|s| ≤ m`). -/
theorem prof_high {τ u s β u1 δ m x : ℝ} (hx : τ * u = x) (hτ : 1 ≤ τ) (hu1 : 0 ≤ u1)
    (hu : u1 ≤ u) (hδ : 0 ≤ δ) (hs : |s| ≤ 1 - δ) (hm : |s| ≤ m) :
    |Real.exp (-(τ * (1 - s))) - Real.exp (-τ) - Real.exp (-x)
        - β * (x * u / 2) * Real.exp (-x)|
      ≤ τ * m * Real.exp (-(δ * τ))
        + 5 * (1 + |β|) * (Real.exp (-(u1 * τ / 4)) * Real.exp (-(x / 4))) := by
  have hτ0 : 0 ≤ τ := by linarith
  have hu0 : 0 ≤ u := hu1.trans hu
  obtain ⟨l1, l2⟩ := CTG.HeatTrace.profile_high_mode real_isExp (tau := τ) (s := s)
    (m := |s|) (delta := δ) hτ0 (neg_abs_le s) (le_abs_self s) hδ hs
  have hb := high_b (γ := β) hx hτ hu1 hu
  have hEd := Real.exp_pos (-(δ * τ))
  have hEx := Real.exp_pos (-x)
  have h3 : τ * |s| * Real.exp (-(δ * τ)) ≤ τ * m * Real.exp (-(δ * τ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hτ0) hEd.le
  have hx0 : 0 ≤ x := by rw [← hx]; exact mul_nonneg hτ0 hu0
  have hq : 0 ≤ (x * u / 2) * Real.exp (-x) :=
    mul_nonneg (by have := mul_nonneg hx0 hu0; linarith) hEx.le
  have h4 : β * ((x * u / 2) * Real.exp (-x)) ≤ |β| * ((x * u / 2) * Real.exp (-x)) :=
    mul_le_mul_of_nonneg_right (le_abs_self β) hq
  have h5 : -(|β| * ((x * u / 2) * Real.exp (-x))) ≤ β * ((x * u / 2) * Real.exp (-x)) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le β) hq
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The hypotheses on the profile function, with an explicit threshold `u₁` between low and high
    modes: (F1) on `[0, u₁]`, (F2) as `|F| ≤ 1 - δ` on `[u₁, ∞)`, (F3), and
    `(5|β| + 9c₃ + 18) u₁ ≤ 1`. See `profile_hyp_of_paper` for the hypotheses of the paper. -/
structure ProfileHyp (F : ℝ → ℝ) (β c3 u1 δ CF p : ℝ) : Prop where
  c3_nonneg : 0 ≤ c3
  u1_pos : 0 < u1
  small : (5 * |β| + 9 * c3 + 18) * u1 ≤ 1
  δ_pos : 0 < δ
  CF_nonneg : 0 ≤ CF
  p_nonneg : 0 ≤ p
  F1 : ∀ u, 0 ≤ u → u ≤ u1 → |F u - (1 - u + β * u ^ 2 / 2)| ≤ c3 * u ^ 3
  F2 : ∀ u, u1 ≤ u → |F u| ≤ 1 - δ
  F3 : ∀ u, 0 ≤ u → |F u| ≤ CF * (1 + u) ^ (-p)

theorem weight_low {u p : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hp : 0 ≤ p) :
    1 ≤ (2 : ℝ) ^ p * (1 + u) ^ (-p) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 : (1 + u) ^ p ≤ (2 : ℝ) ^ p := Real.rpow_le_rpow h1.le (by linarith) hp
  have h3 : 0 < (1 + u) ^ p := Real.rpow_pos_of_pos h1 p
  rw [Real.rpow_neg h1.le, ← div_eq_mul_inv, one_le_div h3]
  exact h2

theorem profc_facts {u1 δ : ℝ} (hu1 : 0 < u1) (hδ : 0 < δ) :
    0 < profc u1 δ ∧ profc u1 δ ≤ δ ∧ profc u1 δ ≤ u1 / 4 :=
  ⟨lt_min hδ (by linarith), min_le_left _ _, min_le_right _ _⟩

/-- **`thm:profile`(i) for one mode**, low or high (`u = σλ`, `x = τu = tλ`, `τ ≥ 1`). -/
theorem prof_mode {F : ℝ → ℝ} {β c3 u1 δ CF p : ℝ} (H : ProfileHyp F β c3 u1 δ CF p)
    {τ u x : ℝ} (hx : τ * u = x) (hτ : 1 ≤ τ) (hu : 0 ≤ u) :
    |Real.exp (-(τ * (1 - F u))) - Real.exp (-τ) - Real.exp (-x)
        - β * (x * u / 2) * Real.exp (-x)|
      ≤ (profB β c3 ^ 2 * (x * u) ^ 2 / 2 + c3 * (x * u * u)) * Real.exp (-(x / 2))
        + profK β CF p * (1 + τ) * Real.exp (-(profc u1 δ * τ))
            * ((1 + u) ^ (-p) + Real.exp (-(x / 4))) := by
  have hτ0 : 0 ≤ τ := by linarith
  obtain ⟨s1, s2, -⟩ := small_consequences H.c3_nonneg H.u1_pos.le H.small
  have hδ1 : δ ≤ 1 := by
    have := (abs_nonneg _).trans (H.F2 u1 le_rfl)
    linarith
  obtain ⟨hc0, hcδ, hcu⟩ := profc_facts H.u1_pos H.δ_pos
  have hc1 : profc u1 δ ≤ 1 := hcδ.trans hδ1
  have hG : 0 ≤ (1 + u) ^ (-p) := Real.rpow_nonneg (by linarith) _
  have hE4 := Real.exp_pos (-(x / 4))
  have hEc := Real.exp_pos (-(profc u1 δ * τ))
  have hx0 : 0 ≤ x := by rw [← hx]; exact mul_nonneg hτ0 hu
  have hP : 0 ≤ (profB β c3 ^ 2 * (x * u) ^ 2 / 2 + c3 * (x * u * u)) * Real.exp (-(x / 2)) :=
    mul_nonneg (add_nonneg (by positivity)
      (mul_nonneg H.c3_nonneg (mul_nonneg (mul_nonneg hx0 hu) hu))) (Real.exp_pos _).le
  have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  have hTG : 0 ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p) :=
    mul_nonneg (mul_nonneg (by linarith) hEc.le) hG
  have hTE : 0 ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4)) :=
    mul_nonneg (mul_nonneg (by linarith) hEc.le) hE4.le
  have hT : Real.exp (-(profc u1 δ * τ)) ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) := by
    have := mul_nonneg hτ0 hEc.le
    linarith
  have hKsplit : profK β CF p * (1 + τ) * Real.exp (-(profc u1 δ * τ))
        * ((1 + u) ^ (-p) + Real.exp (-(x / 4)))
      = (2 : ℝ) ^ p * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p))
        + CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p))
        + 5 * (1 + |β|) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4)))
        + (5 * (1 + |β|) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p))
          + ((2 : ℝ) ^ p + CF)
              * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4)))) := by
    unfold profK
    ring
  have hβ5 : (0 : ℝ) ≤ 5 * (1 + |β|) := by positivity
  have hrest : 0 ≤ 5 * (1 + |β|) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p))
      + ((2 : ℝ) ^ p + CF) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4))) :=
    add_nonneg (mul_nonneg hβ5 hTG) (mul_nonneg (add_nonneg h2p H.CF_nonneg) hTE)
  have n1 := mul_nonneg h2p hTG
  have n2 := mul_nonneg H.CF_nonneg hTG
  have n3 := mul_nonneg hβ5 hTE
  rcases le_total u u1 with h | h
  · have key := prof_low hx hτ0 hu h (by linarith) H.c3_nonneg s2 (H.F1 u hu h)
    obtain ⟨k1, k2⟩ := abs_le.1 key
    have e1 : Real.exp (-τ) ≤ Real.exp (-(profc u1 δ * τ)) :=
      Real.exp_le_exp.2 (by nlinarith [mul_nonneg (sub_nonneg.2 hc1) hτ0])
    have wl := weight_low hu (h.trans (by linarith)) H.p_nonneg
    have a1 := mul_le_mul_of_nonneg_left wl hEc.le
    have a2 : Real.exp (-(profc u1 δ * τ)) * ((2 : ℝ) ^ p * (1 + u) ^ (-p))
        ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) * ((2 : ℝ) ^ p * (1 + u) ^ (-p)) :=
      mul_le_mul_of_nonneg_right hT (mul_nonneg h2p hG)
    have hEt := Real.exp_pos (-τ)
    rw [abs_le]
    constructor
    · linarith
    · linarith
  · have key := prof_high (β := β) hx hτ H.u1_pos.le h H.δ_pos.le (H.F2 u h) (H.F3 u hu)
    have d1 : Real.exp (-(δ * τ)) ≤ Real.exp (-(profc u1 δ * τ)) :=
      Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hcδ hτ0; linarith)
    have d2 : Real.exp (-(u1 * τ / 4)) ≤ Real.exp (-(profc u1 δ * τ)) :=
      Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hcu hτ0; linarith)
    have t0 : τ * Real.exp (-(δ * τ)) ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) :=
      mul_le_mul (by linarith) d1 (Real.exp_pos _).le (by linarith)
    have t1 : τ * (CF * (1 + u) ^ (-p)) * Real.exp (-(δ * τ))
        ≤ CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p)) :=
      calc τ * (CF * (1 + u) ^ (-p)) * Real.exp (-(δ * τ))
          = CF * (1 + u) ^ (-p) * (τ * Real.exp (-(δ * τ))) := by ring
        _ ≤ CF * (1 + u) ^ (-p) * ((1 + τ) * Real.exp (-(profc u1 δ * τ))) :=
            mul_le_mul_of_nonneg_left t0 (mul_nonneg H.CF_nonneg hG)
        _ = CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p)) := by ring
    have t2 : 5 * (1 + |β|) * (Real.exp (-(u1 * τ / 4)) * Real.exp (-(x / 4)))
        ≤ 5 * (1 + |β|) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (d2.trans hT) hE4.le) hβ5
    exact key.trans (by linarith)

/-- `thm:profile`(ii), one low mode: `s = F(u)`, `u ≤ u₁`, `n` steps, `x = nu`. The logarithm of
    the paper is taken with `Real.log` and `Real.abs_log_sub_add_sum_range_le`. -/
theorem prof_low_disc {u s β c3 u1 τ x : ℝ} (n : ℕ) (hn : (n : ℝ) = τ) (hx : τ * u = x)
    (hu : 0 ≤ u) (hu1 : u ≤ u1) (hc : 0 ≤ c3) (hU : (5 * |β| + 9 * c3 + 18) * u1 ≤ 1)
    (hF : |s - (1 - u + β * u ^ 2 / 2)| ≤ c3 * u ^ 3) :
    |s ^ n - Real.exp (-x) - (β - 1) * (x * u / 2) * Real.exp (-x)|
      ≤ (profB2 β c3 ^ 2 * (x * u) ^ 2 / 2 + profCt β c3 * (x * u * u))
          * Real.exp (-(x / 2)) := by
  subst hn
  subst hx
  have hu10 : 0 ≤ u1 := hu.trans hu1
  obtain ⟨s1, s2, s3⟩ := small_consequences hc hu10 hU
  have h1 : u1 ≤ 1 := by linarith
  obtain ⟨w1, w2⟩ := w_bound hu hu1 h1 hc s2 hF
  obtain ⟨f1, f2⟩ := abs_le.1 hF
  obtain ⟨w2a, w2b⟩ := abs_le.1 w2
  have hτ : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hB0 := profB_nonneg (β := β) hc
  have hCt0 := profCt_nonneg (β := β) hc
  have hB20 := profB2_nonneg (β := β) hc
  have hu2 : 0 ≤ u ^ 2 := pow_two_nonneg u
  have hu3 : 0 ≤ u ^ 3 := pow_nonneg hu 3
  have hv0 : 0 ≤ 1 - s := by linarith
  have hv1 : 1 - s ≤ 5 / 4 * u := by linarith
  have hs2 : 1 / 2 ≤ s := by linarith
  have hs : 0 < s := by linarith
  have habs : |1 - s| < 1 := by rw [abs_of_nonneg hv0]; linarith
  have hlog := Real.abs_log_sub_add_sum_range_le habs 2
  have e0 : (∑ i ∈ Finset.range 2, (1 - s) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - (1 - s))
      = Real.log s + (1 - s) + (1 - s) ^ 2 / 2 := by
    have e1 : (1 : ℝ) - (1 - s) = s := by ring
    rw [Finset.sum_range_succ, Finset.sum_range_one, e1]
    push_cast
    ring
  rw [e0, abs_of_nonneg hv0] at hlog
  have hL : |Real.log s + (1 - s) + (1 - s) ^ 2 / 2| ≤ 4 * u ^ 3 := by
    refine hlog.trans ?_
    have e1 : (1 : ℝ) - (1 - s) = s := by ring
    have e2 : (1 - s) ^ (2 + 1) = (1 - s) ^ 3 := by norm_num
    rw [e1, e2, div_le_iff₀ hs]
    have h3 : (1 - s) ^ 3 ≤ (5 / 4 * u) ^ 3 := pow_le_pow_left₀ hv0 hv1 3
    have e3 : (5 / 4 * u) ^ 3 = 125 / 64 * u ^ 3 := by ring
    have h4 := mul_nonneg hu3 (show 0 ≤ s - 1 / 2 by linarith)
    rw [e3] at h3
    linarith
  obtain ⟨L1, L2⟩ := abs_le.1 hL
  have hvu : |(1 - s) ^ 2 - u ^ 2| ≤ profB β c3 * u ^ 2 * (9 / 4 * u) := by
    have e : (1 - s) ^ 2 - u ^ 2 = -(s - 1 + u) * ((1 - s) + u) := by ring
    rw [e, abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ (1 - s) + u by linarith)]
    exact mul_le_mul w1 (by linarith) (by linarith) (mul_nonneg hB0 hu2)
  obtain ⟨D1, D2⟩ := abs_le.1 hvu
  have hρ : |Real.log s + u - (β - 1) * u ^ 2 / 2| ≤ profCt β c3 * u ^ 3 := by
    unfold profCt
    rw [abs_le]
    constructor
    · linarith
    · linarith
  obtain ⟨r1, r2⟩ := abs_le.1 hρ
  have hb1 : (β - 1) * u ^ 2 ≤ |β - 1| * u ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hu2
  have hb2 : -(|β - 1| * u ^ 2) ≤ (β - 1) * u ^ 2 := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le (β - 1)) hu2
    linarith
  have h3 : profCt β c3 * u ^ 3 ≤ profCt β c3 * u ^ 2 := by
    have h : u ^ 3 ≤ u ^ 2 :=
      calc u ^ 3 = u ^ 2 * u := by ring
        _ ≤ u ^ 2 * 1 := mul_le_mul_of_nonneg_left (hu1.trans h1) hu2
        _ = u ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left h hCt0
  have key2 : |Real.log s + u| ≤ profB2 β c3 * u ^ 2 := by
    unfold profB2
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have key3 : |Real.log s + u| ≤ u / 4 := by
    refine key2.trans ?_
    have h5 : profB2 β c3 * u ≤ 1 / 4 := (mul_le_mul_of_nonneg_left hu1 hB20).trans s3
    calc profB2 β c3 * u ^ 2 = u * (profB2 β c3 * u) := by ring
      _ ≤ u * (1 / 4) := mul_le_mul_of_nonneg_left h5 hu
      _ = u / 4 := by ring
  have hxx : 0 ≤ (n : ℝ) * u := mul_nonneg hτ hu
  have key := mode_expansion_abs (x := (n : ℝ) * u) (y := (n : ℝ) * (Real.log s + u))
    (p := (β - 1) * ((n : ℝ) * u * u / 2)) (r := profCt β c3 * ((n : ℝ) * u * u * u))
    (Y := profB2 β c3 ^ 2 * ((n : ℝ) * u * u) ^ 2) hxx
    (mul_nonneg hCt0 (mul_nonneg (mul_nonneg hxx hu) hu)) ?_ ?_ ?_
  · have e : -((n : ℝ) * u) + (n : ℝ) * (Real.log s + u) = (n : ℝ) * Real.log s := by ring
    rw [e, Real.exp_nat_mul, Real.exp_log hs] at key
    exact key
  · have e : (n : ℝ) * (Real.log s + u) - (β - 1) * ((n : ℝ) * u * u / 2)
        = (n : ℝ) * (Real.log s + u - (β - 1) * u ^ 2 / 2) := by ring
    rw [e, abs_mul, abs_of_nonneg hτ]
    calc (n : ℝ) * |Real.log s + u - (β - 1) * u ^ 2 / 2|
        ≤ (n : ℝ) * (profCt β c3 * u ^ 3) := mul_le_mul_of_nonneg_left hρ hτ
      _ = profCt β c3 * ((n : ℝ) * u * u * u) := by ring
  · rw [abs_mul, abs_of_nonneg hτ]
    calc (n : ℝ) * |Real.log s + u| ≤ (n : ℝ) * (u / 4) := mul_le_mul_of_nonneg_left key3 hτ
      _ = (n : ℝ) * u / 4 := by ring
  · have h := mul_self_le_mul_self (abs_nonneg (Real.log s + u)) key2
    rw [abs_mul_abs_self] at h
    have h' := mul_le_mul_of_nonneg_left h (_root_.mul_self_nonneg (n : ℝ))
    calc (n : ℝ) * (Real.log s + u) * ((n : ℝ) * (Real.log s + u))
        = (n : ℝ) * (n : ℝ) * ((Real.log s + u) * (Real.log s + u)) := by ring
      _ ≤ (n : ℝ) * (n : ℝ) * (profB2 β c3 * u ^ 2 * (profB2 β c3 * u ^ 2)) := h'
      _ = profB2 β c3 ^ 2 * ((n : ℝ) * u * u) ^ 2 := by ring

/-- `thm:profile`(ii), one high mode: `|s|^n ≤ (1-δ)^{n-1} |s| ≤ 4 e^{-δ n} m`. -/
theorem prof_high_disc {u s β u1 δ m τ x : ℝ} (n : ℕ) (hn1 : 1 ≤ n) (hn : (n : ℝ) = τ)
    (hx : τ * u = x) (hu1 : 0 ≤ u1) (hu : u1 ≤ u) (hδ1 : δ ≤ 1)
    (hs : |s| ≤ 1 - δ) (hm : |s| ≤ m) :
    |s ^ n - Real.exp (-x) - (β - 1) * (x * u / 2) * Real.exp (-x)|
      ≤ 4 * m * Real.exp (-(δ * τ))
        + 5 * (1 + |β - 1|) * (Real.exp (-(u1 * τ / 4)) * Real.exp (-(x / 4))) := by
  have hτ : 1 ≤ τ := by rw [← hn]; exact_mod_cast hn1
  have hτ0 : 0 ≤ τ := by linarith
  have hu0 : 0 ≤ u := hu1.trans hu
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have hEd := Real.exp_pos (-(δ * τ))
  have q1 : (1 - δ) ^ j ≤ Real.exp (-δ) ^ j :=
    pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-δ); linarith) j
  have q2 : Real.exp (-δ) ^ j = Real.exp δ * Real.exp (-(δ * τ)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← hn]
    congr 1
    push_cast
    ring
  have q3 : Real.exp δ ≤ 4 := (Real.exp_le_exp.2 hδ1).trans exp_one_le_four
  have q4 : (1 - δ) ^ j ≤ 4 * Real.exp (-(δ * τ)) := by
    rw [q2] at q1
    exact q1.trans (mul_le_mul_of_nonneg_right q3 hEd.le)
  have q5 : |s| ^ j ≤ (1 - δ) ^ j := pow_le_pow_left₀ (abs_nonneg s) hs j
  have habs : |s ^ (j + 1)| ≤ 4 * m * Real.exp (-(δ * τ)) := by
    rw [abs_pow, pow_succ]
    calc |s| ^ j * |s| ≤ 4 * Real.exp (-(δ * τ)) * m :=
          mul_le_mul (q5.trans q4) hm (abs_nonneg s) (by positivity)
      _ = 4 * m * Real.exp (-(δ * τ)) := by ring
  obtain ⟨l1, l2⟩ := abs_le.1 habs
  have hb := high_b (γ := β - 1) hx hτ hu1 hu
  have hEx := Real.exp_pos (-x)
  have hx0 : 0 ≤ x := by rw [← hx]; exact mul_nonneg hτ0 hu0
  have hq : 0 ≤ (x * u / 2) * Real.exp (-x) :=
    mul_nonneg (by have := mul_nonneg hx0 hu0; linarith) hEx.le
  have h4 : (β - 1) * ((x * u / 2) * Real.exp (-x)) ≤ |β - 1| * ((x * u / 2) * Real.exp (-x)) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hq
  have h5 : -(|β - 1| * ((x * u / 2) * Real.exp (-x)))
      ≤ (β - 1) * ((x * u / 2) * Real.exp (-x)) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le (β - 1)) hq
    linarith
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **`thm:profile`(ii) for one mode**, low or high (`u = σλ`, `n ≥ 1` steps, `x = nu = tλ`). -/
theorem prof_mode_disc {F : ℝ → ℝ} {β c3 u1 δ CF p : ℝ} (H : ProfileHyp F β c3 u1 δ CF p)
    (n : ℕ) (hn1 : 1 ≤ n) {τ u x : ℝ} (hn : (n : ℝ) = τ) (hx : τ * u = x) (hu : 0 ≤ u) :
    |F u ^ n - Real.exp (-x) - (β - 1) * (x * u / 2) * Real.exp (-x)|
      ≤ (profB2 β c3 ^ 2 * (x * u) ^ 2 / 2 + profCt β c3 * (x * u * u)) * Real.exp (-(x / 2))
        + profK2 β CF * (1 + τ) * Real.exp (-(profc u1 δ * τ))
            * ((1 + u) ^ (-p) + Real.exp (-(x / 4))) := by
  have hτ : 1 ≤ τ := by rw [← hn]; exact_mod_cast hn1
  have hτ0 : 0 ≤ τ := by linarith
  have hδ1 : δ ≤ 1 := by
    have := (abs_nonneg _).trans (H.F2 u1 le_rfl)
    linarith
  obtain ⟨hc0, hcδ, hcu⟩ := profc_facts H.u1_pos H.δ_pos
  have hG : 0 ≤ (1 + u) ^ (-p) := Real.rpow_nonneg (by linarith) _
  have hE4 := Real.exp_pos (-(x / 4))
  have hEc := Real.exp_pos (-(profc u1 δ * τ))
  have hx0 : 0 ≤ x := by rw [← hx]; exact mul_nonneg hτ0 hu
  have hCt0 := profCt_nonneg (β := β) H.c3_nonneg
  have hTG : 0 ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p) :=
    mul_nonneg (mul_nonneg (by linarith) hEc.le) hG
  have hTE : 0 ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4)) :=
    mul_nonneg (mul_nonneg (by linarith) hEc.le) hE4.le
  have hT : Real.exp (-(profc u1 δ * τ)) ≤ (1 + τ) * Real.exp (-(profc u1 δ * τ)) := by
    have := mul_nonneg hτ0 hEc.le
    linarith
  have hβ5 : (0 : ℝ) ≤ 5 * (1 + |β - 1|) := by positivity
  have hKsplit : profK2 β CF * (1 + τ) * Real.exp (-(profc u1 δ * τ))
        * ((1 + u) ^ (-p) + Real.exp (-(x / 4)))
      = 4 * CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p))
        + 5 * (1 + |β - 1|) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4)))
        + (5 * (1 + |β - 1|) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p))
          + 4 * CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4)))) := by
    unfold profK2
    ring
  have h4CF : (0 : ℝ) ≤ 4 * CF := by have := H.CF_nonneg; linarith
  have hrest : 0 ≤ 5 * (1 + |β - 1|) * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p))
      + 4 * CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4))) :=
    add_nonneg (mul_nonneg hβ5 hTG) (mul_nonneg h4CF hTE)
  have n2 := mul_nonneg h4CF hTG
  have n3 := mul_nonneg hβ5 hTE
  rcases le_total u u1 with h | h
  · have key := prof_low_disc n hn hx hu h H.c3_nonneg H.small (H.F1 u hu h)
    exact key.trans (by linarith)
  · have key := prof_high_disc (β := β) n hn1 hn hx H.u1_pos.le h hδ1 (H.F2 u h)
      (H.F3 u hu)
    have d1 : Real.exp (-(δ * τ)) ≤ Real.exp (-(profc u1 δ * τ)) :=
      Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hcδ hτ0; linarith)
    have d2 : Real.exp (-(u1 * τ / 4)) ≤ Real.exp (-(profc u1 δ * τ)) :=
      Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hcu hτ0; linarith)
    have t1 : 4 * (CF * (1 + u) ^ (-p)) * Real.exp (-(δ * τ))
        ≤ 4 * CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p)) :=
      calc 4 * (CF * (1 + u) ^ (-p)) * Real.exp (-(δ * τ))
          = 4 * CF * (1 + u) ^ (-p) * Real.exp (-(δ * τ)) := by ring
        _ ≤ 4 * CF * (1 + u) ^ (-p) * ((1 + τ) * Real.exp (-(profc u1 δ * τ))) :=
            mul_le_mul_of_nonneg_left (d1.trans hT) (mul_nonneg h4CF hG)
        _ = 4 * CF * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * (1 + u) ^ (-p)) := by ring
    have t2 : 5 * (1 + |β - 1|) * (Real.exp (-(u1 * τ / 4)) * Real.exp (-(x / 4)))
        ≤ 5 * (1 + |β - 1|)
            * ((1 + τ) * Real.exp (-(profc u1 δ * τ)) * Real.exp (-(x / 4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (d2.trans hT) hE4.le) hβ5
    have hP : 0 ≤ (profB2 β c3 ^ 2 * (x * u) ^ 2 / 2 + profCt β c3 * (x * u * u))
        * Real.exp (-(x / 2)) :=
      mul_nonneg (add_nonneg (by positivity)
        (mul_nonneg hCt0 (mul_nonneg (mul_nonneg hx0 hu) hu))) (Real.exp_pos _).le
    exact key.trans (by linarith)

/-! #### Summation over a spectrum -/

/-- The remainder for one mode in the variables of the paper (`l = λ_k`). -/
noncomputable def modeR (a1 a2 K c p σ t l : ℝ) : ℝ :=
  (σ / t) ^ 2 * (a1 * t ^ 4 * (l ^ 4 * Real.exp (-(t / 2 * l)))
      + a2 * t ^ 3 * (l ^ 3 * Real.exp (-(t / 2 * l))))
    + K * (1 + t / σ) * Real.exp (-(c * (t / σ)))
        * ((1 + σ * l) ^ (-p) + Real.exp (-(t / 4 * l)))

theorem modeR_eq {A a2 K c p σ t l : ℝ} (ht : 0 < t) :
    (A ^ 2 * (t * l * (σ * l)) ^ 2 / 2 + a2 * (t * l * (σ * l) * (σ * l)))
          * Real.exp (-(t * l / 2))
        + K * (1 + t / σ) * Real.exp (-(c * (t / σ)))
            * ((1 + σ * l) ^ (-p) + Real.exp (-(t * l / 4)))
      = modeR (A ^ 2 / 2) a2 K c p σ t l := by
  have h : σ / t * t = σ := div_mul_cancel₀ σ ht.ne'
  have e4 : t * l / 2 = t / 2 * l := by ring
  have e5 : t * l / 4 = t / 4 * l := by ring
  have e1 : (σ / t) ^ 2 * (A ^ 2 / 2 * t ^ 4 * l ^ 4) = A ^ 2 * (t * l * (σ * l)) ^ 2 / 2 :=
    calc (σ / t) ^ 2 * (A ^ 2 / 2 * t ^ 4 * l ^ 4)
        = A ^ 2 / 2 * (σ / t * t) ^ 2 * t ^ 2 * l ^ 4 := by ring
      _ = A ^ 2 / 2 * σ ^ 2 * t ^ 2 * l ^ 4 := by rw [h]
      _ = A ^ 2 * (t * l * (σ * l)) ^ 2 / 2 := by ring
  have e2 : (σ / t) ^ 2 * (a2 * t ^ 3 * l ^ 3) = a2 * (t * l * (σ * l) * (σ * l)) :=
    calc (σ / t) ^ 2 * (a2 * t ^ 3 * l ^ 3) = a2 * (σ / t * t) ^ 2 * t * l ^ 3 := by ring
      _ = a2 * σ ^ 2 * t * l ^ 3 := by rw [h]
      _ = a2 * (t * l * (σ * l) * (σ * l)) := by ring
  unfold modeR
  rw [← e1, ← e2, e4, e5]
  ring

section Sums

variable {ι : Type*} (lam : ι → ℝ)

/-- `N_p(σ) = ∑_k (1 + σ λ_k)^{-p}` (real exponent). -/
noncomputable def powSum (p σ : ℝ) : ℝ := ∑' k, (1 + σ * lam k) ^ (-p)

/-- `T^F_σ(t) = ∑_k [e^{-τ(1 - F(σ λ_k))} - e^{-τ}]`, `τ = t/σ`. -/
noncomputable def profTr (F : ℝ → ℝ) (σ t : ℝ) : ℝ :=
  ∑' k, (Real.exp (-(t / σ * (1 - F (σ * lam k)))) - Real.exp (-(t / σ)))

/-- `Tr P^n = ∑_k F(σ λ_k)^n`. -/
noncomputable def discTr (F : ℝ → ℝ) (σ : ℝ) (n : ℕ) : ℝ := ∑' k, F (σ * lam k) ^ n

variable {lam}

theorem powSum_nonneg (h : IsSpectrum lam) {σ : ℝ} (hσ : 0 ≤ σ) (p : ℝ) : 0 ≤ powSum lam p σ :=
  tsum_nonneg fun k =>
    Real.rpow_nonneg (by have := mul_nonneg hσ (h.nonneg k); linarith) _

/-- Summation of mode-wise bounds of the form `modeR`. -/
theorem sum_modeR (h : IsSpectrum lam) {a1 a2 K c p σ t : ℝ} (ht : 0 < t)
    (hNp : Summable fun k => (1 + σ * lam k) ^ (-p)) {d : ι → ℝ}
    (hd : ∀ k, |d k| ≤ modeR a1 a2 K c p σ t (lam k)) :
    Summable d ∧
    |∑' k, d k|
      ≤ (σ / t) ^ 2 * (a1 * t ^ 4 * heatMom lam 4 (t / 2) + a2 * t ^ 3 * heatMom lam 3 (t / 2))
        + K * (1 + t / σ) * Real.exp (-(c * (t / σ)))
            * (powSum lam p σ + heatTr lam (t / 4)) := by
  have ht2 : 0 < t / 2 := by linarith
  have ht4 : 0 < t / 4 := by linarith
  have hR : HasSum (fun k => modeR a1 a2 K c p σ t (lam k))
      ((σ / t) ^ 2 * (a1 * t ^ 4 * heatMom lam 4 (t / 2) + a2 * t ^ 3 * heatMom lam 3 (t / 2))
        + K * (1 + t / σ) * Real.exp (-(c * (t / σ)))
            * (powSum lam p σ + heatTr lam (t / 4))) :=
    ((((heatMom_hasSum h 4 ht2).mul_left (a1 * t ^ 4)).add
      ((heatMom_hasSum h 3 ht2).mul_left (a2 * t ^ 3))).mul_left ((σ / t) ^ 2)).add
    ((hNp.hasSum.add (heatTr_hasSum h ht4)).mul_left
      (K * (1 + t / σ) * Real.exp (-(c * (t / σ)))))
  have hs : Summable d :=
    Summable.of_norm_bounded hR.summable (fun k => by rw [Real.norm_eq_abs]; exact hd k)
  refine ⟨hs, ?_⟩
  rw [abs_le]
  constructor
  · exact hasSum_le (fun k => (abs_le.1 (hd k)).1) hR.neg hs.hasSum
  · exact hasSum_le (fun k => (abs_le.1 (hd k)).2) hs.hasSum hR

/-- **`thm:profile`(i) as a statement about a list of eigenvalues, with explicit constants.**
    For `t ≥ σ > 0`, `τ = t/σ`, under `ProfileHyp` and the convergence of `N_p(σ)`:
    `|T^F_σ(t) - Θ(t) - β (σt/2) Θ''(t)| ≤ (σ/t)² [(B²/2) t⁴ Θ''''(t/2) + c₃ t³ |Θ'''(t/2)|]
        + K (1+τ) e^{-cτ} [N_p(σ) + Θ(t/4)]`,
    `B = profB β c₃`, `K = profK β C_F p`, `c = profc u₁ δ`. The series `T^F_σ(t)` converges. -/
theorem profile_i (h : IsSpectrum lam) {F : ℝ → ℝ} {β c3 u1 δ CF p : ℝ}
    (H : ProfileHyp F β c3 u1 δ CF p) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t)
    (hNp : Summable fun k => (1 + σ * lam k) ^ (-p)) :
    Summable (fun k => Real.exp (-(t / σ * (1 - F (σ * lam k)))) - Real.exp (-(t / σ))) ∧
    |profTr lam F σ t - heatTr lam t - β * (σ * t / 2) * heatMom lam 2 t|
      ≤ (σ / t) ^ 2 * (profB β c3 ^ 2 / 2 * t ^ 4 * heatMom lam 4 (t / 2)
            + c3 * t ^ 3 * heatMom lam 3 (t / 2))
        + profK β CF p * (1 + t / σ) * Real.exp (-(profc u1 δ * (t / σ)))
            * (powSum lam p σ + heatTr lam (t / 4)) := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hτ : 1 ≤ t / σ := by rw [le_div_iff₀ hσ]; linarith
  obtain ⟨d, hd_def⟩ : ∃ d : ι → ℝ, d = fun k =>
      Real.exp (-(t / σ * (1 - F (σ * lam k)))) - Real.exp (-(t / σ))
        - Real.exp (-(t * lam k)) - β * (σ * t / 2) * (lam k ^ 2 * Real.exp (-(t * lam k))) :=
    ⟨_, rfl⟩
  have hd : ∀ k, |d k|
      ≤ modeR (profB β c3 ^ 2 / 2) c3 (profK β CF p) (profc u1 δ) p σ t (lam k) := by
    intro k
    have hx : t / σ * (σ * lam k) = t * lam k := by field_simp
    have key := prof_mode H hx hτ (mul_nonneg hσ.le (h.nonneg k))
    rw [modeR_eq ht] at key
    have e : d k = Real.exp (-(t / σ * (1 - F (σ * lam k)))) - Real.exp (-(t / σ))
        - Real.exp (-(t * lam k))
        - β * (t * lam k * (σ * lam k) / 2) * Real.exp (-(t * lam k)) := by
      rw [hd_def]
      ring
    rw [e]
    exact key
  obtain ⟨hs, hb⟩ := sum_modeR h ht hNp hd
  have hΘ := heatTr_hasSum h ht
  have hM := (heatMom_hasSum h 2 ht).mul_left (β * (σ * t / 2))
  have hA : HasSum (fun k => Real.exp (-(t / σ * (1 - F (σ * lam k)))) - Real.exp (-(t / σ)))
      (∑' k, d k + heatTr lam t + β * (σ * t / 2) * heatMom lam 2 t) := by
    convert (hs.hasSum.add hΘ).add hM using 1
    funext k
    rw [hd_def]
    ring
  have e2 : profTr lam F σ t - heatTr lam t - β * (σ * t / 2) * heatMom lam 2 t = ∑' k, d k := by
    unfold profTr
    rw [hA.tsum_eq]
    ring
  rw [e2]
  exact ⟨hA.summable, hb⟩

/-- **`thm:profile`(ii) as a statement about a list of eigenvalues, with explicit constants.**
    For `σ > 0`, an integer `n ≥ 1` and `t = nσ`, under `ProfileHyp` and the convergence of
    `N_p(σ)`:
    `|∑_k F(σλ_k)^n - Θ(t) - (β-1)(σt/2) Θ''(t)|
        ≤ (σ/t)² [(B₂²/2) t⁴ Θ''''(t/2) + c̃ t³ |Θ'''(t/2)|] + K₂ (1+n) e^{-cn} [N_p(σ) + Θ(t/4)]`.
    Nothing is subtracted. (The paper states this for `n ≥ 2`.) -/
theorem profile_ii (h : IsSpectrum lam) {F : ℝ → ℝ} {β c3 u1 δ CF p : ℝ}
    (H : ProfileHyp F β c3 u1 δ CF p) {σ t : ℝ} (hσ : 0 < σ) (n : ℕ) (hn1 : 1 ≤ n)
    (hnt : (n : ℝ) * σ = t) (hNp : Summable fun k => (1 + σ * lam k) ^ (-p)) :
    Summable (fun k => F (σ * lam k) ^ n) ∧
    |discTr lam F σ n - heatTr lam t - (β - 1) * (σ * t / 2) * heatMom lam 2 t|
      ≤ (σ / t) ^ 2 * (profB2 β c3 ^ 2 / 2 * t ^ 4 * heatMom lam 4 (t / 2)
            + profCt β c3 * t ^ 3 * heatMom lam 3 (t / 2))
        + profK2 β CF * (1 + t / σ) * Real.exp (-(profc u1 δ * (t / σ)))
            * (powSum lam p σ + heatTr lam (t / 4)) := by
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have ht : 0 < t := by rw [← hnt]; exact mul_pos (by linarith) hσ
  have hn : (n : ℝ) = t / σ := eq_div_of_mul_eq hσ.ne' hnt
  obtain ⟨d, hd_def⟩ : ∃ d : ι → ℝ, d = fun k =>
      F (σ * lam k) ^ n - Real.exp (-(t * lam k))
        - (β - 1) * (σ * t / 2) * (lam k ^ 2 * Real.exp (-(t * lam k))) :=
    ⟨_, rfl⟩
  have hd : ∀ k, |d k|
      ≤ modeR (profB2 β c3 ^ 2 / 2) (profCt β c3) (profK2 β CF) (profc u1 δ) p σ t (lam k) := by
    intro k
    have hx : t / σ * (σ * lam k) = t * lam k := by field_simp
    have key := prof_mode_disc H n hn1 hn hx (mul_nonneg hσ.le (h.nonneg k))
    rw [modeR_eq ht] at key
    have e : d k = F (σ * lam k) ^ n - Real.exp (-(t * lam k))
        - (β - 1) * (t * lam k * (σ * lam k) / 2) * Real.exp (-(t * lam k)) := by
      rw [hd_def]
      ring
    rw [e]
    exact key
  obtain ⟨hs, hb⟩ := sum_modeR h ht hNp hd
  have hΘ := heatTr_hasSum h ht
  have hM := (heatMom_hasSum h 2 ht).mul_left ((β - 1) * (σ * t / 2))
  have hA : HasSum (fun k => F (σ * lam k) ^ n)
      (∑' k, d k + heatTr lam t + (β - 1) * (σ * t / 2) * heatMom lam 2 t) := by
    convert (hs.hasSum.add hΘ).add hM using 1
    funext k
    rw [hd_def]
    ring
  have e2 : discTr lam F σ n - heatTr lam t - (β - 1) * (σ * t / 2) * heatMom lam 2 t
      = ∑' k, d k := by
    unfold discTr
    rw [hA.tsum_eq]
    ring
  rw [e2]
  exact ⟨hA.summable, hb⟩

end Sums

/-! #### The hypotheses of the paper -/

/-- **The corrected hypotheses of `thm:profile` suffice.** (F1) on `[0, u₀]`, the second part of
    (F2) (`sup_{u ≥ u₁} |F| < 1` for every `u₁ > 0`) and (F3) give `ProfileHyp` with the threshold
    `u₁ = min(u₀, 1/(5|β| + 9c₃ + 18))`, which depends only on `u₀, β, c₃`, and with the `δ`
    that the second part of (F2) provides at this `u₁`. The first part of (F2) is not used. -/
theorem profile_hyp_of_paper {F : ℝ → ℝ} {β c3 u0 CF p : ℝ} (hc : 0 ≤ c3) (hu0 : 0 < u0)
    (hCF : 0 ≤ CF) (hp : 0 ≤ p)
    (hF1 : ∀ u, 0 ≤ u → u ≤ u0 → |F u - (1 - u + β * u ^ 2 / 2)| ≤ c3 * u ^ 3)
    (hF2 : ∀ u1 : ℝ, 0 < u1 → ∃ δ : ℝ, 0 < δ ∧ ∀ u, u1 ≤ u → |F u| ≤ 1 - δ)
    (hF3 : ∀ u, 0 ≤ u → |F u| ≤ CF * (1 + u) ^ (-p)) :
    ∃ δ : ℝ, ProfileHyp F β c3 (min u0 (1 / (5 * |β| + 9 * c3 + 18))) δ CF p := by
  have hD : 0 < 5 * |β| + 9 * c3 + 18 := by have := abs_nonneg β; linarith
  have hu1 : 0 < min u0 (1 / (5 * |β| + 9 * c3 + 18)) := lt_min hu0 (by positivity)
  obtain ⟨δ, hδ, hδF⟩ := hF2 _ hu1
  refine ⟨δ, ⟨hc, hu1, ?_, hδ, hCF, hp, ?_, hδF, hF3⟩⟩
  · calc (5 * |β| + 9 * c3 + 18) * min u0 (1 / (5 * |β| + 9 * c3 + 18))
        ≤ (5 * |β| + 9 * c3 + 18) * (1 / (5 * |β| + 9 * c3 + 18)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hD.le
      _ = 1 := mul_one_div_cancel hD.ne'
  · intro u h0 h1
    exact hF1 u h0 (h1.trans (min_le_left _ _))

/-- **`thm:profile` in the form of the paper** ("there are constants `c, C > 0` such that ..."),
    for lists of eigenvalues: under (F1) on `[0, u₀]`, the second part of (F2) and (F3) there are
    `c, C > 0` such that for every spectrum `lam`, all `t ≥ σ > 0` with `N_p(σ) < ∞`, and
    `𝓡 = C (σ/t)² [t³|Θ'''(t/2)| + t⁴ Θ''''(t/2)] + C (1+τ) e^{-cτ} [N_p(σ) + Θ(t/4)]`:
    (i) `|T^F_σ(t) - Θ(t) - β(σt/2)Θ''(t)| ≤ 𝓡`, and (ii) for every integer `n ≥ 1` with
    `t = nσ`, `|∑_k F(σλ_k)^n - Θ(t) - (β-1)(σt/2)Θ''(t)| ≤ 𝓡`. -/
theorem profile_paper.{v} {F : ℝ → ℝ} {β c3 u0 CF p : ℝ} (hc : 0 ≤ c3) (hu0 : 0 < u0)
    (hCF : 0 ≤ CF) (hp : 0 ≤ p)
    (hF1 : ∀ u, 0 ≤ u → u ≤ u0 → |F u - (1 - u + β * u ^ 2 / 2)| ≤ c3 * u ^ 3)
    (hF2 : ∀ u1 : ℝ, 0 < u1 → ∃ δ : ℝ, 0 < δ ∧ ∀ u, u1 ≤ u → |F u| ≤ 1 - δ)
    (hF3 : ∀ u, 0 ≤ u → |F u| ≤ CF * (1 + u) ^ (-p)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (ι : Type v) (lam : ι → ℝ), IsSpectrum lam →
      ∀ σ t : ℝ, 0 < σ → σ ≤ t → (Summable fun k => (1 + σ * lam k) ^ (-p)) →
        |profTr lam F σ t - heatTr lam t - β * (σ * t / 2) * heatMom lam 2 t|
            ≤ C * ((σ / t) ^ 2 * (t ^ 3 * heatMom lam 3 (t / 2) + t ^ 4 * heatMom lam 4 (t / 2)))
              + C * ((1 + t / σ) * Real.exp (-(c * (t / σ)))
                  * (powSum lam p σ + heatTr lam (t / 4)))
        ∧ ∀ n : ℕ, 1 ≤ n → (n : ℝ) * σ = t →
          |discTr lam F σ n - heatTr lam t - (β - 1) * (σ * t / 2) * heatMom lam 2 t|
            ≤ C * ((σ / t) ^ 2 * (t ^ 3 * heatMom lam 3 (t / 2) + t ^ 4 * heatMom lam 4 (t / 2)))
              + C * ((1 + t / σ) * Real.exp (-(c * (t / σ)))
                  * (powSum lam p σ + heatTr lam (t / 4))) := by
  obtain ⟨δ, H⟩ := profile_hyp_of_paper hc hu0 hCF hp hF1 hF2 hF3
  obtain ⟨hc0, -, -⟩ := profc_facts H.u1_pos H.δ_pos
  have hB0 := profB_nonneg (β := β) hc
  have hCt0 := profCt_nonneg (β := β) hc
  have hB20 := profB2_nonneg (β := β) hc
  have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  have hK0 : 0 ≤ profK β CF p := by
    unfold profK
    have := abs_nonneg β
    linarith
  have hK20 : 0 ≤ profK2 β CF := by
    unfold profK2
    have := abs_nonneg (β - 1)
    linarith
  have hA1 : 0 ≤ profB β c3 ^ 2 / 2 := by positivity
  have hA2 : 0 ≤ profB2 β c3 ^ 2 / 2 := by positivity
  refine ⟨profc (min u0 (1 / (5 * |β| + 9 * c3 + 18))) δ, profB β c3 ^ 2 / 2 + c3 + profK β CF p + profB2 β c3 ^ 2 / 2
    + profCt β c3 + profK2 β CF + 1, hc0, by linarith, ?_⟩
  intro ι lam h σ t hσ hts hNp
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hm3 : 0 ≤ (σ / t) ^ 2 * (t ^ 3 * heatMom lam 3 (t / 2)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (heatMom_nonneg h 3 _))
  have hm4 : 0 ≤ (σ / t) ^ 2 * (t ^ 4 * heatMom lam 4 (t / 2)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (heatMom_nonneg h 4 _))
  have hX : 0 ≤ (1 + t / σ) * Real.exp (-(profc (min u0 (1 / (5 * |β| + 9 * c3 + 18))) δ * (t / σ)))
      * (powSum lam p σ + heatTr lam (t / 4)) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (add_nonneg (powSum_nonneg h hσ.le p) (heatTr_nonneg _))
  constructor
  · refine (profile_i h H hσ hts hNp).2.trans ?_
    have q1 := mul_nonneg hA1 hm4
    have q2 := mul_nonneg hc hm3
    have q3 := mul_nonneg hK0 hX
    have q4 := mul_nonneg (show 0 ≤ c3 + profK β CF p + profB2 β c3 ^ 2 / 2
      + profCt β c3 + profK2 β CF + 1 by linarith) hm4
    have q5 := mul_nonneg (show 0 ≤ profB β c3 ^ 2 / 2 + profK β CF p + profB2 β c3 ^ 2 / 2
      + profCt β c3 + profK2 β CF + 1 by linarith) hm3
    have q6 := mul_nonneg (show 0 ≤ profB β c3 ^ 2 / 2 + c3 + profB2 β c3 ^ 2 / 2
      + profCt β c3 + profK2 β CF + 1 by linarith) hX
    linarith
  · intro n hn1 hnt
    refine (profile_ii h H hσ n hn1 hnt hNp).2.trans ?_
    have q4 := mul_nonneg (show 0 ≤ profB β c3 ^ 2 / 2 + c3 + profK β CF p
      + profCt β c3 + profK2 β CF + 1 by linarith) hm4
    have q5 := mul_nonneg (show 0 ≤ profB β c3 ^ 2 / 2 + c3 + profK β CF p
      + profB2 β c3 ^ 2 / 2 + profK2 β CF + 1 by linarith) hm3
    have q6 := mul_nonneg (show 0 ≤ profB β c3 ^ 2 / 2 + c3 + profK β CF p
      + profB2 β c3 ^ 2 / 2 + profCt β c3 + 1 by linarith) hX
    linarith


/-- The hypotheses `ProfileHyp` are satisfiable: the Gaussian profile `F(u) = e^{-u}` of the
    exactly solvable case, with `β = 1`, `c₃ = 1/6`, `u₁ = 1/25`, `δ = 1 - e^{-1/25}`, `C_F = 2`,
    `p = 2`. (For this `F`, `profile_i` is a weaker form of `PopulationRate.rate_iii`, and
    `profile_ii` has the coefficient `β - 1 = 0`, in agreement with `discTr_exact`.) -/
theorem profileHyp_gauss :
    ProfileHyp (fun u => Real.exp (-u)) 1 (1 / 6) (1 / 25) (1 - Real.exp (-(1 / 25))) 2 2 where
  c3_nonneg := by norm_num
  u1_pos := by norm_num
  small := by rw [abs_one]; norm_num
  δ_pos := by
    have h : Real.exp (-(1 / 25)) < Real.exp 0 := Real.exp_lt_exp.2 (by norm_num)
    rw [Real.exp_zero] at h
    linarith
  CF_nonneg := by norm_num
  p_nonneg := by norm_num
  F1 := fun u hu _ => by
    show |Real.exp (-u) - (1 - u + 1 * u ^ 2 / 2)| ≤ 1 / 6 * u ^ 3
    have t3 := real_isExp3.taylor3 u hu
    have t2 := real_isExp2.taylor_nonpos (-u) (by linarith)
    rw [abs_le]
    constructor
    · linarith
    · linarith
  F2 := fun u hu => by
    show |Real.exp (-u)| ≤ 1 - (1 - Real.exp (-(1 / 25)))
    rw [abs_of_pos (Real.exp_pos _)]
    have h : Real.exp (-u) ≤ Real.exp (-(1 / 25)) := Real.exp_le_exp.2 (by linarith)
    linarith
  F3 := fun u hu => by
    show |Real.exp (-u)| ≤ 2 * (1 + u) ^ (-(2 : ℝ))
    rw [abs_of_pos (Real.exp_pos _)]
    have h1 : (0 : ℝ) < 1 + u := by linarith
    have quad := Real.quadratic_le_exp_of_nonneg hu
    have e1 : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    have h2 : (1 + u) ^ 2 ≤ 2 * Real.exp u := by nlinarith
    rw [Real.rpow_neg h1.le, Real.rpow_two, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc Real.exp (-u) * (1 + u) ^ 2 ≤ Real.exp (-u) * (2 * Real.exp u) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = 2 * (Real.exp (-u) * Real.exp u) := by ring
      _ = 2 := by rw [e1]; ring


/-! #### Negative control: the second part of (F2) cannot be dropped

The function `badF(u) = 1 - u + 5u² - (9/2)u³` on `[0,1]`, `0` on `(1,∞)`, satisfies (F1) on
`[0,1]` with `β = 10`, `c₃ = 9/2` (`badF_F1`), the FIRST part of (F2) with `u₀ = 1`, `δ = 1/2`
(`badF_F2`) and (F3) with `C_F = 12·2^p` (`badF_F3`), but `badF(3/5) = 307/250 > 1`. For the
one-element spectrum `{3/5}` and `σ = 1` the conclusion (i) of `thm:profile`, in the form of
`profile_paper`, fails for every choice of the constants (`profile_F2_fails`): the left side
grows like `e^{57t/250}`, the right side is bounded by a polynomial in `t`. This is the
counterexample recorded in the proof of the paper (core file: `profile_F2_needed`), as a formal
statement about the sums. -/

/-- The profile function of the negative control. -/
noncomputable def badF (u : ℝ) : ℝ := if u ≤ 1 then 1 - u + 5 * u ^ 2 - 9 / 2 * u ^ 3 else 0

theorem badF_F1 (u : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    |badF u - (1 - u + 10 * u ^ 2 / 2)| ≤ 9 / 2 * u ^ 3 := by
  unfold badF
  rw [if_pos hu1]
  have e : 1 - u + 5 * u ^ 2 - 9 / 2 * u ^ 3 - (1 - u + 10 * u ^ 2 / 2) = -(9 / 2 * u ^ 3) := by
    ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) (pow_nonneg hu 3))]

theorem badF_F2 (u : ℝ) (hu : 1 ≤ u) : |badF u| ≤ 1 - 1 / 2 := by
  unfold badF
  rcases eq_or_lt_of_le hu with h | h
  · rw [← h, if_pos le_rfl]
    have e : (1 : ℝ) - 1 + 5 * 1 ^ 2 - 9 / 2 * 1 ^ 3 = 1 / 2 := by norm_num
    rw [e, abs_of_pos (by norm_num)]
    norm_num
  · rw [if_neg (not_le.2 h), abs_zero]
    norm_num

theorem badF_F3 {p : ℝ} (hp : 0 ≤ p) (u : ℝ) (hu : 0 ≤ u) :
    |badF u| ≤ 12 * (2 : ℝ) ^ p * (1 + u) ^ (-p) := by
  have h2p : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  have hG : 0 ≤ (1 + u) ^ (-p) := Real.rpow_nonneg (by linarith) _
  unfold badF
  split_ifs with h
  · have wl := weight_low hu h hp
    have hu2 : u ^ 2 ≤ 1 := pow_le_one₀ hu h
    have hu3 : u ^ 3 ≤ 1 := pow_le_one₀ hu h
    have hu2' : 0 ≤ u ^ 2 := pow_two_nonneg u
    have hu3' : 0 ≤ u ^ 3 := pow_nonneg hu 3
    have habs : |1 - u + 5 * u ^ 2 - 9 / 2 * u ^ 3| ≤ 12 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    calc |1 - u + 5 * u ^ 2 - 9 / 2 * u ^ 3| ≤ 12 * 1 := by linarith
      _ ≤ 12 * ((2 : ℝ) ^ p * (1 + u) ^ (-p)) := mul_le_mul_of_nonneg_left wl (by norm_num)
      _ = 12 * (2 : ℝ) ^ p * (1 + u) ^ (-p) := by ring
  · rw [abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) h2p) hG

theorem badF_value : badF (1 * (3 / 5)) = 307 / 250 := by
  unfold badF
  rw [if_pos (by norm_num)]
  norm_num

/-- The one-element list `{3/5}` is a spectrum in the sense of `IsSpectrum`. -/
theorem unit_isSpectrum : IsSpectrum (fun _ : Unit => (3 / 5 : ℝ)) where
  nonneg := fun _ => by norm_num
  summable := fun _ _ => (hasSum_fintype _).summable

/-- **Negative control.** For `badF` (which satisfies (F1), the first part of (F2) and (F3)), the
    spectrum `{3/5}` and `σ = 1`, there are no constants `c, C > 0` for which the bound (i) of
    `profile_paper` (with `β = 10`) holds for all `t ≥ 1 = σ`. -/
theorem profile_F2_fails (p : ℝ) :
    ¬ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      |profTr (fun _ : Unit => (3 / 5 : ℝ)) badF 1 t - heatTr (fun _ : Unit => (3 / 5 : ℝ)) t
          - 10 * (1 * t / 2) * heatMom (fun _ : Unit => (3 / 5 : ℝ)) 2 t|
        ≤ C * ((1 / t) ^ 2 * (t ^ 3 * heatMom (fun _ : Unit => (3 / 5 : ℝ)) 3 (t / 2)
              + t ^ 4 * heatMom (fun _ : Unit => (3 / 5 : ℝ)) 4 (t / 2)))
          + C * ((1 + t / 1) * Real.exp (-(c * (t / 1)))
              * (powSum (fun _ : Unit => (3 / 5 : ℝ)) p 1
                  + heatTr (fun _ : Unit => (3 / 5 : ℝ)) (t / 4))) := by
  rintro ⟨c, C, hc, hC, hall⟩
  have ev : ∀ f : Unit → ℝ, ∑' k, f k = f () := fun f => by
    rw [tsum_fintype]; simp
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (1 + 1 * (3 / 5 : ℝ)) ^ (-p) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg (by norm_num) _
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (57 / 250) ^ 3 / 6 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; norm_num
  have hCP : 0 ≤ C * (P + 1) := mul_nonneg hC.le (by linarith)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = C + 2 * (C * (P + 1)) + 4 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; linarith
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = b / a + 1 := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hT]; have := div_pos hb0 ha0; linarith
  have hT0 : 0 < T := by linarith
  have hTne : T ≠ 0 := hT0.ne'
  have hane : a ≠ 0 := ha0.ne'
  have hTa : b < a * T := by
    have e : a * (b / a + 1) = b + a := by field_simp
    rw [hT, e]
    linarith
  have key := hall T hT1
  simp only [profTr, heatTr, heatMom, powSum, ev] at key
  rw [badF_value, ← hP] at key
  -- the exponentials
  have hx0 : (0 : ℝ) ≤ 57 / 250 * T := by positivity
  have h3 := Real.pow_div_factorial_le_exp (57 / 250 * T) hx0 3
  have e6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [e6] at h3
  have eA : -(T / 1 * (1 - 307 / 250)) = 57 / 250 * T := by ring
  rw [eA] at key
  have hEt : Real.exp (-(T / 1)) ≤ 1 := Real.exp_le_one_iff.2 (by rw [div_one]; linarith)
  have hEb : Real.exp (-(T * (3 / 5))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE2 : Real.exp (-(T / 2 * (3 / 5))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hE4 : Real.exp (-(T / 4 * (3 / 5))) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hEc : Real.exp (-(c * (T / 1))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by rw [div_one]; have := mul_pos hc hT0; linarith)
  have pEb := Real.exp_pos (-(T * (3 / 5)))
  have pE2 := Real.exp_pos (-(T / 2 * (3 / 5)))
  have pE4 := Real.exp_pos (-(T / 4 * (3 / 5)))
  have pEc := Real.exp_pos (-(c * (T / 1)))
  have hTT : T ≤ T ^ 2 := by nlinarith
  have h1T : 1 ≤ T ^ 2 := by nlinarith
  -- lower bound for the left side
  have l1 : 10 * (1 * T / 2) * ((3 / 5) ^ 2 * Real.exp (-(T * (3 / 5)))) ≤ 9 / 5 * T := by
    have := mul_le_mul_of_nonneg_left hEb (show (0 : ℝ) ≤ 9 / 5 * T by positivity)
    linarith
  have l2 := le_abs_self (Real.exp (57 / 250 * T) - Real.exp (-(T / 1)) - Real.exp (-(T * (3 / 5)))
    - 10 * (1 * T / 2) * ((3 / 5) ^ 2 * Real.exp (-(T * (3 / 5)))))
  -- upper bound for the right side
  have i1 : (1 / T) ^ 2 * T ^ 3 = T := by field_simp
  have i2 : (1 / T) ^ 2 * T ^ 4 = T ^ 2 := by field_simp
  have r1 : (1 / T) ^ 2 * (T ^ 3 * ((3 / 5) ^ 3 * Real.exp (-(T / 2 * (3 / 5))))
        + T ^ 4 * ((3 / 5) ^ 4 * Real.exp (-(T / 2 * (3 / 5))))) ≤ T ^ 2 := by
    have e : (1 / T) ^ 2 * (T ^ 3 * ((3 / 5) ^ 3 * Real.exp (-(T / 2 * (3 / 5))))
          + T ^ 4 * ((3 / 5) ^ 4 * Real.exp (-(T / 2 * (3 / 5)))))
        = ((1 / T) ^ 2 * T ^ 3 * (3 / 5) ^ 3 + (1 / T) ^ 2 * T ^ 4 * (3 / 5) ^ 4)
            * Real.exp (-(T / 2 * (3 / 5))) := by ring
    rw [e, i1, i2]
    have h := mul_le_mul_of_nonneg_left hE2
      (show (0 : ℝ) ≤ T * (3 / 5) ^ 3 + T ^ 2 * (3 / 5) ^ 4 by positivity)
    nlinarith
  have r2 : (1 + T / 1) * Real.exp (-(c * (T / 1))) * (P + Real.exp (-(T / 4 * (3 / 5))))
      ≤ 2 * T ^ 2 * (P + 1) := by
    have h1 : (1 + T / 1) * Real.exp (-(c * (T / 1))) ≤ 2 * T ^ 2 := by
      have := mul_le_mul_of_nonneg_left hEc (show (0 : ℝ) ≤ 1 + T / 1 by positivity)
      rw [div_one] at this ⊢
      linarith
    exact mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  have r1' := mul_le_mul_of_nonneg_left r1 hC.le
  have r2' := mul_le_mul_of_nonneg_left r2 hC.le
  -- the cubic beats the quadratic
  have hcub : b * T ^ 2 < (57 / 250 * T) ^ 3 / 6 := by
    have e : (57 / 250 * T) ^ 3 / 6 = a * T * T ^ 2 := by rw [ha]; ring
    rw [e]
    exact mul_lt_mul_of_pos_right hTa (by positivity)
  have hbT : C * T ^ 2 + C * (2 * T ^ 2 * (P + 1)) + 4 * T ^ 2 = b * T ^ 2 := by
    rw [hb]; ring
  linarith


/-! #### Part A: the trace in discrete time (`prop:discrete`), deterministic part

`prop:discrete` is a statement about the sampled graph ("in the situation of `thm:trace`", almost
surely for large `N`). What is formalised here is the deterministic content of its proof, for an
arbitrary real symmetric matrix `S` whose eigenvalues `s_a` lie in `[-1 + κ₀, 1]`, with the low
modes `1 - s_a < κ` (`κ ≤ 1/2`) and `k = j + 2 ≥ 2` steps:
* `discrete_trace_matrix`: `|Tr S^k - ∑_low e^{-k(1 - s_a)}| ≤ ∑_low k (1 - s_a)² e^{-k(1 - s_a)}
    + (1 - min(κ, κ₀))^{k-2} Tr S²` (no hypothesis beyond the location of the spectrum; here
  `k(1 - s_a) = t λ^N_a` in the notation of the paper, `t = kσ`, and `Tr S^k = Tr P^k`);
* `discrete_trace_conditional`: if in addition, for the low modes, numbers `μ_a ≥ 0` (in the paper
  `μ_a = t λ_a`) satisfy `|k(1 - s_a) - μ_a| ≤ ε μ_a` and `c μ_a ≤ k(1 - s_a)` with `c ≤ 1`
  (HYPOTHESES; in the paper they come from `thm:eig`, equation `eq:eiglow`), then
  `|Tr S^k - ∑_low e^{-μ_a}| ≤ (8/k) ∑_low e^{-c μ_a/2} + ε ∑_low μ_a e^{-c μ_a}
      + (1 - min(κ, κ₀))^{k-2} Tr S²`.
  With `1/k = σ/t` the first term is the term `ξ²/t` of the proof of the paper (constant `8`
  instead of the sharp `16/e²`).
The population counterpart, `∑_k F(σλ_k)^n` against `Θ(nσ)` with the coefficient `β - 1`, is
`profile_ii`; in the exactly solvable case `F = e^{-u}` it is the identity
`PopulationRate.heatTr_pow`, restated as `discTr_exact`.

NOT formalised: everything probabilistic in `prop:discrete` (the eigenvalue estimates of `thm:eig`
for the low modes, the bound `Tr S² ≤ C ξ^{-d}`, the continuum modes beyond the low ones, the
resulting rate `ε_N/ξ_N + ξ_N/√t + k^{d/2} e^{-κk}`, "almost surely for all large `N`"). -/

/-- `discrete_low_mode` of the core file for the real exponential:
    `0 ≤ e^{-kv} - (1 - v)^k ≤ k v² e^{-kv}` for `0 ≤ v ≤ 1/2`. -/
theorem real_discrete_low {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2) (k : ℕ) :
    0 ≤ Real.exp (-((k : ℝ) * v)) - (1 - v) ^ k ∧
    Real.exp (-((k : ℝ) * v)) - (1 - v) ^ k
      ≤ (k : ℝ) * (v * v) * Real.exp (-((k : ℝ) * v)) := by
  have h := CTG.HeatTrace.discrete_low_mode real_isExp real_archimedean hv0 hv1 k
  rw [ncast_eq, pw_eq] at h
  exact h

/-- The splitting of `∑_a s_a^k` into low and high modes, for a finite family of numbers. -/
theorem discrete_sum {ι : Type*} [Fintype ι] (s : ι → ℝ) {κ κ0 : ℝ} (hκ : κ ≤ 1 / 2)
    (h1 : ∀ a, s a ≤ 1) (h0 : ∀ a, -1 + κ0 ≤ s a) (j : ℕ) :
    |∑ a, s a ^ (j + 2)
        - ∑ a ∈ Finset.univ.filter (fun a => 1 - s a < κ),
            Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - s a)))|
      ≤ ∑ a ∈ Finset.univ.filter (fun a => 1 - s a < κ),
            ((j + 2 : ℕ) : ℝ) * ((1 - s a) * (1 - s a))
              * Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - s a)))
        + (1 - min κ κ0) ^ j * ∑ a, s a ^ 2 := by
  have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => 1 - s a < κ)
    (fun a => s a ^ (j + 2))).symm
  have hlow1 : ∑ a ∈ Finset.univ.filter (fun a => 1 - s a < κ), s a ^ (j + 2)
      ≤ ∑ a ∈ Finset.univ.filter (fun a => 1 - s a < κ),
          Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - s a))) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hlt := (Finset.mem_filter.1 ha).2
    have h := (real_discrete_low (v := 1 - s a) (by linarith [h1 a]) (by linarith) (j + 2)).1
    rw [sub_sub_cancel] at h
    linarith
  have hlow2 : ∑ a ∈ Finset.univ.filter (fun a => 1 - s a < κ),
        Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - s a)))
      ≤ ∑ a ∈ Finset.univ.filter (fun a => 1 - s a < κ), s a ^ (j + 2)
        + ∑ a ∈ Finset.univ.filter (fun a => 1 - s a < κ),
            ((j + 2 : ℕ) : ℝ) * ((1 - s a) * (1 - s a))
              * Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - s a))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a ha => ?_
    have hlt := (Finset.mem_filter.1 ha).2
    have h := (real_discrete_low (v := 1 - s a) (by linarith [h1 a]) (by linarith) (j + 2)).2
    rw [sub_sub_cancel] at h
    linarith
  have hϑ : 0 ≤ 1 - min κ κ0 := by have := min_le_left κ κ0; linarith
  have hhigh : |∑ a ∈ Finset.univ.filter (fun a => ¬ (1 - s a < κ)), s a ^ (j + 2)|
      ≤ (1 - min κ κ0) ^ j * ∑ a, s a ^ 2 := by
    calc |∑ a ∈ Finset.univ.filter (fun a => ¬ (1 - s a < κ)), s a ^ (j + 2)|
        ≤ ∑ a ∈ Finset.univ.filter (fun a => ¬ (1 - s a < κ)), |s a ^ (j + 2)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.univ.filter (fun a => ¬ (1 - s a < κ)),
            (1 - min κ κ0) ^ j * s a ^ 2 := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hge := not_lt.1 (Finset.mem_filter.1 ha).2
          have habs : |s a| ≤ 1 - min κ κ0 :=
            abs_le.2 ⟨by linarith [h0 a, min_le_right κ κ0], by linarith [min_le_left κ κ0]⟩
          rw [abs_pow, pow_add, sq_abs]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) habs j)
            (pow_two_nonneg _)
      _ = (1 - min κ κ0) ^ j
            * ∑ a ∈ Finset.univ.filter (fun a => ¬ (1 - s a < κ)), s a ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ (1 - min κ κ0) ^ j * ∑ a, s a ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun a _ _ => pow_two_nonneg _)) (pow_nonneg hϑ j)
  obtain ⟨g1, g2⟩ := abs_le.1 hhigh
  rw [hsplit, abs_le]
  constructor
  · linarith
  · linarith

/-- **`prop:discrete`, deterministic splitting, for a real symmetric matrix.** Eigenvalues in
    `[-1 + κ₀, 1]`, low modes `1 - s_a < κ ≤ 1/2`, `k = j + 2`:
    `|Tr S^k - ∑_low e^{-k(1-s_a)}| ≤ ∑_low k(1-s_a)² e^{-k(1-s_a)} + (1 - min(κ,κ₀))^{k-2} Tr S²`. -/
theorem discrete_trace_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {κ κ0 : ℝ} (hκ : κ ≤ 1 / 2) (h1 : ∀ i, hS.eigenvalues i ≤ 1)
    (h0 : ∀ i, -1 + κ0 ≤ hS.eigenvalues i) (j : ℕ) :
    |(S ^ (j + 2)).trace
        - ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
            Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - hS.eigenvalues i)))|
      ≤ ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
            ((j + 2 : ℕ) : ℝ) * ((1 - hS.eigenvalues i) * (1 - hS.eigenvalues i))
              * Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - hS.eigenvalues i)))
        + (1 - min κ κ0) ^ j * (S ^ 2).trace := by
  rw [trace_pow_eq_sum_eigenvalues S hS (j + 2), trace_pow_eq_sum_eigenvalues S hS 2]
  exact discrete_sum hS.eigenvalues hκ h1 h0 j

/-- One low mode against a reference value `μ` (`z = k v = t λ^N`, `μ = t λ`). -/
theorem discrete_low_conditional {k : ℕ} (hk : 0 < k) {v μ ε c : ℝ} (hv : 0 ≤ v) (hc1 : c ≤ 1)
    (hμ : 0 ≤ μ) (heig : |(k : ℝ) * v - μ| ≤ ε * μ) (hlow : c * μ ≤ (k : ℝ) * v) :
    (k : ℝ) * (v * v) * Real.exp (-((k : ℝ) * v)) ≤ 8 / (k : ℝ) * Real.exp (-(c * μ / 2)) ∧
    |Real.exp (-((k : ℝ) * v)) - Real.exp (-μ)| ≤ ε * (μ * Real.exp (-(c * μ))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk
  have hz : 0 ≤ (k : ℝ) * v := mul_nonneg hk0.le hv
  constructor
  · have quad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ (k : ℝ) * v / 2 by linarith)
    have hE := Real.exp_pos (-((k : ℝ) * v / 2))
    have e1 : Real.exp ((k : ℝ) * v / 2) * Real.exp (-((k : ℝ) * v / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have e2 : Real.exp (-((k : ℝ) * v)) = Real.exp (-((k : ℝ) * v / 2))
        * Real.exp (-((k : ℝ) * v / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h8 : ((k : ℝ) * v) ^ 2 ≤ 8 * Real.exp ((k : ℝ) * v / 2) := by
      nlinarith [pow_two_nonneg ((k : ℝ) * v / 2)]
    have h9 : ((k : ℝ) * v) ^ 2 * Real.exp (-((k : ℝ) * v))
        ≤ 8 * Real.exp (-((k : ℝ) * v / 2)) :=
      calc ((k : ℝ) * v) ^ 2 * Real.exp (-((k : ℝ) * v))
          = ((k : ℝ) * v) ^ 2 * (Real.exp (-((k : ℝ) * v / 2))
              * Real.exp (-((k : ℝ) * v / 2))) := by rw [e2]
        _ ≤ 8 * Real.exp ((k : ℝ) * v / 2) * (Real.exp (-((k : ℝ) * v / 2))
              * Real.exp (-((k : ℝ) * v / 2))) :=
            mul_le_mul_of_nonneg_right h8 (mul_nonneg hE.le hE.le)
        _ = 8 * Real.exp (-((k : ℝ) * v / 2))
              * (Real.exp ((k : ℝ) * v / 2) * Real.exp (-((k : ℝ) * v / 2))) := by ring
        _ = 8 * Real.exp (-((k : ℝ) * v / 2)) := by rw [e1]; ring
    have h10 : Real.exp (-((k : ℝ) * v / 2)) ≤ Real.exp (-(c * μ / 2)) :=
      Real.exp_le_exp.2 (by linarith)
    calc (k : ℝ) * (v * v) * Real.exp (-((k : ℝ) * v))
        = (((k : ℝ) * v) ^ 2 * Real.exp (-((k : ℝ) * v))) / (k : ℝ) := by
          field_simp
      _ ≤ (8 * Real.exp (-(c * μ / 2))) / (k : ℝ) :=
          div_le_div_of_nonneg_right (h9.trans (by linarith)) hk0.le
      _ = 8 / (k : ℝ) * Real.exp (-(c * μ / 2)) := by ring
  · have h := abs_exp_neg_sub ((k : ℝ) * v) μ
    have hmin : c * μ ≤ min ((k : ℝ) * v) μ :=
      le_min hlow (by nlinarith [mul_nonneg (sub_nonneg.2 hc1) hμ])
    have hE : Real.exp (-(min ((k : ℝ) * v) μ)) ≤ Real.exp (-(c * μ)) :=
      Real.exp_le_exp.2 (by linarith)
    calc |Real.exp (-((k : ℝ) * v)) - Real.exp (-μ)|
        ≤ |(k : ℝ) * v - μ| * Real.exp (-(min ((k : ℝ) * v) μ)) := h
      _ ≤ (ε * μ) * Real.exp (-(c * μ)) :=
          mul_le_mul heig hE (Real.exp_pos _).le ((abs_nonneg _).trans heig)
      _ = ε * (μ * Real.exp (-(c * μ))) := by ring

/-- **`prop:discrete`, conditional form for a real symmetric matrix.** HYPOTHESES `heig`, `hlow`:
    the low eigenvalues are close to reference values `μ_a` (in the paper `μ_a = tλ_a`, from
    `thm:eig`). Then `Tr S^k` differs from `∑_low e^{-μ_a}` by at most
    `(8/k) ∑_low e^{-cμ_a/2} + ε ∑_low μ_a e^{-cμ_a} + (1 - min(κ,κ₀))^{k-2} Tr S²`, `k = j+2`. -/
theorem discrete_trace_conditional {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {κ κ0 ε c : ℝ} (hκ : κ ≤ 1 / 2) (h1 : ∀ i, hS.eigenvalues i ≤ 1)
    (h0 : ∀ i, -1 + κ0 ≤ hS.eigenvalues i) (j : ℕ) (hc1 : c ≤ 1) (mu : n → ℝ)
    (hmu : ∀ i, 1 - hS.eigenvalues i < κ → 0 ≤ mu i)
    (heig : ∀ i, 1 - hS.eigenvalues i < κ →
      |((j + 2 : ℕ) : ℝ) * (1 - hS.eigenvalues i) - mu i| ≤ ε * mu i)
    (hlow : ∀ i, 1 - hS.eigenvalues i < κ →
      c * mu i ≤ ((j + 2 : ℕ) : ℝ) * (1 - hS.eigenvalues i)) :
    |(S ^ (j + 2)).trace
        - ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ), Real.exp (-(mu i))|
      ≤ 8 / ((j + 2 : ℕ) : ℝ)
            * ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
                Real.exp (-(c * mu i / 2))
        + ε * ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
                mu i * Real.exp (-(c * mu i))
        + (1 - min κ κ0) ^ j * (S ^ 2).trace := by
  have hdet := discrete_trace_matrix S hS hκ h1 h0 j
  have hk : 0 < j + 2 := by omega
  have hA : ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
        ((j + 2 : ℕ) : ℝ) * ((1 - hS.eigenvalues i) * (1 - hS.eigenvalues i))
          * Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - hS.eigenvalues i)))
      ≤ 8 / ((j + 2 : ℕ) : ℝ)
          * ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
              Real.exp (-(c * mu i / 2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hlt := (Finset.mem_filter.1 hi).2
    exact (discrete_low_conditional hk (by linarith [h1 i]) hc1 (hmu i hlt) (heig i hlt)
      (hlow i hlt)).1
  have hB : |∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
          Real.exp (-(((j + 2 : ℕ) : ℝ) * (1 - hS.eigenvalues i)))
        - ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ), Real.exp (-(mu i))|
      ≤ ε * ∑ i ∈ Finset.univ.filter (fun i => 1 - hS.eigenvalues i < κ),
          mu i * Real.exp (-(c * mu i)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hlt := (Finset.mem_filter.1 hi).2
    exact (discrete_low_conditional hk (by linarith [h1 i]) hc1 (hmu i hlt) (heig i hlt)
      (hlow i hlt)).2
  obtain ⟨a1, a2⟩ := abs_le.1 hdet
  obtain ⟨b1, b2⟩ := abs_le.1 hB
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The exactly solvable case in discrete time (`thm:rate`(i), second statement; first consequence
    drawn after `thm:rate`): for `F(u) = e^{-u}`, `∑_k F(σλ_k)^n = Θ(nσ)` exactly, `n ≥ 1`. -/
theorem discTr_exact {ι : Type*} {lam : ι → ℝ} (h : IsSpectrum lam) {σ : ℝ} (hσ : 0 < σ)
    (j : ℕ) :
    discTr lam (fun u => Real.exp (-u)) σ (j + 1) = heatTr lam (((j + 1 : ℕ) : ℝ) * σ) :=
  (heatTr_pow h hσ j).tsum_eq


/-! #### Part C: `prop:heatbounds` for real symmetric matrices

`Tr e^{-tL} = Tr exp(τ(S - 1))`, `m_1 = Tr S`, `m_2 = Tr S²`, `p_i = S_ii`, `N` the size of the
matrix. Already in the second Lean file: `heat_lower_matrix` (`N e^{-τ} ≤ Tr e^{-tL}` for
`Tr S ≥ 0`), `heat_two_term_matrix` (`e^{-τ}(N + τ Tr S) ≤ Tr e^{-tL}`, i.e. the identity of (ii)
with the non-negativity of the twice-subtracted trace), `heat_upper_matrix` (`Tr e^{-tL} ≤ N`),
`normalised_eigenvalues_mem` (`s_a ∈ [-1, 1]` for the normalised graph matrix). Added here:
* `heat_chain_first`, `heat_chain_second`, `heat_chain_third`: the first three inequalities of the
  chain `eq:chain`,
  `N e^{-τ} ≤ N exp(-τ(1 - m_1/N)) ≤ ∑_i e^{-τ(1 - p_i)} ≤ Tr e^{-tL}`
  (the third one through the diagonal of the matrix exponential in the eigenbasis and Jensen's
  inequality with the weights `|v_a(i)|²`; it holds for every real symmetric `S` and every real
  `τ`); `heat_chain` collects the whole chain;
* `heat_twice_subtracted_matrix`: both bounds of `eq:twoterm`,
  `(τ²/2) e^{-2τ} m_2 ≤ Tr e^{-tL} - e^{-τ}(N + τ m_1) ≤ (τ²/2) m_2` for `τ ≥ 0` and
  eigenvalues in `[-1, 1]` (the lower bound with `e^{-2τ}` was not in the Lean files before);
* `heat_antitone_matrix`, `heat_logconvex_midpoint`: part (iii): nonincreasing in `τ` (for
  eigenvalues `≤ 1`), and `Tr e^{-t L}` at the midpoint `(τ₁+τ₂)/2` squared is at most the product
  of the values at `τ₁` and `τ₂` (Cauchy--Schwarz). Midpoint log-convexity only: the convexity of
  `log Tr e^{-tL}` for all weights (which follows with continuity, or by Hölder) is NOT stated.
The hypothesis "eigenvalues in `[-1, 1]`" is not derived here from "`W` symmetric, non-negative,
positive row sums"; that is `normalised_eigenvalues_mem` of the second file. -/

/-- `e^z (1 - z) ≤ 1 - z²/2` for `z ≥ 0`; equivalently `e^x - 1 - x ≥ (x²/2) e^x` for `x ≤ 0`. -/
theorem exp_neg_second_lower {z : ℝ} (hz : 0 ≤ z) :
    z ^ 2 / 2 * Real.exp (-z) ≤ Real.exp (-z) - 1 + z := by
  have hE := Real.exp_pos (-z)
  rcases le_total (z ^ 2) 2 with h | h
  · have t3 := real_isExp3.taylor3 z hz
    have hq : (1 - z + z * z / 2 - z * z * z / 6) * (1 - z ^ 2 / 2)
        = 1 - z + z ^ 3 * ((z - 3 / 2) ^ 2 + 7 / 4) / 12 := by ring
    have h1 := mul_le_mul_of_nonneg_right t3 (show 0 ≤ 1 - z ^ 2 / 2 by linarith)
    have h2 : 0 ≤ z ^ 3 * ((z - 3 / 2) ^ 2 + 7 / 4) / 12 := by positivity
    rw [hq] at h1
    linarith
  · have quad := Real.quadratic_le_exp_of_nonneg hz
    have e1 : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    have hz1 : 1 ≤ z := by nlinarith
    have h1 : Real.exp (-z) * (1 + z + z ^ 2 / 2) ≤ 1 := by
      have := mul_le_mul_of_nonneg_left quad hE.le
      linarith
    have h2 : z ^ 2 / 2 - 1 ≤ (z - 1) * (1 + z + z ^ 2 / 2) := by
      have : 0 ≤ z ^ 3 := pow_nonneg hz 3
      nlinarith
    have h3 := mul_le_mul_of_nonneg_left h2 hE.le
    have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ z - 1 by linarith)
    linarith

/-- `φ(x) = e^x - 1 - x` for `|x| ≤ τ`: `(x²/2) e^{-τ} ≤ φ(x) ≤ (x²/2) e^{τ}`. -/
theorem phi_two_sided {x τ : ℝ} (h1 : -τ ≤ x) (h2 : x ≤ τ) :
    x ^ 2 / 2 * Real.exp (-τ) ≤ Real.exp x - 1 - x ∧
    Real.exp x - 1 - x ≤ x ^ 2 / 2 * Real.exp τ := by
  have hx2 : 0 ≤ x ^ 2 / 2 := by positivity
  have hτ : 0 ≤ τ := by linarith
  have hEm : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hEp : 1 ≤ Real.exp τ := Real.one_le_exp hτ
  rcases le_total 0 x with h | h
  · constructor
    · have quad := Real.quadratic_le_exp_of_nonneg h
      have := mul_le_mul_of_nonneg_left hEm hx2
      linarith
    · have t := real_isExp2.taylor_nonneg x h
      have hm : Real.exp x ≤ Real.exp τ := Real.exp_le_exp.2 h2
      have := mul_le_mul_of_nonneg_left hm hx2
      linarith
  · constructor
    · have l := exp_neg_second_lower (z := -x) (by linarith)
      rw [neg_neg] at l
      have hm : Real.exp (-τ) ≤ Real.exp x := Real.exp_le_exp.2 h1
      have := mul_le_mul_of_nonneg_left hm hx2
      have e : (-x) ^ 2 = x ^ 2 := by ring
      rw [e] at l
      linarith
    · have t := real_isExp2.taylor_nonpos x h
      have := mul_le_mul_of_nonneg_left hEp hx2
      linarith

/-- **`prop:heatbounds`(ii), both bounds, for a real symmetric matrix with spectrum in `[-1,1]`:**
    `(τ²/2) e^{-2τ} Tr S² ≤ Tr exp(τ(S-1)) - e^{-τ}(N + τ Tr S) ≤ (τ²/2) Tr S²` for `τ ≥ 0`. -/
theorem heat_twice_subtracted_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) (h1 : ∀ i, hS.eigenvalues i ≤ 1)
    (h0 : ∀ i, -1 ≤ hS.eigenvalues i) :
    τ ^ 2 / 2 * Real.exp (-(2 * τ)) * (S ^ 2).trace
        ≤ (NormedSpace.exp (τ • (S - 1))).trace
          - Real.exp (-τ) * ((Fintype.card n : ℝ) + τ * S.trace) ∧
    (NormedSpace.exp (τ • (S - 1))).trace - Real.exp (-τ) * ((Fintype.card n : ℝ) + τ * S.trace)
        ≤ τ ^ 2 / 2 * (S ^ 2).trace := by
  rw [trace_exp_heat S hS τ, trace_pow_eq_sum_eigenvalues S hS 2]
  have htr : S.trace = ∑ i, hS.eigenvalues i := by
    have h := hS.trace_eq_sum_eigenvalues (𝕜 := ℝ)
    simpa using h
  have hsum : Real.exp (-τ) * ((Fintype.card n : ℝ) + τ * S.trace)
      = ∑ i, Real.exp (-τ) * (1 + τ * hS.eigenvalues i) := by
    rw [htr, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hEt := Real.exp_pos (-τ)
  have e2 : Real.exp (-(2 * τ)) = Real.exp (-τ) * Real.exp (-τ) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-τ) * Real.exp τ = 1 := by rw [← Real.exp_add]; simp
  have hmode : ∀ i, τ ^ 2 / 2 * Real.exp (-(2 * τ)) * hS.eigenvalues i ^ 2
        ≤ Real.exp (-(τ * (1 - hS.eigenvalues i))) - Real.exp (-τ) * (1 + τ * hS.eigenvalues i) ∧
      Real.exp (-(τ * (1 - hS.eigenvalues i))) - Real.exp (-τ) * (1 + τ * hS.eigenvalues i)
        ≤ τ ^ 2 / 2 * hS.eigenvalues i ^ 2 := by
    intro i
    have ha : Real.exp (-(τ * (1 - hS.eigenvalues i)))
        = Real.exp (-τ) * Real.exp (τ * hS.eigenvalues i) := by
      rw [← Real.exp_add]; congr 1; ring
    obtain ⟨p1, p2⟩ := phi_two_sided (x := τ * hS.eigenvalues i) (τ := τ)
      (by nlinarith [mul_nonneg hτ (show 0 ≤ hS.eigenvalues i + 1 by linarith [h0 i])])
      (by nlinarith [mul_nonneg hτ (show 0 ≤ 1 - hS.eigenvalues i by linarith [h1 i])])
    have q1 := mul_le_mul_of_nonneg_left p1 hEt.le
    have q2 := mul_le_mul_of_nonneg_left p2 hEt.le
    have r1 : Real.exp (-τ) * ((τ * hS.eigenvalues i) ^ 2 / 2 * Real.exp (-τ))
        = τ ^ 2 / 2 * Real.exp (-(2 * τ)) * hS.eigenvalues i ^ 2 := by rw [e2]; ring
    have r2 : Real.exp (-τ) * ((τ * hS.eigenvalues i) ^ 2 / 2 * Real.exp τ)
        = τ ^ 2 / 2 * hS.eigenvalues i ^ 2 :=
      calc Real.exp (-τ) * ((τ * hS.eigenvalues i) ^ 2 / 2 * Real.exp τ)
          = τ ^ 2 / 2 * hS.eigenvalues i ^ 2 * (Real.exp (-τ) * Real.exp τ) := by ring
        _ = τ ^ 2 / 2 * hS.eigenvalues i ^ 2 := by rw [e3]; ring
    rw [r1] at q1
    rw [r2] at q2
    rw [ha]
    constructor
    · linarith
    · linarith
  rw [hsum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun i _ => (hmode i).1, Finset.sum_le_sum fun i _ => (hmode i).2⟩

/-- First inequality of `eq:chain`: `N e^{-τ} ≤ N exp(-τ(1 - m_1/N))` for `τ, m_1 ≥ 0`. -/
theorem heat_chain_first {N τ m1 : ℝ} (hN : 0 ≤ N) (hτ : 0 ≤ τ) (hm : 0 ≤ m1) :
    N * Real.exp (-τ) ≤ N * Real.exp (-(τ * (1 - m1 / N))) := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hN
  have := mul_nonneg hτ (div_nonneg hm hN)
  linarith

/-- Jensen's inequality for the exponential in the supporting-line form: for weights `w_a ≥ 0`
    with `∑ w_a = 1`, `exp(∑ w_a y_a) ≤ ∑ w_a exp(y_a)`. -/
theorem exp_jensen {ι : Type*} [Fintype ι] (w y : ι → ℝ) (hw : ∀ a, 0 ≤ w a)
    (h1 : ∑ a, w a = 1) : Real.exp (∑ a, w a * y a) ≤ ∑ a, w a * Real.exp (y a) := by
  have hE := Real.exp_pos (∑ a, w a * y a)
  have hterm : ∀ a, w a * (Real.exp (∑ b, w b * y b) * (1 + (y a - ∑ b, w b * y b)))
      ≤ w a * Real.exp (y a) := by
    intro a
    refine mul_le_mul_of_nonneg_left ?_ (hw a)
    have h := Real.add_one_le_exp (y a - ∑ b, w b * y b)
    have e : Real.exp (y a) = Real.exp (∑ b, w b * y b) * Real.exp (y a - ∑ b, w b * y b) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) hE.le
  have hsum : ∑ a, w a * (Real.exp (∑ b, w b * y b) * (1 + (y a - ∑ b, w b * y b)))
      = Real.exp (∑ b, w b * y b) := by
    have e : ∀ a, w a * (Real.exp (∑ b, w b * y b) * (1 + (y a - ∑ b, w b * y b)))
        = Real.exp (∑ b, w b * y b) * (1 - ∑ b, w b * y b) * w a
          + Real.exp (∑ b, w b * y b) * (w a * y a) := fun a => by ring
    rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, h1]
    ring
  calc Real.exp (∑ a, w a * y a)
      = ∑ a, w a * (Real.exp (∑ b, w b * y b) * (1 + (y a - ∑ b, w b * y b))) := hsum.symm
    _ ≤ ∑ a, w a * Real.exp (y a) := Finset.sum_le_sum fun a _ => hterm a

/-- Second inequality of `eq:chain` (Jensen with uniform weights), for any numbers `p_i`:
    `N exp(-τ(1 - (∑ p_i)/N)) ≤ ∑_i e^{-τ(1 - p_i)}`. -/
theorem heat_chain_second {ι : Type*} [Fintype ι] (p : ι → ℝ) (τ : ℝ) :
    (Fintype.card ι : ℝ) * Real.exp (-(τ * (1 - (∑ i, p i) / (Fintype.card ι : ℝ))))
      ≤ ∑ i, Real.exp (-(τ * (1 - p i))) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · have hN : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.2 Fintype.card_pos
    have h := exp_jensen (fun _ : ι => 1 / (Fintype.card ι : ℝ))
      (fun i => -(τ * (1 - p i))) (fun _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    have e1 : ∑ i : ι, 1 / (Fintype.card ι : ℝ) * -(τ * (1 - p i))
        = -(τ * (1 - (∑ i, p i) / (Fintype.card ι : ℝ))) := by
      rw [← Finset.mul_sum, Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have e2 : ∑ i : ι, 1 / (Fintype.card ι : ℝ) * Real.exp (-(τ * (1 - p i)))
        = (∑ i, Real.exp (-(τ * (1 - p i)))) / (Fintype.card ι : ℝ) := by
      rw [← Finset.mul_sum]; ring
    rw [e1, e2, le_div_iff₀ hN] at h
    linarith

/-- Part (iii), monotonicity: for eigenvalues `≤ 1` the trace is nonincreasing in `τ`. -/
theorem heat_antitone_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (h1 : ∀ i, hS.eigenvalues i ≤ 1) {τ1 τ2 : ℝ} (h : τ1 ≤ τ2) :
    (NormedSpace.exp (τ2 • (S - 1))).trace ≤ (NormedSpace.exp (τ1 • (S - 1))).trace := by
  rw [trace_exp_heat S hS τ1, trace_exp_heat S hS τ2]
  refine Finset.sum_le_sum fun i _ => Real.exp_le_exp.2 ?_
  nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 (h1 i))]

/-- Part (iii), logarithmic convexity at the midpoint (Cauchy--Schwarz):
    `(Tr e^{-tL} at (τ₁+τ₂)/2)² ≤ (Tr e^{-tL} at τ₁)(Tr e^{-tL} at τ₂)`, every real symmetric `S`. -/
theorem heat_logconvex_midpoint {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (τ1 τ2 : ℝ) :
    (NormedSpace.exp (((τ1 + τ2) / 2) • (S - 1))).trace ^ 2
      ≤ (NormedSpace.exp (τ1 • (S - 1))).trace * (NormedSpace.exp (τ2 • (S - 1))).trace := by
  rw [trace_exp_heat S hS τ1, trace_exp_heat S hS τ2, trace_exp_heat S hS ((τ1 + τ2) / 2)]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.exp (-(τ1 * (1 - hS.eigenvalues i)) / 2))
    (fun i => Real.exp (-(τ2 * (1 - hS.eigenvalues i)) / 2))
  have e0 : ∀ i, Real.exp (-(τ1 * (1 - hS.eigenvalues i)) / 2)
        * Real.exp (-(τ2 * (1 - hS.eigenvalues i)) / 2)
      = Real.exp (-((τ1 + τ2) / 2 * (1 - hS.eigenvalues i))) := fun i => by
    rw [← Real.exp_add]; congr 1; ring
  have e1 : ∀ τ : ℝ, ∀ i, Real.exp (-(τ * (1 - hS.eigenvalues i)) / 2) ^ 2
      = Real.exp (-(τ * (1 - hS.eigenvalues i))) := fun τ i => by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  simp only [e0, e1] at h
  exact h

/-- The diagonal of the matrix exponential in the eigenbasis: with the orthogonal matrix `U` of
    eigenvectors, `(exp(τ(S-1)))_ii = ∑_a U_ia² e^{-τ(1-s_a)}`, `S_ii = ∑_a U_ia² s_a` and
    `∑_a U_ia² = 1`. -/
theorem exp_diag_eigen {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (τ : ℝ) (i : n) :
    (NormedSpace.exp (τ • (S - 1))) i i
        = ∑ a, (hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2
            * Real.exp (-(τ * (1 - hS.eigenvalues a))) ∧
    S i i = ∑ a, (hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2 * hS.eigenvalues a ∧
    ∑ a, (hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2 = 1 := by
  let U : Matrix n n ℝ := hS.eigenvectorUnitary
  have h1 : U * star U = 1 := Unitary.coe_mul_star_self _
  have h2 : star U * U = 1 := Unitary.coe_star_mul_self _
  let u : (Matrix n n ℝ)ˣ := ⟨U, star U, h1, h2⟩
  have hS' : S = (u : Matrix n n ℝ) * diagonal (RCLike.ofReal ∘ hS.eigenvalues)
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    conv_lhs => rw [hS.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rfl
  have hD : diagonal (fun i => τ * (hS.eigenvalues i - 1))
      = τ • (diagonal (RCLike.ofReal ∘ hS.eigenvalues) - 1) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hsub : S - 1 = (u : Matrix n n ℝ) * (diagonal (RCLike.ofReal ∘ hS.eigenvalues) - 1)
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv, ← hS']
  have hL : τ • (S - 1) = (u : Matrix n n ℝ) * diagonal (fun i => τ * (hS.eigenvalues i - 1))
      * ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    rw [hD, hsub, Matrix.mul_smul, Matrix.smul_mul]
  have hexp := (congrArg NormedSpace.exp hL).trans (Matrix.exp_units_conj u _)
  have entry : ∀ d : n → ℝ, (U * diagonal d * star U) i i = ∑ a, U i a ^ 2 * d a := by
    intro d
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hexp, Matrix.exp_diagonal]
    have := entry (NormedSpace.exp fun i => τ * (hS.eigenvalues i - 1))
    refine this.trans (Finset.sum_congr rfl fun a _ => ?_)
    rw [Pi.coe_exp, ← Real.exp_eq_exp_ℝ]
    congr 2
    ring
  · have := entry hS.eigenvalues
    conv_lhs => rw [hS']
    exact this
  · have := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.star_apply, star_trivial]
    ring

/-- Third inequality of `eq:chain`: `∑_i e^{-τ(1 - S_ii)} ≤ Tr exp(τ(S-1))`, for every real
    symmetric `S` and every real `τ` (Jensen with the weights `|v_a(i)|²`). -/
theorem heat_chain_third {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (τ : ℝ) :
    ∑ i, Real.exp (-(τ * (1 - S i i))) ≤ (NormedSpace.exp (τ • (S - 1))).trace := by
  unfold Matrix.trace
  refine Finset.sum_le_sum fun i _ => ?_
  obtain ⟨e1, e2, e3⟩ := exp_diag_eigen S hS τ i
  have h := exp_jensen (fun a => (hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2)
    (fun a => -(τ * (1 - hS.eigenvalues a))) (fun a => pow_two_nonneg _) e3
  have e4 : ∑ a, (hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2 * -(τ * (1 - hS.eigenvalues a))
      = -(τ * (1 - S i i)) := by
    have e : ∀ a, (hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2 * -(τ * (1 - hS.eigenvalues a))
        = τ * ((hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2 * hS.eigenvalues a)
          - τ * (hS.eigenvectorUnitary : Matrix n n ℝ) i a ^ 2 := fun a => by ring
    rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, ← e2, e3]
    ring
  rw [e4] at h
  rw [Matrix.diag_apply, e1]
  exact h

/-- **`prop:heatbounds`(i), the chain `eq:chain`, for a real symmetric matrix** with `Tr S ≥ 0`
    and eigenvalues `≤ 1`, `τ ≥ 0`:
    `N e^{-τ} ≤ N exp(-τ(1 - Tr S/N)) ≤ ∑_i e^{-τ(1 - S_ii)} ≤ Tr exp(τ(S-1)) ≤ N`. -/
theorem heat_chain {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) (htr : 0 ≤ S.trace)
    (h1 : ∀ i, hS.eigenvalues i ≤ 1) :
    (Fintype.card n : ℝ) * Real.exp (-τ)
        ≤ (Fintype.card n : ℝ) * Real.exp (-(τ * (1 - S.trace / (Fintype.card n : ℝ)))) ∧
    (Fintype.card n : ℝ) * Real.exp (-(τ * (1 - S.trace / (Fintype.card n : ℝ))))
        ≤ ∑ i, Real.exp (-(τ * (1 - S i i))) ∧
    ∑ i, Real.exp (-(τ * (1 - S i i))) ≤ (NormedSpace.exp (τ • (S - 1))).trace ∧
    (NormedSpace.exp (τ • (S - 1))).trace ≤ (Fintype.card n : ℝ) :=
  ⟨heat_chain_first (Nat.cast_nonneg _) hτ htr, heat_chain_second (fun i => S i i) τ,
    heat_chain_third S hS τ, heat_upper_matrix S hS hτ h1⟩

end OlderParts

/-! ## The limit `N → ∞` at a FIXED kernel scale on the flat torus (A48)

Formal counterparts, on the flat torus `(ℝ/ℤ)^d` with the uniform density and the periodised
Gaussian kernel only, of Theorem "fixedxi" and Corollary "torus" of Appendix G.

WHAT IS PROVED (no hypotheses beyond: the points are independent, measurable and uniform;
`σ > 0`):
* `trace_pow_tendsto_ae`: almost surely, for EVERY `k ≥ 1` simultaneously, `Tr P_N^k → m_k`
  (`m_k = heatMode d σ k`, the heat kernel of the torus at the origin after `k` steps).
* `subtracted_trace_uniform_ae`: almost surely, for every `Tm ≥ 0` and `ε > 0`, eventually in `N`,
  `|Tr exp(τ(S_N - 1)) - N e^{-τ} - poissonMean d σ τ| ≤ ε` for ALL `τ ∈ [0, Tm]` (one null set for
  all `τ`, uniform on compact sets of `τ`); `subtracted_trace_tendsto_ae` is the pointwise form.
* `cor_torus_ae`: the same in the conventions of the paper (`s = ξ²/2` is the `σ` of the paper,
  the kernel has variance `2s`, `τ = t/s`): the limits are `Tr e^{ksΔ}` and `T_s(t)` (`subTr`),
  and for `s ≤ t ≤ 1` the quotient by `Θ(t)` converges to a number within `popRem d s t` of
  `1 + d(d+2)/8 · s/t`.

WHAT IS NOT PROVED: Theorem "fixedxi" itself. The paper states it for a closed manifold, a
continuous positive density and an arbitrary continuous symmetric kernel, and proves it with the
strong law for U-statistics. Here the entrywise limit `heatTorus_walk_ae` of the second file
(Hoeffding, nets, Borel–Cantelli, semigroup property of the heat kernel) is used instead, which
exists only for the torus, the uniform density and the heat kernel. Part (ii) of Corollary "torus"
(other profiles) is not formalised. The sample is nested (the first `N` points of one sequence),
the graph keeps its self-loops, the kernel is defined by its Fourier series (`heatTorus`; it is the
periodised Gaussian by `heatTorus_eq_prod`), and the normalisation is the estimated one, `q_i`
divided by `N`. No rate in `N` is claimed. -/

namespace FixedScale

open Filter Topology
open CTG.Reals.TraceG29 PopulationRate SharpRate

variable {Ω : Type*} {d : ℕ}

/-- The kernel matrix of the first `N` sample points: `K_ij = p_σ(X_i - X_j)`, `p_σ` the heat
    kernel of the torus of variance `σ` (`heatTorus d (2π²σ)`), diagonal included. -/
noncomputable def fsK (d : ℕ) (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    Fin N → Fin N → ℝ :=
  fun i j => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω)

/-- The estimated normalisation `ρ_i = (1/N) ∑_l K_il`. -/
noncomputable def fsRho (d : ℕ) (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) : Fin N → ℝ :=
  fun i => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N

/-- The walk matrix `P_N` of the first `N` sample points. -/
noncomputable def fsWalk (d : ℕ) (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℝ :=
  walkMatrix (fsK d σ X N ω) (fsRho d σ X N ω)

/-- The symmetric normalised matrix `S_N` of the first `N` sample points. -/
noncomputable def fsSym (d : ℕ) (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℝ :=
  symGraph (fsK d σ X N ω) (fsRho d σ X N ω)

/-- The subtracted heat trace `Tr exp(τ(S_N - 1)) - N e^{-τ}` (`= Tr e^{-tL} - N e^{-τ}` with
    `L = (2/ξ²)(1 - S)`, `τ = 2t/ξ²`). -/
noncomputable def fsSub (d : ℕ) (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  (NormedSpace.exp (τ • (fsSym d σ X N ω - 1))).trace - (N : ℝ) * Real.exp (-τ)

/-- The normalisation is the `heatRho` of the other sections (sum over `Fin N` against sum over
    `Finset.range N`), so the matrices here are those of `kernel_theorem_G28`, `heat_trace_G29`. -/
theorem fsRho_eq_heatRho (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) (i : Fin N) :
    fsRho d σ X N ω i = heatRho d σ N (fun j => X j ω) i := by
  unfold fsRho heatRho
  rw [Fin.sum_univ_eq_sum_range
    (fun l : ℕ => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) N]

/-! ### Deterministic facts about the sampled graph -/

theorem fsK_symm (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) (i j : Fin N) :
    fsK d σ X N ω i j = fsK d σ X N ω j i := by
  unfold fsK
  rw [← heatTorus_even, neg_sub]

theorem fsK_nonneg {σ : ℝ} (hσ : 0 < σ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) (i j : Fin N) :
    0 ≤ fsK d σ X N ω i j := by
  have hpi := Real.pi_pos
  exact heatTorus_nonneg (by positivity) d _

theorem fsRho_pos {σ : ℝ} (hσ : 0 < σ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) (i : Fin N) :
    0 < fsRho d σ X N ω i := by
  have hpi := Real.pi_pos
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  unfold fsRho
  refine div_pos ?_ hN
  refine Finset.sum_pos' (fun l _ => heatTorus_nonneg hc d _) ⟨i, Finset.mem_univ _, ?_⟩
  rw [sub_self]
  exact heatTorus_zero_pos hc d

theorem fs_degree_pos {σ : ℝ} (hσ : 0 < σ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω)
    (i : Fin N) :
    0 < ∑ l, fsK d σ X N ω i l / (fsRho d σ X N ω i * fsRho d σ X N ω l) := by
  have hpi := Real.pi_pos
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  refine Finset.sum_pos'
    (fun l _ => div_nonneg (fsK_nonneg hσ X N ω i l)
      (mul_pos (fsRho_pos hσ X N ω i) (fsRho_pos hσ X N ω l)).le) ⟨i, Finset.mem_univ _, ?_⟩
  refine div_pos ?_ (mul_pos (fsRho_pos hσ X N ω i) (fsRho_pos hσ X N ω i))
  unfold fsK
  rw [sub_self]
  exact heatTorus_zero_pos hc d

theorem fsSym_isHermitian (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    (fsSym d σ X N ω).IsHermitian :=
  symGraph_isHermitian _ _ (fsK_symm σ X N ω)

/-- `Tr S_N^k = Tr P_N^k`. -/
theorem fs_trace_eq {σ : ℝ} (hσ : 0 < σ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) (k : ℕ) :
    (fsSym d σ X N ω ^ k).trace = (fsWalk d σ X N ω ^ k).trace :=
  symGraph_trace_pow _ _ (fs_degree_pos hσ X N ω) k

/-- `|Tr S_N^k| ≤ Tr S_N²` for `k ≥ 2` (Proposition "moments"(ii), spectral form). -/
theorem fs_trace_le_sq {σ : ℝ} (hσ : 0 < σ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) {k : ℕ}
    (hk : 2 ≤ k) : |(fsSym d σ X N ω ^ k).trace| ≤ (fsSym d σ X N ω ^ 2).trace :=
  (symGraph_trace_bounds _ _ (fsK_symm σ X N ω) (fsK_nonneg hσ X N ω) (fsRho_pos hσ X N ω)
    (fs_degree_pos hσ X N ω) k).2 hk

/-- The Poisson series of the subtracted heat trace of the sampled graph. -/
theorem fsSub_hasSum (σ : ℝ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) (τ : ℝ) :
    HasSum (fun j : ℕ => pw τ (j + 1) * (fsSym d σ X N ω ^ (j + 1)).trace)
      (fsSub d σ X N ω τ) := by
  have h := subtracted_trace_hasSum (fsSym d σ X N ω) (fsSym_isHermitian σ X N ω) τ
  rw [Fintype.card_fin] at h
  exact h

/-! ### Stage 1: the traces of the powers -/

variable {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- One power and one tolerance: almost surely, for all large `N`,
    `|Tr P_N^{k+1} - m_{k+1}| ≤ eta` (the diagonal of `heatTorus_walk_ae`). -/
theorem trace_pow_eventually_ae (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ) (k : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop,
      |(fsWalk d σ X N ω ^ (k + 1)).trace - heatMode d σ (k + 1)| ≤ eta := by
  have hpi := Real.pi_pos
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  filter_upwards [heatTorus_walk_ae d X h_indep hX hlaw hc k heta] with ω hω
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨N0 + 1, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn := hN0 n (by omega)
  refine trace_from_diagonal (Nat.succ_pos n) (fsWalk d σ X (n + 1) ω ^ (k + 1)) (fun a => ?_)
  have h2 := hn a a
  rw [sub_self] at h2
  have e : ((k + 1 : ℕ) : ℝ) * (2 * Real.pi ^ 2 * σ)
      = 2 * Real.pi ^ 2 * (((k + 1 : ℕ) : ℝ) * σ) := by ring
  rw [e] at h2
  exact h2

/-- **Theorem "fixedxi"(i) on the flat torus, Gaussian profile.** Almost surely, for every
    `k ≥ 1`, `Tr P_N^k → m_k = p_{kσ}(0)` as `N → ∞` (kernel of variance `σ` fixed; one null set
    for all `k`). -/
theorem trace_pow_tendsto_ae (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂μ, ∀ k, 1 ≤ k →
      Tendsto (fun N => (fsWalk d σ X N ω ^ k).trace) atTop (𝓝 (heatMode d σ k)) := by
  have h : ∀ᵐ ω ∂μ, ∀ k n : ℕ, ∀ᶠ N in atTop,
      |(fsWalk d σ X N ω ^ (k + 1)).trace - heatMode d σ (k + 1)| ≤ 1 / ((n : ℝ) + 1) := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro n
    exact trace_pow_eventually_ae X h_indep hX hlaw hσ k (by positivity)
  filter_upwards [h] with ω hω k hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k n] with N hN
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hN hn

/-! ### Stage 2: the subtracted heat trace -/

/-- A nonnegative series dominated by a summable one is small if a tail of the dominating series
    and the corresponding initial segment are small. -/
theorem tsum_lt_of_tail {f b : ℕ → ℝ} (hf0 : ∀ j, 0 ≤ f j) (hle : ∀ j, f j ≤ b j)
    (hb : Summable b) (J : ℕ) {e : ℝ} (hJ : ∑' j, b (j + J) < e / 2)
    (hfin : ∑ j ∈ Finset.range J, f j < e / 2) : ∑' j, f j < e := by
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hle hb
  rw [← Summable.sum_add_tsum_nat_add J hsum]
  have h2 : ∑' j, f (j + J) ≤ ∑' j, b (j + J) :=
    Summable.tsum_le_tsum (fun j => hle (j + J)) ((summable_nat_add_iff J).2 hsum)
      ((summable_nat_add_iff J).2 hb)
  linarith

/-- Deterministic limit of Poisson means, uniform for `τ` in `[0, Tm]`: if `a_N(j) → m(j)` for
    every `j ≥ 1` and eventually `|a_N(j)| ≤ B` for all `j ≥ 1`, `|m(j)| ≤ B`, then for every
    `ε > 0`, eventually in `N`, `|∑_{j≥1} w_j(τ) a_N(j) - ∑_{j≥1} w_j(τ) m(j)| ≤ ε` for all
    `τ ∈ [0, Tm]`. (Dominated convergence for series with the weights `Tm^j/j!`, done by hand: tail plus finite sum.) -/
theorem poisson_limit_uniform (a : ℕ → ℕ → ℝ) (m : ℕ → ℝ) {B Tm : ℝ} (hTm : 0 ≤ Tm)
    (hconv : ∀ j, Tendsto (fun N => a N (j + 1)) atTop (𝓝 (m (j + 1))))
    (hB : ∀ᶠ N in atTop, ∀ j, |a N (j + 1)| ≤ B) (hm : ∀ j, |m (j + 1)| ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ τ, 0 ≤ τ → τ ≤ Tm → ∀ A T : ℝ,
      HasSum (fun j : ℕ => pw τ (j + 1) * a N (j + 1)) A →
      HasSum (fun j : ℕ => pw τ (j + 1) * m (j + 1)) T → |A - T| ≤ ε := by
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℝ, g = fun j : ℕ => Tm ^ (j + 1) / ((j + 1).factorial : ℝ) :=
    ⟨_, rfl⟩
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    rw [hgdef]; exact div_nonneg (pow_nonneg hTm _) (Nat.cast_nonneg _)
  have hg : Summable g := by
    rw [hgdef]
    exact (summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial Tm)
  have hbs : Summable (fun j => g j * (2 * B)) := hg.mul_right _
  obtain ⟨J, hJ⟩ : ∃ J, ∑' j, g (j + J) * (2 * B) < ε / 2 := by
    have h := tendsto_sum_nat_add (fun j => g j * (2 * B))
    exact ((tendsto_order.1 h).2 (ε / 2) (by linarith)).exists
  have hfin : Tendsto (fun N => ∑ j ∈ Finset.range J, g j * |a N (j + 1) - m (j + 1)|) atTop
      (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.range J)
      (fun j _ => (((hconv j).sub_const (m (j + 1))).abs).const_mul (g j))
    simpa using h
  have hF : ∀ᶠ N in atTop, ∑' j, g j * |a N (j + 1) - m (j + 1)| < ε := by
    filter_upwards [(tendsto_order.1 hfin).2 (ε / 2) (by linarith), hB] with N hN hBN
    have hle : ∀ j, g j * |a N (j + 1) - m (j + 1)| ≤ g j * (2 * B) := fun j => by
      refine mul_le_mul_of_nonneg_left ?_ (hg0 j)
      have := abs_sub (a N (j + 1)) (m (j + 1))
      linarith [hBN j, hm j]
    exact tsum_lt_of_tail (f := fun j => g j * |a N (j + 1) - m (j + 1)|)
      (b := fun j => g j * (2 * B)) (fun j => mul_nonneg (hg0 j) (abs_nonneg _)) hle hbs J hJ hN
  filter_upwards [hF, hB] with N hN hBN τ hτ0 hτ A T hA hT
  have hsum : Summable (fun j => g j * |a N (j + 1) - m (j + 1)|) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hg0 j) (abs_nonneg _))
      (fun j => by
        refine mul_le_mul_of_nonneg_left ?_ (hg0 j)
        have := abs_sub (a N (j + 1)) (m (j + 1))
        linarith [hBN j, hm j]) (hg.mul_right (2 * B))
  have hpw : ∀ j, pw τ (j + 1) ≤ g j := fun j => by
    rw [hgdef]
    unfold pw
    have h1 : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : τ ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ Tm ^ (j + 1) / ((j + 1).factorial : ℝ) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hτ0 hτ _) (Nat.cast_nonneg _)
    have h3 : 0 ≤ τ ^ (j + 1) / ((j + 1).factorial : ℝ) :=
      div_nonneg (pow_nonneg hτ0 _) (Nat.cast_nonneg _)
    calc Real.exp (-τ) * (τ ^ (j + 1) / ((j + 1).factorial : ℝ))
        ≤ 1 * (τ ^ (j + 1) / ((j + 1).factorial : ℝ)) := mul_le_mul_of_nonneg_right h1 h3
      _ ≤ Tm ^ (j + 1) / ((j + 1).factorial : ℝ) := by rw [one_mul]; exact h2
  have hD := hA.sub hT
  have hle := hD.norm_le_of_bounded hsum.hasSum (fun j => by
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (pw_nonneg hτ0 _)]
    exact mul_le_mul_of_nonneg_right (hpw j) (abs_nonneg _))
  rw [Real.norm_eq_abs] at hle
  exact hle.trans hN.le

/-- **Theorem "fixedxi"(ii) on the flat torus, Gaussian profile, uniformly on compact sets of
    `τ`.** Kernel of variance `σ > 0` fixed. Almost surely: for every `Tm ≥ 0` and `ε > 0`, for all
    large `N`, `|Tr exp(τ(S_N - 1)) - N e^{-τ} - ∑_{j≥1} w_j(τ) m_j| ≤ ε` for all `τ ∈ [0, Tm]`.
    The null set does not depend on `τ`, `Tm`, `ε`. -/
theorem subtracted_trace_uniform_ae (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂μ, ∀ Tm : ℝ, 0 ≤ Tm → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ τ, 0 ≤ τ → τ ≤ Tm →
      |fsSub d σ X N ω τ - poissonMean d σ τ| ≤ ε := by
  filter_upwards [trace_pow_tendsto_ae X h_indep hX hlaw hσ] with ω hω Tm hTm ε hε
  have hconv : ∀ j, Tendsto (fun N => (fsSym d σ X N ω ^ (j + 1)).trace) atTop
      (𝓝 (heatMode d σ (j + 1))) := fun j =>
    (hω (j + 1) (by omega)).congr (fun N => (fs_trace_eq hσ X N ω (j + 1)).symm)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = heatTorus d (2 * Real.pi ^ 2 * σ) 0 := ⟨_, rfl⟩
  have hmle : ∀ j, heatMode d σ (j + 1) ≤ M := fun j => by
    rw [hMdef]; exact heatMode_le hσ d (by omega)
  have hmge : ∀ j, 1 ≤ heatMode d σ (j + 1) := fun j => heatMode_ge_one hσ d (by omega)
  have hm : ∀ j, |heatMode d σ (j + 1)| ≤ M + 1 := fun j => by
    rw [abs_of_nonneg (by linarith [hmge j])]; linarith [hmle j]
  have hev : ∀ j, ∀ᶠ N in atTop, |(fsSym d σ X N ω ^ (j + 1)).trace| ≤ M + 1 := fun j => by
    filter_upwards [(Metric.tendsto_nhds.1 (hconv j)) 1 one_pos] with N hN
    rw [Real.dist_eq] at hN
    have h1 := abs_sub_abs_le_abs_sub ((fsSym d σ X N ω ^ (j + 1)).trace) (heatMode d σ (j + 1))
    have h2 := hm j
    have h3 : |heatMode d σ (j + 1)| ≤ M := by
      rw [abs_of_nonneg (by linarith [hmge j])]; exact hmle j
    linarith
  have hB : ∀ᶠ N in atTop, ∀ j, |(fsSym d σ X N ω ^ (j + 1)).trace| ≤ M + 1 := by
    filter_upwards [hev 0, hev 1] with N h0 h1 j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj]; exact h0
    · have h2 := fs_trace_le_sq hσ X N ω (k := j + 1) (by omega)
      exact h2.trans ((le_abs_self _).trans h1)
  filter_upwards [poisson_limit_uniform (fun N j => (fsSym d σ X N ω ^ j).trace)
    (heatMode d σ) hTm hconv hB hm hε] with N hN τ hτ0 hτ
  exact hN τ hτ0 hτ _ _ (fsSub_hasSum σ X N ω τ) (poissonMean_hasSum hσ d hτ0)

/-- **Theorem "fixedxi"(ii) on the flat torus, Gaussian profile, pointwise form.** Almost surely,
    for every `τ ≥ 0`: `Tr exp(τ(S_N - 1)) - N e^{-τ} → poissonMean d σ τ` as `N → ∞`. -/
theorem subtracted_trace_tendsto_ae (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ ω ∂μ, ∀ τ : ℝ, 0 ≤ τ →
      Tendsto (fun N => fsSub d σ X N ω τ) atTop (𝓝 (poissonMean d σ τ)) := by
  filter_upwards [subtracted_trace_uniform_ae X h_indep hX hlaw hσ] with ω hω τ hτ
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hω τ hτ (ε / 2) (by linarith)] with N hN
  rw [Real.dist_eq]
  have := hN τ hτ le_rfl
  linarith

/-! ### Stage 3: Corollary "torus"(i) in the conventions of the paper -/

/-- `m_k` for the kernel of variance `2s` is the heat trace `Θ(ks) = Tr e^{ksΔ}` of the torus. -/
theorem heatMode_eq_heatTr (d : ℕ) (s : ℝ) (k : ℕ) :
    heatMode d (2 * s) k = heatTr (torusLam d) ((k : ℝ) * s) := by
  rw [heatTr_torus]
  unfold heatMode
  congr 1
  ring

/-- **Corollary "torus"(i), Gaussian profile.** `s > 0` is the `σ = ξ²/2` of the paper; the
    kernel is the heat kernel of variance `ξ² = 2s`, and `τ = t/s`. Almost surely (one null set
    for all `k` and `t`):
    (a) `Tr P_N^k → Θ(ks) = Tr e^{ksΔ}` for every `k ≥ 1`;
    (b) `Tr e^{-tL_N} - N e^{-τ} → T_s(t)` (`subTr`, equation `eq:Tsigma`) for every `t ≥ 0`;
    (c) for `s ≤ t ≤ 1` the quotient by `Θ(t)` converges to `T_s(t)/Θ(t)`, and this limit satisfies
        `|T_s(t)/Θ(t) - 1 - d(d+2)/8 · s/t| ≤ popRem d s t` (`eq:rateexact` with the explicit
        remainder of `rate_exact_torus_explicit`; the remainder is `O(τ^{-2})` plus terms that are
        exponentially small in `τ` and in `1/t`, see there for when it is small). -/
theorem cor_torus_ae (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂μ,
      (∀ k : ℕ, 1 ≤ k → Tendsto (fun N => (fsWalk d (2 * s) X N ω ^ k).trace) atTop
          (𝓝 (heatTr (torusLam d) ((k : ℝ) * s))))
      ∧ (∀ t : ℝ, 0 ≤ t → Tendsto (fun N => fsSub d (2 * s) X N ω (t / s)) atTop
          (𝓝 (subTr (torusLam d) s t)))
      ∧ (∀ t : ℝ, s ≤ t → t ≤ 1 →
          Tendsto (fun N => fsSub d (2 * s) X N ω (t / s) / heatTr (torusLam d) t) atTop
            (𝓝 (subTr (torusLam d) s t / heatTr (torusLam d) t))
          ∧ |subTr (torusLam d) s t / heatTr (torusLam d) t - 1
              - (d : ℝ) * ((d : ℝ) + 2) / 8 * (s / t)| ≤ popRem d s t) := by
  have h2s : 0 < 2 * s := by linarith
  filter_upwards [trace_pow_tendsto_ae X h_indep hX hlaw h2s,
    subtracted_trace_tendsto_ae X h_indep hX hlaw h2s] with ω h1 h2
  have hb : ∀ t : ℝ, 0 ≤ t → Tendsto (fun N => fsSub d (2 * s) X N ω (t / s)) atTop
      (𝓝 (subTr (torusLam d) s t)) := fun t ht => by
    rw [subTr_torus d hs ht]
    exact h2 (t / s) (div_nonneg ht hs.le)
  refine ⟨fun k hk => ?_, hb, fun t hts ht1 => ⟨?_, ?_⟩⟩
  · rw [← heatMode_eq_heatTr]
    exact h1 k hk
  · exact (hb t (hs.le.trans hts)).div_const _
  · exact rate_exact_torus_explicit d hs hts ht1

end FixedScale

/-! ## Older parts of Appendix G, second block: `prop:moments`, `cor:subtractions`, `eq:window`,
`thm:profileHS` (with the indicator of an interval, `d = 1`) and the algebra of `prop:sphere`

Meant to stand at the end of the seventh file, inside `namespace CTG.Reals2`.
Part A: `prop:moments` (complete, for real matrices) and the DETERMINISTIC part of
`cor:subtractions` and of the display `eq:window`. Part B: `thm:profileHS` for lists of eigenvalues
(complete, with explicit constants and without Weyl's law) and its hypotheses for the indicator
of an interval. Part C: the algebra of `prop:sphere`/`prop:spheregap` over `ℝ`, CONDITIONAL on the
Taylor estimate for the Legendre polynomials. Each part has its own comment with what is and what
is not proved. No statement here is "the statement of the paper, machine-checked" where the paper
speaks of manifolds, operators or random samples.
-/

namespace OlderParts2

open PopulationRate OlderParts CTG.Reals.TraceG29

/-! ### Part A: `prop:moments` and the deterministic part of `cor:subtractions`

Setting as in `symGraph`, `walkMatrix` of the second file: a kernel matrix `K` and a normalisation
`rho`, `W_ij = K_ij/(rho_i rho_j)`, `D_i = ∑_l W_il`, `P = D⁻¹ W = walkMatrix K rho`,
`S = D^{-1/2} W D^{-1/2} = symGraph K rho`; `Tr e^{-tL} = Tr exp(τ(S - 1))`, `N = Fintype.card n`.
(Take `rho = 1` for a general symmetric nonnegative `W = K` with positive row sums.)
Hypotheses, where needed: `K` symmetric, `K ≥ 0`, `rho > 0`, `D_i > 0`.

`prop:moments`:
* (i)  `moments_zero`, `moments_one`, `moments_two` (`m_0 = N`, `m_1 = ∑_i W_ii/D_i`,
  `m_2 = ∑_{i,j} W_ij²/(D_i D_j)`); `pow_succ_apply_paths`, `trace_closed_walks` (for an arbitrary
  square matrix: `Tr P^{k+1}` is the sum over the closed walks `i → f_0 → … → f_{k-1} → i` of the
  products of the entries);
* (ii) `moments_bounds`: `0 ≤ m_k ≤ N`, `1 ≤ m_{2k}` (for `N > 0`), `m_{2k+2} ≤ m_{2k}`,
  `m_k ≤ m_2` for `k ≥ 2`; `walk_pow_stoch`: `P^k` has entries in `[0,1]` and row sums one;
  `moments_trace_eq`: `Tr S^k = Tr P^k` (this is `symGraph_trace_pow` of the second file);
* (iii) `moments_series`: `e^τ Tr e^{-tL} = ∑_k τ^k m_k / k!` as a `HasSum`, for every real `τ`,
  and `m_k` is the `k`-th derivative of `τ ↦ e^τ Tr exp(τ(S-1))` at `τ = 0` (Mathlib's
  `iteratedDeriv`); for an arbitrary real symmetric `S`: `moments_series_sym`,
  `moments_iteratedDeriv_sym`;
* the sentence after the proposition: `moments_one_noloops` (`m_1 = 0` if `K_ii = 0` for all `i`).

`cor:subtractions`, DETERMINISTIC part only (the differences between the subtractions):
* (a) `subtraction_a_modes`, `subtraction_a`:
  `0 ≤ ∑_i e^{-τ(1-p_i)} - N e^{-τ} ≤ τ e^{-τ(1-q)} m_1` if `0 ≤ p_i ≤ q` (the paper: `q = 1/2`);
  `subtraction_a_rate`: for `q = 1/2`, `τ ≥ τ₀ > 0`, `κ ≤ 1/2` the difference is at most
  `(1/τ₀) τ² e^{-κτ} m_1`;
* (b) `subtraction_b`: `0 ≤ e^{-τ} ∑_{k<m} τ^k/k! Tr P^k - N e^{-τ} ≤ B e^{-τ} ∑_{1≤k<m} τ^k/k!`
  with `B = max(m_1, m_2)` (`moments_le_max`: `m_k ≤ max(m_1, m_2)` for `k ≥ 1`);
* `subtraction_arith_one`, `subtraction_arith`: the elementary inequality
  `τ^k e^{-τ/2} ≤ C τ² e^{-κτ}` for `τ ≥ τ₀ > 0`, `κ < 1/2`, used at the end of the proof;
* the display `eq:window` after the corollary: `poisson_lower_tail`, `poisson_upper_tail` (the two
  Chernoff bounds `e^{-τ} ∑_{k ≤ τ/2} τ^k/k! ≤ e^{-τ(1 - ln 2)/2}`,
  `e^{-τ} ∑_{k ≥ 2τ} τ^k/k! ≤ e^{-τ(2 ln 2 - 1)}`), `window_bound`, `window_bound_graph`
  (`|Tr e^{-tL} - N e^{-τ} - e^{-τ} ∑_{τ/2<k<2τ} τ^k/k! Tr P^k| ≤ B (sum of the two exponentials)`
  with `B = max(m_1, m_2)`) and `window_exponents` (both exponents are `≥ 0.15`).
NOT proved, NOT claimed: the corollary itself. Its statement is about the almost sure limit
`eq:tracesub` and the bound `eq:tracerate` of `thm:trace`, which are not formalised; the inputs
`max_i p_i ≤ 1/2` and `m_1, m_2 ≤ C ξ^{-d}` (Lemmas `lem:weights`, `lem:traces`, probabilistic) appear
here as the free numbers `q` and `B`.
-/

section Moments

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The entries of the walk matrix are nonnegative. -/
theorem mom_walk_nonneg (K : n → n → ℝ) (rho : n → ℝ) (hK0 : ∀ i j, 0 ≤ K i j)
    (hrho : ∀ i, 0 < rho i) (i j : n) : 0 ≤ walkMatrix K rho i j := by
  simp only [walkMatrix, Matrix.of_apply]
  exact div_nonneg (div_nonneg (hK0 i j) (mul_pos (hrho i) (hrho j)).le)
    (Finset.sum_nonneg fun l _ => div_nonneg (hK0 i l) (mul_pos (hrho i) (hrho l)).le)

/-- `prop:moments`(ii), first sentence of the proof: `P^k` is row-stochastic with nonnegative
    entries, so all its entries (in particular the diagonal ones) lie in `[0, 1]`. -/
theorem walk_pow_stoch (K : n → n → ℝ) (rho : n → ℝ) (hK0 : ∀ i j, 0 ≤ K i j)
    (hrho : ∀ i, 0 < rho i) (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) (k : ℕ) (i j : n) :
    0 ≤ (walkMatrix K rho ^ k) i j ∧ ∑ l, (walkMatrix K rho ^ k) i l = 1
      ∧ (walkMatrix K rho ^ k) i j ≤ 1 := by
  have h0 := pow_entries_nonneg (walkMatrix K rho) (mom_walk_nonneg K rho hK0 hrho) k
  have h1 := CTG.Reals.pow_row_sum (walkMatrix K rho)
    (fun a => walkMatrix_row_sum K rho a (hD a).ne') k i
  refine ⟨h0 i j, h1, ?_⟩
  rw [← h1]
  exact Finset.single_le_sum (fun l _ => h0 i l) (Finset.mem_univ j)

/-- `prop:moments`(i): `m_0 = N`. -/
theorem moments_zero (P : Matrix n n ℝ) : (P ^ 0).trace = (Fintype.card n : ℝ) := by
  simp [Matrix.trace]

/-- `prop:moments`(i): `m_1 = ∑_i W_ii / D_i`. -/
theorem moments_one (K : n → n → ℝ) (rho : n → ℝ) :
    (walkMatrix K rho ^ 1).trace
      = ∑ i, (K i i / (rho i * rho i)) / (∑ l, K i l / (rho i * rho l)) := by
  simp [Matrix.trace, walkMatrix]

/-- The sentence after `prop:moments`: `m_1` vanishes identically if the self-loops are omitted. -/
theorem moments_one_noloops (K : n → n → ℝ) (rho : n → ℝ) (h0 : ∀ i, K i i = 0) :
    (walkMatrix K rho ^ 1).trace = 0 := by
  rw [moments_one]
  exact Finset.sum_eq_zero fun i _ => by rw [h0 i]; simp

/-- `prop:moments`(i): `m_2 = ∑_{i,j} W_ij² / (D_i D_j)` for symmetric `K`. -/
theorem moments_two (K : n → n → ℝ) (rho : n → ℝ) (hK : ∀ i j, K i j = K j i) :
    (walkMatrix K rho ^ 2).trace
      = ∑ i, ∑ j, (K i j / (rho i * rho j)) ^ 2
          / ((∑ l, K i l / (rho i * rho l)) * (∑ l, K j l / (rho j * rho l))) := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply, walkMatrix,
    Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hK j i, mul_comm (rho j) (rho i), div_mul_div_comm]

/-- The weight of the walk `i → f 0 → f 1 → … → f (k-1) → j` (with `k + 1` steps). -/
noncomputable def pathW (P : Matrix n n ℝ) : (k : ℕ) → n → (Fin k → n) → n → ℝ
  | 0, i, _, j => P i j
  | k + 1, i, f, j => P i (f 0) * pathW P k (f 0) (Fin.tail f) j

/-- The entries of `P^{k+1}` as sums over walks (the definition of the matrix product). -/
theorem pow_succ_apply_paths (P : Matrix n n ℝ) (k : ℕ) (i j : n) :
    (P ^ (k + 1)) i j = ∑ f : Fin k → n, pathW P k i f j := by
  induction k generalizing i with
  | zero => simp [pathW]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => n)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ih a, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [pathW, Fin.consEquiv]

/-- `prop:moments`(i), general statement: `Tr P^{k+1}` is the sum over the closed walks
    `i → f 0 → … → f (k-1) → i` of the products of the entries of `P`. For any square matrix. -/
theorem trace_closed_walks (P : Matrix n n ℝ) (k : ℕ) :
    (P ^ (k + 1)).trace = ∑ i, ∑ f : Fin k → n, pathW P k i f i := by
  simp only [Matrix.trace, Matrix.diag_apply, pow_succ_apply_paths]

/-- `Tr S^k = Tr P^k` (`symGraph_trace_pow` of the second file, repeated for reference). -/
theorem moments_trace_eq (K : n → n → ℝ) (rho : n → ℝ)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) (k : ℕ) :
    (symGraph K rho ^ k).trace = (walkMatrix K rho ^ k).trace :=
  CTG.Reals.TraceG29.symGraph_trace_pow K rho hD k

/-- The eigenvalues of `S` lie in `[-1, 1]` (from `normalised_eigenvalues_mem`). -/
theorem mom_eig_mem (K : n → n → ℝ) (rho : n → ℝ) (hK : ∀ i j, K i j = K j i)
    (hK0 : ∀ i j, 0 ≤ K i j) (hrho : ∀ i, 0 < rho i)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) (hS : (symGraph K rho).IsHermitian) (i : n) :
    -1 ≤ hS.eigenvalues i ∧ hS.eigenvalues i ≤ 1 :=
  normalised_eigenvalues_mem (fun i j => K i j / (rho i * rho j))
    (fun i j => by beta_reduce; rw [hK i j, mul_comm])
    (fun i j => div_nonneg (hK0 i j) (mul_pos (hrho i) (hrho j)).le) hD
    (symGraph K rho) (fun i j => rfl) hS i

/-- **`prop:moments`(ii).** `0 ≤ m_k ≤ N` for all `k`; `1 ≤ m_{2k}` (if `N > 0`);
    `m_{2k+2} ≤ m_{2k}`; and `m_k ≤ m_2` for `k ≥ 2`. Here `m_k = Tr P^k`. -/
theorem moments_bounds (K : n → n → ℝ) (rho : n → ℝ) (hK : ∀ i j, K i j = K j i)
    (hK0 : ∀ i j, 0 ≤ K i j) (hrho : ∀ i, 0 < rho i)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) (k : ℕ) :
    0 ≤ (walkMatrix K rho ^ k).trace ∧
    (walkMatrix K rho ^ k).trace ≤ (Fintype.card n : ℝ) ∧
    (0 < Fintype.card n → 1 ≤ (walkMatrix K rho ^ (2 * k)).trace) ∧
    (walkMatrix K rho ^ (2 * k + 2)).trace ≤ (walkMatrix K rho ^ (2 * k)).trace ∧
    (2 ≤ k → (walkMatrix K rho ^ k).trace ≤ (walkMatrix K rho ^ 2).trace) := by
  have hS := symGraph_isHermitian K rho hK
  have hmem := mom_eig_mem K rho hK hK0 hrho hD hS
  have hsq : ∀ i, hS.eigenvalues i ^ 2 ≤ 1 := fun i => by
    have := hmem i
    nlinarith
  have e : ∀ j, (walkMatrix K rho ^ j).trace = ∑ i, hS.eigenvalues i ^ j := fun j => by
    rw [← moments_trace_eq K rho hD j, trace_pow_eq_sum_eigenvalues _ hS j]
  have hb := CTG.Reals.TraceG29.symGraph_trace_bounds K rho hK hK0 hrho hD k
  rw [moments_trace_eq K rho hD k, moments_trace_eq K rho hD 2] at hb
  refine ⟨?_, (le_abs_self _).trans hb.1, ?_, ?_, fun h2 => (le_abs_self _).trans (hb.2 h2)⟩
  · unfold Matrix.trace
    exact Finset.sum_nonneg fun i _ => (walk_pow_stoch K rho hK0 hrho hD k i i).1
  · intro h0
    have htop := symGraph_top_eigenvalue K rho hK hK0 hrho hD hS h0
    have h1 : hS.eigenvalues ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨0, h0⟩) = 1 := by
      simpa [IsHermitian.eigenvalues] using htop
    rw [e]
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ hS.eigenvalues i ^ (2 * k) := fun i _ => by
      rw [pow_mul]; exact pow_nonneg (pow_two_nonneg _) k
    have := Finset.single_le_sum hnn (Finset.mem_univ
      ((Fintype.equivOfCardEq (Fintype.card_fin _)) ⟨0, h0⟩))
    rw [h1, one_pow] at this
    exact this
  · rw [e, e]
    refine Finset.sum_le_sum fun i _ => ?_
    have hnn : 0 ≤ hS.eigenvalues i ^ (2 * k) := by
      rw [pow_mul]; exact pow_nonneg (pow_two_nonneg _) k
    calc hS.eigenvalues i ^ (2 * k + 2) = hS.eigenvalues i ^ (2 * k) * hS.eigenvalues i ^ 2 := by
          rw [pow_add]
      _ ≤ hS.eigenvalues i ^ (2 * k) * 1 := mul_le_mul_of_nonneg_left (hsq i) hnn
      _ = hS.eigenvalues i ^ (2 * k) := mul_one _

/-- `m_k ≤ max(m_1, m_2)` for every `k ≥ 1`. -/
theorem moments_le_max (K : n → n → ℝ) (rho : n → ℝ) (hK : ∀ i j, K i j = K j i)
    (hK0 : ∀ i j, 0 ≤ K i j) (hrho : ∀ i, 0 < rho i)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) {k : ℕ} (hk : 1 ≤ k) :
    (walkMatrix K rho ^ k).trace
      ≤ max (walkMatrix K rho ^ 1).trace (walkMatrix K rho ^ 2).trace := by
  rcases Nat.lt_or_ge k 2 with h | h
  · have : k = 1 := by omega
    subst this
    exact le_max_left _ _
  · exact ((moments_bounds K rho hK hK0 hrho hD k).2.2.2.2 h).trans (le_max_right _ _)

/-- `e^τ Tr exp(τ(S-1)) = ∑_i e^{τ s_i}` for a real symmetric matrix. -/
theorem exp_mul_heat_trace (S : Matrix n n ℝ) (hS : S.IsHermitian) (τ : ℝ) :
    Real.exp τ * (NormedSpace.exp (τ • (S - 1))).trace
      = ∑ i, Real.exp (hS.eigenvalues i * τ) := by
  rw [trace_exp_heat S hS τ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- **`prop:moments`(iii), as a power series:** for a real symmetric `S` and every real `τ`,
    `e^τ Tr exp(τ(S-1)) = ∑_k τ^k Tr S^k / k!`. -/
theorem moments_series_sym (S : Matrix n n ℝ) (hS : S.IsHermitian) (τ : ℝ) :
    HasSum (fun k : ℕ => τ ^ k / (k.factorial : ℝ) * (S ^ k).trace)
      (Real.exp τ * (NormedSpace.exp (τ • (S - 1))).trace) := by
  have h := (poisson_representation_matrix S hS τ).mul_left (Real.exp τ)
  have e1 : Real.exp τ * Real.exp (-τ) = 1 := by rw [← Real.exp_add]; simp
  convert h using 1
  funext k
  calc τ ^ k / (k.factorial : ℝ) * (S ^ k).trace
      = Real.exp τ * Real.exp (-τ) * (τ ^ k / (k.factorial : ℝ)) * (S ^ k).trace := by
        rw [e1, one_mul]
    _ = Real.exp τ * (Real.exp (-τ) * (τ ^ k / (k.factorial : ℝ)) * (S ^ k).trace) := by ring

/-- Iterated derivatives of a finite sum of exponentials. -/
theorem iteratedDeriv_sum_exp {ι : Type*} (I : Finset ι) (s : ι → ℝ) (k : ℕ) :
    iteratedDeriv k (fun τ : ℝ => ∑ i ∈ I, Real.exp (s i * τ))
      = fun τ => ∑ i ∈ I, s i ^ k * Real.exp (s i * τ) := by
  induction k with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext τ
    have h : HasDerivAt (fun τ : ℝ => ∑ i ∈ I, s i ^ k * Real.exp (s i * τ))
        (∑ i ∈ I, s i ^ (k + 1) * Real.exp (s i * τ)) τ := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      have h1 : HasDerivAt (fun τ : ℝ => s i * τ) (s i) τ := by
        simpa using (hasDerivAt_id τ).const_mul (s i)
      have h2 := (h1.exp).const_mul (s i ^ k)
      convert h2 using 1
      ring
    exact h.deriv

/-- **`prop:moments`(iii) for a real symmetric matrix:** `Tr S^k` is the `k`-th derivative of
    `τ ↦ e^τ Tr exp(τ(S-1))` at `τ = 0`. -/
theorem moments_iteratedDeriv_sym (S : Matrix n n ℝ) (hS : S.IsHermitian) (k : ℕ) :
    iteratedDeriv k (fun τ : ℝ => Real.exp τ * (NormedSpace.exp (τ • (S - 1))).trace) 0
      = (S ^ k).trace := by
  have e : (fun τ : ℝ => Real.exp τ * (NormedSpace.exp (τ • (S - 1))).trace)
      = fun τ : ℝ => ∑ i, Real.exp (hS.eigenvalues i * τ) :=
    funext fun τ => exp_mul_heat_trace S hS τ
  rw [e, iteratedDeriv_sum_exp, trace_pow_eq_sum_eigenvalues S hS k]
  simp

/-- **`prop:moments`(iii) for the graph:** `e^τ Tr e^{-tL} = ∑_k τ^k m_k / k!` with
    `m_k = Tr P^k`, for every real `τ`, and `m_k = d^k/dτ^k [e^τ Tr e^{-tL}]` at `τ = 0`. -/
theorem moments_series (K : n → n → ℝ) (rho : n → ℝ) (hK : ∀ i j, K i j = K j i)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) :
    (∀ τ : ℝ, HasSum (fun k : ℕ => τ ^ k / (k.factorial : ℝ) * (walkMatrix K rho ^ k).trace)
      (Real.exp τ * (NormedSpace.exp (τ • (symGraph K rho - 1))).trace)) ∧
    ∀ k : ℕ, iteratedDeriv k
        (fun τ : ℝ => Real.exp τ * (NormedSpace.exp (τ • (symGraph K rho - 1))).trace) 0
      = (walkMatrix K rho ^ k).trace := by
  have hS := symGraph_isHermitian K rho hK
  constructor
  · intro τ
    have h := moments_series_sym (symGraph K rho) hS τ
    simpa only [moments_trace_eq K rho hD] using h
  · intro k
    rw [moments_iteratedDeriv_sym _ hS k, moments_trace_eq K rho hD k]

end Moments

/-! #### `cor:subtractions`: the differences between the subtractions (deterministic) -/

section Subtractions

/-- One term of (a): `0 ≤ e^{-τ(1-p)} - e^{-τ} ≤ τ p e^{-τ(1-q)}` for `0 ≤ p ≤ q`, `τ ≥ 0`. -/
theorem subtraction_a_mode {τ p q : ℝ} (hτ : 0 ≤ τ) (hp : 0 ≤ p) (hpq : p ≤ q) :
    0 ≤ Real.exp (-(τ * (1 - p))) - Real.exp (-τ) ∧
    Real.exp (-(τ * (1 - p))) - Real.exp (-τ) ≤ τ * p * Real.exp (-(τ * (1 - q))) := by
  have hτp := mul_nonneg hτ hp
  have h1 : Real.exp (-τ) ≤ Real.exp (-(τ * (1 - p))) := Real.exp_le_exp.2 (by nlinarith)
  have e : Real.exp (-τ) = Real.exp (-(τ * (1 - p))) * Real.exp (-(τ * p)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : 1 - τ * p ≤ Real.exp (-(τ * p)) := by
    have := Real.add_one_le_exp (-(τ * p)); linarith
  have hE := Real.exp_pos (-(τ * (1 - p)))
  have h3 : Real.exp (-(τ * (1 - p))) ≤ Real.exp (-(τ * (1 - q))) :=
    Real.exp_le_exp.2 (by nlinarith [mul_nonneg hτ (sub_nonneg.2 hpq)])
  refine ⟨by linarith, ?_⟩
  have h4 := mul_le_mul_of_nonneg_left h2 hE.le
  have h5 := mul_le_mul_of_nonneg_left h3 hτp
  rw [e]
  nlinarith

/-- **`cor:subtractions`(a), deterministic part.** If `0 ≤ p_i ≤ q` for all `i` and `τ ≥ 0`:
    `0 ≤ ∑_i e^{-τ(1-p_i)} - N e^{-τ} ≤ τ e^{-τ(1-q)} ∑_i p_i`. (The paper: `q = 1/2`.) -/
theorem subtraction_a_modes {ι : Type*} [Fintype ι] (p : ι → ℝ) {τ q : ℝ} (hτ : 0 ≤ τ)
    (hp : ∀ i, 0 ≤ p i) (hpq : ∀ i, p i ≤ q) :
    0 ≤ ∑ i, Real.exp (-(τ * (1 - p i))) - (Fintype.card ι : ℝ) * Real.exp (-τ) ∧
    ∑ i, Real.exp (-(τ * (1 - p i))) - (Fintype.card ι : ℝ) * Real.exp (-τ)
      ≤ τ * Real.exp (-(τ * (1 - q))) * ∑ i, p i := by
  have e : ∑ i, Real.exp (-(τ * (1 - p i))) - (Fintype.card ι : ℝ) * Real.exp (-τ)
      = ∑ i, (Real.exp (-(τ * (1 - p i))) - Real.exp (-τ)) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [e]
  refine ⟨Finset.sum_nonneg fun i _ => (subtraction_a_mode hτ (hp i) (hpq i)).1, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := (subtraction_a_mode hτ (hp i) (hpq i)).2
  linarith

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **`cor:subtractions`(a) for the graph, deterministic part:** with `p_i = P_ii ≤ q`,
    `0 ≤ ∑_i e^{-τ(1-p_i)} - N e^{-τ} ≤ τ e^{-τ(1-q)} m_1`, `m_1 = Tr P`. Hence the two subtracted
    traces `Tr e^{-tL} - N e^{-τ}` and `Tr e^{-tL} - ∑_i e^{-τ(1-p_i)}` differ by at most
    `τ e^{-τ(1-q)} m_1`. -/
theorem subtraction_a (K : n → n → ℝ) (rho : n → ℝ) (hK0 : ∀ i j, 0 ≤ K i j)
    (hrho : ∀ i, 0 < rho i) {τ q : ℝ} (hτ : 0 ≤ τ) (hq : ∀ i, walkMatrix K rho i i ≤ q) :
    0 ≤ ∑ i, Real.exp (-(τ * (1 - walkMatrix K rho i i))) - (Fintype.card n : ℝ) * Real.exp (-τ) ∧
    ∑ i, Real.exp (-(τ * (1 - walkMatrix K rho i i))) - (Fintype.card n : ℝ) * Real.exp (-τ)
      ≤ τ * Real.exp (-(τ * (1 - q))) * (walkMatrix K rho ^ 1).trace := by
  have h := subtraction_a_modes (fun i => walkMatrix K rho i i) hτ
    (fun i => mom_walk_nonneg K rho hK0 hrho i i) hq
  simpa [Matrix.trace] using h

/-- **`cor:subtractions`(b), deterministic part.** For `τ ≥ 0` and `m ≥ 1`, with
    `B = max(m_1, m_2)`:
    `0 ≤ e^{-τ} ∑_{k<m} τ^k/k! Tr P^k - N e^{-τ} ≤ B e^{-τ} ∑_{1≤k<m} τ^k/k!`. -/
theorem subtraction_b (K : n → n → ℝ) (rho : n → ℝ) (hK : ∀ i j, K i j = K j i)
    (hK0 : ∀ i j, 0 ≤ K i j) (hrho : ∀ i, 0 < rho i)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) {τ : ℝ} (hτ : 0 ≤ τ) (m : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (m + 1), pw τ k * (walkMatrix K rho ^ k).trace
        - (Fintype.card n : ℝ) * Real.exp (-τ) ∧
    ∑ k ∈ Finset.range (m + 1), pw τ k * (walkMatrix K rho ^ k).trace
        - (Fintype.card n : ℝ) * Real.exp (-τ)
      ≤ max (walkMatrix K rho ^ 1).trace (walkMatrix K rho ^ 2).trace
          * ∑ k ∈ Finset.range m, pw τ (k + 1) := by
  have e : ∑ k ∈ Finset.range (m + 1), pw τ k * (walkMatrix K rho ^ k).trace
        - (Fintype.card n : ℝ) * Real.exp (-τ)
      = ∑ k ∈ Finset.range m, pw τ (k + 1) * (walkMatrix K rho ^ (k + 1)).trace := by
    rw [Finset.sum_range_succ', pw_zero, moments_zero]
    ring
  rw [e]
  constructor
  · exact Finset.sum_nonneg fun k _ => mul_nonneg (pw_nonneg hτ _)
      (moments_bounds K rho hK hK0 hrho hD (k + 1)).1
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right
      (moments_le_max K rho hK hK0 hrho hD (Nat.succ_le_succ (Nat.zero_le k))) (pw_nonneg hτ _)

/-- End of the proof of `cor:subtractions`, the term `k = 1`:
    `τ e^{-τ/2} ≤ (1/τ₀) τ² e^{-κτ}` for `τ ≥ τ₀ > 0`, `κ ≤ 1/2`. -/
theorem subtraction_arith_one {τ τ0 κ : ℝ} (hτ0 : 0 < τ0) (hτ : τ0 ≤ τ) (hκ : κ ≤ 1 / 2) :
    τ * Real.exp (-(τ / 2)) ≤ 1 / τ0 * τ ^ 2 * Real.exp (-(κ * τ)) := by
  have hτp : 0 < τ := lt_of_lt_of_le hτ0 hτ
  have h1 : Real.exp (-(τ / 2)) ≤ Real.exp (-(κ * τ)) := Real.exp_le_exp.2 (by nlinarith)
  have h2 : τ ≤ 1 / τ0 * τ ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hτ0]
    nlinarith
  exact mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)

/-- End of the proof of `cor:subtractions`, the terms `k = j + 2 ≥ 2`:
    `τ^{j+2} e^{-τ/2} ≤ (j!/(1/2-κ)^j) τ² e^{-κτ}` for `τ ≥ 0`, `κ < 1/2`. -/
theorem subtraction_arith {τ κ : ℝ} (hτ : 0 ≤ τ) (hκ : κ < 1 / 2) (j : ℕ) :
    τ ^ (j + 2) * Real.exp (-(τ / 2))
      ≤ (j.factorial : ℝ) / (1 / 2 - κ) ^ j * τ ^ 2 * Real.exp (-(κ * τ)) := by
  have ha : 0 < 1 / 2 - κ := by linarith
  have hy : 0 ≤ (1 / 2 - κ) * τ := mul_nonneg ha.le hτ
  have h1 := Real.pow_div_factorial_le_exp (x := (1 / 2 - κ) * τ) hy j
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hap : 0 < (1 / 2 - κ) ^ j := pow_pos ha j
  have h2 : τ ^ j ≤ (j.factorial : ℝ) / (1 / 2 - κ) ^ j * Real.exp ((1 / 2 - κ) * τ) := by
    rw [div_le_iff₀ hf, mul_pow] at h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hap]
    linarith
  have e : Real.exp ((1 / 2 - κ) * τ) * Real.exp (-(τ / 2)) = Real.exp (-(κ * τ)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc τ ^ (j + 2) * Real.exp (-(τ / 2))
      = τ ^ j * (τ ^ 2 * Real.exp (-(τ / 2))) := by ring
    _ ≤ (j.factorial : ℝ) / (1 / 2 - κ) ^ j * Real.exp ((1 / 2 - κ) * τ)
          * (τ ^ 2 * Real.exp (-(τ / 2))) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg (pow_two_nonneg τ) (Real.exp_pos _).le)
    _ = (j.factorial : ℝ) / (1 / 2 - κ) ^ j * τ ^ 2
          * (Real.exp ((1 / 2 - κ) * τ) * Real.exp (-(τ / 2))) := by ring
    _ = (j.factorial : ℝ) / (1 / 2 - κ) ^ j * τ ^ 2 * Real.exp (-(κ * τ)) := by rw [e]

/-- `cor:subtractions`(a) with the rate of the last step of the proof: if `P_ii ≤ 1/2` for all
    `i`, `τ ≥ τ₀ > 0` and `κ ≤ 1/2`, then
    `0 ≤ ∑_i e^{-τ(1-p_i)} - N e^{-τ} ≤ (1/τ₀) τ² e^{-κτ} m_1`. -/
theorem subtraction_a_rate (K : n → n → ℝ) (rho : n → ℝ) (hK0 : ∀ i j, 0 ≤ K i j)
    (hrho : ∀ i, 0 < rho i) {τ τ0 κ : ℝ} (hτ0 : 0 < τ0) (hτ : τ0 ≤ τ) (hκ : κ ≤ 1 / 2)
    (hq : ∀ i, walkMatrix K rho i i ≤ 1 / 2) :
    0 ≤ ∑ i, Real.exp (-(τ * (1 - walkMatrix K rho i i))) - (Fintype.card n : ℝ) * Real.exp (-τ) ∧
    ∑ i, Real.exp (-(τ * (1 - walkMatrix K rho i i))) - (Fintype.card n : ℝ) * Real.exp (-τ)
      ≤ 1 / τ0 * τ ^ 2 * Real.exp (-(κ * τ)) * (walkMatrix K rho ^ 1).trace := by
  obtain ⟨h1, h2⟩ := subtraction_a K rho hK0 hrho (le_trans hτ0.le hτ) hq
  refine ⟨h1, h2.trans ?_⟩
  have hm : 0 ≤ (walkMatrix K rho ^ 1).trace := by
    simp only [pow_one, Matrix.trace, Matrix.diag_apply]
    exact Finset.sum_nonneg fun i _ => mom_walk_nonneg K rho hK0 hrho i i
  have e : -(τ * (1 - 1 / 2)) = -(τ / 2) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (subtraction_arith_one hτ0 hτ hκ) hm

end Subtractions

/-! #### The display `eq:window`: concentration of the Poisson weights (deterministic) -/

section Window

/-- Chernoff bound for the lower tail of the Poisson weights:
    `e^{-τ} ∑_{k ∈ s} τ^k/k! ≤ e^{-τ(1 - ln 2)/2}` if every `k ∈ s` satisfies `k ≤ τ/2`. -/
theorem poisson_lower_tail {τ : ℝ} (hτ : 0 ≤ τ) (s : Finset ℕ)
    (hs : ∀ k ∈ s, (k : ℝ) ≤ τ / 2) :
    ∑ k ∈ s, pw τ k ≤ Real.exp (-(τ * (1 - Real.log 2) / 2)) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hterm : ∀ k ∈ s, pw τ k
      ≤ Real.exp (-τ) * Real.exp (τ / 2 * Real.log 2) * ((τ / 2) ^ k / (k.factorial : ℝ)) := by
    intro k hk
    have h2 : (2 : ℝ) ^ k ≤ Real.exp (τ / 2 * Real.log 2) := by
      have e : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [e]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hs k hk) hl)
    have hq : 0 ≤ (τ / 2) ^ k / (k.factorial : ℝ) :=
      div_nonneg (pow_nonneg (by linarith) k) (Nat.cast_nonneg _)
    have e : pw τ k = Real.exp (-τ) * (2 : ℝ) ^ k * ((τ / 2) ^ k / (k.factorial : ℝ)) := by
      unfold pw
      rw [div_pow]
      have : (2 : ℝ) ^ k ≠ 0 := by positivity
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hq
  have hsub : s ⊆ Finset.range (s.sup id + 1) := fun k hk =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have hsum : ∑ k ∈ s, (τ / 2) ^ k / (k.factorial : ℝ) ≤ Real.exp (τ / 2) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
      div_nonneg (pow_nonneg (by linarith) k) (Nat.cast_nonneg _))).trans
      (Real.sum_le_exp_of_nonneg (by linarith) _)
  calc ∑ k ∈ s, pw τ k
      ≤ ∑ k ∈ s, Real.exp (-τ) * Real.exp (τ / 2 * Real.log 2)
          * ((τ / 2) ^ k / (k.factorial : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.exp (-τ) * Real.exp (τ / 2 * Real.log 2)
          * ∑ k ∈ s, (τ / 2) ^ k / (k.factorial : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-τ) * Real.exp (τ / 2 * Real.log 2) * Real.exp (τ / 2) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-(τ * (1 - Real.log 2) / 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Chernoff bound for the upper tail of the Poisson weights:
    `e^{-τ} ∑_{k ∈ s} τ^k/k! ≤ e^{-τ(2 ln 2 - 1)}` if every `k ∈ s` satisfies `k ≥ 2τ`. -/
theorem poisson_upper_tail {τ : ℝ} (hτ : 0 ≤ τ) (s : Finset ℕ)
    (hs : ∀ k ∈ s, 2 * τ ≤ (k : ℝ)) :
    ∑ k ∈ s, pw τ k ≤ Real.exp (-(τ * (2 * Real.log 2 - 1))) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hterm : ∀ k ∈ s, pw τ k
      ≤ Real.exp (-τ) * Real.exp (-(2 * τ * Real.log 2))
          * ((2 * τ) ^ k / (k.factorial : ℝ)) := by
    intro k hk
    have h2 : Real.exp (-((k : ℝ) * Real.log 2)) ≤ Real.exp (-(2 * τ * Real.log 2)) :=
      Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right (hs k hk) hl; linarith)
    have e2 : Real.exp (-((k : ℝ) * Real.log 2)) * (2 : ℝ) ^ k = 1 := by
      have e : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      rw [e, ← Real.exp_add]; simp
    have hq : 0 ≤ (2 * τ) ^ k / (k.factorial : ℝ) :=
      div_nonneg (pow_nonneg (by linarith) k) (Nat.cast_nonneg _)
    have e : pw τ k = Real.exp (-τ) * Real.exp (-((k : ℝ) * Real.log 2))
        * ((2 * τ) ^ k / (k.factorial : ℝ)) := by
      unfold pw
      rw [mul_pow]
      calc Real.exp (-τ) * (τ ^ k / (k.factorial : ℝ))
          = Real.exp (-τ) * (Real.exp (-((k : ℝ) * Real.log 2)) * (2 : ℝ) ^ k)
              * (τ ^ k / (k.factorial : ℝ)) := by rw [e2, mul_one]
        _ = Real.exp (-τ) * Real.exp (-((k : ℝ) * Real.log 2))
              * ((2 : ℝ) ^ k * τ ^ k / (k.factorial : ℝ)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hq
  have hsub : s ⊆ Finset.range (s.sup id + 1) := fun k hk =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have hsum : ∑ k ∈ s, (2 * τ) ^ k / (k.factorial : ℝ) ≤ Real.exp (2 * τ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ =>
      div_nonneg (pow_nonneg (by linarith) k) (Nat.cast_nonneg _))).trans
      (Real.sum_le_exp_of_nonneg (by linarith) _)
  calc ∑ k ∈ s, pw τ k
      ≤ ∑ k ∈ s, Real.exp (-τ) * Real.exp (-(2 * τ * Real.log 2))
          * ((2 * τ) ^ k / (k.factorial : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.exp (-τ) * Real.exp (-(2 * τ * Real.log 2))
          * ∑ k ∈ s, (2 * τ) ^ k / (k.factorial : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-τ) * Real.exp (-(2 * τ * Real.log 2)) * Real.exp (2 * τ) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-(τ * (2 * Real.log 2 - 1))) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

variable {n : Type} [Fintype n] [DecidableEq n]

/-- **The display `eq:window`, deterministic form.** For a real symmetric `S`, `τ ≥ 0` and a number
    `B` with `|Tr S^k| ≤ B` for all `k ≥ 1`:
    `|Tr exp(τ(S-1)) - N e^{-τ} - e^{-τ} ∑_{τ/2 < k < 2τ} τ^k/k! Tr S^k|
        ≤ B (e^{-τ(1 - ln 2)/2} + e^{-τ(2 ln 2 - 1)})`.
    (Both exponents are at least `0.15 τ`; in the paper `B = C ξ^{-d}`, probabilistic.) -/
theorem window_bound (S : Matrix n n ℝ) (hS : S.IsHermitian) {τ B : ℝ} (hτ : 0 ≤ τ)
    (hB : ∀ k : ℕ, 1 ≤ k → |(S ^ k).trace| ≤ B) :
    |(NormedSpace.exp (τ • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-τ)
        - ∑ k ∈ (Finset.range ⌈2 * τ⌉₊).filter (fun k : ℕ => τ / 2 < (k : ℝ)),
            pw τ k * (S ^ k).trace|
      ≤ B * (Real.exp (-(τ * (1 - Real.log 2) / 2))
          + Real.exp (-(τ * (2 * Real.log 2 - 1)))) := by
  classical
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1 le_rfl)
  obtain ⟨W, hW⟩ : ∃ W : Finset ℕ,
      W = (Finset.range ⌈2 * τ⌉₊).filter (fun k : ℕ => τ / 2 < (k : ℝ)) := ⟨_, rfl⟩
  rw [← hW]
  have h0W : (0 : ℕ) ∉ W := by
    rw [hW, Finset.mem_filter]
    rintro ⟨-, h⟩
    simp at h
    linarith
  have hf : HasSum (fun k : ℕ => pw τ k * (S ^ k).trace)
      (NormedSpace.exp (τ • (S - 1))).trace := poisson_representation_matrix S hS τ
  have hind : HasSum (fun k : ℕ => if k ∈ insert 0 W then pw τ k * (S ^ k).trace else 0)
      (∑ k ∈ insert 0 W, pw τ k * (S ^ k).trace) := by
    have this : HasSum (fun k : ℕ => if k ∈ insert 0 W then pw τ k * (S ^ k).trace else 0)
        (∑ b ∈ insert 0 W, (fun k : ℕ =>
          if k ∈ insert 0 W then pw τ k * (S ^ k).trace else 0) b) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => if_neg hb)
    convert this using 1
    exact Finset.sum_congr rfl fun k hk => (if_pos hk).symm
  have hg := hf.sub hind
  have e0 : ∑ k ∈ insert 0 W, pw τ k * (S ^ k).trace
      = (Fintype.card n : ℝ) * Real.exp (-τ) + ∑ k ∈ W, pw τ k * (S ^ k).trace := by
    rw [Finset.sum_insert h0W, pw_zero]
    simp [Matrix.trace_one, mul_comm]
  rw [e0] at hg
  -- the two tails
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℝ, L = fun k : ℕ => if (k : ℝ) ≤ τ / 2 then pw τ k else 0 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : ℕ → ℝ, U = fun k : ℕ => if 2 * τ ≤ (k : ℝ) then pw τ k else 0 := ⟨_, rfl⟩
  have hL0 : ∀ k, 0 ≤ L k := fun k => by
    rw [hL]; beta_reduce; split_ifs
    · exact pw_nonneg hτ k
    · exact le_rfl
  have hU0 : ∀ k, 0 ≤ U k := fun k => by
    rw [hU]; beta_reduce; split_ifs
    · exact pw_nonneg hτ k
    · exact le_rfl
  have hLs : Summable L := Summable.of_nonneg_of_le hL0 (fun k => by
    rw [hL]; beta_reduce; split_ifs
    · exact le_rfl
    · exact pw_nonneg hτ k) (pw_hasSum τ).summable
  have hUs : Summable U := Summable.of_nonneg_of_le hU0 (fun k => by
    rw [hU]; beta_reduce; split_ifs
    · exact le_rfl
    · exact pw_nonneg hτ k) (pw_hasSum τ).summable
  have hLt : ∑' k, L k ≤ Real.exp (-(τ * (1 - Real.log 2) / 2)) := by
    refine Real.tsum_le_of_sum_le hL0 fun s => ?_
    rw [hL, ← Finset.sum_filter]
    exact poisson_lower_tail hτ _ fun k hk => (Finset.mem_filter.1 hk).2
  have hUt : ∑' k, U k ≤ Real.exp (-(τ * (2 * Real.log 2 - 1))) := by
    refine Real.tsum_le_of_sum_le hU0 fun s => ?_
    rw [hU, ← Finset.sum_filter]
    exact poisson_upper_tail hτ _ fun k hk => (Finset.mem_filter.1 hk).2
  have hR : HasSum (fun k => B * (L k + U k)) (B * (∑' k, L k + ∑' k, U k)) :=
    (hLs.hasSum.add hUs.hasSum).mul_left B
  have hbd : ∀ k : ℕ, |(fun k : ℕ => pw τ k * (S ^ k).trace) k
      - (fun k : ℕ => if k ∈ insert 0 W then pw τ k * (S ^ k).trace else 0) k|
      ≤ B * (L k + U k) := by
    intro k
    beta_reduce
    by_cases hk : k ∈ insert 0 W
    · rw [if_pos hk, sub_self, abs_zero]
      exact mul_nonneg hB0 (add_nonneg (hL0 k) (hU0 k))
    · rw [if_neg hk, sub_zero, abs_mul, abs_of_nonneg (pw_nonneg hτ k)]
      rw [Finset.mem_insert, not_or] at hk
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk.1
      have hpw : pw τ k ≤ L k + U k := by
        by_cases h1 : (k : ℝ) ≤ τ / 2
        · have : L k = pw τ k := by rw [hL]; exact if_pos h1
          have := hU0 k
          linarith
        · have h2 : 2 * τ ≤ (k : ℝ) := by
            by_contra h3
            apply hk.2
            rw [hW, Finset.mem_filter, Finset.mem_range]
            exact ⟨Nat.lt_ceil.2 (not_le.1 h3), not_le.1 h1⟩
          have : U k = pw τ k := by rw [hU]; exact if_pos h2
          have := hL0 k
          linarith
      calc pw τ k * |(S ^ k).trace| ≤ pw τ k * B :=
            mul_le_mul_of_nonneg_left (hB k hk1) (pw_nonneg hτ k)
        _ ≤ (L k + U k) * B := mul_le_mul_of_nonneg_right hpw hB0
        _ = B * (L k + U k) := mul_comm _ _
  have habs : |(NormedSpace.exp (τ • (S - 1))).trace
      - ((Fintype.card n : ℝ) * Real.exp (-τ) + ∑ k ∈ W, pw τ k * (S ^ k).trace)|
      ≤ B * (∑' k, L k + ∑' k, U k) := by
    rw [abs_le]
    constructor
    · exact hasSum_le (fun k => (abs_le.1 (hbd k)).1) hR.neg hg
    · exact hasSum_le (fun k => (abs_le.1 (hbd k)).2) hg hR
  have e : (NormedSpace.exp (τ • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-τ)
        - ∑ k ∈ W, pw τ k * (S ^ k).trace
      = (NormedSpace.exp (τ • (S - 1))).trace
        - ((Fintype.card n : ℝ) * Real.exp (-τ) + ∑ k ∈ W, pw τ k * (S ^ k).trace) := by ring
  rw [e]
  exact habs.trans (mul_le_mul_of_nonneg_left (add_le_add hLt hUt) hB0)

/-- `eq:window` for the graph: `Tr P^k` in place of `Tr S^k`, with `B = max(m_1, m_2)`. -/
theorem window_bound_graph (K : n → n → ℝ) (rho : n → ℝ) (hK : ∀ i j, K i j = K j i)
    (hK0 : ∀ i j, 0 ≤ K i j) (hrho : ∀ i, 0 < rho i)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) {τ : ℝ} (hτ : 0 ≤ τ) :
    |(NormedSpace.exp (τ • (symGraph K rho - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-τ)
        - ∑ k ∈ (Finset.range ⌈2 * τ⌉₊).filter (fun k : ℕ => τ / 2 < (k : ℝ)),
            pw τ k * (walkMatrix K rho ^ k).trace|
      ≤ max (walkMatrix K rho ^ 1).trace (walkMatrix K rho ^ 2).trace
          * (Real.exp (-(τ * (1 - Real.log 2) / 2))
            + Real.exp (-(τ * (2 * Real.log 2 - 1)))) := by
  have hS := symGraph_isHermitian K rho hK
  have h := window_bound (symGraph K rho) hS hτ
    (B := max (walkMatrix K rho ^ 1).trace (walkMatrix K rho ^ 2).trace) (fun k hk => by
      rw [moments_trace_eq K rho hD k,
        abs_of_nonneg (moments_bounds K rho hK hK0 hrho hD k).1]
      exact moments_le_max K rho hK hK0 hrho hD hk)
  simpa only [moments_trace_eq K rho hD] using h

/-- The two exponents in `eq:window` are at least `0.15`: `(1 - ln 2)/2 ≥ 0.15` and
    `2 ln 2 - 1 ≥ 0.15`. -/
theorem window_exponents :
    (0.15 : ℝ) ≤ (1 - Real.log 2) / 2 ∧ (0.15 : ℝ) ≤ 2 * Real.log 2 - 1 := by
  have h1 := Real.log_two_lt_d9
  have h2 := Real.log_two_gt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

end Window

/-! ### Part B: `thm:profileHS` (profiles with a jump) for lists of eigenvalues, and the indicator
of an interval (`d = 1`)

Conventions as in `OlderParts`: `σ` is the `σ` of the PAPER, `τ = t/σ`, a "manifold" is a list
`lam : ι → ℝ` with `PopulationRate.IsSpectrum lam`.

* `ProfileHypHS F β c3 u1 δ`: (F1) on `[0, u₁]`, (F2) as `|F| ≤ 1 - δ` on `[u₁, ∞)`, the smallness
  condition on `u₁` of `OlderParts.ProfileHyp`; NO hypothesis (F3).
* `profTrHS lam F σ t m1 = e^{-τ}[τ m₁ + ∑_k φ(τ F(σλ_k))]`, `φ(x) = e^x - 1 - x`: the `T^F_σ(t)` of
  `thm:profileHS`, with `m₁` a free real number.
* `profileHS_i`, `profileHS_ii`: (i) and (ii) of `thm:profile` for these objects, with explicit
  constants and with `N_p(σ)` replaced by `Q(σ) = ∑_k F(σλ_k)²` (HYPOTHESIS: this series converges),
  plus the term `τ e^{-τ}|m₁|` in (i); (ii) for `n ≥ 2`.
* `profileHS_paper`: under (F3') in the form `Q(σ) ≤ B`, `|m₁| ≤ B` (the paper: `B = C_F σ^{-d/2}`)
  both remainders are at most `... + K (1+τ) e^{-cτ} [B + Θ(t/4)]`.
In contrast to the proof of the paper, Weyl's law is NOT used: the number of low modes is bounded by
`4 Q(σ)`, because `F ≥ 1/2` on the low modes.  So the constants do not depend on the manifold.

The indicator of an interval, `κ = ½·1_{[-1,1]}`, `d = 1`:
* `interval_fourier`: `∫_{-1}^{1} ½ cos(ζx) dx = sinc ζ`; `interval_moments`: `E X² = 1/3`,
  `E X⁴ = 1/5` (so `σ = ξ²/6` and `β = 3/5` by `eq:beta`; `eq:beta` itself is not formalised);
* `ballF u = sinc √(6u)`, so that `ballF (σ λ_n) = sinc(2πξ n)` for `σ = ξ²/6`, `λ_n = 4π² n²`
  (`ballF_eigen`);
* `sin_taylor`, `sinc_taylor`: `1 - x²/6 + x⁴/120 - x⁶/5040 ≤ sinc x ≤ 1 - x²/6 + x⁴/120` (`x ≥ 0`);
* `ballF_F1`: (F1) for ALL `u ≥ 0` with `β = 3/5`, `c₃ = 3/70`;
* `ballF_F2`: the second part of (F2): `|ballF u| ≤ 1 - min(1/2, 4u₁/5)` for `u ≥ u₁ > 0`;
* `ballF_hyp : ProfileHypHS ballF (3/5) (3/70) (1/24) (1/30)`;
* `sinc_sq_sum`: `∑_{n ∈ ℤ} sinc(a n)² ≤ 1 + 8/a` for `a > 0` (elementary; NOT Parseval's identity,
  which gives the exact value `π/a` for `a ≤ π`), hence (F3') in the form `Q(σ) ≤ 3/ξ` for `ξ ≤ 1`;
* `interval_profile`: (i) and (ii) for the interval indicator with `β = 3/5`.
NOT proved: Parseval's identity `∑ s_n² = 1/(2ξ)`, that `m₁ = 1/(2ξ)` is the diagonal value of the
normalised kernel, that the `s_n` are the eigenvalues of a convolution operator on the circle (only
the Fourier integral `interval_fourier`), general dimension (Bessel functions), the relative
deviations `β d(d+2)/8τ`, `(β-1) d(d+2)/8τ`.
-/

section ProfilesWithJump

/-- The hypotheses of `thm:profileHS` on the profile function without (F3'), with an explicit
    threshold `u₁` (cf. `OlderParts.ProfileHyp`). -/
structure ProfileHypHS (F : ℝ → ℝ) (β c3 u1 δ : ℝ) : Prop where
  c3_nonneg : 0 ≤ c3
  u1_pos : 0 < u1
  small : (5 * |β| + 9 * c3 + 18) * u1 ≤ 1
  δ_pos : 0 < δ
  F1 : ∀ u, 0 ≤ u → u ≤ u1 → |F u - (1 - u + β * u ^ 2 / 2)| ≤ c3 * u ^ 3
  F2 : ∀ u, u1 ≤ u → |F u| ≤ 1 - δ

/-- The exponential rate `min(δ/2, u₁/4)`. -/
noncomputable def profcHS (u1 δ : ℝ) : ℝ := min (δ / 2) (u1 / 4)

/-- The constant of the exponentially small terms in (i). -/
noncomputable def profKHS (β δ : ℝ) : ℝ := 4 + 1 / δ + 5 * (1 + |β|)

/-- The constant of the exponentially small terms in (ii). -/
noncomputable def profKHS2 (β : ℝ) : ℝ := 16 + 5 * (1 + |β - 1|)

theorem profcHS_facts {u1 δ : ℝ} (hu1 : 0 < u1) (hδ : 0 < δ) :
    0 < profcHS u1 δ ∧ profcHS u1 δ ≤ δ / 2 ∧ profcHS u1 δ ≤ u1 / 4 :=
  ⟨lt_min (by linarith) (by linarith), min_le_left _ _, min_le_right _ _⟩

/-- On a low mode `1/2 ≤ F(u) ≤ 1`. -/
theorem hs_low_value {F : ℝ → ℝ} {β c3 u1 δ : ℝ} (H : ProfileHypHS F β c3 u1 δ) {u : ℝ}
    (hu : 0 ≤ u) (hu1 : u ≤ u1) : 1 / 2 ≤ F u ∧ F u ≤ 1 := by
  obtain ⟨s1, s2, -⟩ := small_consequences H.c3_nonneg H.u1_pos.le H.small
  obtain ⟨-, w2⟩ := w_bound hu hu1 (by linarith) H.c3_nonneg s2 (H.F1 u hu hu1)
  obtain ⟨a, b⟩ := abs_le.1 w2
  constructor <;> linarith

/-- Low modes: the two subtracted terms `e^{-τ}(1 + τ s)` with `1/2 ≤ s ≤ 1`. -/
theorem hs_low_extra {τ s c : ℝ} (hτ : 0 ≤ τ) (hc : c ≤ 1) (h1 : 1 / 2 ≤ s) (h2 : s ≤ 1) :
    0 ≤ Real.exp (-τ) * (1 + τ * s) ∧
    Real.exp (-τ) * (1 + τ * s) ≤ 4 * ((1 + τ) * Real.exp (-(c * τ)) * s ^ 2) := by
  have hs0 : 0 ≤ s := by linarith
  have hτs : 0 ≤ τ * s := mul_nonneg hτ hs0
  have hEt := Real.exp_pos (-τ)
  have hEc := Real.exp_pos (-(c * τ))
  have e1 : Real.exp (-τ) ≤ Real.exp (-(c * τ)) :=
    Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hc hτ; linarith)
  have a : 1 + τ * s ≤ 1 + τ := by have := mul_le_mul_of_nonneg_left h2 hτ; linarith
  have b : Real.exp (-τ) * (1 + τ * s) ≤ Real.exp (-(c * τ)) * (1 + τ) :=
    mul_le_mul e1 a (by linarith) hEc.le
  have c4 : 1 ≤ 4 * s ^ 2 := by
    have := mul_le_mul h1 h1 (by norm_num) hs0
    rw [pow_two]; linarith
  have hX : 0 ≤ (1 + τ) * Real.exp (-(c * τ)) := mul_nonneg (by linarith) hEc.le
  have d := mul_le_mul_of_nonneg_left c4 hX
  refine ⟨mul_nonneg hEt.le (by linarith), ?_⟩
  calc Real.exp (-τ) * (1 + τ * s) ≤ (1 + τ) * Real.exp (-(c * τ)) * 1 := by
        rw [mul_one, mul_comm (1 + τ)]; exact b
    _ ≤ (1 + τ) * Real.exp (-(c * τ)) * (4 * s ^ 2) := d
    _ = 4 * ((1 + τ) * Real.exp (-(c * τ)) * s ^ 2) := by ring

/-- High modes: `0 ≤ e^{-τ} φ(τ s) ≤ (1/δ) (1+τ) e^{-cτ} s²` if `|s| ≤ 1 - δ`, `c ≤ δ/2`
    (the paper: `≤ ½ τ² s² e^{-δτ}`). -/
theorem hs_high_phi {τ s δ c : ℝ} (hτ : 0 ≤ τ) (hδ : 0 < δ) (hs : |s| ≤ 1 - δ)
    (hc : c ≤ δ / 2) :
    0 ≤ Real.exp (-τ) * (Real.exp (τ * s) - 1 - τ * s) ∧
    Real.exp (-τ) * (Real.exp (τ * s) - 1 - τ * s)
      ≤ 1 / δ * ((1 + τ) * Real.exp (-(c * τ)) * s ^ 2) := by
  have hs2 : 0 ≤ s ^ 2 := pow_two_nonneg _
  have hinv : 0 ≤ 1 / δ := by positivity
  obtain ⟨p1, p2⟩ := phi_two_sided (x := τ * s) (τ := τ * |s|)
    (by have := mul_le_mul_of_nonneg_left (neg_abs_le s) hτ; linarith)
    (mul_le_mul_of_nonneg_left (le_abs_self _) hτ)
  have hEt := Real.exp_pos (-τ)
  have hq : 0 ≤ (τ * s) ^ 2 / 2 := by positivity
  have q0 : 0 ≤ Real.exp (-τ) * (Real.exp (τ * s) - 1 - τ * s) :=
    mul_nonneg hEt.le ((mul_nonneg hq (Real.exp_pos _).le).trans p1)
  have q1 : Real.exp (-τ) * Real.exp (τ * |s|) ≤ Real.exp (-(δ * τ)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left hs hτ
    linarith
  have q2 : Real.exp (-(δ * τ)) = Real.exp (-(δ / 2 * τ)) * Real.exp (-(δ / 2 * τ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE2 := Real.exp_pos (-(δ / 2 * τ))
  have q3 : τ / 2 * Real.exp (-(δ / 2 * τ)) ≤ 1 / δ := by
    have h1 := Real.add_one_le_exp (δ / 2 * τ)
    have h2 : Real.exp (-(δ / 2 * τ)) * Real.exp (δ / 2 * τ) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_left h1 hE2.le
    have h4 : δ * (τ / 2 * Real.exp (-(δ / 2 * τ))) ≤ 1 := by
      have e : δ * (τ / 2 * Real.exp (-(δ / 2 * τ)))
          = Real.exp (-(δ / 2 * τ)) * (δ / 2 * τ + 1) - Real.exp (-(δ / 2 * τ)) := by ring
      rw [e]; linarith
    rw [le_div_iff₀ hδ]
    linarith
  have q4 : Real.exp (-(δ / 2 * τ)) ≤ Real.exp (-(c * τ)) :=
    Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hc hτ; linarith)
  refine ⟨q0, ?_⟩
  calc Real.exp (-τ) * (Real.exp (τ * s) - 1 - τ * s)
      ≤ Real.exp (-τ) * ((τ * s) ^ 2 / 2 * Real.exp (τ * |s|)) :=
        mul_le_mul_of_nonneg_left p2 hEt.le
    _ = (τ * s) ^ 2 / 2 * (Real.exp (-τ) * Real.exp (τ * |s|)) := by ring
    _ ≤ (τ * s) ^ 2 / 2 * Real.exp (-(δ * τ)) := mul_le_mul_of_nonneg_left q1 hq
    _ = τ / 2 * Real.exp (-(δ / 2 * τ)) * (τ * Real.exp (-(δ / 2 * τ)) * s ^ 2) := by
        rw [q2]; ring
    _ ≤ 1 / δ * (τ * Real.exp (-(δ / 2 * τ)) * s ^ 2) :=
        mul_le_mul_of_nonneg_right q3 (mul_nonneg (mul_nonneg hτ hE2.le) hs2)
    _ ≤ 1 / δ * ((1 + τ) * Real.exp (-(c * τ)) * s ^ 2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hs2) hinv
        exact mul_le_mul (by linarith) q4 hE2.le (by linarith)

/-- The continuum part of a high mode against the weight `A e^{-x/4}`, `A = (1+τ) e^{-cτ}`,
    `c ≤ u₁/4`. -/
theorem hs_high_cont {τ u u1 γ x c : ℝ} (hx : τ * u = x) (hτ : 1 ≤ τ) (hu1 : 0 ≤ u1)
    (hu : u1 ≤ u) (hc : c ≤ u1 / 4) :
    |Real.exp (-x) + γ * (x * u / 2) * Real.exp (-x)|
      ≤ 5 * (1 + |γ|) * ((1 + τ) * Real.exp (-(c * τ)) * Real.exp (-(x / 4))) := by
  have hτ0 : 0 ≤ τ := by linarith
  have hb := high_b (γ := γ) hx hτ hu1 hu
  have hx0 : 0 ≤ x := by rw [← hx]; exact mul_nonneg hτ0 (hu1.trans hu)
  have hEx := Real.exp_pos (-x)
  have hE4 := Real.exp_pos (-(x / 4))
  have hEc := Real.exp_pos (-(c * τ))
  have hβ5 : (0 : ℝ) ≤ 5 * (1 + |γ|) := by positivity
  have d2 : Real.exp (-(u1 * τ / 4)) ≤ Real.exp (-(c * τ)) :=
    Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hc hτ0; linarith)
  have d3 : Real.exp (-(u1 * τ / 4)) * Real.exp (-(x / 4))
      ≤ (1 + τ) * Real.exp (-(c * τ)) * Real.exp (-(x / 4)) := by
    refine mul_le_mul_of_nonneg_right ?_ hE4.le
    have := mul_nonneg hτ0 hEc.le
    linarith
  have d4 := mul_le_mul_of_nonneg_left d3 hβ5
  have hqq : 0 ≤ (x * u / 2) * Real.exp (-x) :=
    mul_nonneg (by have := mul_nonneg hx0 (hu1.trans hu); linarith) hEx.le
  have h4 : γ * ((x * u / 2) * Real.exp (-x)) ≤ |γ| * ((x * u / 2) * Real.exp (-x)) :=
    mul_le_mul_of_nonneg_right (le_abs_self γ) hqq
  have h5 : -(|γ| * ((x * u / 2) * Real.exp (-x))) ≤ γ * ((x * u / 2) * Real.exp (-x)) := by
    have := mul_le_mul_of_nonneg_right (neg_abs_le γ) hqq
    linarith
  have h6 := mul_nonneg (abs_nonneg γ) hqq
  rw [abs_le]
  constructor <;> linarith

/-- **`thm:profileHS`(i) for one mode**, low or high (`u = σλ`, `x = τu = tλ`, `τ ≥ 1`):
    the term `e^{-τ} φ(τ F(u))` against `e^{-x} + β (xu/2) e^{-x}`. -/
theorem profHS_mode {F : ℝ → ℝ} {β c3 u1 δ : ℝ} (H : ProfileHypHS F β c3 u1 δ)
    {τ u x : ℝ} (hx : τ * u = x) (hτ : 1 ≤ τ) (hu : 0 ≤ u) :
    |Real.exp (-τ) * (Real.exp (τ * F u) - 1 - τ * F u) - Real.exp (-x)
        - β * (x * u / 2) * Real.exp (-x)|
      ≤ (profB β c3 ^ 2 * (x * u) ^ 2 / 2 + c3 * (x * u * u)) * Real.exp (-(x / 2))
        + profKHS β δ * (1 + τ) * Real.exp (-(profcHS u1 δ * τ))
            * (F u ^ 2 + Real.exp (-(x / 4))) := by
  have hτ0 : 0 ≤ τ := by linarith
  obtain ⟨s1, s2, -⟩ := small_consequences H.c3_nonneg H.u1_pos.le H.small
  have hδ1 : δ ≤ 1 := by
    have := (abs_nonneg _).trans (H.F2 u1 le_rfl)
    linarith
  obtain ⟨hc0, hcδ, hcu⟩ := profcHS_facts H.u1_pos H.δ_pos
  have hc1 : profcHS u1 δ ≤ 1 := by linarith
  have hE4 := Real.exp_pos (-(x / 4))
  have hEc := Real.exp_pos (-(profcHS u1 δ * τ))
  have hx0 : 0 ≤ x := by rw [← hx]; exact mul_nonneg hτ0 hu
  have hP : 0 ≤ (profB β c3 ^ 2 * (x * u) ^ 2 / 2 + c3 * (x * u * u)) * Real.exp (-(x / 2)) :=
    mul_nonneg (add_nonneg (by positivity)
      (mul_nonneg H.c3_nonneg (mul_nonneg (mul_nonneg hx0 hu) hu))) (Real.exp_pos _).le
  have hs2 : 0 ≤ F u ^ 2 := pow_two_nonneg _
  have hA0 : 0 ≤ (1 + τ) * Real.exp (-(profcHS u1 δ * τ)) := mul_nonneg (by linarith) hEc.le
  have hβ5 : (0 : ℝ) ≤ 5 * (1 + |β|) := by positivity
  have hinv : 0 ≤ 1 / δ := by have := H.δ_pos; positivity
  have hKsplit : profKHS β δ * (1 + τ) * Real.exp (-(profcHS u1 δ * τ))
        * (F u ^ 2 + Real.exp (-(x / 4)))
      = 4 * ((1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * F u ^ 2)
        + 1 / δ * ((1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * F u ^ 2)
        + 5 * (1 + |β|) * ((1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * Real.exp (-(x / 4)))
        + (5 * (1 + |β|) * ((1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * F u ^ 2)
          + (4 + 1 / δ) * ((1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * Real.exp (-(x / 4)))) := by
    unfold profKHS
    ring
  have n1 : 0 ≤ (1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * F u ^ 2 := mul_nonneg hA0 hs2
  have n2 : 0 ≤ (1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * Real.exp (-(x / 4)) :=
    mul_nonneg hA0 hE4.le
  have hrest : 0 ≤ 5 * (1 + |β|) * ((1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * F u ^ 2)
      + (4 + 1 / δ) * ((1 + τ) * Real.exp (-(profcHS u1 δ * τ)) * Real.exp (-(x / 4))) :=
    add_nonneg (mul_nonneg hβ5 n1) (mul_nonneg (by linarith) n2)
  have m1 := mul_nonneg hinv n1
  have m2 := mul_nonneg hβ5 n2
  rw [hKsplit]
  rcases le_total u u1 with h | h
  · -- low mode
    have key := prof_low hx hτ0 hu h (by linarith) H.c3_nonneg s2 (H.F1 u hu h)
    obtain ⟨k1, k2⟩ := abs_le.1 key
    obtain ⟨v1, v2⟩ := hs_low_value H hu h
    obtain ⟨t0, t1⟩ := hs_low_extra hτ0 hc1 v1 v2
    have he : Real.exp (-τ) * Real.exp (τ * F u) = Real.exp (-(τ * (1 - F u))) := by
      rw [← Real.exp_add]; congr 1; ring
    have e0 : Real.exp (-τ) * (Real.exp (τ * F u) - 1 - τ * F u)
        = Real.exp (-(τ * (1 - F u))) - Real.exp (-τ) * (1 + τ * F u) := by
      rw [← he]; ring
    rw [e0, abs_le]
    constructor <;> linarith
  · -- high mode
    obtain ⟨q0, q5⟩ := hs_high_phi hτ0 H.δ_pos (H.F2 u h) hcδ
    have hb := abs_le.1 (hs_high_cont (γ := β) hx hτ H.u1_pos.le h hcu)
    obtain ⟨b1, b2⟩ := hb
    rw [abs_le]
    constructor <;> linarith

/-- **`thm:profileHS`(ii) for one mode**, low or high (`u = σλ`, `n ≥ 2` steps, `x = nu = tλ`). -/
theorem profHS_mode_disc {F : ℝ → ℝ} {β c3 u1 δ : ℝ} (H : ProfileHypHS F β c3 u1 δ)
    (n : ℕ) (hn2 : 2 ≤ n) {τ u x : ℝ} (hn : (n : ℝ) = τ) (hx : τ * u = x) (hu : 0 ≤ u) :
    |F u ^ n - Real.exp (-x) - (β - 1) * (x * u / 2) * Real.exp (-x)|
      ≤ (profB2 β c3 ^ 2 * (x * u) ^ 2 / 2 + profCt β c3 * (x * u * u)) * Real.exp (-(x / 2))
        + profKHS2 β * (1 + τ) * Real.exp (-(profcHS u1 δ * τ))
            * (F u ^ 2 + Real.exp (-(x / 4))) := by
  have hτ : 2 ≤ τ := by rw [← hn]; exact_mod_cast hn2
  have hτ0 : 0 ≤ τ := by linarith
  have hδ1 : δ ≤ 1 := by
    have := (abs_nonneg _).trans (H.F2 u1 le_rfl)
    linarith
  have hδ := H.δ_pos
  obtain ⟨hc0, hcδ, hcu⟩ := profcHS_facts H.u1_pos H.δ_pos
  have hE4 := Real.exp_pos (-(x / 4))
  have hEc := Real.exp_pos (-(profcHS u1 δ * τ))
  have hx0 : 0 ≤ x := by rw [← hx]; exact mul_nonneg hτ0 hu
  have hCt0 := profCt_nonneg (β := β) H.c3_nonneg
  have hs2 : 0 ≤ F u ^ 2 := pow_two_nonneg _
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 + τ) * Real.exp (-(profcHS u1 δ * τ)) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg (by linarith) hEc.le
  have hβ5 : (0 : ℝ) ≤ 5 * (1 + |β - 1|) := by positivity
  have hKsplit : profKHS2 β * (1 + τ) * Real.exp (-(profcHS u1 δ * τ))
        * (F u ^ 2 + Real.exp (-(x / 4)))
      = 16 * (A * F u ^ 2) + 5 * (1 + |β - 1|) * (A * Real.exp (-(x / 4)))
        + (5 * (1 + |β - 1|) * (A * F u ^ 2) + 16 * (A * Real.exp (-(x / 4)))) := by
    rw [hA]
    unfold profKHS2
    ring
  have n1 : 0 ≤ A * F u ^ 2 := mul_nonneg hA0 hs2
  have n2 : 0 ≤ A * Real.exp (-(x / 4)) := mul_nonneg hA0 hE4.le
  have hrest : 0 ≤ 5 * (1 + |β - 1|) * (A * F u ^ 2) + 16 * (A * Real.exp (-(x / 4))) :=
    add_nonneg (mul_nonneg hβ5 n1) (mul_nonneg (by norm_num) n2)
  have m2 := mul_nonneg hβ5 n2
  have hP : 0 ≤ (profB2 β c3 ^ 2 * (x * u) ^ 2 / 2 + profCt β c3 * (x * u * u))
      * Real.exp (-(x / 2)) :=
    mul_nonneg (add_nonneg (by positivity)
      (mul_nonneg hCt0 (mul_nonneg (mul_nonneg hx0 hu) hu))) (Real.exp_pos _).le
  rw [hKsplit]
  rcases le_total u u1 with h | h
  · have key := prof_low_disc n hn hx hu h H.c3_nonneg H.small (H.F1 u hu h)
    exact key.trans (by linarith)
  · have hs := H.F2 u h
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    have hEd := Real.exp_pos (-(δ * τ))
    have q1 : (1 - δ) ^ j ≤ Real.exp (-δ) ^ j :=
      pow_le_pow_left₀ (by linarith) (by have := Real.add_one_le_exp (-δ); linarith) j
    have q2 : Real.exp (-δ) ^ j = Real.exp (2 * δ) * Real.exp (-(δ * τ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← hn]
      congr 1
      push_cast
      ring
    have q3 : Real.exp (2 * δ) ≤ 16 := by
      have h1 : Real.exp (2 * δ) ≤ Real.exp (1 + 1) := Real.exp_le_exp.2 (by linarith)
      rw [Real.exp_add] at h1
      have h4 := exp_one_le_four
      have hp := Real.exp_pos 1
      nlinarith
    have q4 : (1 - δ) ^ j ≤ 16 * Real.exp (-(δ * τ)) := by
      rw [q2] at q1
      exact q1.trans (mul_le_mul_of_nonneg_right q3 hEd.le)
    have q5 : |F u| ^ j ≤ (1 - δ) ^ j := pow_le_pow_left₀ (abs_nonneg _) hs j
    have d1 : Real.exp (-(δ * τ)) ≤ A := by
      rw [hA]
      have e : Real.exp (-(δ * τ)) ≤ Real.exp (-(profcHS u1 δ * τ)) :=
        Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hcδ hτ0; nlinarith)
      have := mul_nonneg hτ0 hEc.le
      linarith
    have habs : |F u ^ (j + 2)| ≤ 16 * (A * F u ^ 2) := by
      rw [abs_pow, pow_add, sq_abs]
      calc |F u| ^ j * F u ^ 2 ≤ 16 * Real.exp (-(δ * τ)) * F u ^ 2 :=
            mul_le_mul_of_nonneg_right (q5.trans q4) hs2
        _ ≤ 16 * A * F u ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left d1 (by norm_num)) hs2
        _ = 16 * (A * F u ^ 2) := by ring
    obtain ⟨l1, l2⟩ := abs_le.1 habs
    have hb := high_b (γ := β - 1) hx (by linarith) H.u1_pos.le h
    have d2 : Real.exp (-(u1 * τ / 4)) ≤ Real.exp (-(profcHS u1 δ * τ)) :=
      Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hcu hτ0; linarith)
    have d3 : Real.exp (-(u1 * τ / 4)) * Real.exp (-(x / 4)) ≤ A * Real.exp (-(x / 4)) := by
      refine mul_le_mul_of_nonneg_right ?_ hE4.le
      rw [hA]
      have := mul_nonneg hτ0 hEc.le
      linarith
    have d4 := mul_le_mul_of_nonneg_left d3 hβ5
    have hEx := Real.exp_pos (-x)
    have hqq : 0 ≤ (x * u / 2) * Real.exp (-x) :=
      mul_nonneg (by have := mul_nonneg hx0 (H.u1_pos.le.trans h); linarith) hEx.le
    have h4 : (β - 1) * ((x * u / 2) * Real.exp (-x))
        ≤ |β - 1| * ((x * u / 2) * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hqq
    have h5 : -(|β - 1| * ((x * u / 2) * Real.exp (-x)))
        ≤ (β - 1) * ((x * u / 2) * Real.exp (-x)) := by
      have := mul_le_mul_of_nonneg_right (neg_abs_le (β - 1)) hqq
      linarith
    rw [abs_le]
    constructor <;> linarith

/-! #### Summation over a spectrum -/

section SumsHS

variable {ι : Type*} (lam : ι → ℝ)

/-- `T^F_σ(t) = e^{-τ}[τ m₁ + ∑_k φ(τ F(σλ_k))]` of `thm:profileHS`, `τ = t/σ`,
    `φ(x) = e^x - 1 - x`; `m₁` is a free number. -/
noncomputable def profTrHS (F : ℝ → ℝ) (σ t m1 : ℝ) : ℝ :=
  Real.exp (-(t / σ)) * (t / σ * m1
    + ∑' k, (Real.exp (t / σ * F (σ * lam k)) - 1 - t / σ * F (σ * lam k)))

/-- `Q(σ) = ∑_k F(σλ_k)²`, the left-hand side of (F3'). -/
noncomputable def sqSum (F : ℝ → ℝ) (σ : ℝ) : ℝ := ∑' k, F (σ * lam k) ^ 2

variable {lam}

/-- Summation of mode-wise bounds with a general summable weight `w` in place of
    `(1 + σλ)^{-p}` (cf. `OlderParts.sum_modeR`). -/
theorem sum_modeHS (h : IsSpectrum lam) {a1 a2 K c σ t : ℝ} (ht : 0 < t) {w : ι → ℝ}
    (hw : Summable w) {d : ι → ℝ}
    (hd : ∀ k, |d k| ≤ (σ / t) ^ 2 * (a1 * t ^ 4 * (lam k ^ 4 * Real.exp (-(t / 2 * lam k)))
          + a2 * t ^ 3 * (lam k ^ 3 * Real.exp (-(t / 2 * lam k))))
        + K * (1 + t / σ) * Real.exp (-(c * (t / σ)))
            * (w k + Real.exp (-(t / 4 * lam k)))) :
    Summable d ∧
    |∑' k, d k|
      ≤ (σ / t) ^ 2 * (a1 * t ^ 4 * heatMom lam 4 (t / 2) + a2 * t ^ 3 * heatMom lam 3 (t / 2))
        + K * (1 + t / σ) * Real.exp (-(c * (t / σ)))
            * (∑' k, w k + heatTr lam (t / 4)) := by
  have ht2 : 0 < t / 2 := by linarith
  have ht4 : 0 < t / 4 := by linarith
  have hR := ((((heatMom_hasSum h 4 ht2).mul_left (a1 * t ^ 4)).add
      ((heatMom_hasSum h 3 ht2).mul_left (a2 * t ^ 3))).mul_left ((σ / t) ^ 2)).add
    ((hw.hasSum.add (heatTr_hasSum h ht4)).mul_left
      (K * (1 + t / σ) * Real.exp (-(c * (t / σ)))))
  have hs : Summable d :=
    Summable.of_norm_bounded hR.summable (fun k => by rw [Real.norm_eq_abs]; exact hd k)
  refine ⟨hs, ?_⟩
  rw [abs_le]
  constructor
  · exact hasSum_le (fun k => (abs_le.1 (hd k)).1) hR.neg hs.hasSum
  · exact hasSum_le (fun k => (abs_le.1 (hd k)).2) hs.hasSum hR

/-- Change of variables for one mode (cf. `OlderParts.modeR_eq`). -/
theorem modeHS_eq {A a2 K c σ t l W : ℝ} (ht : 0 < t) :
    (A ^ 2 * (t * l * (σ * l)) ^ 2 / 2 + a2 * (t * l * (σ * l) * (σ * l)))
          * Real.exp (-(t * l / 2))
        + K * (1 + t / σ) * Real.exp (-(c * (t / σ))) * (W + Real.exp (-(t * l / 4)))
      = (σ / t) ^ 2 * (A ^ 2 / 2 * t ^ 4 * (l ^ 4 * Real.exp (-(t / 2 * l)))
          + a2 * t ^ 3 * (l ^ 3 * Real.exp (-(t / 2 * l))))
        + K * (1 + t / σ) * Real.exp (-(c * (t / σ))) * (W + Real.exp (-(t / 4 * l))) := by
  have h : σ / t * t = σ := div_mul_cancel₀ σ ht.ne'
  have e4 : t * l / 2 = t / 2 * l := by ring
  have e5 : t * l / 4 = t / 4 * l := by ring
  have e1 : (σ / t) ^ 2 * (A ^ 2 / 2 * t ^ 4 * l ^ 4) = A ^ 2 * (t * l * (σ * l)) ^ 2 / 2 :=
    calc (σ / t) ^ 2 * (A ^ 2 / 2 * t ^ 4 * l ^ 4)
        = A ^ 2 / 2 * (σ / t * t) ^ 2 * t ^ 2 * l ^ 4 := by ring
      _ = A ^ 2 / 2 * σ ^ 2 * t ^ 2 * l ^ 4 := by rw [h]
      _ = A ^ 2 * (t * l * (σ * l)) ^ 2 / 2 := by ring
  have e2 : (σ / t) ^ 2 * (a2 * t ^ 3 * l ^ 3) = a2 * (t * l * (σ * l) * (σ * l)) :=
    calc (σ / t) ^ 2 * (a2 * t ^ 3 * l ^ 3) = a2 * (σ / t * t) ^ 2 * t * l ^ 3 := by ring
      _ = a2 * σ ^ 2 * t * l ^ 3 := by rw [h]
      _ = a2 * (t * l * (σ * l) * (σ * l)) := by ring
  rw [← e1, ← e2, e4, e5]
  ring

/-- **`thm:profileHS`, statement (i), as a statement about a list of eigenvalues, with explicit
    constants.** For `t ≥ σ > 0`, `τ = t/σ`, under `ProfileHypHS` and the convergence of
    `Q(σ) = ∑_k F(σλ_k)²`, for every real `m₁`:
    `|T^F_σ(t) - Θ(t) - β (σt/2) Θ''(t)| ≤ (σ/t)² [(B²/2) t⁴ Θ''''(t/2) + c₃ t³ |Θ'''(t/2)|]
        + K (1+τ) e^{-cτ} [Q(σ) + Θ(t/4)] + τ e^{-τ} |m₁|`.
    The series `∑_k φ(τ F(σλ_k))` converges. -/
theorem profileHS_i (h : IsSpectrum lam) {F : ℝ → ℝ} {β c3 u1 δ : ℝ}
    (H : ProfileHypHS F β c3 u1 δ) {σ t : ℝ} (hσ : 0 < σ) (hts : σ ≤ t) (m1 : ℝ)
    (hQ : Summable fun k => F (σ * lam k) ^ 2) :
    Summable (fun k => Real.exp (t / σ * F (σ * lam k)) - 1 - t / σ * F (σ * lam k)) ∧
    |profTrHS lam F σ t m1 - heatTr lam t - β * (σ * t / 2) * heatMom lam 2 t|
      ≤ (σ / t) ^ 2 * (profB β c3 ^ 2 / 2 * t ^ 4 * heatMom lam 4 (t / 2)
            + c3 * t ^ 3 * heatMom lam 3 (t / 2))
        + profKHS β δ * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
            * (sqSum lam F σ + heatTr lam (t / 4))
        + t / σ * Real.exp (-(t / σ)) * |m1| := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hτ : 1 ≤ t / σ := by rw [le_div_iff₀ hσ]; linarith
  have hEt := Real.exp_pos (-(t / σ))
  obtain ⟨d, hd_def⟩ : ∃ d : ι → ℝ, d = fun k =>
      Real.exp (-(t / σ)) * (Real.exp (t / σ * F (σ * lam k)) - 1 - t / σ * F (σ * lam k))
        - Real.exp (-(t * lam k)) - β * (σ * t / 2) * (lam k ^ 2 * Real.exp (-(t * lam k))) :=
    ⟨_, rfl⟩
  have hd : ∀ k, |d k|
      ≤ (σ / t) ^ 2 * (profB β c3 ^ 2 / 2 * t ^ 4 * (lam k ^ 4 * Real.exp (-(t / 2 * lam k)))
          + c3 * t ^ 3 * (lam k ^ 3 * Real.exp (-(t / 2 * lam k))))
        + profKHS β δ * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
            * (F (σ * lam k) ^ 2 + Real.exp (-(t / 4 * lam k))) := by
    intro k
    have hx : t / σ * (σ * lam k) = t * lam k := by field_simp
    have key := profHS_mode H hx hτ (mul_nonneg hσ.le (h.nonneg k))
    rw [modeHS_eq ht] at key
    have e : d k = Real.exp (-(t / σ))
          * (Real.exp (t / σ * F (σ * lam k)) - 1 - t / σ * F (σ * lam k))
        - Real.exp (-(t * lam k))
        - β * (t * lam k * (σ * lam k) / 2) * Real.exp (-(t * lam k)) := by
      rw [hd_def]
      ring
    rw [e]
    exact key
  obtain ⟨hs, hb⟩ := sum_modeHS h ht hQ hd
  have hΘ := heatTr_hasSum h ht
  have hM := (heatMom_hasSum h 2 ht).mul_left (β * (σ * t / 2))
  have hA : HasSum (fun k => Real.exp (-(t / σ))
        * (Real.exp (t / σ * F (σ * lam k)) - 1 - t / σ * F (σ * lam k)))
      (∑' k, d k + heatTr lam t + β * (σ * t / 2) * heatMom lam 2 t) := by
    convert (hs.hasSum.add hΘ).add hM using 1
    funext k
    rw [hd_def]
    ring
  have hφ : Summable (fun k => Real.exp (t / σ * F (σ * lam k)) - 1 - t / σ * F (σ * lam k)) := by
    have := hA.summable.mul_left (Real.exp (t / σ))
    refine this.congr fun k => ?_
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have e2 : profTrHS lam F σ t m1 - heatTr lam t - β * (σ * t / 2) * heatMom lam 2 t
      = ∑' k, d k + Real.exp (-(t / σ)) * (t / σ * m1) := by
    unfold profTrHS
    rw [mul_add, ← tsum_mul_left, hA.tsum_eq]
    ring
  refine ⟨hφ, ?_⟩
  rw [e2]
  have e3 : |Real.exp (-(t / σ)) * (t / σ * m1)| = t / σ * Real.exp (-(t / σ)) * |m1| := by
    rw [abs_mul, abs_mul, abs_of_pos hEt, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t / σ)]
    ring
  have := abs_add_le (∑' k, d k) (Real.exp (-(t / σ)) * (t / σ * m1))
  rw [e3] at this
  unfold sqSum
  linarith

/-- **`thm:profileHS`, statement (ii), as a statement about a list of eigenvalues, with explicit
    constants.** For `σ > 0`, an integer `n ≥ 2` and `t = nσ`, under `ProfileHypHS` and the
    convergence of `Q(σ)`:
    `|∑_k F(σλ_k)^n - Θ(t) - (β-1)(σt/2) Θ''(t)|
        ≤ (σ/t)² [(B₂²/2) t⁴ Θ''''(t/2) + c̃ t³ |Θ'''(t/2)|] + K₂ (1+n) e^{-cn} [Q(σ) + Θ(t/4)]`. -/
theorem profileHS_ii (h : IsSpectrum lam) {F : ℝ → ℝ} {β c3 u1 δ : ℝ}
    (H : ProfileHypHS F β c3 u1 δ) {σ t : ℝ} (hσ : 0 < σ) (n : ℕ) (hn2 : 2 ≤ n)
    (hnt : (n : ℝ) * σ = t) (hQ : Summable fun k => F (σ * lam k) ^ 2) :
    Summable (fun k => F (σ * lam k) ^ n) ∧
    |discTr lam F σ n - heatTr lam t - (β - 1) * (σ * t / 2) * heatMom lam 2 t|
      ≤ (σ / t) ^ 2 * (profB2 β c3 ^ 2 / 2 * t ^ 4 * heatMom lam 4 (t / 2)
            + profCt β c3 * t ^ 3 * heatMom lam 3 (t / 2))
        + profKHS2 β * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
            * (sqSum lam F σ + heatTr lam (t / 4)) := by
  have hn0 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have ht : 0 < t := by rw [← hnt]; exact mul_pos (by linarith) hσ
  have hn : (n : ℝ) = t / σ := eq_div_of_mul_eq hσ.ne' hnt
  obtain ⟨d, hd_def⟩ : ∃ d : ι → ℝ, d = fun k =>
      F (σ * lam k) ^ n - Real.exp (-(t * lam k))
        - (β - 1) * (σ * t / 2) * (lam k ^ 2 * Real.exp (-(t * lam k))) :=
    ⟨_, rfl⟩
  have hd : ∀ k, |d k|
      ≤ (σ / t) ^ 2 * (profB2 β c3 ^ 2 / 2 * t ^ 4 * (lam k ^ 4 * Real.exp (-(t / 2 * lam k)))
          + profCt β c3 * t ^ 3 * (lam k ^ 3 * Real.exp (-(t / 2 * lam k))))
        + profKHS2 β * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
            * (F (σ * lam k) ^ 2 + Real.exp (-(t / 4 * lam k))) := by
    intro k
    have hx : t / σ * (σ * lam k) = t * lam k := by field_simp
    have key := profHS_mode_disc H n hn2 hn hx (mul_nonneg hσ.le (h.nonneg k))
    rw [modeHS_eq ht] at key
    have e : d k = F (σ * lam k) ^ n - Real.exp (-(t * lam k))
        - (β - 1) * (t * lam k * (σ * lam k) / 2) * Real.exp (-(t * lam k)) := by
      rw [hd_def]
      ring
    rw [e]
    exact key
  obtain ⟨hs, hb⟩ := sum_modeHS h ht hQ hd
  have hΘ := heatTr_hasSum h ht
  have hM := (heatMom_hasSum h 2 ht).mul_left ((β - 1) * (σ * t / 2))
  have hA : HasSum (fun k => F (σ * lam k) ^ n)
      (∑' k, d k + heatTr lam t + (β - 1) * (σ * t / 2) * heatMom lam 2 t) := by
    convert (hs.hasSum.add hΘ).add hM using 1
    funext k
    rw [hd_def]
    ring
  have e2 : discTr lam F σ n - heatTr lam t - (β - 1) * (σ * t / 2) * heatMom lam 2 t
      = ∑' k, d k := by
    unfold discTr
    rw [hA.tsum_eq]
    ring
  rw [e2]
  exact ⟨hA.summable, hb⟩

/-- **`thm:profileHS` in the form of the paper, with (F3') as the bounds `Q(σ) ≤ B`, `|m₁| ≤ B`**
    (the paper: `B = C_F σ^{-d/2}`): both remainders are at most
    `(σ/t)²[...] + K (1+τ) e^{-cτ} [B + Θ(t/4)]`; (i) for `t ≥ σ`, (ii) for `t = nσ`, `n ≥ 2`. -/
theorem profileHS_paper (h : IsSpectrum lam) {F : ℝ → ℝ} {β c3 u1 δ : ℝ}
    (H : ProfileHypHS F β c3 u1 δ) {σ t B m1 : ℝ} (hσ : 0 < σ) (hts : σ ≤ t)
    (hQ : Summable fun k => F (σ * lam k) ^ 2) (hQB : sqSum lam F σ ≤ B) (hm : |m1| ≤ B) :
    |profTrHS lam F σ t m1 - heatTr lam t - β * (σ * t / 2) * heatMom lam 2 t|
      ≤ (σ / t) ^ 2 * (profB β c3 ^ 2 / 2 * t ^ 4 * heatMom lam 4 (t / 2)
            + c3 * t ^ 3 * heatMom lam 3 (t / 2))
        + (profKHS β δ + 1) * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
            * (B + heatTr lam (t / 4))
    ∧ ∀ n : ℕ, 2 ≤ n → (n : ℝ) * σ = t →
      |discTr lam F σ n - heatTr lam t - (β - 1) * (σ * t / 2) * heatMom lam 2 t|
        ≤ (σ / t) ^ 2 * (profB2 β c3 ^ 2 / 2 * t ^ 4 * heatMom lam 4 (t / 2)
              + profCt β c3 * t ^ 3 * heatMom lam 3 (t / 2))
          + profKHS2 β * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
              * (B + heatTr lam (t / 4)) := by
  have ht : 0 < t := lt_of_lt_of_le hσ hts
  have hτ : 1 ≤ t / σ := by rw [le_div_iff₀ hσ]; linarith
  have hτ0 : 0 ≤ t / σ := by linarith
  obtain ⟨hc0, hcδ, hcu⟩ := profcHS_facts H.u1_pos H.δ_pos
  have hδ1 : δ ≤ 1 := by
    have := (abs_nonneg _).trans (H.F2 u1 le_rfl)
    linarith
  have hEc := Real.exp_pos (-(profcHS u1 δ * (t / σ)))
  have hΘ := heatTr_nonneg (lam := lam) (t / 4)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hm
  have hA0 : 0 ≤ (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ))) :=
    mul_nonneg (by linarith) hEc.le
  have hK0 : 0 ≤ profKHS β δ := by
    unfold profKHS
    have := abs_nonneg β
    have : 0 ≤ 1 / δ := by have := H.δ_pos; positivity
    linarith
  have hK20 : 0 ≤ profKHS2 β := by
    unfold profKHS2
    have := abs_nonneg (β - 1)
    linarith
  have mono : sqSum lam F σ + heatTr lam (t / 4) ≤ B + heatTr lam (t / 4) := by linarith
  constructor
  · refine (profileHS_i h H hσ hts m1 hQ).2.trans ?_
    have e1 : Real.exp (-(t / σ)) ≤ Real.exp (-(profcHS u1 δ * (t / σ))) :=
      Real.exp_le_exp.2 (by nlinarith)
    have a1 : t / σ * Real.exp (-(t / σ)) * |m1|
        ≤ (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ))) * (B + heatTr lam (t / 4)) := by
      refine mul_le_mul (mul_le_mul (by linarith) e1 (Real.exp_pos _).le (by linarith))
        (by linarith) (abs_nonneg _) hA0
    have a2 : profKHS β δ * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
          * (sqSum lam F σ + heatTr lam (t / 4))
        ≤ profKHS β δ * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
          * (B + heatTr lam (t / 4)) :=
      mul_le_mul_of_nonneg_left mono (by
        rw [mul_assoc]; exact mul_nonneg hK0 hA0)
    have e : (profKHS β δ + 1) * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
          * (B + heatTr lam (t / 4))
        = profKHS β δ * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
            * (B + heatTr lam (t / 4))
          + (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ))) * (B + heatTr lam (t / 4)) := by
      ring
    rw [e]
    linarith
  · intro n hn2 hnt
    refine (profileHS_ii h H hσ n hn2 hnt hQ).2.trans ?_
    have a2 : profKHS2 β * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
          * (sqSum lam F σ + heatTr lam (t / 4))
        ≤ profKHS2 β * (1 + t / σ) * Real.exp (-(profcHS u1 δ * (t / σ)))
          * (B + heatTr lam (t / 4)) :=
      mul_le_mul_of_nonneg_left mono (by
        rw [mul_assoc]; exact mul_nonneg hK20 hA0)
    linarith

end SumsHS

/-! #### The indicator of an interval: Taylor bounds for the sine -/

/-- A function with nonnegative derivative on `[0, ∞)` and `f 0 = 0` is nonnegative there. -/
theorem nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (h0 : f 0 = 0)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x := by
  have hm : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hf y).continuousAt.continuousWithinAt)
      (fun y _ => (hf y).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    rw [(hf y).deriv]
    exact hpos y (le_of_lt hy)
  have := hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  rwa [h0] at this

/-- `x - x³/6 ≤ sin x` for `x ≥ 0`. -/
theorem sin_lower3 {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ Real.sin x := by
  have hd : ∀ y : ℝ, HasDerivAt (fun x : ℝ => Real.sin x - x + x ^ 3 / 6)
      (Real.cos y - 1 + y ^ 2 / 2) y := by
    intro y
    have h := ((Real.hasDerivAt_sin y).fun_sub (hasDerivAt_id' y)).fun_add
      ((hasDerivAt_pow 3 y).div_const 6)
    convert h using 1
    norm_num
    ring
  have := nonneg_of_deriv_nonneg hd (by simp)
    (fun y _ => by have := Real.one_sub_sq_div_two_le_cos (x := y); linarith) hx
  simp only at this
  linarith

/-- `cos x ≤ 1 - x²/2 + x⁴/24` for `x ≥ 0`. -/
theorem cos_upper4 {x : ℝ} (hx : 0 ≤ x) : Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun x : ℝ => 1 - x ^ 2 / 2 + x ^ 4 / 24 - Real.cos x)
      (-y + y ^ 3 / 6 + Real.sin y) y := by
    intro y
    have h := ((((hasDerivAt_const y (1 : ℝ)).fun_sub ((hasDerivAt_pow 2 y).div_const 2)).fun_add
      ((hasDerivAt_pow 4 y).div_const 24)).fun_sub (Real.hasDerivAt_cos y))
    convert h using 1
    norm_num
    ring
  have := nonneg_of_deriv_nonneg hd (by simp)
    (fun y hy => by have := sin_lower3 hy; linarith) hx
  simp only at this
  linarith

/-- `sin x ≤ x - x³/6 + x⁵/120` for `x ≥ 0`. -/
theorem sin_upper5 {x : ℝ} (hx : 0 ≤ x) : Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun x : ℝ => x - x ^ 3 / 6 + x ^ 5 / 120 - Real.sin x)
      (1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y) y := by
    intro y
    have h := ((((hasDerivAt_id' y).fun_sub ((hasDerivAt_pow 3 y).div_const 6)).fun_add
      ((hasDerivAt_pow 5 y).div_const 120)).fun_sub (Real.hasDerivAt_sin y))
    convert h using 1
    norm_num
    ring
  have := nonneg_of_deriv_nonneg hd (by simp)
    (fun y hy => by have := cos_upper4 hy; linarith) hx
  simp only at this
  linarith

/-- `1 - x²/2 + x⁴/24 - x⁶/720 ≤ cos x` for `x ≥ 0`. -/
theorem cos_lower6 {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ Real.cos x := by
  have hd : ∀ y : ℝ, HasDerivAt
      (fun x : ℝ => Real.cos x - 1 + x ^ 2 / 2 - x ^ 4 / 24 + x ^ 6 / 720)
      (-Real.sin y + y - y ^ 3 / 6 + y ^ 5 / 120) y := by
    intro y
    have h := (((((Real.hasDerivAt_cos y).fun_sub (hasDerivAt_const y (1 : ℝ))).fun_add
      ((hasDerivAt_pow 2 y).div_const 2)).fun_sub ((hasDerivAt_pow 4 y).div_const 24)).fun_add
      ((hasDerivAt_pow 6 y).div_const 720))
    convert h using 1
    norm_num
    ring
  have := nonneg_of_deriv_nonneg hd (by simp)
    (fun y hy => by have := sin_upper5 hy; linarith) hx
  simp only at this
  linarith

/-- **Taylor bounds for the sine with explicit remainder:**
    `x - x³/6 + x⁵/120 - x⁷/5040 ≤ sin x ≤ x - x³/6 + x⁵/120` for `x ≥ 0`. -/
theorem sin_taylor {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x ∧
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  refine ⟨?_, sin_upper5 hx⟩
  have hd : ∀ y : ℝ, HasDerivAt
      (fun x : ℝ => Real.sin x - x + x ^ 3 / 6 - x ^ 5 / 120 + x ^ 7 / 5040)
      (Real.cos y - 1 + y ^ 2 / 2 - y ^ 4 / 24 + y ^ 6 / 720) y := by
    intro y
    have h := (((((Real.hasDerivAt_sin y).fun_sub (hasDerivAt_id' y)).fun_add
      ((hasDerivAt_pow 3 y).div_const 6)).fun_sub ((hasDerivAt_pow 5 y).div_const 120)).fun_add
      ((hasDerivAt_pow 7 y).div_const 5040))
    convert h using 1
    norm_num
    ring
  have := nonneg_of_deriv_nonneg hd (by simp)
    (fun y hy => by have := cos_lower6 hy; linarith) hx
  simp only at this
  linarith

/-- **Taylor bounds for `sinc` with explicit remainder:**
    `1 - x²/6 + x⁴/120 - x⁶/5040 ≤ sinc x ≤ 1 - x²/6 + x⁴/120` for `x ≥ 0`. -/
theorem sinc_taylor {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040 ≤ Real.sinc x ∧
    Real.sinc x ≤ 1 - x ^ 2 / 6 + x ^ 4 / 120 := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.sinc_zero]
    norm_num
  · obtain ⟨l, r⟩ := sin_taylor hx
    rw [Real.sinc_of_ne_zero h.ne', le_div_iff₀ h, div_le_iff₀ h]
    constructor
    · have e : (1 - x ^ 2 / 6 + x ^ 4 / 120 - x ^ 6 / 5040) * x
          = x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 := by ring
      rw [e]; exact l
    · have e : (1 - x ^ 2 / 6 + x ^ 4 / 120) * x = x - x ^ 3 / 6 + x ^ 5 / 120 := by ring
      rw [e]; exact r

/-- `|sinc x| ≤ 1/x` for `x > 0`. -/
theorem abs_sinc_le_inv {x : ℝ} (hx : 0 < x) : |Real.sinc x| ≤ 1 / x := by
  rw [Real.sinc_of_ne_zero hx.ne', abs_div, abs_of_pos hx]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one x) hx.le

/-- `|sinc x| ≤ 1 - 2x²/15` for `0 ≤ x ≤ 2`. -/
theorem abs_sinc_le_small {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    |Real.sinc x| ≤ 1 - 2 * x ^ 2 / 15 := by
  obtain ⟨l, r⟩ := sinc_taylor hx
  have h2 : x ^ 2 ≤ 4 := by nlinarith
  have h20 : 0 ≤ x ^ 2 := pow_two_nonneg x
  have h4 : x ^ 4 ≤ 4 * x ^ 2 := by nlinarith
  have h40 : 0 ≤ x ^ 4 := by positivity
  have h6 : x ^ 6 ≤ 4 * x ^ 4 := by nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- **`sup_{x ≥ x₁} |sinc x| < 1`, quantitatively:** `|sinc x| ≤ 1 - min(1/2, 2x₁²/15)` for
    `x ≥ x₁ ≥ 0`. -/
theorem abs_sinc_gap {x x1 : ℝ} (hx1 : 0 ≤ x1) (hx : x1 ≤ x) :
    |Real.sinc x| ≤ 1 - min (1 / 2) (2 * x1 ^ 2 / 15) := by
  rcases le_total x 2 with h | h
  · have := abs_sinc_le_small (hx1.trans hx) h
    have h1 : x1 ^ 2 ≤ x ^ 2 := by nlinarith
    have := min_le_right (1 / 2 : ℝ) (2 * x1 ^ 2 / 15)
    linarith
  · have h0 : (0 : ℝ) < x := by linarith
    have := abs_sinc_le_inv h0
    have h1 : 1 / x ≤ 1 / 2 := by
      rw [div_le_div_iff₀ h0 (by norm_num)]; linarith
    have := min_le_left (1 / 2 : ℝ) (2 * x1 ^ 2 / 15)
    linarith

/-! #### The indicator of an interval: the profile function -/

/-- The Fourier transform of `κ = ½·1_{[-1,1]}`: `∫_{-1}^{1} ½ cos(ζx) dx = sinc ζ`. -/
theorem interval_fourier (ζ : ℝ) :
    ∫ x in (-1 : ℝ)..1, 1 / 2 * Real.cos (ζ * x) = Real.sinc ζ := by
  rcases eq_or_ne ζ 0 with h | h
  · subst h
    simp
    norm_num
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ h,
      integral_cos, Real.sinc_of_ne_zero h]
    simp only [mul_one, mul_neg, Real.sin_neg, smul_eq_mul]
    field_simp
    ring

/-- The moments of `κ = ½·1_{[-1,1]}`: `E X² = 1/3`, `E X⁴ = 1/5`; hence, by `eq:beta` of the paper
    (not formalised), `σ = ξ²/6` and `β = (1/5)/(3·(1/3)²) = 3/5`. -/
theorem interval_moments :
    (∫ x in (-1 : ℝ)..1, 1 / 2 * x ^ 2) = 1 / 3 ∧ (∫ x in (-1 : ℝ)..1, 1 / 2 * x ^ 4) = 1 / 5 ∧
    (1 / 5 : ℝ) / (3 * (1 / 3) ^ 2) = 3 / 5 := by
  refine ⟨?_, ?_, by norm_num⟩
  · rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num
  · rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num

/-- The profile function of the interval indicator in the variable `u = σλ`:
    `F(u) = sinc √(6u)`. -/
noncomputable def ballF (u : ℝ) : ℝ := Real.sinc (Real.sqrt (6 * u))

/-- The eigenvalues of `-d²/dx²` on the circle `ℝ/ℤ` as a list over `ℤ`: `λ_n = 4π² n²`. -/
noncomputable def lam1 (n : ℤ) : ℝ := 4 * Real.pi ^ 2 * (n : ℝ) ^ 2

theorem lam1_isSpectrum : IsSpectrum lam1 where
  nonneg := fun n => by unfold lam1; positivity
  summable := fun s hs => by
    have h := (torus_isSpectrum 1).summable s hs
    have h2 := ((Equiv.funUnique (Fin 1) ℤ).symm.summable_iff).2 h
    refine h2.congr fun n => ?_
    simp [torusLam, lam1]

/-- `F(σ λ_n) = sinc(2πξ n)` for `σ = ξ²/6`: the values of the Fourier transform of the kernel
    `ξ^{-1} κ(·/ξ)` at the frequencies `2πn`. -/
theorem ballF_eigen (ξ : ℝ) (n : ℤ) :
    ballF (ξ ^ 2 / 6 * lam1 n) = Real.sinc (2 * Real.pi * ξ * n) := by
  unfold ballF lam1
  have e : 6 * (ξ ^ 2 / 6 * (4 * Real.pi ^ 2 * (n : ℝ) ^ 2)) = (2 * Real.pi * ξ * n) ^ 2 := by
    ring
  rw [e, Real.sqrt_sq_eq_abs]
  rcases abs_choice (2 * Real.pi * ξ * n) with h | h
  · rw [h]
  · rw [h, Real.sinc_neg]

/-- **(F1) for the interval indicator, for all `u ≥ 0`:** `β = 3/5`, `c₃ = 3/70`. -/
theorem ballF_F1 {u : ℝ} (hu : 0 ≤ u) :
    |ballF u - (1 - u + 3 / 5 * u ^ 2 / 2)| ≤ 3 / 70 * u ^ 3 := by
  unfold ballF
  have h6 : 0 ≤ 6 * u := by linarith
  have hx := Real.sqrt_nonneg (6 * u)
  have h2 : Real.sqrt (6 * u) ^ 2 = 6 * u := Real.sq_sqrt h6
  have h4 : Real.sqrt (6 * u) ^ 4 = 36 * u ^ 2 := by
    calc Real.sqrt (6 * u) ^ 4 = (Real.sqrt (6 * u) ^ 2) ^ 2 := by ring
      _ = 36 * u ^ 2 := by rw [h2]; ring
  have h6' : Real.sqrt (6 * u) ^ 6 = 216 * u ^ 3 := by
    calc Real.sqrt (6 * u) ^ 6 = (Real.sqrt (6 * u) ^ 2) ^ 3 := by ring
      _ = 216 * u ^ 3 := by rw [h2]; ring
  obtain ⟨l, r⟩ := sinc_taylor hx
  rw [h2, h4, h6'] at l
  rw [h2, h4] at r
  rw [abs_le]
  constructor <;> linarith

/-- **The second part of (F2) for the interval indicator:** for `u ≥ u₁ > 0`,
    `|F(u)| ≤ 1 - min(1/2, 4u₁/5)`. -/
theorem ballF_F2 {u u1 : ℝ} (hu1 : 0 ≤ u1) (hu : u1 ≤ u) :
    |ballF u| ≤ 1 - min (1 / 2) (4 * u1 / 5) := by
  unfold ballF
  have h := abs_sinc_gap (x1 := Real.sqrt (6 * u1)) (x := Real.sqrt (6 * u)) (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (by linarith))
  rw [Real.sq_sqrt (by linarith)] at h
  have e : 2 * (6 * u1) / 15 = 4 * u1 / 5 := by ring
  rw [e] at h
  exact h

/-- The interval indicator satisfies the hypotheses of `thm:profileHS` on the profile function:
    `β = 3/5`, `c₃ = 3/70`, threshold `u₁ = 1/24`, `δ = 1/30`. -/
theorem ballF_hyp : ProfileHypHS ballF (3 / 5) (3 / 70) (1 / 24) (1 / 30) where
  c3_nonneg := by norm_num
  u1_pos := by norm_num
  small := by rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5)]; norm_num
  δ_pos := by norm_num
  F1 := fun u hu _ => ballF_F1 hu
  F2 := fun u hu => by
    have h := ballF_F2 (u1 := 1 / 24) (by norm_num) hu
    have e : min (1 / 2 : ℝ) (4 * (1 / 24) / 5) = 1 / 30 := by
      rw [min_eq_right (by norm_num)]; norm_num
    rw [e] at h
    exact h

/-- The hypotheses of the paper on `F` for the interval indicator: (F1) on `[0, ∞)` and the second
    part of (F2) in the form `∀ u₁ > 0, ∃ δ > 0, ∀ u ≥ u₁, |F u| ≤ 1 - δ`. -/
theorem ballF_F2_paper : ∀ u1 : ℝ, 0 < u1 → ∃ δ : ℝ, 0 < δ ∧ ∀ u, u1 ≤ u → |ballF u| ≤ 1 - δ :=
  fun u1 hu1 => ⟨min (1 / 2) (4 * u1 / 5), lt_min (by norm_num) (by positivity),
    fun _ hu => ballF_F2 hu1.le hu⟩

/-! #### The indicator of an interval: (F3') -/

/-- `sinc(y)² ≤ 4/(1+y)²` for `y ≥ 0`. -/
theorem sinc_sq_le {y : ℝ} (hy : 0 ≤ y) : Real.sinc y ^ 2 ≤ 4 / (1 + y) ^ 2 := by
  have h1 : (0 : ℝ) < 1 + y := by linarith
  have key : |Real.sinc y| ≤ 2 / (1 + y) := by
    rcases le_total y 1 with h | h
    · refine (Real.abs_sinc_le_one y).trans ?_
      rw [le_div_iff₀ h1]; linarith
    · have h0 : 0 < y := by linarith
      refine (abs_sinc_le_inv h0).trans ?_
      rw [div_le_div_iff₀ h0 h1]; linarith
  have := mul_self_le_mul_self (abs_nonneg _) key
  rw [abs_mul_abs_self] at this
  calc Real.sinc y ^ 2 = Real.sinc y * Real.sinc y := by ring
    _ ≤ 2 / (1 + y) * (2 / (1 + y)) := this
    _ = 4 / (1 + y) ^ 2 := by field_simp; ring

/-- One term of the telescoping bound. -/
theorem sinc_sq_step {a : ℝ} (ha : 0 < a) (m : ℕ) :
    Real.sinc (a * ((m : ℝ) + 1)) ^ 2
      ≤ 4 / a / (1 + a * m) - 4 / a / (1 + a * ((m : ℝ) + 1)) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hP : 0 < 1 + a * m := by have := mul_nonneg ha.le hm; linarith
  have hQ : 0 < 1 + a * ((m : ℝ) + 1) := by nlinarith
  have e : 4 / a / (1 + a * m) - 4 / a / (1 + a * ((m : ℝ) + 1))
      = 4 / ((1 + a * m) * (1 + a * ((m : ℝ) + 1))) := by
    field_simp
    ring
  rw [e]
  refine (sinc_sq_le (by nlinarith)).trans ?_
  refine div_le_div_of_nonneg_left (by norm_num) (mul_pos hP hQ) ?_
  nlinarith

/-- Partial sums: `∑_{m<M} sinc(a(m+1))² ≤ 4/a`. -/
theorem sinc_sq_partial {a : ℝ} (ha : 0 < a) (M : ℕ) :
    ∑ m ∈ Finset.range M, Real.sinc (a * ((m : ℝ) + 1)) ^ 2 ≤ 4 / a := by
  have key : ∀ M : ℕ, ∑ m ∈ Finset.range M, Real.sinc (a * ((m : ℝ) + 1)) ^ 2
      ≤ 4 / a - 4 / a / (1 + a * M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ]
      have := sinc_sq_step ha M
      push_cast
      linarith
  have hp : 0 ≤ 4 / a / (1 + a * M) := by
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have := mul_nonneg ha.le this
    positivity
  linarith [key M]

/-- **(F3') for the interval indicator, elementary form:** `∑_{n ∈ ℤ} sinc(a n)² ≤ 1 + 8/a` for
    `a > 0`, and the series converges. (Parseval's identity gives the value `π/a` for `a ≤ π`;
    that is not proved here.) -/
theorem sinc_sq_sum {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℤ => Real.sinc (a * n) ^ 2) ∧
    ∑' n : ℤ, Real.sinc (a * n) ^ 2 ≤ 1 + 8 / a := by
  have hg0 : ∀ m : ℕ, 0 ≤ Real.sinc (a * ((m : ℝ) + 1)) ^ 2 := fun m => pow_two_nonneg _
  have hgs : Summable (fun m : ℕ => Real.sinc (a * ((m : ℝ) + 1)) ^ 2) :=
    summable_of_sum_range_le hg0 (sinc_sq_partial ha)
  have hgt : ∑' m : ℕ, Real.sinc (a * ((m : ℝ) + 1)) ^ 2 ≤ 4 / a :=
    Real.tsum_le_of_sum_range_le hg0 (sinc_sq_partial ha)
  have hcast1 : ∀ m : ℕ, (((m + 1 : ℕ) : ℤ) : ℝ) = (m : ℝ) + 1 := fun m => by norm_num
  have hcast2 : ∀ m : ℕ, ((-((m : ℤ) + 1) : ℤ) : ℝ) = -((m : ℝ) + 1) := fun m => by norm_num
  have hpos1 : Summable (fun n : ℕ => Real.sinc (a * (((n + 1 : ℕ) : ℤ) : ℝ)) ^ 2) :=
    hgs.congr fun m => by rw [hcast1]
  have hpos : Summable (fun n : ℕ => Real.sinc (a * ((n : ℤ) : ℝ)) ^ 2) :=
    (summable_nat_add_iff 1).1 hpos1
  have hneg : Summable (fun n : ℕ => Real.sinc (a * ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2) :=
    hgs.congr fun m => by rw [hcast2, mul_neg, Real.sinc_neg]
  have E1 : ∑' n : ℤ, Real.sinc (a * (n : ℝ)) ^ 2
      = ∑' n : ℕ, Real.sinc (a * ((n : ℤ) : ℝ)) ^ 2
        + ∑' n : ℕ, Real.sinc (a * ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2 :=
    tsum_of_nat_of_neg_add_one (f := fun n : ℤ => Real.sinc (a * (n : ℝ)) ^ 2) hpos hneg
  have E2 : ∑' n : ℕ, Real.sinc (a * ((n : ℤ) : ℝ)) ^ 2
      = Real.sinc (a * (((0 : ℕ) : ℤ) : ℝ)) ^ 2
        + ∑' n : ℕ, Real.sinc (a * (((n + 1 : ℕ) : ℤ) : ℝ)) ^ 2 :=
    hpos.tsum_eq_zero_add
  have E3 : ∑' n : ℕ, Real.sinc (a * (((n + 1 : ℕ) : ℤ) : ℝ)) ^ 2
      = ∑' m : ℕ, Real.sinc (a * ((m : ℝ) + 1)) ^ 2 :=
    tsum_congr fun m => by rw [hcast1]
  have E4 : ∑' n : ℕ, Real.sinc (a * ((-((n : ℤ) + 1) : ℤ) : ℝ)) ^ 2
      = ∑' m : ℕ, Real.sinc (a * ((m : ℝ) + 1)) ^ 2 :=
    tsum_congr fun m => by rw [hcast2, mul_neg, Real.sinc_neg]
  have e0 : Real.sinc (a * (((0 : ℕ) : ℤ) : ℝ)) ^ 2 = 1 := by simp
  refine ⟨Summable.of_nat_of_neg_add_one
    (f := fun n : ℤ => Real.sinc (a * (n : ℝ)) ^ 2) hpos hneg, ?_⟩
  rw [E1, E2, E3, E4, e0]
  have : 8 / a = 4 / a + 4 / a := by ring
  linarith

/-- (F3') for the interval indicator in the variables of the paper: for `0 < ξ ≤ 1` and
    `σ = ξ²/6`, `Q(σ) = ∑_n F(σλ_n)² ≤ 3/ξ` (`= (3/√6) σ^{-1/2}`), and the series converges. -/
theorem ballF_F3' {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    Summable (fun n : ℤ => ballF (ξ ^ 2 / 6 * lam1 n) ^ 2) ∧
    sqSum lam1 ballF (ξ ^ 2 / 6) ≤ 3 / ξ := by
  have ha : 0 < 2 * Real.pi * ξ := by have := Real.pi_pos; positivity
  obtain ⟨hs, hb⟩ := sinc_sq_sum ha
  have e : (fun n : ℤ => ballF (ξ ^ 2 / 6 * lam1 n) ^ 2)
      = fun n : ℤ => Real.sinc (2 * Real.pi * ξ * n) ^ 2 :=
    funext fun n => by rw [ballF_eigen]
  unfold sqSum
  rw [e]
  refine ⟨hs, hb.trans ?_⟩
  have hπ := Real.two_le_pi
  have h1 : 8 / (2 * Real.pi * ξ) ≤ 2 / ξ := by
    rw [div_le_div_iff₀ ha hξ]
    nlinarith
  have h2 : 1 ≤ 1 / ξ := by rw [le_div_iff₀ hξ]; linarith
  have : 3 / ξ = 1 / ξ + 2 / ξ := by ring
  linarith

/-- **`thm:profileHS` for the indicator of an interval (`d = 1`, `β = 3/5`, `σ = ξ²/6`).**
    For `0 < ξ ≤ 1`, `σ = ξ²/6`, `t ≥ σ`, the list `λ_n = 4π²n²` and any number `m₁` with
    `|m₁| ≤ 3/ξ` (the paper: `m₁ = 1/(2ξ)`):
    (i) `|T^F_σ(t) - Θ(t) - (3/5)(σt/2)Θ''(t)| ≤ 𝓡₁`, and
    (ii) `|∑_n sinc(2πξn)^k - Θ(t) + (2/5)(σt/2)Θ''(t)| ≤ 𝓡₂` for `t = kσ`, `k ≥ 2`,
    with the explicit remainders of `profileHS_paper` and `B = 3/ξ`. -/
theorem interval_profile {ξ t m1 : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hts : ξ ^ 2 / 6 ≤ t)
    (hm : |m1| ≤ 3 / ξ) :
    |profTrHS lam1 ballF (ξ ^ 2 / 6) t m1 - heatTr lam1 t
        - 3 / 5 * (ξ ^ 2 / 6 * t / 2) * heatMom lam1 2 t|
      ≤ (ξ ^ 2 / 6 / t) ^ 2 * (profB (3 / 5) (3 / 70) ^ 2 / 2 * t ^ 4 * heatMom lam1 4 (t / 2)
            + 3 / 70 * t ^ 3 * heatMom lam1 3 (t / 2))
        + (profKHS (3 / 5) (1 / 30) + 1) * (1 + t / (ξ ^ 2 / 6))
            * Real.exp (-(profcHS (1 / 24) (1 / 30) * (t / (ξ ^ 2 / 6))))
            * (3 / ξ + heatTr lam1 (t / 4))
    ∧ ∀ k : ℕ, 2 ≤ k → (k : ℝ) * (ξ ^ 2 / 6) = t →
      |∑' n : ℤ, Real.sinc (2 * Real.pi * ξ * n) ^ k - heatTr lam1 t
          - (3 / 5 - 1) * (ξ ^ 2 / 6 * t / 2) * heatMom lam1 2 t|
        ≤ (ξ ^ 2 / 6 / t) ^ 2
            * (profB2 (3 / 5) (3 / 70) ^ 2 / 2 * t ^ 4 * heatMom lam1 4 (t / 2)
              + profCt (3 / 5) (3 / 70) * t ^ 3 * heatMom lam1 3 (t / 2))
          + profKHS2 (3 / 5) * (1 + t / (ξ ^ 2 / 6))
              * Real.exp (-(profcHS (1 / 24) (1 / 30) * (t / (ξ ^ 2 / 6))))
              * (3 / ξ + heatTr lam1 (t / 4)) := by
  have hσ : 0 < ξ ^ 2 / 6 := by positivity
  obtain ⟨hs, hb⟩ := ballF_F3' hξ hξ1
  obtain ⟨p1, p2⟩ := profileHS_paper lam1_isSpectrum ballF_hyp hσ hts hs hb hm
  refine ⟨p1, fun k hk hkt => ?_⟩
  have := p2 k hk hkt
  have e : discTr lam1 ballF (ξ ^ 2 / 6) k = ∑' n : ℤ, Real.sinc (2 * Real.pi * ξ * n) ^ k := by
    unfold discTr
    exact tsum_congr fun n => by rw [ballF_eigen]
  rw [e] at this
  exact this

end ProfilesWithJump

/-! ### Part C: `prop:sphere` and `prop:spheregap`, the algebra over `ℝ` (CONDITIONAL)

The round sphere `S²` with the Gaussian profile. NOTHING about the sphere is formalised here: no
spherical harmonics, no Funk–Hecke formula, no Legendre polynomials, no integrals. The eigenvalue
`s_l` of the population walk on the harmonics of degree `l` and the moments `𝗆_n = E[θ^n]` are free
real numbers, and the analytic input of the proof of `prop:sphere` is the HYPOTHESIS

  `hT : |s_l - (1 - (λ_l/4) 𝗆₂ + (λ_l(3λ_l - 2)/192) 𝗆₄)| ≤ (𝗆₆/720) λ_l³`

(Funk–Hecke: `s_l = E[P_l(cos θ)]`; Taylor's formula of order six for `f(θ) = P_l(cos θ)` with the
coefficients `-λ/4`, `λ(3λ-2)/192` (`legendre_coefficients` of the core file checks the recursion)
and `|f⁽⁶⁾| ≤ l⁶ ≤ λ_l³` by Bernstein's inequality). Proved from it, over `ℝ`, by instantiating
`sphere_low_mode`, `sphere_sigma`, `sphere_gap_low` of the core file:
* `sphere_F1`: `eq:sphereF1`, `|s_l - 1 + σ_ξ λ_l - (𝗆₄/64) λ_l²| ≤ (𝗆₆/720) λ_l³`,
  `σ_ξ = 𝗆₂/4 + 𝗆₄/96`;
* `sphere_F1_u`: the same as (F1) in the variable `u = σ_ξ λ_l`, with `β = 𝗆₄/(32 σ_ξ²)` and
  `c₃ = 𝗆₆/(720 σ_ξ³)`;
* `sphere_low_gap`: if moreover `0 ≤ β ≤ 51/50`, `c₃ ≤ 27/50` and `u ≤ 1/2`, then
  `2/5 ≤ s_l ≤ 1 - (3/5) u` (first display of `prop:spheregap`);
* `sphere_sequence`: the three statements for a sequence `s : ℕ → ℝ`, `λ_l = l(l+1)`;
* `sphere_sigma_real`: with `𝗆₂ I₀ = I₂`, `I₀ = x - x²/3`, `I₂ = 2x² - 4x³/3`, `𝗆₄ = 8x²`
  (`x = ξ²`; these are the integrals with `sin θ` replaced by `θ - θ³/6` and extended to
  `[0, ∞)`, HYPOTHESES): `σ_ξ - (x/2)(1 - x/6) = -(x³/18)/(1 - x/3)` for `0 < x < 3`.
NOT proved: `eq:spheresigma` for the true moments (the error terms `O(ξ⁶)`), the bounds
`β_ξ ≤ 51/50`, `c₃ ≤ 27/50` for small `ξ`, the high modes (Szegő's inequality), (F3').
-/

section SphereReal

/-- **`eq:sphereF1` from the Taylor estimate `hT` (HYPOTHESIS).** -/
theorem sphere_F1 {s lam m2 m4 m6 : ℝ}
    (hT : |s - (1 + (-(lam / 4)) * m2 + (lam * (3 * lam - 2) / 192) * m4)|
      ≤ m6 / 720 * lam ^ 3) :
    |s - 1 + (m2 / 4 + m4 / 96) * lam - m4 / 64 * lam ^ 2| ≤ m6 / 720 * lam ^ 3 := by
  rw [CTG.HeatTrace.sphere_low_mode lam m2 m4] at hT
  have e : s - 1 + (m2 / 4 + m4 / 96) * lam - m4 / 64 * lam ^ 2
      = s - (1 - (m2 / 4 + m4 / 96) * lam + m4 / 64 * (lam * lam)) := by ring
  rw [e]
  exact hT

/-- **(F1) on the sphere in the variable `u = σ_ξ λ`,** with `β = 𝗆₄/(32σ_ξ²)`,
    `c₃ = 𝗆₆/(720σ_ξ³)`; `hT` is the HYPOTHESIS of `sphere_F1`. -/
theorem sphere_F1_u {s lam m2 m4 m6 σ : ℝ} (hσ : σ = m2 / 4 + m4 / 96) (hσ0 : 0 < σ)
    (hT : |s - (1 + (-(lam / 4)) * m2 + (lam * (3 * lam - 2) / 192) * m4)|
      ≤ m6 / 720 * lam ^ 3) :
    |s - (1 - σ * lam + m4 / (32 * σ ^ 2) * (σ * lam) ^ 2 / 2)|
      ≤ m6 / (720 * σ ^ 3) * (σ * lam) ^ 3 := by
  have h := sphere_F1 hT
  rw [← hσ] at h
  have e1 : m4 / (32 * σ ^ 2) * (σ * lam) ^ 2 / 2 = m4 / 64 * lam ^ 2 := by
    field_simp; ring
  have e2 : m6 / (720 * σ ^ 3) * (σ * lam) ^ 3 = m6 / 720 * lam ^ 3 := by
    field_simp
  rw [e1, e2]
  have e : s - (1 - σ * lam + m4 / 64 * lam ^ 2) = s - 1 + σ * lam - m4 / 64 * lam ^ 2 := by ring
  rw [e]
  exact h

/-- **First display of `prop:spheregap` (low modes), over `ℝ`:** from (F1) with `0 ≤ β ≤ 51/50`,
    `0 ≤ c₃ ≤ 27/50`, for `0 ≤ u ≤ 1/2`: `2/5 ≤ s ≤ 1 - (3/5)u`. -/
theorem sphere_low_gap {u s β c : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (hb0 : 0 ≤ β)
    (hb1 : β ≤ 51 / 50) (hc0 : 0 ≤ c) (hc1 : c ≤ 27 / 50)
    (hF : |s - (1 - u + β * u ^ 2 / 2)| ≤ c * u ^ 3) :
    2 / 5 ≤ s ∧ s ≤ 1 - 3 / 5 * u := by
  obtain ⟨a, b⟩ := abs_le.1 hF
  have e2 : u ^ 2 = u * u := by ring
  have e3 : u ^ 3 = u * u * u := by ring
  rw [e2, e3] at a b
  exact CTG.HeatTrace.sphere_gap_low hu0 hu1 hb0 hb1 hc0 hc1 a b

/-- **`prop:sphere`/`prop:spheregap` for the sequence of eigenvalues, CONDITIONAL on `hT`.**
    Let `s : ℕ → ℝ`, `λ_l = l(l+1)`, `σ = 𝗆₂/4 + 𝗆₄/96 > 0`, `β = 𝗆₄/(32σ²)`, `c₃ = 𝗆₆/(720σ³)`.
    If `hT` holds for every `l` (HYPOTHESIS: Funk–Hecke, Taylor, Bernstein), then for every `l`:
    `eq:sphereF1`; (F1) at `u = σλ_l`; and, if `0 ≤ β ≤ 51/50`, `0 ≤ c₃ ≤ 27/50` and
    `σλ_l ≤ 1/2`: `2/5 ≤ s_l ≤ 1 - (3/5)σλ_l`. -/
theorem sphere_sequence {s : ℕ → ℝ} {m2 m4 m6 σ : ℝ} (hσ : σ = m2 / 4 + m4 / 96) (hσ0 : 0 < σ)
    (hT : ∀ l : ℕ, |s l - (1 + (-(((l : ℝ) * (l + 1)) / 4)) * m2
        + (((l : ℝ) * (l + 1)) * (3 * ((l : ℝ) * (l + 1)) - 2) / 192) * m4)|
      ≤ m6 / 720 * ((l : ℝ) * (l + 1)) ^ 3) (l : ℕ) :
    |s l - 1 + σ * ((l : ℝ) * (l + 1)) - m4 / 64 * ((l : ℝ) * (l + 1)) ^ 2|
        ≤ m6 / 720 * ((l : ℝ) * (l + 1)) ^ 3 ∧
    |s l - (1 - σ * ((l : ℝ) * (l + 1))
          + m4 / (32 * σ ^ 2) * (σ * ((l : ℝ) * (l + 1))) ^ 2 / 2)|
        ≤ m6 / (720 * σ ^ 3) * (σ * ((l : ℝ) * (l + 1))) ^ 3 ∧
    (0 ≤ m4 / (32 * σ ^ 2) → m4 / (32 * σ ^ 2) ≤ 51 / 50 → 0 ≤ m6 / (720 * σ ^ 3) →
      m6 / (720 * σ ^ 3) ≤ 27 / 50 → σ * ((l : ℝ) * (l + 1)) ≤ 1 / 2 →
      2 / 5 ≤ s l ∧ s l ≤ 1 - 3 / 5 * (σ * ((l : ℝ) * (l + 1)))) := by
  have hl : (0 : ℝ) ≤ (l : ℝ) * (l + 1) := by positivity
  have h1 := sphere_F1 (hT l)
  rw [← hσ] at h1
  have h2 := sphere_F1_u hσ hσ0 (hT l)
  exact ⟨h1, h2, fun hb0 hb1 hc0 hc1 hu =>
    sphere_low_gap (mul_nonneg hσ0.le hl) hu hb0 hb1 hc0 hc1 h2⟩

/-- **The algebra of `eq:spheresigma`, over `ℝ`:** with `𝗆₂ (x - x²/3) = 2x² - 4x³/3` and
    `𝗆₄ = 8x²` (HYPOTHESES, see above), for `0 < x < 3`:
    `𝗆₂/4 + 𝗆₄/96 - (x/2)(1 - x/6) = -(x³/18)/(1 - x/3)`. -/
theorem sphere_sigma_real {x m2 : ℝ} (hx : 0 < x) (hx3 : x < 3)
    (h : m2 * (x - x * x / 3) = 2 * (x * x) - 4 * (x * x * x) / 3) :
    m2 / 4 + 8 * (x * x) / 96 - x / 2 * (1 - x / 6) = -(x ^ 3 / 18) / (1 - x / 3) := by
  have h0 := CTG.HeatTrace.sphere_sigma x m2 h
  have hd : 0 < 1 - x / 3 := by linarith
  rw [eq_div_iff hd.ne']
  have hx0 : x ≠ 0 := hx.ne'
  have e : (m2 / 4 + 8 * (x * x) / 96 - x / 2 * (1 - x / 6)) * (x - x * x / 3)
      = (m2 / 4 + 8 * (x * x) / 96 - x / 2 * (1 - x / 6)) * (1 - x / 3) * x := by ring
  rw [e] at h0
  have h1 : (m2 / 4 + 8 * (x * x) / 96 - x / 2 * (1 - x / 6)) * (1 - x / 3) * x
      = -(x ^ 3 / 18) * x := by rw [h0]; ring
  exact mul_right_cancel₀ hx0 h1

end SphereReal

end OlderParts2

/-! ## The rate in `N` at a FIXED kernel scale on the flat torus (A52)

Counterpart, on the flat torus with uniform points and the periodised Gaussian kernel only, of
Proposition "rateN" of Appendix G: at a fixed kernel variance `σ ∈ (0,1]` (`σ = ξ²`) the traces
`Tr P^k` and the subtracted heat trace are within a constant times `√(log N/N)` of their limits,
almost surely for all large `N`. Both statements are the theorems `kernel_trace_rate` and
`heat_trace_rate` of `TraceRates` applied to the constant sequence `σ_N = σ`; the regime
`N σ^{d/2+1}/log N → ∞` then holds automatically.

NOT the proposition of the paper: that one is stated for a closed manifold, a density and a general
profile, in probability, with a constant that is not uniform in `ξ`. Here: torus, uniform density,
heat kernel, relative errors, nested sample, constants `kernelRateC`, `traceRateC` of the file
divided by `(σ^{d/2+1})^{1/2}`; the range of `k` is `k ≤ ⌈c/σ⌉` and of `τ` is `2 ≤ τ ≤ c/σ`. -/

namespace RateN

open Filter Topology TraceRates
open CTG.Reals.TraceG29

/-- For a constant `a > 0`: `N a / log N → ∞`. -/
theorem const_regime {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (N : ℝ) * a / Real.log N) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h0, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  have h2 : Tendsto (fun x : ℝ => (Real.log x / x)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun x : ℝ => a * (Real.log x / x)⁻¹) atTop atTop :=
    h2.const_mul_atTop ha
  have h4 := h3.comp tendsto_natCast_atTop_atTop
  refine h4.congr (fun N => ?_)
  simp only [Function.comp]
  rw [inv_div]
  ring

/-- `√(rateQ0 d σ N) = √(log N/N) / √(σ^{d/2} σ)`. -/
theorem sqrt_rateQ0 (d : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (N : ℕ) :
    Real.sqrt (rateQ0 d σ N)
      = Real.sqrt (Real.log N / N) / Real.sqrt (Real.sqrt σ ^ d * σ) := by
  have e : rateQ0 d σ N = (Real.log N / N) / (Real.sqrt σ ^ d * σ) := by
    unfold rateQ0
    rw [div_div, mul_assoc]
  rw [e, Real.sqrt_div']
  positivity

/-- **Rate `√(log N/N)` for `Tr P^k` at a fixed kernel scale, almost surely.** -/
theorem trace_pow_rateN {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ c : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hc : 0 < c) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ ⌈c / σ⌉₊ →
        |((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace
            / heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 - 1|
          ≤ kernelRateC d c / Real.sqrt (Real.sqrt σ ^ d * σ) * Real.sqrt (Real.log N / N) := by
  have hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt σ ^ d * σ / Real.log N) atTop atTop := by
    have ha : 0 < Real.sqrt σ ^ d * σ := by positivity
    refine (const_regime ha).congr (fun N => ?_)
    ring
  have h := kernel_trace_rate d hd X h_indep hX hlaw (fun _ => σ) hc
    (Eventually.of_forall fun _ => ⟨hσ, hσ1⟩) hreg
  filter_upwards [h] with ω hω
  filter_upwards [hω] with N hN k hk1 hk2
  have := hN k hk1 hk2
  rw [sqrt_rateQ0 d hσ.le] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Rate `√(log N/N)` (with the factor `(1 + σ log N)^{1/2}`) for the subtracted heat trace at a
    fixed kernel scale, almost surely, for all `τ` with `2 ≤ τ ≤ c/σ` at once.** -/
theorem heat_trace_rateN {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ c : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hc : 0 < c) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      ∀ τ : ℝ, 2 ≤ τ → τ ≤ c / σ →
        |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|
          ≤ traceRateC d c * Real.sqrt (rateQ d σ N) := by
  have hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt σ ^ d * σ / Real.log N) atTop atTop := by
    have ha : 0 < Real.sqrt σ ^ d * σ := by positivity
    refine (const_regime ha).congr (fun N => ?_)
    ring
  exact heat_trace_rate d hd X h_indep hX hlaw (fun _ => σ) hc
    (Eventually.of_forall fun _ => ⟨hσ, hσ1⟩) hreg

end RateN

/-! ## The joint regime of Theorem "jointslow" on the flat torus (A53)

Theorem "jointslow" of Appendix G assumes `ξ_N → 0` and `ξ_N^{d+2} log N ≥ 64`. With `σ = ξ²` this
reads `σ_N^{d/2+1} log N ≥ 64`, and it implies both regimes used in this file:
`N σ^{d/2+1}/log N ≥ 64 N/(log N)² → ∞` and `N σ^{d/2+3}/log N ≥ 64³ N/(log N)⁴ → ∞`
(`jointslow_regime1`, `jointslow_regime3`). Hence the statements of `TraceRates` and `SharpRate`
hold in the regime of that theorem: `jointslow_trace_pow` (relative error of `Tr P^k` with a rate,
`k ≤ ⌈1/σ_N⌉`) and `jointslow_sharp` (the "Consequently" display: the subtracted trace divided by
`Θ(t)`, uniformly for `σ_N ≤ t ≤ 1`).

NOT the theorem of the paper: its first display bounds the ABSOLUTE errors by `N^{-1/4}`; here the
errors are relative, with the rates and constants of the file, and the proof is the one of the
kernel theorem, not the moment argument of the paper. `ξ_N → 0` is not needed. The remarks at the
head of `SharpRate` apply (for `t` of order one the coefficient is not identified). -/

namespace JointSlow

open Filter Topology TraceRates SharpRate PopulationRate

/-- `N/(log N)^n → ∞`. -/
theorem pow_log_regime (n : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) / Real.log N ^ n) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ n / x) atTop (𝓝 0) :=
    (Real.isLittleO_pow_log_id_atTop (n := n)).tendsto_div_nhds_zero
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ n / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h0, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (pow_pos (Real.log_pos hx) n) (by linarith)
  have h2 : Tendsto (fun x : ℝ => (Real.log x ^ n / x)⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h4 := h2.comp tendsto_natCast_atTop_atTop
  refine h4.congr (fun N => ?_)
  simp only [Function.comp]
  rw [inv_div]

/-- From `0 < σ ≤ 1`, `64 ≤ σ^{d/2} σ L`, `L > 0`: `64 ≤ σ L`. -/
theorem sigma_log_ge {d : ℕ} {s L : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) (hL : 0 < L)
    (h64 : 64 ≤ Real.sqrt s ^ d * s * L) : 64 ≤ s * L := by
  have hA1 : Real.sqrt s ^ d ≤ 1 :=
    pow_le_one₀ (Real.sqrt_nonneg s) (Real.sqrt_le_one.mpr h1)
  have hsL : 0 ≤ s * L := (mul_pos h0 hL).le
  have : Real.sqrt s ^ d * s * L ≤ s * L := by
    rw [mul_assoc]
    exact mul_le_of_le_one_left hsL hA1
  linarith

/-- The regime `N σ^{d/2+1}/log N → ∞` follows from `σ_N^{d/2+1} log N ≥ 64`. -/
theorem jointslow_regime1 (d : ℕ) (σ : ℕ → ℝ)
    (hs : ∀ᶠ N : ℕ in atTop, 0 < σ N ∧ σ N ≤ 1 ∧
      64 ≤ Real.sqrt (σ N) ^ d * σ N * Real.log N) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N) atTop atTop := by
  have h := (pow_log_regime 2).const_mul_atTop (show (0 : ℝ) < 64 by norm_num)
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [hs, eventually_gt_atTop 1] with N hN h1N
  obtain ⟨h0, h1, h64⟩ := hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast h1N)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have e : (N : ℝ) * Real.sqrt (σ N) ^ d * σ N / Real.log N
      = (N : ℝ) * (Real.sqrt (σ N) ^ d * σ N * Real.log N) / Real.log N ^ 2 := by
    rw [div_eq_div_iff hL.ne' (pow_pos hL 2).ne']
    ring
  have e2 : (64 : ℝ) * ((N : ℝ) / Real.log N ^ 2) = (N : ℝ) * 64 / Real.log N ^ 2 := by ring
  show (64 : ℝ) * ((N : ℝ) / Real.log N ^ 2) ≤ _
  rw [e, e2]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h64 hN0) (pow_pos hL 2).le

/-- The regime `N σ^{d/2+3}/log N → ∞` follows from `σ_N^{d/2+1} log N ≥ 64`. -/
theorem jointslow_regime3 (d : ℕ) (σ : ℕ → ℝ)
    (hs : ∀ᶠ N : ℕ in atTop, 0 < σ N ∧ σ N ≤ 1 ∧
      64 ≤ Real.sqrt (σ N) ^ d * σ N * Real.log N) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop := by
  have h := (pow_log_regime 4).const_mul_atTop (show (0 : ℝ) < 64 * 64 ^ 2 by norm_num)
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [hs, eventually_gt_atTop 1] with N hN h1N
  obtain ⟨h0, h1, h64⟩ := hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast h1N)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsL := sigma_log_ge h0 h1 hL h64
  have hsq : (64 : ℝ) ^ 2 ≤ (σ N * Real.log N) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hsL 2
  have hprod : (64 : ℝ) * 64 ^ 2
      ≤ (Real.sqrt (σ N) ^ d * σ N * Real.log N) * (σ N * Real.log N) ^ 2 :=
    mul_le_mul h64 hsq (by norm_num) (by linarith)
  have e : (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N
      = (N : ℝ) * ((Real.sqrt (σ N) ^ d * σ N * Real.log N) * (σ N * Real.log N) ^ 2)
          / Real.log N ^ 4 := by
    rw [div_eq_div_iff hL.ne' (pow_pos hL 4).ne']
    ring
  have e2 : (64 : ℝ) * 64 ^ 2 * ((N : ℝ) / Real.log N ^ 4)
      = (N : ℝ) * (64 * 64 ^ 2) / Real.log N ^ 4 := by ring
  show (64 : ℝ) * 64 ^ 2 * ((N : ℝ) / Real.log N ^ 4) ≤ _
  rw [e, e2]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hN0) (pow_pos hL 4).le

/-- **`Tr P^k` in the regime of Theorem "jointslow", almost surely, with a rate** (relative error,
    all `1 ≤ k ≤ ⌈1/σ_N⌉`). -/
theorem jointslow_trace_pow {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ)
    (hs : ∀ᶠ N : ℕ in atTop, 0 < σ N ∧ σ N ≤ 1 ∧
      64 ≤ Real.sqrt (σ N) ^ d * σ N * Real.log N) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ ⌈1 / σ N⌉₊ →
        |((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k).trace
            / heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 - 1|
          ≤ kernelRateC d 1 * Real.sqrt (rateQ0 d (σ N) N) :=
  kernel_trace_rate d hd X h_indep hX hlaw σ one_pos (hs.mono fun _ h => ⟨h.1, h.2.1⟩)
    (jointslow_regime1 d σ hs)

/-- **The "Consequently" display of Theorem "jointslow", almost surely, uniformly in
    `σ_N ≤ t ≤ 1`** (`τ = 2t/σ_N`, `Θ(t) = heatTr (torusLam d) t`). -/
theorem jointslow_sharp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ)
    (hs : ∀ᶠ N : ℕ in atTop, 0 < σ N ∧ σ N ≤ 1 ∧
      64 ≤ Real.sqrt (σ N) ^ d * σ N * Real.log N) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, σ N ≤ t → t ≤ 1 →
      |((NormedSpace.exp ((2 * t / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t / σ N))) / heatTr (torusLam d) t - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t)|
        ≤ sharpC2 d * (σ N / 2 / t) ^ 2 + sharpC1 d * (σ N / 2) + η * σ N :=
  sharp_rate_ae d hd X h_indep hX hlaw σ (hs.mono fun _ h => ⟨h.1, h.2.1⟩)
    (jointslow_regime3 d σ hs)

end JointSlow

/-! ## The regime of Theorem "jointpoly" on the flat torus (A54)

Theorem "jointpoly" of Appendix G assumes `N ξ_N^{2d+6}/log N → ∞`; with `σ = ξ²` this is
`N σ_N^{d+3}/log N → ∞`. For `σ_N ≤ 1` it implies the regime `N σ_N^{d/2+3}/log N → ∞` of
`SharpRate.sharp_rate_ae` (`jointpoly_regime3`), so the last display of that theorem holds there
ALMOST SURELY and uniformly in `σ_N ≤ t ≤ 1` (`jointpoly_sharp`), for every `d ≥ 1`.

NOT the theorem of the paper as proved there: the paper proves it in probability, for `d ≥ 2`, by
counting closed walks for the walk with exact normalisation (Lemma "oraclemoments"); that argument
is NOT formalised. Here the conclusion is obtained from the kernel theorem. The remarks at the
head of `SharpRate` apply. -/

namespace JointPoly

open Filter Topology SharpRate PopulationRate

/-- `N σ^{d+3}/log N → ∞` and `σ ≤ 1` give `N σ^{d/2+3}/log N → ∞`. -/
theorem jointpoly_regime3 (d : ℕ) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N : ℕ in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * σ N ^ (d + 3) / Real.log N) atTop atTop) :
    Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt (σ N) ^ d * σ N ^ 3 / Real.log N)
      atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ hreg
  filter_upwards [hσ, eventually_gt_atTop 1] with N hN h1N
  obtain ⟨h0, h1⟩ := hN
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast h1N)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hA0 : 0 ≤ Real.sqrt (σ N) ^ d := pow_nonneg (Real.sqrt_nonneg _) d
  have hA1 : Real.sqrt (σ N) ^ d ≤ 1 :=
    pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr h1)
  have hsq : σ N ^ d = Real.sqrt (σ N) ^ d * Real.sqrt (σ N) ^ d := by
    rw [← mul_pow, Real.mul_self_sqrt h0.le]
  have hle : σ N ^ d ≤ Real.sqrt (σ N) ^ d := by
    rw [hsq]
    exact mul_le_of_le_one_left hA0 hA1
  have h3 : 0 ≤ σ N ^ 3 := pow_nonneg h0.le 3
  show (N : ℝ) * σ N ^ (d + 3) / Real.log N ≤ _
  refine div_le_div_of_nonneg_right ?_ hL.le
  rw [pow_add, mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle h3) hN0

/-- **The last display of Theorem "jointpoly" in its regime, almost surely, uniformly in
    `σ_N ≤ t ≤ 1`** (`τ = 2t/σ_N`, `Θ(t) = heatTr (torusLam d) t`). -/
theorem jointpoly_sharp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ N : ℕ in atTop, 0 < σ N ∧ σ N ≤ 1)
    (hreg : Tendsto (fun N : ℕ => (N : ℝ) * σ N ^ (d + 3) / Real.log N) atTop atTop) :
    ∀ᵐ ω ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, σ N ≤ t → t ≤ 1 →
      |((NormedSpace.exp ((2 * t / σ N) • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-(2 * t / σ N))) / heatTr (torusLam d) t - 1
          - (d : ℝ) * ((d : ℝ) + 2) / 8 * (σ N / 2 / t)|
        ≤ sharpC2 d * (σ N / 2 / t) ^ 2 + sharpC1 d * (σ N / 2) + η * σ N :=
  sharp_rate_ae d hd X h_indep hX hlaw σ hσ (jointpoly_regime3 d σ hσ hreg)

end JointPoly

/-! ## Proposition "estimated" on the flat torus with the Gaussian kernel (A55)

At a FIXED kernel variance `σ ∈ (0,1]` and a fixed `τ ≥ 2` the relative error of the subtracted
heat trace of the sampled graph (estimated normalisation, self-loops) is `O_P(log N/N)`: for every
`ε > 0` there is `C` with `P(|…| > C log N/N) ≤ ε` for all large `N`. This is
`SecondStageLimit.second_stage_tight` for constant sequences.

NOT the proposition of the paper: there `p` is any even Lipschitz density on a torus and `τ > 0`
is arbitrary, and the first display (for `Tr P^j`, fixed `j`) is stated separately; here only the
periodised Gaussian kernel, `τ ≥ 2`, the error relative to `poissonMean`, the nested sample, and
the proof through the second-stage reduction instead of the expansion in the normalisation
errors. -/

namespace EstimatedTorus

open Filter Topology
open CTG.Reals.TraceG29

theorem estimated_trace_OP {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ τ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hτ : 2 ≤ τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      μ.real {ω | C * (Real.log N / N)
        < |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|}
        ≤ ε := by
  have hreg : Tendsto (fun N : ℕ => (N : ℝ) * Real.sqrt σ ^ d * σ / Real.log N) atTop atTop := by
    have ha : 0 < Real.sqrt σ ^ d * σ := by positivity
    refine (RateN.const_regime ha).congr (fun N => ?_)
    ring
  have hτ0 : 0 < τ := by linarith
  obtain ⟨C, hC, h⟩ := SecondStageLimit.second_stage_tight d hd X h_indep hX hlaw
    (fun _ => σ) (fun _ => τ) (c := τ * σ) (mul_pos hτ0 hσ)
    (Eventually.of_forall fun _ => ⟨hσ, hσ1⟩)
    (Eventually.of_forall fun _ => ⟨hτ, (mul_div_cancel_right₀ τ hσ.ne').ge⟩) hreg hε
  have hM : 0 < heatTorus d (2 * Real.pi ^ 2 * σ) 0 :=
    heatTorus_zero_pos (mul_pos (by positivity) hσ) d
  refine ⟨C * heatTorus d (2 * Real.pi ^ 2 * σ) 0 * τ, mul_pos (mul_pos hC hM) hτ0, ?_⟩
  filter_upwards [h] with N hN
  have e : C * heatTorus d (2 * Real.pi ^ 2 * σ) 0 * τ * (Real.log N / N)
      = C * (heatTorus d (2 * Real.pi ^ 2 * σ) 0 * Real.log N / N) * τ := by ring
  rw [e]
  exact hN

end EstimatedTorus

/-! ## Proposition "oracle" for `j = 2` (A56)

Second moment of a degenerate two-point statistic INCLUDING the diagonal, and from it the case
`j = 2` of Proposition "oracle" of Appendix G: for the walk with exact normalisation,
`Tr P̃² = N⁻² ∑_{i,j} p(x_i - x_j)²` (for an even kernel), and
`E (Tr P̃² - m₂)² ≤ (4V + 2B²)/N²`, i.e. the fluctuations are of order `1/N`.

HYPOTHESIS, as the structure `Deg2`: the points are independent with law `ν`, and
`ψ = p² - m` is measurable, bounded by `B`, even, DEGENERATE (`∫ ψ(x - z) dν(z) = 0` for every
`x`; for a translation-invariant `ν` this says `m = ∫ p²`) with `∫ ψ(x - z)² dν(z) ≤ V`.

NOT the proposition of the paper: only `j = 2`. For general `j` the paper uses Hoeffding's
variance formula for U-statistics of order `j` and a count of index coincidences; neither is
formalised. With `0 ≤ p ≤ M`, `B = M²`, `V = M⁴` the bound reads `√6 M²/N`, below the `12 M²/N`
of the paper. -/

namespace OracleTwo

open PiBound

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ : G → ℝ} {B V : ℝ}

omit [MeasurableSpace G] [MeasurableSub₂ G] in
theorem full_sum_eq (ψ : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
      = Soff ψ X N ω + N * ψ 0 := by
  unfold Soff
  have h : ∀ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
      = ∑ j ∈ Finset.range N, aT ψ X i j ω + ψ 0 := by
    intro i hi
    have h' : ∀ j ∈ Finset.range N, ψ (X i ω - X j ω)
        = aT ψ X i j ω + (if i = j then ψ 0 else 0) := by
      intro j _
      unfold aT
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl h', Finset.sum_add_distrib, Finset.sum_ite_eq (Finset.range N) i,
      if_pos hi]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib]
  simp [Finset.sum_const, nsmul_eq_mul]

theorem Soff_meas (H : Deg2 μ ν X ψ B V) (N : ℕ) : Measurable (Soff ψ X N) := by
  unfold Soff
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => H.aT_meas i j

theorem Soff_bound (H : Deg2 μ ν X ψ B V) (N : ℕ) (ω : Ω) :
    |Soff ψ X N ω| ≤ (N : ℝ) * ((N : ℝ) * B) := by
  unfold Soff
  calc |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, aT ψ X i j ω|
      ≤ ∑ i ∈ Finset.range N, |∑ j ∈ Finset.range N, aT ψ X i j ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, |aT ψ X i j ω| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => H.aT_bound i j ω
    _ = (N : ℝ) * ((N : ℝ) * B) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- **Second moment of the full degenerate two-point statistic** (diagonal included):
    `E (N⁻² ∑_{i,j} ψ(X_i - X_j))² ≤ (1/N²)² (4 N² V + 2 N² B²)`, which is `(4V + 2B²)/N²`. -/
theorem Z0_second_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg2 μ ν X ψ B V) (N : ℕ) :
    ∫ ω, (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ψ (X i ω - X j ω)) ^ 2 ∂μ
      ≤ (1 / (N : ℝ) ^ 2) ^ 2 * (4 * (N : ℝ) ^ 2 * V + 2 * ((N : ℝ) ^ 2 * B ^ 2)) := by
  have hB := H.B_nonneg
  have hc : |ψ 0| ≤ B := H.bound 0
  have hc2 : ψ 0 ^ 2 ≤ B ^ 2 := by
    have := abs_le.mp hc
    nlinarith
  have hI : Integrable (fun ω => Soff ψ X N ω ^ 2) μ := by
    refine Integrable.of_bound ((Soff_meas H N).pow_const 2).aestronglyMeasurable
      (((N : ℝ) * ((N : ℝ) * B)) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (Soff_bound H N ω) 2
  have hpt : ∀ ω, (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        ψ (X i ω - X j ω)) ^ 2
      ≤ (1 / (N : ℝ) ^ 2) ^ 2 * (2 * Soff ψ X N ω ^ 2 + 2 * ((N : ℝ) ^ 2 * B ^ 2)) := by
    intro ω
    rw [full_sum_eq, mul_pow]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 : ((N : ℝ) * ψ 0) ^ 2 ≤ (N : ℝ) ^ 2 * B ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hc2 (by positivity)
    nlinarith [_root_.sq_nonneg (Soff ψ X N ω - (N : ℝ) * ψ 0)]
  have hg : Integrable (fun ω => (1 / (N : ℝ) ^ 2) ^ 2 *
      (2 * Soff ψ X N ω ^ 2 + 2 * ((N : ℝ) ^ 2 * B ^ 2))) μ :=
    ((hI.const_mul 2).add (integrable_const _)).const_mul _
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => by positivity) hg (Filter.Eventually.of_forall hpt)
  refine hmono.trans ?_
  rw [integral_const_mul, integral_add (hI.const_mul 2) (integrable_const _), integral_const_mul]
  have hconst : ∫ _ : Ω, (2 * ((N : ℝ) ^ 2 * B ^ 2)) ∂μ = 2 * ((N : ℝ) ^ 2 * B ^ 2) := by simp
  rw [hconst]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := H.second_moment N
  linarith

/-- **Proposition "oracle" for `j = 2`:** with `ψ = p² - m` degenerate,
    `E (N⁻² ∑_{i,j} p(X_i - X_j)² - m)² ≤ (1/N²)² (4N²V + 2N²B²)` for `N ≥ 1`; the left-hand
    statistic is `Tr P̃²` for an even kernel `p`. -/
theorem oracle_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {p : G → ℝ} {m : ℝ}
    (H : Deg2 μ ν X (fun u => p u ^ 2 - m) B V) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        p (X i ω - X j ω) ^ 2 - m) ^ 2 ∂μ
      ≤ (1 / (N : ℝ) ^ 2) ^ 2 * (4 * (N : ℝ) ^ 2 * V + 2 * ((N : ℝ) ^ 2 * B ^ 2)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ∀ ω, 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        p (X i ω - X j ω) ^ 2 - m
      = 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (p (X i ω - X j ω) ^ 2 - m) := by
    intro ω
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_sub]
    congr 1
    field_simp
  simp_rw [e]
  exact Z0_second_moment H N

end OracleTwo

/-! ## Proposition "oracle" for `j = 2` on the flat torus with the Gaussian kernel (A57)

The hypothesis `Deg2` of `OracleTwo.oracle_two` is discharged for the periodised Gaussian kernel
`p = pker d σ` of variance `σ` on the flat torus with uniform points (`φ⁰ = p·p - m₂` of `PiBound`
with `k = 1`): for `N ≥ 1`, with `M = m₁ = p(0)`,
`E (N⁻² ∑_{i,j} p(X_i - X_j)² - m₂)² ≤ (1/N²)² (4 N² M³ + 2 N² M⁴)`, i.e. `≤ (4M³ + 2M⁴)/N²`.
The statistic is `Tr P̃²` for the walk `P̃_{ij} = p(x_i - x_j)/N` with exact normalisation.
No hypothesis beyond: independent, measurable, uniform points and `σ > 0`. Only `j = 2`. -/

namespace OracleTwoTorus

open PiBound OracleTwo CTG.Reals.TorusReduction

theorem oracle_two_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        pker d σ (X i ω - X j ω) ^ 2 - torusM d σ 2) ^ 2 ∂μ
      ≤ (1 / (N : ℝ) ^ 2) ^ 2 * (4 * (N : ℝ) ^ 2 * (torusM d σ 1 * torusM d σ 1 ^ 2)
          + 2 * ((N : ℝ) ^ 2 * (torusM d σ 1 * torusM d σ 1) ^ 2)) := by
  have hM0 : 0 ≤ torusM d σ 1 := (torusM_pos hσ d le_rfl).le
  have H0 : Deg2 μ (flatTorusMeasure d) X (phi0 d σ 1) (torusM d σ 1 * torusM d σ 1)
      (torusM d σ 1 * torusM d σ 1 ^ 2) :=
    { indep := h_indep
      meas := hX
      law := hlaw
      psi_meas := (phi0_continuous hσ d 1 le_rfl).measurable
      bound := phi0_bound hσ d 1 le_rfl
      even := phi0_even d σ 1
      mean := phi0_mean hσ d 1 le_rfl
      var := phi0_var hσ d 1 le_rfl
      V_nonneg := mul_nonneg hM0 (_root_.sq_nonneg _) }
  have hfun : (fun u : FlatTorus d => pker d σ u ^ 2 - torusM d σ 2) = phi0 d σ 1 := by
    funext u
    simp only [phi0, pker, heatP_one, pow_two, Nat.reduceAdd]
  have H1 : Deg2 μ (flatTorusMeasure d) X (fun u : FlatTorus d => pker d σ u ^ 2 - torusM d σ 2)
      (torusM d σ 1 * torusM d σ 1) (torusM d σ 1 * torusM d σ 1 ^ 2) := by
    rw [hfun]
    exact H0
  exact oracle_two H1 N hN

end OracleTwoTorus

/-! ## Lemma "oraclemoments" for `k = 2` on the flat torus (A58)

For the walk with exact normalisation `P̃_{ij} = p(x_i - x_j)/N`, `p = pker d σ` the periodised
Gaussian kernel, `M = m₁ = p(0)`: `E |Tr P̃² - m₂| ≤ 16 M²/N` for every `N ≥ 1`. This is the bound
`4 k² M²/N` of Lemma "oraclemoments" of Appendix G for `k = 2` (the trace written as a double
sum), here WITHOUT the condition `k² M ≤ N`. It follows from the second moment
`OracleTwoTorus.oracle_two_torus` and Cauchy–Schwarz.

NOT the lemma of the paper: only `k = 2` (and `k = 1` is trivial, `Tr P̃ = M = m₁`). The general
case needs the count of closed walks by coincidence pattern and the spanning-tree integration;
neither is formalised. -/

namespace OracleMomentsTwo

open PiBound OracleTwo OracleTwoTorus CTG.Reals.TorusReduction

theorem oraclemoments_two {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, |1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        pker d σ (X i ω - X j ω) ^ 2 - torusM d σ 2| ∂μ
      ≤ 16 * torusM d σ 1 ^ 2 / N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have e : ∀ ω, 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        pker d σ (X i ω - X j ω) ^ 2 - torusM d σ 2
      = 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          phi0 d σ 1 (X i ω - X j ω) := by
    intro ω
    have h1 : ∀ i j : ℕ, phi0 d σ 1 (X i ω - X j ω)
        = pker d σ (X i ω - X j ω) ^ 2 - torusM d σ 2 := by
      intro i j
      simp only [phi0, pker, heatP_one, pow_two, Nat.reduceAdd]
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [mul_sub]
    congr 1
    field_simp
  have hmeas : Measurable fun ω => 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N,
      ∑ j ∈ Finset.range N, pker d σ (X i ω - X j ω) ^ 2 - torusM d σ 2 :=
    ((Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((pker_continuous hσ d).measurable.comp ((hX i).sub (hX j))).pow_const 2).const_mul
        _).sub_const _
  have hb : ∀ ω, |1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        pker d σ (X i ω - X j ω) ^ 2 - torusM d σ 2|
      ≤ 1 / (N : ℝ) ^ 2 * ((N : ℝ) * ((N : ℝ) * (torusM d σ 1 * torusM d σ 1))) := by
    intro ω
    rw [e ω, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, phi0 d σ 1 (X i ω - X j ω)|
        ≤ ∑ i ∈ Finset.range N, |∑ j ∈ Finset.range N, phi0 d σ 1 (X i ω - X j ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, |phi0 d σ 1 (X i ω - X j ω)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, torusM d σ 1 * torusM d σ 1 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            phi0_bound hσ d 1 le_rfl _
      _ = (N : ℝ) * ((N : ℝ) * (torusM d σ 1 * torusM d σ 1)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have h2 := abs_integral_le_sqrt (μ := μ) _ hmeas hb
    (oracle_two_torus X h_indep hX hlaw hσ N hN)
  refine h2.trans ?_
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hr : (16 * torusM d σ 1 ^ 2 / (N : ℝ)) ^ 2 = (16 * torusM d σ 1 ^ 2) ^ 2 / (N : ℝ) ^ 2 :=
    div_pow _ _ _
  rw [hr, le_div_iff₀ (by positivity)]
  have ht : 1 / (N : ℝ) ^ 2 * (N : ℝ) ^ 2 = 1 := by field_simp
  have hw : (1 / (N : ℝ) ^ 2) ^ 2 * (4 * (N : ℝ) ^ 2 * (torusM d σ 1 * torusM d σ 1 ^ 2)
        + 2 * ((N : ℝ) ^ 2 * (torusM d σ 1 * torusM d σ 1) ^ 2)) * (N : ℝ) ^ 2
      = (1 / (N : ℝ) ^ 2 * (N : ℝ) ^ 2) ^ 2
          * (4 * (torusM d σ 1 * torusM d σ 1 ^ 2) + 2 * (torusM d σ 1 * torusM d σ 1) ^ 2) := by
    ring
  rw [hw, ht]
  have h34 : torusM d σ 1 ^ 3 ≤ torusM d σ 1 ^ 4 := by
    nlinarith [mul_nonneg (pow_nonneg hM0 3) (sub_nonneg.mpr hM1)]
  nlinarith [h34, pow_nonneg hM0 4]

end OracleMomentsTwo


/-! ## Lemma "oraclemoments" and Proposition "oracle" for EVERY number of steps (A59)

The walk with exact normalisation `P̃_{ab} = p(x_a - x_b)/N` on `N` independent uniform points of
the flat torus, `p = pker d σ` the periodised Gaussian kernel of variance `σ`, `M = p(0) = m₁`,
`m_k = p^{*k}(0) = torusM d σ k`.  For every `k ≥ 1` with `k² M ≤ N`:

* `oraclemoments_torus`:       `E |Tr P̃^k - m_k| ≤ 3 k² M²/N`   (Lemma "oraclemoments"; the paper
  has the constant 4);
* `oraclemoments_bias_torus`:  `|E Tr P̃^k - m_k| ≤ k² M²/N`;
* `oracle_torus` (`k ≥ 2`):    `E (Tr P̃^k - m_k)² ≤ (3 k² M^k/N)²`   (the form of Proposition
  "oracle", in the regime `k² M ≤ N` instead of `k ≤ N/2`).

`Tr P̃^k` is the trace of the `k`-th power of the matrix `Matrix.of fun a b : Fin N => p(X_a - X_b)/N`.
The three statements are instances of `RK.oraclemoments`, which holds for any family of kernels
`q_i(x,y)` on a probability space `(G, ν)` satisfying the HYPOTHESES collected in the structure
`RK` (measurable, nonnegative, `q_1 ≤ M`, mass one, semigroup, constant diagonal `m_i`, `1 ≤ M`,
`0 ≤ m_i ≤ M`); `torusRK` proves them for the Gaussian kernel on the flat torus, so the three
statements on the torus carry no hypothesis beyond: independent, measurable, uniform points, `σ > 0`,
`k² M ≤ N`.

How the proof follows the paper, and where it deviates:
* `Tr P̃^k = N^{-k} ∑` over the lists `I` of `k` indices of the closed-walk products `cyc q x I`
  (`trace_walk_pow`); the lists with distinct entries give `D_k` (`Dsum`).
* Distinct entries: the expectation is `m_k` (`RK.int_nodup`), by integrating out one vertex after
  the other with the semigroup (`ch_marginal`, `ch_integral`).  The same computation next to a
  factor depending on at most one vertex of the walk (`cyc_integral_spect`) is the degeneracy
  "the conditional expectation of `g_I` given one of its points is `m_k`"; it gives
  `E g_I g_J = m_k²` for two walks with at most one common index (`RK.pair_eq`).
* Spanning tree: instead of choosing a spanning tree of the image multigraph, the walk is explored
  from its first vertex; an edge to a vertex that does not occur later (and not in a second walk
  `J`) is integrated out with `∫ p = 1`, every other edge is bounded by `M` (`op_integral_le`).
  This gives `E g_I ≤ M · wt(I)` (`RK.int_le`), `wt(I) = M^{#repeated entries}`, which is the bound
  `M^{c+1}` of the paper, and `E g_I g_J ≤ M² · M^{#common indices}` (`RK.pair_le`), ONE FACTOR `M`
  MORE than the `M^{c+1}` of the paper (both closing edges are bounded by `M`).
* Counting: NO partitions.  The weights are multiplicative along the list, so their sums over all
  lists satisfy one-step recursions (`sum_LL_succ`): `#distinct = ∏(N - l)` (`aN_succ`,
  `aN_bounds`), `∑ wt ≤ N^k (1 + k²(M-1)/N)` (`bN_bound`), and for the pairs with at least two
  common indices two marked entries (`w1`, `w2`, `s_bounds`).  The bounds are
  `E[Tr P̃^k - D_k] ≤ k² M²/N` (as in the paper) and `Var`-type bound
  `E (D_k - m_k)² ≤ (2 k² M²/N)²` (the paper: `Var D_k ≤ 2 k⁴ M³/N²`).
* NOT formalised: the count of the coincidence patterns by partitions (`binom(k,2)^c / c!`), the
  bound `M^{c+1}` for pairs, Hoeffding's variance formula used in the proof of Proposition
  "oracle" of the paper, the range `k ≤ N/2` with `k² M > N` of that proposition, and a second
  moment of `Tr P̃^k` on the scale `k² M²/N` (`oracle_torus` bounds the walks with repeated
  indices pointwise by `M^k`, as the paper does).  Evenness of `p` is not used. -/


namespace WalkCount

open MeasureTheory Function
open scoped ENNReal

/-! ### Lists of a fixed length as a finite set -/

section Lists

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All lists of length `n` over `ι`. -/
def LL (ι : Type*) [Fintype ι] [DecidableEq ι] : ℕ → Finset (List ι)
  | 0 => {[]}
  | n + 1 => Finset.univ.biUnion fun a : ι => (LL ι n).image (List.cons a)

theorem mem_LL {n : ℕ} {L : List ι} : L ∈ LL ι n ↔ L.length = n := by
  induction n generalizing L with
  | zero => simp [LL]
  | succ n ih =>
    simp only [LL, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨a, L', hL', rfl⟩
      simp [ih.mp hL']
    · intro h
      cases L with
      | nil => simp at h
      | cons a L' => exact ⟨a, L', ih.mpr (by simpa using h), rfl⟩

theorem sum_LL_succ {R : Type*} [AddCommMonoid R] (n : ℕ) (F : List ι → R) :
    ∑ L ∈ LL ι (n + 1), F L = ∑ L ∈ LL ι n, ∑ a : ι, F (a :: L) := by
  rw [Finset.sum_comm]
  show ∑ L ∈ Finset.univ.biUnion (fun a : ι => (LL ι n).image (List.cons a)), F L = _
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_image]
    intro L _ L' _ h
    exact (List.cons.inj h).2
  · intro a _ b _ hab
    show Disjoint ((LL ι n).image (List.cons a)) ((LL ι n).image (List.cons b))
    rw [Finset.disjoint_left]
    intro L hL hL'
    simp only [Finset.mem_image] at hL hL'
    obtain ⟨L1, _, rfl⟩ := hL
    obtain ⟨L2, _, h2⟩ := hL'
    exact hab (List.cons.inj h2).1.symm

theorem exists_cons_of_mem_LL {n : ℕ} {I : List ι} (h : I ∈ LL ι (n + 1)) :
    ∃ a L, I = a :: L ∧ L.length = n := by
  have hl := mem_LL.mp h
  cases I with
  | nil => simp at hl
  | cons a L => exact ⟨a, L, rfl, by simpa using hl⟩

/-- `∑_a (if a ∈ L then u else w) = |L| u + (N - |L|) w`, `|L|` the number of distinct entries. -/
theorem sum_ite_mem (L : List ι) (u w : ℝ) :
    ∑ a : ι, (if a ∈ L then u else w)
      = (L.toFinset.card : ℝ) * u + ((Fintype.card ι : ℝ) - L.toFinset.card) * w := by
  have h1 : ∀ a : ι, (if a ∈ L then u else w) = w + (if a ∈ L then (u - w) else 0) := by
    intro a; split_ifs <;> ring
  have h2 : (Finset.univ.filter fun a : ι => a ∈ L) = L.toFinset := by
    ext a; simp
  simp_rw [h1]
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, h2, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  ring

end Lists

/-! ### Chains, open paths, cycles and weights -/

section Chains

variable {ι : Type*} {G : Type*} {R : Type*} [CommSemiring R]

/-- `ch Q x i a [c₁,…,cₙ] b = Q_i(x_a,x_{c₁}) Q_1(x_{c₁},x_{c₂}) ⋯ Q_1(x_{cₙ},x_b)`. -/
def ch (Q : ℕ → G → G → R) (x : ι → G) : ℕ → ι → List ι → ι → R
  | i, a, [], b => Q i (x a) (x b)
  | i, a, c :: L, b => Q i (x a) (x c) * ch Q x 1 c L b

/-- The open path `Q_1(x_a,x_{c₁}) ⋯ Q_1(x_{cₙ₋₁},x_{cₙ})`. -/
def op (Q : ℕ → G → G → R) (x : ι → G) : ι → List ι → R
  | _, [] => 1
  | a, c :: L => Q 1 (x a) (x c) * op Q x c L

/-- The closed walk through the entries of a list. -/
def cyc (Q : ℕ → G → G → R) (x : ι → G) : List ι → R
  | [] => 0
  | a :: L => ch Q x 1 a L a

theorem ch_nil (Q : ℕ → G → G → R) (x : ι → G) (i : ℕ) (a b : ι) :
    ch Q x i a [] b = Q i (x a) (x b) := rfl

theorem ch_cons (Q : ℕ → G → G → R) (x : ι → G) (i : ℕ) (a c : ι) (L : List ι) (b : ι) :
    ch Q x i a (c :: L) b = Q i (x a) (x c) * ch Q x 1 c L b := rfl

theorem op_nil (Q : ℕ → G → G → R) (x : ι → G) (a : ι) : op Q x a [] = 1 := rfl

theorem op_cons (Q : ℕ → G → G → R) (x : ι → G) (a c : ι) (L : List ι) :
    op Q x a (c :: L) = Q 1 (x a) (x c) * op Q x c L := rfl

theorem cyc_cons (Q : ℕ → G → G → R) (x : ι → G) (a : ι) (L : List ι) :
    cyc Q x (a :: L) = ch Q x 1 a L a := rfl

theorem ch_append (Q : ℕ → G → G → R) (x : ι → G) (i : ℕ) (a : ι) (L1 : List ι) (v : ι)
    (L2 : List ι) (b : ι) :
    ch Q x i a (L1 ++ v :: L2) b = ch Q x i a L1 v * ch Q x 1 v L2 b := by
  induction L1 generalizing i a with
  | nil => rfl
  | cons c L ih => rw [List.cons_append, ch_cons, ch_cons, ih, mul_assoc]

theorem ch_update [DecidableEq ι] (Q : ℕ → G → G → R) (x : ι → G) (v : ι) (y : G) (i : ℕ)
    (a : ι) (L : List ι) (b : ι) (ha : v ≠ a) (hb : v ≠ b) (hL : v ∉ L) :
    ch Q (update x v y) i a L b = ch Q x i a L b := by
  induction L generalizing i a with
  | nil => rw [ch_nil, ch_nil, update_of_ne ha.symm, update_of_ne hb.symm]
  | cons c L ih =>
    have hc : v ≠ c := fun h => hL (by rw [h]; exact List.mem_cons_self)
    have hL' : v ∉ L := fun h => hL (List.mem_cons_of_mem _ h)
    rw [ch_cons, ch_cons, ih 1 c hc hL', update_of_ne ha.symm, update_of_ne hc.symm]

theorem op_update [DecidableEq ι] (Q : ℕ → G → G → R) (x : ι → G) (v : ι) (y : G)
    (a : ι) (L : List ι) (ha : v ≠ a) (hL : v ∉ L) :
    op Q (update x v y) a L = op Q x a L := by
  induction L generalizing a with
  | nil => rfl
  | cons c L ih =>
    have hc : v ≠ c := fun h => hL (by rw [h]; exact List.mem_cons_self)
    have hL' : v ∉ L := fun h => hL (List.mem_cons_of_mem _ h)
    rw [op_cons, op_cons, ih c hc hL', update_of_ne ha.symm, update_of_ne hc.symm]

theorem cyc_update [DecidableEq ι] (Q : ℕ → G → G → R) (x : ι → G) (v : ι) (y : G)
    (J : List ι) (hJ : v ∉ J) : cyc Q (update x v y) J = cyc Q x J := by
  cases J with
  | nil => rfl
  | cons a L =>
    have ha : v ≠ a := fun h => hJ (by rw [h]; exact List.mem_cons_self)
    have hL' : v ∉ L := fun h => hJ (List.mem_cons_of_mem _ h)
    exact ch_update Q x v y 1 a L a ha ha hL'

/-- The weight of a list relative to a list `J`: a factor `M` for every entry that occurs again
    later in the list or lies in `J`. -/
def wt [DecidableEq ι] (M : R) (J : List ι) : List ι → R
  | [] => 1
  | a :: L => (if a ∈ L ∨ a ∈ J then M else 1) * wt M J L

theorem wt_cons [DecidableEq ι] (M : R) (J : List ι) (a : ι) (L : List ι) :
    wt M J (a :: L) = (if a ∈ L ∨ a ∈ J then M else 1) * wt M J L := rfl

omit [CommSemiring R] in
theorem meas2 {α : Type*} [MeasurableSpace α] [MeasurableSpace G] [MeasurableSpace R]
    {Q : ℕ → G → G → R} (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2) (i : ℕ)
    {f g : α → G} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => Q i (f x) (g x) :=
  (hQ i).comp (hf.prodMk hg)

theorem ch_meas [MeasurableSpace G] [MeasurableSpace R] [MeasurableMul₂ R]
    {Q : ℕ → G → G → R} (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (i : ℕ) (a : ι) (L : List ι) (b : ι) : Measurable fun x : ι → G => ch Q x i a L b := by
  induction L generalizing i a with
  | nil => exact meas2 hQ i (measurable_pi_apply a) (measurable_pi_apply b)
  | cons c L ih =>
    exact (meas2 hQ i (measurable_pi_apply a) (measurable_pi_apply c)).mul (ih 1 c)

theorem op_meas [MeasurableSpace G] [MeasurableSpace R] [MeasurableMul₂ R]
    {Q : ℕ → G → G → R} (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (a : ι) (L : List ι) : Measurable fun x : ι → G => op Q x a L := by
  induction L generalizing a with
  | nil => exact measurable_const
  | cons c L ih =>
    exact (meas2 hQ 1 (measurable_pi_apply a) (measurable_pi_apply c)).mul (ih c)

theorem cyc_meas [MeasurableSpace G] [MeasurableSpace R] [MeasurableMul₂ R]
    {Q : ℕ → G → G → R} (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (J : List ι) : Measurable fun x : ι → G => cyc Q x J := by
  cases J with
  | nil => exact measurable_const
  | cons a L => exact ch_meas hQ 1 a L a

end Chains

/-! ### Integration over the product measure, one coordinate at a time -/

section Integrals

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [MeasurableSpace G]
  (ν : Measure G) [IsProbabilityMeasure ν]

/-- Integrate out one coordinate first. -/
theorem lintegral_pi_coord (v : ι) {F : (ι → G) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂Measure.pi (fun _ : ι => ν)
      = ∫⁻ x, ∫⁻ y, F (update x v y) ∂ν ∂Measure.pi (fun _ : ι => ν) := by
  have h1 : (∫⋯∫⁻_{v}, F ∂(fun _ : ι => ν)) = fun x => ∫⁻ y, F (update x v y) ∂ν :=
    lmarginal_singleton F v
  have hg : Measurable fun x : ι → G => ∫⁻ y, F (update x v y) ∂ν := by
    rw [← h1]; exact hF.lmarginal _
  refine lintegral_eq_of_lmarginal_eq {v} hF hg ?_
  rw [h1, lmarginal_singleton]
  funext x
  simp [update_idem]

variable (Q : ℕ → G → G → ℝ≥0∞)

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace G] in
theorem ch_le_op (M : ℝ≥0∞) (hb : ∀ x y, Q 1 x y ≤ M) (x : ι → G) (a : ι) (L : List ι) (b : ι) :
    ch Q x 1 a L b ≤ op Q x a L * M := by
  induction L generalizing a with
  | nil => rw [ch_nil, op_nil, one_mul]; exact hb _ _
  | cons c L ih =>
    rw [ch_cons, op_cons, mul_assoc]
    exact mul_le_mul' le_rfl (ih c)

/-- **Open paths (spanning-tree integration).** -/
theorem op_integral_le (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2) (M : ℝ≥0∞)
    (hM1 : 1 ≤ M) (hb : ∀ x y, Q 1 x y ≤ M) (hmass : ∀ z, ∫⁻ y, Q 1 y z ∂ν = 1)
    (J : List ι) {h : (ι → G) → ℝ≥0∞} (hh : Measurable h)
    (hind : ∀ c, c ∉ J → ∀ x y, h (update x c y) = h x) (a : ι) (L : List ι) :
    ∫⁻ x, op Q x a L * h x ∂Measure.pi (fun _ : ι => ν)
      ≤ wt M J (a :: L) * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν) := by
  induction L generalizing a with
  | nil =>
    have h1 : (1 : ℝ≥0∞) ≤ wt M J [a] := by
      rw [wt_cons]
      show (1 : ℝ≥0∞) ≤ (if a ∈ ([] : List ι) ∨ a ∈ J then M else 1) * 1
      rw [mul_one]
      split_ifs
      · exact hM1
      · exact le_rfl
    simp only [op_nil, one_mul]
    calc ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν)
        = 1 * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν) := (one_mul _).symm
      _ ≤ wt M J [a] * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν) := mul_le_mul' h1 le_rfl
  | cons c L ih =>
    have hm : Measurable fun x : ι → G => op Q x c L * h x := (op_meas hQ c L).mul hh
    by_cases hcase : a ∈ c :: L ∨ a ∈ J
    · calc ∫⁻ x, op Q x a (c :: L) * h x ∂Measure.pi (fun _ : ι => ν)
          ≤ ∫⁻ x, M * (op Q x c L * h x) ∂Measure.pi (fun _ : ι => ν) :=
            lintegral_mono fun x => by
              rw [op_cons, mul_assoc]
              exact mul_le_mul' (hb _ _) le_rfl
        _ = M * ∫⁻ x, op Q x c L * h x ∂Measure.pi (fun _ : ι => ν) := lintegral_const_mul _ hm
        _ ≤ M * (wt M J (c :: L) * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν)) :=
            mul_le_mul' le_rfl (ih c)
        _ = wt M J (a :: c :: L) * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν) := by
            rw [wt_cons M J a, if_pos hcase, mul_assoc]
    · have hacL : a ∉ c :: L := fun h' => hcase (Or.inl h')
      have haJ : a ∉ J := fun h' => hcase (Or.inr h')
      have hac : a ≠ c := fun h' => hacL (by rw [h']; exact List.mem_cons_self)
      have haL : a ∉ L := fun h' => hacL (List.mem_cons_of_mem _ h')
      have hF : Measurable fun x : ι → G => op Q x a (c :: L) * h x :=
        (op_meas hQ a (c :: L)).mul hh
      rw [lintegral_pi_coord ν a hF]
      have inner : ∀ x : ι → G,
          ∫⁻ y, op Q (update x a y) a (c :: L) * h (update x a y) ∂ν = op Q x c L * h x := by
        intro x
        have e : ∀ y, op Q (update x a y) a (c :: L) * h (update x a y)
            = Q 1 y (x c) * (op Q x c L * h x) := by
          intro y
          rw [hind a haJ x y, op_cons, update_self, update_of_ne (Ne.symm hac),
            op_update Q x a y c L hac haL, mul_assoc]
        simp_rw [e]
        have hmy : Measurable fun y : G => Q 1 y (x c) := meas2 hQ 1 measurable_id measurable_const
        rw [lintegral_mul_const _ hmy, hmass, one_mul]
      simp_rw [inner]
      calc ∫⁻ x, op Q x c L * h x ∂Measure.pi (fun _ : ι => ν)
          ≤ wt M J (c :: L) * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν) := ih c
        _ = wt M J (a :: c :: L) * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν) := by
            rw [wt_cons M J a, if_neg hcase, one_mul]

omit [Fintype ι] [IsProbabilityMeasure ν] in
/-- Integrating out the first inner vertex of a chain merges two steps (semigroup). -/
theorem ch_marginal (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (hsemi : ∀ i j x z, 1 ≤ i → 1 ≤ j → ∫⁻ y, Q i x y * Q j y z ∂ν = Q (i + j) x z)
    (x : ι → G) (i : ℕ) (hi : 1 ≤ i) (a c : ι) (L : List ι) (b : ι) (hca : c ≠ a) (hcb : c ≠ b)
    (hcL : c ∉ L) :
    ∫⁻ y, ch Q (update x c y) i a (c :: L) b ∂ν = ch Q x (i + 1) a L b := by
  cases L with
  | nil =>
    have e : ∀ y, ch Q (update x c y) i a [c] b = Q i (x a) y * Q 1 y (x b) := by
      intro y
      rw [ch_cons, ch_nil, update_self, update_of_ne hca.symm, update_of_ne hcb.symm]
    simp_rw [e]
    exact hsemi i 1 _ _ hi le_rfl
  | cons c' L' =>
    have hcc' : c ≠ c' := fun h => hcL (by rw [h]; exact List.mem_cons_self)
    have hcL' : c ∉ L' := fun h => hcL (List.mem_cons_of_mem _ h)
    have e : ∀ y, ch Q (update x c y) i a (c :: c' :: L') b
        = Q i (x a) y * Q 1 y (x c') * ch Q x 1 c' L' b := by
      intro y
      rw [ch_cons, ch_cons, update_self, update_of_ne hca.symm, update_of_ne hcc'.symm,
        ch_update Q x c y 1 c' L' b hcc' hcb hcL', mul_assoc]
    simp_rw [e]
    have hmy : Measurable fun y : G => Q i (x a) y * Q 1 y (x c') :=
      (meas2 hQ i measurable_const measurable_id).mul (meas2 hQ 1 measurable_id measurable_const)
    rw [lintegral_mul_const _ hmy, hsemi i 1 _ _ hi le_rfl, ch_cons]

/-- **A chain through distinct vertices collapses to one kernel**, next to a factor that does
    not depend on the inner vertices. -/
theorem ch_integral (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (hsemi : ∀ i j x z, 1 ≤ i → 1 ≤ j → ∫⁻ y, Q i x y * Q j y z ∂ν = Q (i + j) x z)
    {h : (ι → G) → ℝ≥0∞} (hh : Measurable h) (L : List ι) (hnd : L.Nodup) (i : ℕ) (hi : 1 ≤ i)
    (a b : ι) (ha : a ∉ L) (hb : b ∉ L) (hind : ∀ c ∈ L, ∀ x y, h (update x c y) = h x) :
    ∫⁻ x, ch Q x i a L b * h x ∂Measure.pi (fun _ : ι => ν)
      = ∫⁻ x, Q (i + L.length) (x a) (x b) * h x ∂Measure.pi (fun _ : ι => ν) := by
  induction L generalizing i with
  | nil => rfl
  | cons c L ih =>
    have hcL : c ∉ L := (List.nodup_cons.mp hnd).1
    have hca : c ≠ a := fun e => ha (by rw [← e]; exact List.mem_cons_self)
    have hcb : c ≠ b := fun e => hb (by rw [← e]; exact List.mem_cons_self)
    have hF : Measurable fun x : ι → G => ch Q x i a (c :: L) b * h x :=
      (ch_meas hQ i a (c :: L) b).mul hh
    rw [lintegral_pi_coord ν c hF]
    have inner : ∀ x : ι → G,
        ∫⁻ y, ch Q (update x c y) i a (c :: L) b * h (update x c y) ∂ν
          = ch Q x (i + 1) a L b * h x := by
      intro x
      simp_rw [hind c List.mem_cons_self x]
      have hmy : Measurable fun y : G => ch Q (update x c y) i a (c :: L) b :=
        (ch_meas hQ i a (c :: L) b).comp (measurable_update x)
      rw [lintegral_mul_const _ hmy,
        ch_marginal ν Q hQ hsemi x i hi a c L b hca hcb hcL]
    simp_rw [inner]
    rw [ih (List.nodup_cons.mp hnd).2 (i + 1) (by omega)
      (fun hm => ha (List.mem_cons_of_mem _ hm)) (fun hm => hb (List.mem_cons_of_mem _ hm))
      (fun c' hc' => hind c' (List.mem_cons_of_mem _ hc'))]
    have hlen : i + 1 + L.length = i + (c :: L).length := by simp; omega
    rw [hlen]

end Integrals

section Integrals2

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [MeasurableSpace G]
  (ν : Measure G) [IsProbabilityMeasure ν] (Q : ℕ → G → G → ℝ≥0∞)

/-- **Degeneracy of the cycle.** A closed walk through distinct vertices, next to a factor `h`
    that depends on at most one of its vertices, integrates to `m_k ∫ h`. -/
theorem cyc_integral_spect (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (hsemi : ∀ i j x z, 1 ≤ i → 1 ≤ j → ∫⁻ y, Q i x y * Q j y z ∂ν = Q (i + j) x z)
    (mE : ℕ → ℝ≥0∞) (hdiag : ∀ i x, 1 ≤ i → Q i x x = mE i)
    {h : (ι → G) → ℝ≥0∞} (hh : Measurable h) (a : ι) (L : List ι) (hnd : (a :: L).Nodup)
    (v : ι) (hv : v ∈ a :: L)
    (hind : ∀ c ∈ a :: L, c ≠ v → ∀ x y, h (update x c y) = h x) :
    ∫⁻ x, ch Q x 1 a L a * h x ∂Measure.pi (fun _ : ι => ν)
      = mE (L.length + 1) * ∫⁻ x, h x ∂Measure.pi (fun _ : ι => ν) := by
  have haL : a ∉ L := (List.nodup_cons.mp hnd).1
  have hL : L.Nodup := (List.nodup_cons.mp hnd).2
  rcases List.mem_cons.mp hv with hva | hvL
  · rw [ch_integral ν Q hQ hsemi hh L hL 1 le_rfl a a haL haL
      (fun c hc => hind c (List.mem_cons_of_mem _ hc)
        (fun e => haL (by rw [← hva, ← e]; exact hc)))]
    simp_rw [hdiag _ _ (by omega : 1 ≤ 1 + L.length)]
    rw [lintegral_const_mul _ hh, add_comm]
  · obtain ⟨L1, L2, rfl⟩ := List.append_of_mem hvL
    have hav : a ≠ v := fun e => haL (by rw [e]; exact hvL)
    obtain ⟨hL1, hvL2nd, hdisj⟩ := List.nodup_append.mp hL
    have hvL2 : v ∉ L2 := (List.nodup_cons.mp hvL2nd).1
    have hL2 : L2.Nodup := (List.nodup_cons.mp hvL2nd).2
    have hvL1 : v ∉ L1 := fun hm => hdisj v hm v List.mem_cons_self rfl
    have haL1 : a ∉ L1 := fun hm => haL (List.mem_append_left _ hm)
    have haL2 : a ∉ L2 :=
      fun hm => haL (List.mem_append_right _ (List.mem_cons_of_mem _ hm))
    have hL21 : ∀ c ∈ L2, c ∉ L1 :=
      fun c hc hm => hdisj c hm c (List.mem_cons_of_mem _ hc) rfl
    have hmemL1 : ∀ c ∈ L1, c ∈ a :: (L1 ++ v :: L2) :=
      fun c hc => List.mem_cons_of_mem _ (List.mem_append_left _ hc)
    have hmemL2 : ∀ c ∈ L2, c ∈ a :: (L1 ++ v :: L2) :=
      fun c hc => List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
    have hneL1 : ∀ c ∈ L1, c ≠ v := fun c hc e => hvL1 (by rw [← e]; exact hc)
    have hneL2 : ∀ c ∈ L2, c ≠ v := fun c hc e => hvL2 (by rw [← e]; exact hc)
    have hneaL1 : ∀ c ∈ L1, c ≠ a := fun c hc e => haL1 (by rw [← e]; exact hc)
    have hneaL2 : ∀ c ∈ L2, c ≠ a := fun c hc e => haL2 (by rw [← e]; exact hc)
    -- step 1: integrate out `L2`
    have s1 : ∀ x : ι → G, ch Q x 1 a (L1 ++ v :: L2) a * h x
        = ch Q x 1 v L2 a * (ch Q x 1 a L1 v * h x) := by
      intro x; rw [ch_append]; ring
    simp_rw [s1]
    have hh1 : Measurable fun x : ι → G => ch Q x 1 a L1 v * h x := (ch_meas hQ 1 a L1 v).mul hh
    rw [ch_integral ν Q hQ hsemi hh1 L2 hL2 1 le_rfl v a hvL2 haL2
      (fun c hc x y => by
        rw [ch_update Q x c y 1 a L1 v (hneaL2 c hc) (hneL2 c hc) (hL21 c hc),
          hind c (hmemL2 c hc) (hneL2 c hc) x y])]
    -- step 2: integrate out `L1`
    have s2 : ∀ x : ι → G, Q (1 + L2.length) (x v) (x a) * (ch Q x 1 a L1 v * h x)
        = ch Q x 1 a L1 v * (Q (1 + L2.length) (x v) (x a) * h x) := by
      intro x; ring
    simp_rw [s2]
    have hh2 : Measurable fun x : ι → G => Q (1 + L2.length) (x v) (x a) * h x :=
      (meas2 hQ _ (measurable_pi_apply v) (measurable_pi_apply a)).mul hh
    rw [ch_integral ν Q hQ hsemi hh2 L1 hL1 1 le_rfl a v haL1 hvL1
      (fun c hc x y => by
        rw [update_of_ne (hneL1 c hc).symm, update_of_ne (hneaL1 c hc).symm,
          hind c (hmemL1 c hc) (hneL1 c hc) x y])]
    -- step 3: integrate out `a`
    have hF : Measurable fun x : ι → G =>
        Q (1 + L1.length) (x a) (x v) * (Q (1 + L2.length) (x v) (x a) * h x) :=
      (meas2 hQ _ (measurable_pi_apply a) (measurable_pi_apply v)).mul hh2
    rw [lintegral_pi_coord ν a hF]
    have inner : ∀ x : ι → G,
        ∫⁻ y, Q (1 + L1.length) (update x a y a) (update x a y v)
            * (Q (1 + L2.length) (update x a y v) (update x a y a) * h (update x a y)) ∂ν
          = mE ((L1 ++ v :: L2).length + 1) * h x := by
      intro x
      have e : ∀ y, Q (1 + L1.length) (update x a y a) (update x a y v)
            * (Q (1 + L2.length) (update x a y v) (update x a y a) * h (update x a y))
          = Q (1 + L2.length) (x v) y * Q (1 + L1.length) y (x v) * h x := by
        intro y
        rw [update_self, update_of_ne hav.symm, hind a List.mem_cons_self hav x y]
        ring
      simp_rw [e]
      have hmy : Measurable fun y : G => Q (1 + L2.length) (x v) y * Q (1 + L1.length) y (x v) :=
        (meas2 hQ _ measurable_const measurable_id).mul (meas2 hQ _ measurable_id measurable_const)
      rw [lintegral_mul_const _ hmy, hsemi _ _ _ _ (by omega) (by omega),
        hdiag _ _ (by omega)]
      have hlen : 1 + L2.length + (1 + L1.length) = (L1 ++ v :: L2).length + 1 := by
        simp; omega
      rw [hlen]
    simp_rw [inner]
    rw [lintegral_const_mul _ hh]

/-- A closed walk through distinct vertices has expectation `m_k`. -/
theorem cyc_integral_nodup (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (hsemi : ∀ i j x z, 1 ≤ i → 1 ≤ j → ∫⁻ y, Q i x y * Q j y z ∂ν = Q (i + j) x z)
    (mE : ℕ → ℝ≥0∞) (hdiag : ∀ i x, 1 ≤ i → Q i x x = mE i)
    (a : ι) (L : List ι) (hnd : (a :: L).Nodup) :
    ∫⁻ x, cyc Q x (a :: L) ∂Measure.pi (fun _ : ι => ν) = mE (L.length + 1) := by
  have h := cyc_integral_spect ν Q hQ hsemi mE hdiag (h := fun _ => 1) measurable_const a L hnd
    a List.mem_cons_self (fun _ _ _ _ _ => rfl)
  simpa [cyc_cons] using h

/-- Every closed walk has expectation at most `M` times its weight. -/
theorem cyc_integral_le (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2) (M : ℝ≥0∞)
    (hM1 : 1 ≤ M) (hb : ∀ x y, Q 1 x y ≤ M) (hmass : ∀ z, ∫⁻ y, Q 1 y z ∂ν = 1)
    (a : ι) (L : List ι) :
    ∫⁻ x, cyc Q x (a :: L) ∂Measure.pi (fun _ : ι => ν) ≤ M * wt M [] (a :: L) := by
  have h := op_integral_le ν Q hQ M hM1 hb hmass [] (h := fun _ => 1) measurable_const
    (fun _ _ _ _ => rfl) a L
  calc ∫⁻ x, cyc Q x (a :: L) ∂Measure.pi (fun _ : ι => ν)
      ≤ ∫⁻ x, M * (op Q x a L * 1) ∂Measure.pi (fun _ : ι => ν) :=
        lintegral_mono fun x => by
          rw [cyc_cons, mul_one, mul_comm]; exact ch_le_op Q M hb x a L a
    _ = M * ∫⁻ x, op Q x a L * 1 ∂Measure.pi (fun _ : ι => ν) :=
        lintegral_const_mul _ ((op_meas hQ a L).mul measurable_const)
    _ ≤ M * (wt M [] (a :: L) * ∫⁻ _, 1 ∂Measure.pi (fun _ : ι => ν)) := mul_le_mul' le_rfl h
    _ = M * wt M [] (a :: L) := by simp

/-- Two closed walks: the product has expectation at most `M² wt_J(I) wt(J)`. -/
theorem pair_integral_le (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2) (M : ℝ≥0∞)
    (hM1 : 1 ≤ M) (hb : ∀ x y, Q 1 x y ≤ M) (hmass : ∀ z, ∫⁻ y, Q 1 y z ∂ν = 1)
    (a : ι) (L : List ι) (a' : ι) (L' : List ι) :
    ∫⁻ x, cyc Q x (a :: L) * cyc Q x (a' :: L') ∂Measure.pi (fun _ : ι => ν)
      ≤ M * (wt M (a' :: L') (a :: L) * (M * wt M [] (a' :: L'))) := by
  have hJm : Measurable fun x : ι → G => cyc Q x (a' :: L') := cyc_meas hQ _
  have h := op_integral_le ν Q hQ M hM1 hb hmass (a' :: L') hJm
    (fun c hc x y => cyc_update Q x c y _ hc) a L
  calc ∫⁻ x, cyc Q x (a :: L) * cyc Q x (a' :: L') ∂Measure.pi (fun _ : ι => ν)
      ≤ ∫⁻ x, M * (op Q x a L * cyc Q x (a' :: L')) ∂Measure.pi (fun _ : ι => ν) :=
        lintegral_mono fun x => by
          rw [cyc_cons Q x a L, ← mul_assoc, mul_comm M]
          exact mul_le_mul' (ch_le_op Q M hb x a L a) le_rfl
    _ = M * ∫⁻ x, op Q x a L * cyc Q x (a' :: L') ∂Measure.pi (fun _ : ι => ν) :=
        lintegral_const_mul _ ((op_meas hQ a L).mul hJm)
    _ ≤ M * (wt M (a' :: L') (a :: L) * ∫⁻ x, cyc Q x (a' :: L') ∂Measure.pi (fun _ : ι => ν)) :=
        mul_le_mul' le_rfl h
    _ ≤ M * (wt M (a' :: L') (a :: L) * (M * wt M [] (a' :: L'))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl (cyc_integral_le ν Q hQ M hM1 hb hmass a' L'))

/-- Two closed walks through distinct vertices with at most one common vertex are uncorrelated. -/
theorem pair_integral_eq (hQ : ∀ i, Measurable fun p : G × G => Q i p.1 p.2)
    (hsemi : ∀ i j x z, 1 ≤ i → 1 ≤ j → ∫⁻ y, Q i x y * Q j y z ∂ν = Q (i + j) x z)
    (mE : ℕ → ℝ≥0∞) (hdiag : ∀ i x, 1 ≤ i → Q i x x = mE i)
    (a : ι) (L : List ι) (hnd : (a :: L).Nodup) (a' : ι) (L' : List ι)
    (hnd' : (a' :: L').Nodup) (v : ι) (hv : v ∈ a :: L)
    (hcommon : ∀ c ∈ a :: L, c ∈ a' :: L' → c = v) :
    ∫⁻ x, cyc Q x (a :: L) * cyc Q x (a' :: L') ∂Measure.pi (fun _ : ι => ν)
      = mE (L.length + 1) * mE (L'.length + 1) := by
  have hJm : Measurable fun x : ι → G => cyc Q x (a' :: L') := cyc_meas hQ _
  have h := cyc_integral_spect ν Q hQ hsemi mE hdiag hJm a L hnd v hv
    (fun c hc hcv x y => cyc_update Q x c y _ (fun hcJ => hcv (hcommon c hc hcJ)))
  rw [← cyc_integral_nodup ν Q hQ hsemi mE hdiag a' L' hnd']
  exact h

end Integrals2

/-! ### Real kernels: the hypotheses and the moments of single closed walks and of pairs -/

section RealKernels

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [MeasurableSpace G]
  {ν : Measure G} [IsProbabilityMeasure ν] {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

/-- HYPOTHESES on a family of kernels `q_i(x,y)` (`q_1` is the kernel of the walk, `q_i` its
    `i`-fold convolution): measurable, nonnegative, `q_1 ≤ M`, mass one, semigroup, constant
    diagonal `q_i(x,x) = m_i`, `1 ≤ M`, `0 ≤ m_i ≤ M` (for `i ≥ 1`). -/
structure RK (ν : Measure G) (q : ℕ → G → G → ℝ) (M : ℝ) (m : ℕ → ℝ) : Prop where
  meas : ∀ i, Measurable fun p : G × G => q i p.1 p.2
  nonneg : ∀ i x y, 0 ≤ q i x y
  bound : ∀ x y, q 1 x y ≤ M
  mass : ∀ z, ∫⁻ y, ENNReal.ofReal (q 1 y z) ∂ν = 1
  semi : ∀ i j x z, 1 ≤ i → 1 ≤ j →
    ∫⁻ y, ENNReal.ofReal (q i x y) * ENNReal.ofReal (q j y z) ∂ν = ENNReal.ofReal (q (i + j) x z)
  diag : ∀ i x, 1 ≤ i → q i x x = m i
  M_ge : 1 ≤ M
  m_nonneg : ∀ i, 1 ≤ i → 0 ≤ m i
  m_le : ∀ i, 1 ≤ i → m i ≤ M

/-- The kernels with values in `ℝ≥0∞`. -/
noncomputable def QE (q : ℕ → G → G → ℝ) : ℕ → G → G → ℝ≥0∞ :=
  fun i x y => ENNReal.ofReal (q i x y)

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace G] in
theorem ch_nonneg (hq : ∀ i x y, 0 ≤ q i x y) (x : ι → G) (i : ℕ) (a : ι) (L : List ι) (b : ι) :
    0 ≤ ch q x i a L b := by
  induction L generalizing i a with
  | nil => exact hq _ _ _
  | cons c L ih => rw [ch_cons]; exact mul_nonneg (hq _ _ _) (ih 1 c)

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace G] in
theorem cyc_nonneg (hq : ∀ i x y, 0 ≤ q i x y) (x : ι → G) (J : List ι) : 0 ≤ cyc q x J := by
  cases J with
  | nil => exact le_rfl
  | cons a L => exact ch_nonneg hq x 1 a L a

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace G] in
theorem ofReal_ch (hq : ∀ i x y, 0 ≤ q i x y) (x : ι → G) (i : ℕ) (a : ι) (L : List ι) (b : ι) :
    ENNReal.ofReal (ch q x i a L b) = ch (QE q) x i a L b := by
  induction L generalizing i a with
  | nil => rfl
  | cons c L ih =>
    rw [ch_cons, ch_cons, ENNReal.ofReal_mul (hq _ _ _), ih]
    rfl

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace G] in
theorem ofReal_cyc (hq : ∀ i x y, 0 ≤ q i x y) (x : ι → G) (J : List ι) :
    ENNReal.ofReal (cyc q x J) = cyc (QE q) x J := by
  cases J with
  | nil => exact ENNReal.ofReal_zero
  | cons a L => exact ofReal_ch hq x 1 a L a

omit [Fintype ι] in
theorem wt_nonneg (hM : 0 ≤ M) (J L : List ι) : 0 ≤ wt M J L := by
  induction L with
  | nil => exact zero_le_one
  | cons a L ih =>
    rw [wt_cons]
    refine mul_nonneg ?_ ih
    split_ifs
    · exact hM
    · exact zero_le_one

omit [Fintype ι] in
theorem ofReal_wt (hM : 0 ≤ M) (J L : List ι) :
    ENNReal.ofReal (wt M J L) = wt (ENNReal.ofReal M) J L := by
  induction L with
  | nil => exact ENNReal.ofReal_one
  | cons a L ih =>
    have h0 : (0 : ℝ) ≤ (if a ∈ L ∨ a ∈ J then M else 1) := by
      split_ifs
      · exact hM
      · exact zero_le_one
    rw [wt_cons, wt_cons, ENNReal.ofReal_mul h0, ih]
    congr 1
    split_ifs
    · rfl
    · exact ENNReal.ofReal_one

omit [Fintype ι] in
theorem wt_nodup (L : List ι) (h : L.Nodup) : wt M [] L = 1 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have haL : a ∉ L := (List.nodup_cons.mp h).1
    have hc : ¬ (a ∈ L ∨ a ∈ ([] : List ι)) := by simp [haL]
    rw [wt_cons, if_neg hc, one_mul, ih (List.nodup_cons.mp h).2]

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace G] in
theorem ch_le_pow (hq : ∀ i x y, 0 ≤ q i x y) (hb : ∀ x y, q 1 x y ≤ M) (x : ι → G) (a : ι)
    (L : List ι) (b : ι) : ch q x 1 a L b ≤ M ^ (L.length + 1) := by
  induction L generalizing a with
  | nil => simpa [ch_nil] using hb (x a) (x b)
  | cons c L ih =>
    rw [ch_cons, List.length_cons, pow_succ' M (L.length + 1)]
    exact mul_le_mul (hb _ _) (ih c) (ch_nonneg hq x 1 c L b) ((hq 1 (x a) (x c)).trans (hb _ _))

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace G] in
theorem cyc_abs_le (hq : ∀ i x y, 0 ≤ q i x y) (hb : ∀ x y, q 1 x y ≤ M) (_hM : 1 ≤ M)
    (x : ι → G) (J : List ι) : |cyc q x J| ≤ M ^ J.length := by
  rw [abs_of_nonneg (cyc_nonneg hq x J)]
  cases J with
  | nil => simp [cyc]
  | cons a L => exact ch_le_pow hq hb x a L a

theorem integral_le_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal C) : ∫ x, f x ∂μ ≤ C := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
    hfm.aestronglyMeasurable]
  calc (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = C := ENNReal.toReal_ofReal hC

theorem integral_eq_of_lintegral_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal C) : ∫ x, f x ∂μ = C := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0)
    hfm.aestronglyMeasurable, h, ENNReal.toReal_ofReal hC]

namespace RK

variable (S : RK ν q M m)
include S

omit [IsProbabilityMeasure ν] in
theorem measE (i : ℕ) : Measurable fun p : G × G => QE q i p.1 p.2 :=
  ENNReal.measurable_ofReal.comp (S.meas i)

omit [IsProbabilityMeasure ν] in
theorem M_nonneg : 0 ≤ M := zero_le_one.trans S.M_ge

omit [IsProbabilityMeasure ν] in
theorem M1E : (1 : ℝ≥0∞) ≤ ENNReal.ofReal M := by
  rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal S.M_ge

omit [IsProbabilityMeasure ν] in
theorem boundE (x y : G) : QE q 1 x y ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (S.bound x y)

omit [IsProbabilityMeasure ν] in
theorem diagE (i : ℕ) (x : G) (hi : 1 ≤ i) : QE q i x x = ENNReal.ofReal (m i) := by
  show ENNReal.ofReal (q i x x) = _
  rw [S.diag i x hi]

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure ν] in
theorem cyc_measurable (J : List ι) : Measurable fun x : ι → G => cyc q x J := cyc_meas S.meas J

omit [DecidableEq ι] in
theorem cyc_integrable (J : List ι) :
    Integrable (fun x : ι → G => cyc q x J) (Measure.pi fun _ : ι => ν) :=
  Integrable.of_bound (S.cyc_measurable J).aestronglyMeasurable (M ^ J.length)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact cyc_abs_le S.nonneg S.bound S.M_ge x J)

omit [DecidableEq ι] in
theorem pair_integrable (I J : List ι) :
    Integrable (fun x : ι → G => cyc q x I * cyc q x J) (Measure.pi fun _ : ι => ν) :=
  Integrable.of_bound ((S.cyc_measurable I).mul (S.cyc_measurable J)).aestronglyMeasurable
    (M ^ I.length * M ^ J.length)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (cyc_abs_le S.nonneg S.bound S.M_ge x I)
        (cyc_abs_le S.nonneg S.bound S.M_ge x J) (abs_nonneg _)
        (pow_nonneg S.M_nonneg _))

/-- Stage (1): a closed walk through distinct points has expectation `m_k`. -/
theorem int_nodup (a : ι) (L : List ι) (hnd : (a :: L).Nodup) :
    ∫ x, cyc q x (a :: L) ∂Measure.pi (fun _ : ι => ν) = m (L.length + 1) := by
  refine integral_eq_of_lintegral_eq (fun x => cyc_nonneg S.nonneg x _) (S.cyc_measurable _)
    (S.m_nonneg _ (by omega)) ?_
  simp_rw [ofReal_cyc S.nonneg]
  exact cyc_integral_nodup ν (QE q) S.measE S.semi (fun i => ENNReal.ofReal (m i)) S.diagE a L hnd

/-- Stage (2): every closed walk has expectation at most `M` times its weight. -/
theorem int_le (a : ι) (L : List ι) :
    ∫ x, cyc q x (a :: L) ∂Measure.pi (fun _ : ι => ν) ≤ M * wt M [] (a :: L) := by
  refine integral_le_of_lintegral_le (fun x => cyc_nonneg S.nonneg x _) (S.cyc_measurable _)
    (mul_nonneg S.M_nonneg (wt_nonneg S.M_nonneg _ _)) ?_
  simp_rw [ofReal_cyc S.nonneg]
  rw [ENNReal.ofReal_mul S.M_nonneg, ofReal_wt S.M_nonneg]
  exact cyc_integral_le ν (QE q) S.measE _ S.M1E S.boundE S.mass a L

theorem pair_le (a : ι) (L : List ι) (a' : ι) (L' : List ι) :
    ∫ x, cyc q x (a :: L) * cyc q x (a' :: L') ∂Measure.pi (fun _ : ι => ν)
      ≤ M * (wt M (a' :: L') (a :: L) * (M * wt M [] (a' :: L'))) := by
  have hM := S.M_nonneg
  refine integral_le_of_lintegral_le
    (fun x => mul_nonneg (cyc_nonneg S.nonneg x _) (cyc_nonneg S.nonneg x _))
    ((S.cyc_measurable _).mul (S.cyc_measurable _))
    (mul_nonneg hM (mul_nonneg (wt_nonneg hM _ _) (mul_nonneg hM (wt_nonneg hM _ _)))) ?_
  simp_rw [ENNReal.ofReal_mul (cyc_nonneg S.nonneg _ _), ofReal_cyc S.nonneg]
  rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_mul (wt_nonneg hM _ _), ENNReal.ofReal_mul hM,
    ofReal_wt hM, ofReal_wt hM]
  exact pair_integral_le ν (QE q) S.measE _ S.M1E S.boundE S.mass a L a' L'

theorem pair_eq (a : ι) (L : List ι) (hnd : (a :: L).Nodup) (a' : ι) (L' : List ι)
    (hnd' : (a' :: L').Nodup) (v : ι) (hv : v ∈ a :: L)
    (hcommon : ∀ c ∈ a :: L, c ∈ a' :: L' → c = v) :
    ∫ x, cyc q x (a :: L) * cyc q x (a' :: L') ∂Measure.pi (fun _ : ι => ν)
      = m (L.length + 1) * m (L'.length + 1) := by
  refine integral_eq_of_lintegral_eq
    (fun x => mul_nonneg (cyc_nonneg S.nonneg x _) (cyc_nonneg S.nonneg x _))
    ((S.cyc_measurable _).mul (S.cyc_measurable _))
    (mul_nonneg (S.m_nonneg _ (by omega)) (S.m_nonneg _ (by omega))) ?_
  simp_rw [ENNReal.ofReal_mul (cyc_nonneg S.nonneg _ _), ofReal_cyc S.nonneg]
  rw [ENNReal.ofReal_mul (S.m_nonneg _ (by omega))]
  exact pair_integral_eq ν (QE q) S.measE S.semi (fun i => ENNReal.ofReal (m i)) S.diagE a L hnd
    a' L' hnd' v hv hcommon

end RK

end RealKernels

/-! ### Counting: weighted sums over the lists of a fixed length -/

section Counting

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of lists of length `n` with distinct entries, as a real number. -/
noncomputable def aN (ι : Type*) [Fintype ι] [DecidableEq ι] (n : ℕ) : ℝ :=
  ∑ I ∈ LL ι n, if I.Nodup then (1 : ℝ) else 0

theorem aN_nonneg (n : ℕ) : 0 ≤ aN ι n :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem aN_zero : aN ι 0 = 1 := by
  unfold aN
  rw [show LL ι 0 = {[]} from rfl, Finset.sum_singleton]
  simp

theorem aN_succ (n : ℕ) : aN ι (n + 1) = ((Fintype.card ι : ℝ) - n) * aN ι n := by
  unfold aN
  rw [sum_LL_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun L hL => ?_
  have hlen := mem_LL.mp hL
  by_cases hnd : L.Nodup
  · have h1 : ∀ a : ι, (if (a :: L).Nodup then (1 : ℝ) else 0) = if a ∈ L then 0 else 1 := by
      intro a
      by_cases ha : a ∈ L <;> simp [List.nodup_cons, ha, hnd]
    simp_rw [h1]
    rw [sum_ite_mem, if_pos hnd, List.toFinset_card_of_nodup hnd, hlen]
    ring
  · have h1 : ∀ a : ι, (if (a :: L).Nodup then (1 : ℝ) else 0) = 0 := by
      intro a
      rw [if_neg]
      intro h
      exact hnd (List.nodup_cons.mp h).2
    simp_rw [h1]
    simp [hnd]

/-- `N^n (1 - n²/(2N)) ≤ #{distinct lists} ≤ N^n`, written without division. -/
theorem aN_bounds (n : ℕ) (hn : n ≤ Fintype.card ι) :
    aN ι n ≤ (Fintype.card ι : ℝ) ^ n ∧
      (2 * (Fintype.card ι : ℝ) - (n : ℝ) ^ 2) * (Fintype.card ι : ℝ) ^ n
        ≤ 2 * (Fintype.card ι : ℝ) * aN ι n := by
  induction n with
  | zero => simp [aN_zero]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hNn : (n : ℝ) + 1 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have ha := aN_nonneg (ι := ι) n
    have ht : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ n := pow_nonneg (Nat.cast_nonneg _) n
    rw [aN_succ, pow_succ]
    generalize (Fintype.card ι : ℝ) = N at *
    generalize aN ι n = a at *
    generalize N ^ n = t at *
    push_cast
    have hN0 : 0 ≤ N := by linarith
    constructor
    · have h1 : n * a ≥ 0 := mul_nonneg hn0 ha
      have h2 : N * a ≤ N * t := mul_le_mul_of_nonneg_left ih1 hN0
      linarith
    · have h1 : (N - n) * ((2 * N - (n : ℝ) ^ 2) * t) ≤ (N - n) * (2 * N * a) :=
        mul_le_mul_of_nonneg_left ih2 (by linarith)
      have h2 : 0 ≤ ((n : ℝ) ^ 3 + N) * t := mul_nonneg (by positivity) ht
      linarith

theorem card_LL (n : ℕ) : ∑ _I ∈ LL ι n, (1 : ℝ) = (Fintype.card ι : ℝ) ^ n := by
  induction n with
  | zero => simp [LL]
  | succ n ih =>
    rw [sum_LL_succ, pow_succ, ← ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun L _ => ?_
    simp

/-- The sum of the weights `wt M []` over all lists of length `n`. -/
noncomputable def bN (ι : Type*) [Fintype ι] [DecidableEq ι] (M : ℝ) (n : ℕ) : ℝ :=
  ∑ I ∈ LL ι n, wt M [] I

theorem bN_nonneg {M : ℝ} (hM : 0 ≤ M) (n : ℕ) : 0 ≤ bN ι M n :=
  Finset.sum_nonneg fun _ _ => wt_nonneg hM _ _

theorem bN_zero (M : ℝ) : bN ι M 0 = 1 := by simp [bN, LL, wt]

theorem bN_succ_le {M : ℝ} (hM : 1 ≤ M) (n : ℕ) :
    bN ι M (n + 1) ≤ ((Fintype.card ι : ℝ) + n * (M - 1)) * bN ι M n := by
  unfold bN
  rw [sum_LL_succ, Finset.mul_sum]
  refine Finset.sum_le_sum fun L hL => ?_
  have hlen := mem_LL.mp hL
  have h1 : ∀ a : ι, wt M [] (a :: L) = (if a ∈ L then M else 1) * wt M [] L := by
    intro a
    rw [wt_cons]
    simp
  simp_rw [h1]
  rw [← Finset.sum_mul, sum_ite_mem]
  refine mul_le_mul_of_nonneg_right ?_ (wt_nonneg (by linarith) _ _)
  have hc : (L.toFinset.card : ℝ) ≤ n := by
    have := List.toFinset_card_le L
    rw [hlen] at this
    exact_mod_cast this
  have h2 : (L.toFinset.card : ℝ) * (M - 1) ≤ n * (M - 1) :=
    mul_le_mul_of_nonneg_right hc (by linarith)
  linarith

/-- `∑ wt ≤ N^n (1 + n²(M-1)/N)` as long as `n²(M-1) ≤ N`, written without division. -/
theorem bN_bound {M : ℝ} (hM : 1 ≤ M) (n : ℕ)
    (h : (n : ℝ) ^ 2 * (M - 1) ≤ (Fintype.card ι : ℝ)) :
    (Fintype.card ι : ℝ) * bN ι M n
      ≤ ((Fintype.card ι : ℝ) + (n : ℝ) ^ 2 * (M - 1)) * (Fintype.card ι : ℝ) ^ n := by
  induction n with
  | zero => simp [bN_zero]
  | succ n ih =>
    have hu : 0 ≤ M - 1 := by linarith
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast at h
    have hn : (n : ℝ) ^ 2 * (M - 1) ≤ (Fintype.card ι : ℝ) := by nlinarith
    have ih' := ih hn
    have hb := bN_nonneg (ι := ι) (by linarith : 0 ≤ M) n
    have hb' := bN_succ_le (ι := ι) hM n
    have ht : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ n := pow_nonneg (Nat.cast_nonneg _) n
    have hN0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    rw [pow_succ (Fintype.card ι : ℝ) n]
    push_cast
    generalize (Fintype.card ι : ℝ) = N at *
    generalize bN ι M n = b at *
    generalize bN ι M (n + 1) = b' at *
    generalize N ^ n = t at *
    generalize M - 1 = u at *
    have f1 : N * b' ≤ N * ((N + n * u) * b) := mul_le_mul_of_nonneg_left hb' hN0
    have f2 : (N + n * u) * (N * b) ≤ (N + n * u) * ((N + (n : ℝ) ^ 2 * u) * t) :=
      mul_le_mul_of_nonneg_left ih' (by positivity)
    have f3 : (n : ℝ) * ((n : ℝ) ^ 2 * u) ≤ n * N := mul_le_mul_of_nonneg_left hn hn0
    have f4 : 0 ≤ u * (N * (n + 1) - n * ((n : ℝ) ^ 2 * u)) * t :=
      mul_nonneg (mul_nonneg hu (by nlinarith)) ht
    linarith

theorem wbad_eq (M : ℝ) (n : ℕ) :
    ∑ I ∈ LL ι n, (if ¬ I.Nodup then wt M [] I else 0) = bN ι M n - aN ι n := by
  unfold bN aN
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hnd : I.Nodup
  · simp [hnd, wt_nodup I hnd]
  · simp [hnd]

/-! Weights for the pairs: `w0` is the weight of a list with distinct entries relative to `J`,
`w1`, `w2` the same with one resp. two marked entries in `J`. -/

/-- The factor of one entry: zero if it repeats, `M` if it lies in `J`, one otherwise. -/
noncomputable def ee (M : ℝ) (J : List ι) (a : ι) (L : List ι) : ℝ :=
  if a ∈ L then 0 else if a ∈ J then M else 1

noncomputable def w0 (M : ℝ) (J : List ι) : List ι → ℝ
  | [] => 1
  | a :: L => ee M J a L * w0 M J L

noncomputable def w1 (M : ℝ) (J : List ι) : List ι → ℝ
  | [] => 0
  | a :: L => ee M J a L * w1 M J L + (if a ∈ J then ee M J a L * w0 M J L else 0)

noncomputable def w2 (M : ℝ) (J : List ι) : List ι → ℝ
  | [] => 0
  | a :: L => ee M J a L * w2 M J L + (if a ∈ J then ee M J a L * w1 M J L else 0)

omit [Fintype ι] in
theorem ee_nonneg {M : ℝ} (hM : 0 ≤ M) (J : List ι) (a : ι) (L : List ι) : 0 ≤ ee M J a L := by
  unfold ee
  split_ifs
  · exact le_rfl
  · exact hM
  · exact zero_le_one

omit [Fintype ι] in
theorem w0_nonneg {M : ℝ} (hM : 0 ≤ M) (J L : List ι) : 0 ≤ w0 M J L := by
  induction L with
  | nil => exact zero_le_one
  | cons a L ih => exact mul_nonneg (ee_nonneg hM J a L) ih

omit [Fintype ι] in
theorem w1_nonneg {M : ℝ} (hM : 0 ≤ M) (J L : List ι) : 0 ≤ w1 M J L := by
  induction L with
  | nil => exact le_rfl
  | cons a L ih =>
    show 0 ≤ ee M J a L * w1 M J L + (if a ∈ J then ee M J a L * w0 M J L else 0)
    have h1 := mul_nonneg (ee_nonneg hM J a L) ih
    have h2 := mul_nonneg (ee_nonneg hM J a L) (w0_nonneg hM J L)
    split_ifs <;> linarith

omit [Fintype ι] in
theorem w2_nonneg {M : ℝ} (hM : 0 ≤ M) (J L : List ι) : 0 ≤ w2 M J L := by
  induction L with
  | nil => exact le_rfl
  | cons a L ih =>
    show 0 ≤ ee M J a L * w2 M J L + (if a ∈ J then ee M J a L * w1 M J L else 0)
    have h1 := mul_nonneg (ee_nonneg hM J a L) ih
    have h2 := mul_nonneg (ee_nonneg hM J a L) (w1_nonneg hM J L)
    split_ifs <;> linarith

omit [Fintype ι] in
theorem wt_eq_w0 (M : ℝ) (J I : List ι) (hnd : I.Nodup) : wt M J I = w0 M J I := by
  induction I with
  | nil => rfl
  | cons a L ih =>
    have haL : a ∉ L := (List.nodup_cons.mp hnd).1
    show (if a ∈ L ∨ a ∈ J then M else 1) * wt M J L = ee M J a L * w0 M J L
    rw [ih (List.nodup_cons.mp hnd).2]
    unfold ee
    simp [haL]

omit [Fintype ι] in
theorem w0_le_w1 {M : ℝ} (hM : 0 ≤ M) (J I : List ι) (h : 1 ≤ I.countP (· ∈ J)) :
    w0 M J I ≤ w1 M J I := by
  induction I with
  | nil => simp at h
  | cons a L ih =>
    show ee M J a L * w0 M J L
      ≤ ee M J a L * w1 M J L + (if a ∈ J then ee M J a L * w0 M J L else 0)
    have h1 := mul_nonneg (ee_nonneg hM J a L) (w1_nonneg hM J L)
    by_cases haJ : a ∈ J
    · rw [if_pos haJ]; linarith
    · rw [if_neg haJ, add_zero]
      rw [List.countP_cons] at h
      simp only [haJ, decide_false, Bool.false_eq_true, if_false, add_zero] at h
      exact mul_le_mul_of_nonneg_left (ih h) (ee_nonneg hM J a L)

omit [Fintype ι] in
theorem w0_le_w2 {M : ℝ} (hM : 0 ≤ M) (J I : List ι) (h : 2 ≤ I.countP (· ∈ J)) :
    w0 M J I ≤ w2 M J I := by
  induction I with
  | nil => simp at h
  | cons a L ih =>
    show ee M J a L * w0 M J L
      ≤ ee M J a L * w2 M J L + (if a ∈ J then ee M J a L * w1 M J L else 0)
    have h2 := mul_nonneg (ee_nonneg hM J a L) (w2_nonneg hM J L)
    rw [List.countP_cons] at h
    by_cases haJ : a ∈ J
    · rw [if_pos haJ]
      simp only [haJ, decide_true, if_true] at h
      have h1 := mul_le_mul_of_nonneg_left (w0_le_w1 hM J L (by omega)) (ee_nonneg hM J a L)
      linarith
    · rw [if_neg haJ, add_zero]
      simp only [haJ, decide_false, Bool.false_eq_true, if_false, add_zero] at h
      exact mul_le_mul_of_nonneg_left (ih h) (ee_nonneg hM J a L)

theorem sum_ee_le {M : ℝ} (hM : 0 ≤ M) (J L : List ι) :
    ∑ a : ι, ee M J a L ≤ (Fintype.card ι : ℝ) + J.length * M := by
  have h1 : ∀ a : ι, ee M J a L ≤ if a ∈ J then M else 1 := by
    intro a
    unfold ee
    split_ifs <;> linarith
  refine (Finset.sum_le_sum fun a _ => h1 a).trans ?_
  rw [sum_ite_mem]
  have hc : (J.toFinset.card : ℝ) ≤ J.length := by exact_mod_cast List.toFinset_card_le J
  have h2 : (J.toFinset.card : ℝ) * M ≤ J.length * M := mul_le_mul_of_nonneg_right hc hM
  have h3 : (0 : ℝ) ≤ (J.toFinset.card : ℝ) := Nat.cast_nonneg _
  linarith

theorem sum_eeJ_le {M : ℝ} (hM : 0 ≤ M) (J L : List ι) :
    ∑ a : ι, (if a ∈ J then ee M J a L else 0) ≤ J.length * M := by
  have h1 : ∀ a : ι, (if a ∈ J then ee M J a L else 0) ≤ if a ∈ J then M else 0 := by
    intro a
    unfold ee
    split_ifs <;> linarith
  refine (Finset.sum_le_sum fun a _ => h1 a).trans ?_
  rw [sum_ite_mem]
  have hc : (J.toFinset.card : ℝ) ≤ J.length := by exact_mod_cast List.toFinset_card_le J
  have h2 : (J.toFinset.card : ℝ) * M ≤ J.length * M := mul_le_mul_of_nonneg_right hc hM
  linarith

theorem s0_succ {M : ℝ} (hM : 0 ≤ M) (J : List ι) (n : ℕ) :
    ∑ I ∈ LL ι (n + 1), w0 M J I
      ≤ ((Fintype.card ι : ℝ) + J.length * M) * ∑ I ∈ LL ι n, w0 M J I := by
  rw [sum_LL_succ, Finset.mul_sum]
  refine Finset.sum_le_sum fun L _ => ?_
  show ∑ a : ι, ee M J a L * w0 M J L ≤ _
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (sum_ee_le hM J L) (w0_nonneg hM J L)

theorem s1_succ {M : ℝ} (hM : 0 ≤ M) (J : List ι) (n : ℕ) :
    ∑ I ∈ LL ι (n + 1), w1 M J I
      ≤ ((Fintype.card ι : ℝ) + J.length * M) * ∑ I ∈ LL ι n, w1 M J I
        + J.length * M * ∑ I ∈ LL ι n, w0 M J I := by
  rw [sum_LL_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun L _ => ?_
  show ∑ a : ι, (ee M J a L * w1 M J L + (if a ∈ J then ee M J a L * w0 M J L else 0)) ≤ _
  have e : ∀ a : ι, (if a ∈ J then ee M J a L * w0 M J L else 0)
      = (if a ∈ J then ee M J a L else 0) * w0 M J L := by
    intro a; split_ifs <;> simp
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right (sum_ee_le hM J L) (w1_nonneg hM J L))
    (mul_le_mul_of_nonneg_right (sum_eeJ_le hM J L) (w0_nonneg hM J L))

theorem s2_succ {M : ℝ} (hM : 0 ≤ M) (J : List ι) (n : ℕ) :
    ∑ I ∈ LL ι (n + 1), w2 M J I
      ≤ ((Fintype.card ι : ℝ) + J.length * M) * ∑ I ∈ LL ι n, w2 M J I
        + J.length * M * ∑ I ∈ LL ι n, w1 M J I := by
  rw [sum_LL_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun L _ => ?_
  show ∑ a : ι, (ee M J a L * w2 M J L + (if a ∈ J then ee M J a L * w1 M J L else 0)) ≤ _
  have e : ∀ a : ι, (if a ∈ J then ee M J a L * w1 M J L else 0)
      = (if a ∈ J then ee M J a L else 0) * w1 M J L := by
    intro a; split_ifs <;> simp
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  exact add_le_add (mul_le_mul_of_nonneg_right (sum_ee_le hM J L) (w2_nonneg hM J L))
    (mul_le_mul_of_nonneg_right (sum_eeJ_le hM J L) (w1_nonneg hM J L))

/-- Closed forms: with `B = N + |J| M`, `c = |J| M`:
    `∑ w0 ≤ Bⁿ`, `N ∑ w1 ≤ n c Bⁿ`, `2 N² ∑ w2 ≤ n² c² Bⁿ`. -/
theorem s_bounds {M : ℝ} (hM : 0 ≤ M) (J : List ι) (n : ℕ) :
    ∑ I ∈ LL ι n, w0 M J I ≤ ((Fintype.card ι : ℝ) + J.length * M) ^ n ∧
    (Fintype.card ι : ℝ) * ∑ I ∈ LL ι n, w1 M J I
      ≤ n * (J.length * M) * ((Fintype.card ι : ℝ) + J.length * M) ^ n ∧
    2 * (Fintype.card ι : ℝ) ^ 2 * ∑ I ∈ LL ι n, w2 M J I
      ≤ (n : ℝ) ^ 2 * (J.length * M) ^ 2 * ((Fintype.card ι : ℝ) + J.length * M) ^ n := by
  induction n with
  | zero => simp [LL, w0, w1, w2]
  | succ n ih =>
    obtain ⟨i0, i1, i2⟩ := ih
    have h0 := s0_succ (ι := ι) hM J n
    have h1 := s1_succ (ι := ι) hM J n
    have h2 := s2_succ (ι := ι) hM J n
    have p0 : 0 ≤ ∑ I ∈ LL ι n, w0 M J I := Finset.sum_nonneg fun I _ => w0_nonneg hM J I
    have p1 : 0 ≤ ∑ I ∈ LL ι n, w1 M J I := Finset.sum_nonneg fun I _ => w1_nonneg hM J I
    have hN0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
    have hc0 : (0 : ℝ) ≤ (J.length : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [pow_succ]
    push_cast
    generalize (Fintype.card ι : ℝ) = N at *
    generalize (J.length : ℝ) * M = c at *
    generalize ∑ I ∈ LL ι n, w0 M J I = s0 at *
    generalize ∑ I ∈ LL ι n, w1 M J I = s1 at *
    generalize ∑ I ∈ LL ι n, w2 M J I = s2 at *
    generalize ∑ I ∈ LL ι (n + 1), w0 M J I = s0' at *
    generalize ∑ I ∈ LL ι (n + 1), w1 M J I = s1' at *
    generalize ∑ I ∈ LL ι (n + 1), w2 M J I = s2' at *
    have hB0 : 0 ≤ N + c := by linarith
    have ht : 0 ≤ (N + c) ^ n := pow_nonneg hB0 n
    generalize (N + c) ^ n = t at *
    refine ⟨?_, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_left i0 hB0
      linarith
    · have a1 : N * s1' ≤ N * ((N + c) * s1 + c * s0) := mul_le_mul_of_nonneg_left h1 hN0
      have a2 : (N + c) * (N * s1) ≤ (N + c) * (n * c * t) := mul_le_mul_of_nonneg_left i1 hB0
      have a3 : c * N * s0 ≤ c * N * t := mul_le_mul_of_nonneg_left i0 (mul_nonneg hc0 hN0)
      have a4 : 0 ≤ c * c * t := mul_nonneg (mul_nonneg hc0 hc0) ht
      linarith
    · have a1 : 2 * N ^ 2 * s2' ≤ 2 * N ^ 2 * ((N + c) * s2 + c * s1) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have a2 : (N + c) * (2 * N ^ 2 * s2) ≤ (N + c) * ((n : ℝ) ^ 2 * c ^ 2 * t) :=
        mul_le_mul_of_nonneg_left i2 hB0
      have a3 : 2 * N * c * (N * s1) ≤ 2 * N * c * (n * c * t) :=
        mul_le_mul_of_nonneg_left i1 (by positivity)
      have a4 : 0 ≤ c * c * c * t * (2 * n + 1) := by positivity
      have a5 : 0 ≤ N * (c * c * t) := by positivity
      linarith

/-- Lists with distinct entries of which at least two lie in `J`: the weights sum to at most
    `∑ w2`. -/
theorem pair_count_le {M : ℝ} (hM : 0 ≤ M) (J : List ι) (n : ℕ) :
    ∑ I ∈ LL ι n, (if I.Nodup then (if 2 ≤ I.countP (· ∈ J) then wt M J I else 0) else 0)
      ≤ ∑ I ∈ LL ι n, w2 M J I := by
  refine Finset.sum_le_sum fun I _ => ?_
  by_cases hnd : I.Nodup
  · rw [if_pos hnd]
    by_cases h2 : 2 ≤ I.countP (· ∈ J)
    · rw [if_pos h2, wt_eq_w0 M J I hnd]
      exact w0_le_w2 hM J I h2
    · rw [if_neg h2]; exact w2_nonneg hM J I
  · rw [if_neg hnd]; exact w2_nonneg hM J I

omit [Fintype ι] in
/-- At most one entry of `I` in `J`: all such entries coincide. -/
theorem common_unique (J I : List ι) (h : I.countP (· ∈ J) ≤ 1) :
    ∀ c ∈ I, ∀ c' ∈ I, c ∈ J → c' ∈ J → c = c' := by
  induction I with
  | nil => intro c hc; simp at hc
  | cons a L ih =>
    rw [List.countP_cons] at h
    by_cases haJ : a ∈ J
    · simp only [haJ, decide_true, if_true] at h
      have h0 : L.countP (· ∈ J) = 0 := by omega
      have hno : ∀ c ∈ L, c ∉ J := by
        intro c hc hcJ
        have := List.countP_eq_zero.mp h0 c hc
        simp [hcJ] at this
      intro c hc c' hc' hcJ hc'J
      rcases List.mem_cons.mp hc with rfl | hcL
      · rcases List.mem_cons.mp hc' with rfl | hc'L
        · rfl
        · exact absurd hc'J (hno c' hc'L)
      · exact absurd hcJ (hno c hcL)
    · simp only [haJ, decide_false, Bool.false_eq_true, if_false, add_zero] at h
      intro c hc c' hc' hcJ hc'J
      rcases List.mem_cons.mp hc with rfl | hcL
      · exact absurd hcJ haJ
      · rcases List.mem_cons.mp hc' with rfl | hc'L
        · exact absurd hc'J haJ
        · exact ih h c hcL c' hc'L hcJ hc'J

end Counting

/-! ### Assembly on the product space -/

section Assembly

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*} [MeasurableSpace G]
  {ν : Measure G} [IsProbabilityMeasure ν] {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

/-- `N^k Tr P̃^k`: the sum over all closed walks of `k = n + 1` steps. -/
noncomputable def Tsum (q : ℕ → G → G → ℝ) (n : ℕ) (x : ι → G) : ℝ :=
  ∑ I ∈ LL ι (n + 1), cyc q x I

/-- The part of `Tsum` from the walks through distinct indices (`N^k D_k` of the paper). -/
noncomputable def Dsum (q : ℕ → G → G → ℝ) (n : ℕ) (x : ι → G) : ℝ :=
  ∑ I ∈ (LL ι (n + 1)).filter (fun I => I.Nodup), cyc q x I

omit [MeasurableSpace G] in
theorem Dsum_sq (n : ℕ) (x : ι → G) :
    Dsum q n x ^ 2 = ∑ I ∈ (LL ι (n + 1)).filter (fun I => I.Nodup),
      ∑ J ∈ (LL ι (n + 1)).filter (fun I => I.Nodup), cyc q x I * cyc q x J := by
  unfold Dsum
  rw [pow_two, Finset.sum_mul_sum]

omit [MeasurableSpace G] in
theorem Tsum_sub (n : ℕ) (x : ι → G) :
    Tsum q n x - Dsum q n x = ∑ I ∈ LL ι (n + 1), (if ¬ I.Nodup then cyc q x I else 0) := by
  unfold Tsum Dsum
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hnd : I.Nodup <;> simp [hnd]

theorem int_abs_le_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) {t : ℝ}
    (ht : 0 < t) (h : ∫ x, f x ^ 2 ∂μ ≤ t ^ 2) : ∫ x, |f x| ∂μ ≤ t := by
  have hp : ∀ x, |f x| ≤ (f x ^ 2 + t ^ 2) / (2 * t) := by
    intro x
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_two_nonneg (|f x| - t), _root_.sq_abs (f x)]
  have hi : Integrable (fun x => (f x ^ 2 + t ^ 2) / (2 * t)) μ :=
    (hf2.add (integrable_const _)).div_const _
  calc ∫ x, |f x| ∂μ ≤ ∫ x, (f x ^ 2 + t ^ 2) / (2 * t) ∂μ := integral_mono hf.abs hi hp
    _ = ((∫ x, f x ^ 2 ∂μ) + t ^ 2) / (2 * t) := by
        rw [integral_div, integral_add hf2 (integrable_const _)]
        simp
    _ ≤ (t ^ 2 + t ^ 2) / (2 * t) := by gcongr
    _ = t := by field_simp; ring

theorem ER_arith {N M Nk b a kk : ℝ} (hN : 0 < N) (hNk : 0 < Nk) (hM : 1 ≤ M) (hkk : 0 ≤ kk)
    (h : 2 * N * (b - a) ≤ kk * (2 * M - 1) * Nk) : M * (b - a) / Nk ≤ kk * M ^ 2 / N := by
  rw [div_le_div_iff₀ hNk hN]
  have h1 := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ M)
  have h2 : 0 ≤ kk * M * Nk := by positivity
  linarith

theorem V_arith {N M mk α w kk V : ℝ} (hN : 0 < N) (hM : 1 ≤ M) (hmk0 : 0 ≤ mk) (hmk : mk ≤ M)
    (hα1 : α ≤ 1) (hα0 : 1 - kk / (2 * N) ≤ α) (hkk : 0 ≤ kk)
    (hw : w ≤ 3 * kk ^ 2 * M ^ 2 / (2 * N ^ 2))
    (hV : V ≤ mk ^ 2 * α ^ 2 + M ^ 2 * w - 2 * mk ^ 2 * α + mk ^ 2) :
    V ≤ (2 * kk * M ^ 2 / N) ^ 2 := by
  have hr0 : 0 ≤ kk / N := div_nonneg hkk hN.le
  have e1 : kk / (2 * N) = kk / N / 2 := by ring
  have e2 : 3 * kk ^ 2 * M ^ 2 / (2 * N ^ 2) = 3 / 2 * (kk / N) ^ 2 * M ^ 2 := by ring
  have e3 : (2 * kk * M ^ 2 / N) ^ 2 = 4 * (kk / N) ^ 2 * M ^ 4 := by ring
  rw [e1] at hα0
  rw [e2] at hw
  rw [e3]
  generalize kk / N = r at *
  have h1 : 0 ≤ 1 - α := by linarith
  have h2 : (1 - α) ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ h1 (by linarith) 2
  have h3 : mk ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hmk0 hmk 2
  have h4 : mk ^ 2 * (1 - α) ^ 2 ≤ M ^ 2 * (r / 2) ^ 2 :=
    mul_le_mul h3 h2 (by positivity) (by positivity)
  have h5 : M ^ 2 * w ≤ M ^ 2 * (3 / 2 * r ^ 2 * M ^ 2) :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  have hM2 : 1 ≤ M ^ 2 := by nlinarith
  have h6 : M ^ 2 ≤ M ^ 4 := by nlinarith [mul_nonneg (pow_two_nonneg M) (sub_nonneg.mpr hM2)]
  have h7 : r ^ 2 * M ^ 2 ≤ r ^ 2 * M ^ 4 := mul_le_mul_of_nonneg_left h6 (by positivity)
  have h8 : 0 ≤ r ^ 2 * M ^ 4 := by positivity
  linarith

theorem bias_arith {N M mk α kk e : ℝ} (hN : 0 < N) (hM : 1 ≤ M) (hmk0 : 0 ≤ mk) (hmk : mk ≤ M)
    (hα1 : α ≤ 1) (hα0 : 1 - kk / (2 * N) ≤ α) (hkk : 0 ≤ kk) (he0 : 0 ≤ e)
    (he : e ≤ kk * M ^ 2 / N) : |e + α * mk - mk| ≤ kk * M ^ 2 / N := by
  have hr0 : 0 ≤ kk / N := div_nonneg hkk hN.le
  have e1 : kk / (2 * N) = kk / N / 2 := by ring
  have e2 : kk * M ^ 2 / N = kk / N * M ^ 2 := by ring
  rw [e1] at hα0
  rw [e2] at he ⊢
  generalize kk / N = r at *
  have h2 : (1 - α) * mk ≤ r / 2 * M := mul_le_mul (by linarith) hmk hmk0 (by positivity)
  have hMM : M ≤ M ^ 2 := by nlinarith
  have h3 : r * M ≤ r * M ^ 2 := mul_le_mul_of_nonneg_left hMM hr0
  have h4 : 0 ≤ (1 - α) * mk := mul_nonneg (by linarith) hmk0
  have h5 : 0 ≤ r * M := mul_nonneg hr0 (by linarith)
  rw [abs_le]
  constructor <;> linarith

theorem sq_arith {N M kk Mk : ℝ} (hMk : M ^ 2 ≤ Mk) :
    2 * (kk * Mk / (2 * N)) ^ 2 + 2 * (2 * kk * M ^ 2 / N) ^ 2 ≤ (3 * kk * Mk / N) ^ 2 := by
  have e1 : 2 * (kk * Mk / (2 * N)) ^ 2 + 2 * (2 * kk * M ^ 2 / N) ^ 2
      = (kk / N) ^ 2 * (Mk ^ 2 / 2 + 8 * (M ^ 2) ^ 2) := by ring
  have e2 : (3 * kk * Mk / N) ^ 2 = (kk / N) ^ 2 * (9 * Mk ^ 2) := by ring
  rw [e1, e2]
  have h1 : (M ^ 2) ^ 2 ≤ Mk ^ 2 := pow_le_pow_left₀ (by positivity) hMk 2
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h2 : 0 ≤ Mk ^ 2 := by positivity
  linarith

theorem pow_bound {N y : ℝ} (hN : 0 < N) (hy : 0 ≤ y) (k : ℕ) (h : k * y ≤ N) :
    (N + y) ^ k ≤ 3 * N ^ k := by
  have h1 : N + y = N * (1 + y / N) := by field_simp
  have h2 : (1 + y / N) ^ k ≤ 3 :=
    calc (1 + y / N) ^ k ≤ (Real.exp (y / N)) ^ k :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (y / N)]) k
      _ = Real.exp (k * (y / N)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by
          rw [← mul_div_assoc, div_le_one hN]; exact h)
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  rw [h1, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right h2 (by positivity)

namespace RK

variable (S : RK ν q M m)
include S

theorem Dsum_integrable (n : ℕ) :
    Integrable (fun x : ι → G => Dsum q n x) (Measure.pi fun _ : ι => ν) :=
  integrable_finset_sum _ fun I _ => S.cyc_integrable I

theorem Tsum_integrable (n : ℕ) :
    Integrable (fun x : ι → G => Tsum q n x) (Measure.pi fun _ : ι => ν) :=
  integrable_finset_sum _ fun I _ => S.cyc_integrable I

theorem Dsum_sq_integrable (n : ℕ) :
    Integrable (fun x : ι → G => Dsum q n x ^ 2) (Measure.pi fun _ : ι => ν) := by
  simp_rw [Dsum_sq (q := q) n]
  exact integrable_finset_sum _ fun I _ => integrable_finset_sum _ fun J _ =>
    S.pair_integrable I J

/-- Stage (1), summed: `E D = #{distinct tuples} · m_k`. -/
theorem int_Dsum (n : ℕ) :
    ∫ x, Dsum q n x ∂Measure.pi (fun _ : ι => ν) = aN ι (n + 1) * m (n + 1) := by
  unfold Dsum
  rw [integral_finset_sum _ (fun I _ => S.cyc_integrable I)]
  have h : ∀ I ∈ (LL ι (n + 1)).filter (fun I => I.Nodup),
      ∫ x, cyc q x I ∂Measure.pi (fun _ : ι => ν) = m (n + 1) := by
    intro I hI
    obtain ⟨hI1, hnd⟩ := Finset.mem_filter.mp hI
    obtain ⟨a, L, rfl, hlen⟩ := exists_cons_of_mem_LL hI1
    rw [S.int_nodup a L hnd, hlen]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, aN, Finset.natCast_card_filter]

omit [IsProbabilityMeasure ν] in
theorem Tsum_sub_nonneg (n : ℕ) (x : ι → G) : 0 ≤ Tsum q n x - Dsum q n x := by
  rw [Tsum_sub]
  refine Finset.sum_nonneg fun I _ => ?_
  by_cases hnd : I.Nodup <;> simp [hnd, cyc_nonneg S.nonneg x I]

/-- Stages (2), (3): the walks with a repeated index. -/
theorem int_Tsum_sub (n : ℕ) :
    ∫ x, (Tsum q n x - Dsum q n x) ∂Measure.pi (fun _ : ι => ν)
      ≤ M * (bN ι M (n + 1) - aN ι (n + 1)) := by
  simp_rw [Tsum_sub (q := q) n]
  have hint : ∀ I ∈ LL ι (n + 1), Integrable
      (fun x : ι → G => if ¬ I.Nodup then cyc q x I else 0) (Measure.pi fun _ : ι => ν) := by
    intro I _
    by_cases hnd : I.Nodup
    · simp [hnd]
    · simpa [hnd] using S.cyc_integrable I
  rw [integral_finset_sum _ hint, ← wbad_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  by_cases hnd : I.Nodup
  · simp [hnd]
  · obtain ⟨a, L, rfl, _⟩ := exists_cons_of_mem_LL hI
    simpa [hnd] using S.int_le a L

/-- Second moment of the distinct part. -/
theorem int_Dsum_sq (n : ℕ) :
    ∫ x, Dsum q n x ^ 2 ∂Measure.pi (fun _ : ι => ν)
      ≤ aN ι (n + 1) ^ 2 * m (n + 1) ^ 2
        + M ^ 2 * ∑ J ∈ LL ι (n + 1), (if J.Nodup then
            ∑ I ∈ LL ι (n + 1), (if I.Nodup then
              (if 2 ≤ I.countP (· ∈ J) then wt M J I else 0) else 0) else 0) := by
  have hM := S.M_nonneg
  simp_rw [Dsum_sq (q := q) n]
  rw [integral_finset_sum _ (fun I _ => integrable_finset_sum _ fun J _ =>
    S.pair_integrable I J)]
  have hterm : ∀ I ∈ (LL ι (n + 1)).filter (fun I => I.Nodup),
      ∀ J ∈ (LL ι (n + 1)).filter (fun I => I.Nodup),
      ∫ x, cyc q x I * cyc q x J ∂Measure.pi (fun _ : ι => ν)
        ≤ m (n + 1) ^ 2 + M ^ 2 * (if 2 ≤ I.countP (· ∈ J) then wt M J I else 0) := by
    intro I hI J hJ
    obtain ⟨hI1, hndI⟩ := Finset.mem_filter.mp hI
    obtain ⟨hJ1, hndJ⟩ := Finset.mem_filter.mp hJ
    obtain ⟨a, L, rfl, hlen⟩ := exists_cons_of_mem_LL hI1
    obtain ⟨a', L', rfl, hlen'⟩ := exists_cons_of_mem_LL hJ1
    by_cases h2 : 2 ≤ (a :: L).countP (· ∈ a' :: L')
    · rw [if_pos h2]
      have h := S.pair_le a L a' L'
      rw [wt_nodup _ hndJ] at h
      have h0 : 0 ≤ m (n + 1) ^ 2 := by positivity
      have e : M * (wt M (a' :: L') (a :: L) * (M * 1)) = M ^ 2 * wt M (a' :: L') (a :: L) := by
        ring
      linarith
    · rw [if_neg h2, mul_zero, add_zero]
      have hu := common_unique (a' :: L') (a :: L) (by omega)
      have hv : ∃ v ∈ a :: L, ∀ c ∈ a :: L, c ∈ a' :: L' → c = v := by
        by_cases hex : ∃ c ∈ a :: L, c ∈ a' :: L'
        · obtain ⟨v, hv1, hv2⟩ := hex
          exact ⟨v, hv1, fun c hc hcJ => hu c hc v hv1 hcJ hv2⟩
        · exact ⟨a, List.mem_cons_self, fun c hc hcJ => absurd ⟨c, hc, hcJ⟩ hex⟩
      obtain ⟨v, hv1, hv2⟩ := hv
      rw [S.pair_eq a L hndI a' L' hndJ v hv1 hv2, hlen, hlen', pow_two]
  have hsum := Finset.sum_le_sum fun I hI =>
    (integral_finset_sum _ (fun J _ => S.pair_integrable I J)).le.trans
      (Finset.sum_le_sum fun J hJ => hterm I hI J hJ)
  refine hsum.trans (le_of_eq ?_)
  have hA : (((LL ι (n + 1)).filter (fun I => I.Nodup)).card : ℝ) = aN ι (n + 1) := by
    rw [aN, Finset.natCast_card_filter]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · simp only [Finset.sum_const, nsmul_eq_mul]
    rw [hA]; ring
  · rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun J _ => ?_
    by_cases hJ : J.Nodup
    · rw [if_pos hJ, if_pos hJ, Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      by_cases hI : I.Nodup <;> simp [hI]
    · rw [if_neg hJ, if_neg hJ, mul_zero]

/-- **Main statement on the product space.** For `k = n + 1` with `k² M ≤ N`:
    `E |N^{-k} T - m_k| ≤ 3 k² M²/N`, `|E N^{-k} T - m_k| ≤ k² M²/N` and, for the part `D` from
    the walks through distinct indices, `E (N^{-k} D - m_k)² ≤ (2 k² M²/N)²`. -/
theorem main_pi (n : ℕ) (hk : ((n : ℝ) + 1) ^ 2 * M ≤ (Fintype.card ι : ℝ)) :
    ∫ x, |Tsum q n x / (Fintype.card ι : ℝ) ^ (n + 1) - m (n + 1)|
        ∂Measure.pi (fun _ : ι => ν)
      ≤ 3 * ((n : ℝ) + 1) ^ 2 * M ^ 2 / (Fintype.card ι : ℝ) ∧
    |∫ x, Tsum q n x / (Fintype.card ι : ℝ) ^ (n + 1) ∂Measure.pi (fun _ : ι => ν) - m (n + 1)|
      ≤ ((n : ℝ) + 1) ^ 2 * M ^ 2 / (Fintype.card ι : ℝ) ∧
    ∫ x, (Dsum q n x / (Fintype.card ι : ℝ) ^ (n + 1) - m (n + 1)) ^ 2
        ∂Measure.pi (fun _ : ι => ν)
      ≤ (2 * ((n : ℝ) + 1) ^ 2 * M ^ 2 / (Fintype.card ι : ℝ)) ^ 2 := by
  have hM1 := S.M_ge
  have hM0 := S.M_nonneg
  have hmk0 := S.m_nonneg (n + 1) (by omega)
  have hmk := S.m_le (n + 1) (by omega)
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkk1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hkkM : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * M := by nlinarith
  have hN1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hkN : n + 1 ≤ Fintype.card ι := by
    have : ((n : ℝ) + 1) ≤ (Fintype.card ι : ℝ) := by nlinarith
    exact_mod_cast this
  have hNk : (0 : ℝ) < (Fintype.card ι : ℝ) ^ (n + 1) := pow_pos hNpos _
  obtain ⟨hA1, hA2⟩ := aN_bounds (ι := ι) (n + 1) hkN
  have hB := bN_bound (ι := ι) hM1 (n + 1) (by push_cast; nlinarith)
  have ha0 := aN_nonneg (ι := ι) (n + 1)
  have hE1 := S.int_Tsum_sub (ι := ι) n
  have hE2 := S.int_Dsum (ι := ι) n
  have hE3 := S.int_Dsum_sq (ι := ι) n
  have hTi := S.Tsum_integrable (ι := ι) n
  have hDi := S.Dsum_integrable (ι := ι) n
  have hD2i := S.Dsum_sq_integrable (ι := ι) n
  -- the pair sum
  have hW : 2 * (Fintype.card ι : ℝ) ^ 2 * ∑ J ∈ LL ι (n + 1), (if J.Nodup then
            ∑ I ∈ LL ι (n + 1), (if I.Nodup then
              (if 2 ≤ I.countP (· ∈ J) then wt M J I else 0) else 0) else 0)
      ≤ 3 * (((n : ℝ) + 1) ^ 2) ^ 2 * M ^ 2 * ((Fintype.card ι : ℝ) ^ (n + 1)) ^ 2 := by
    have hC : ∀ J ∈ LL ι (n + 1), 2 * (Fintype.card ι : ℝ) ^ 2 * (if J.Nodup then
            ∑ I ∈ LL ι (n + 1), (if I.Nodup then
              (if 2 ≤ I.countP (· ∈ J) then wt M J I else 0) else 0) else 0)
        ≤ (if J.Nodup then (1 : ℝ) else 0)
          * (3 * (((n : ℝ) + 1) ^ 2) ^ 2 * M ^ 2 * (Fintype.card ι : ℝ) ^ (n + 1)) := by
      intro J hJ
      have hlen := mem_LL.mp hJ
      by_cases hnd : J.Nodup
      · rw [if_pos hnd, if_pos hnd, one_mul]
        have h1 := pair_count_le (ι := ι) hM0 J (n + 1)
        have h2 := (s_bounds (ι := ι) hM0 J (n + 1)).2.2
        rw [hlen] at h2
        push_cast at h2
        have h3 := pow_bound hNpos (mul_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1) hM0)
          (n + 1) (by push_cast; nlinarith)
        have h4 : ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1) * M) ^ 2
              * ((Fintype.card ι : ℝ) + ((n : ℝ) + 1) * M) ^ (n + 1)
            ≤ ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 1) * M) ^ 2
              * (3 * (Fintype.card ι : ℝ) ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have h5 := mul_le_mul_of_nonneg_left h1
          (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card ι : ℝ) ^ 2)
        calc _ ≤ _ := h5
          _ ≤ _ := h2
          _ ≤ _ := h4
          _ = _ := by ring
      · rw [if_neg hnd, if_neg hnd]; simp
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hC).trans ?_
    rw [← Finset.sum_mul]
    have : ∑ J ∈ LL ι (n + 1), (if J.Nodup then (1 : ℝ) else 0) = aN ι (n + 1) := rfl
    rw [this]
    have h6 := mul_le_mul_of_nonneg_right hA1
      (by positivity : (0 : ℝ) ≤ 3 * (((n : ℝ) + 1) ^ 2) ^ 2 * M ^ 2
        * (Fintype.card ι : ℝ) ^ (n + 1))
    refine h6.trans (le_of_eq ?_)
    ring
  push_cast at hA2 hB
  generalize hWdef : (∑ J ∈ LL ι (n + 1), (if J.Nodup then
            ∑ I ∈ LL ι (n + 1), (if I.Nodup then
              (if 2 ≤ I.countP (· ∈ J) then wt M J I else 0) else 0) else 0)) = W at hW hE3
  generalize hadef : aN ι (n + 1) = a at *
  generalize hbdef : bN ι M (n + 1) = b at *
  generalize hmdef : m (n + 1) = mk at *
  generalize hkkdef : ((n : ℝ) + 1) ^ 2 = kk at *
  generalize hNdef : (Fintype.card ι : ℝ) = N at *
  generalize hNkdef : N ^ (n + 1) = Nk at *
  have hkk0 : 0 ≤ kk := by linarith
  -- E (T - D)/Nk
  have hER : (∫ x, (Tsum q n x - Dsum q n x) ∂Measure.pi (fun _ : ι => ν)) / Nk
      ≤ kk * M ^ 2 / N := by
    refine (div_le_div_of_nonneg_right hE1 hNk.le).trans ?_
    exact ER_arith hNpos hNk hM1 hkk0 (by linarith)
  have hER0 : 0 ≤ ∫ x, (Tsum q n x - Dsum q n x) ∂Measure.pi (fun _ : ι => ν) :=
    integral_nonneg fun x => S.Tsum_sub_nonneg n x
  have hα1 : a / Nk ≤ 1 := (div_le_one hNk).mpr hA1
  have hα0 : 1 - kk / (2 * N) ≤ a / Nk := by
    rw [le_div_iff₀ hNk]
    have e : (1 - kk / (2 * N)) * Nk = (2 * N - kk) * Nk / (2 * N) := by field_simp
    rw [e, div_le_iff₀ (by linarith)]
    linarith
  have hf : Integrable (fun x : ι → G => Dsum q n x / Nk - mk) (Measure.pi fun _ : ι => ν) :=
    (hDi.div_const _).sub (integrable_const _)
  have e2 : ∀ x : ι → G, (Dsum q n x / Nk - mk) ^ 2
      = 1 / Nk ^ 2 * Dsum q n x ^ 2 - 2 * mk / Nk * Dsum q n x + mk ^ 2 := by
    intro x; ring
  have hf2 : Integrable (fun x : ι → G => (Dsum q n x / Nk - mk) ^ 2)
      (Measure.pi fun _ : ι => ν) := by
    simp_rw [e2]
    exact ((hD2i.const_mul _).sub (hDi.const_mul _)).add (integrable_const _)
  have hV : ∫ x, (Dsum q n x / Nk - mk) ^ 2 ∂Measure.pi (fun _ : ι => ν)
      ≤ (2 * kk * M ^ 2 / N) ^ 2 := by
    simp_rw [e2]
    have j1 : Integrable (fun x : ι → G => 1 / Nk ^ 2 * Dsum q n x ^ 2)
        (Measure.pi fun _ : ι => ν) := hD2i.const_mul _
    have j2 : Integrable (fun x : ι → G => 2 * mk / Nk * Dsum q n x)
        (Measure.pi fun _ : ι => ν) := hDi.const_mul _
    have j3 : Integrable (fun x : ι → G => 1 / Nk ^ 2 * Dsum q n x ^ 2
        - 2 * mk / Nk * Dsum q n x) (Measure.pi fun _ : ι => ν) := j1.sub j2
    rw [integral_add j3 (integrable_const _), integral_sub j1 j2, integral_const_mul,
      integral_const_mul, hE2]
    simp only [integral_const, probReal_univ, one_smul]
    have hw : W / Nk ^ 2 ≤ 3 * kk ^ 2 * M ^ 2 / (2 * N ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    refine V_arith hNpos hM1 hmk0 hmk hα1 hα0 hkk0 hw ?_
    have h1 := mul_le_mul_of_nonneg_left hE3 (by positivity : (0 : ℝ) ≤ 1 / Nk ^ 2)
    have e3 : 1 / Nk ^ 2 * (a ^ 2 * mk ^ 2 + M ^ 2 * W) - 2 * mk / Nk * (a * mk) + mk ^ 2
        = mk ^ 2 * (a / Nk) ^ 2 + M ^ 2 * (W / Nk ^ 2) - 2 * mk ^ 2 * (a / Nk) + mk ^ 2 := by
      ring
    linarith
  refine ⟨?_, ?_, hV⟩
  · -- the L¹ bound
    have hkkN : 0 < 2 * kk * M ^ 2 / N := by positivity
    have hD1 := int_abs_le_of_sq hf hf2 hkkN hV
    have hp : ∀ x : ι → G, |Tsum q n x / Nk - mk|
        ≤ (Tsum q n x - Dsum q n x) / Nk + |Dsum q n x / Nk - mk| := by
      intro x
      have e : Tsum q n x / Nk - mk = (Tsum q n x - Dsum q n x) / Nk + (Dsum q n x / Nk - mk) := by
        ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_nonneg (div_nonneg (S.Tsum_sub_nonneg n x) hNk.le)]
    have hi1 : Integrable (fun x : ι → G => (Tsum q n x - Dsum q n x) / Nk)
        (Measure.pi fun _ : ι => ν) := (hTi.sub hDi).div_const _
    calc ∫ x, |Tsum q n x / Nk - mk| ∂Measure.pi (fun _ : ι => ν)
        ≤ ∫ x, ((Tsum q n x - Dsum q n x) / Nk + |Dsum q n x / Nk - mk|)
            ∂Measure.pi (fun _ : ι => ν) :=
          integral_mono (((hTi.div_const _).sub (integrable_const _)).abs) (hi1.add hf.abs) hp
      _ = (∫ x, (Tsum q n x - Dsum q n x) ∂Measure.pi (fun _ : ι => ν)) / Nk
            + ∫ x, |Dsum q n x / Nk - mk| ∂Measure.pi (fun _ : ι => ν) := by
          rw [integral_add hi1 hf.abs, integral_div]
      _ ≤ kk * M ^ 2 / N + 2 * kk * M ^ 2 / N := add_le_add hER hD1
      _ = 3 * kk * M ^ 2 / N := by ring
  · -- the bias
    have e : ∀ x : ι → G, Tsum q n x / Nk = (Tsum q n x - Dsum q n x) / Nk + Dsum q n x / Nk := by
      intro x; ring
    simp_rw [e]
    have j1 : Integrable (fun x : ι → G => (Tsum q n x - Dsum q n x) / Nk)
        (Measure.pi fun _ : ι => ν) := (hTi.sub hDi).div_const _
    have j2 : Integrable (fun x : ι → G => Dsum q n x / Nk)
        (Measure.pi fun _ : ι => ν) := hDi.div_const _
    rw [integral_add j1 j2, integral_div, integral_div, hE2]
    have h1 : 0 ≤ (∫ x, (Tsum q n x - Dsum q n x) ∂Measure.pi (fun _ : ι => ν)) / Nk :=
      div_nonneg hER0 hNk.le
    have e4 : a * mk / Nk = a / Nk * mk := by ring
    rw [e4]
    exact bias_arith hNpos hM1 hmk0 hmk hα1 hα0 hkk0 h1 hER

omit [IsProbabilityMeasure ν] in
/-- The walks with a repeated index, pointwise: `0 ≤ T - D ≤ M^k (N^k - #distinct)`. -/
theorem Tsum_sub_le (n : ℕ) (x : ι → G) :
    Tsum q n x - Dsum q n x
      ≤ M ^ (n + 1) * ((Fintype.card ι : ℝ) ^ (n + 1) - aN ι (n + 1)) := by
  rw [Tsum_sub, ← card_LL (ι := ι) (n + 1), aN, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  have hlen := mem_LL.mp hI
  by_cases hnd : I.Nodup
  · simp [hnd]
  · have h := (le_abs_self _).trans (cyc_abs_le S.nonneg S.bound S.M_ge x I)
    rw [hlen] at h
    simpa [hnd] using h

/-- **Second moment on the product space** (the form of Proposition "oracle"). For `k = n + 1 ≥ 2`
    with `k² M ≤ N`: `E (N^{-k} T - m_k)² ≤ (3 k² M^k/N)²`. -/
theorem main_pi_sq (n : ℕ) (hn : 1 ≤ n)
    (hk : ((n : ℝ) + 1) ^ 2 * M ≤ (Fintype.card ι : ℝ)) :
    ∫ x, (Tsum q n x / (Fintype.card ι : ℝ) ^ (n + 1) - m (n + 1)) ^ 2
        ∂Measure.pi (fun _ : ι => ν)
      ≤ (3 * ((n : ℝ) + 1) ^ 2 * M ^ (n + 1) / (Fintype.card ι : ℝ)) ^ 2 := by
  have hM1 := S.M_ge
  have hM0 := S.M_nonneg
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hkk1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hkkM : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * M := by nlinarith
  have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by linarith
  have hkN : n + 1 ≤ Fintype.card ι := by
    have : ((n : ℝ) + 1) ≤ (Fintype.card ι : ℝ) := by nlinarith
    exact_mod_cast this
  have hNk : (0 : ℝ) < (Fintype.card ι : ℝ) ^ (n + 1) := pow_pos hNpos _
  obtain ⟨-, hA2⟩ := aN_bounds (ι := ι) (n + 1) hkN
  obtain ⟨-, -, hV⟩ := S.main_pi (ι := ι) n hk
  have hDi := S.Dsum_integrable (ι := ι) n
  have hD2i := S.Dsum_sq_integrable (ι := ι) n
  have hMk : M ^ 2 ≤ M ^ (n + 1) := pow_le_pow_right₀ hM1 (by omega)
  have hsub := S.Tsum_sub_le (ι := ι) n
  have hsub0 := S.Tsum_sub_nonneg (ι := ι) n
  have hMk0 : 0 ≤ M ^ (n + 1) := pow_nonneg hM0 _
  push_cast at hA2
  generalize aN ι (n + 1) = a at *
  generalize m (n + 1) = mk at *
  generalize ((n : ℝ) + 1) ^ 2 = kk at *
  generalize (Fintype.card ι : ℝ) = N at *
  generalize N ^ (n + 1) = Nk at *
  generalize M ^ (n + 1) = Mk at *
  have hkk0 : 0 ≤ kk := by linarith
  have hR : ∀ x : ι → G, (Tsum q n x - Dsum q n x) / Nk ≤ kk * Mk / (2 * N) := by
    intro x
    rw [div_le_div_iff₀ hNk (by linarith)]
    have h1 : (Tsum q n x - Dsum q n x) * (2 * N) ≤ Mk * (Nk - a) * (2 * N) :=
      mul_le_mul_of_nonneg_right (hsub x) (by linarith)
    have h2 : Mk * (2 * N * (Nk - a)) ≤ Mk * (kk * Nk) :=
      mul_le_mul_of_nonneg_left (by linarith) hMk0
    linarith
  have e2 : ∀ x : ι → G, (Dsum q n x / Nk - mk) ^ 2
      = 1 / Nk ^ 2 * Dsum q n x ^ 2 - 2 * mk / Nk * Dsum q n x + mk ^ 2 := by
    intro x; ring
  have hf2 : Integrable (fun x : ι → G => (Dsum q n x / Nk - mk) ^ 2)
      (Measure.pi fun _ : ι => ν) := by
    simp_rw [e2]
    exact ((hD2i.const_mul _).sub (hDi.const_mul _)).add (integrable_const _)
  have hp : ∀ x : ι → G, (Tsum q n x / Nk - mk) ^ 2
      ≤ 2 * (kk * Mk / (2 * N)) ^ 2 + 2 * (Dsum q n x / Nk - mk) ^ 2 := by
    intro x
    have e : Tsum q n x / Nk - mk = (Tsum q n x - Dsum q n x) / Nk + (Dsum q n x / Nk - mk) := by
      ring
    have h0 : 0 ≤ (Tsum q n x - Dsum q n x) / Nk := div_nonneg (hsub0 x) hNk.le
    have h1 : ((Tsum q n x - Dsum q n x) / Nk) ^ 2 ≤ (kk * Mk / (2 * N)) ^ 2 :=
      pow_le_pow_left₀ h0 (hR x) 2
    rw [e]
    nlinarith [pow_two_nonneg ((Tsum q n x - Dsum q n x) / Nk - (Dsum q n x / Nk - mk))]
  have hg : Integrable (fun x : ι → G => 2 * (kk * Mk / (2 * N)) ^ 2
      + 2 * (Dsum q n x / Nk - mk) ^ 2) (Measure.pi fun _ : ι => ν) :=
    (integrable_const _).add (hf2.const_mul 2)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun x : ι → G => pow_two_nonneg (Tsum q n x / Nk - mk)) hg
    (Filter.Eventually.of_forall hp)
  refine hmono.trans ?_
  have hc : ∫ x : ι → G, 2 * (Dsum q n x / Nk - mk) ^ 2 ∂Measure.pi (fun _ : ι => ν)
      = 2 * ∫ x : ι → G, (Dsum q n x / Nk - mk) ^ 2 ∂Measure.pi (fun _ : ι => ν) :=
    integral_const_mul _ _
  rw [integral_add (integrable_const _) (hf2.const_mul 2), hc]
  simp only [integral_const, probReal_univ, one_smul]
  have := sq_arith (N := N) (kk := kk) hMk
  linarith

end RK

end Assembly

/-! ### The trace of a power of the walk matrix as a sum over closed walks -/

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Type*}

/-- The kernel matrix `q_1(x_a, x_b)`. -/
def Amat (q : ℕ → G → G → ℝ) (x : ι → G) : Matrix ι ι ℝ := fun a b => q 1 (x a) (x b)

theorem Amat_pow_apply (q : ℕ → G → G → ℝ) (x : ι → G) (n : ℕ) (a b : ι) :
    ((Amat q x) ^ (n + 1)) a b = ∑ L ∈ LL ι n, ch q x 1 a L b := by
  induction n generalizing a with
  | zero =>
    rw [zero_add, pow_one, show LL ι 0 = {[]} from rfl, Finset.sum_singleton]
    rfl
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply, sum_LL_succ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ih, Finset.mul_sum]
    rfl

theorem trace_Amat_pow (q : ℕ → G → G → ℝ) (x : ι → G) (n : ℕ) :
    Matrix.trace ((Amat q x) ^ (n + 1)) = Tsum q n x := by
  unfold Tsum Matrix.trace
  rw [sum_LL_succ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, Amat_pow_apply]
  rfl

/-- `Tr P̃^k = N^{-k} ∑_{closed walks}` for `P̃_{ab} = q_1(x_a,x_b)/N`. -/
theorem trace_walk_pow (q : ℕ → G → G → ℝ) (x : ι → G) (n : ℕ) (N : ℝ) :
    Matrix.trace ((Matrix.of fun a b : ι => q 1 (x a) (x b) / N) ^ (n + 1))
      = Tsum q n x / N ^ (n + 1) := by
  have h : (Matrix.of fun a b : ι => q 1 (x a) (x b) / N) = (1 / N) • Amat q x := by
    ext a b
    simp [Amat, Matrix.smul_apply, div_eq_inv_mul]
  rw [h, smul_pow, Matrix.trace_smul, trace_Amat_pow, smul_eq_mul, one_div, inv_pow]
  ring

end Trace

/-! ### From independent sample points to the product measure -/

section Sample

variable {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
  {q : ℕ → G → G → ℝ} {M : ℝ} {m : ℕ → ℝ}

/-- **Moments of the walk with exact normalisation, general `k = n + 1`** (abstract kernel).
    Under the HYPOTHESES `RK` on the kernel family, for independent points `X_j` with law `ν`,
    `P̃_{ab} = q_1(X_a, X_b)/N` (`a, b < N`) and `k² M ≤ N`:
    `E |Tr P̃^k - m_k| ≤ 3 k² M²/N`, `|E Tr P̃^k - m_k| ≤ k² M²/N` and, for `k ≥ 2`,
    `E (Tr P̃^k - m_k)² ≤ (3 k² M^k/N)²`. -/
theorem RK.oraclemoments (S : RK ν q M m) {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → G) (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (N n : ℕ)
    (hk : ((n : ℝ) + 1) ^ 2 * M ≤ N) :
    ∫ ω, |Matrix.trace ((Matrix.of fun a b : Fin N => q 1 (X a ω) (X b ω) / N) ^ (n + 1))
        - m (n + 1)| ∂μ ≤ 3 * ((n : ℝ) + 1) ^ 2 * M ^ 2 / N ∧
    |∫ ω, Matrix.trace ((Matrix.of fun a b : Fin N => q 1 (X a ω) (X b ω) / N) ^ (n + 1)) ∂μ
        - m (n + 1)| ≤ ((n : ℝ) + 1) ^ 2 * M ^ 2 / N ∧
    (1 ≤ n → ∫ ω, (Matrix.trace ((Matrix.of fun a b : Fin N => q 1 (X a ω) (X b ω) / N) ^ (n + 1))
        - m (n + 1)) ^ 2 ∂μ ≤ (3 * ((n : ℝ) + 1) ^ 2 * M ^ (n + 1) / N) ^ 2) := by
  have hmap : μ.map (fun ω (j : Fin N) => X j ω) = Measure.pi (fun _ : Fin N => ν) := by
    have hi : ProbabilityTheory.iIndepFun (fun j : Fin N => X j) μ :=
      h_indep.precomp Fin.val_injective
    have h := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun j : Fin N => (hX j).aemeasurable)).mp hi
    simp_rw [hlaw] at h
    exact h
  have hΦ : Measurable (fun ω (j : Fin N) => X j ω) := measurable_pi_lambda _ fun j => hX j
  have hT : Measurable fun x : Fin N → G => Tsum q n x :=
    Finset.measurable_sum _ fun I _ => S.cyc_measurable I
  obtain ⟨h1, h2, -⟩ := S.main_pi (ι := Fin N) n (by simpa using hk)
  have h3 := fun hn : 1 ≤ n => S.main_pi_sq (ι := Fin N) n hn (by simpa using hk)
  simp only [Fintype.card_fin] at h1 h2 h3
  rw [← hmap] at h3
  simp_rw [integral_map hΦ.aemeasurable
    (((hT.div_const _).sub_const _).pow_const 2).aestronglyMeasurable] at h3
  rw [← hmap, integral_map hΦ.aemeasurable
    (((hT.div_const _).sub_const _).abs).aestronglyMeasurable] at h1
  rw [← hmap, integral_map hΦ.aemeasurable (hT.div_const _).aestronglyMeasurable] at h2
  simp_rw [trace_walk_pow]
  exact ⟨h1, h2, h3⟩

end Sample

/-! ### The flat torus with the Gaussian kernel -/

section Torus

open PiBound CTG.Reals.TorusReduction

/-- The hypotheses `RK` hold for the periodised Gaussian kernel of variance `σ` on the flat torus:
    `q_i(x,y) = p_{iσ}(x - y)`, `M = m_1 = p_σ(0)`, `m_i = p_{iσ}(0)`. -/
theorem torusRK {σ : ℝ} (hσ : 0 < σ) (d : ℕ) :
    RK (flatTorusMeasure d) (fun i (x y : FlatTorus d) => heatP d σ i (x - y)) (torusM d σ 1)
      (fun i => torusM d σ i) := by
  have hmeas : ∀ i, Measurable fun p : FlatTorus d × FlatTorus d => heatP d σ i (p.1 - p.2) := by
    intro i
    by_cases hi : i = 0
    · have : (fun p : FlatTorus d × FlatTorus d => heatP d σ i (p.1 - p.2)) = fun _ => 0 := by
        funext p; simp [heatP, hi]
      rw [this]; exact measurable_const
    · exact (heatP_cont hσ d (by omega : 1 ≤ i)).measurable.comp (measurable_fst.sub measurable_snd)
  have hint : ∀ (i : ℕ), 1 ≤ i → ∀ x : FlatTorus d,
      Integrable (fun y : FlatTorus d => heatP d σ i (x - y)) (flatTorusMeasure d) := by
    intro i hi x
    refine Integrable.of_bound (((heatP_cont hσ d hi).measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable) (torusM d σ i)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (heatP_nonneg hσ d i _)]
    exact heatP_le hσ d hi _
  refine
    { meas := hmeas
      nonneg := fun i x y => heatP_nonneg hσ d i _
      bound := fun x y => heatP_le hσ d le_rfl _
      mass := ?_
      semi := ?_
      diag := ?_
      M_ge := torusM_ge_one hσ d le_rfl
      m_nonneg := fun i hi => (torusM_pos hσ d hi).le
      m_le := fun i hi => torusM_anti hσ d le_rfl hi }
  · intro z
    have e : ∀ y : FlatTorus d, heatP d σ 1 (y - z) = heatP d σ 1 (z - y) :=
      fun y => heatP_flip d σ 1 y z
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint 1 le_rfl z)
      (Filter.Eventually.of_forall fun y => heatP_nonneg hσ d 1 _), heatP_mass hσ d le_rfl z,
      ENNReal.ofReal_one]
  · intro i j x z hi hj
    simp_rw [← ENNReal.ofReal_mul (heatP_nonneg hσ d i _)]
    have hprod : Integrable (fun y : FlatTorus d => heatP d σ i (x - y) * heatP d σ j (y - z))
        (flatTorusMeasure d) := by
      refine Integrable.of_bound ((((heatP_cont hσ d hi).measurable.comp
        (measurable_const.sub measurable_id)).mul ((heatP_cont hσ d hj).measurable.comp
        (measurable_id.sub measurable_const))).aestronglyMeasurable)
        (torusM d σ i * torusM d σ j) (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (heatP_nonneg hσ d i _) (heatP_nonneg hσ d j _))]
      exact mul_le_mul (heatP_le hσ d hi _) (heatP_le hσ d hj _) (heatP_nonneg hσ d j _)
        (torusM_pos hσ d hi).le
    rw [← ofReal_integral_eq_lintegral_ofReal hprod
      (Filter.Eventually.of_forall fun y =>
        mul_nonneg (heatP_nonneg hσ d i _) (heatP_nonneg hσ d j _)), heatP_semi hσ d hi hj x z]
  · intro i x hi
    show heatP d σ i (x - x) = torusM d σ i
    rw [sub_self, heatP_zero d σ hi]

/-- **Lemma "oraclemoments" on the flat torus, every `k ≥ 1`.** Independent uniform points,
    `p = pker d σ` the periodised Gaussian kernel of variance `σ`, `M = p(0) = m₁`,
    `P̃_{ab} = p(X_a - X_b)/N`. If `k² M ≤ N` then `E |Tr P̃^k - m_k| ≤ 3 k² M²/N`. -/
theorem oraclemoments_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N k : ℕ) (hk : 1 ≤ k)
    (hkN : (k : ℝ) ^ 2 * torusM d σ 1 ≤ N) :
    ∫ ω, |Matrix.trace ((Matrix.of fun a b : Fin N => pker d σ (X a ω - X b ω) / N) ^ k)
        - torusM d σ k| ∂μ ≤ 3 * (k : ℝ) ^ 2 * torusM d σ 1 ^ 2 / N := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h := ((torusRK hσ d).oraclemoments X h_indep hX hlaw N n (by exact_mod_cast hkN)).1
  simp only [heatP_one] at h
  push_cast
  exact h

/-- **The bias of `Tr P̃^k` on the flat torus:** `|E Tr P̃^k - m_k| ≤ k² M²/N` if `k² M ≤ N`. -/
theorem oraclemoments_bias_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N k : ℕ) (hk : 1 ≤ k)
    (hkN : (k : ℝ) ^ 2 * torusM d σ 1 ≤ N) :
    |∫ ω, Matrix.trace ((Matrix.of fun a b : Fin N => pker d σ (X a ω - X b ω) / N) ^ k) ∂μ
        - torusM d σ k| ≤ (k : ℝ) ^ 2 * torusM d σ 1 ^ 2 / N := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h := ((torusRK hσ d).oraclemoments X h_indep hX hlaw N n (by exact_mod_cast hkN)).2.1
  simp only [heatP_one] at h
  push_cast
  exact h

/-- **Proposition "oracle" on the flat torus with the Gaussian kernel**, in the regime
    `k² M ≤ N`, `k ≥ 2`: `E (Tr P̃^k - m_k)² ≤ (3 k² M^k/N)²`. -/
theorem oracle_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : ProbabilityTheory.iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N k : ℕ) (hk : 2 ≤ k)
    (hkN : (k : ℝ) ^ 2 * torusM d σ 1 ≤ N) :
    ∫ ω, (Matrix.trace ((Matrix.of fun a b : Fin N => pker d σ (X a ω - X b ω) / N) ^ k)
        - torusM d σ k) ^ 2 ∂μ ≤ (3 * (k : ℝ) ^ 2 * torusM d σ 1 ^ k / N) ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have h := ((torusRK hσ d).oraclemoments X h_indep hX hlaw N n (by exact_mod_cast hkN)).2.2
    (by omega)
  simp only [heatP_one] at h
  push_cast
  exact h

end Torus

end WalkCount


namespace BiasVariance

open PiBound CTG.Reals.TorusReduction

/-! # A60: `prop:bias` and `prop:variance` (Appendix G) on the flat torus with the heat kernel

What is proved here (see the docstrings for the exact statements and the deviations from the
paper):

* `gamma_second_order`, `trace_one_expansion`: Steps 1–3 of the proof of `prop:bias` for `k = 1`
  (deterministic, on the event `max |ε| ≤ δ ≤ 1/8`), with the remainder bounded by `δ · ε²`
  instead of `|ε|³`.
* `BVK`, `BVK.split_pair`, `BVK.mean_E1`, `BVK.mean_E2`, `BVK.mean_EB`, `BVK.mean_BB`: Steps 5, 6
  for the polynomial statistics that occur for `k = 1`, with explicit `O(N⁻²)` remainders.
* `Q1_mean`, `bias_one_general`, `bias_one`: `E Tr P = m₁ + β₁/N + O(√(log N) N^{-3/2})` for the
  NORMALISED walk with self-loops, `β₁ = m₁ (m₄ - 3m₃ + 3m₂ - m₁)`: `prop:bias` for `k = 1`.
* `deg_pair_eq`, `deg_second_moment`, `deg_first_order`, `deg_full_variance`, `var_trace_two`:
  the Hoeffding structure of Step 2 of the proof of `prop:variance` for degenerate two-point
  statistics, in exact form; the exact variance of `Tr P̃²` (`Q_0` for `k = 2`).
* `first_order_vanish`, `trace_pow_first_order`: `E[Tr P^k | X_l] = E Tr P^k` for the normalised
  walk and every `k` (the Hoeffding component of order one vanishes exactly).

NOT proved: `prop:bias` for `k ≥ 2`, the graph without self-loops, `prop:variance` for the
normalised walk (no pair kernel `H_k`, no `v_k`), the remainder `N^{-3/2}` without the factor
`√(log N)`.  Nothing is assumed without proof beyond the stated hypotheses. -/

/-! ## Part 1 (deterministic): Step 2 of `prop:bias` over `ℝ`, with the remainder bound -/

theorem abs_mul_le' {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) : |x * y| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- **Step 2 of `prop:bias` (expansion of `γ_i = u_i / r_i`), with an explicit remainder.**
    `e = ε_i`, `b = (P̃ε)_i`, `s = (P̃ε²)_i`, `z = (P̃ϑ)_i`; `γ (1+e)(1+χ) = 1` with
    `χ = e - b + s + z`.  On `|ε| ≤ δ ≤ 1/8` (which gives the hypotheses on `b`, `s`, `z`):
    `|γ - (1 + φ¹ + φ²)| ≤ 44 δ (e² + s)`, `φ¹ = -2e + b`, `φ² = 3e² - 3eb + b² - s`.
    (In the paper the remainder is bounded by `C₀ ω_i`, `ω_i = |e|³ + (P̃|ε|³)_i`; here by
    `δ (e² + s) ≥ ω_i`, which needs second moments only.) -/
theorem gamma_second_order {e b s z δ γ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (he : |e| ≤ δ) (hb : |b| ≤ 9 / 8 * δ) (hb2 : b ^ 2 ≤ 9 / 8 * s) (hs0 : 0 ≤ s)
    (hs : s ≤ 9 / 8 * δ ^ 2) (hz : |z| ≤ 8 / 7 * δ * s)
    (hγ : γ * ((1 + e) * (1 + (e - b + (s + z)))) = 1) :
    |γ - (1 - 2 * e + b + 3 * e ^ 2 - 3 * e * b + b ^ 2 - s)| ≤ 44 * δ * (e ^ 2 + s) := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = e ^ 2 + s := ⟨_, rfl⟩
  have he2 : 0 ≤ e ^ 2 := _root_.sq_nonneg e
  have hq0 : 0 ≤ q := by rw [hq]; linarith only [he2, hs0]
  have hsq : s ≤ q := by rw [hq]; linarith only [he2]
  have heq : e ^ 2 ≤ q := by rw [hq]; linarith only [hs0]
  have hδq : 0 ≤ δ * q := mul_nonneg hδ0 hq0
  have hδsq : δ * s ≤ δ * q := mul_le_mul_of_nonneg_left hsq hδ0
  have hδs0 : 0 ≤ δ * s := mul_nonneg hδ0 hs0
  have hδ2 : δ ^ 2 ≤ δ / 8 := by
    have := mul_nonneg hδ0 (sub_nonneg.mpr hδ); linarith only [this]
  have hsδ : s ≤ 9 / 64 * δ := by linarith only [hs, hδ2]
  have hδs : δ * s ≤ s / 8 := by
    have := mul_le_mul_of_nonneg_right hδ hs0; linarith only [this]
  have hzs : |z| ≤ s / 7 := by linarith only [hz, hδs]
  obtain ⟨hz1, hz2⟩ := abs_le.mp hzs
  obtain ⟨he1, he3⟩ := abs_le.mp he
  obtain ⟨hb1, hb3⟩ := abs_le.mp hb
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = s + z := ⟨_, rfl⟩
  have hσ : |w| ≤ 8 / 7 * s := by rw [hw, abs_le]; constructor <;> linarith only [hz1, hz2, hs0]
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = e - b + w := ⟨_, rfl⟩
  obtain ⟨hw1, hw2⟩ := abs_le.mp hσ
  have hχ1 : |χ| ≤ 5 / 2 * δ := by rw [hχ, abs_le]; constructor <;> linarith only [he1, he3, hb1, hb3, hw1, hw2, hsδ, hδ0]
  have hw2' : w ^ 2 ≤ (8 / 7 * s) ^ 2 := sq_le_sq' hw1 hw2
  have hss : s ^ 2 ≤ 9 / 64 * (δ * s) := by
    have := mul_le_mul_of_nonneg_right hsδ hs0; linarith only [this]
  have hχ2 : χ ^ 2 ≤ 5 * q := by
    have h3 : (e - b + w) ^ 2 ≤ 3 * e ^ 2 + 3 * b ^ 2 + 3 * w ^ 2 := by
      linarith only [_root_.sq_nonneg (e + b), _root_.sq_nonneg (e - w), _root_.sq_nonneg (b + w)]
    rw [hχ, hq]; linarith only [h3, hw2', hss, hb2, he2, hδs0, hδs, hs0]
  have hχ2a : |χ ^ 2| ≤ 5 * q := by rw [abs_of_nonneg (_root_.sq_nonneg χ)]; exact hχ2
  obtain ⟨hχl, hχu⟩ := abs_le.mp hχ1
  have h1e : 7 / 8 ≤ 1 + e := by linarith only [he1, hδ]
  have h1χ : 11 / 16 ≤ 1 + χ := by linarith only [hχl, hδ]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (1 + e) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1 + χ) := ⟨_, rfl⟩
  have ha1 : a * (1 + e) = 1 := by rw [ha]; exact one_div_mul_cancel (by linarith only [h1e])
  have hc1 : c * (1 + χ) = 1 := by rw [hc]; exact one_div_mul_cancel (by linarith only [h1χ])
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg zero_le_one (by linarith only [h1e])
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg zero_le_one (by linarith only [h1χ])
  have ha8 : a ≤ 8 / 7 := by
    have := mul_le_mul_of_nonneg_left h1e ha0; linarith only [this, ha1]
  have hc8 : c ≤ 16 / 11 := by
    have := mul_le_mul_of_nonneg_left h1χ hc0; linarith only [this, hc1]
  have hγac : γ = a * c := by
    have h : γ * ((1 + e) * (1 + χ)) = 1 := by rw [hχ, hw]; exact hγ
    calc γ = γ * ((a * (1 + e)) * (c * (1 + χ))) := by rw [ha1, hc1]; ring
      _ = (γ * ((1 + e) * (1 + χ))) * (a * c) := by ring
      _ = a * c := by rw [h]; ring
  have hA : a = 1 - e + e ^ 2 - e ^ 3 * a := by linear_combination (1 - e + e ^ 2) * ha1
  have hC : c = 1 - χ + χ ^ 2 - χ ^ 3 * c := by linear_combination (1 - χ + χ ^ 2) * hc1
  have hdec : γ - (1 - 2 * e + b + 3 * e ^ 2 - 3 * e * b + b ^ 2 - s)
      = (-z + w ^ 2 + 3 * e * w - 2 * b * w - e * χ ^ 2 - e ^ 2 * χ + e ^ 2 * χ ^ 2)
        - (1 - e + e ^ 2) * (χ * χ ^ 2 * c) - e * e ^ 2 * (a * c) := by
    rw [hγac]
    subst hχ
    subst hw
    linear_combination c * hA + (1 - e + e ^ 2) * hC
  have b1 : |z| ≤ 8 / 7 * (δ * q) := by linarith only [hz, hδsq]
  have b2 : |w ^ 2| ≤ δ * q := by
    rw [abs_of_nonneg (_root_.sq_nonneg w)]; linarith only [hw2', hss, hδsq, hδs0]
  have b3 : |3 * e * w| ≤ 4 * (δ * q) := by
    have h := abs_mul_le' (x := 3 * e) (y := w) (A := 3 * δ) (B := 8 / 7 * s)
      (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; linarith only [he]) hσ
    linarith only [h, hδsq, hδs0]
  have b4 : |2 * b * w| ≤ 3 * (δ * q) := by
    have h := abs_mul_le' (x := 2 * b) (y := w) (A := 9 / 4 * δ) (B := 8 / 7 * s)
      (by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith only [hb]) hσ
    linarith only [h, hδsq, hδs0]
  have b5 : |e * χ ^ 2| ≤ 5 * (δ * q) := by
    have h := abs_mul_le' he hχ2a
    linarith only [h]
  have he2a : |e ^ 2| ≤ q := by rw [abs_of_nonneg he2]; exact heq
  have b6 : |e ^ 2 * χ| ≤ 3 * (δ * q) := by
    have h := abs_mul_le' he2a hχ1
    linarith only [h, hδq]
  have hχ2b : |χ ^ 2| ≤ 25 / 32 * δ := by
    rw [abs_of_nonneg (_root_.sq_nonneg χ)]
    have : χ ^ 2 ≤ (5 / 2 * δ) ^ 2 := sq_le_sq' hχl hχu
    linarith only [this, hδ2]
  have b7 : |e ^ 2 * χ ^ 2| ≤ δ * q := by
    have h := abs_mul_le' he2a hχ2b
    linarith only [h, hδq]
  have hU : |1 - e + e ^ 2| ≤ 5 / 4 := by
    have hee : e ^ 2 ≤ (1 / 8) ^ 2 := sq_le_sq' (by linarith only [he1, hδ]) (by linarith only [he3, hδ])
    rw [abs_le]; constructor <;> linarith only [he1, he3, hδ, he2, hee]
  have hca : |c| ≤ 16 / 11 := by rw [abs_of_nonneg hc0]; exact hc8
  have b8 : |(1 - e + e ^ 2) * (χ * χ ^ 2 * c)| ≤ 23 * (δ * q) := by
    have h1 := abs_mul_le' (abs_mul_le' hχ1 hχ2a) hca
    have h2 := abs_mul_le' hU h1
    linarith only [h2, hδq]
  have hac : |a * c| ≤ 8 / 7 * (16 / 11) := by
    apply abs_mul_le' _ hca
    rw [abs_of_nonneg ha0]; exact ha8
  have b9 : |e * e ^ 2 * (a * c)| ≤ 2 * (δ * q) := by
    have h := abs_mul_le' (abs_mul_le' he he2a) hac
    linarith only [h, hδq]
  rw [hdec, ← hq]
  obtain ⟨l1, u1⟩ := abs_le.mp b1
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  obtain ⟨l3, u3⟩ := abs_le.mp b3
  obtain ⟨l4, u4⟩ := abs_le.mp b4
  obtain ⟨l5, u5⟩ := abs_le.mp b5
  obtain ⟨l6, u6⟩ := abs_le.mp b6
  obtain ⟨l7, u7⟩ := abs_le.mp b7
  obtain ⟨l8, u8⟩ := abs_le.mp b8
  obtain ⟨l9, u9⟩ := abs_le.mp b9
  rw [abs_le]
  constructor <;> linarith only [l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8, l9, u9]

/-! ## Part 2 (deterministic): the trace of the normalised walk for `k = 1` in second order -/

/-- Bounds for one row of the kernel matrix (`k l = K_il ≥ 0`, row sum `N ρ`, `|ε| ≤ δ ≤ 1/8`):
    `b = (P̃ε)_i`, `s = (P̃ε²)_i`, `z = (P̃ϑ)_i` with `ϑ_l = 1/(1+ε_l) - (1 - ε_l + ε_l²)`. -/
theorem row_bounds {N : ℕ} (hN : 0 < N) (k ε : Fin N → ℝ) {δ ρ : ℝ} (hk : ∀ l, 0 ≤ k l)
    (hδ : δ ≤ 1 / 8) (hεδ : ∀ l, |ε l| ≤ δ) (hsum : ∑ l, k l = N * ρ) (hρ : ρ ≤ 9 / 8) :
    |1 / (N : ℝ) * ∑ l, k l * ε l| ≤ 9 / 8 * δ
    ∧ (1 / (N : ℝ) * ∑ l, k l * ε l) ^ 2 ≤ 9 / 8 * (1 / (N : ℝ) * ∑ l, k l * ε l ^ 2)
    ∧ 0 ≤ 1 / (N : ℝ) * ∑ l, k l * ε l ^ 2
    ∧ 1 / (N : ℝ) * ∑ l, k l * ε l ^ 2 ≤ 9 / 8 * δ ^ 2
    ∧ |1 / (N : ℝ) * ∑ l, k l * (1 / (1 + ε l) - (1 - ε l + ε l ^ 2))|
        ≤ 8 / 7 * δ * (1 / (N : ℝ) * ∑ l, k l * ε l ^ 2)
    ∧ 1 / (N : ℝ) * ∑ l, k l / (1 + ε l)
        = ρ - 1 / (N : ℝ) * ∑ l, k l * ε l + (1 / (N : ℝ) * ∑ l, k l * ε l ^ 2
            + 1 / (N : ℝ) * ∑ l, k l * (1 / (1 + ε l) - (1 - ε l + ε l ^ 2))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  have hδ0 : 0 ≤ δ := (abs_nonneg (ε ⟨0, hN⟩)).trans (hεδ _)
  have hl : ∀ l, -δ ≤ ε l ∧ ε l ≤ δ := fun l => abs_le.mp (hεδ l)
  have hS0 : 0 ≤ ∑ l, k l := Finset.sum_nonneg fun l _ => hk l
  have hρ0 : 0 ≤ ρ := by
    by_contra h
    have h' : ρ < 0 := not_le.mp h
    have := mul_neg_of_pos_of_neg hNpos h'
    linarith only [this, hsum, hS0]
  have hinvS : 1 / (N : ℝ) * ∑ l, k l = ρ := by rw [hsum]; field_simp
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ l, k l * ε l := ⟨_, rfl⟩
  obtain ⟨S2, hS2⟩ : ∃ S2 : ℝ, S2 = ∑ l, k l * ε l ^ 2 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∑ l, k l * (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)) := ⟨_, rfl⟩
  rw [← hA, ← hS2, ← hZ]
  have hS2n : 0 ≤ S2 := by
    rw [hS2]; exact Finset.sum_nonneg fun l _ => mul_nonneg (hk l) (_root_.sq_nonneg _)
  have hε2 : ∀ l, ε l ^ 2 ≤ δ ^ 2 := fun l => sq_le_sq' (hl l).1 (hl l).2
  have hA1 : A ≤ δ * ∑ l, k l := by
    rw [hA, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => by
      have := mul_le_mul_of_nonneg_left (hl l).2 (hk l); linarith only [this]
  have hA2 : -(δ * ∑ l, k l) ≤ A := by
    rw [hA, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun l _ => by
      have := mul_le_mul_of_nonneg_left (hl l).1 (hk l); linarith only [this]
  have hAsq : A ^ 2 ≤ (∑ l, k l) * S2 := by
    rw [hA, hS2]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun l _ => hk l)
      (fun l _ => mul_nonneg (hk l) (_root_.sq_nonneg _)) (fun l _ => by ring)
  have hS2le : S2 ≤ δ ^ 2 * ∑ l, k l := by
    rw [hS2, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => by
      have := mul_le_mul_of_nonneg_left (hε2 l) (hk l); linarith only [this]
  have hϑ : ∀ l, |1 / (1 + ε l) - (1 - ε l + ε l ^ 2)| ≤ 8 / 7 * δ * ε l ^ 2 := by
    intro l
    have h1 : 7 / 8 ≤ 1 + ε l := by linarith only [(hl l).1, hδ]
    have hne : 1 + ε l ≠ 0 := by linarith only [h1]
    have e1 : (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)) * (1 + ε l) = -(ε l * ε l ^ 2) := by
      field_simp; ring
    have e2 : |1 / (1 + ε l) - (1 - ε l + ε l ^ 2)| * (1 + ε l) = |ε l| * ε l ^ 2 := by
      have := congrArg abs e1
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (_root_.sq_nonneg (ε l)),
        abs_of_pos (by linarith only [h1] : 0 < 1 + ε l)] at this
      exact this
    have e3 : |ε l| * ε l ^ 2 ≤ δ * ε l ^ 2 :=
      mul_le_mul_of_nonneg_right (hεδ l) (_root_.sq_nonneg _)
    have e4 := mul_le_mul_of_nonneg_left h1 (abs_nonneg (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)))
    linarith only [e2, e3, e4]
  have hZle : |Z| ≤ 8 / 7 * δ * S2 := by
    rw [hZ, hS2, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul, abs_of_nonneg (hk l)]
    have := mul_le_mul_of_nonneg_left (hϑ l) (hk l)
    linarith only [this]
  have hδρ : δ * ρ ≤ 9 / 8 * δ := by
    have := mul_le_mul_of_nonneg_left hρ hδ0; linarith only [this]
  have hSρ : ρ * (1 / (N : ℝ) * S2) ≤ 9 / 8 * (1 / (N : ℝ) * S2) :=
    mul_le_mul_of_nonneg_right hρ (mul_nonneg hinv.le hS2n)
  refine ⟨?_, ?_, mul_nonneg hinv.le hS2n, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hinv]
    have h : |A| ≤ δ * ∑ l, k l := abs_le.mpr ⟨hA2, hA1⟩
    have h2 := mul_le_mul_of_nonneg_left h hinv.le
    have e : 1 / (N : ℝ) * (δ * ∑ l, k l) = δ * ρ := by rw [← hinvS]; ring
    linarith only [h2, e, hδρ]
  · have h2 := mul_le_mul_of_nonneg_left hAsq (mul_nonneg hinv.le hinv.le)
    have e : 1 / (N : ℝ) * (1 / (N : ℝ)) * ((∑ l, k l) * S2) = ρ * (1 / (N : ℝ) * S2) := by
      rw [← hinvS]; ring
    have e' : (1 / (N : ℝ) * A) ^ 2 = 1 / (N : ℝ) * (1 / (N : ℝ)) * A ^ 2 := by ring
    linarith only [h2, e, e', hSρ]
  · have h2 := mul_le_mul_of_nonneg_left hS2le hinv.le
    have e : 1 / (N : ℝ) * (δ ^ 2 * ∑ l, k l) = δ ^ 2 * ρ := by rw [← hinvS]; ring
    have h3 := mul_le_mul_of_nonneg_left hρ (_root_.sq_nonneg δ)
    linarith only [h2, e, h3]
  · rw [abs_mul, abs_of_pos hinv]
    have h2 := mul_le_mul_of_nonneg_left hZle hinv.le
    linarith only [h2]
  · have e : ∑ l, k l / (1 + ε l) = (∑ l, k l) - A + (S2 + Z) := by
      rw [hA, hS2, hZ, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by rw [div_eq_mul_one_div]; ring
    rw [e, ← hinvS]; ring

/-- **`k = 1`, deterministic: the trace of the normalised walk in second order.** `K` symmetric,
    nonnegative, constant diagonal `m` (self-loops), `ρ_i = (1/N) ∑_l K_il = 1 + ε_i`,
    `|ε_i| ≤ δ ≤ 1/8`, `b_i = (P̃ε)_i = (1/N) ∑_l K_il ε_l`.  Then
    `|Tr P - m (1 - ε̄ + (1/N) ∑_i (3ε_i² - 3ε_i b_i + b_i²))| ≤ 95 m δ (1/N) ∑_i ε_i²`.
    (Steps 1–3 of the proof of `prop:bias` for `k = 1`, where `Q_3 = 0`; the terms `(P̃ε)_i` and
    `(P̃ε²)_i` of `φ¹`, `φ²` are summed over `i` with the column sums of `K`.) -/
theorem trace_one_expansion {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ) (ρ ε : Fin N → ℝ)
    {m δ : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i) (hd : ∀ i, K i i = m)
    (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1) (hm : 0 ≤ m)
    (hδ : δ ≤ 1 / 8) (hεδ : ∀ i, |ε i| ≤ δ) :
    |(walkMatrix K ρ).trace
        - m * (1 - 1 / (N : ℝ) * ∑ i, ε i
            + 1 / (N : ℝ) * ∑ i, (3 * ε i ^ 2 - 3 * ε i * (1 / (N : ℝ) * ∑ l, K i l * ε l)
                + (1 / (N : ℝ) * ∑ l, K i l * ε l) ^ 2))|
      ≤ 95 * m * δ * (1 / (N : ℝ) * ∑ i, ε i ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  have hδ0 : 0 ≤ δ := (abs_nonneg (ε ⟨0, hN⟩)).trans (hεδ _)
  have hl : ∀ l, -δ ≤ ε l ∧ ε l ≤ δ := fun l => abs_le.mp (hεδ l)
  have hρe : ∀ l, ρ l = 1 + ε l := fun l => by rw [hε l]; ring
  have hρlo : ∀ l, 7 / 8 ≤ ρ l := fun l => by rw [hρe l]; linarith only [(hl l).1, hδ]
  have hρhi : ∀ l, ρ l ≤ 9 / 8 := fun l => by rw [hρe l]; linarith only [(hl l).2, hδ]
  obtain ⟨bv, hbv⟩ : ∃ bv : Fin N → ℝ, bv = fun i => 1 / (N : ℝ) * ∑ l, K i l * ε l := ⟨_, rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : Fin N → ℝ, sv = fun i => 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨Qf, hQf⟩ : ∃ Qf : Fin N → ℝ,
      Qf = fun i => 3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 := ⟨_, rfl⟩
  have hrow : ∀ i, ∃ γ : ℝ, walkMatrix K ρ i i = m / N * γ
      ∧ |γ - (1 - 2 * ε i + bv i + Qf i - sv i)| ≤ 44 * δ * (ε i ^ 2 + sv i) := by
    intro i
    have H := row_bounds hN (K i) ε (fun l => hK0 i l) hδ hεδ (hρ i) (hρhi i)
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 / (N : ℝ) * ∑ l, K i l * ε l := ⟨_, rfl⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2 := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z : ℝ,
        z = 1 / (N : ℝ) * ∑ l, K i l * (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)) := ⟨_, rfl⟩
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 / (N : ℝ) * ∑ l, K i l / (1 + ε l) := ⟨_, rfl⟩
    rw [← hb, ← hs, ← hz, ← hR] at H
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
    have hbi : bv i = b := by rw [hbv, hb]
    have hsi : sv i = s := by rw [hsv, hs]
    obtain ⟨hz1, hz2⟩ := abs_le.mp h5
    obtain ⟨hb1, hb2⟩ := abs_le.mp h1
    have hδs : δ * s ≤ 1 / 8 * s := mul_le_mul_of_nonneg_right hδ h3
    have hRpos : 0 < R := by
      rw [h6]; linarith only [hρlo i, hb2, hδ, hz1, hδs, h3]
    have hρi : ρ i ≠ 0 := by linarith only [hρlo i]
    have hsumR : ∑ l, K i l / ρ l = N * R := by
      rw [hR]
      have : ∑ l, K i l / ρ l = ∑ l, K i l / (1 + ε l) :=
        Finset.sum_congr rfl fun l _ => by rw [hρe l]
      rw [this]; field_simp
    refine ⟨1 / ρ i / R, ?_, ?_⟩
    · rw [walkMatrix_apply' K ρ i i hρi, hsumR, hd i]
      field_simp
    · have hQi : Qf i = 3 * ε i ^ 2 - 3 * ε i * b + b ^ 2 := by rw [hQf, ← hbi]
      rw [hQi, hbi, hsi]
      have hγ : 1 / ρ i / R * ((1 + ε i) * (1 + (ε i - b + (s + z)))) = 1 := by
        have e : 1 + (ε i - b + (s + z)) = R := by rw [h6, hρe i]; ring
        rw [e, ← hρe i]
        field_simp
      have h := gamma_second_order hδ0 hδ (hεδ i) h1 h2 h3 h4 h5 hγ
      have e2 : 1 - 2 * ε i + b + (3 * ε i ^ 2 - 3 * ε i * b + b ^ 2) - s
          = 1 - 2 * ε i + b + 3 * ε i ^ 2 - 3 * ε i * b + b ^ 2 - s := by ring
      rw [e2]; exact h
  choose γ hγ1 hγ2 using hrow
  -- column sums
  have hcol : ∀ f : Fin N → ℝ,
      ∑ i, 1 / (N : ℝ) * ∑ l, K i l * f l = ∑ l, ρ l * f l := by
    intro f
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i, K i l = N * ρ l := by
      rw [← hρ l]; exact Finset.sum_congr rfl fun i _ => hsym i l
    rw [this]; field_simp
  obtain ⟨Se, hSe⟩ : ∃ Se : ℝ, Se = ∑ i, ε i := ⟨_, rfl⟩
  obtain ⟨Se2, hSe2⟩ : ∃ Se2 : ℝ, Se2 = ∑ i, ε i ^ 2 := ⟨_, rfl⟩
  obtain ⟨Se3, hSe3⟩ : ∃ Se3 : ℝ, Se3 = ∑ i, ε i ^ 3 := ⟨_, rfl⟩
  obtain ⟨SQ, hSQ⟩ : ∃ SQ : ℝ, SQ = ∑ i, Qf i := ⟨_, rfl⟩
  have hSb : ∑ i, bv i = Se + Se2 := by
    rw [hbv, hcol ε, hSe, hSe2, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hρe l]; ring
  have hSs : ∑ i, sv i = Se2 + Se3 := by
    rw [hsv, hcol (fun l => ε l ^ 2), hSe2, hSe3, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hρe l]; ring
  have hST : ∑ i, (1 - 2 * ε i + bv i + Qf i - sv i) = N - Se + SQ - Se3 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
    rw [hSb, hSs, ← hSe, ← hSQ]; ring
  have htr : (walkMatrix K ρ).trace = m / N * ∑ i, γ i := by
    simp only [Matrix.trace, Matrix.diag_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hγ1 i
  have hgoal : (walkMatrix K ρ).trace
        - m * (1 - 1 / (N : ℝ) * ∑ i, ε i
            + 1 / (N : ℝ) * ∑ i, (3 * ε i ^ 2 - 3 * ε i * (1 / (N : ℝ) * ∑ l, K i l * ε l)
                + (1 / (N : ℝ) * ∑ l, K i l * ε l) ^ 2))
      = m / N * (∑ i, (γ i - (1 - 2 * ε i + bv i + Qf i - sv i)) - Se3) := by
    have eQ : ∑ i, (3 * ε i ^ 2 - 3 * ε i * (1 / (N : ℝ) * ∑ l, K i l * ε l)
                + (1 / (N : ℝ) * ∑ l, K i l * ε l) ^ 2) = SQ := by
      rw [hSQ, hQf, hbv]
    rw [eQ, htr, Finset.sum_sub_distrib, hST, ← hSe]
    field_simp; ring
  rw [hgoal]
  have hSe2n : 0 ≤ Se2 := by rw [hSe2]; exact Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
  have hSs2 : ∑ i, sv i ≤ 9 / 8 * Se2 := by
    rw [hsv, hcol (fun l => ε l ^ 2), hSe2, Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hρhi l) (_root_.sq_nonneg _)
  have hG : |∑ i, (γ i - (1 - 2 * ε i + bv i + Qf i - sv i))| ≤ 44 * δ * (Se2 + ∑ i, sv i) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hSe2, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hγ2 i
  have h3 : |Se3| ≤ δ * Se2 := by
    rw [hSe3, hSe2, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have e : ε i ^ 3 = ε i * ε i ^ 2 := by ring
    rw [e, abs_mul, abs_of_nonneg (_root_.sq_nonneg (ε i))]
    exact mul_le_mul_of_nonneg_right (hεδ i) (_root_.sq_nonneg _)
  have hmN : 0 ≤ m / N := div_nonneg hm hNpos.le
  rw [abs_mul, abs_of_nonneg hmN]
  obtain ⟨g1, g2⟩ := abs_le.mp hG
  obtain ⟨t1, t2⟩ := abs_le.mp h3
  have hδS : 0 ≤ δ * Se2 := mul_nonneg hδ0 hSe2n
  have hδSs := mul_le_mul_of_nonneg_left hSs2 hδ0
  have hfin : |∑ i, (γ i - (1 - 2 * ε i + bv i + Qf i - sv i)) - Se3| ≤ 95 * (δ * Se2) := by
    rw [abs_le]; constructor <;> linarith only [g1, g2, t1, t2, hδS, hδSs]
  have := mul_le_mul_of_nonneg_left hfin hmN
  have e : m / N * (95 * (δ * Se2)) = 95 * m * δ * (1 / (N : ℝ) * Se2) := by ring
  rw [← hSe2, ← e]; exact this

/-! ## Part 3: expectations of the polynomial statistics (Steps 5, 6 of `prop:bias`, `k = 1`) -/

/-- Hypotheses for the expectations: independent points `X_j` with law `ν` on a group `G`;
    `c = p - 1` measurable, even, bounded, `∫ c(x - z) dν(z) = 0`,
    `∫ c(x - z) c(y - z) dν(z) = κ₂(x - y)` (so `κ₂ = p₂ - 1`), and the two constants
    `c3 = ∫ p κ₂ = m₃ - 1`, `c4 = ∫ p₂ κ₂ = m₄ - 1`; everything bounded by `B ≥ 1`. -/
structure BVK {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) {G : Type*} [AddCommGroup G]
    [MeasurableSpace G] (ν : Measure G) (X : ℕ → Ω → G) (c κ₂ : G → ℝ) (B c3 c4 : ℝ) :
    Prop where
  indep : iIndepFun X μ
  meas : ∀ j, Measurable (X j)
  law : ∀ j, μ.map (X j) = ν
  c_meas : Measurable c
  k_meas : Measurable κ₂
  B_one : 1 ≤ B
  bound : ∀ u, |c u| ≤ B
  gbound : ∀ u, |1 + c u| ≤ B
  kbound : ∀ u, |κ₂ u| ≤ B
  even : ∀ u, c (-u) = c u
  mean : ∀ x, ∫ z, c (x - z) ∂ν = 0
  conv : ∀ x y, ∫ z, c (x - z) * c (y - z) ∂ν = κ₂ (x - y)
  three : ∀ x, ∫ z, (1 + c (x - z)) * κ₂ (x - z) ∂ν = c3
  four : ∀ x, ∫ z, (1 + κ₂ (x - z)) * κ₂ (x - z) ∂ν = c4
  c3b : |c3| ≤ B
  c4b : |c4| ≤ B

namespace BVK

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {c κ₂ : G → ℝ}
  {B c3 c4 : ℝ}

omit [MeasurableSub₂ G] in
theorem B_nonneg (H : BVK μ ν X c κ₂ B c3 c4) : 0 ≤ B := zero_le_one.trans H.B_one

omit [MeasurableSub₂ G] in
/-- One point is independent of the tuple of the points over a finite set not containing it. -/
theorem indep_tuple (H : BVK μ ν X c κ₂ B c3 c4) (T : Finset ℕ) (v : ℕ) (hv : v ∉ T) :
    IndepFun (X v) (fun ω (t : T) => X t ω) μ := by
  have hind0 := H.indep.indepFun_finset {v} T (Finset.disjoint_singleton_left.mpr hv) H.meas
  exact hind0.comp (φ := fun u : (({v} : Finset ℕ) → G) => u ⟨v, Finset.mem_singleton_self v⟩)
    (ψ := id) (measurable_pi_apply _) measurable_id

omit [MeasurableSub₂ G] in
theorem bmF (H : BVK μ ν X c κ₂ B c3 c4) (T : Finset ℕ) (F : (T → G) → ℝ) (hF : Measurable F)
    {BF : ℝ} (hFb : ∀ y, |F y| ≤ BF) : BM (fun ω => F (fun t : T => X t ω)) :=
  ⟨hF.comp (measurable_pi_lambda _ fun t => H.meas t), BF, fun _ => hFb _⟩

theorem bmc (H : BVK μ ν X c κ₂ B c3 c4) (i j : ℕ) : BM (fun ω => c (X i ω - X j ω)) :=
  ⟨H.c_meas.comp ((H.meas i).sub (H.meas j)), B, fun _ => H.bound _⟩

theorem bmk (H : BVK μ ν X c κ₂ B c3 c4) (i j : ℕ) : BM (fun ω => κ₂ (X i ω - X j ω)) :=
  ⟨H.k_meas.comp ((H.meas i).sub (H.meas j)), B, fun _ => H.kbound _⟩

/-- Rule (b) of Step 5: a `c`-edge to a free index. -/
theorem tail_single [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (T : Finset ℕ) (a : T) (v : ℕ) (hv : v ∉ T)
    (F : (T → G) → ℝ) (hF : Measurable F) {BF : ℝ} (hFb : ∀ y, |F y| ≤ BF) :
    ∫ ω, F (fun t : T => X t ω) * c (X a ω - X v ω) ∂μ = 0 := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hFb (fun _ => 0))
  have hc := H.c_meas
  exact indep_integral_zero ν (X v) (fun ω (t : T) => X t ω) (H.meas v)
    (measurable_pi_lambda _ fun t => H.meas t) (H.indep_tuple T v hv) (H.law v)
    (fun p : G × (T → G) => F p.2 * c (p.2 a - p.1))
    ((hF.comp measurable_snd).mul
      (hc.comp (((measurable_pi_apply a).comp measurable_snd).sub measurable_fst)))
    (B := BF * B)
    (fun p => by rw [abs_mul]; exact mul_le_mul (hFb _) (H.bound _) (abs_nonneg _) hBF)
    (fun y => by
      show ∫ z, F y * c (y a - z) ∂ν = 0
      rw [integral_const_mul, H.mean, mul_zero])

/-- Two `c`-edges to the same free index: integrate that point (`∫ c c = κ₂`). -/
theorem tail_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (T : Finset ℕ) (a b : T) (v : ℕ) (hv : v ∉ T)
    (F : (T → G) → ℝ) (hF : Measurable F) {BF : ℝ} (hFb : ∀ y, |F y| ≤ BF) :
    ∫ ω, F (fun t : T => X t ω) * (c (X a ω - X v ω) * c (X b ω - X v ω)) ∂μ
      = ∫ ω, F (fun t : T => X t ω) * κ₂ (X a ω - X b ω) ∂μ := by
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hFb (fun _ => 0))
  have hB := H.B_nonneg
  have hc := H.c_meas
  have hYm : Measurable (fun ω (t : T) => X t ω) := measurable_pi_lambda _ fun t => H.meas t
  have ea : Measurable fun p : G × (T → G) => p.2 a :=
    (measurable_pi_apply a).comp measurable_snd
  have eb : Measurable fun p : G × (T → G) => p.2 b :=
    (measurable_pi_apply b).comp measurable_snd
  have h1 := indep_integral_eq ν (X v) (fun ω (t : T) => X t ω) (H.meas v) hYm
    (H.indep_tuple T v hv) (H.law v)
    (fun p : G × (T → G) => F p.2 * (c (p.2 a - p.1) * c (p.2 b - p.1)))
    ((hF.comp measurable_snd).mul
      ((hc.comp (ea.sub measurable_fst)).mul (hc.comp (eb.sub measurable_fst))))
    (B := BF * (B * B))
    (fun p => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hFb _) (mul_le_mul (H.bound _) (H.bound _) (abs_nonneg _) hB)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hBF)
  have h2 : ∀ y : T → G,
      ∫ z, F y * (c (y a - z) * c (y b - z)) ∂ν = F y * κ₂ (y a - y b) := fun y => by
    rw [integral_const_mul, H.conv]
  have h3 : ∫ y, F y * κ₂ (y a - y b) ∂(μ.map fun ω (t : T) => X t ω)
      = ∫ ω, F (fun t : T => X t ω) * κ₂ (X a ω - X b ω) ∂μ :=
    integral_map hYm.aemeasurable
      (hF.mul (H.k_meas.comp ((measurable_pi_apply a).sub
        (measurable_pi_apply b)))).aestronglyMeasurable
  rw [← h3]
  refine h1.trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall h2)

/-- Two `c`-edges to different indices, one of them free: the mean vanishes. -/
theorem tail_ne [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (T : Finset ℕ) (a b : T) (v v' : ℕ) (hv : v ∉ T)
    (hvv : v ≠ v') (F : (T → G) → ℝ) (hF : Measurable F) {BF : ℝ} (hFb : ∀ y, |F y| ≤ BF) :
    ∫ ω, F (fun t : T => X t ω) * (c (X a ω - X v ω) * c (X b ω - X v' ω)) ∂μ = 0 := by
  classical
  have hBF : 0 ≤ BF := (abs_nonneg _).trans (hFb (fun _ => 0))
  have hB := H.B_nonneg
  have hc := H.c_meas
  obtain ⟨T', hT'⟩ : ∃ T' : Finset ℕ, T' = insert v' T := ⟨_, rfl⟩
  have hsub : ∀ t : T, (t : ℕ) ∈ T' := fun t => by rw [hT']; exact Finset.mem_insert_of_mem t.2
  have hv'T : v' ∈ T' := by rw [hT']; exact Finset.mem_insert_self _ _
  have hvT' : v ∉ T' := by rw [hT', Finset.mem_insert]; exact fun h => h.elim hvv hv
  have er : Measurable fun p : G × (T' → G) => fun t : T => p.2 ⟨t, hsub t⟩ :=
    measurable_pi_lambda _ fun t => (measurable_pi_apply _).comp measurable_snd
  have e1 : Measurable fun p : G × (T' → G) => p.2 ⟨a, hsub a⟩ :=
    (measurable_pi_apply _).comp measurable_snd
  have e2 : Measurable fun p : G × (T' → G) => p.2 ⟨b, hsub b⟩ :=
    (measurable_pi_apply _).comp measurable_snd
  have e3 : Measurable fun p : G × (T' → G) => p.2 ⟨v', hv'T⟩ :=
    (measurable_pi_apply _).comp measurable_snd
  exact indep_integral_zero ν (X v) (fun ω (t : T') => X t ω) (H.meas v)
    (measurable_pi_lambda _ fun t => H.meas t) (H.indep_tuple T' v hvT') (H.law v)
    (fun p : G × (T' → G) => F (fun t : T => p.2 ⟨t, hsub t⟩)
      * (c (p.2 ⟨a, hsub a⟩ - p.1) * c (p.2 ⟨b, hsub b⟩ - p.2 ⟨v', hv'T⟩)))
    ((hF.comp er).mul ((hc.comp (e1.sub measurable_fst)).mul (hc.comp (e2.sub e3))))
    (B := BF * (B * B))
    (fun p => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hFb _) (mul_le_mul (H.bound _) (H.bound _) (abs_nonneg _) hB)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hBF)
    (fun y => by
      show ∫ z, F (fun t : T => y ⟨t, hsub t⟩)
        * (c (y ⟨a, hsub a⟩ - z) * c (y ⟨b, hsub b⟩ - y ⟨v', hv'T⟩)) ∂ν = 0
      have e : ∀ z, F (fun t : T => y ⟨t, hsub t⟩)
            * (c (y ⟨a, hsub a⟩ - z) * c (y ⟨b, hsub b⟩ - y ⟨v', hv'T⟩))
          = F (fun t : T => y ⟨t, hsub t⟩) * c (y ⟨b, hsub b⟩ - y ⟨v', hv'T⟩)
            * c (y ⟨a, hsub a⟩ - z) := fun z => by ring
      simp_rw [e]
      rw [integral_const_mul, H.mean, mul_zero])

/-- The tail sum `∑_{v ∈ R} c(X_a - X_v)` over indices outside `T` has conditional mean zero. -/
theorem tail_sum_single [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (T : Finset ℕ) (a : T) (R : Finset ℕ)
    (hR : ∀ v ∈ R, v ∉ T) (F : (T → G) → ℝ) (hF : Measurable F) {BF : ℝ}
    (hFb : ∀ y, |F y| ≤ BF) :
    ∫ ω, F (fun t : T => X t ω) * ∑ v ∈ R, c (X a ω - X v ω) ∂μ = 0 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ (fun v _ => ((H.bmF T F hF hFb).mul (H.bmc a v)).integrable)]
  exact Finset.sum_eq_zero fun v hv => H.tail_single T a v (hR v hv) F hF hFb

/-- The product of two tail sums: only the diagonal `v = v'` survives, and each diagonal term
    is `E[F κ₂(X_a - X_b)]`. -/
theorem tail_sum_pair [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (T : Finset ℕ) (a b : T) (R : Finset ℕ)
    (hR : ∀ v ∈ R, v ∉ T) (F : (T → G) → ℝ) (hF : Measurable F) {BF : ℝ}
    (hFb : ∀ y, |F y| ≤ BF) :
    ∫ ω, F (fun t : T => X t ω)
        * ((∑ v ∈ R, c (X a ω - X v ω)) * ∑ v' ∈ R, c (X b ω - X v' ω)) ∂μ
      = (R.card : ℝ) * ∫ ω, F (fun t : T => X t ω) * κ₂ (X a ω - X b ω) ∂μ := by
  classical
  have hint : ∀ v v', Integrable (fun ω => F (fun t : T => X t ω)
      * (c (X a ω - X v ω) * c (X b ω - X v' ω))) μ := fun v v' =>
    ((H.bmF T F hF hFb).mul ((H.bmc a v).mul (H.bmc b v'))).integrable
  have e : ∀ ω, F (fun t : T => X t ω)
        * ((∑ v ∈ R, c (X a ω - X v ω)) * ∑ v' ∈ R, c (X b ω - X v' ω))
      = ∑ v ∈ R, ∑ v' ∈ R, F (fun t : T => X t ω)
          * (c (X a ω - X v ω) * c (X b ω - X v' ω)) := by
    intro ω
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
  simp_rw [e]
  rw [integral_finset_sum _ (fun v _ => integrable_finset_sum _ fun v' _ => hint v v')]
  have e2 : ∀ v ∈ R, ∫ ω, ∑ v' ∈ R, F (fun t : T => X t ω)
        * (c (X a ω - X v ω) * c (X b ω - X v' ω)) ∂μ
      = ∫ ω, F (fun t : T => X t ω) * κ₂ (X a ω - X b ω) ∂μ := by
    intro v hv
    rw [integral_finset_sum _ (fun v' _ => hint v v'), Finset.sum_eq_single v]
    · exact H.tail_eq T a b v (hR v hv) F hF hFb
    · intro v' _ hne
      exact H.tail_ne T a b v v' (hR v hv) (Ne.symm hne) F hF hFb
    · intro h; exact absurd hv h
  rw [Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul]

end BVK

theorem abs_int_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : BM f) {C : ℝ} (h : ∀ ω, |f ω| ≤ C) : |∫ ω, f ω ∂μ| ≤ C := by
  have i := hf.integrable (μ := μ)
  have h1 : ∫ ω, f ω ∂μ ≤ ∫ _ω, C ∂μ :=
    integral_mono i (integrable_const C) fun ω => (abs_le.mp (h ω)).2
  have h2 : ∫ _ω, -C ∂μ ≤ ∫ ω, f ω ∂μ :=
    integral_mono (integrable_const _) i fun ω => (abs_le.mp (h ω)).1
  rw [integral_const, probReal_univ, one_smul] at h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

namespace BVK

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {c κ₂ : G → ℝ}
  {B c3 c4 : ℝ}

theorem bmH (H : BVK μ ν X c κ₂ B c3 c4) (N q : ℕ) : BM (Hrow c X N q) := by
  show BM (fun ω => ∑ v ∈ Finset.range N, c (X q ω - X v ω))
  exact BM.sum _ _ fun v _ => H.bmc q v

/-- **Splitting off the tail.** For `T ⊆ {0,…,N-1}`, `a, b ∈ T` and a bounded measurable function
    `F` of the points over `T`: in `E[F · (Nε_a) · (Nε_b)]` the row sums may be replaced by their
    parts over `T`, at the price of `(N - |T|) E[F κ₂(X_a - X_b)]` (rules (b), (c) of Step 5 of
    the proof of `prop:bias`, in exact form). -/
theorem split_pair [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) (T : Finset ℕ) (hT : T ⊆ Finset.range N) (a b : T)
    (F : (T → G) → ℝ) (hF : Measurable F) {BF : ℝ} (hFb : ∀ y, |F y| ≤ BF) :
    ∫ ω, F (fun t : T => X t ω) * (Hrow c X N a ω * Hrow c X N b ω) ∂μ
      = ∫ ω, F (fun t : T => X t ω)
          * ((∑ t ∈ T, c (X a ω - X t ω)) * ∑ t ∈ T, c (X b ω - X t ω)) ∂μ
        + ((N : ℝ) - T.card) * ∫ ω, F (fun t : T => X t ω) * κ₂ (X a ω - X b ω) ∂μ := by
  classical
  have hc := H.c_meas
  obtain ⟨R, hRdef⟩ : ∃ R : Finset ℕ, R = Finset.range N \ T := ⟨_, rfl⟩
  have hR : ∀ v ∈ R, v ∉ T := fun v hv => by
    rw [hRdef] at hv; exact (Finset.mem_sdiff.mp hv).2
  have hcard : (R.card : ℝ) = (N : ℝ) - T.card := by
    rw [hRdef, Finset.card_sdiff_of_subset hT, Nat.cast_sub (Finset.card_le_card hT),
      Finset.card_range]
  have hdm : ∀ e : T, Measurable fun y : T → G => ∑ t ∈ T.attach, c (y e - y t) := fun e =>
    Finset.measurable_sum _ fun t _ =>
      hc.comp ((measurable_pi_apply e).sub (measurable_pi_apply t))
  have hdb : ∀ (e : T) (y : T → G),
      |∑ t ∈ T.attach, c (y e - y t)| ≤ ∑ _t ∈ T.attach, B := fun e y =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => H.bound _)
  have hatt : ∀ (e : T) (ω : Ω),
      ∑ t ∈ T.attach, c (X e ω - X t ω) = ∑ t ∈ T, c (X e ω - X t ω) := fun e ω =>
    Finset.sum_attach T (fun v => c (X e ω - X v ω))
  have hsplit : ∀ (e : T) (ω : Ω), Hrow c X N e ω
      = (∑ t ∈ T.attach, c (X e ω - X t ω)) + ∑ v ∈ R, c (X e ω - X v ω) := by
    intro e ω
    rw [hatt e ω, hRdef, add_comm]
    exact (Finset.sum_sdiff hT).symm
  obtain ⟨Fa, hFa⟩ : ∃ Fa : (T → G) → ℝ,
      Fa = fun y => F y * ∑ t ∈ T.attach, c (y a - y t) := ⟨_, rfl⟩
  obtain ⟨Fb, hFb'⟩ : ∃ Fb : (T → G) → ℝ,
      Fb = fun y => F y * ∑ t ∈ T.attach, c (y b - y t) := ⟨_, rfl⟩
  have hFam : Measurable Fa := by rw [hFa]; exact hF.mul (hdm a)
  have hFbm : Measurable Fb := by rw [hFb']; exact hF.mul (hdm b)
  have hFab : ∀ y, |Fa y| ≤ BF * ∑ _t ∈ T.attach, B := fun y => by
    rw [hFa]; exact abs_mul_le' (hFb y) (hdb a y)
  have hFbb : ∀ y, |Fb y| ≤ BF * ∑ _t ∈ T.attach, B := fun y => by
    rw [hFb']; exact abs_mul_le' (hFb y) (hdb b y)
  have z1 := H.tail_sum_single T b R hR Fa hFam hFab
  have z2 := H.tail_sum_single T a R hR Fb hFbm hFbb
  have z3 := H.tail_sum_pair T a b R hR F hF hFb
  have bF := H.bmF T F hF hFb
  have bFa := H.bmF T Fa hFam hFab
  have bFb := H.bmF T Fb hFbm hFbb
  have bh : ∀ e : T, BM (fun ω => ∑ t ∈ T.attach, c (X e ω - X t ω)) := fun e =>
    BM.sum _ _ fun t _ => H.bmc e t
  have bt : ∀ e : T, BM (fun ω => ∑ v ∈ R, c (X e ω - X v ω)) := fun e =>
    BM.sum _ _ fun v _ => H.bmc e v
  have e : ∀ ω, F (fun t : T => X t ω) * (Hrow c X N a ω * Hrow c X N b ω)
      = F (fun t : T => X t ω)
          * ((∑ t ∈ T.attach, c (X a ω - X t ω)) * ∑ t ∈ T.attach, c (X b ω - X t ω))
        + (Fa (fun t : T => X t ω) * ∑ v ∈ R, c (X b ω - X v ω)
          + (Fb (fun t : T => X t ω) * ∑ v ∈ R, c (X a ω - X v ω)
            + F (fun t : T => X t ω)
              * ((∑ v ∈ R, c (X a ω - X v ω)) * ∑ v' ∈ R, c (X b ω - X v' ω)))) := by
    intro ω
    rw [hsplit a ω, hsplit b ω]
    simp only [hFa, hFb']
    ring
  have b1 := bF.mul ((bh a).mul (bh b))
  have b2 := bFa.mul (bt b)
  have b3 := bFb.mul (bt a)
  have b4 := bF.mul ((bt a).mul (bt b))
  rw [integral_congr_ae (Filter.Eventually.of_forall e),
    integral_add (b1.integrable (μ := μ)) (b2.add (b3.add b4)).integrable,
    integral_add b2.integrable (b3.add b4).integrable, integral_add b3.integrable b4.integrable,
    z1, z2, z3, hcard]
  simp_rw [hatt]
  ring

/-- `E[p(X_i - X_q) κ₂(X_i - X_q)] = c3` for `i ≠ q`. -/
theorem two_point [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) {i q : ℕ} (hiq : i ≠ q) :
    ∫ ω, (1 + c (X i ω - X q ω)) * κ₂ (X i ω - X q ω) ∂μ = c3 := by
  haveI : IsProbabilityMeasure (μ.map (X i)) :=
    Measure.isProbabilityMeasure_map (H.meas i).aemeasurable
  have h := indep_integral_eq ν (X q) (X i) (H.meas q) (H.meas i) (H.indep.indepFun hiq.symm)
    (H.law q) (fun p : G × G => (1 + c (p.2 - p.1)) * κ₂ (p.2 - p.1))
    ((measurable_const.add (H.c_meas.comp (measurable_snd.sub measurable_fst))).mul
      (H.k_meas.comp (measurable_snd.sub measurable_fst)))
    (B := B * B) (fun p => abs_mul_le' (H.gbound _) (H.kbound _))
  rw [h]
  simp only [H.three, integral_const, probReal_univ, one_smul]

/-- `E[p₂(X_q - X_q') κ₂(X_q - X_q')] = c4` for `q ≠ q'`. -/
theorem two_point4 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) {i q : ℕ} (hiq : i ≠ q) :
    ∫ ω, (1 + κ₂ (X i ω - X q ω)) * κ₂ (X i ω - X q ω) ∂μ = c4 := by
  haveI : IsProbabilityMeasure (μ.map (X i)) :=
    Measure.isProbabilityMeasure_map (H.meas i).aemeasurable
  have h := indep_integral_eq ν (X q) (X i) (H.meas q) (H.meas i) (H.indep.indepFun hiq.symm)
    (H.law q) (fun p : G × G => (1 + κ₂ (p.2 - p.1)) * κ₂ (p.2 - p.1))
    ((measurable_const.add (H.k_meas.comp (measurable_snd.sub measurable_fst))).mul
      (H.k_meas.comp (measurable_snd.sub measurable_fst)))
    (B := (1 + B) * B)
    (fun p => abs_mul_le' ((abs_add_le _ _).trans (by
      rw [abs_one]; exact add_le_add le_rfl (H.kbound _))) (H.kbound _))
  rw [h]
  simp only [H.four, integral_const, probReal_univ, one_smul]

/-- `E[p(X_i - X_q) p(X_i - X_q') κ₂(X_q - X_q')] = c4` for distinct `i, q, q'`
    (integrate `X_i` first: `∫ p(z - y) p(z - y') dz = 1 + κ₂(y - y')`). -/
theorem three_point [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) {i q q' : ℕ} (hqi : q ≠ i) (hq'i : q' ≠ i) (hqq' : q ≠ q') :
    ∫ ω, (1 + c (X i ω - X q ω)) * (1 + c (X i ω - X q' ω)) * κ₂ (X q ω - X q' ω) ∂μ = c4 := by
  have hB := H.B_nonneg
  have hc := H.c_meas
  have hind : IndepFun (X i) (fun ω => (X q ω, X q' ω)) μ :=
    (H.indep.indepFun_prodMk H.meas q q' i hqi hq'i).symm
  have hYm : Measurable fun ω => (X q ω, X q' ω) := (H.meas q).prodMk (H.meas q')
  have h := indep_integral_eq ν (X i) (fun ω => (X q ω, X q' ω)) (H.meas i) hYm hind (H.law i)
    (fun p : G × (G × G) => (1 + c (p.1 - p.2.1)) * (1 + c (p.1 - p.2.2)) * κ₂ (p.2.1 - p.2.2))
    (((measurable_const.add (hc.comp (measurable_fst.sub (measurable_fst.comp measurable_snd)))).mul
      (measurable_const.add (hc.comp (measurable_fst.sub (measurable_snd.comp measurable_snd))))).mul
      (H.k_meas.comp ((measurable_fst.comp measurable_snd).sub
        (measurable_snd.comp measurable_snd))))
    (B := B * B * B)
    (fun p => abs_mul_le' (abs_mul_le' (H.gbound _) (H.gbound _)) (H.kbound _))
  have hin : ∀ y : G × G,
      ∫ z, (1 + c (z - y.1)) * (1 + c (z - y.2)) * κ₂ (y.1 - y.2) ∂ν
        = (1 + κ₂ (y.1 - y.2)) * κ₂ (y.1 - y.2) := by
    intro y
    have ev : ∀ (w z : G), c (z - w) = c (w - z) := fun w z => by rw [← H.even, neg_sub]
    have m1 : ∀ w : G, BM (fun z : G => c (w - z)) := fun w =>
      ⟨hc.comp (measurable_const.sub measurable_id), B, fun _ => H.bound _⟩
    have k1 : BM (fun _ : G => (1 : ℝ)) := BM.const 1
    have e : ∀ z, (1 + c (z - y.1)) * (1 + c (z - y.2)) * κ₂ (y.1 - y.2)
        = κ₂ (y.1 - y.2) * (1 + c (y.1 - z) + c (y.2 - z) + c (y.1 - z) * c (y.2 - z)) :=
      fun z => by rw [ev y.1 z, ev y.2 z]; ring
    simp_rw [e]
    rw [integral_const_mul,
      integral_add (((k1.add (m1 y.1)).add (m1 y.2)).integrable (μ := ν))
        ((m1 y.1).mul (m1 y.2)).integrable,
      integral_add ((k1.add (m1 y.1)).integrable (μ := ν)) (m1 y.2).integrable,
      integral_add (k1.integrable (μ := ν)) (m1 y.1).integrable,
      integral_const, probReal_univ, one_smul, H.mean, H.mean, H.conv]
    ring
  have h3 : ∫ y, (1 + κ₂ (y.1 - y.2)) * κ₂ (y.1 - y.2) ∂(μ.map fun ω => (X q ω, X q' ω))
      = ∫ ω, (1 + κ₂ (X q ω - X q' ω)) * κ₂ (X q ω - X q' ω) ∂μ :=
    integral_map hYm.aemeasurable
      ((measurable_const.add (H.k_meas.comp (measurable_fst.sub measurable_snd))).mul
        (H.k_meas.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  rw [← H.two_point4 hqq', ← h3]
  refine h.trans ?_
  exact integral_congr_ae (Filter.Eventually.of_forall hin)

/-- **`E (Nε_q)² = c(0)² + (N - 1) κ₂(0)`**, exactly (`q < N`). -/
theorem row_sq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N q : ℕ) (hq : q ∈ Finset.range N) :
    ∫ ω, Hrow c X N q ω * Hrow c X N q ω ∂μ = c 0 * c 0 + ((N : ℝ) - 1) * κ₂ 0 := by
  have h := H.split_pair N {q} (Finset.singleton_subset_iff.mpr hq)
    ⟨q, Finset.mem_singleton_self q⟩ ⟨q, Finset.mem_singleton_self q⟩ (fun _ => 1)
    measurable_const (BF := 1) (fun _ => by rw [abs_one])
  simp only [one_mul, Finset.sum_singleton, sub_self, Finset.card_singleton, Nat.cast_one,
    integral_const, probReal_univ, smul_eq_mul] at h
  exact h

end BVK

/-- The four-index statistic `N⁴ · (1/N) ∑_i ε_i (P̃ε)_i = ∑_{i,q} g_iq (Nε_i)(Nε_q)`. -/
noncomputable def stEB {Ω G : Type*} [AddCommGroup G] (c : G → ℝ) (X : ℕ → Ω → G) (N : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N,
    (1 + c (X i ω - X q ω)) * (Hrow c X N i ω * Hrow c X N q ω)

/-- The five-index statistic `N⁵ · (1/N) ∑_i (P̃ε)_i² = ∑_{i,q,q'} g_iq g_iq' (Nε_q)(Nε_q')`. -/
noncomputable def stBB {Ω G : Type*} [AddCommGroup G] (c : G → ℝ) (X : ℕ → Ω → G) (N : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
    (1 + c (X i ω - X q ω)) * (1 + c (X i ω - X q' ω)) * (Hrow c X N q ω * Hrow c X N q' ω)

theorem triple_count (N : ℕ) :
    ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
        ((if q = i then (1 : ℝ) else 0) + (if q' = i then (1 : ℝ) else 0)
          + (if q = q' then (1 : ℝ) else 0)) ≤ 3 * (N : ℝ) ^ 2 := by
  have h1 : ∀ (s : Finset ℕ) (a : ℕ), ∑ j ∈ s, (if j = a then (1 : ℝ) else 0) ≤ 1 := fun s a => by
    rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
  have h2 : ∀ (s : Finset ℕ) (a : ℕ), ∑ j ∈ s, (if a = j then (1 : ℝ) else 0) ≤ 1 := fun s a => by
    rw [Finset.sum_ite_eq]; split_ifs <;> norm_num
  have hin : ∀ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
        ((if q = i then (1 : ℝ) else 0) + (if q' = i then (1 : ℝ) else 0)
          + (if q = q' then (1 : ℝ) else 0)) ≤ 3 * (N : ℝ) := by
    intro i _
    have e : ∀ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
        ((if q = i then (1 : ℝ) else 0) + (if q' = i then (1 : ℝ) else 0)
          + (if q = q' then (1 : ℝ) else 0))
        ≤ (N : ℝ) * (if q = i then (1 : ℝ) else 0) + 1 + 1 := by
      intro q _
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      linarith only [h1 (Finset.range N) i, h2 (Finset.range N) q]
    refine (Finset.sum_le_sum e).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have := mul_le_mul_of_nonneg_left (h1 (Finset.range N) i) hN0
    linarith only [this]
  refine (Finset.sum_le_sum hin).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_eq (by ring)

namespace BVK

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {c κ₂ : G → ℝ}
  {B c3 c4 : ℝ}

omit [MeasurableSub₂ G] in
theorem pows (H : BVK μ ν X c κ₂ B c3 c4) :
    0 ≤ B ∧ B ≤ B ^ 2 ∧ B ^ 2 ≤ B ^ 3 ∧ B ^ 3 ≤ B ^ 4 ∧ 1 ≤ B ^ 2 := by
  have h1 := H.B_one
  have h0 := H.B_nonneg
  have a2 : B ≤ B ^ 2 := by nlinarith
  have a3 : B ^ 2 ≤ B ^ 3 := by nlinarith
  have a4 : B ^ 3 ≤ B ^ 4 := by nlinarith [pow_nonneg h0 3]
  exact ⟨h0, a2, a3, a4, by nlinarith⟩

theorem bmg (H : BVK μ ν X c κ₂ B c3 c4) (i j : ℕ) : BM (fun ω => 1 + c (X i ω - X j ω)) :=
  (BM.const 1).add (H.bmc i j)

/-- `E (Nε_q) = c(0)`: the mean of a row sum. -/
theorem row_mean [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N q : ℕ) (hq : q ∈ Finset.range N) :
    ∫ ω, Hrow c X N q ω ∂μ = c 0 := by
  classical
  have hR : ∀ v ∈ (Finset.range N).erase q, v ∉ ({q} : Finset ℕ) := fun v hv =>
    fun h => Finset.ne_of_mem_erase hv (Finset.mem_singleton.mp h)
  have z := H.tail_sum_single {q} ⟨q, Finset.mem_singleton_self q⟩ ((Finset.range N).erase q)
    hR (fun _ => 1) measurable_const (BF := 1) (fun _ => by rw [abs_one])
  simp only [one_mul] at z
  have e : ∀ ω, Hrow c X N q ω
      = c 0 + ∑ v ∈ (Finset.range N).erase q, c (X q ω - X v ω) := fun ω => by
    have := Finset.add_sum_erase (Finset.range N) (fun v => c (X q ω - X v ω)) hq
    simp only [sub_self] at this
    exact this.symm
  have bt : BM (fun ω => ∑ v ∈ (Finset.range N).erase q, c (X q ω - X v ω)) :=
    BM.sum _ _ fun v _ => H.bmc q v
  rw [integral_congr_ae (Filter.Eventually.of_forall e),
    integral_add ((BM.const (c 0)).integrable (μ := μ)) bt.integrable, z, integral_const,
    probReal_univ, one_smul, add_zero]

omit [MeasurableSub₂ G] in
theorem rs_le (H : BVK μ ν X c κ₂ B c3 c4) {N : ℕ} (hN : 1 ≤ N) :
    c 0 * c 0 + ((N : ℝ) - 1) * κ₂ 0 ≤ 2 * N * B ^ 2 := by
  obtain ⟨h0, a2, _, _, a1⟩ := H.pows
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : c 0 * c 0 ≤ B * B := (le_abs_self _).trans (abs_mul_le' (H.bound 0) (H.bound 0))
  have h2 : ((N : ℝ) - 1) * κ₂ 0 ≤ ((N : ℝ) - 1) * B :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans (H.kbound 0)) (by linarith only [hN1])
  have h3 : (N : ℝ) * B ≤ N * B ^ 2 := mul_le_mul_of_nonneg_left a2 (by linarith only [hN1])
  have h4 : 1 * B ^ 2 ≤ (N : ℝ) * B ^ 2 := mul_le_mul_of_nonneg_right hN1 (by positivity)
  nlinarith only [h1, h2, h3, h4, h0]

/-- `|E[W (Nε_q)(Nε_q')]| ≤ ‖W‖_∞ E(Nε)²`. -/
theorem prod_bound [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) {q q' : ℕ} (hq : q ∈ Finset.range N)
    (hq' : q' ∈ Finset.range N) (W : Ω → ℝ) (hW : BM W) {BW : ℝ} (hWb : ∀ ω, |W ω| ≤ BW) :
    |∫ ω, W ω * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ|
      ≤ BW * (c 0 * c 0 + ((N : ℝ) - 1) * κ₂ 0) := by
  have bq := H.bmH N q
  have bq' := H.bmH N q'
  have bf := hW.mul (bq.mul bq')
  have bg := BM.const_mul (BW / 2) ((bq.mul bq).add (bq'.mul bq'))
  have hpt : ∀ ω, |W ω * (Hrow c X N q ω * Hrow c X N q' ω)|
      ≤ BW / 2 * (Hrow c X N q ω * Hrow c X N q ω + Hrow c X N q' ω * Hrow c X N q' ω) := by
    intro ω
    have hBW : 0 ≤ BW := (abs_nonneg _).trans (hWb ω)
    have h1 : |Hrow c X N q ω * Hrow c X N q' ω|
        ≤ (Hrow c X N q ω * Hrow c X N q ω + Hrow c X N q' ω * Hrow c X N q' ω) / 2 := by
      rw [abs_le]
      constructor
      · nlinarith only [_root_.sq_nonneg (Hrow c X N q ω + Hrow c X N q' ω)]
      · nlinarith only [_root_.sq_nonneg (Hrow c X N q ω - Hrow c X N q' ω)]
    have h2 := abs_mul_le' (hWb ω) h1
    linarith only [h2]
  have hg : ∫ ω, BW / 2 * (Hrow c X N q ω * Hrow c X N q ω
      + Hrow c X N q' ω * Hrow c X N q' ω) ∂μ = BW * (c 0 * c 0 + ((N : ℝ) - 1) * κ₂ 0) := by
    rw [integral_const_mul, integral_add (bq.mul bq).integrable (bq'.mul bq').integrable,
      H.row_sq N q hq, H.row_sq N q' hq']
    ring
  have h1 : ∫ ω, W ω * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ
      ≤ ∫ ω, BW / 2 * (Hrow c X N q ω * Hrow c X N q ω
          + Hrow c X N q' ω * Hrow c X N q' ω) ∂μ :=
    integral_mono bf.integrable bg.integrable fun ω => (abs_le.mp (hpt ω)).2
  have h2 : -∫ ω, BW / 2 * (Hrow c X N q ω * Hrow c X N q ω
          + Hrow c X N q' ω * Hrow c X N q' ω) ∂μ
      ≤ ∫ ω, W ω * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ := by
    rw [← integral_neg]
    exact integral_mono bg.integrable.neg bf.integrable fun ω => (abs_le.mp (hpt ω)).1
  rw [hg] at h1 h2
  exact abs_le.mpr ⟨h2, h1⟩

/-- **The two-row moment**, `i ≠ q`: `|E[g_iq (Nε_i)(Nε_q)] - (N-2) c3| ≤ 4B³`. -/
theorem pair_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) {i q : ℕ} (hi : i ∈ Finset.range N)
    (hq : q ∈ Finset.range N) (hiq : i ≠ q) :
    |∫ ω, (1 + c (X i ω - X q ω)) * (Hrow c X N i ω * Hrow c X N q ω) ∂μ
        - ((N : ℝ) - 2) * c3| ≤ 4 * B ^ 3 := by
  classical
  obtain ⟨T, hTd⟩ : ∃ T : Finset ℕ, T = {i, q} := ⟨_, rfl⟩
  have hiT : i ∈ T := by rw [hTd]; simp
  have hqT : q ∈ T := by rw [hTd]; simp
  have hTs : T ⊆ Finset.range N := by
    rw [hTd]; intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hi
    · rw [Finset.mem_singleton.mp h]; exact hq
  obtain ⟨F, hFd⟩ : ∃ F : (T → G) → ℝ,
      F = fun y => 1 + c (y ⟨i, hiT⟩ - y ⟨q, hqT⟩) := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hFd]
    exact measurable_const.add
      (H.c_meas.comp ((measurable_pi_apply _).sub (measurable_pi_apply _)))
  have hFb : ∀ y, |F y| ≤ B := fun y => by rw [hFd]; exact H.gbound _
  have h : ∫ ω, F (fun t : T => X t ω) * (Hrow c X N i ω * Hrow c X N q ω) ∂μ
      = ∫ ω, F (fun t : T => X t ω)
          * ((∑ t ∈ T, c (X i ω - X t ω)) * ∑ t ∈ T, c (X q ω - X t ω)) ∂μ
        + ((N : ℝ) - T.card) * ∫ ω, F (fun t : T => X t ω) * κ₂ (X i ω - X q ω) ∂μ :=
    H.split_pair N T hTs ⟨i, hiT⟩ ⟨q, hqT⟩ F hFm hFb
  have h2 : ∫ ω, F (fun t : T => X t ω) * κ₂ (X i ω - X q ω) ∂μ = c3 := by
    rw [hFd]; exact H.two_point hiq
  have hcard : (T.card : ℝ) = 2 := by rw [hTd, Finset.card_pair hiq]; norm_num
  have hhd : |∫ ω, F (fun t : T => X t ω)
      * ((∑ t ∈ T, c (X i ω - X t ω)) * ∑ t ∈ T, c (X q ω - X t ω)) ∂μ|
      ≤ B * (2 * B * (2 * B)) := by
    apply abs_int_le
    · exact (H.bmF T F hFm hFb).mul
        ((BM.sum _ _ fun t _ => H.bmc i t).mul (BM.sum _ _ fun t _ => H.bmc q t))
    · intro ω
      have s1 : ∀ e : ℕ, |∑ t ∈ T, c (X e ω - X t ω)| ≤ 2 * B := fun e => by
        rw [hTd, Finset.sum_pair hiq]
        exact (abs_add_le _ _).trans
          (by linarith only [H.bound (X e ω - X i ω), H.bound (X e ω - X q ω)])
      exact abs_mul_le' (hFb _) (abs_mul_le' (s1 i) (s1 q))
  have e1 : ∫ ω, (1 + c (X i ω - X q ω)) * (Hrow c X N i ω * Hrow c X N q ω) ∂μ
      = ∫ ω, F (fun t : T => X t ω) * (Hrow c X N i ω * Hrow c X N q ω) ∂μ := by rw [hFd]
  rw [e1, h, h2, hcard, add_sub_cancel_right]
  exact hhd.trans (le_of_eq (by ring))

/-- **The three-row moment**, `i, q, q'` distinct:
    `|E[g_iq g_iq' (Nε_q)(Nε_q')] - (N-3) c4| ≤ 9B⁴`. -/
theorem triple_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) {i q q' : ℕ} (hi : i ∈ Finset.range N)
    (hq : q ∈ Finset.range N) (hq' : q' ∈ Finset.range N) (hqi : q ≠ i) (hq'i : q' ≠ i)
    (hqq' : q ≠ q') :
    |∫ ω, (1 + c (X i ω - X q ω)) * (1 + c (X i ω - X q' ω))
          * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ
        - ((N : ℝ) - 3) * c4| ≤ 9 * B ^ 4 := by
  classical
  have hB := H.B_nonneg
  obtain ⟨T, hTd⟩ : ∃ T : Finset ℕ, T = insert i {q, q'} := ⟨_, rfl⟩
  have hin : i ∉ ({q, q'} : Finset ℕ) := by
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim (fun h => hqi h.symm) (fun h => hq'i h.symm)
  have hiT : i ∈ T := by rw [hTd]; simp
  have hqT : q ∈ T := by rw [hTd]; simp
  have hq'T : q' ∈ T := by rw [hTd]; simp
  have hTs : T ⊆ Finset.range N := by
    rw [hTd]; intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hi
    · rcases Finset.mem_insert.mp h with h | h
      · rw [h]; exact hq
      · rw [Finset.mem_singleton.mp h]; exact hq'
  obtain ⟨F, hFd⟩ : ∃ F : (T → G) → ℝ,
      F = fun y => (1 + c (y ⟨i, hiT⟩ - y ⟨q, hqT⟩)) * (1 + c (y ⟨i, hiT⟩ - y ⟨q', hq'T⟩)) :=
    ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hFd]
    exact (measurable_const.add
        (H.c_meas.comp ((measurable_pi_apply (⟨i, hiT⟩ : T)).sub
          (measurable_pi_apply (⟨q, hqT⟩ : T))))).mul
      (measurable_const.add
        (H.c_meas.comp ((measurable_pi_apply (⟨i, hiT⟩ : T)).sub
          (measurable_pi_apply (⟨q', hq'T⟩ : T)))))
  have hFb : ∀ y, |F y| ≤ B * B := fun y => by
    rw [hFd]; exact abs_mul_le' (H.gbound _) (H.gbound _)
  have h : ∫ ω, F (fun t : T => X t ω) * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ
      = ∫ ω, F (fun t : T => X t ω)
          * ((∑ t ∈ T, c (X q ω - X t ω)) * ∑ t ∈ T, c (X q' ω - X t ω)) ∂μ
        + ((N : ℝ) - T.card) * ∫ ω, F (fun t : T => X t ω) * κ₂ (X q ω - X q' ω) ∂μ :=
    H.split_pair N T hTs ⟨q, hqT⟩ ⟨q', hq'T⟩ F hFm hFb
  have h2 : ∫ ω, F (fun t : T => X t ω) * κ₂ (X q ω - X q' ω) ∂μ = c4 := by
    rw [hFd]; exact H.three_point hqi hq'i hqq'
  have hcard : (T.card : ℝ) = 3 := by
    rw [hTd, Finset.card_insert_of_notMem hin, Finset.card_pair hqq']; norm_num
  have hhd : |∫ ω, F (fun t : T => X t ω)
      * ((∑ t ∈ T, c (X q ω - X t ω)) * ∑ t ∈ T, c (X q' ω - X t ω)) ∂μ|
      ≤ B * B * (3 * B * (3 * B)) := by
    apply abs_int_le
    · exact (H.bmF T F hFm hFb).mul
        ((BM.sum _ _ fun t _ => H.bmc q t).mul (BM.sum _ _ fun t _ => H.bmc q' t))
    · intro ω
      have s1 : ∀ e : ℕ, |∑ t ∈ T, c (X e ω - X t ω)| ≤ 3 * B := fun e => by
        rw [hTd, Finset.sum_insert hin, Finset.sum_pair hqq']
        refine (abs_add_le _ _).trans ?_
        have := abs_add_le (c (X e ω - X q ω)) (c (X e ω - X q' ω))
        linarith only [this, H.bound (X e ω - X i ω), H.bound (X e ω - X q ω),
          H.bound (X e ω - X q' ω)]
      exact abs_mul_le' (hFb _) (abs_mul_le' (s1 q) (s1 q'))
  have e1 : ∫ ω, (1 + c (X i ω - X q ω)) * (1 + c (X i ω - X q' ω))
        * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ
      = ∫ ω, F (fun t : T => X t ω) * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ := by rw [hFd]
  rw [e1, h, h2, hcard, add_sub_cancel_right]
  exact hhd.trans (le_of_eq (by ring))

end BVK

namespace BVK

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {c κ₂ : G → ℝ}
  {B c3 c4 : ℝ}

/-- `E ∑_q Nε_q = N c(0)` (so `E ε̄ = (m₁ - 1)/N`), exactly. -/
theorem mean_E1 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) :
    ∫ ω, ∑ q ∈ Finset.range N, Hrow c X N q ω ∂μ = N * c 0 := by
  rw [integral_finset_sum _ fun q _ => (H.bmH N q).integrable,
    Finset.sum_congr rfl fun q hq => H.row_mean N q hq, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- `E ∑_q (Nε_q)² = N (c(0)² + (N-1) κ₂(0))`, exactly. -/
theorem mean_E2 [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) :
    ∫ ω, ∑ q ∈ Finset.range N, Hrow c X N q ω * Hrow c X N q ω ∂μ
      = N * (c 0 * c 0 + ((N : ℝ) - 1) * κ₂ 0) := by
  rw [integral_finset_sum _ fun q _ => ((H.bmH N q).mul (H.bmH N q)).integrable,
    Finset.sum_congr rfl fun q hq => H.row_sq N q hq, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- **`|E ∑_{i,q} g_iq (Nε_i)(Nε_q) - N³ c3| ≤ 9 N² B³`** (the statistic `∑_i ε_i (P̃ε)_i` of
    Step 6, to the order `1/N` with an explicit `O(N⁻²)` remainder). -/
theorem mean_EB [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) (hN : 1 ≤ N) :
    |∫ ω, stEB c X N ω ∂μ - (N : ℝ) ^ 3 * c3| ≤ 9 * (N : ℝ) ^ 2 * B ^ 3 := by
  classical
  obtain ⟨h0, a2, a3, a4, a1⟩ := H.pows
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB3 : 0 ≤ B ^ 3 := pow_nonneg h0 3
  have hint : ∀ i q, Integrable (fun ω => (1 + c (X i ω - X q ω))
      * (Hrow c X N i ω * Hrow c X N q ω)) μ := fun i q =>
    ((H.bmg i q).mul ((H.bmH N i).mul (H.bmH N q))).integrable
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ → ℝ, e = fun i q =>
      ∫ ω, (1 + c (X i ω - X q ω)) * (Hrow c X N i ω * Hrow c X N q ω) ∂μ := ⟨_, rfl⟩
  have hsum : ∫ ω, stEB c X N ω ∂μ
      = ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, e i q := by
    rw [he]
    simp only [stEB]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun q _ => hint i q]
    exact Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun q _ => hint i q
  have hb : ∀ i ∈ Finset.range N, ∀ q ∈ Finset.range N,
      |e i q - ((N : ℝ) - 2) * c3|
        ≤ 4 * B ^ 3 + (if i = q then 3 * (N : ℝ) * B ^ 3 else 0) := by
    intro i hi q hq
    by_cases hiq : i = q
    · rw [if_pos hiq]
      subst hiq
      have p := H.prod_bound N hi hi (fun ω => 1 + c (X i ω - X i ω)) (H.bmg i i) (BW := B)
        (fun ω => H.gbound _)
      have p' : |e i i| ≤ B * (c 0 * c 0 + ((N : ℝ) - 1) * κ₂ 0) := by rw [he]; exact p
      have r := H.rs_le hN
      have t1 : |((N : ℝ) - 2) * c3| ≤ N * B :=
        abs_mul_le' (by rw [abs_le]; constructor <;> linarith only [hN1]) H.c3b
      have t2 := mul_le_mul_of_nonneg_left r h0
      have t3 : (N : ℝ) * B ≤ N * B ^ 3 :=
        mul_le_mul_of_nonneg_left (a2.trans a3) (by linarith only [hN1])
      obtain ⟨p1, p2⟩ := abs_le.mp p'
      obtain ⟨u1, u2⟩ := abs_le.mp t1
      rw [abs_le]; constructor <;> linarith only [p1, p2, u1, u2, t2, t3, hB3]
    · rw [if_neg hiq, add_zero, he]
      exact H.pair_moment N hi hq hiq
  have hdiff : |∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, e i q
        - ∑ i ∈ Finset.range N, ∑ _q ∈ Finset.range N, ((N : ℝ) - 2) * c3|
      ≤ ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N,
          (4 * B ^ 3 + (if i = q then 3 * (N : ℝ) * B ^ 3 else 0)) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => hb i hi q hq)
  have hS1 : ∑ _i ∈ Finset.range N, ∑ _q ∈ Finset.range N, ((N : ℝ) - 2) * c3
      = N * (N * (((N : ℝ) - 2) * c3)) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
  have hS2 : ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N,
        (4 * B ^ 3 + (if i = q then 3 * (N : ℝ) * B ^ 3 else 0))
      = N * (N * (4 * B ^ 3) + 3 * N * B ^ 3) := by
    have : ∀ i ∈ Finset.range N, ∑ q ∈ Finset.range N,
        (4 * B ^ 3 + (if i = q then 3 * (N : ℝ) * B ^ 3 else 0))
        = N * (4 * B ^ 3) + 3 * N * B ^ 3 := by
      intro i hi
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Finset.sum_ite_eq, if_pos hi]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  rw [hS1, hS2] at hdiff
  obtain ⟨c31, c32⟩ := abs_le.mp H.c3b
  obtain ⟨d1, d2⟩ := abs_le.mp hdiff
  have hN2 : 0 ≤ (N : ℝ) ^ 2 := by positivity
  have t1 := mul_le_mul_of_nonneg_left c32 hN2
  have t2 := mul_le_mul_of_nonneg_left c31 hN2
  have t3 : (N : ℝ) ^ 2 * B ≤ N ^ 2 * B ^ 3 := mul_le_mul_of_nonneg_left (a2.trans a3) hN2
  rw [abs_le]; constructor <;> linarith only [d1, d2, t1, t2, t3]

/-- **`|E ∑_{i,q,q'} g_iq g_iq' (Nε_q)(Nε_q') - N⁴ c4| ≤ 27 N³ B⁴`** (the statistic
    `∑_i (P̃ε)_i²` of Step 6, to the order `1/N` with an explicit `O(N⁻²)` remainder). -/
theorem mean_BB [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N : ℕ) (hN : 1 ≤ N) :
    |∫ ω, stBB c X N ω ∂μ - (N : ℝ) ^ 4 * c4| ≤ 27 * (N : ℝ) ^ 3 * B ^ 4 := by
  classical
  obtain ⟨h0, a2, a3, a4, a1⟩ := H.pows
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB4 : 0 ≤ B ^ 4 := pow_nonneg h0 4
  have hNB : 0 ≤ (N : ℝ) * B ^ 4 := mul_nonneg (by linarith only [hN1]) hB4
  have hint : ∀ i q q', Integrable (fun ω => (1 + c (X i ω - X q ω))
      * (1 + c (X i ω - X q' ω)) * (Hrow c X N q ω * Hrow c X N q' ω)) μ := fun i q q' =>
    (((H.bmg i q).mul (H.bmg i q')).mul ((H.bmH N q).mul (H.bmH N q'))).integrable
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℕ → ℕ → ℝ, e = fun i q q' =>
      ∫ ω, (1 + c (X i ω - X q ω)) * (1 + c (X i ω - X q' ω))
        * (Hrow c X N q ω * Hrow c X N q' ω) ∂μ := ⟨_, rfl⟩
  obtain ⟨ind, hind⟩ : ∃ ind : ℕ → ℕ → ℕ → ℝ, ind = fun i q q' =>
      (if q = i then (1 : ℝ) else 0) + (if q' = i then (1 : ℝ) else 0)
        + (if q = q' then (1 : ℝ) else 0) := ⟨_, rfl⟩
  have hsum : ∫ ω, stBB c X N ω ∂μ
      = ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N, e i q q' := by
    rw [he]
    simp only [stBB]
    rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun q _ =>
      integrable_finset_sum _ fun q' _ => hint i q q']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ fun q _ => integrable_finset_sum _ fun q' _ => hint i q q']
    exact Finset.sum_congr rfl fun q _ => integral_finset_sum _ fun q' _ => hint i q q'
  have hb : ∀ i ∈ Finset.range N, ∀ q ∈ Finset.range N, ∀ q' ∈ Finset.range N,
      |e i q q' - ((N : ℝ) - 3) * c4| ≤ 9 * B ^ 4 + 5 * (N : ℝ) * B ^ 4 * ind i q q' := by
    intro i hi q hq q' hq'
    have p := H.prod_bound N hq hq'
      (fun ω => (1 + c (X i ω - X q ω)) * (1 + c (X i ω - X q' ω)))
      ((H.bmg i q).mul (H.bmg i q')) (BW := B * B)
      (fun ω => abs_mul_le' (H.gbound _) (H.gbound _))
    have p' : |e i q q'| ≤ B * B * (c 0 * c 0 + ((N : ℝ) - 1) * κ₂ 0) := by rw [he]; exact p
    have r := H.rs_le hN
    have t1 : |((N : ℝ) - 3) * c4| ≤ 3 * N * B :=
      abs_mul_le' (by rw [abs_le]; constructor <;> linarith only [hN1]) H.c4b
    have t2 := mul_le_mul_of_nonneg_left r (mul_nonneg h0 h0)
    have t3 : (N : ℝ) * B ≤ N * B ^ 4 :=
      mul_le_mul_of_nonneg_left (a2.trans (a3.trans a4)) (by linarith only [hN1])
    obtain ⟨p1, p2⟩ := abs_le.mp p'
    obtain ⟨u1, u2⟩ := abs_le.mp t1
    have gen : |e i q q' - ((N : ℝ) - 3) * c4| ≤ 5 * (N : ℝ) * B ^ 4 := by
      rw [abs_le]; constructor <;> linarith only [p1, p2, u1, u2, t2, t3]
    have h5 : 0 ≤ 5 * (N : ℝ) * B ^ 4 := by linarith only [hNB]
    by_cases hd : q ≠ i ∧ q' ≠ i ∧ q ≠ q'
    · have tm : |e i q q' - ((N : ℝ) - 3) * c4| ≤ 9 * B ^ 4 := by
        rw [he]; exact H.triple_moment N hi hq hq' hd.1 hd.2.1 hd.2.2
      have i0 : 0 ≤ ind i q q' := by
        rw [hind]; simp only; split_ifs <;> norm_num
      have := mul_nonneg h5 i0
      linarith only [tm, this]
    · have i1 : 1 ≤ ind i q q' := by
        rw [hind]; simp only
        split_ifs <;> first
          | (exfalso; exact hd ⟨‹¬q = i›, ‹¬q' = i›, ‹¬q = q'›⟩)
          | norm_num
      have := mul_le_mul_of_nonneg_left i1 h5
      linarith only [gen, this, hB4]
  have hdiff : |∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N, e i q q'
        - ∑ _i ∈ Finset.range N, ∑ _q ∈ Finset.range N, ∑ _q' ∈ Finset.range N,
            ((N : ℝ) - 3) * c4|
      ≤ ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
          (9 * B ^ 4 + 5 * (N : ℝ) * B ^ 4 * ind i q q') := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q hq => ?_)
    rw [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun q' hq' => hb i hi q hq q' hq')
  have hS1 : ∑ _i ∈ Finset.range N, ∑ _q ∈ Finset.range N, ∑ _q' ∈ Finset.range N,
      ((N : ℝ) - 3) * c4 = N * (N * (N * (((N : ℝ) - 3) * c4))) := by
    rw [Finset.sum_const, Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      nsmul_eq_mul, nsmul_eq_mul]
  have hS2 : ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
        (9 * B ^ 4 + 5 * (N : ℝ) * B ^ 4 * ind i q q')
      = N * (N * (N * (9 * B ^ 4))) + 5 * (N : ℝ) * B ^ 4
        * ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N, ind i q q' := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
  have hS3 : ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N, ind i q q'
      ≤ 3 * (N : ℝ) ^ 2 := by rw [hind]; exact triple_count N
  have hS4 := mul_le_mul_of_nonneg_left hS3 (by linarith only [hNB] : 0 ≤ 5 * (N : ℝ) * B ^ 4)
  rw [hsum]
  rw [hS1, hS2] at hdiff
  obtain ⟨c41, c42⟩ := abs_le.mp H.c4b
  obtain ⟨d1, d2⟩ := abs_le.mp hdiff
  have hN3 : 0 ≤ (N : ℝ) ^ 3 := by positivity
  have t1 := mul_le_mul_of_nonneg_left c42 hN3
  have t2 := mul_le_mul_of_nonneg_left c41 hN3
  have t3 : (N : ℝ) ^ 3 * B ≤ N ^ 3 * B ^ 4 :=
    mul_le_mul_of_nonneg_left (a2.trans (a3.trans a4)) hN3
  rw [abs_le]; constructor <;> linarith only [d1, d2, t1, t2, t3, hS4]

end BVK

/-! ## Part 4: the flat torus with the heat kernel -/

theorem pker_even' (d : ℕ) (τ : ℝ) (a b : FlatTorus d) : pker d τ (a - b) = pker d τ (b - a) := by
  rw [← neg_sub b a]; exact heatTorus_even d _ _

theorem pker_two_zero (d : ℕ) (σ : ℝ) : pker d (σ + σ) 0 = torusM d σ 2 := by
  show heatTorus d (2 * Real.pi ^ 2 * (σ + σ)) 0
    = heatTorus d (2 * Real.pi ^ 2 * (((2 : ℕ) : ℝ) * σ)) 0
  congr 1; push_cast; ring

theorem pker_bounds {τ : ℝ} (hτ : 0 < τ) (d : ℕ) (u : FlatTorus d) :
    0 ≤ pker d τ u ∧ pker d τ u ≤ pker d τ 0 :=
  ⟨heatTorus_nonneg (by positivity) d u, heatTorus_le_zero (by positivity) d u⟩

/-- The hypotheses `BVK` hold for independent uniform points on the flat torus and the heat
    kernel `p = p_σ`: `c = p - 1`, `κ₂ = p₂ - 1`, `B = m₁`, `c3 = m₃ - 1`, `c4 = m₄ - 1`. -/
theorem torus_bvk {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {d : ℕ}
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) :
    BVK μ (flatTorusMeasure d) X (cK d σ) (fun u => pker d (σ + σ) u - 1) (torusM d σ 1)
      (torusM d σ 3 - 1) (torusM d σ 4 - 1) := by
  have hσ2 : 0 < σ + σ := by linarith
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  have hM1e : torusM d σ 1 = pker d σ 0 := torusM_one d σ
  have hp : ∀ u, 0 ≤ pker d σ u ∧ pker d σ u ≤ torusM d σ 1 := fun u => by
    rw [hM1e]; exact pker_bounds hσ d u
  have hp2 : ∀ u, 0 ≤ pker d (σ + σ) u ∧ pker d (σ + σ) u ≤ torusM d σ 1 := fun u => by
    refine ⟨(pker_bounds hσ2 d u).1, (pker_bounds hσ2 d u).2.trans ?_⟩
    rw [pker_two_zero]; exact torusM_anti hσ d le_rfl (by norm_num)
  have c1 : ∀ x : FlatTorus d, Continuous fun z : FlatTorus d => pker d σ (x - z) := fun x =>
    (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
  have c2 : ∀ x : FlatTorus d, Continuous fun z : FlatTorus d => pker d (σ + σ) (x - z) :=
    fun x => (pker_continuous hσ2 d).comp (continuous_const.sub continuous_id)
  have c1' : ∀ x : FlatTorus d, Continuous fun z : FlatTorus d => pker d σ (z - x) := fun x =>
    (pker_continuous hσ d).comp (continuous_id.sub continuous_const)
  have c2' : ∀ x : FlatTorus d, Continuous fun z : FlatTorus d => pker d (σ + σ) (z - x) :=
    fun x => (pker_continuous hσ2 d).comp (continuous_id.sub continuous_const)
  refine
    { indep := h_indep
      meas := hX
      law := hlaw
      c_meas := (pker_continuous hσ d).measurable.sub measurable_const
      k_meas := (pker_continuous hσ2 d).measurable.sub measurable_const
      B_one := hM1
      bound := fun u => (cK_facts hσ d u).1
      gbound := fun u => ?_
      kbound := fun u => ?_
      even := cK_even d σ
      mean := fun x => c_mean_zero hσ d x
      conv := fun x y => ?_
      three := fun x => ?_
      four := fun x => ?_
      c3b := ?_
      c4b := ?_ }
  · have e : 1 + cK d σ u = pker d σ u := by unfold cK; ring
    rw [e, abs_of_nonneg (hp u).1]; exact (hp u).2
  · show |pker d (σ + σ) u - 1| ≤ torusM d σ 1
    rw [abs_le]; constructor <;> linarith only [(hp2 u).1, (hp2 u).2, hM1]
  · show ∫ z, cK d σ (x - z) * cK d σ (y - z) ∂flatTorusMeasure d = pker d (σ + σ) (x - y) - 1
    have s1 : ∫ z, pker d σ (x - z) * pker d σ (z - y) ∂flatTorusMeasure d
        = pker d (σ + σ) (x - y) := semigroup_all hσ hσ d x y
    have e : ∀ z, cK d σ (x - z) * cK d σ (y - z)
        = pker d σ (x - z) * pker d σ (z - y) - pker d σ (x - z) - pker d σ (y - z) + 1 :=
      fun z => by unfold cK; rw [pker_even' d σ z y]; ring
    have i1 : Integrable (fun z => pker d σ (x - z) * pker d σ (z - y)) (flatTorusMeasure d) :=
      flat_integrable d _ ((c1 x).mul (c1' y))
    have i2 := flat_integrable d _ (c1 x)
    have i3 := flat_integrable d _ (c1 y)
    have i12 : Integrable (fun z => pker d σ (x - z) * pker d σ (z - y) - pker d σ (x - z))
        (flatTorusMeasure d) := i1.sub i2
    have i123 : Integrable (fun z => pker d σ (x - z) * pker d σ (z - y) - pker d σ (x - z)
        - pker d σ (y - z)) (flatTorusMeasure d) := i12.sub i3
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_add i123 (integrable_const 1),
      integral_sub i12 i3, integral_sub i1 i2, s1, pker_mass hσ d x, pker_mass hσ d y,
      integral_const, probReal_univ, one_smul]
    ring
  · show ∫ z, (1 + cK d σ (x - z)) * (pker d (σ + σ) (x - z) - 1) ∂flatTorusMeasure d
      = torusM d σ 3 - 1
    have s1 : ∫ z, pker d σ (x - z) * pker d (σ + σ) (z - x) ∂flatTorusMeasure d
        = heatTorus d (2 * Real.pi ^ 2 * (σ + (σ + σ))) (x - x) := semigroup_all hσ hσ2 d x x
    have s2 : heatTorus d (2 * Real.pi ^ 2 * (σ + (σ + σ))) (x - x) = torusM d σ 3 := by
      unfold torusM; rw [sub_self]; congr 1; push_cast; ring
    have e : ∀ z, (1 + cK d σ (x - z)) * (pker d (σ + σ) (x - z) - 1)
        = pker d σ (x - z) * pker d (σ + σ) (z - x) - pker d σ (x - z) :=
      fun z => by unfold cK; rw [pker_even' d (σ + σ) z x]; ring
    have i1 : Integrable (fun z => pker d σ (x - z) * pker d (σ + σ) (z - x))
        (flatTorusMeasure d) := flat_integrable d _ ((c1 x).mul (c2' x))
    rw [integral_congr_ae (Filter.Eventually.of_forall e),
      integral_sub i1 (flat_integrable d _ (c1 x)), s1, s2, pker_mass hσ d x]
  · show ∫ z, (1 + (pker d (σ + σ) (x - z) - 1)) * (pker d (σ + σ) (x - z) - 1)
        ∂flatTorusMeasure d = torusM d σ 4 - 1
    have s1 : ∫ z, pker d (σ + σ) (x - z) * pker d (σ + σ) (z - x) ∂flatTorusMeasure d
        = heatTorus d (2 * Real.pi ^ 2 * ((σ + σ) + (σ + σ))) (x - x) :=
      semigroup_all hσ2 hσ2 d x x
    have s2 : heatTorus d (2 * Real.pi ^ 2 * ((σ + σ) + (σ + σ))) (x - x) = torusM d σ 4 := by
      unfold torusM; rw [sub_self]; congr 1; push_cast; ring
    have e : ∀ z, (1 + (pker d (σ + σ) (x - z) - 1)) * (pker d (σ + σ) (x - z) - 1)
        = pker d (σ + σ) (x - z) * pker d (σ + σ) (z - x) - pker d (σ + σ) (x - z) :=
      fun z => by rw [pker_even' d (σ + σ) z x]; ring
    have i1 : Integrable (fun z => pker d (σ + σ) (x - z) * pker d (σ + σ) (z - x))
        (flatTorusMeasure d) := flat_integrable d _ ((c2 x).mul (c2' x))
    rw [integral_congr_ae (Filter.Eventually.of_forall e),
      integral_sub i1 (flat_integrable d _ (c2 x)), s1, s2, pker_mass hσ2 d x]
  · have h1 := torusM_ge_one hσ d (a := 3) (by norm_num)
    have h2 := torusM_anti hσ d (k := 1) (s := 3) le_rfl (by norm_num)
    rw [abs_le]; constructor <;> linarith only [h1, h2, hM1]
  · have h1 := torusM_ge_one hσ d (a := 4) (by norm_num)
    have h2 := torusM_anti hσ d (k := 1) (s := 4) le_rfl (by norm_num)
    rw [abs_le]; constructor <;> linarith only [h1, h2, hM1]

/-! ## Part 5: the polynomial statistic `Q` for `k = 1` and its relation to the trace -/

theorem abs_sum_le_card {s : Finset ℕ} {f : ℕ → ℝ} {C : ℝ} (h : ∀ i ∈ s, |f i| ≤ C) :
    |∑ i ∈ s, f i| ≤ s.card * C := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum h

/-- The diagonal entries of a walk matrix lie in `[0, 1]`. -/
theorem walk_diag_unit {n : Type} [Fintype n] (K : n → n → ℝ) (ρ : n → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hρ : ∀ i, 0 ≤ ρ i) (i : n) :
    0 ≤ walkMatrix K ρ i i ∧ walkMatrix K ρ i i ≤ 1 := by
  have ht : ∀ l, 0 ≤ K i l / (ρ i * ρ l) := fun l =>
    div_nonneg (hK i l) (mul_nonneg (hρ i) (hρ l))
  have hs : 0 ≤ ∑ l, K i l / (ρ i * ρ l) := Finset.sum_nonneg fun l _ => ht l
  simp only [walkMatrix, Matrix.of_apply]
  exact ⟨div_nonneg (ht i) hs,
    div_le_one_of_le₀ (Finset.single_le_sum (fun l _ => ht l) (Finset.mem_univ i)) hs⟩

/-- **The polynomial statistic of Step 3 for `k = 1`** (with self-loops), summed over the
    vertices: `Q = m₁ (1 - ε̄ + (1/N) ∑_i (3ε_i² - 3ε_i (P̃ε)_i + (P̃ε)_i²))`, written with the row
    sums `Nε_q = ∑_v c(X_q - X_v)`.  (Compared with `Q_0 + Q_1 + Q_2` of the paper the term
    `-(m₁/N) ∑_i ε_i³`, which is of the order of the remainder, is left out.) -/
noncomputable def Q1 {Ω : Type*} (d : ℕ) (σ : ℝ) (N : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) : ℝ :=
  torusM d σ 1 * (1 - 1 / (N : ℝ) ^ 2 * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω
    + 3 * (1 / (N : ℝ) ^ 3
        * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω)
    - 3 * (1 / (N : ℝ) ^ 4 * stEB (cK d σ) X N ω) + 1 / (N : ℝ) ^ 5 * stBB (cK d σ) X N ω)

theorem Q1_alg (N : ℕ) (M : ℝ) (H : ℕ → ℝ) (g : ℕ → ℕ → ℝ) :
    M * (1 - 1 / (N : ℝ) * ∑ i ∈ Finset.range N, 1 / (N : ℝ) * H i
        + 1 / (N : ℝ) * ∑ i ∈ Finset.range N, (3 * (1 / (N : ℝ) * H i) ^ 2
            - 3 * (1 / (N : ℝ) * H i)
              * (1 / (N : ℝ) * ∑ l ∈ Finset.range N, g i l * (1 / (N : ℝ) * H l))
            + (1 / (N : ℝ) * ∑ l ∈ Finset.range N, g i l * (1 / (N : ℝ) * H l)) ^ 2))
      = M * (1 - 1 / (N : ℝ) ^ 2 * ∑ q ∈ Finset.range N, H q
          + 3 * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N, H q * H q)
          - 3 * (1 / (N : ℝ) ^ 4 * ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N,
              g i q * (H i * H q))
          + 1 / (N : ℝ) ^ 5 * ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N,
              ∑ q' ∈ Finset.range N, g i q * g i q' * (H q * H q')) := by
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℝ, A = fun i => ∑ l ∈ Finset.range N, g i l * H l := ⟨_, rfl⟩
  have e1 : ∀ i, ∑ l ∈ Finset.range N, g i l * (1 / (N : ℝ) * H l) = 1 / (N : ℝ) * A i := by
    intro i; rw [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∀ i, ∑ q ∈ Finset.range N, g i q * (H i * H q) = H i * A i := by
    intro i; rw [hA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have e3 : ∀ i, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N, g i q * g i q' * (H q * H q')
      = A i * A i := by
    intro i; rw [hA]; simp only; rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring
  have e4 : ∀ i, 3 * (1 / (N : ℝ) * H i) ^ 2
        - 3 * (1 / (N : ℝ) * H i) * (1 / (N : ℝ) * (1 / (N : ℝ) * A i))
        + (1 / (N : ℝ) * (1 / (N : ℝ) * A i)) ^ 2
      = 3 / (N : ℝ) ^ 2 * (H i * H i) - 3 / (N : ℝ) ^ 3 * (H i * A i)
        + 1 / (N : ℝ) ^ 4 * (A i * A i) := fun i => by ring
  simp_rw [e1, e2, e3, e4, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The statistic of `trace_one_expansion` at the sample is `Q1`. -/
theorem Q1_eq {d : ℕ} (σ : ℝ) (N : ℕ) (hN : 0 < N) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    torusM d σ 1 * (1 - 1 / (N : ℝ) * ∑ i : Fin N, (heatRho d σ N (fun j => X j ω) i - 1)
        + 1 / (N : ℝ) * ∑ i : Fin N, (3 * (heatRho d σ N (fun j => X j ω) i - 1) ^ 2
            - 3 * (heatRho d σ N (fun j => X j ω) i - 1)
              * (1 / (N : ℝ) * ∑ l : Fin N, torusK d σ N (fun j => X j ω) i l
                  * (heatRho d σ N (fun j => X j ω) l - 1))
            + (1 / (N : ℝ) * ∑ l : Fin N, torusK d σ N (fun j => X j ω) i l
                  * (heatRho d σ N (fun j => X j ω) l - 1)) ^ 2))
      = Q1 d σ N X ω := by
  have hε := fun q => SecondStageTrace2.eps_eq_Hrow d σ N hN X ω q
  have hin : ∀ i : Fin N, ∑ l : Fin N, torusK d σ N (fun j => X j ω) i l
        * (heatRho d σ N (fun j => X j ω) l - 1)
      = ∑ l ∈ Finset.range N, (1 + cK d σ (X i ω - X l ω))
          * (1 / (N : ℝ) * Hrow (cK d σ) X N l ω) := by
    intro i
    rw [← Fin.sum_univ_eq_sum_range
      (fun l => (1 + cK d σ (X i ω - X l ω)) * (1 / (N : ℝ) * Hrow (cK d σ) X N l ω)) N]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hε l]
    have : torusK d σ N (fun j => X j ω) i l = 1 + cK d σ (X i ω - X l ω) := by
      unfold torusK cK pker; ring
    rw [this]
  simp_rw [hin, hε]
  rw [Fin.sum_univ_eq_sum_range (fun i => 1 / (N : ℝ) * Hrow (cK d σ) X N i ω) N,
    Fin.sum_univ_eq_sum_range (fun i => 3 * (1 / (N : ℝ) * Hrow (cK d σ) X N i ω) ^ 2
      - 3 * (1 / (N : ℝ) * Hrow (cK d σ) X N i ω)
        * (1 / (N : ℝ) * ∑ l ∈ Finset.range N, (1 + cK d σ (X i ω - X l ω))
            * (1 / (N : ℝ) * Hrow (cK d σ) X N l ω))
      + (1 / (N : ℝ) * ∑ l ∈ Finset.range N, (1 + cK d σ (X i ω - X l ω))
            * (1 / (N : ℝ) * Hrow (cK d σ) X N l ω)) ^ 2) N]
  exact Q1_alg N (torusM d σ 1) (fun q => Hrow (cK d σ) X N q ω)
    (fun i q => 1 + cK d σ (X i ω - X q ω))

/-- **On the normalisation event** `|ρ_a - 1| ≤ δ ≤ 1/8`:
    `|Tr P - Q| ≤ 95 m₁ δ (1/N) ∑_q ε_q²` (deterministic; Steps 1–3 for `k = 1`). -/
theorem trace_Q1_good {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 0 < N)
    (X : ℕ → Ω → FlatTorus d) (ω : Ω) {δ : ℝ} (hδ : δ ≤ 1 / 8)
    (hρ : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ) :
    |(torusWalk d σ N (fun j => X j ω)).trace - Q1 d σ N X ω|
      ≤ 95 * torusM d σ 1 * δ * (1 / (N : ℝ) ^ 3
          * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hM0 : 0 ≤ torusM d σ 1 := zero_le_one.trans (torusM_one_ge hσ d)
  have h := trace_one_expansion hN (torusK d σ N (fun j => X j ω))
    (torusRho d σ N (fun j => X j ω)) (fun a : Fin N => heatRho d σ N (fun j => X j ω) a - 1)
    (m := torusM d σ 1) (δ := δ)
    (fun i j => heatTorus_nonneg hc d _)
    (fun i j => by
      show heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω)
        = heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X i ω)
      rw [← neg_sub (X j ω) (X i ω), heatTorus_even])
    (fun i => by
      show heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X i ω) = torusM d σ 1
      rw [sub_self, torusM_one])
    (fun i => by
      show ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)
        = N * heatRho d σ N (fun j => X j ω) i
      rw [Fin.sum_univ_eq_sum_range
        (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) N]
      unfold heatRho
      field_simp)
    (fun i => rfl) hM0 hδ hρ
  rw [Q1_eq σ N hN X ω] at h
  have e : 1 / (N : ℝ) * ∑ i : Fin N, (heatRho d σ N (fun j => X j ω) i - 1) ^ 2
      = 1 / (N : ℝ) ^ 3
        * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω := by
    have hε := fun q => SecondStageTrace2.eps_eq_Hrow d σ N hN X ω q
    simp_rw [hε]
    rw [Fin.sum_univ_eq_sum_range (fun i => (1 / (N : ℝ) * Hrow (cK d σ) X N i ω) ^ 2) N,
      Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e] at h
  exact h

/-- `|Nε_q| ≤ N m₁`. -/
theorem Hrow_abs_le {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (N q : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    |Hrow (cK d σ) X N q ω| ≤ N * torusM d σ 1 := by
  have := abs_sum_le_card (s := Finset.range N) (f := fun v => cK d σ (X q ω - X v ω))
    (C := torusM d σ 1) (fun v _ => (cK_facts hσ d _).1)
  rw [Finset.card_range] at this
  exact this

/-- `|Q| ≤ 9 m₁⁵` always. -/
theorem Q1_abs_le {d : ℕ} {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 0 < N)
    (X : ℕ → Ω → FlatTorus d) (ω : Ω) : |Q1 d σ N X ω| ≤ 9 * torusM d σ 1 ^ 5 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hH : ∀ q, |Hrow (cK d σ) X N q ω| ≤ N * M := fun q => by
    rw [hMd]; exact Hrow_abs_le hσ N q X ω
  have hg : ∀ i q, |1 + cK d σ (X i ω - X q ω)| ≤ M := fun i q => by
    have e : 1 + cK d σ (X i ω - X q ω) = pker d σ (X i ω - X q ω) := by unfold cK; ring
    rw [e, hMd, torusM_one, abs_of_nonneg (pker_bounds hσ d _).1]
    exact (pker_bounds hσ d _).2
  have hHH : ∀ q q', |Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q' ω| ≤ N * M * (N * M) :=
    fun q q' => abs_mul_le' (hH q) (hH q')
  have b1 : |∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω| ≤ N * (N * M) := by
    have := abs_sum_le_card (s := Finset.range N) (fun q _ => hH q)
    rwa [Finset.card_range] at this
  have b2 : |∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω|
      ≤ N * (N * M * (N * M)) := by
    have := abs_sum_le_card (s := Finset.range N) (fun q _ => hHH q q)
    rwa [Finset.card_range] at this
  have b3 : |stEB (cK d σ) X N ω| ≤ N * (N * (M * (N * M * (N * M)))) := by
    unfold stEB
    have := abs_sum_le_card (s := Finset.range N)
      (f := fun i => ∑ q ∈ Finset.range N, (1 + cK d σ (X i ω - X q ω))
        * (Hrow (cK d σ) X N i ω * Hrow (cK d σ) X N q ω))
      (C := N * (M * (N * M * (N * M)))) (fun i _ => by
        have := abs_sum_le_card (s := Finset.range N)
          (f := fun q => (1 + cK d σ (X i ω - X q ω))
            * (Hrow (cK d σ) X N i ω * Hrow (cK d σ) X N q ω))
          (fun q _ => abs_mul_le' (hg i q) (hHH i q))
        rwa [Finset.card_range] at this)
    rwa [Finset.card_range] at this
  have b4 : |stBB (cK d σ) X N ω| ≤ N * (N * (N * (M * M * (N * M * (N * M))))) := by
    unfold stBB
    have := abs_sum_le_card (s := Finset.range N)
      (f := fun i => ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
        (1 + cK d σ (X i ω - X q ω)) * (1 + cK d σ (X i ω - X q' ω))
          * (Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q' ω))
      (C := N * (N * (M * M * (N * M * (N * M))))) (fun i _ => by
        have := abs_sum_le_card (s := Finset.range N)
          (f := fun q => ∑ q' ∈ Finset.range N,
            (1 + cK d σ (X i ω - X q ω)) * (1 + cK d σ (X i ω - X q' ω))
              * (Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q' ω))
          (C := N * (M * M * (N * M * (N * M)))) (fun q _ => by
            have := abs_sum_le_card (s := Finset.range N)
              (f := fun q' => (1 + cK d σ (X i ω - X q ω)) * (1 + cK d σ (X i ω - X q' ω))
                * (Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q' ω))
              (fun q' _ => abs_mul_le' (abs_mul_le' (hg i q) (hg i q')) (hHH q q'))
            rwa [Finset.card_range] at this)
        rwa [Finset.card_range] at this)
    rwa [Finset.card_range] at this
  have c1 : |1 / (N : ℝ) ^ 2 * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω| ≤ M := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 2)]
    calc 1 / (N : ℝ) ^ 2 * |∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω|
        ≤ 1 / (N : ℝ) ^ 2 * (N * (N * M)) := mul_le_mul_of_nonneg_left b1 (by positivity)
      _ = M := by field_simp
  have c2 : |1 / (N : ℝ) ^ 3
      * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω| ≤ M ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 3)]
    calc 1 / (N : ℝ) ^ 3 * |∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω
          * Hrow (cK d σ) X N q ω|
        ≤ 1 / (N : ℝ) ^ 3 * (N * (N * M * (N * M))) :=
          mul_le_mul_of_nonneg_left b2 (by positivity)
      _ = M ^ 2 := by field_simp
  have c3 : |1 / (N : ℝ) ^ 4 * stEB (cK d σ) X N ω| ≤ M ^ 3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 4)]
    calc 1 / (N : ℝ) ^ 4 * |stEB (cK d σ) X N ω|
        ≤ 1 / (N : ℝ) ^ 4 * (N * (N * (M * (N * M * (N * M))))) :=
          mul_le_mul_of_nonneg_left b3 (by positivity)
      _ = M ^ 3 := by field_simp
  have c4 : |1 / (N : ℝ) ^ 5 * stBB (cK d σ) X N ω| ≤ M ^ 4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 5)]
    calc 1 / (N : ℝ) ^ 5 * |stBB (cK d σ) X N ω|
        ≤ 1 / (N : ℝ) ^ 5 * (N * (N * (N * (M * M * (N * M * (N * M)))))) :=
          mul_le_mul_of_nonneg_left b4 (by positivity)
      _ = M ^ 4 := by field_simp
  unfold Q1
  rw [← hMd, abs_mul, abs_of_nonneg hM0]
  obtain ⟨l1, u1⟩ := abs_le.mp c1
  obtain ⟨l2, u2⟩ := abs_le.mp c2
  obtain ⟨l3, u3⟩ := abs_le.mp c3
  obtain ⟨l4, u4⟩ := abs_le.mp c4
  have p2 : M ≤ M ^ 2 := by nlinarith only [hM1]
  have p3 : M ^ 2 ≤ M ^ 3 := by nlinarith only [hM1, hM0]
  have p4 : M ^ 3 ≤ M ^ 4 := by nlinarith only [hM1, pow_nonneg hM0 3]
  have hin : |1 - 1 / (N : ℝ) ^ 2 * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω
      + 3 * (1 / (N : ℝ) ^ 3
          * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω)
      - 3 * (1 / (N : ℝ) ^ 4 * stEB (cK d σ) X N ω)
      + 1 / (N : ℝ) ^ 5 * stBB (cK d σ) X N ω| ≤ 9 * M ^ 4 := by
    rw [abs_le]; constructor <;> linarith only [l1, u1, l2, u2, l3, u3, l4, u4, p2, p3, p4, hM1]
  calc M * |1 - 1 / (N : ℝ) ^ 2 * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω
      + 3 * (1 / (N : ℝ) ^ 3
          * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω)
      - 3 * (1 / (N : ℝ) ^ 4 * stEB (cK d σ) X N ω)
      + 1 / (N : ℝ) ^ 5 * stBB (cK d σ) X N ω|
      ≤ M * (9 * M ^ 4) := mul_le_mul_of_nonneg_left hin hM0
    _ = 9 * M ^ 5 := by ring

end Sample

/-! ## Part 6: the bias of `Tr P` in the order `1/N` (`prop:bias` for `k = 1`, self-loops) -/

theorem abs_int_le_int {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (h : ∀ ω, |f ω| ≤ g ω) :
    |∫ ω, f ω ∂μ| ≤ ∫ ω, g ω ∂μ := by
  have h1 : ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ := integral_mono hf hg fun ω => (abs_le.mp (h ω)).2
  have h2 : ∫ ω, -g ω ∂μ ≤ ∫ ω, f ω ∂μ := integral_mono hg.neg hf fun ω => (abs_le.mp (h ω)).1
  rw [integral_neg] at h2
  exact abs_le.mpr ⟨h2, h1⟩

/-- The arithmetic of Step 7 for `k = 1`: the five expectations add up to `m₁ + β₁/N` with
    `β₁ = m₁ (m₄ - 3m₃ + 3m₂ - m₁)`, up to `60 m₁⁵ / N²`. -/
theorem final_arith {n M m2 m3 m4 S1 S2 EB BB : ℝ} (hn : 1 ≤ n) (hM : 1 ≤ M)
    (h2 : 1 ≤ m2) (h2' : m2 ≤ M)
    (hS1 : S1 = n * (M - 1)) (hS2 : S2 = n * ((M - 1) * (M - 1) + (n - 1) * (m2 - 1)))
    (hEB : |EB - n ^ 3 * (m3 - 1)| ≤ 9 * n ^ 2 * M ^ 3)
    (hBB : |BB - n ^ 4 * (m4 - 1)| ≤ 27 * n ^ 3 * M ^ 4) :
    |M * (1 - 1 / n ^ 2 * S1 + 3 * (1 / n ^ 3 * S2) - 3 * (1 / n ^ 4 * EB) + 1 / n ^ 5 * BB)
        - (M + M * (m4 - 3 * m3 + 3 * m2 - M) / n)| ≤ 60 * M ^ 5 / n ^ 2 := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = EB - n ^ 3 * (m3 - 1) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = BB - n ^ 4 * (m4 - 1) := ⟨_, rfl⟩
  rw [← hD] at hEB
  rw [← hE] at hBB
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / n ^ 2 := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have key : M * (1 - 1 / n ^ 2 * S1 + 3 * (1 / n ^ 3 * S2) - 3 * (1 / n ^ 4 * EB)
        + 1 / n ^ 5 * BB) - (M + M * (m4 - 3 * m3 + 3 * m2 - M) / n)
      = M * (3 * ((M - 1) * (M - 1) - (m2 - 1)) * r - 3 * (D / n ^ 4) + E / n ^ 5) := by
    rw [hS1, hS2, hD, hE, hr]; field_simp; ring
  have d1 : |D / n ^ 4| ≤ 9 * M ^ 3 * r := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n ^ 4), hr]
    calc |D| / n ^ 4 ≤ (9 * n ^ 2 * M ^ 3) / n ^ 4 :=
          div_le_div_of_nonneg_right hEB (by positivity)
      _ = 9 * M ^ 3 * (1 / n ^ 2) := by field_simp
  have d2 : |E / n ^ 5| ≤ 27 * M ^ 4 * r := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < n ^ 5), hr]
    calc |E| / n ^ 5 ≤ (27 * n ^ 3 * M ^ 4) / n ^ 5 :=
          div_le_div_of_nonneg_right hBB (by positivity)
      _ = 27 * M ^ 4 * (1 / n ^ 2) := by field_simp
  have hMM := mul_nonneg hM0 (sub_nonneg.mpr hM)
  have a0 : |3 * ((M - 1) * (M - 1) - (m2 - 1))| ≤ 3 * M ^ 2 := by
    rw [abs_le]; constructor
    · nlinarith only [hM, h2', hMM, _root_.sq_nonneg (M - 1)]
    · linarith only [hM, h2]
  have d0 : |3 * ((M - 1) * (M - 1) - (m2 - 1)) * r| ≤ 3 * M ^ 2 * r :=
    abs_mul_le' a0 (by rw [abs_of_nonneg hr0])
  obtain ⟨l0, u0⟩ := abs_le.mp d0
  obtain ⟨l1, u1⟩ := abs_le.mp d1
  obtain ⟨l2, u2⟩ := abs_le.mp d2
  have hin : |3 * ((M - 1) * (M - 1) - (m2 - 1)) * r - 3 * (D / n ^ 4) + E / n ^ 5|
      ≤ (3 * M ^ 2 + 27 * M ^ 3 + 27 * M ^ 4) * r := by
    rw [abs_le]; constructor <;> linarith only [l0, u0, l1, u1, l2, u2]
  have hM2 : 1 ≤ M ^ 2 := by nlinarith only [hM]
  have p2 : M ^ 2 ≤ M ^ 4 := by
    have := mul_le_mul_of_nonneg_left hM2 (pow_nonneg hM0 2); linarith only [this]
  have p3 : M ^ 3 ≤ M ^ 4 := by
    have := mul_le_mul_of_nonneg_left hM (pow_nonneg hM0 3); linarith only [this]
  have hpoly : M * (3 * M ^ 2 + 27 * M ^ 3 + 27 * M ^ 4) ≤ 60 * M ^ 5 := by
    have := mul_le_mul_of_nonneg_left (by linarith only [p2, p3] :
      3 * M ^ 2 + 27 * M ^ 3 + 27 * M ^ 4 ≤ 57 * M ^ 4) hM0
    have h5 := pow_nonneg hM0 5
    linarith only [this, h5]
  rw [key, abs_mul, abs_of_nonneg hM0]
  calc M * |3 * ((M - 1) * (M - 1) - (m2 - 1)) * r - 3 * (D / n ^ 4) + E / n ^ 5|
      ≤ M * ((3 * M ^ 2 + 27 * M ^ 3 + 27 * M ^ 4) * r) :=
        mul_le_mul_of_nonneg_left hin hM0
    _ = M * (3 * M ^ 2 + 27 * M ^ 3 + 27 * M ^ 4) * r := by ring
    _ ≤ 60 * M ^ 5 * r := mul_le_mul_of_nonneg_right hpoly hr0
    _ = 60 * M ^ 5 / n ^ 2 := by rw [hr]; ring

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The mean of the polynomial statistic, `k = 1`:**
    `|E Q - (m₁ + β₁/N)| ≤ 60 m₁⁵/N²`, `β₁ = m₁ (m₄ - 3m₃ + 3m₂ - m₁)`
    (Steps 5–7 of the proof of `prop:bias` for `k = 1`, `ρ = p(0)`, with an explicit
    `O(N⁻²)` remainder). -/
theorem Q1_mean [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N) :
    BM (Q1 d σ N X) ∧
    |∫ ω, Q1 d σ N X ω ∂μ - (torusM d σ 1 + torusM d σ 1
        * (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1) / N)|
      ≤ 60 * torusM d σ 1 ^ 5 / (N : ℝ) ^ 2 := by
  have H := torus_bvk X h_indep hX hlaw hσ
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have bS1 : BM (fun ω => ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω) :=
    BM.sum _ _ fun q _ => H.bmH N q
  have bS2 : BM (fun ω => ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) :=
    BM.sum _ _ fun q _ => (H.bmH N q).mul (H.bmH N q)
  have bEB : BM (fun ω => stEB (cK d σ) X N ω) := by
    show BM (fun ω => ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N,
      (1 + cK d σ (X i ω - X q ω)) * (Hrow (cK d σ) X N i ω * Hrow (cK d σ) X N q ω))
    exact BM.sum _ _ fun i _ => BM.sum _ _ fun q _ =>
      (H.bmg i q).mul ((H.bmH N i).mul (H.bmH N q))
  have bBB : BM (fun ω => stBB (cK d σ) X N ω) := by
    show BM (fun ω => ∑ i ∈ Finset.range N, ∑ q ∈ Finset.range N, ∑ q' ∈ Finset.range N,
      (1 + cK d σ (X i ω - X q ω)) * (1 + cK d σ (X i ω - X q' ω))
        * (Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q' ω))
    exact BM.sum _ _ fun i _ => BM.sum _ _ fun q _ => BM.sum _ _ fun q' _ =>
      ((H.bmg i q).mul (H.bmg i q')).mul ((H.bmH N q).mul (H.bmH N q'))
  have b1 : BM (fun _ : Ω => (1 : ℝ)) := BM.const 1
  have t1 := b1.sub (BM.const_mul (1 / (N : ℝ) ^ 2) bS1)
  have u2 := BM.const_mul 3 (BM.const_mul (1 / (N : ℝ) ^ 3) bS2)
  have t2 := t1.add u2
  have u3 := BM.const_mul 3 (BM.const_mul (1 / (N : ℝ) ^ 4) bEB)
  have t3 := t2.sub u3
  have u4 := BM.const_mul (1 / (N : ℝ) ^ 5) bBB
  have t4 := t3.add u4
  have bQ : BM (Q1 d σ N X) := BM.const_mul (torusM d σ 1) t4
  refine ⟨bQ, ?_⟩
  have hκ : cK d σ 0 = torusM d σ 1 - 1 := by unfold cK; rw [torusM_one]; rfl
  have hk2 : pker d (σ + σ) 0 - 1 = torusM d σ 2 - 1 := by rw [pker_two_zero]
  have e1 := H.mean_E1 N
  have e2 := H.mean_E2 N
  have e3 := H.mean_EB N hN
  have e4 := H.mean_BB N hN
  simp only [hκ, hk2] at e1 e2
  have hQ : ∫ ω, Q1 d σ N X ω ∂μ
      = torusM d σ 1 * (1 - 1 / (N : ℝ) ^ 2
            * ∫ ω, ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω ∂μ
          + 3 * (1 / (N : ℝ) ^ 3 * ∫ ω, ∑ q ∈ Finset.range N,
              Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ)
          - 3 * (1 / (N : ℝ) ^ 4 * ∫ ω, stEB (cK d σ) X N ω ∂μ)
          + 1 / (N : ℝ) ^ 5 * ∫ ω, stBB (cK d σ) X N ω ∂μ) := by
    simp only [Q1]
    rw [integral_const_mul, integral_add (t3.integrable (μ := μ)) u4.integrable,
      integral_sub t2.integrable u3.integrable, integral_add t1.integrable u2.integrable,
      integral_sub b1.integrable (BM.const_mul (1 / (N : ℝ) ^ 2) bS1).integrable,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hQ]
  exact final_arith hN1 (torusM_one_ge hσ d) (torusM_ge_one hσ d (a := 2) (by norm_num))
    (torusM_anti hσ d (k := 1) (s := 2) le_rfl (by norm_num)) e1 e2 e3 e4

/-- **`prop:bias` for `k = 1` with self-loops on the flat torus with the heat kernel, general
    normalisation event.** For independent uniform points, `N ≥ 1` and `0 ≤ δ ≤ 1/8`:
    `|E Tr P - m₁ - β₁/N| ≤ 190 δ m₁³/N + 60 m₁⁵/N² + (N + 9 m₁⁵) · P(max_a |ρ_a - 1| > δ)`,
    `β₁ = m₁ (m₄ - 3m₃ + 3m₂ - m₁)` (the `β_1` of the proposition with `ρ = p(0)`: the sums
    `Σ_c` are empty for `k = 1`). -/
theorem bias_one_general [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) :
    |∫ ω, (torusWalk d σ N (fun j => X j ω)).trace ∂μ
        - (torusM d σ 1 + torusM d σ 1
          * (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1) / N)|
      ≤ 190 * δ * torusM d σ 1 ^ 3 / N + 60 * torusM d σ 1 ^ 5 / (N : ℝ) ^ 2
        + (N + 9 * torusM d σ 1 ^ 5)
          * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
  have H := torus_bvk X h_indep hX hlaw hσ
  have hN' : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  obtain ⟨bQ, hQm⟩ := Q1_mean X h_indep hX hlaw hσ N hN
  rw [← hMd] at hQm ⊢
  -- the trace
  have hT01 : ∀ ω (a : Fin N), 0 ≤ torusWalk d σ N (fun j => X j ω) a a
      ∧ torusWalk d σ N (fun j => X j ω) a a ≤ 1 := fun ω a =>
    walk_diag_unit _ _ (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) a
  have hTb : ∀ ω, |(torusWalk d σ N (fun j => X j ω)).trace| ≤ N := by
    intro ω
    have h0 : 0 ≤ (torusWalk d σ N (fun j => X j ω)).trace :=
      Finset.sum_nonneg fun a _ => (hT01 ω a).1
    rw [abs_of_nonneg h0]
    calc (torusWalk d σ N (fun j => X j ω)).trace
        ≤ ∑ _a : Fin N, (1 : ℝ) := Finset.sum_le_sum fun a _ => (hT01 ω a).2
      _ = N := by simp
  have bT : BM (fun ω => (torusWalk d σ N (fun j => X j ω)).trace) :=
    ⟨Finset.measurable_sum _ fun a _ => walk_entry_measurable hσ d X hX N a a, N, hTb⟩
  -- the event
  have hGm : MeasurableSet {ω | ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => measurableSet_le
      (continuous_abs.measurable.comp
        ((heatRho_sample_measurable hσ d X hX N a).sub measurable_const)) measurable_const
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Set Ω,
      Gc = {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  have hGcm : MeasurableSet Gc := by rw [hGc]; exact hGm.compl
  rw [← hGc]
  have bS2 : BM (fun ω => ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) :=
    BM.sum _ _ fun q _ => (H.bmH N q).mul (H.bmH N q)
  have hS2n : ∀ ω, 0 ≤ ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω := fun ω =>
    Finset.sum_nonneg fun q _ => _root_.mul_self_nonneg _
  have hpt : ∀ ω, |(torusWalk d σ N (fun j => X j ω)).trace - Q1 d σ N X ω|
      ≤ 95 * M * δ * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
          Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω)
        + (N + 9 * M ^ 5) * Gc.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ
    · have hnot : ω ∉ Gc := by rw [hGc]; exact fun h => h hω
      rw [Set.indicator_of_notMem hnot, mul_zero, add_zero, hMd]
      exact trace_Q1_good hσ N hN' X ω hδ hω
    · have hin : ω ∈ Gc := by rw [hGc]; exact hω
      rw [Set.indicator_of_mem hin, mul_one]
      have hq := Q1_abs_le hσ N hN' X ω
      rw [← hMd] at hq
      have h0 : 0 ≤ 95 * M * δ * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
          Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hδ0)
          (mul_nonneg (by positivity) (hS2n ω))
      obtain ⟨q1, q2⟩ := abs_le.mp hq
      obtain ⟨s1, s2⟩ := abs_le.mp (hTb ω)
      rw [abs_le]; constructor <;> linarith only [q1, q2, s1, s2, h0]
  have bg1 := BM.const_mul (95 * M * δ) (BM.const_mul (1 / (N : ℝ) ^ 3) bS2)
  have ig2 : Integrable (fun ω => (N + 9 * M ^ 5) * Gc.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hGcm).const_mul _
  obtain ⟨g1, hg1⟩ : ∃ g1 : Ω → ℝ, g1 = fun ω => 95 * M * δ * (1 / (N : ℝ) ^ 3
      * ∑ q ∈ Finset.range N, Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g2 : Ω → ℝ,
      g2 = fun ω => (N + 9 * M ^ 5) * Gc.indicator (fun _ => (1 : ℝ)) ω := ⟨_, rfl⟩
  have ig1' : Integrable g1 μ := by rw [hg1]; exact bg1.integrable
  have ig2' : Integrable g2 μ := by rw [hg2]; exact ig2
  have ig : Integrable (fun ω => g1 ω + g2 ω) μ := ig1'.add ig2'
  have hpt' : ∀ ω, |(torusWalk d σ N (fun j => X j ω)).trace - Q1 d σ N X ω|
      ≤ g1 ω + g2 ω := by rw [hg1, hg2]; exact hpt
  have hint := abs_int_le_int ((bT.sub bQ).integrable (μ := μ)) ig hpt'
  rw [integral_sub bT.integrable bQ.integrable, integral_add ig1' ig2', hg1, hg2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator_const (1 : ℝ) hGcm, smul_eq_mul, mul_one] at hint
  -- the second moment of the normalisation errors
  have e2 := H.mean_E2 N
  have r := H.rs_le hN
  rw [← hMd] at r
  have hS2 : ∫ ω, ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ ≤ N * (2 * N * M ^ 2) := by
    rw [e2]; exact mul_le_mul_of_nonneg_left r hNpos.le
  have hfirst : 95 * M * δ * (1 / (N : ℝ) ^ 3 * ∫ ω, ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ) ≤ 190 * δ * M ^ 3 / N := by
    have h1 : 1 / (N : ℝ) ^ 3 * ∫ ω, ∑ q ∈ Finset.range N,
        Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ
        ≤ 1 / (N : ℝ) ^ 3 * (N * (2 * N * M ^ 2)) :=
      mul_le_mul_of_nonneg_left hS2 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg (by norm_num) hM0) hδ0 :
      0 ≤ 95 * M * δ)
    have e : 95 * M * δ * (1 / (N : ℝ) ^ 3 * (N * (2 * N * M ^ 2))) = 190 * δ * M ^ 3 / N := by
      field_simp; ring
    linarith only [h2, e]
  obtain ⟨i1, i2⟩ := abs_le.mp hint
  obtain ⟨m1, m2⟩ := abs_le.mp hQm
  rw [abs_le]; constructor <;> linarith only [i1, i2, m1, m2, hfirst]

/-- **`prop:bias` for `k = 1` with self-loops, heat kernel on the flat torus.** Under the
    hypotheses of `norm_sample` (`σ ≤ 1`, `d ≥ 1`, `N ≥ 2`, `kernelC1 d · δ' ≤ 1` with
    `δ' = √(m₁ log N / N)`, i.e. `N ≥ N₀(d, σ)`):
    `|E Tr P - m₁ - β₁/N| ≤ 190 normC δ' m₁³/N + 60 m₁⁵/N² + (N + 9m₁⁵)/N³`,
    `β₁ = m₁ (m₄ - 3m₃ + 3m₂ - m₁)`.  The right-hand side is `O(√(log N) · N^{-3/2})` for fixed
    `σ` (the paper has `O(N^{-3/2})`; the factor `√(log N)` comes from bounding the cubic
    remainder by `δ ε²` on the normalisation event instead of by third moments). -/
theorem bias_one [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1) :
    |∫ ω, (torusWalk d σ N (fun j => X j ω)).trace ∂μ
        - (torusM d σ 1 + torusM d σ 1
          * (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1) / N)|
      ≤ 190 * (TorusReductionL1.normC d * δp) * torusM d σ 1 ^ 3 / N
        + 60 * torusM d σ 1 ^ 5 / (N : ℝ) ^ 2
        + (N + 9 * torusM d σ 1 ^ 5) * (1 / (N : ℝ) ^ 3) := by
  have hr : kernelC1 d * δp * Real.sqrt ((1 : ℕ) : ℝ) ≤ 1 := by
    rw [Nat.cast_one, Real.sqrt_one, mul_one]; exact hrange
  obtain ⟨h8, hp⟩ := TorusReductionL1.norm_sample hσ hσ1 d hd X h_indep hX hlaw N 1 hN2
    Nat.one_pos hMp hδp hr
  have hδ0 : 0 ≤ TorusReductionL1.normC d * δp := by
    rw [hδp]; exact mul_nonneg (TorusReductionL1.normC_nonneg d) (Real.sqrt_nonneg _)
  have h := bias_one_general X h_indep hX hlaw hσ N (by omega) hδ0 h8
  have hM0 : 0 ≤ torusM d σ 1 := zero_le_one.trans (torusM_one_ge hσ d)
  have hc : (0 : ℝ) ≤ N + 9 * torusM d σ 1 ^ 5 :=
    add_nonneg (Nat.cast_nonneg N) (mul_nonneg (by norm_num) (pow_nonneg hM0 5))
  have := mul_le_mul_of_nonneg_left hp hc
  linarith only [h, this]

end Sample

/-! ## Part 7: the Hoeffding structure of the variance (Step 2 of the proof of `prop:variance`)
for degenerate two-point statistics -/

section Variance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ : G → ℝ}
  {B V V0 : ℝ}

/-- `E ψ(X_i - X_j)² = V0` for `i ≠ j`, when `∫ ψ(x - z)² dν(z) = V0` for all `x`. -/
theorem deg_sq_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (hV : ∀ x, ∫ z, ψ (x - z) ^ 2 ∂ν = V0) {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, ψ (X i ω - X j ω) ^ 2 ∂μ = V0 := by
  haveI : IsProbabilityMeasure (μ.map (X i)) :=
    Measure.isProbabilityMeasure_map (H.meas i).aemeasurable
  rw [indep_integral_eq ν (X j) (X i) (H.meas j) (H.meas i) (H.indep.indepFun hij.symm)
    (H.law j) (fun p : G × G => ψ (p.2 - p.1) ^ 2)
    ((H.psi_meas.comp (measurable_snd.sub measurable_fst)).pow_const 2) (B := B ^ 2)
    (fun p => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (H.bound _) 2)]
  simp only [hV, integral_const, probReal_univ, one_smul]

/-- **Orthogonality of the off-diagonal summands, exact form**: the mean of a product of two
    off-diagonal summands is `V0` if the two index pairs coincide as sets and `0` otherwise. -/
theorem deg_pair_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (hV : ∀ x, ∫ z, ψ (x - z) ^ 2 ∂ν = V0) (i j i' j' : ℕ) :
    ∫ ω, aT ψ X i j ω * aT ψ X i' j' ω ∂μ
      = if i = j then 0 else V0 * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
          + (if i' = j ∧ j' = i then (1 : ℝ) else 0)) := by
  by_cases hij : i = j
  · have hz : (fun ω => aT ψ X i j ω * aT ψ X i' j' ω) = fun _ => (0 : ℝ) := by
      funext ω; simp [aT, hij]
    rw [if_pos hij, hz, integral_zero]
  rw [if_neg hij]
  by_cases hij' : i' = j'
  · have hz : (fun ω => aT ψ X i j ω * aT ψ X i' j' ω) = fun _ => (0 : ℝ) := by
      funext ω; simp [aT, hij']
    have n1 : ¬(i' = i ∧ j' = j) := fun h => hij (h.1.symm.trans (hij'.trans h.2))
    have n2 : ¬(i' = j ∧ j' = i) := fun h => hij (h.2.symm.trans (hij'.symm.trans h.1))
    rw [hz, integral_zero, if_neg n1, if_neg n2]; ring
  have hA : (fun ω => aT ψ X i j ω * aT ψ X i' j' ω)
      = fun ω => ψ (X i ω - X j ω) * ψ (X i' ω - X j' ω) := by
    funext ω; simp [aT, hij, hij']
  rw [hA]
  by_cases h1 : j ≠ i' ∧ j ≠ j'
  · have n1 : ¬(i' = i ∧ j' = j) := fun h => h1.2 h.2.symm
    have n2 : ¬(i' = j ∧ j' = i) := fun h => h1.1 h.1.symm
    rw [H.cross_right (a := i) (b := i') (c := j') (j := j) (Ne.symm hij) h1.1 h1.2,
      if_neg n1, if_neg n2]; ring
  by_cases h2 : i ≠ i' ∧ i ≠ j'
  · have n1 : ¬(i' = i ∧ j' = j) := fun h => h2.1 h.1.symm
    have n2 : ¬(i' = j ∧ j' = i) := fun h => h2.2 h.2.symm
    rw [H.cross_left (a := j) (b := i') (c := j') (j := i) hij h2.1 h2.2,
      if_neg n1, if_neg n2]; ring
  have h3 : (i' = i ∧ j' = j) ∨ (i' = j ∧ j' = i) := by omega
  rcases h3 with h | h
  · have n2 : ¬(i' = j ∧ j' = i) := fun h' => hij (h.1.symm.trans h'.1)
    have he : (fun ω => ψ (X i ω - X j ω) * ψ (X i' ω - X j' ω))
        = fun ω => ψ (X i ω - X j ω) ^ 2 := by
      funext ω; rw [h.1, h.2]; ring
    rw [if_pos h, if_neg n2, add_zero, mul_one, he]
    exact deg_sq_eq H hV hij
  · have n1 : ¬(i' = i ∧ j' = j) := fun h' => hij (h'.1.symm.trans h.1)
    have he : (fun ω => ψ (X i ω - X j ω) * ψ (X i' ω - X j' ω))
        = fun ω => ψ (X i ω - X j ω) ^ 2 := by
      funext ω
      have hh : ψ (X j ω - X i ω) = ψ (X i ω - X j ω) := by rw [← H.even, neg_sub]
      rw [h.1, h.2, hh]; ring
    rw [if_neg n1, if_pos h, zero_add, mul_one, he]
    exact deg_sq_eq H hV hij

/-- **The mean of the injective part vanishes.** -/
theorem deg_mean [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : Deg2 μ ν X ψ B V)
    (N : ℕ) : ∫ ω, Soff ψ X N ω ∂μ = 0 := by
  have hterm : ∀ i j, ∫ ω, aT ψ X i j ω ∂μ = 0 := by
    intro i j
    by_cases hij : i = j
    · have hz : aT ψ X i j = fun _ => (0 : ℝ) := by funext ω; simp [aT, hij]
      rw [hz, integral_zero]
    · have hA : aT ψ X i j = fun ω => ψ (X i ω - X j ω) := by funext ω; simp [aT, hij]
      rw [hA]
      exact indep_integral_zero ν (X j) (X i) (H.meas j) (H.meas i)
        (H.indep.indepFun (Ne.symm hij)) (H.law j) (fun p : G × G => ψ (p.2 - p.1))
        (H.psi_meas.comp (measurable_snd.sub measurable_fst)) (B := B) (fun p => H.bound _)
        (fun y => H.mean y)
  have hint : ∀ i j, Integrable (aT ψ X i j) μ := fun i j => (H.BM_aT i j).integrable
  show ∫ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, aT ψ X i j ω ∂μ = 0
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  exact Finset.sum_eq_zero fun j _ => hterm i j

/-- **The variance of the injective part, exactly**: `E (∑_{i≠j} ψ(X_i - X_j))² = 2 N (N-1) V0`.
    Only the Hoeffding component of order two is present: the pairs `{i,j}` are orthogonal and
    each contributes `(2ψ)²`-mass `4 V0`. -/
theorem deg_second_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg2 μ ν X ψ B V) (hV : ∀ x, ∫ z, ψ (x - z) ^ 2 ∂ν = V0) (N : ℕ) :
    ∫ ω, Soff ψ X N ω ^ 2 ∂μ = 2 * ((N : ℝ) * ((N : ℝ) - 1)) * V0 := by
  have hS2 : ∀ ω, Soff ψ X N ω ^ 2
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ j' ∈ Finset.range N, aT ψ X i j ω * aT ψ X i' j' ω := by
    intro ω
    unfold Soff
    rw [pow_two, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
  have h4 : ∫ ω, ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
        ∑ j' ∈ Finset.range N, aT ψ X i j ω * aT ψ X i' j' ω ∂μ
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ i' ∈ Finset.range N,
          ∑ j' ∈ Finset.range N, ∫ ω, aT ψ X i j ω * aT ψ X i' j' ω ∂μ :=
    integral_sum4 (Finset.range N) (fun i j i' j' ω => aT ψ X i j ω * aT ψ X i' j' ω)
      (fun i j i' j' => H.aT_prod_integrable i j i' j')
  simp_rw [hS2]
  rw [h4]
  have e : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N,
      ∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N, ∫ ω, aT ψ X i j ω * aT ψ X i' j' ω ∂μ
        = 2 * V0 - (if i = j then 2 * V0 else 0) := by
    intro i hi j hj
    simp_rw [deg_pair_eq H hV i j]
    by_cases hij : i = j
    · simp only [if_pos hij, Finset.sum_const_zero]; ring
    · simp only [if_neg hij]
      have e' : ∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N,
            V0 * ((if i' = i ∧ j' = j then (1 : ℝ) else 0)
              + (if i' = j ∧ j' = i then (1 : ℝ) else 0))
          = V0 * (∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N,
                (if i' = i ∧ j' = j then (1 : ℝ) else 0)
              + ∑ i' ∈ Finset.range N, ∑ j' ∈ Finset.range N,
                (if i' = j ∧ j' = i then (1 : ℝ) else 0)) := by
        simp only [← Finset.mul_sum, ← Finset.sum_add_distrib]
      rw [e', count1 N i j hi hj, count1 N j i hj hi]; ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => e i hi j hj]
  have e2 : ∀ i ∈ Finset.range N,
      ∑ j ∈ Finset.range N, (2 * V0 - (if i = j then 2 * V0 else 0))
        = ((N : ℝ) - 1) * (2 * V0) := by
    intro i hi
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos hi, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]; ring
  rw [Finset.sum_congr rfl e2, Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **The Hoeffding component of order one vanishes** (the statistic is invariant under a
    common translation): `E[(∑_{i≠j} ψ(X_i - X_j)) f(X_l)] = 0` for every bounded measurable `f`
    and every index `l`. -/
theorem deg_first_order [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg2 μ ν X ψ B V) (N l : ℕ) (f : G → ℝ) (hf : Measurable f) {Bf : ℝ}
    (hfb : ∀ u, |f u| ≤ Bf) :
    ∫ ω, Soff ψ X N ω * f (X l ω) ∂μ = 0 := by
  have hBf : 0 ≤ Bf := (abs_nonneg _).trans (hfb 0)
  have bf : BM (fun ω => f (X l ω)) := ⟨hf.comp (H.meas l), Bf, fun _ => hfb _⟩
  have hterm : ∀ i j, ∫ ω, aT ψ X i j ω * f (X l ω) ∂μ = 0 := by
    intro i j
    by_cases hij : i = j
    · have hz : (fun ω => aT ψ X i j ω * f (X l ω)) = fun _ => (0 : ℝ) := by
        funext ω; simp [aT, hij]
      rw [hz, integral_zero]
    have hA : (fun ω => aT ψ X i j ω * f (X l ω))
        = fun ω => ψ (X i ω - X j ω) * f (X l ω) := by funext ω; simp [aT, hij]
    rw [hA]
    by_cases hjl : j = l
    · -- the free index is `i`
      subst hjl
      have h := indep_integral_zero ν (X i) (X j) (H.meas i) (H.meas j)
        (H.indep.indepFun hij) (H.law i) (fun p : G × G => ψ (p.1 - p.2) * f p.2)
        ((H.psi_meas.comp (measurable_fst.sub measurable_snd)).mul (hf.comp measurable_snd))
        (B := B * Bf) (fun p => abs_mul_le' (H.bound _) (hfb _))
        (fun y => by
          show ∫ z, ψ (z - y) * f y ∂ν = 0
          have e : ∀ z, ψ (z - y) = ψ (y - z) := fun z => by rw [← H.even, neg_sub]
          simp_rw [e]
          rw [integral_mul_const, H.mean, zero_mul])
      exact h
    · -- the free index is `j`
      have hind : IndepFun (X j) (fun ω => (X i ω, X l ω)) μ :=
        (H.indep.indepFun_prodMk H.meas i l j hij (Ne.symm hjl)).symm
      exact indep_integral_zero ν (X j) (fun ω => (X i ω, X l ω)) (H.meas j)
        ((H.meas i).prodMk (H.meas l)) hind (H.law j)
        (fun p : G × (G × G) => ψ (p.2.1 - p.1) * f p.2.2)
        ((H.psi_meas.comp ((measurable_fst.comp measurable_snd).sub measurable_fst)).mul
          (hf.comp (measurable_snd.comp measurable_snd)))
        (B := B * Bf) (fun p => abs_mul_le' (H.bound _) (hfb _))
        (fun y => by
          show ∫ z, ψ (y.1 - z) * f y.2 ∂ν = 0
          rw [integral_mul_const, H.mean, zero_mul])
  have hint : ∀ i j, Integrable (fun ω => aT ψ X i j ω * f (X l ω)) μ := fun i j =>
    ((H.BM_aT i j).mul bf).integrable
  have e : ∀ ω, Soff ψ X N ω * f (X l ω)
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, aT ψ X i j ω * f (X l ω) := by
    intro ω
    unfold Soff
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall e),
    integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finset_sum _ fun j _ => hint i j]
  exact Finset.sum_eq_zero fun j _ => hterm i j

end Variance

section Variance2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {ψ : G → ℝ}
  {B V V0 : ℝ}

/-- **Mean and variance of a degenerate two-point statistic with the diagonal, exactly**:
    for `Z = N⁻² ∑_{i,j} ψ(X_i - X_j)`: `E Z = ψ(0)/N` and
    `E (Z - ψ(0)/N)² = 2 N (N-1) V0 / N⁴ = (1 - 1/N) · (1/N²) · ½ ∫ (2ψ)²`. -/
theorem deg_full_variance [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : Deg2 μ ν X ψ B V) (hV : ∀ x, ∫ z, ψ (x - z) ^ 2 ∂ν = V0) (N : ℕ) (hN : 0 < N) :
    ∫ ω, 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω) ∂μ
        = ψ 0 / N
    ∧ ∫ ω, (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
          - ψ 0 / N) ^ 2 ∂μ
        = 2 * ((N : ℝ) * ((N : ℝ) - 1)) * V0 / (N : ℝ) ^ 4 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have bS : BM (Soff ψ X N) := by
    show BM (fun ω => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, aT ψ X i j ω)
    exact BM.sum _ _ fun i _ => BM.sum _ _ fun j _ => H.BM_aT i j
  have e1 : ∀ ω, 1 / (N : ℝ) ^ 2
        * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
      = 1 / (N : ℝ) ^ 2 * Soff ψ X N ω + ψ 0 / N := by
    intro ω
    rw [OracleTwo.full_sum_eq ψ X N ω]; field_simp
  constructor
  · rw [integral_congr_ae (Filter.Eventually.of_forall e1),
      integral_add (BM.const_mul _ bS).integrable (integrable_const _), integral_const_mul,
      deg_mean H N, integral_const, probReal_univ, one_smul]
    ring
  · have e2 : ∀ ω, (1 / (N : ℝ) ^ 2
          * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω) - ψ 0 / N) ^ 2
        = 1 / (N : ℝ) ^ 4 * Soff ψ X N ω ^ 2 := by
      intro ω
      rw [e1 ω]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e2), integral_const_mul,
      deg_second_moment H hV N]
    ring

end Variance2

section VarianceTorus

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The variance of `Tr P̃²` (the statistic `Q_0` of `prop:variance` for `k = 2`, self-loops),
    exactly, on the flat torus with the heat kernel.**  With `H = 2 (p² - m₂)` (the pair kernel
    `H_{Q_0} = k Γ_k - k(k-1) μ_k` of Step 3 for `k = 2`):
    `E Tr P̃² = m₂ + (m₁² - m₂)/N` and
    `Var Tr P̃² = 2 N (N-1) ∫ (p² - m₂)² / N⁴ = (1 - 1/N) · (1/N²) · ½ ∫ H²`.
    This is NOT the variance of the trace of the normalised walk. -/
theorem var_trace_two [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        pker d σ (X i ω - X j ω) ^ 2 ∂μ
      = torusM d σ 2 + (torusM d σ 1 ^ 2 - torusM d σ 2) / N
    ∧ ∫ ω, (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          pker d σ (X i ω - X j ω) ^ 2
          - (torusM d σ 2 + (torusM d σ 1 ^ 2 - torusM d σ 2) / N)) ^ 2 ∂μ
      = 2 * ((N : ℝ) * ((N : ℝ) - 1))
          * (∫ u, (pker d σ u ^ 2 - torusM d σ 2) ^ 2 ∂flatTorusMeasure d) / (N : ℝ) ^ 4 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hM0 : 0 ≤ torusM d σ 1 := zero_le_one.trans (torusM_one_ge hσ d)
  have H0 : Deg2 μ (flatTorusMeasure d) X (phi0 d σ 1) (torusM d σ 1 * torusM d σ 1)
      (torusM d σ 1 * torusM d σ 1 ^ 2) :=
    { indep := h_indep
      meas := hX
      law := hlaw
      psi_meas := (phi0_continuous hσ d 1 le_rfl).measurable
      bound := phi0_bound hσ d 1 le_rfl
      even := phi0_even d σ 1
      mean := phi0_mean hσ d 1 le_rfl
      var := phi0_var hσ d 1 le_rfl
      V_nonneg := mul_nonneg hM0 (_root_.sq_nonneg _) }
  have hfun : (fun u : FlatTorus d => pker d σ u ^ 2 - torusM d σ 2) = phi0 d σ 1 := by
    funext u
    simp only [phi0, pker, heatP_one, pow_two, Nat.reduceAdd]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : FlatTorus d → ℝ,
      ψ = fun u : FlatTorus d => pker d σ u ^ 2 - torusM d σ 2 := ⟨_, rfl⟩
  have H1 : Deg2 μ (flatTorusMeasure d) X ψ (torusM d σ 1 * torusM d σ 1)
      (torusM d σ 1 * torusM d σ 1 ^ 2) := by rw [hψ, hfun]; exact H0
  obtain ⟨V0, hV0⟩ : ∃ V0 : ℝ, V0 = ∫ u, ψ u ^ 2 ∂flatTorusMeasure d := ⟨_, rfl⟩
  have hV : ∀ x, ∫ z, ψ (x - z) ^ 2 ∂flatTorusMeasure d = V0 := by
    intro x
    haveI : (flatTorusMeasure d).IsNegInvariant :=
      Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
    rw [hV0]
    exact integral_sub_left_eq_self (fun u => ψ u ^ 2) (flatTorusMeasure d) x
  obtain ⟨g1, g2⟩ := deg_full_variance H1 hV N hN
  have hψ0 : ψ 0 = torusM d σ 1 ^ 2 - torusM d σ 2 := by rw [hψ, torusM_one]; rfl
  have e : ∀ ω, 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        pker d σ (X i ω - X j ω) ^ 2
      = 1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)
        + torusM d σ 2 := by
    intro ω
    have : ∀ i ∈ Finset.range N, ∀ j ∈ Finset.range N, pker d σ (X i ω - X j ω) ^ 2
        = ψ (X i ω - X j ω) + torusM d σ 2 := fun i _ j _ => by rw [hψ]; ring
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => this i hi j hj]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have bψ : BM (fun ω => 1 / (N : ℝ) ^ 2
      * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ψ (X i ω - X j ω)) :=
    BM.const_mul _ (BM.sum _ _ fun i _ => BM.sum _ _ fun j _ => H1.BM_psi i j)
  have hV0' : V0 = ∫ u, (pker d σ u ^ 2 - torusM d σ 2) ^ 2 ∂flatTorusMeasure d := by
    rw [hV0, hψ]
  rw [← hV0']
  constructor
  · rw [integral_congr_ae (Filter.Eventually.of_forall e),
      integral_add bψ.integrable (integrable_const _), g1, hψ0, integral_const, probReal_univ,
      one_smul]
    ring
  · have e2 : ∀ ω, (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          pker d σ (X i ω - X j ω) ^ 2
          - (torusM d σ 2 + (torusM d σ 1 ^ 2 - torusM d σ 2) / N)) ^ 2
        = (1 / (N : ℝ) ^ 2 * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            ψ (X i ω - X j ω) - ψ 0 / N) ^ 2 := by
      intro ω; rw [e ω, hψ0]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall e2)]
    exact g2

end VarianceTorus

/-! ## Part 8: the Hoeffding component of order one of `Tr P^k` itself vanishes
(Step 2 of the proof of `prop:variance`: "`E[Q | x_1]` is constant", here for the trace of the
normalised walk and every `k`, without the polynomial approximation) -/

section FirstOrder

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableSub₂ G] {ν : Measure G}

/-- The law of a tuple of independent points with a translation-invariant law is invariant
    under a common translation. -/
theorem tuple_shift [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant]
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (S : Finset ℕ) (Ψ : (S → G) → ℝ) (hΨ : Measurable Ψ)
    (x : G) :
    ∫ ω, Ψ (fun t : S => X t ω - x) ∂μ = ∫ ω, Ψ (fun t : S => X t ω) ∂μ := by
  have hYm : Measurable (fun ω (t : S) => X t ω) := measurable_pi_lambda _ fun t => hX t
  have h1 : iIndepFun (fun (t : S) => X t) μ := h_indep.precomp Subtype.val_injective
  have hpi : μ.map (fun ω (t : S) => X t ω) = Measure.pi (fun _ : S => ν) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun t : S => (hX t).aemeasurable)).mp h1]
    congr 1; funext t; exact hlaw t
  have hsh : Measurable fun y : S → G => fun t : S => y t - x :=
    measurable_pi_lambda _ fun t => (measurable_pi_apply t).sub measurable_const
  have e1 : ∫ ω, Ψ (fun t : S => X t ω - x) ∂μ
      = ∫ y, Ψ (fun t => y t - x) ∂(μ.map fun ω (t : S) => X t ω) :=
    (integral_map hYm.aemeasurable (hΨ.comp hsh).aestronglyMeasurable).symm
  have e2 : ∫ ω, Ψ (fun t : S => X t ω) ∂μ = ∫ y, Ψ y ∂(μ.map fun ω (t : S) => X t ω) :=
    (integral_map hYm.aemeasurable hΨ.aestronglyMeasurable).symm
  rw [e1, e2, hpi]
  have e3 : ∀ y : S → G, (fun t => y t - x) = (fun _ : S => -x) + y := fun y => by
    funext t; simp [sub_eq_neg_add]
  simp_rw [e3]
  exact integral_add_left_eq_self Ψ (fun _ : S => -x)

/-- **The first-order Hoeffding projection of a translation-invariant statistic vanishes.**
    `X_j` independent with a translation-invariant law `ν`; `Φ` a bounded measurable function of
    the points over a finite index set `T`, invariant under a common translation; `l ∈ T`; `f`
    bounded measurable.  Then `E[Φ · f(X_l)] = E[Φ] · E[f(X_l)]`, i.e. `E[Φ | X_l] = E Φ`. -/
theorem first_order_vanish [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [ν.IsAddLeftInvariant] (X : ℕ → Ω → G) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (T : Finset ℕ) {l : ℕ}
    (Φ : (T → G) → ℝ) (hΦ : Measurable Φ) {BΦ : ℝ} (hΦb : ∀ y, |Φ y| ≤ BΦ)
    (hinv : ∀ (y : T → G) (z : G), Φ (fun t => y t - z) = Φ y)
    (f : G → ℝ) (hf : Measurable f) {Bf : ℝ} (hfb : ∀ u, |f u| ≤ Bf) :
    ∫ ω, Φ (fun t : T => X t ω) * f (X l ω) ∂μ
      = (∫ ω, Φ (fun t : T => X t ω) ∂μ) * ∫ ω, f (X l ω) ∂μ := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S = T.erase l := ⟨_, rfl⟩
  have hlS : l ∉ S := by rw [hS]; exact Finset.notMem_erase l T
  have hST : ∀ t : T, (t : ℕ) ≠ l → (t : ℕ) ∈ S := fun t ht => by
    rw [hS]; exact Finset.mem_erase.mpr ⟨ht, t.2⟩
  obtain ⟨gl, hgl⟩ : ∃ gl : (S → G) → (T → G),
      gl = fun (w : S → G) (t : T) => if h : (t : ℕ) = l then 0 else w ⟨t, hST t h⟩ :=
    ⟨_, rfl⟩
  have hglm : Measurable gl := by
    rw [hgl]; refine measurable_pi_lambda _ fun t => ?_
    by_cases h : (t : ℕ) = l
    · simp only [dif_pos h]; exact measurable_const
    · simp only [dif_neg h]; exact measurable_pi_apply _
  obtain ⟨Φ0, hΦ0⟩ : ∃ Φ0 : (S → G) → ℝ, Φ0 = fun w => Φ (gl w) := ⟨_, rfl⟩
  have hΦ0m : Measurable Φ0 := by rw [hΦ0]; exact hΦ.comp hglm
  have hΦ0b : ∀ w, |Φ0 w| ≤ BΦ := fun w => by rw [hΦ0]; exact hΦb _
  have hBΦ : 0 ≤ BΦ := (abs_nonneg _).trans (hΦb (fun _ => 0))
  have hrep : ∀ ω, Φ (fun t : T => X t ω) = Φ0 (fun s : S => X s ω - X l ω) := by
    intro ω
    rw [hΦ0, ← hinv (fun t : T => X t ω) (X l ω)]
    congr 1
    funext t
    rw [hgl]
    by_cases h : (t : ℕ) = l
    · simp only [dif_pos h]; rw [h, sub_self]
    · simp only [dif_neg h]
  have hind0 := h_indep.indepFun_finset S {l} (Finset.disjoint_singleton_right.mpr hlS) hX
  have hind : IndepFun (fun ω (s : S) => X s ω) (X l) μ :=
    hind0.comp (φ := id)
      (ψ := fun u : (({l} : Finset ℕ) → G) => u ⟨l, Finset.mem_singleton_self l⟩)
      measurable_id (measurable_pi_apply _)
  have hYm : Measurable (fun ω (s : S) => X s ω) := measurable_pi_lambda _ fun s => hX s
  haveI : IsProbabilityMeasure (μ.map fun ω (s : S) => X s ω) :=
    Measure.isProbabilityMeasure_map hYm.aemeasurable
  obtain ⟨c0, hc0⟩ : ∃ c0 : ℝ, c0 = ∫ ω, Φ0 (fun s : S => X s ω) ∂μ := ⟨_, rfl⟩
  have hsh : ∀ x : G, Measurable fun y : S → G => fun s : S => y s - x := fun x =>
    measurable_pi_lambda _ fun s => (measurable_pi_apply s).sub measurable_const
  have hin : ∀ x : G, ∫ y, Φ0 (fun s => y s - x) ∂(μ.map fun ω (s : S) => X s ω) = c0 := by
    intro x
    have e : ∫ y, Φ0 (fun s => y s - x) ∂(μ.map fun ω (s : S) => X s ω)
        = ∫ ω, Φ0 (fun s : S => X s ω - x) ∂μ :=
      integral_map hYm.aemeasurable (hΦ0m.comp (hsh x)).aestronglyMeasurable
    rw [e, hc0]
    exact tuple_shift X h_indep hX hlaw S Φ0 hΦ0m x
  have key : ∀ (g : G → ℝ), Measurable g → ∀ Bg : ℝ, (∀ u, |g u| ≤ Bg) →
      ∫ ω, Φ (fun t : T => X t ω) * g (X l ω) ∂μ = c0 * ∫ ω, g (X l ω) ∂μ := by
    intro g hg Bg hgb
    simp_rw [hrep]
    have h := indep_integral_eq (μ.map fun ω (s : S) => X s ω) (fun ω (s : S) => X s ω) (X l)
      hYm (hX l) hind rfl
      (fun p : (S → G) × G => Φ0 (fun s => p.1 s - p.2) * g p.2)
      ((hΦ0m.comp (measurable_pi_lambda _ fun s =>
        ((measurable_pi_apply s).comp measurable_fst).sub measurable_snd)).mul
        (hg.comp measurable_snd))
      (B := BΦ * Bg) (fun p => abs_mul_le' (hΦ0b _) (hgb _))
    refine h.trans ?_
    have h2 : ∀ x : G, ∫ y, Φ0 (fun s => y s - x) * g x ∂(μ.map fun ω (s : S) => X s ω)
        = c0 * g x := fun x => by rw [integral_mul_const, hin x]
    rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_const_mul,
      integral_map (hX l).aemeasurable hg.aestronglyMeasurable]
  have k1 := key f hf Bf hfb
  have k2 := key (fun _ => 1) measurable_const 1 (fun _ => by rw [abs_one])
  simp only [mul_one, integral_const, probReal_univ, one_smul] at k2
  rw [k1, k2]

end FirstOrder

section TraceFirstOrder

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Powers of a matrix with nonnegative entries and row sums at most one have the same
    properties. -/
theorem substoch_pow {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (h0 : ∀ a b, 0 ≤ P a b) (h1 : ∀ a, ∑ b, P a b ≤ 1) (k : ℕ) :
    (∀ a b, 0 ≤ (P ^ k) a b) ∧ ∀ a, ∑ b, (P ^ k) a b ≤ 1 := by
  induction k with
  | zero =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ k ih =>
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun c _ => mul_nonneg (ih.1 a c) (h0 c b)
    · have e : ∑ b, (P ^ (k + 1)) a b = ∑ c, (P ^ k) a c * ∑ b, P c b := by
        simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
        exact Finset.sum_comm
      rw [e]
      calc ∑ c, (P ^ k) a c * ∑ b, P c b ≤ ∑ c, (P ^ k) a c * 1 :=
            Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (h1 c) (ih.1 a c)
        _ ≤ 1 := by simp only [mul_one]; exact ih.2 a

/-- `|Tr P^k| ≤ N` for a walk matrix on `N` vertices built from nonnegative data. -/
theorem walk_pow_trace_le {N : ℕ} (K : Fin N → Fin N → ℝ) (ρ : Fin N → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hρ : ∀ i, 0 ≤ ρ i) (k : ℕ) :
    |((walkMatrix K ρ) ^ k).trace| ≤ N := by
  have ht : ∀ i l, 0 ≤ K i l / (ρ i * ρ l) := fun i l =>
    div_nonneg (hK i l) (mul_nonneg (hρ i) (hρ l))
  have hs : ∀ i, 0 ≤ ∑ l, K i l / (ρ i * ρ l) := fun i => Finset.sum_nonneg fun l _ => ht i l
  have h0 : ∀ a b, 0 ≤ walkMatrix K ρ a b := fun a b => by
    simp only [walkMatrix, Matrix.of_apply]; exact div_nonneg (ht a b) (hs a)
  have h1 : ∀ a, ∑ b, walkMatrix K ρ a b ≤ 1 := fun a => by
    simp only [walkMatrix, Matrix.of_apply]
    rw [← Finset.sum_div]; exact div_self_le_one _
  obtain ⟨p0, p1⟩ := substoch_pow (walkMatrix K ρ) h0 h1 k
  have hd : ∀ a, ((walkMatrix K ρ) ^ k) a a ≤ 1 := fun a =>
    (Finset.single_le_sum (fun b _ => p0 a b) (Finset.mem_univ a)).trans (p1 a)
  have hn : 0 ≤ ((walkMatrix K ρ) ^ k).trace := Finset.sum_nonneg fun a _ => p0 a a
  rw [abs_of_nonneg hn]
  calc ((walkMatrix K ρ) ^ k).trace ≤ ∑ _a : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun a _ => hd a
    _ = N := by simp

/-- The walk matrix depends only on the differences of the first `N` points. -/
theorem torusWalk_congr (d : ℕ) (σ : ℝ) (N : ℕ) (x x' : ℕ → FlatTorus d)
    (h : ∀ a, a < N → ∀ b, b < N → x a - x b = x' a - x' b) :
    torusWalk d σ N x = torusWalk d σ N x' := by
  have hK : torusK d σ N x = torusK d σ N x' := by
    funext a j; unfold torusK; rw [h a a.2 j j.2]
  have hR : torusRho d σ N x = torusRho d σ N x' := by
    funext a; unfold torusRho heatRho
    congr 1
    exact Finset.sum_congr rfl fun l hl => by rw [h a a.2 l (Finset.mem_range.mp hl)]
  unfold torusWalk; rw [hK, hR]

/-- **`E[Tr P^k | X_l] = E Tr P^k`** for the normalised walk on the flat torus (heat kernel,
    self-loops), every `k` and every `N ≥ 1`: for every bounded measurable `f` and `l < N`,
    `E[Tr P^k · f(X_l)] = E[Tr P^k] · E[f(X_l)]`.  The Hoeffding component of order one of
    `Tr P^k` vanishes exactly (translation invariance); hence
    `Var Tr P^k = ∑_{j ≥ 2} binom(N, j) E η_j²`. -/
theorem trace_pow_first_order [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N k : ℕ) {l : ℕ}
    (f : FlatTorus d → ℝ) (hf : Measurable f) {Bf : ℝ} (hfb : ∀ u, |f u| ≤ Bf) :
    ∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ k).trace * f (X l ω) ∂μ
      = (∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ k).trace ∂μ) * ∫ ω, f (X l ω) ∂μ := by
  classical
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = Finset.range N := ⟨_, rfl⟩
  obtain ⟨ext, hext⟩ : ∃ ext : ℕ → (T → FlatTorus d) → FlatTorus d,
      ext = fun j y => if h : j ∈ T then y ⟨j, h⟩ else 0 := ⟨_, rfl⟩
  have hextm : ∀ j, Measurable (ext j) := by
    intro j; rw [hext]
    by_cases h : j ∈ T
    · simp only [dif_pos h]; exact measurable_pi_apply _
    · simp only [dif_neg h]; exact measurable_const
  have hmem : ∀ a, a < N → a ∈ T := fun a ha => by rw [hT]; exact Finset.mem_range.mpr ha
  have hexta : ∀ (y : T → FlatTorus d) (a : ℕ) (ha : a < N), ext a y = y ⟨a, hmem a ha⟩ :=
    fun y a ha => by rw [hext]; simp only [dif_pos (hmem a ha)]
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : (T → FlatTorus d) → ℝ,
      Φ = fun y => ((torusWalk d σ N (fun j => ext j y)) ^ k).trace := ⟨_, rfl⟩
  have hΦm : Measurable Φ := by
    rw [hΦd]
    exact Finset.measurable_sum _ fun a _ =>
      walk_pow_entry_measurable hσ d ext hextm N k a a
  have hΦb : ∀ y, |Φ y| ≤ N := fun y => by
    rw [hΦd]
    exact walk_pow_trace_le _ _ (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) k
  have hinv : ∀ (y : T → FlatTorus d) (z : FlatTorus d), Φ (fun t => y t - z) = Φ y := by
    intro y z
    rw [hΦd]
    simp only
    rw [torusWalk_congr d σ N (fun j => ext j (fun t => y t - z)) (fun j => ext j y)
      (fun a ha b hb => by
        simp only [hexta _ a ha, hexta _ b hb]; exact sub_sub_sub_cancel_right _ _ _)]
  have hrep : ∀ ω, Φ (fun t : T => X t ω) = ((torusWalk d σ N (fun j => X j ω)) ^ k).trace := by
    intro ω
    rw [hΦd]
    simp only
    rw [torusWalk_congr d σ N (fun j => ext j (fun t : T => X t ω)) (fun j => X j ω)
      (fun a ha b hb => by simp only [hexta _ a ha, hexta _ b hb])]
  have h := first_order_vanish X h_indep hX hlaw T (l := l) Φ hΦm hΦb hinv f hf hfb
  simp_rw [hrep] at h
  exact h

end TraceFirstOrder

end BiasVariance


namespace BiasVariance2

open PiBound CTG.Reals.TorusReduction BiasVariance

/-! # A61: continuation of `BiasVariance` (`prop:bias`, `prop:variance`, Appendix G)

* `trace_pow_gamma`: Step 1 of the proof of `prop:bias` for EVERY `k` as a matrix identity,
  `Tr P^k = Tr (P̃ · diag γ)^k`.
* `gamma_vertex`, `pair_gamma`, `trace_two_expansion`: Steps 2–3 for `k = 2` (deterministic,
  on `max |ε| ≤ δ ≤ 1/8`): `Tr P²` up to second order with remainder `580 δ M (1/N) ∑ ε²`.
* `beta_one_nonpos`: `β₁ ≤ 0` on the flat torus; `bias_one_noloops`: `Tr P° = 0`.

NOT proved here: the expectations of the nine polynomial statistics for `k = 2` (so no
`E Tr P² = m₂ + β₂/N + …`), general `k` beyond Step 1, `prop:variance` for the normalised
walk. -/

theorem mul_pow_succ_comm {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) (k : ℕ) :
    (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ (B * A)]; simp only [Matrix.mul_assoc]

theorem trace_pow_comm {n : Type} [Fintype n] [DecidableEq n] (A B : Matrix n n ℝ) (k : ℕ) :
    ((A * B) ^ k).trace = ((B * A) ^ k).trace := by
  cases k with
  | zero => simp
  | succ k =>
    rw [mul_pow_succ_comm, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
      ← pow_succ]

/-- The walk matrix as `diag(1/r) · P̃ · diag(u)`, `u = 1/ρ`, `r_i = (1/N) ∑_l K_il u_l`. -/
theorem walk_factor {N : ℕ} (K : Fin N → Fin N → ℝ) (ρ : Fin N → ℝ) (hρ : ∀ i, ρ i ≠ 0) :
    walkMatrix K ρ = Matrix.diagonal (fun i => 1 / (1 / (N : ℝ) * ∑ l, K i l / ρ l))
      * (Matrix.of (fun i j => K i j / (N : ℝ)) * Matrix.diagonal (fun j => 1 / ρ j)) := by
  ext b j
  rw [walkMatrix_apply' K ρ b j (hρ b), Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.of_apply]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp b.pos)
  have hρj := hρ j
  by_cases hS : ∑ l, K b l / ρ l = 0
  · rw [hS]; simp
  · field_simp

/-- **Step 1 of the proof of `prop:bias`, every `k`** (`eq:bias-identity` in matrix form):
    `Tr P^k = Tr (P̃ · diag γ)^k` with `P̃ = K/N`, `γ_i = u_i / r_i`. -/
theorem trace_pow_gamma {N : ℕ} (K : Fin N → Fin N → ℝ) (ρ : Fin N → ℝ) (hρ : ∀ i, ρ i ≠ 0)
    (k : ℕ) :
    ((walkMatrix K ρ) ^ k).trace
      = ((Matrix.of (fun i j => K i j / (N : ℝ))
          * Matrix.diagonal (fun i => 1 / ρ i * (1 / (1 / (N : ℝ) * ∑ l, K i l / ρ l)))) ^ k).trace := by
  rw [walk_factor K ρ hρ, trace_pow_comm, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]

/-- Step 2 at one vertex (as inside `trace_one_expansion`), exported. -/
theorem gamma_vertex {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ) (ρ ε : Fin N → ℝ) {δ : ℝ}
    (hK0 : ∀ i j, 0 ≤ K i j) (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1)
    (hδ : δ ≤ 1 / 8) (hεδ : ∀ i, |ε i| ≤ δ) (i : Fin N) :
    |1 / ρ i * (1 / (1 / (N : ℝ) * ∑ l, K i l / ρ l))
        - (1 - 2 * ε i + 1 / (N : ℝ) * ∑ l, K i l * ε l + 3 * ε i ^ 2
            - 3 * ε i * (1 / (N : ℝ) * ∑ l, K i l * ε l)
            + (1 / (N : ℝ) * ∑ l, K i l * ε l) ^ 2 - 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)|
      ≤ 44 * δ * (ε i ^ 2 + 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    ∧ |1 / (N : ℝ) * ∑ l, K i l * ε l| ≤ 9 / 8 * δ
    ∧ (1 / (N : ℝ) * ∑ l, K i l * ε l) ^ 2 ≤ 9 / 8 * (1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    ∧ 0 ≤ 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2
    ∧ 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2 ≤ 9 / 8 * δ ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hδ0 : 0 ≤ δ := (abs_nonneg (ε ⟨0, hN⟩)).trans (hεδ _)
  have hl : ∀ l, -δ ≤ ε l ∧ ε l ≤ δ := fun l => abs_le.mp (hεδ l)
  have hρe : ∀ l, ρ l = 1 + ε l := fun l => by rw [hε l]; ring
  have hρlo : 7 / 8 ≤ ρ i := by rw [hρe i]; linarith only [(hl i).1, hδ]
  have hρhi : ρ i ≤ 9 / 8 := by rw [hρe i]; linarith only [(hl i).2, hδ]
  have H := row_bounds hN (K i) ε (fun l => hK0 i l) hδ hεδ (hρ i) hρhi
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 / (N : ℝ) * ∑ l, K i l * ε l := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2 := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ,
      z = 1 / (N : ℝ) * ∑ l, K i l * (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 / (N : ℝ) * ∑ l, K i l / (1 + ε l) := ⟨_, rfl⟩
  rw [← hb, ← hs, ← hz, ← hR] at H
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  rw [← hb, ← hs]
  obtain ⟨hz1, hz2⟩ := abs_le.mp h5
  obtain ⟨hb1, hb2⟩ := abs_le.mp h1
  have hδs : δ * s ≤ 1 / 8 * s := mul_le_mul_of_nonneg_right hδ h3
  have hRpos : 0 < R := by rw [h6]; linarith only [hρlo, hb2, hδ, hz1, hδs, h3]
  have hρi : ρ i ≠ 0 := by linarith only [hρlo]
  have hsumR : 1 / (N : ℝ) * ∑ l, K i l / ρ l = R := by
    rw [hR]
    have : ∑ l, K i l / ρ l = ∑ l, K i l / (1 + ε l) :=
      Finset.sum_congr rfl fun l _ => by rw [hρe l]
    rw [this]
  rw [hsumR]
  refine ⟨?_, h1, h2, h3, h4⟩
  have hγ : 1 / ρ i * (1 / R) * ((1 + ε i) * (1 + (ε i - b + (s + z)))) = 1 := by
    have e : 1 + (ε i - b + (s + z)) = R := by rw [h6, hρe i]; ring
    rw [e, ← hρe i]
    field_simp
  have h := gamma_second_order hδ0 hδ (hεδ i) h1 h2 h3 h4 h5 hγ
  exact h

/-- The product of two vertex factors to second order (Step 3 for two positions). -/
theorem pair_gamma {δ g1 g2 a1 a2 c1 c2 q1 q2 : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8)
    (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2) (hq1' : q1 ≤ 17 / 8 * δ ^ 2) (hq2' : q2 ≤ 17 / 8 * δ ^ 2)
    (h1 : |g1 - (1 + a1 + c1)| ≤ 44 * δ * q1) (h2 : |g2 - (1 + a2 + c2)| ≤ 44 * δ * q2)
    (ha1 : |a1| ≤ 4 * δ) (ha2 : |a2| ≤ 4 * δ) (hc1 : |c1| ≤ 5 * q1) (hc2 : |c2| ≤ 5 * q2) :
    |g1 * g2 - (1 + (a1 + c1) + (a2 + c2) + a1 * a2)| ≤ 121 * δ * (q1 + q2) := by
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, R1 = g1 - (1 + a1 + c1) := ⟨_, rfl⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, R2 = g2 - (1 + a2 + c2) := ⟨_, rfl⟩
  rw [← hR1] at h1
  rw [← hR2] at h2
  have hδq1 : δ * q1 ≤ 1 / 8 * q1 := mul_le_mul_of_nonneg_right hδ hq1
  have hδq2 : δ * q2 ≤ 1 / 8 * q2 := mul_le_mul_of_nonneg_right hδ hq2
  have d1 : 0 ≤ δ * q1 := mul_nonneg hδ0 hq1
  have d2 : 0 ≤ δ * q2 := mul_nonneg hδ0 hq2
  have hu1 : |c1 + R1| ≤ 11 * q1 := by
    obtain ⟨x1, x2⟩ := abs_le.mp hc1; obtain ⟨y1, y2⟩ := abs_le.mp h1
    rw [abs_le]; constructor <;> linarith only [x1, x2, y1, y2, hδq1]
  have hu2 : |c2 + R2| ≤ 11 * q2 := by
    obtain ⟨x1, x2⟩ := abs_le.mp hc2; obtain ⟨y1, y2⟩ := abs_le.mp h2
    rw [abs_le]; constructor <;> linarith only [x1, x2, y1, y2, hδq2]
  have e : g1 * g2 - (1 + (a1 + c1) + (a2 + c2) + a1 * a2)
      = R1 + R2 + a1 * (c2 + R2) + (c1 + R1) * a2 + (c1 + R1) * (c2 + R2) := by
    rw [hR1, hR2]; ring
  have t1 := abs_mul_le' ha1 hu2
  have t2 := abs_mul_le' hu1 ha2
  have t3 := abs_mul_le' hu1 hu2
  have hδ2 : δ ^ 2 ≤ δ / 8 := by
    have := mul_nonneg hδ0 (sub_nonneg.mpr hδ); linarith only [this]
  have hqq : q1 * q2 ≤ 17 / 64 * (δ * q1) := by
    have := mul_le_mul_of_nonneg_left hq2' hq1
    have h' := mul_le_mul_of_nonneg_right hδ2 hq1
    linarith only [this, h']
  obtain ⟨r1, r1'⟩ := abs_le.mp h1
  obtain ⟨r2, r2'⟩ := abs_le.mp h2
  obtain ⟨s1, s1'⟩ := abs_le.mp t1
  obtain ⟨s2, s2'⟩ := abs_le.mp t2
  obtain ⟨s3, s3'⟩ := abs_le.mp t3
  rw [e, abs_le]
  constructor <;> linarith only [r1, r1', r2, r2', s1, s1', s2, s2', s3, s3', hqq, d1, d2]

/-- **Steps 1–3 of the proof of `prop:bias` for `k = 2`, deterministic.** `K` symmetric with
    values in `[0, M]`, `ρ_i = (1/N) ∑_l K_il = 1 + ε_i`, `|ε_i| ≤ δ ≤ 1/8`; `w_ij = P̃_ij P̃_ji`,
    `φ¹ = -2ε + P̃ε`, `φ² = 3ε² - 3ε P̃ε + (P̃ε)² - P̃ε²`.  Then
    `|Tr P² - ∑_{i,j} w_ij (1 + (φ¹_i + φ²_i) + (φ¹_j + φ²_j) + φ¹_i φ¹_j)| ≤ 580 δ M (1/N) ∑ ε²`.
    The subtracted sum is `Q_0 + Q_1 + Q_2 + Q_3` of the paper for `k = 2` (for `k = 2` the
    product over the cycle has two factors, so there is no term `E_3`). -/
theorem trace_two_expansion {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ) (ρ ε : Fin N → ℝ)
    {M δ : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hKM : ∀ i j, K i j ≤ M) (hsym : ∀ i j, K i j = K j i)
    (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1)
    (hδ : δ ≤ 1 / 8) (hεδ : ∀ i, |ε i| ≤ δ) :
    |((walkMatrix K ρ) ^ 2).trace
        - ∑ i, ∑ j, K i j / (N : ℝ) * (K j i / (N : ℝ))
          * (1 + ((-2 * ε i + 1 / (N : ℝ) * ∑ l, K i l * ε l)
                + (3 * ε i ^ 2 - 3 * ε i * (1 / (N : ℝ) * ∑ l, K i l * ε l)
                  + (1 / (N : ℝ) * ∑ l, K i l * ε l) ^ 2 - 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2))
              + ((-2 * ε j + 1 / (N : ℝ) * ∑ l, K j l * ε l)
                + (3 * ε j ^ 2 - 3 * ε j * (1 / (N : ℝ) * ∑ l, K j l * ε l)
                  + (1 / (N : ℝ) * ∑ l, K j l * ε l) ^ 2 - 1 / (N : ℝ) * ∑ l, K j l * ε l ^ 2))
              + (-2 * ε i + 1 / (N : ℝ) * ∑ l, K i l * ε l)
                * (-2 * ε j + 1 / (N : ℝ) * ∑ l, K j l * ε l))|
      ≤ 580 * δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  have hδ0 : 0 ≤ δ := (abs_nonneg (ε ⟨0, hN⟩)).trans (hεδ _)
  have hM0 : 0 ≤ M := (hK0 ⟨0, hN⟩ ⟨0, hN⟩).trans (hKM _ _)
  have hl : ∀ l, -δ ≤ ε l ∧ ε l ≤ δ := fun l => abs_le.mp (hεδ l)
  have hρe : ∀ l, ρ l = 1 + ε l := fun l => by rw [hε l]; ring
  have hρlo : ∀ l, 7 / 8 ≤ ρ l := fun l => by rw [hρe l]; linarith only [(hl l).1, hδ]
  have hρhi : ∀ l, ρ l ≤ 9 / 8 := fun l => by rw [hρe l]; linarith only [(hl l).2, hδ]
  have hρ0 : ∀ l, ρ l ≠ 0 := fun l => by linarith only [hρlo l]
  obtain ⟨bv, hbv⟩ : ∃ bv : Fin N → ℝ, bv = fun i => 1 / (N : ℝ) * ∑ l, K i l * ε l := ⟨_, rfl⟩
  obtain ⟨sv, hsv⟩ : ∃ sv : Fin N → ℝ, sv = fun i => 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨γ, hγd⟩ : ∃ γ : Fin N → ℝ,
      γ = fun i => 1 / ρ i * (1 / (1 / (N : ℝ) * ∑ l, K i l / ρ l)) := ⟨_, rfl⟩
  have hbi : ∀ i, 1 / (N : ℝ) * ∑ l, K i l * ε l = bv i := fun i => by rw [hbv]
  have hsi : ∀ i, 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2 = sv i := fun i => by rw [hsv]
  have hv : ∀ i, |γ i - (1 + (-2 * ε i + bv i)
        + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))| ≤ 44 * δ * (ε i ^ 2 + sv i)
      ∧ |bv i| ≤ 9 / 8 * δ ∧ bv i ^ 2 ≤ 9 / 8 * sv i ∧ 0 ≤ sv i ∧ sv i ≤ 9 / 8 * δ ^ 2 := by
    intro i
    have Gv := gamma_vertex hN K ρ ε hK0 hρ hε hδ hεδ i
    rw [hbi i, hsi i] at Gv
    obtain ⟨g1, g2, g3, g4, g5⟩ := Gv
    refine ⟨?_, g2, g3, g4, g5⟩
    rw [hγd]
    have e : 1 + (-2 * ε i + bv i) + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i)
        = 1 - 2 * ε i + bv i + 3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i := by ring
    rw [e]; exact g1
  simp_rw [hbi, hsi]
  -- the trace
  have htr : ((walkMatrix K ρ) ^ 2).trace
      = ∑ i, ∑ j, K i j / (N : ℝ) * (K j i / (N : ℝ)) * (γ i * γ j) := by
    have e := trace_pow_gamma K ρ hρ0 2
    rw [← hγd] at e
    have hA : ∀ i j, (Matrix.of (fun i j => K i j / (N : ℝ)) * Matrix.diagonal γ) i j
        = K i j / (N : ℝ) * γ j := fun i j => by rw [Matrix.mul_diagonal, Matrix.of_apply]
    rw [e, pow_two, Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, hA]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [htr, ← Finset.sum_sub_distrib]
  obtain ⟨qv, hqv⟩ : ∃ qv : Fin N → ℝ, qv = fun i => ε i ^ 2 + sv i := ⟨_, rfl⟩
  have hq0 : ∀ i, 0 ≤ qv i := fun i => by
    rw [hqv]; exact add_nonneg (_root_.sq_nonneg _) (hv i).2.2.2.1
  have hpair : ∀ i j, |γ i * γ j - (1 + ((-2 * ε i + bv i)
        + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))
        + ((-2 * ε j + bv j) + (3 * ε j ^ 2 - 3 * ε j * bv j + bv j ^ 2 - sv j))
        + (-2 * ε i + bv i) * (-2 * ε j + bv j))| ≤ 121 * δ * (qv i + qv j) := by
    have hx : ∀ i, qv i ≤ 17 / 8 * δ ^ 2 ∧ |-2 * ε i + bv i| ≤ 4 * δ
        ∧ |3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i| ≤ 5 * qv i := by
      intro i
      obtain ⟨_, g2, g3, g4, g5⟩ := hv i
      have he2 : ε i ^ 2 ≤ δ ^ 2 := sq_le_sq' (hl i).1 (hl i).2
      obtain ⟨b1, b2⟩ := abs_le.mp g2
      refine ⟨by rw [hqv]; linarith only [he2, g5], ?_, ?_⟩
      · rw [abs_le]; constructor <;> linarith only [(hl i).1, (hl i).2, b1, b2, hδ0]
      · rw [hqv, abs_le]
        constructor
        · nlinarith only [_root_.sq_nonneg (ε i - bv i), _root_.sq_nonneg (ε i + bv i), g3, g4,
            _root_.sq_nonneg (ε i), _root_.sq_nonneg (bv i)]
        · nlinarith only [_root_.sq_nonneg (ε i - bv i), _root_.sq_nonneg (ε i + bv i), g3, g4,
            _root_.sq_nonneg (ε i), _root_.sq_nonneg (bv i)]
    intro i j
    have hi := (hv i).1
    have hj := (hv j).1
    have ei : ε i ^ 2 + sv i = qv i := by rw [hqv]
    have ej : ε j ^ 2 + sv j = qv j := by rw [hqv]
    rw [ei] at hi
    rw [ej] at hj
    exact pair_gamma hδ0 hδ (hq0 i) (hq0 j) (hx i).1 (hx j).1 hi hj (hx i).2.1 (hx j).2.1
      (hx i).2.2 (hx j).2.2
  -- weights
  have hw : ∀ i j, 0 ≤ K i j / (N : ℝ) * (K j i / (N : ℝ))
      ∧ K i j / (N : ℝ) * (K j i / (N : ℝ)) ≤ M / N * (K i j / (N : ℝ)) := by
    intro i j
    have a0 : 0 ≤ K i j / (N : ℝ) := div_nonneg (hK0 i j) hNpos.le
    have a1 : 0 ≤ K j i / (N : ℝ) := div_nonneg (hK0 j i) hNpos.le
    have a2 : K j i / (N : ℝ) ≤ M / N := div_le_div_of_nonneg_right (hKM j i) hNpos.le
    refine ⟨mul_nonneg a0 a1, ?_⟩
    have := mul_le_mul_of_nonneg_left a2 a0
    linarith only [this]
  have hrow : ∀ i, ∑ j, K i j / (N : ℝ) = ρ i := fun i => by
    rw [← Finset.sum_div, hρ i]; field_simp
  have hcolq : ∑ i, sv i ≤ 9 / 8 * ∑ i, ε i ^ 2 := by
    rw [hsv, ← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i, K i l = N * ρ l := by
      rw [← hρ l]; exact Finset.sum_congr rfl fun i _ => hsym i l
    rw [this]
    have h1 := mul_le_mul_of_nonneg_right (hρhi l) (_root_.sq_nonneg (ε l))
    have e : 1 / (N : ℝ) * (N * ρ l * ε l ^ 2) = ρ l * ε l ^ 2 := by field_simp
    rw [e]; exact h1
  have hSq : ∑ i, qv i ≤ 17 / 8 * ∑ i, ε i ^ 2 := by
    rw [hqv, Finset.sum_add_distrib]; linarith only [hcolq]
  have hSe : 0 ≤ ∑ i, ε i ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
  -- sum of the pair bounds
  have hterm : ∀ i j, |K i j / (N : ℝ) * (K j i / (N : ℝ)) * (γ i * γ j)
        - K i j / (N : ℝ) * (K j i / (N : ℝ)) * (1 + ((-2 * ε i + bv i)
          + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))
          + ((-2 * ε j + bv j) + (3 * ε j ^ 2 - 3 * ε j * bv j + bv j ^ 2 - sv j))
          + (-2 * ε i + bv i) * (-2 * ε j + bv j))|
      ≤ 121 * δ * (M / N) * (K i j / (N : ℝ) * qv i + K i j / (N : ℝ) * qv j) := by
    intro i j
    rw [← mul_sub, abs_mul, abs_of_nonneg (hw i j).1]
    have h1 := mul_le_mul (hw i j).2 (hpair i j) (abs_nonneg _)
      (mul_nonneg (div_nonneg hM0 hNpos.le) (div_nonneg (hK0 i j) hNpos.le))
    refine h1.trans (le_of_eq (by ring))
  have hS1 : ∑ i, ∑ j, K i j / (N : ℝ) * qv i ≤ 9 / 8 * ∑ i, qv i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul, hrow i]
    exact mul_le_mul_of_nonneg_right (hρhi i) (hq0 i)
  have hS2 : ∑ i, ∑ j, K i j / (N : ℝ) * qv j ≤ 9 / 8 * ∑ i, qv i := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i, K i j / (N : ℝ) = ρ j := by
      rw [← hrow j]; exact Finset.sum_congr rfl fun i _ => by rw [hsym i j]
    rw [this]
    exact mul_le_mul_of_nonneg_right (hρhi j) (hq0 j)
  have hc0 : 0 ≤ 121 * δ * (M / N) :=
    mul_nonneg (mul_nonneg (by norm_num) hδ0) (div_nonneg hM0 hNpos.le)
  calc |∑ i, (∑ j, K i j / (N : ℝ) * (K j i / (N : ℝ)) * (γ i * γ j)
          - ∑ j, K i j / (N : ℝ) * (K j i / (N : ℝ)) * (1 + ((-2 * ε i + bv i)
            + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))
            + ((-2 * ε j + bv j) + (3 * ε j ^ 2 - 3 * ε j * bv j + bv j ^ 2 - sv j))
            + (-2 * ε i + bv i) * (-2 * ε j + bv j)))|
      ≤ ∑ i, ∑ j, 121 * δ * (M / N)
          * (K i j / (N : ℝ) * qv i + K i j / (N : ℝ) * qv j) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm i j)
    _ = 121 * δ * (M / N) * (∑ i, ∑ j, K i j / (N : ℝ) * qv i
          + ∑ i, ∑ j, K i j / (N : ℝ) * qv j) := by
        simp only [← Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 121 * δ * (M / N) * (9 / 8 * (17 / 8 * ∑ i, ε i ^ 2)
          + 9 / 8 * (17 / 8 * ∑ i, ε i ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        linarith only [hS1, hS2, hSq]
    _ ≤ 580 * δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2) := by
        have e : 121 * δ * (M / N) * (9 / 8 * (17 / 8 * ∑ i, ε i ^ 2)
            + 9 / 8 * (17 / 8 * ∑ i, ε i ^ 2))
            = 121 * 2 * (9 / 8) * (17 / 8) * (δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2)) := by
          field_simp; ring
        have hnn : 0 ≤ δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2) :=
          mul_nonneg (mul_nonneg hδ0 hM0) (mul_nonneg hinv.le hSe)
        rw [e]; linarith only [hnn]

/-! ### `β₁ ≤ 0`; the graph without self-loops for `k = 1` -/

theorem torusM_hasSum {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    HasSum (fun n : Fin d → ℤ =>
      Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ^ k) (torusM d σ k) := by
  have hk' : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hc : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := by have := Real.pi_pos; positivity
  have hs := (gauss_summable hc d).hasSum
  have h0 : heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0
      = ∑' n : Fin d → ℤ, Real.exp (-(2 * Real.pi ^ 2 * ((k : ℝ) * σ))
          * ∑ i, ((n i : ℤ) : ℝ) ^ 2) := cosSeries_zero d _
  unfold torusM
  rw [h0]
  have e : (fun n : Fin d → ℤ =>
        Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ^ k)
      = fun n : Fin d → ℤ => Real.exp (-(2 * Real.pi ^ 2 * ((k : ℝ) * σ))
          * ∑ i, ((n i : ℤ) : ℝ) ^ 2) := by
    funext n; rw [← Real.exp_nat_mul]; congr 1; ring
  rw [e]; exact hs

/-- **`β₁ ≤ 0` on the flat torus**: `m₄ - 3m₃ + 3m₂ - m₁ = -∑_n a_n (1 - a_n)³ ≤ 0` with
    `a_n = e^{-2π²σ|n|²} ∈ (0, 1]` (`rem:bias`(i): `β₁ = -m₁ Tr[𝒫(1-𝒫)³]`). -/
theorem beta_one_nonpos {σ : ℝ} (hσ : 0 < σ) (d : ℕ) :
    HasSum (fun n : Fin d → ℤ =>
        -(Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
          * (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) ^ 3))
      (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1)
    ∧ torusM d σ 1 * (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1) ≤ 0 := by
  have h1 := torusM_hasSum hσ d (k := 1) le_rfl
  have h2 := torusM_hasSum hσ d (k := 2) (by norm_num)
  have h3 := torusM_hasSum hσ d (k := 3) (by norm_num)
  have h4 := torusM_hasSum hσ d (k := 4) (by norm_num)
  have hs := (((h4.sub (h3.mul_left 3)).add (h2.mul_left 3)).sub h1)
  have e : (fun n : Fin d → ℤ =>
        -(Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
          * (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) ^ 3))
      = fun n : Fin d → ℤ =>
        Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ^ 4
          - 3 * Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ^ 3
          + 3 * Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ^ 2
          - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ^ 1 := by
    funext n; ring
  have hS : HasSum (fun n : Fin d → ℤ =>
        -(Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
          * (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)) ^ 3))
      (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1) := by
    rw [e]; exact hs
  refine ⟨hS, ?_⟩
  have hle : torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2 - torusM d σ 1 ≤ 0 := by
    refine hasSum_le (fun n => ?_) hS hasSum_zero
    have hpos := Real.exp_pos (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    have hle1 : Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ i, ((n i : ℤ) : ℝ) ^ 2) ≤ 1 := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have h0 : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
      have hc : 0 ≤ 2 * Real.pi ^ 2 * σ := by positivity
      nlinarith only [mul_nonneg hc h0]
    exact neg_nonpos.mpr (mul_nonneg hpos.le (pow_nonneg (sub_nonneg.mpr hle1) 3))
  exact mul_nonpos_of_nonneg_of_nonpos (zero_le_one.trans (torusM_one_ge hσ d)) hle

/-- **`k = 1` without self-loops**: `Tr P° = 0` for every configuration (so `μ₁ = 0`, `β₁ = 0`
    in `prop:bias` with `ρ = 0`); restatement of `NoLoopsTrace.noloopWalk_trace`. -/
theorem bias_one_noloops (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) :
    (NoLoops.noloopWalk d σ N x).trace = 0 :=
  NoLoopsTrace.noloopWalk_trace d σ N x

end BiasVariance2


namespace JumpProfile

open Filter Topology
open CTG.Reals.TraceG29 FixedScale

/-! ### Bracketing and the Glivenko–Cantelli theorem with brackets -/

/-- A family `f t`, `t ∈ T`, of functions with values in `[0, M]` has FINITE BRACKETING NUMBERS
    with respect to `ν`: for every `ε > 0` there is a finite set of pairs `(lo, up)` of measurable
    functions, `0 ≤ lo ≤ up ≤ M`, `∫ (up - lo) dν ≤ ε`, such that every `f t` lies between the two
    functions of one pair. -/
def IsBrk {E T : Type*} [MeasurableSpace E] (ν : Measure E) (f : T → E → ℝ) (M : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ S : Set ((E → ℝ) × (E → ℝ)), S.Finite ∧
    (∀ b ∈ S, Measurable b.1 ∧ Measurable b.2 ∧ (∀ z, 0 ≤ b.1 z ∧ b.1 z ≤ b.2 z ∧ b.2 z ≤ M) ∧
      ∫ z, (b.2 z - b.1 z) ∂ν ≤ ε) ∧
    ∀ t, ∃ b ∈ S, ∀ z, b.1 z ≤ f t z ∧ f t z ≤ b.2 z

theorem integrable_of_bdd {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsFiniteMeasure ν]
    {g : E → ℝ} (hg : Measurable g) {M : ℝ} (h0 : ∀ z, 0 ≤ g z) (hM : ∀ z, g z ≤ M) :
    Integrable g ν :=
  Integrable.of_bound hg.aestronglyMeasurable M
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 z)]; exact hM z)

/-- The strong law of large numbers for a function of independent points with law `ν`. -/
theorem slln_fn {Ω E : Type*} [MeasurableSpace E] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ν : Measure E) (X : ℕ → Ω → E) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (g : E → ℝ) (hg : Measurable g)
    (hint : Integrable g ν) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, g (X j ω)) / N) atTop
      (𝓝 (∫ z, g z ∂ν)) := by
  have hint0 : Integrable (fun ω => g (X 0 ω)) μ := by
    have h : Integrable g (μ.map (X 0)) := by rw [hlaw 0]; exact hint
    exact (integrable_map_measure hg.aestronglyMeasurable (hX 0).aemeasurable).1 h
  have hind : Pairwise (Function.onFun (fun a b => IndepFun a b μ) (fun j ω => g (X j ω))) := by
    intro i j hij
    exact (h_indep.indepFun hij).comp hg hg
  have hid : ∀ i, IdentDistrib (fun ω => g (X i ω)) (fun ω => g (X 0 ω)) μ μ := by
    intro i
    have h0 : IdentDistrib (X i) (X 0) μ μ :=
      ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩
    exact h0.comp hg
  have h := ProbabilityTheory.strong_law_ae (fun j ω => g (X j ω)) hint0 hind hid
  have e : ∫ ω, g (X 0 ω) ∂μ = ∫ z, g z ∂ν := by
    rw [← hlaw 0]
    exact (integral_map (hX 0).aemeasurable hg.aestronglyMeasurable).symm
  rw [e] at h
  filter_upwards [h] with ω hω
  refine hω.congr (fun N => ?_)
  rw [smul_eq_mul, inv_mul_eq_div]

theorem brk_arith {N s sl su I Il Iu e ε : ℝ} (hN : 0 < N) (h1 : sl ≤ s) (h2 : s ≤ su)
    (h3 : |sl / N - Il| < ε / 2) (h4 : |su / N - Iu| < ε / 2) (h5 : Il ≤ I) (h6 : I ≤ Iu)
    (h7 : Iu - Il ≤ e) (h8 : e < ε / 2) : |s - N * I| ≤ ε * N := by
  rw [abs_lt] at h3 h4
  have hsl : sl / N * N = sl := by field_simp
  have hsu : su / N * N = su := by field_simp
  have ha : (I - ε) * N ≤ sl / N * N := mul_le_mul_of_nonneg_right (by linarith) hN.le
  have hb : su / N * N ≤ (I + ε) * N := mul_le_mul_of_nonneg_right (by linarith) hN.le
  rw [hsl] at ha
  rw [hsu] at hb
  rw [abs_le]
  constructor <;> nlinarith

/-- **Glivenko–Cantelli theorem with brackets.** Independent points `X_j` with law `ν`; a family
    of measurable functions `f t` with finite bracketing numbers. Then almost surely, for every
    `ε > 0` and all large `N`: `|∑_{j<N} f t (X_j) - N ∫ f t dν| ≤ ε N` for ALL `t`
    simultaneously. (Proof: the strong law for the countably many bracket functions.) -/
theorem brk_gc {Ω E T : Type*} [MeasurableSpace E] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (ν : Measure E) [IsProbabilityMeasure ν] (X : ℕ → Ω → E)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν)
    (f : T → E → ℝ) {M : ℝ} (hf : ∀ t, Measurable (f t)) (hbrk : IsBrk ν f M) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ t,
      |∑ j ∈ Finset.range N, f t (X j ω) - N * ∫ z, f t z ∂ν| ≤ ε * N := by
  choose S hSfin hSprop hScov using
    fun n : ℕ => hbrk (1 / ((n : ℝ) + 1)) (by positivity)
  have hae : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ b ∈ S n,
      Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, b.1 (X j ω)) / N) atTop
        (𝓝 (∫ z, b.1 z ∂ν))
      ∧ Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, b.2 (X j ω)) / N) atTop
        (𝓝 (∫ z, b.2 z ∂ν)) := by
    rw [ae_all_iff]; intro n
    rw [ae_ball_iff (hSfin n).countable]
    intro b hb
    obtain ⟨hm1, hm2, hbd, -⟩ := hSprop n b hb
    have i1 := integrable_of_bdd ν hm1 (fun z => (hbd z).1)
      (fun z => (hbd z).2.1.trans (hbd z).2.2)
    have i2 := integrable_of_bdd ν hm2 (fun z => (hbd z).1.trans (hbd z).2.1)
      (fun z => (hbd z).2.2)
    filter_upwards [slln_fn ν X h_indep hX hlaw b.1 hm1 i1,
      slln_fn ν X h_indep hX hlaw b.2 hm2 i2] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hae] with ω hω ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
  have hev : ∀ᶠ N : ℕ in atTop, ∀ b ∈ S n,
      |(∑ j ∈ Finset.range N, b.1 (X j ω)) / N - ∫ z, b.1 z ∂ν| < ε / 2
      ∧ |(∑ j ∈ Finset.range N, b.2 (X j ω)) / N - ∫ z, b.2 z ∂ν| < ε / 2 := by
    rw [eventually_all_finite (hSfin n)]
    intro b hb
    obtain ⟨h1, h2⟩ := hω n b hb
    have e1 := (Metric.tendsto_nhds.1 h1) (ε / 2) (half_pos hε)
    have e2 := (Metric.tendsto_nhds.1 h2) (ε / 2) (half_pos hε)
    filter_upwards [e1, e2] with N a1 a2
    rw [Real.dist_eq] at a1 a2
    exact ⟨a1, a2⟩
  filter_upwards [hev, eventually_gt_atTop 0] with N hN hNpos t
  obtain ⟨b, hb, hbt⟩ := hScov n t
  obtain ⟨hm1, hm2, hbd, hint⟩ := hSprop n b hb
  have i1 := integrable_of_bdd ν hm1 (fun z => (hbd z).1)
    (fun z => (hbd z).2.1.trans (hbd z).2.2)
  have i2 := integrable_of_bdd ν hm2 (fun z => (hbd z).1.trans (hbd z).2.1)
    (fun z => (hbd z).2.2)
  have it : Integrable (f t) ν := integrable_of_bdd ν (hf t)
    (fun z => (hbd z).1.trans (hbt z).1) (fun z => (hbt z).2.trans (hbd z).2.2)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  refine brk_arith hNr (Finset.sum_le_sum fun j _ => (hbt _).1)
    (Finset.sum_le_sum fun j _ => (hbt _).2) (hN b hb).1 (hN b hb).2
    (integral_mono i1 it fun z => (hbt z).1) (integral_mono it i2 fun z => (hbt z).2) ?_ hn
  rw [← integral_sub i2 i1]
  exact hint

theorem prod_brk_arith {b1 b2 c1 c2 M1 M2 : ℝ} (hb : b1 ≤ b2) (hb2 : b2 ≤ M1)
    (hc : c1 ≤ c2) (hc2 : c2 ≤ M2) :
    b2 * c2 - b1 * c1 ≤ M1 * (c2 - c1) + M2 * (b2 - b1) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hb2) (sub_nonneg.2 hc),
    mul_nonneg (sub_nonneg.2 (hc.trans hc2)) (sub_nonneg.2 hb)]

theorem prod_eps {M1 M2 ε : ℝ} (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hε : 0 ≤ ε) :
    M1 * (ε / (2 * (M1 + 1))) + M2 * (ε / (2 * (M2 + 1))) ≤ ε := by
  have h : ∀ M : ℝ, 0 ≤ M → M * (ε / (2 * (M + 1))) ≤ ε / 2 := by
    intro M hM
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hε hM]
  linarith [h M1 hM1, h M2 hM2]

/-- Products of two bracketed families are bracketed. -/
theorem IsBrk.mul {E T T' : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    {f : T → E → ℝ} {g : T' → E → ℝ} {M1 M2 : ℝ} (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hf : IsBrk ν f M1) (hg : IsBrk ν g M2) :
    IsBrk ν (fun t : T × T' => fun z => f t.1 z * g t.2 z) (M1 * M2) := by
  intro ε hε
  obtain ⟨S1, hS1, hp1, hc1⟩ := hf (ε / (2 * (M2 + 1))) (by positivity)
  obtain ⟨S2, hS2, hp2, hc2⟩ := hg (ε / (2 * (M1 + 1))) (by positivity)
  refine ⟨Set.image2 (fun b c : (E → ℝ) × (E → ℝ) =>
    ((fun z => b.1 z * c.1 z), (fun z => b.2 z * c.2 z))) S1 S2, hS1.image2 _ hS2, ?_, ?_⟩
  · rintro _ ⟨b, hb, c, hc, rfl⟩
    obtain ⟨bm1, bm2, bbd, bint⟩ := hp1 b hb
    obtain ⟨cm1, cm2, cbd, cint⟩ := hp2 c hc
    have ib1 := integrable_of_bdd ν bm1 (fun z => (bbd z).1)
      (fun z => (bbd z).2.1.trans (bbd z).2.2)
    have ib2 := integrable_of_bdd ν bm2 (fun z => (bbd z).1.trans (bbd z).2.1)
      (fun z => (bbd z).2.2)
    have ic1 := integrable_of_bdd ν cm1 (fun z => (cbd z).1)
      (fun z => (cbd z).2.1.trans (cbd z).2.2)
    have ic2 := integrable_of_bdd ν cm2 (fun z => (cbd z).1.trans (cbd z).2.1)
      (fun z => (cbd z).2.2)
    have hlo0 : ∀ z, 0 ≤ b.1 z * c.1 z := fun z => mul_nonneg (bbd z).1 (cbd z).1
    have hlu : ∀ z, b.1 z * c.1 z ≤ b.2 z * c.2 z := fun z =>
      mul_le_mul (bbd z).2.1 (cbd z).2.1 (cbd z).1 ((bbd z).1.trans (bbd z).2.1)
    have hup : ∀ z, b.2 z * c.2 z ≤ M1 * M2 := fun z =>
      mul_le_mul (bbd z).2.2 (cbd z).2.2 ((cbd z).1.trans (cbd z).2.1) hM1
    have il := integrable_of_bdd ν (bm1.mul cm1) hlo0 (fun z => (hlu z).trans (hup z))
    have iu := integrable_of_bdd ν (bm2.mul cm2) (fun z => (hlo0 z).trans (hlu z)) hup
    refine ⟨bm1.mul cm1, bm2.mul cm2, fun z => ⟨hlo0 z, hlu z, hup z⟩, ?_⟩
    have idc : Integrable (fun z => c.2 z - c.1 z) ν := ic2.sub ic1
    have idb : Integrable (fun z => b.2 z - b.1 z) ν := ib2.sub ib1
    have ilhs : Integrable (fun z => b.2 z * c.2 z - b.1 z * c.1 z) ν := iu.sub il
    have irhs : Integrable (fun z => M1 * (c.2 z - c.1 z) + M2 * (b.2 z - b.1 z)) ν :=
      (idc.const_mul M1).add (idb.const_mul M2)
    calc ∫ z, (b.2 z * c.2 z - b.1 z * c.1 z) ∂ν
        ≤ ∫ z, (M1 * (c.2 z - c.1 z) + M2 * (b.2 z - b.1 z)) ∂ν :=
          integral_mono ilhs irhs (fun z => prod_brk_arith (bbd z).2.1 (bbd z).2.2
            (cbd z).2.1 (cbd z).2.2)
      _ = M1 * ∫ z, (c.2 z - c.1 z) ∂ν + M2 * ∫ z, (b.2 z - b.1 z) ∂ν := by
          rw [integral_add (idc.const_mul M1) (idb.const_mul M2), integral_const_mul,
            integral_const_mul]
      _ ≤ M1 * (ε / (2 * (M1 + 1))) + M2 * (ε / (2 * (M2 + 1))) :=
          add_le_add (mul_le_mul_of_nonneg_left cint hM1) (mul_le_mul_of_nonneg_left bint hM2)
      _ ≤ ε := prod_eps hM1 hM2 hε.le
  · rintro ⟨t, s⟩
    obtain ⟨b, hb, hbt⟩ := hc1 t
    obtain ⟨c, hc, hcs⟩ := hc2 s
    obtain ⟨-, -, bbd, -⟩ := hp1 b hb
    obtain ⟨-, -, cbd, -⟩ := hp2 c hc
    refine ⟨_, ⟨b, hb, c, hc, rfl⟩, fun z => ⟨?_, ?_⟩⟩
    · exact mul_le_mul (hbt z).1 (hcs z).1 (cbd z).1 ((bbd z).1.trans (hbt z).1)
    · exact mul_le_mul (hbt z).2 (hcs z).2 ((cbd z).1.trans (hcs z).1)
        ((bbd z).1.trans (bbd z).2.1)

/-! ### Convolution preserves bracketing -/

section Group

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableSub₂ G]
  [MeasurableNeg G] (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant]
  [ν.IsNegInvariant]

/-- If the translates `z ↦ q(z - y)` are bracketed, so are the translates of `p * q`, for a
    probability density `0 ≤ p ≤ M` (Fubini: the brackets are convolved with `p`). -/
theorem IsBrk.conv (p : G → ℝ) (hp : Measurable p) {M : ℝ} (hp0 : ∀ u, 0 ≤ p u)
    (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1) {q : G → ℝ} (hqm : Measurable q) {B : ℝ}
    (hq : IsBrk ν (fun y z => q (z - y)) B) :
    IsBrk ν (fun y z => ∫ w, p (z - y - w) * q w ∂ν) B := by
  have hM0 : 0 ≤ M := (hp0 0).trans (hpM 0)
  have hpz : ∀ z, Measurable (fun w => p (z - w)) := fun z =>
    hp.comp (measurable_const.sub measurable_id)
  have hone : ∀ z, ∫ w, p (z - w) ∂ν = 1 := fun z => by
    rw [integral_sub_left_eq_self p ν z]; exact hmass
  have ipz : ∀ z, Integrable (fun w => p (z - w)) ν := fun z =>
    integrable_of_bdd ν (hpz z) (fun w => hp0 _) (fun w => hpM _)
  intro ε hε
  obtain ⟨S, hS, hprop, hcov⟩ := hq ε hε
  have hI : ∀ b ∈ S, ∀ z, Integrable (fun w => p (z - w) * b.1 w) ν
      ∧ Integrable (fun w => p (z - w) * b.2 w) ν := by
    intro b hb z
    obtain ⟨m1, m2, bd, -⟩ := hprop b hb
    have hB0 : 0 ≤ B := ((bd 0).1.trans (bd 0).2.1).trans (bd 0).2.2
    exact ⟨integrable_of_bdd ν ((hpz z).mul m1) (fun w => mul_nonneg (hp0 _) (bd w).1)
        (fun w => mul_le_mul (hpM _) ((bd w).2.1.trans (bd w).2.2) (bd w).1 hM0),
      integrable_of_bdd ν ((hpz z).mul m2)
        (fun w => mul_nonneg (hp0 _) ((bd w).1.trans (bd w).2.1))
        (fun w => mul_le_mul (hpM _) (bd w).2.2 ((bd w).1.trans (bd w).2.1) hM0)⟩
  refine ⟨(fun b : (G → ℝ) × (G → ℝ) => ((fun z => ∫ w, p (z - w) * b.1 w ∂ν),
    (fun z => ∫ w, p (z - w) * b.2 w ∂ν))) '' S, hS.image _, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨m1, m2, bd, hint⟩ := hprop b hb
    have hB0 : 0 ≤ B := ((bd 0).1.trans (bd 0).2.1).trans (bd 0).2.2
    have mL : Measurable (fun z => ∫ w, p (z - w) * b.1 w ∂ν) := by
      have hF : Measurable (fun x : G × G => p (x.1 - x.2) * b.1 x.2) :=
        (hp.comp (measurable_fst.sub measurable_snd)).mul (m1.comp measurable_snd)
      exact (hF.stronglyMeasurable.integral_prod_right').measurable
    have mU : Measurable (fun z => ∫ w, p (z - w) * b.2 w ∂ν) := by
      have hF : Measurable (fun x : G × G => p (x.1 - x.2) * b.2 x.2) :=
        (hp.comp (measurable_fst.sub measurable_snd)).mul (m2.comp measurable_snd)
      exact (hF.stronglyMeasurable.integral_prod_right').measurable
    refine ⟨mL, mU, fun z => ⟨integral_nonneg (fun w => mul_nonneg (hp0 _) (bd w).1),
      integral_mono (hI b hb z).1 (hI b hb z).2
        (fun w => mul_le_mul_of_nonneg_left (bd w).2.1 (hp0 _)), ?_⟩, ?_⟩
    · calc ∫ w, p (z - w) * b.2 w ∂ν ≤ ∫ w, p (z - w) * B ∂ν :=
            integral_mono (hI b hb z).2 ((ipz z).mul_const B)
              (fun w => mul_le_mul_of_nonneg_left (bd w).2.2 (hp0 _))
        _ = B := by rw [integral_mul_const, hone z, one_mul]
    · have e1 : ∀ z, (∫ w, p (z - w) * b.2 w ∂ν) - ∫ w, p (z - w) * b.1 w ∂ν
          = ∫ w, p (z - w) * (b.2 w - b.1 w) ∂ν := fun z => by
        rw [← integral_sub (hI b hb z).2 (hI b hb z).1]
        congr 1; funext w; ring
      show ∫ z, ((∫ w, p (z - w) * b.2 w ∂ν) - ∫ w, p (z - w) * b.1 w ∂ν) ∂ν ≤ ε
      simp only [e1]
      have hmeas : Measurable (fun x : G × G => p (x.1 - x.2) * (b.2 x.2 - b.1 x.2)) :=
        (hp.comp (measurable_fst.sub measurable_snd)).mul ((m2.sub m1).comp measurable_snd)
      have hInt : Integrable (Function.uncurry fun z w : G => p (z - w) * (b.2 w - b.1 w))
          (ν.prod ν) := by
        refine Integrable.of_bound hmeas.aestronglyMeasurable (M * B)
          (Eventually.of_forall fun x => ?_)
        have h1 : 0 ≤ b.2 x.2 - b.1 x.2 := sub_nonneg.2 (bd x.2).2.1
        have h2 : b.2 x.2 - b.1 x.2 ≤ B := by linarith [(bd x.2).1, (bd x.2).2.2]
        show ‖p (x.1 - x.2) * (b.2 x.2 - b.1 x.2)‖ ≤ M * B
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 _) h1)]
        exact mul_le_mul (hpM _) h2 h1 hM0
      rw [integral_integral_swap hInt]
      have e2 : ∀ w, ∫ z, p (z - w) * (b.2 w - b.1 w) ∂ν = b.2 w - b.1 w := fun w => by
        rw [integral_mul_const, integral_sub_right_eq_self p w, hmass, one_mul]
      simp only [e2]
      exact hint
  · intro y
    obtain ⟨b, hb, hby⟩ := hcov y
    obtain ⟨m1, m2, bd, -⟩ := hprop b hb
    have hB0 : 0 ≤ B := ((bd 0).1.trans (bd 0).2.1).trans (bd 0).2.2
    refine ⟨_, ⟨b, hb, rfl⟩, fun z => ?_⟩
    have e : ∫ w, p (z - y - w) * q w ∂ν = ∫ w, p (z - w) * q (w - y) ∂ν := by
      rw [← integral_sub_right_eq_self (fun w => p (z - y - w) * q w) y]
      congr 1; funext w
      have : z - y - (w - y) = z - w := by abel
      rw [this]
    have Iq : Integrable (fun w => p (z - w) * q (w - y)) ν :=
      integrable_of_bdd ν ((hpz z).mul (hqm.comp (measurable_id.sub measurable_const)))
        (fun w => mul_nonneg (hp0 _) ((bd w).1.trans (hby w).1))
        (fun w => mul_le_mul (hpM _) ((hby w).2.trans (bd w).2.2) ((bd w).1.trans (hby w).1) hM0)
    show (∫ w, p (z - w) * b.1 w ∂ν) ≤ ∫ w, p (z - y - w) * q w ∂ν
      ∧ (∫ w, p (z - y - w) * q w ∂ν) ≤ ∫ w, p (z - w) * b.2 w ∂ν
    rw [e]
    exact ⟨integral_mono (hI b hb z).1 Iq (fun w => mul_le_mul_of_nonneg_left (hby w).1 (hp0 _)),
      integral_mono Iq (hI b hb z).2 (fun w => mul_le_mul_of_nonneg_left (hby w).2 (hp0 _))⟩

/-- All convolution powers of an even probability density with bracketed translates have
    bracketed translates. -/
theorem brk_convPow (p : G → ℝ) (hp : Measurable p) {M : ℝ} (hp0 : ∀ u, 0 ≤ p u)
    (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1) (heven : ∀ u, p (-u) = p u)
    (hbrk : IsBrk ν (fun x z => p (x - z)) M) :
    ∀ m, IsBrk ν (fun y z => convPow ν p m (z - y)) M
  | 0 => by
    have e : (fun y z : G => convPow ν p 0 (z - y)) = fun x z => p (x - z) := by
      funext y z
      show p (z - y) = p (y - z)
      rw [← heven, neg_sub]
    rw [e]; exact hbrk
  | m + 1 => IsBrk.conv ν p hp hp0 hpM hmass (convPow_measurable ν p hp m)
      (brk_convPow p hp hp0 hpM hmass heven hbrk m)

/-- The semigroup property: `∫ p(x - z) p^{*(m+1)}(z - y) dν(z) = p^{*(m+2)}(x - y)`. -/
theorem conv_mean (p : G → ℝ) (m : ℕ) (x y : G) :
    ∫ z, p (x - z) * convPow ν p m (z - y) ∂ν = convPow ν p (m + 1) (x - y) := by
  have h2 := integral_add_right_eq_self (μ := ν) (fun z => p (x - z) * convPow ν p m (z - y)) y
  rw [← h2]
  show ∫ w, p (x - (w + y)) * convPow ν p m (w + y - y) ∂ν
    = ∫ w, p (x - y - w) * convPow ν p m w ∂ν
  congr 1
  funext w
  rw [add_sub_cancel_right, sub_add_eq_sub_sub, sub_right_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **The uniform laws of large numbers for a kernel with bracketed translates** (Step 1 of
    Theorem "fixedxi" without continuity). Almost surely, for every `ε > 0`:
    the normalisation, `sup_x |∑_{j<N} p(x - X_j) - N| ≤ ε N` for all large `N`, and for every
    `m` the consistency of the walk with the exact normalisation,
    `sup_{x,y} |∑_{j<N} p(x - X_j) p^{*(m+1)}(X_j - y) - N p^{*(m+2)}(x - y)| ≤ ε N`
    for all large `N`. -/
theorem jump_events_ae (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (p : G → ℝ) (hp : Measurable p) {M : ℝ}
    (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (heven : ∀ u, p (-u) = p u) (hbrk : IsBrk ν (fun x z => p (x - z)) M) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε →
      (∀ᶠ N : ℕ in atTop, ∀ x : G, |∑ j ∈ Finset.range N, p (x - X j ω) - N| ≤ ε * N)
      ∧ ∀ m : ℕ, ∀ᶠ N : ℕ in atTop, ∀ t : G × G,
          |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
            - N * convPow ν p (m + 1) (t.1 - t.2)| ≤ ε * N := by
  have hM0 : 0 ≤ M := (hp0 0).trans (hpM 0)
  have hpx : ∀ x, Measurable (fun z => p (x - z)) := fun x =>
    hp.comp (measurable_const.sub measurable_id)
  have h1 := brk_gc (μ := μ) ν X h_indep hX hlaw (fun x z => p (x - z)) hpx hbrk
  have h2 : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ t : G × G,
      |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
        - N * ∫ z, p (t.1 - z) * convPow ν p m (z - t.2) ∂ν| ≤ ε * N := by
    rw [ae_all_iff]; intro m
    exact brk_gc (μ := μ) ν X h_indep hX hlaw
      (fun t : G × G => fun z => p (t.1 - z) * convPow ν p m (z - t.2))
      (fun t => (hpx t.1).mul
        ((convPow_measurable ν p hp m).comp (measurable_id.sub measurable_const)))
      (IsBrk.mul ν hM0 hM0 hbrk (brk_convPow ν p hp hp0 hpM hmass heven hbrk m))
  filter_upwards [h1, h2] with ω a1 a2 ε hε
  refine ⟨?_, fun m => ?_⟩
  · filter_upwards [a1 ε hε] with N hN x
    have h := hN x
    rw [integral_sub_left_eq_self p ν x, hmass, mul_one] at h
    exact h
  · filter_upwards [a2 m ε hε] with N hN t
    have h := hN t
    rw [conv_mean] at h
    exact h

end Group

/-! ### The sampled walk of a kernel with bracketed translates -/

/-- The deterministic step of `kernel_fixed_scale_whp` at one configuration `x_0, x_1, …`. -/
theorem jump_point_det {G : Type*} [AddCommGroup G] [MeasurableSpace G] (ν : Measure G)
    (x : ℕ → G) (p : G → ℝ) (Bf : ℕ → ℝ) (N : ℕ) [NeZero N] (k : ℕ)
    (hq0 : ∀ m u, 0 ≤ convPow ν p m u) (hqB : ∀ m u, convPow ν p m u ≤ Bf m)
    (P : Matrix (Fin N) (Fin N) ℝ)
    (hP : ∀ b j : Fin N, P b j
      = (p (x b - x j) / ((∑ l : Fin N, p (x j - x l)) / N))
        / ∑ l : Fin N, p (x b - x l) / ((∑ l' : Fin N, p (x l - x l')) / N))
    {epsn epsc : ℝ} (hepsn0 : 0 ≤ epsn) (hepsn : epsn ≤ N / 8)
    (hn' : ∀ y : G, |∑ j ∈ Finset.range N, p (y - x j) - N| ≤ epsn)
    (hc' : ∀ m, m < k → ∀ t : G × G,
        |∑ j ∈ Finset.range N, p (t.1 - x j) * convPow ν p m (x j - t.2)
          - N * convPow ν p (m + 1) (t.1 - t.2)| ≤ epsc)
    (a i : Fin N) :
    |(N : ℝ) * (P ^ (k + 1)) a i - convPow ν p k (x a - x i)|
      ≤ 10 * (epsn / N) * (convPow ν p k (x a - x i)
            + ∑ m ∈ Finset.range k, (3 * (epsc / N) + 11 * (epsn / N) * Bf (m + 1)))
          + ∑ m ∈ Finset.range k, (3 * (epsc / N) + 11 * (epsn / N) * Bf (m + 1)) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have key := kernel_fixed_scale_det (n := Fin N)
    (fun m b i' => convPow ν p (m - 1) (x b - x i')) (fun m => Bf (m - 1))
    (fun _ => epsc / N) (fun b => (∑ l : Fin N, p (x b - x l)) / N) P
    (delta := epsn / N) (div_nonneg hepsn0 hNpos.le)
    (by rw [div_le_iff₀ hNpos]; linarith)
    (fun m b i' => hq0 _ _) (fun m b i' => hqB _ _)
    (fun b => by
      simp only [Fintype.card_fin]
      have : (fun l : Fin N => convPow ν p (1 - 1) (x b - x l))
          = fun l : Fin N => p (x b - x l) := rfl
      rw [this]; field_simp)
    (fun b => by
      have h := hn' (x b)
      rw [← Fin.sum_univ_eq_sum_range (fun j => p (x b - x j)) N] at h
      have e : (∑ l : Fin N, p (x b - x l)) / N - 1
          = (∑ l : Fin N, p (x b - x l) - N) / N := by field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le)
    (fun b j => hP b j) k
    (fun m b i' hm1 hmk => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h := hc' m' (by omega) (x b, x i')
      simp only at h
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => p (x b - x j) * convPow ν p m' (x j - x i')) N] at h
      simp only [Fintype.card_fin, Nat.add_sub_cancel]
      have e : ∑ j : Fin N, convPow ν p (1 - 1) (x b - x j) / (N : ℝ)
            * convPow ν p m' (x j - x i') - convPow ν p (m' + 1) (x b - x i')
          = (∑ j : Fin N, p (x b - x j) * convPow ν p m' (x j - x i')
              - N * convPow ν p (m' + 1) (x b - x i')) / N := by
        have : ∀ j : Fin N, convPow ν p (1 - 1) (x b - x j) = p (x b - x j) :=
          fun j => rfl
        simp_rw [this]
        rw [sub_div, Finset.sum_div]
        congr 1
        · exact Finset.sum_congr rfl (fun j _ => by ring)
        · field_simp
      rw [e, abs_div, abs_of_pos hNpos]
      exact div_le_div_of_nonneg_right h hNpos.le) a i
  simp only [Fintype.card_fin, Nat.add_sub_cancel] at key
  exact key

theorem jump_tol {ε η M q k : ℝ} (hε0 : 0 ≤ ε) (hε8 : ε ≤ 1 / 8) (hM : 0 ≤ M)
    (hq : q ≤ M) (hk : 0 ≤ k) (hεη : ε * (10 * M + 3 * k * (3 + 11 * M) + 1) ≤ η) :
    10 * ε * (q + k * (3 * ε + 11 * ε * M)) + k * (3 * ε + 11 * ε * M) ≤ η := by
  have hA : 0 ≤ k * ε * (3 + 11 * M) := by positivity
  have h1 : ε * q ≤ ε * M := mul_le_mul_of_nonneg_left hq hε0
  have h2 : ε * (k * ε * (3 + 11 * M)) ≤ 1 / 8 * (k * ε * (3 + 11 * M)) :=
    mul_le_mul_of_nonneg_right hε8 hA
  nlinarith

section Walk

variable {Ω G : Type*} [AddCommGroup G]

/-- Kernel matrix `K_ij = p(X_i - X_j)` of the first `N` sample points (diagonal included). -/
noncomputable def jpK (p : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) : Fin N → Fin N → ℝ :=
  fun i j => p (X i ω - X j ω)

/-- The estimated normalisation `ρ_i = (1/N) ∑_l K_il`. -/
noncomputable def jpRho (p : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) : Fin N → ℝ :=
  fun i => (∑ l : Fin N, p (X i ω - X l ω)) / N

/-- The walk matrix `P_N = D^{-1} W`, `W_ij = K_ij/(ρ_i ρ_j)`. -/
noncomputable def jpWalk (p : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℝ :=
  walkMatrix (jpK p X N ω) (jpRho p X N ω)

/-- The symmetric normalised matrix `S_N = D^{-1/2} W D^{-1/2}`. -/
noncomputable def jpSym (p : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Matrix (Fin N) (Fin N) ℝ :=
  symGraph (jpK p X N ω) (jpRho p X N ω)

/-- The subtracted heat trace `Tr exp(τ(S_N - 1)) - N e^{-τ}`. -/
noncomputable def jpSub (p : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  (NormedSpace.exp (τ • (jpSym p X N ω - 1))).trace - (N : ℝ) * Real.exp (-τ)

theorem jpK_symm {p : G → ℝ} (heven : ∀ u, p (-u) = p u) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω)
    (i j : Fin N) : jpK p X N ω i j = jpK p X N ω j i := by
  unfold jpK
  rw [← heven, neg_sub]

theorem jpRho_pos {p : G → ℝ} (hp0 : ∀ u, 0 ≤ p u) (hpzero : 0 < p 0) (X : ℕ → Ω → G) (N : ℕ)
    (ω : Ω) (i : Fin N) : 0 < jpRho p X N ω i := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  unfold jpRho
  refine div_pos ?_ hN
  refine Finset.sum_pos' (fun l _ => hp0 _) ⟨i, Finset.mem_univ _, ?_⟩
  rw [sub_self]
  exact hpzero

theorem jp_degree_pos {p : G → ℝ} (hp0 : ∀ u, 0 ≤ p u) (hpzero : 0 < p 0) (X : ℕ → Ω → G)
    (N : ℕ) (ω : Ω) (i : Fin N) :
    0 < ∑ l, jpK p X N ω i l / (jpRho p X N ω i * jpRho p X N ω l) := by
  refine Finset.sum_pos'
    (fun l _ => div_nonneg (hp0 _)
      (mul_pos (jpRho_pos hp0 hpzero X N ω i) (jpRho_pos hp0 hpzero X N ω l)).le)
    ⟨i, Finset.mem_univ _, ?_⟩
  refine div_pos ?_ (mul_pos (jpRho_pos hp0 hpzero X N ω i) (jpRho_pos hp0 hpzero X N ω i))
  unfold jpK
  rw [sub_self]
  exact hpzero

theorem jpSym_isHermitian {p : G → ℝ} (heven : ∀ u, p (-u) = p u) (X : ℕ → Ω → G) (N : ℕ)
    (ω : Ω) : (jpSym p X N ω).IsHermitian :=
  symGraph_isHermitian _ _ (jpK_symm heven X N ω)

theorem jp_trace_eq {p : G → ℝ} (hp0 : ∀ u, 0 ≤ p u) (hpzero : 0 < p 0) (X : ℕ → Ω → G)
    (N : ℕ) (ω : Ω) (k : ℕ) : (jpSym p X N ω ^ k).trace = (jpWalk p X N ω ^ k).trace :=
  symGraph_trace_pow _ _ (jp_degree_pos hp0 hpzero X N ω) k

theorem jp_trace_le_sq {p : G → ℝ} (hp0 : ∀ u, 0 ≤ p u) (hpzero : 0 < p 0)
    (heven : ∀ u, p (-u) = p u) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) {k : ℕ} (hk : 2 ≤ k) :
    |(jpSym p X N ω ^ k).trace| ≤ (jpSym p X N ω ^ 2).trace :=
  (symGraph_trace_bounds _ _ (jpK_symm heven X N ω) (fun i j => hp0 _)
    (jpRho_pos hp0 hpzero X N ω) (jp_degree_pos hp0 hpzero X N ω) k).2 hk

theorem jpSub_hasSum {p : G → ℝ} (heven : ∀ u, p (-u) = p u) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω)
    (τ : ℝ) :
    HasSum (fun j : ℕ => pw τ (j + 1) * (jpSym p X N ω ^ (j + 1)).trace) (jpSub p X N ω τ) := by
  have h := subtracted_trace_hasSum (jpSym p X N ω) (jpSym_isHermitian heven X N ω) τ
  rw [Fintype.card_fin] at h
  exact h

end Walk

section Limits

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableSub₂ G]
  [MeasurableNeg G] (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant]
  [ν.IsNegInvariant]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Entrywise limit of the powers of the sampled walk, kernel with bracketed translates.**
    `G` a commutative measurable group with an invariant probability measure `ν`; `X_j`
    independent with law `ν`; `p` a measurable even probability density, `0 ≤ p ≤ M`, `p(0) > 0`,
    NOT assumed continuous, whose translates have finite bracketing numbers. Then almost surely,
    for every `k` and `η > 0`, for all large `N` and all `a, i < N`:
    `|N (P_N^{k+1})_{ai} - p^{*(k+1)}(X_a - X_i)| ≤ η`. -/
theorem jump_walk_ae (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) (p : G → ℝ) (hp : Measurable p) {M : ℝ}
    (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (heven : ∀ u, p (-u) = p u) (hpzero : 0 < p 0)
    (hbrk : IsBrk ν (fun x z => p (x - z)) M) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ a i : Fin N,
      |(N : ℝ) * (jpWalk p X N ω ^ (k + 1)) a i - convPow ν p k (X a ω - X i ω)| ≤ η := by
  have hM0 : 0 ≤ M := (hp0 0).trans (hpM 0)
  have hpint : Integrable p ν := integrable_of_bdd ν hp hp0 hpM
  filter_upwards [jump_events_ae (μ := μ) ν X h_indep hX hlaw p hp hp0 hpM hmass heven hbrk]
    with ω hω k η hη
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 10 * M + 3 * (k : ℝ) * (3 + 11 * M) + 1 := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hC]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 8) (η / C) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; exact lt_min (by norm_num) (div_pos hη hCpos)
  have hε8 : ε ≤ 1 / 8 := by rw [hεdef]; exact min_le_left _ _
  have hεC : ε * C ≤ η := by
    have h : ε ≤ η / C := by rw [hεdef]; exact min_le_right _ _
    calc ε * C ≤ η / C * C := mul_le_mul_of_nonneg_right h hCpos.le
      _ = η := div_mul_cancel₀ η hCpos.ne'
  obtain ⟨hn, hc⟩ := hω ε hε0
  have hcall : ∀ᶠ N : ℕ in atTop, ∀ m ∈ Finset.range k, ∀ t : G × G,
      |∑ j ∈ Finset.range N, p (t.1 - X j ω) * convPow ν p m (X j ω - t.2)
        - N * convPow ν p (m + 1) (t.1 - t.2)| ≤ ε * N := by
    rw [eventually_all_finset]
    intro m _
    exact hc m
  filter_upwards [hn, hcall, eventually_gt_atTop 0] with N h1 h2 hNpos a i
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hP : ∀ b j : Fin N, jpWalk p X N ω b j
      = (p (X b ω - X j ω) / ((∑ l : Fin N, p (X j ω - X l ω)) / N))
        / ∑ l : Fin N, p (X b ω - X l ω) / ((∑ l' : Fin N, p (X l ω - X l' ω)) / N) :=
    fun b j => walkMatrix_apply' _ _ b j (jpRho_pos hp0 hpzero X N ω b).ne'
  have key := jump_point_det ν (fun j => X j ω) p (fun _ => M) N k (convPow_nonneg ν p hp0)
    (convPow_le_all ν p hp hp0 hpM hpint hmass) (jpWalk p X N ω) hP
    (epsn := ε * N) (epsc := ε * N) (by positivity) (by nlinarith) h1
    (fun m hm t => h2 m (Finset.mem_range.2 hm) t) a i
  have e : ε * N / N = ε := by field_simp
  rw [e, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at key
  refine key.trans (jump_tol hε0.le hε8 hM0 (convPow_le_all ν p hp hp0 hpM hpint hmass k _)
    (Nat.cast_nonneg k) ?_)
  rw [← hC]; exact hεC

/-- **Theorem "fixedxi"(i) / Proposition "fixedxijump" for the traces of the powers.** Under the
    hypotheses of `jump_walk_ae`: almost surely, for every `k`,
    `Tr P_N^{k+1} → p^{*(k+1)}(0)` as `N → ∞` (one null set for all `k`). -/
theorem jump_trace_tendsto_ae (X : ℕ → Ω → G) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (p : G → ℝ) (hp : Measurable p)
    {M : ℝ} (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (heven : ∀ u, p (-u) = p u) (hpzero : 0 < p 0)
    (hbrk : IsBrk ν (fun x z => p (x - z)) M) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ,
      Tendsto (fun N => (jpWalk p X N ω ^ (k + 1)).trace) atTop (𝓝 (convPow ν p k 0)) := by
  filter_upwards [jump_walk_ae (μ := μ) ν X h_indep hX hlaw p hp hp0 hpM hmass heven hpzero hbrk]
    with ω hω k
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hω k (ε / 2) (half_pos hε), eventually_gt_atTop 0] with N hN hNpos
  rw [Real.dist_eq]
  have h := trace_from_diagonal hNpos (jpWalk p X N ω ^ (k + 1)) (m := convPow ν p k 0)
    (E := ε / 2) (fun a => by
      have h := hN a a
      rw [sub_self] at h
      exact h)
  linarith

/-- The limit of the subtracted trace: `e^{-τ} ∑_{j≥1} τ^j/j! · p^{*j}(0)`. -/
noncomputable def jpMean (p : G → ℝ) (τ : ℝ) : ℝ := ∑' j : ℕ, pw τ (j + 1) * convPow ν p j 0

theorem jpMean_hasSum (p : G → ℝ) (hp : Measurable p) {M : ℝ} (hp0 : ∀ u, 0 ≤ p u)
    (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    HasSum (fun j : ℕ => pw τ (j + 1) * convPow ν p j 0) (jpMean ν p τ) := by
  have hpint : Integrable p ν := integrable_of_bdd ν hp hp0 hpM
  refine (Summable.of_nonneg_of_le (fun j => mul_nonneg (pw_nonneg hτ _) (convPow_nonneg ν p hp0 j 0))
    (fun j => mul_le_mul_of_nonneg_left (convPow_le_all ν p hp hp0 hpM hpint hmass j 0)
      (pw_nonneg hτ _)) ((pw_shift_hasSum τ).summable.mul_right M)).hasSum

/-- **Theorem "fixedxi"(ii) / Proposition "fixedxijump" for the subtracted trace, uniformly on
    compact sets of `τ`.** Under the hypotheses of `jump_walk_ae`: almost surely, for every
    `Tm ≥ 0` and `ε > 0`, for all large `N`:
    `|Tr exp(τ(S_N - 1)) - N e^{-τ} - e^{-τ} ∑_{j≥1} τ^j/j! · p^{*j}(0)| ≤ ε` for all
    `τ ∈ [0, Tm]`. -/
theorem jump_subtracted_uniform_ae (X : ℕ → Ω → G) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = ν) (p : G → ℝ) (hp : Measurable p)
    {M : ℝ} (hp0 : ∀ u, 0 ≤ p u) (hpM : ∀ u, p u ≤ M) (hmass : ∫ u, p u ∂ν = 1)
    (heven : ∀ u, p (-u) = p u) (hpzero : 0 < p 0)
    (hbrk : IsBrk ν (fun x z => p (x - z)) M) :
    ∀ᵐ ω ∂μ, ∀ Tm : ℝ, 0 ≤ Tm → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ τ, 0 ≤ τ → τ ≤ Tm →
      |jpSub p X N ω τ - jpMean ν p τ| ≤ ε := by
  have hM0 : 0 ≤ M := (hp0 0).trans (hpM 0)
  have hpint : Integrable p ν := integrable_of_bdd ν hp hp0 hpM
  filter_upwards [jump_trace_tendsto_ae (μ := μ) ν X h_indep hX hlaw p hp hp0 hpM hmass heven
    hpzero hbrk] with ω hω Tm hTm ε hε
  obtain ⟨mf, hmf⟩ : ∃ mf : ℕ → ℝ, mf = fun j => convPow ν p (j - 1) 0 := ⟨_, rfl⟩
  have hmf1 : ∀ j, mf (j + 1) = convPow ν p j 0 := fun j => by
    rw [hmf]; simp only [Nat.add_sub_cancel]
  have hconv : ∀ j, Tendsto (fun N => (jpSym p X N ω ^ (j + 1)).trace) atTop
      (𝓝 (mf (j + 1))) := fun j => by
    rw [hmf1]
    exact (hω j).congr (fun N => (jp_trace_eq hp0 hpzero X N ω (j + 1)).symm)
  have hm0 : ∀ j, 0 ≤ mf (j + 1) := fun j => by rw [hmf1]; exact convPow_nonneg ν p hp0 j 0
  have hmle : ∀ j, mf (j + 1) ≤ M := fun j => by
    rw [hmf1]; exact convPow_le_all ν p hp hp0 hpM hpint hmass j 0
  have hm : ∀ j, |mf (j + 1)| ≤ M + 1 := fun j => by
    rw [abs_of_nonneg (hm0 j)]; linarith [hmle j]
  have hev : ∀ j, ∀ᶠ N in atTop, |(jpSym p X N ω ^ (j + 1)).trace| ≤ M + 1 := fun j => by
    filter_upwards [(Metric.tendsto_nhds.1 (hconv j)) 1 one_pos] with N hN
    rw [Real.dist_eq] at hN
    have h1 := abs_sub_abs_le_abs_sub ((jpSym p X N ω ^ (j + 1)).trace) (mf (j + 1))
    have h3 : |mf (j + 1)| ≤ M := by rw [abs_of_nonneg (hm0 j)]; exact hmle j
    linarith
  have hB : ∀ᶠ N in atTop, ∀ j, |(jpSym p X N ω ^ (j + 1)).trace| ≤ M + 1 := by
    filter_upwards [hev 0, hev 1] with N h0 h1 j
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj]; exact h0
    · have h2 := jp_trace_le_sq hp0 hpzero heven X N ω (k := j + 1) (by omega)
      exact h2.trans ((le_abs_self _).trans h1)
  filter_upwards [poisson_limit_uniform (fun N j => (jpSym p X N ω ^ j).trace)
    mf hTm hconv hB hm hε] with N hN τ hτ0 hτ
  refine hN τ hτ0 hτ _ _ (jpSub_hasSum heven X N ω τ) ?_
  have h := jpMean_hasSum ν p hp hp0 hpM hmass hτ0
  simp only [hmf1]
  exact h

end Limits

/-! ### The normalised indicator of a ball: a kernel with a jump -/

section Ball

variable {G : Type*} [AddCommGroup G] [MetricSpace G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
  (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsAddLeftInvariant] [ν.IsNegInvariant]

/-- The indicator function of the closed ball of radius `ξ` about `0`, normalised to a
    probability density: `p(u) = 1_{dist(u,0) ≤ ξ} / ν(B(0,ξ))`. -/
noncomputable def ballKer (ξ : ℝ) : G → ℝ :=
  (Metric.closedBall (0 : G) ξ).indicator (fun _ => (ν.real (Metric.closedBall (0 : G) ξ))⁻¹)

theorem ballKer_measurable (ξ : ℝ) : Measurable (ballKer ν ξ) :=
  measurable_const.indicator measurableSet_closedBall

theorem ballKer_nonneg (ξ : ℝ) (u : G) : 0 ≤ ballKer ν ξ u :=
  Set.indicator_nonneg (fun _ _ => inv_nonneg.2 measureReal_nonneg) u

theorem ballKer_le (ξ : ℝ) (u : G) :
    ballKer ν ξ u ≤ (ν.real (Metric.closedBall (0 : G) ξ))⁻¹ := by
  classical
  unfold ballKer
  rw [Set.indicator_apply]
  split_ifs
  · exact le_rfl
  · exact inv_nonneg.2 measureReal_nonneg

theorem ballKer_mass {ξ : ℝ} (hc : 0 < ν.real (Metric.closedBall (0 : G) ξ)) :
    ∫ u, ballKer ν ξ u ∂ν = 1 := by
  unfold ballKer
  rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_inv_cancel₀ hc.ne']

theorem ballKer_even (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x') (ξ : ℝ) (u : G) :
    ballKer ν ξ (-u) = ballKer ν ξ u := by
  have h : dist (-u) 0 = dist u 0 := by
    have h := hdist 0 u u
    rw [zero_sub, sub_self] at h
    rw [h, dist_comm]
  classical
  unfold ballKer
  simp only [Set.indicator_apply, Metric.mem_closedBall, h]

theorem ballKer_zero_pos {ξ : ℝ} (hc : 0 < ν.real (Metric.closedBall (0 : G) ξ)) :
    0 < ballKer ν ξ 0 := by
  have hξ : 0 ≤ ξ := by
    by_contra h
    rw [Metric.closedBall_eq_empty.2 (not_le.1 h), measureReal_empty] at hc
    exact lt_irrefl _ hc
  unfold ballKer
  rw [Set.indicator_of_mem (Metric.mem_closedBall_self hξ)]
  exact inv_pos.2 hc

theorem ballKer_sub (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x') (ξ : ℝ) (x z : G) :
    ballKer ν ξ (x - z) = (Metric.closedBall x ξ).indicator
      (fun _ => (ν.real (Metric.closedBall (0 : G) ξ))⁻¹) z := by
  have h : dist (x - z) 0 = dist z x := by
    have h := hdist x z z
    rw [sub_self] at h
    rw [h, dist_comm]
  classical
  unfold ballKer
  simp only [Set.indicator_apply, Metric.mem_closedBall, h]

theorem ball_transl (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x') (a : G) (ρ : ℝ) :
    ν.real (Metric.closedBall a ρ) = ν.real (Metric.closedBall (0 : G) ρ) := by
  have e : Metric.closedBall a ρ = (fun z => z + (-a)) ⁻¹' Metric.closedBall (0 : G) ρ := by
    ext z
    simp only [Metric.mem_closedBall, Set.mem_preimage]
    have h := hdist z a a
    rw [sub_self] at h
    rw [← sub_eq_add_neg, h]
  rw [measureReal_def, measureReal_def, e, measure_preimage_add_right]

theorem brk_ball_arith {c F Fp Fm ε : ℝ} (hc : 0 < c) (h1 : |Fp - F| < ε / (2 * c))
    (h2 : |Fm - F| < ε / (2 * c)) : Fp * c - Fm * c ≤ ε := by
  rw [abs_lt] at h1 h2
  have e : ε / (2 * c) * c = ε / 2 := by field_simp
  have a := mul_lt_mul_of_pos_right h1.2 hc
  have b := mul_lt_mul_of_pos_right h2.1 hc
  rw [e] at a
  rw [neg_mul, e] at b
  nlinarith

/-- **The translates of the indicator of a ball have finite bracketing numbers**, provided the
    volume of the ball is continuous in the radius at `ξ` (equivalently: the sphere of radius `ξ`
    is a null set). Brackets: balls of radius `ξ ∓ r` about the points of a finite `r`-net. -/
theorem ballKer_brk (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x') {ξ : ℝ}
    (hc : 0 < ν.real (Metric.closedBall (0 : G) ξ))
    (hcont : ContinuousAt (fun ρ : ℝ => ν.real (Metric.closedBall (0 : G) ρ)) ξ) :
    IsBrk ν (fun x z => ballKer ν ξ (x - z)) (ν.real (Metric.closedBall (0 : G) ξ))⁻¹ := by
  intro ε hε
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (ν.real (Metric.closedBall (0 : G) ξ))⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hcdef]; exact inv_pos.2 hc
  obtain ⟨δ, hδ, hδF⟩ := Metric.continuousAt_iff.1 hcont (ε / (2 * c)) (by positivity)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = δ / 2 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hF1 : |ν.real (Metric.closedBall (0 : G) (ξ + r)) - ν.real (Metric.closedBall (0 : G) ξ)|
      < ε / (2 * c) := by
    have h := hδF (x := ξ + r) (by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hr0]; linarith)
    rw [Real.dist_eq] at h
    exact h
  have hF2 : |ν.real (Metric.closedBall (0 : G) (ξ - r)) - ν.real (Metric.closedBall (0 : G) ξ)|
      < ε / (2 * c) := by
    have h := hδF (x := ξ - r) (by
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hr0]; linarith)
    rw [Real.dist_eq] at h
    exact h
  obtain ⟨t, -, htfin, htcov⟩ :=
    finite_cover_balls_of_compact (isCompact_univ : IsCompact (Set.univ : Set G)) hr0
  rw [← hcdef]
  refine ⟨(fun a : G => ((Metric.closedBall a (ξ - r)).indicator (fun _ => c),
    (Metric.closedBall a (ξ + r)).indicator (fun _ => c))) '' t, htfin.image _, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    refine ⟨measurable_const.indicator measurableSet_closedBall,
      measurable_const.indicator measurableSet_closedBall,
      fun z => ⟨Set.indicator_nonneg (fun _ _ => hc0.le) z, ?_, ?_⟩, ?_⟩
    · show (Metric.closedBall a (ξ - r)).indicator (fun _ => c) z
        ≤ (Metric.closedBall a (ξ + r)).indicator (fun _ => c) z
      exact Set.indicator_le_indicator_of_subset
        (Metric.closedBall_subset_closedBall (by linarith)) (fun _ => hc0.le) z
    · show (Metric.closedBall a (ξ + r)).indicator (fun _ => c) z ≤ c
      classical
      rw [Set.indicator_apply]
      split_ifs
      · exact le_rfl
      · exact hc0.le
    · show ∫ z, ((Metric.closedBall a (ξ + r)).indicator (fun _ => c) z
          - (Metric.closedBall a (ξ - r)).indicator (fun _ => c) z) ∂ν ≤ ε
      rw [integral_sub ((integrable_const c).indicator measurableSet_closedBall)
          ((integrable_const c).indicator measurableSet_closedBall),
        integral_indicator_const c measurableSet_closedBall,
        integral_indicator_const c measurableSet_closedBall, smul_eq_mul, smul_eq_mul,
        ball_transl ν hdist a, ball_transl ν hdist a]
      exact brk_ball_arith hc0 hF1 hF2
  · intro x
    have hx := htcov (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    refine ⟨_, ⟨a, ha, rfl⟩, fun z => ?_⟩
    show (Metric.closedBall a (ξ - r)).indicator (fun _ => c) z ≤ ballKer ν ξ (x - z)
      ∧ ballKer ν ξ (x - z) ≤ (Metric.closedBall a (ξ + r)).indicator (fun _ => c) z
    rw [ballKer_sub ν hdist, ← hcdef]
    exact ⟨Set.indicator_le_indicator_of_subset
        (Metric.closedBall_subset_closedBall' (by linarith [dist_comm a x])) (fun _ => hc0.le) z,
      Set.indicator_le_indicator_of_subset
        (Metric.closedBall_subset_closedBall' (by linarith)) (fun _ => hc0.le) z⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Proposition "fixedxijump" for the indicator of a ball on a compact abelian group.**
    `G` compact abelian with a translation-invariant metric and invariant probability measure
    `ν`; `X_j` independent with law `ν`; kernel `k(x,y) = 1_{dist(x,y) ≤ ξ}` (the walk does not
    depend on the normalising constant), self-loops kept, estimated normalisation.
    HYPOTHESES on the geometry: the ball has positive volume, and its volume is continuous in the
    radius at `ξ`. Then almost surely:
    (a) for every `k` and `η > 0`, eventually `|N (P_N^{k+1})_{ai} - p^{*(k+1)}(X_a - X_i)| ≤ η`
        for all `a, i < N`;
    (b) `Tr P_N^{k+1} → p^{*(k+1)}(0)` for every `k`;
    (c) for every `Tm ≥ 0`, `ε > 0`, eventually
        `|Tr exp(τ(S_N - 1)) - N e^{-τ} - e^{-τ} ∑_{j≥1} τ^j/j! p^{*j}(0)| ≤ ε` for all
        `τ ∈ [0, Tm]`. -/
theorem ball_fixed_scale_ae (hdist : ∀ x x' y : G, dist (x - y) (x' - y) = dist x x')
    (X : ℕ → Ω → G) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = ν) {ξ : ℝ}
    (hc : 0 < ν.real (Metric.closedBall (0 : G) ξ))
    (hcont : ContinuousAt (fun ρ : ℝ => ν.real (Metric.closedBall (0 : G) ρ)) ξ) :
    ∀ᵐ ω ∂μ,
      (∀ k : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ a i : Fin N,
        |(N : ℝ) * (jpWalk (ballKer ν ξ) X N ω ^ (k + 1)) a i
          - convPow ν (ballKer ν ξ) k (X a ω - X i ω)| ≤ η)
      ∧ (∀ k : ℕ, Tendsto (fun N => (jpWalk (ballKer ν ξ) X N ω ^ (k + 1)).trace) atTop
          (𝓝 (convPow ν (ballKer ν ξ) k 0)))
      ∧ (∀ Tm : ℝ, 0 ≤ Tm → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ τ, 0 ≤ τ → τ ≤ Tm →
          |jpSub (ballKer ν ξ) X N ω τ - jpMean ν (ballKer ν ξ) τ| ≤ ε) := by
  have hbrk := ballKer_brk ν hdist hc hcont
  filter_upwards [
    jump_walk_ae (μ := μ) ν X h_indep hX hlaw (ballKer ν ξ) (ballKer_measurable ν ξ)
      (ballKer_nonneg ν ξ) (ballKer_le ν ξ) (ballKer_mass ν hc) (ballKer_even ν hdist ξ)
      (ballKer_zero_pos ν hc) hbrk,
    jump_trace_tendsto_ae (μ := μ) ν X h_indep hX hlaw (ballKer ν ξ) (ballKer_measurable ν ξ)
      (ballKer_nonneg ν ξ) (ballKer_le ν ξ) (ballKer_mass ν hc) (ballKer_even ν hdist ξ)
      (ballKer_zero_pos ν hc) hbrk,
    jump_subtracted_uniform_ae (μ := μ) ν X h_indep hX hlaw (ballKer ν ξ)
      (ballKer_measurable ν ξ) (ballKer_nonneg ν ξ) (ballKer_le ν ξ) (ballKer_mass ν hc)
      (ballKer_even ν hdist ξ) (ballKer_zero_pos ν hc) hbrk] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

end Ball

/-! ### The flat torus: cubes (`d = 1`: intervals) -/

/-- Volume of the closed ball of the flat torus in its metric (the supremum over the coordinates
    of the distances on the circle; a cube, for `d = 1` the interval `|u| ≤ ρ`):
    `min(1, 2ρ)^d`. -/
theorem torus_ball_real (d : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (flatTorusMeasure d).real (Metric.closedBall (0 : FlatTorus d) ρ) = (min 1 (2 * ρ)) ^ d := by
  have h1 : ∀ s : Set UnitAddCircle,
      (AddCircle.haarAddCircle : Measure UnitAddCircle) s = MeasureTheory.volume s := by
    intro s
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  have hm : (0 : ℝ) ≤ min 1 (2 * ρ) := le_min zero_le_one (by linarith)
  rw [measureReal_def, closedBall_pi _ hρ, Measure.pi_pi]
  simp only [h1, AddCircle.volume_closedBall, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hm]

/-- **Proposition "fixedxijump" on the flat torus, cube profile, without hypotheses on the
    geometry.** Independent uniform points on `FlatTorus d`; kernel
    `k(x,y) = 1_{max_i |x_i - y_i| ≤ ξ}` (distance on the circle), `ξ > 0`; for `d = 1` this is the
    indicator of the interval `|x - y| ≤ ξ`, the indicator of a ball. The three conclusions of
    `ball_fixed_scale_ae` hold almost surely. -/
theorem torus_cube_fixed_scale_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {ξ : ℝ}
    (hξ : 0 < ξ) :
    ∀ᵐ ω ∂μ,
      (∀ k : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop, ∀ a i : Fin N,
        |(N : ℝ) * (jpWalk (ballKer (flatTorusMeasure d) ξ) X N ω ^ (k + 1)) a i
          - convPow (flatTorusMeasure d) (ballKer (flatTorusMeasure d) ξ) k (X a ω - X i ω)| ≤ η)
      ∧ (∀ k : ℕ, Tendsto
          (fun N => (jpWalk (ballKer (flatTorusMeasure d) ξ) X N ω ^ (k + 1)).trace) atTop
          (𝓝 (convPow (flatTorusMeasure d) (ballKer (flatTorusMeasure d) ξ) k 0)))
      ∧ (∀ Tm : ℝ, 0 ≤ Tm → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ τ, 0 ≤ τ → τ ≤ Tm →
          |jpSub (ballKer (flatTorusMeasure d) ξ) X N ω τ
            - jpMean (flatTorusMeasure d) (ballKer (flatTorusMeasure d) ξ) τ| ≤ ε) := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have hc : 0 < (flatTorusMeasure d).real (Metric.closedBall (0 : FlatTorus d) ξ) := by
    rw [torus_ball_real d hξ.le]
    exact pow_pos (lt_min one_pos (by linarith)) d
  have hcont : ContinuousAt
      (fun ρ : ℝ => (flatTorusMeasure d).real (Metric.closedBall (0 : FlatTorus d) ρ)) ξ := by
    have h1 : ContinuousAt (fun ρ : ℝ => (min 1 (2 * ρ)) ^ d) ξ :=
      (by fun_prop : Continuous (fun ρ : ℝ => (min 1 (2 * ρ)) ^ d)).continuousAt
    refine h1.congr ?_
    filter_upwards [Ioi_mem_nhds hξ] with ρ hρ
    exact (torus_ball_real d (le_of_lt hρ)).symm
  exact ball_fixed_scale_ae (μ := μ) (flatTorusMeasure d) (fun x x' y => dist_sub_right x x' y)
    X h_indep hX hlaw hc hcont

/-- For `d = 1` and `ξ ≤ 1/2` the normalising constant is `1/(2ξ)`: the kernel is
    `1_{|u| ≤ ξ}/(2ξ)`, and `p(0) = m_1 = 1/(2ξ)` (the value `ξ^{-d}/|B|` of the paper). -/
theorem interval_ballKer_zero {ξ : ℝ} (hξ : 0 < ξ) (hξ2 : ξ ≤ 1 / 2) :
    ballKer (flatTorusMeasure 1) ξ 0 = 1 / (2 * ξ) := by
  unfold ballKer
  rw [Set.indicator_of_mem (Metric.mem_closedBall_self hξ.le), torus_ball_real 1 hξ.le, pow_one,
    min_eq_right (by linarith), one_div]

end JumpProfile

end CTG.Reals2
