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

end CTG.Reals2
