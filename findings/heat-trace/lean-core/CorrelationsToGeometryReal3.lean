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

end CTG.Reals2
