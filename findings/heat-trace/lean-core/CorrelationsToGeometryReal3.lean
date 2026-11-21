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

end CTG.Reals2
