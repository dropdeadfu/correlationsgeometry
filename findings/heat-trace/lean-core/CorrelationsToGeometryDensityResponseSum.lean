/-
Fifty-fifth file: the local density response on the flat torus summed over the powers.
Namespace `CTG.DensityResponseSum`; imports the fifty-first and the fifty-fourth file (compiled modules);
check with `./check_density_response_sum.sh`.
Notation: `t_m = ga c m = exp(−c|m|²)`, `fc J` the coefficients of `1 − √(1−s)`, `hJ`, as in the fifty-fourth file.
`cl u v = u/(2√(1−u))` if `u = v`, `u/(√(1−u)+√(1−v))` otherwise.
`mode_hasSum`: for `c > 0`, `n ≠ 0` and every `m`, `Σ_J fc J · hJ(t_m, t_{m+n}) J = cl(t_m, t_{m+n})` (the case
`t_m = t_{m+n} = 1` does not occur for `n ≠ 0`); `cl_summable`; `double_summable`;
`sum_powers_modes`: `Σ_J fc J Σ_m hJ(t_m, t_{m+n}) J = Σ_m cl(t_m, t_{m+n})`, all sums convergent;
`brk c n j`: literally the bracket of `kpow_diag_torus` of the fifty-first file; `brk_eq`;
`local_response_sum`: `Σ_j fc(j+1) · brk c n j = Σ_m cl(t_m, t_{m+n})`.
Together with `kpow_diag_torus` this is the sum over the powers of the first-order local responses of the iterated
kernels, weighted with the coefficients of `1 − √(1−s)`.
NOT formalised: that this sum is the derivative of the corresponding sum of the perturbed iterated kernels (exchange
of the derivative in the density with the sum over the powers; needs remainders of second order uniform in the
power); the symmetrised form `½ Σ_m (t_m + t_{m+n})/(w_m + w_{m+n})`; the coefficient `c(a)`, the passage to the
continuum integral `I(a)` and the limit `3 (aξ)²`.  No hypothesis.  No sorry, no axiom, no native_decide.
Written by the author-side AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryDensityResponseLocal
import CorrelationsToGeometrySqrtSeries

open Finset
open CTG.DensityResponseCont.Local (ga ga_nonneg ga_le_one ga_summable)
open CTG.SqrtSeries

noncomputable section
namespace CTG.DensityResponseSum

variable {d : ℕ}

lemma ga_pow (c : ℝ) (k : ℕ) (m : Fin d → ℤ) : ga ((k : ℝ) * c) m = ga c m ^ k := by
  unfold ga
  rw [← Real.exp_nat_mul]; congr 1; ring

lemma ssq_nonneg (m : Fin d → ℤ) : 0 ≤ ∑ i, ((m i : ℤ) : ℝ) ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

lemma ga_eq_one_iff {c : ℝ} (hc : 0 < c) (m : Fin d → ℤ) : ga c m = 1 ↔ m = 0 := by
  unfold ga
  rw [Real.exp_eq_one_iff]
  constructor
  · intro h
    have hS : ∑ i, ((m i : ℤ) : ℝ) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h with h1 | h1
      · linarith
      · exact h1
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((m i : ℤ) : ℝ))).mp hS i
      (Finset.mem_univ i)
    have h2 : ((m i : ℤ) : ℝ) = 0 := by simpa using this
    exact_mod_cast h2
  · rintro rfl; simp

lemma ga_le_exp {c : ℝ} (hc : 0 < c) {m : Fin d → ℤ} (hm : m ≠ 0) : ga c m ≤ Real.exp (-c) := by
  unfold ga
  apply Real.exp_le_exp.mpr
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h; push_neg at h; exact hm (funext h)
  have h1 : (1 : ℝ) ≤ ((m i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (m i) ^ 2 := by
      have := Int.one_le_abs hi
      nlinarith [sq_abs (m i)]
    exact_mod_cast this
  have h2 : ((m i : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((m j : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((m j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  nlinarith

/-- closed form of the sum over the powers for one mode. -/
def cl (u v : ℝ) : ℝ :=
  if u = v then u / (2 * Real.sqrt (1 - u)) else u / (Real.sqrt (1 - u) + Real.sqrt (1 - v))

lemma cl_nonneg {u v : ℝ} (hu : 0 ≤ u) : 0 ≤ cl u v := by
  unfold cl; split_ifs <;> positivity

lemma cl_le {u v q : ℝ} (hu : 0 ≤ u) (huq : u ≤ q) (hq : q < 1) :
    cl u v ≤ u / Real.sqrt (1 - q) := by
  have hwq : 0 < Real.sqrt (1 - q) := Real.sqrt_pos.mpr (by linarith)
  have hwu : Real.sqrt (1 - q) ≤ Real.sqrt (1 - u) := Real.sqrt_le_sqrt (by linarith)
  have hwv : 0 ≤ Real.sqrt (1 - v) := Real.sqrt_nonneg _
  unfold cl
  split_ifs
  · exact div_le_div_of_nonneg_left hu hwq (by linarith)
  · exact div_le_div_of_nonneg_left hu hwq (by linarith)

/-- the sum over the powers for the mode `m`. -/
lemma mode_hasSum {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) (m : Fin d → ℤ) :
    HasSum (fun J => fc J * hJ (ga c m) (ga c (m + n)) J) (cl (ga c m) (ga c (m + n))) := by
  unfold cl
  by_cases h : ga c m = ga c (m + n)
  · rw [if_pos h, ← h]
    refine mode_sum_eq (ga_nonneg c m) (lt_of_le_of_ne (ga_le_one hc.le m) ?_)
    intro h1
    have hm : m = 0 := (ga_eq_one_iff hc m).mp h1
    have hmn : m + n = 0 := (ga_eq_one_iff hc (m + n)).mp (h ▸ h1)
    apply hn; rw [hm, zero_add] at hmn; exact hmn
  · rw [if_neg h]
    exact mode_sum_ne (ga_nonneg c m) (ga_le_one hc.le m) (ga_nonneg c _) (ga_le_one hc.le _) h

lemma cl_summable {c : ℝ} (hc : 0 < c) (n : Fin d → ℤ) :
    Summable fun m : Fin d → ℤ => cl (ga c m) (ga c (m + n)) := by
  have hq : Real.exp (-c) < 1 := by
    have := Real.exp_lt_exp.mpr (show -c < 0 by linarith); simpa using this
  have hs : Summable fun m : Fin d → ℤ => ga c m := by
    have := ga_summable hc d
    simpa [abs_of_nonneg (ga_nonneg c _)] using this
  set K0 : ℝ := cl (ga c (0 : Fin d → ℤ)) (ga c ((0 : Fin d → ℤ) + n)) with hK0
  have hi : Summable fun m : Fin d → ℤ => (if m = 0 then K0 else 0) :=
    (hasSum_ite_eq (0 : Fin d → ℤ) K0).summable
  have hb : Summable fun m : Fin d → ℤ =>
      ga c m / Real.sqrt (1 - Real.exp (-c)) + (if m = 0 then K0 else 0) :=
    (hs.div_const _).add hi
  refine Summable.of_nonneg_of_le (fun m => cl_nonneg (ga_nonneg c m)) (fun m => ?_) hb
  by_cases hm : m = 0
  · subst hm
    rw [if_pos rfl]
    have : 0 ≤ ga c (0 : Fin d → ℤ) / Real.sqrt (1 - Real.exp (-c)) :=
      div_nonneg (ga_nonneg c _) (Real.sqrt_nonneg _)
    linarith
  · rw [if_neg hm, add_zero]
    exact cl_le (ga_nonneg c m) (ga_le_exp hc hm) hq

/-- the double family is summable. -/
lemma double_summable {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) :
    Summable fun p : (Fin d → ℤ) × ℕ => fc p.2 * hJ (ga c p.1) (ga c (p.1 + n)) p.2 := by
  rw [summable_prod_of_nonneg (fun p => mul_nonneg (fc_nonneg _)
    (hJ_nonneg (ga_nonneg c _) (ga_nonneg c _) _))]
  refine ⟨fun m => (mode_hasSum hc hn m).summable, ?_⟩
  have : (fun m : Fin d → ℤ => ∑' J, fc J * hJ (ga c m) (ga c (m + n)) J)
      = fun m => cl (ga c m) (ga c (m + n)) := by
    funext m; exact (mode_hasSum hc hn m).tsum_eq
  rw [this]; exact cl_summable hc n

/-- **Sum over the powers and over the modes.** For `c > 0`, `n ≠ 0`:
`Σ_J f_J Σ_m h_J(t_m, t_{m+n}) = Σ_m cl(t_m, t_{m+n})`, all sums convergent. -/
theorem sum_powers_modes {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) :
    HasSum (fun J : ℕ => fc J * ∑' m : Fin d → ℤ, hJ (ga c m) (ga c (m + n)) J)
      (∑' m : Fin d → ℤ, cl (ga c m) (ga c (m + n))) := by
  have hd := double_summable hc hn
  have h1 : HasSum (fun m : Fin d → ℤ => cl (ga c m) (ga c (m + n)))
      (∑' p : (Fin d → ℤ) × ℕ, fc p.2 * hJ (ga c p.1) (ga c (p.1 + n)) p.2) :=
    hd.hasSum.prod_fiberwise fun m => mode_hasSum hc hn m
  have hd' := hd.prod_symm
  have h2 : HasSum (fun J : ℕ => fc J * ∑' m : Fin d → ℤ, hJ (ga c m) (ga c (m + n)) J)
      (∑' p : ℕ × (Fin d → ℤ), fc p.1 * hJ (ga c p.2) (ga c (p.2 + n)) p.1) := by
    refine hd'.hasSum.prod_fiberwise fun J => ?_
    have hsm : Summable fun m : Fin d → ℤ => fc J * hJ (ga c m) (ga c (m + n)) J :=
      hd'.prod_factor J
    have := hsm.hasSum
    rwa [tsum_mul_left] at this
  have e : (∑' p : ℕ × (Fin d → ℤ), fc p.1 * hJ (ga c p.2) (ga c (p.2 + n)) p.1)
      = ∑' p : (Fin d → ℤ) × ℕ, fc p.2 * hJ (ga c p.1) (ga c (p.1 + n)) p.2 :=
    (Equiv.prodComm ℕ (Fin d → ℤ)).tsum_eq
      (fun p : (Fin d → ℤ) × ℕ => fc p.2 * hJ (ga c p.1) (ga c (p.1 + n)) p.2)
  rw [e, ← h1.tsum_eq] at h2
  exact h2


/-- The bracket of `kpow_diag_torus` (fifty-first file) for the iterate with `j + 1` factors. -/
def brk (c : ℝ) (n : Fin d → ℤ) (j : ℕ) : ℝ :=
  (∑' m : Fin d → ℤ, ga (((j + 1 : ℕ) : ℝ) * c) m) +
    ∑ i ∈ range j, ∑' m : Fin d → ℤ, ga (((i + 1 : ℕ) : ℝ) * c) m * ga (((j - i : ℕ) : ℝ) * c) (m + n)

lemma ga_sum {c : ℝ} (hc : 0 < c) (k : ℕ) (hk : 0 < k) :
    Summable fun m : Fin d → ℤ => ga ((k : ℝ) * c) m := by
  have hkc : 0 < (k : ℝ) * c := mul_pos (by exact_mod_cast hk) hc
  have := ga_summable hkc d
  simpa [abs_of_nonneg (ga_nonneg _ _)] using this

lemma brk_eq {c : ℝ} (hc : 0 < c) (n : Fin d → ℤ) (j : ℕ) :
    brk c n j = ∑' m : Fin d → ℤ, hJ (ga c m) (ga c (m + n)) (j + 1) := by
  have hterm : ∀ m : Fin d → ℤ, hJ (ga c m) (ga c (m + n)) (j + 1)
      = (∑ i ∈ range j, ga (((i + 1 : ℕ) : ℝ) * c) m * ga (((j - i : ℕ) : ℝ) * c) (m + n))
        + ga (((j + 1 : ℕ) : ℝ) * c) m := by
    intro m
    unfold hJ
    rw [sum_range_succ]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      rw [show j + 1 - 1 - i = j - i by omega, ga_pow, ga_pow]
    · rw [show j + 1 - 1 - j = 0 by omega, pow_zero, mul_one, ga_pow]
  have hs2 : ∀ i ∈ range j, Summable fun m : Fin d → ℤ =>
      ga (((i + 1 : ℕ) : ℝ) * c) m * ga (((j - i : ℕ) : ℝ) * c) (m + n) := by
    intro i _
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (ga_nonneg _ _) (ga_nonneg _ _))
      (fun m => ?_) (ga_sum hc (i + 1) (Nat.succ_pos i))
    have h1 : ga (((j - i : ℕ) : ℝ) * c) (m + n) ≤ 1 :=
      ga_le_one (mul_nonneg (Nat.cast_nonneg _) hc.le) _
    have h0 := ga_nonneg (((i + 1 : ℕ) : ℝ) * c) m
    nlinarith
  rw [tsum_congr hterm, Summable.tsum_add (summable_sum hs2) (ga_sum hc (j + 1) (Nat.succ_pos j)),
    Summable.tsum_finsetSum hs2]
  unfold brk; ring

/-- **The local density response summed over the powers.** For `c > 0`, `n ≠ 0`, with the brackets
`brk c n j` of `kpow_diag_torus`: `Σ_j f_{j+1} · brk c n j = Σ_m cl(t_m, t_{m+n})`. -/
theorem local_response_sum {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) :
    HasSum (fun j : ℕ => fc (j + 1) * brk c n j)
      (∑' m : Fin d → ℤ, cl (ga c m) (ga c (m + n))) := by
  have h := sum_powers_modes hc hn
  have h1 := (hasSum_nat_add_iff' (f := fun J : ℕ => fc J * ∑' m : Fin d → ℤ,
    hJ (ga c m) (ga c (m + n)) J) 1).mpr h
  have h0 : fc 0 = 0 := by simp [fc]
  simp only [range_one, sum_singleton, h0, zero_mul, sub_zero] at h1
  have e : (fun j : ℕ => fc (j + 1) * brk c n j)
      = fun j : ℕ => fc (j + 1) * ∑' m : Fin d → ℤ, hJ (ga c m) (ga c (m + n)) (j + 1) := by
    funext j; rw [brk_eq hc n j]
  rw [e]; exact h1

end CTG.DensityResponseSum
