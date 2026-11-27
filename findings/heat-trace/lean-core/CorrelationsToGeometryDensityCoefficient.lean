/-
Sixty-fourth file: the coefficient of the density term of the node model and its limit `3 (aξ)²`.
Namespace `CTG.DensityCoefficient`; imports the compiled module of the fifty-fifth file; check with
`./check_density_coefficient.sh`.
Normalisations (flat unit torus `(ℝ/ℤ)^d`): the heat kernel `heatTorus d c` has Fourier coefficients `t_m = e^{−c|m|²}`,
`c = 2π²ξ²`, `a = 2π|n|`, `t_n = e^{−ξ²a²/2}`, `(aξ)² = 2c|n|²` (`aXi2`).  `cCoef d c n` is the coefficient of the
first-order local density response of `torus_density_response` (sixty-third file) divided by the normalisation of the
paper; `bR d c` is the constant of equation (9.16) (`eq:bRgraph`), `zetaP d = Σ_J f_J J^{1−d/2}` (`paper_normalisation`
states both in the variables of the paper).
`main_limit`, `lattice_sum_limit`: `(√c)^d Σ_m cl(t_m, t_{m+n}) → √π^d · zetaP d` as `c → 0⁺`, `d ≥ 2`, `n ≠ 0` (bounds by
Chebyshev and mediant inequalities, power series of `t/√(1−t)`, theta function bounds by Poisson summation, Tannery).
**`coefficient_limit`**: for `d ≥ 2` and `n ≠ 0`, `cCoef d c n / (bR d c · aXi2 d c n) → 3` as `c → 0⁺`, no hypothesis.
This confirms the statement `c/b_R → 3 (aξ)²` of the note after Proposition 9.8 on the flat unit torus, in the joint
limit `c → 0` at fixed `n` (continuum limit and `aξ → 0` together); `b_R` is the normalising constant of (9.16), not
the measured curvature coefficient.
NOT formalised: the Riemann sum at fixed `aξ` (the integral `I(a)` at finite `aξ`); the next order in `aξ`; the
divergence for `d = 1` (the statement is false there, as the paper says); the identification of the density response
with the derivative of the energy density beyond the sixty-third file; whether `b_R` is the true curvature coefficient.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryDensityResponseSum

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Filter Topology Finset
open CTG.SqrtSeries

noncomputable section
namespace CTG.DensityCoefficient

variable {d : ℕ}

/-! ### Lattice notation -/

/-- `|m|²` for `m ∈ ℤ^d`. -/
def nsq (m : Fin d → ℤ) : ℝ := ∑ i, ((m i : ℤ) : ℝ) ^ 2

/-- `t_m = exp(−c|m|²)` (definitionally the `ga c m` of the fifty-first file). -/
def gx (c : ℝ) (m : Fin d → ℤ) : ℝ := Real.exp (-c * nsq m)

lemma nsq_nonneg (m : Fin d → ℤ) : 0 ≤ nsq m := Finset.sum_nonneg fun i _ => sq_nonneg _

lemma nsq_zero : nsq (0 : Fin d → ℤ) = 0 := by simp [nsq]

lemma nsq_neg (m : Fin d → ℤ) : nsq (-m) = nsq m := by simp [nsq]

lemma nsq_ge_one {m : Fin d → ℤ} (hm : m ≠ 0) : 1 ≤ nsq m := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h; push_neg at h; exact hm (funext h)
  have h1 : (1 : ℝ) ≤ ((m i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (m i) ^ 2 := by
      have := Int.one_le_abs hi
      nlinarith [sq_abs (m i)]
    exact_mod_cast this
  have h2 : ((m i : ℤ) : ℝ) ^ 2 ≤ nsq m :=
    Finset.single_le_sum (f := fun j => ((m j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  linarith

lemma gx_pos (c : ℝ) (m : Fin d → ℤ) : 0 < gx c m := Real.exp_pos _

lemma gx_zero (c : ℝ) : gx c (0 : Fin d → ℤ) = 1 := by simp [gx, nsq_zero]

lemma gx_neg (c : ℝ) (m : Fin d → ℤ) : gx c (-m) = gx c m := by simp [gx, nsq_neg]

lemma gx_le_one {c : ℝ} (hc : 0 ≤ c) (m : Fin d → ℤ) : gx c m ≤ 1 := by
  unfold gx; apply Real.exp_le_one_iff.mpr; nlinarith [nsq_nonneg m]

lemma gx_le_exp {c : ℝ} (hc : 0 < c) {m : Fin d → ℤ} (hm : m ≠ 0) : gx c m ≤ Real.exp (-c) := by
  unfold gx; apply Real.exp_le_exp.mpr; nlinarith [nsq_ge_one hm]

lemma exp_neg_lt_one {c : ℝ} (hc : 0 < c) : Real.exp (-c) < 1 := by
  have := Real.exp_lt_exp.mpr (show -c < 0 by linarith); simpa using this

lemma gx_lt_one {c : ℝ} (hc : 0 < c) {m : Fin d → ℤ} (hm : m ≠ 0) : gx c m < 1 :=
  (gx_le_exp hc hm).trans_lt (exp_neg_lt_one hc)

lemma gx_pow (c : ℝ) (J : ℕ) (m : Fin d → ℤ) : gx c m ^ J = gx (J * c) m := by
  unfold gx; rw [← Real.exp_nat_mul]; congr 1; ring

lemma gx_anti {c c' : ℝ} (h : c ≤ c') (m : Fin d → ℤ) : gx c' m ≤ gx c m := by
  unfold gx; apply Real.exp_le_exp.mpr; nlinarith [nsq_nonneg m]

/-- Peter–Paul on the lattice: `|m+n|² ≤ (1+δ)|m|² + (1+1/δ)|n|²`. -/
lemma nsq_add_le (m n : Fin d → ℤ) {δ : ℝ} (hδ : 0 < δ) :
    nsq (m + n) ≤ (1 + δ) * nsq m + (1 + 1 / δ) * nsq n := by
  unfold nsq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add]
  have h : (1 + δ) * ((m i : ℤ) : ℝ) ^ 2 + (1 + 1 / δ) * ((n i : ℤ) : ℝ) ^ 2
      - (((m i : ℤ) : ℝ) + ((n i : ℤ) : ℝ)) ^ 2
      = (δ * ((m i : ℤ) : ℝ) - ((n i : ℤ) : ℝ)) ^ 2 / δ := by
    field_simp; ring
  have : 0 ≤ (δ * ((m i : ℤ) : ℝ) - ((n i : ℤ) : ℝ)) ^ 2 / δ := div_nonneg (sq_nonneg _) hδ.le
  linarith

/-! ### Theta functions -/

/-- `θ_d(s) = Σ_{m ∈ ℤ^d} e^{−s|m|²}`. -/
def theta (d : ℕ) (s : ℝ) : ℝ := ∑' m : Fin d → ℤ, gx s m

/-- `θ_d(s) − 1 = Σ_{m ≠ 0} e^{−s|m|²}`. -/
def thetaM (d : ℕ) (s : ℝ) : ℝ := ∑' m : Fin d → ℤ, if m = 0 then 0 else gx s m

/-- The three facts about `θ_d` used below (summability, the lower bound from Poisson summation and
the upper bound by comparison with the Gaussian integral).  They are proved WITHOUT hypothesis in
the final part of this file from `heatTorus_zero_ge` and `gauss_tsum_le` of the second file. -/
structure ThetaFacts (d : ℕ) : Prop where
  summ : ∀ s : ℝ, 0 < s → Summable fun m : Fin d → ℤ => gx s m
  low : ∀ s : ℝ, 0 < s → Real.sqrt (Real.pi / s) ^ d ≤ theta d s
  up : ∀ s : ℝ, 0 < s → theta d s ≤ (1 + Real.sqrt (Real.pi / s)) ^ d

section Theta
variable (hT : ThetaFacts d)
include hT

lemma ite_summable {s : ℝ} (hs : 0 < s) :
    Summable fun m : Fin d → ℤ => if m = 0 then 0 else gx s m :=
  Summable.of_nonneg_of_le (fun m => by split_ifs <;> simp [(gx_pos s m).le])
    (fun m => by split_ifs <;> simp [(gx_pos s m).le]) (hT.summ s hs)

lemma thetaM_eq {s : ℝ} (hs : 0 < s) : thetaM d s = theta d s - 1 := by
  unfold thetaM theta
  rw [(hT.summ s hs).tsum_eq_add_tsum_ite 0, gx_zero]; ring

lemma thetaM_nonneg (s : ℝ) : 0 ≤ thetaM d s :=
  tsum_nonneg fun m => by split_ifs <;> simp [(gx_pos s m).le]

lemma thetaM_le {s : ℝ} (hs : 0 < s) : thetaM d s ≤ Real.exp (-(s / 2)) * theta d (s / 2) := by
  unfold thetaM theta
  rw [← tsum_mul_left]
  refine hasSum_le (fun m => ?_) (ite_summable hT hs).hasSum
    ((hT.summ (s / 2) (half_pos hs)).mul_left _).hasSum
  by_cases hm : m = 0
  · rw [if_pos hm]; exact mul_nonneg (Real.exp_pos _).le (gx_pos _ _).le
  · rw [if_neg hm]
    unfold gx
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [nsq_ge_one hm]

/-- The uniform constant of the domination. -/
def Kc (d : ℕ) : ℝ := (d.factorial : ℝ) * Real.exp (Real.sqrt (2 * Real.pi) + 1 / 2)

/-- `(√s)^d (θ_d(s) − 1) ≤ K_d` for every `s > 0`. -/
lemma key_bound {s : ℝ} (hs : 0 < s) : Real.sqrt s ^ d * thetaM d s ≤ Kc d := by
  have h1 := thetaM_le hT hs
  have h2 := hT.up (s / 2) (half_pos hs)
  set y := Real.sqrt s with hydef
  set b := Real.sqrt (2 * Real.pi) with hbdef
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hys : y ^ 2 = s := Real.sq_sqrt hs.le
  have e : y * (1 + Real.sqrt (Real.pi / (s / 2))) = y + b := by
    rw [mul_add, mul_one, hydef, ← Real.sqrt_mul hs.le]
    congr 2; field_simp
  have hth : 0 ≤ theta d (s / 2) := (thetaM_nonneg hT (s/2)).trans
    (by rw [thetaM_eq hT (half_pos hs)]; linarith)
  have step1 : y ^ d * thetaM d s ≤ y ^ d * (Real.exp (-(s / 2)) * (1 + Real.sqrt (Real.pi / (s / 2))) ^ d) :=
    mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le))
      (pow_nonneg hy d)
  have step2 : y ^ d * (Real.exp (-(s / 2)) * (1 + Real.sqrt (Real.pi / (s / 2))) ^ d)
      = Real.exp (-(s / 2)) * (y + b) ^ d := by
    rw [← e, mul_pow]; ring
  have hfact : (y + b) ^ d ≤ (d.factorial : ℝ) * Real.exp (y + b) := by
    have := Real.pow_div_factorial_le_exp (y + b) (add_nonneg hy hb) d
    have hf : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
    rw [div_le_iff₀ hf] at this; linarith
  have hexp : Real.exp (-(s / 2)) * Real.exp (y + b) ≤ Real.exp (b + 1 / 2) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [sq_nonneg (y - 1)]
  calc y ^ d * thetaM d s ≤ Real.exp (-(s / 2)) * (y + b) ^ d := step1.trans step2.le
    _ ≤ Real.exp (-(s / 2)) * ((d.factorial : ℝ) * Real.exp (y + b)) :=
        mul_le_mul_of_nonneg_left hfact (Real.exp_pos _).le
    _ = (d.factorial : ℝ) * (Real.exp (-(s / 2)) * Real.exp (y + b)) := by ring
    _ ≤ Kc d := mul_le_mul_of_nonneg_left hexp (by positivity)

end Theta

/-! ### The function `g(t) = t/√(1−t)` and the pair function -/

/-- `g(t) = t/√(1−t)`. -/
def gq (t : ℝ) : ℝ := t / Real.sqrt (1 - t)

/-- `G(u,v) = (u+v)/(√(1−u)+√(1−v))`, the summand of the symmetrised lattice sum. -/
def Gp (u v : ℝ) : ℝ := (u + v) / (Real.sqrt (1 - u) + Real.sqrt (1 - v))

lemma gq_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ gq t := div_nonneg ht (Real.sqrt_nonneg _)

lemma Gp_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ Gp u v :=
  div_nonneg (add_nonneg hu hv) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

lemma gq_mono {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') (ht1 : t' < 1) : gq t ≤ gq t' :=
  div_le_div₀ (ht.trans htt) htt (Real.sqrt_pos.mpr (by linarith))
    (Real.sqrt_le_sqrt (by linarith))

lemma gq_le {t q : ℝ} (ht : 0 ≤ t) (htq : t ≤ q) (hq : q < 1) : gq t ≤ t / Real.sqrt (1 - q) :=
  div_le_div_of_nonneg_left ht (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (by linarith))

lemma gq_le_inv {t : ℝ} (ht1 : t ≤ 1) : gq t ≤ 1 / Real.sqrt (1 - t) := by
  unfold gq
  rcases (Real.sqrt_nonneg (1 - t)).eq_or_lt with h | h
  · rw [← h]; simp
  · exact div_le_div_of_nonneg_right ht1 h.le

lemma hJ_diag (u : ℝ) (J : ℕ) : hJ u u J = J * u ^ J := by
  unfold hJ
  rw [Finset.sum_congr rfl (g := fun _ => u ^ J) (fun p hp => by
    rw [← pow_add]; congr 1; have := Finset.mem_range.mp hp; omega)]
  simp

/-- `t/√(1−t) = Σ_J 2 f_J J t^J` on `[0,1)`. -/
lemma gq_hasSum {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    HasSum (fun J : ℕ => 2 * fc J * J * t ^ J) (gq t) := by
  have h := (mode_sum_eq h0 h1).mul_left 2
  have hw : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.mpr (by linarith)
  convert h using 1
  · funext J; rw [hJ_diag]; ring
  · unfold gq; field_simp

/-- Chebyshev: `G(u,v) ≤ (g(u)+g(v))/2`. -/
lemma Gp_le {u v : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) (hv : 0 ≤ v) (hv1 : v < 1) :
    Gp u v ≤ (gq u + gq v) / 2 := by
  have ha : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.mpr (by linarith)
  set a := Real.sqrt (1 - u)
  set b := Real.sqrt (1 - v)
  have key : 0 ≤ (b - a) * (u * b - v * a) := by
    rcases le_total u v with h | h
    · have hab : b ≤ a := Real.sqrt_le_sqrt (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by nlinarith)
    · have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
      exact mul_nonneg (by linarith) (by nlinarith)
  unfold Gp gq
  rw [div_add_div _ _ ha.ne' hb.ne', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [key, mul_pos ha hb]

/-- Mediant: `g(L) ≤ G(u,v)` if `0 ≤ L ≤ u, v < 1`. -/
lemma le_Gp {u v L : ℝ} (hL : 0 ≤ L) (hLu : L ≤ u) (hLv : L ≤ v) (hu1 : u < 1) (hv1 : v < 1) :
    gq L ≤ Gp u v := by
  have ha : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < Real.sqrt (1 - v) := Real.sqrt_pos.mpr (by linarith)
  have h1 : gq L ≤ u / Real.sqrt (1 - u) := gq_mono hL hLu hu1
  have h2 : gq L ≤ v / Real.sqrt (1 - v) := gq_mono hL hLv hv1
  rw [le_div_iff₀ ha] at h1
  rw [le_div_iff₀ hb] at h2
  unfold Gp
  rw [le_div_iff₀ (by positivity)]
  nlinarith


/-! ### Elementary facts -/

lemma fc_zero : fc 0 = 0 := by simp [fc]

lemma fc_one : fc 1 = 1 / 2 := by simp [fc]; norm_num

lemma fc_summable : Summable fc := by
  have h := (hasSum_one_sub_sqrt (s := 1) zero_le_one le_rfl).summable
  simpa using h

lemma fc_tsum : ∑' J, fc J = 1 := by
  have h := (hasSum_one_sub_sqrt (s := 1) zero_le_one le_rfl)
  simp at h; exact h.tsum_eq

lemma one_sub_exp_neg_ge {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hx1 : 0 < 1 + x := by linarith
  have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [le_div_iff₀ hx1]
    calc Real.exp (-x) * (1 + x) ≤ Real.exp (-x) * Real.exp x :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have e : 1 - 1 / (1 + x) = x / (1 + x) := by field_simp; ring
  linarith

lemma sqrt_tendsto_zero : Tendsto (fun c : ℝ => Real.sqrt c) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  simpa using this

/-! ### The lattice sums -/

/-- `h_{A,B}(m) = g(B e^{−A|m|²})` for `m ≠ 0` and `0` for `m = 0`. -/
def hf (A B : ℝ) (m : Fin d → ℤ) : ℝ := if m = 0 then 0 else gq (B * gx A m)

/-- The symmetrised lattice sum `I_torus = Σ_m G(t_m, t_{m+n})`. -/
def Ssum (d : ℕ) (c : ℝ) (n : Fin d → ℤ) : ℝ := ∑' m : Fin d → ℤ, Gp (gx c m) (gx c (m + n))

lemma hf_nonneg {A B : ℝ} (hB : 0 ≤ B) (m : Fin d → ℤ) : 0 ≤ hf A B m := by
  unfold hf; split_ifs
  · exact le_rfl
  · exact gq_nonneg (mul_nonneg hB (gx_pos A m).le)

section Lattice
variable (hT : ThetaFacts d)
include hT

lemma hf_summable {A B : ℝ} (hA : 0 < A) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    Summable (hf (d := d) A B) := by
  refine Summable.of_nonneg_of_le (hf_nonneg hB0) (fun m => ?_)
    ((hT.summ A hA).div_const (Real.sqrt (1 - Real.exp (-A))))
  unfold hf; split_ifs with hm
  · exact div_nonneg (gx_pos A m).le (Real.sqrt_nonneg _)
  · have hle : B * gx A m ≤ gx A m := mul_le_of_le_one_left (gx_pos A m).le hB1
    calc gq (B * gx A m) ≤ B * gx A m / Real.sqrt (1 - Real.exp (-A)) :=
          gq_le (mul_nonneg hB0 (gx_pos A m).le) (hle.trans (gx_le_exp hA hm)) (exp_neg_lt_one hA)
      _ ≤ gx A m / Real.sqrt (1 - Real.exp (-A)) :=
          div_le_div_of_nonneg_right hle (Real.sqrt_nonneg _)

/-- **Series in the powers:** `Σ_{m ≠ 0} g(B e^{−A|m|²}) = Σ_J 2 f_J J B^J (θ_d(JA) − 1)`. -/
theorem hf_series {A B : ℝ} (hA : 0 < A) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) :
    HasSum (fun J : ℕ => 2 * fc J * J * B ^ J * thetaM d (J * A)) (∑' m : Fin d → ℤ, hf A B m) := by
  let F : (Fin d → ℤ) × ℕ → ℝ := fun p =>
    if p.1 = 0 then 0 else 2 * fc p.2 * p.2 * (B * gx A p.1) ^ p.2
  have hF0 : 0 ≤ F := fun p => by
    show 0 ≤ (if p.1 = 0 then 0 else 2 * fc p.2 * p.2 * (B * gx A p.1) ^ p.2)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (fc_nonneg _)) (Nat.cast_nonneg _))
        (pow_nonneg (mul_nonneg hB0 (gx_pos A _).le) _)
  have hfib : ∀ m, HasSum (fun J => F (m, J)) (hf A B m) := by
    intro m
    by_cases hm : m = 0
    · simp only [F, hf, if_pos hm]; exact hasSum_zero
    · simp only [F, hf, if_neg hm]
      have hx0 : 0 ≤ B * gx A m := mul_nonneg hB0 (gx_pos A m).le
      have hx1 : B * gx A m < 1 :=
        (mul_le_of_le_one_left (gx_pos A m).le hB1).trans_lt (gx_lt_one hA hm)
      exact gq_hasSum hx0 hx1
  have hd : Summable F := by
    rw [summable_prod_of_nonneg hF0]
    refine ⟨fun m => (hfib m).summable, ?_⟩
    have : (fun m => ∑' J, F (m, J)) = hf A B := funext fun m => (hfib m).tsum_eq
    rw [this]; exact hf_summable hT hA hB0 hB1
  have h1 : HasSum (hf A B) (∑' p, F p) := hd.hasSum.prod_fiberwise hfib
  have hd' := hd.prod_symm
  have e : (∑' p : ℕ × (Fin d → ℤ), F p.swap) = ∑' p, F p := (Equiv.prodComm ℕ _).tsum_eq F
  have h2 : HasSum (fun J : ℕ => ∑' m, F (m, J)) (∑' m : Fin d → ℤ, hf A B m) := by
    have := hd'.hasSum.prod_fiberwise fun J => (hd'.prod_factor J).hasSum
    rw [h1.tsum_eq, ← e]
    exact this
  have hfun : (fun J : ℕ => ∑' m, F (m, J))
      = fun J : ℕ => 2 * fc J * J * B ^ J * thetaM d (J * A) := by
    funext J
    unfold thetaM
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [F]
    split_ifs
    · ring
    · rw [mul_pow, gx_pow]; ring
  rw [hfun] at h2
  exact h2

/-- Pointwise limit of one term of the series. -/
lemma theta_pt (hd : 1 ≤ d) {J : ℕ} (hJ : 1 ≤ J) (k : ℝ → ℝ) (hk1 : ∀ c, 0 < c → 1 ≤ k c)
    (hk : Tendsto k (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun c => Real.sqrt c ^ d * thetaM d (J * (c * k c))) (𝓝[>] 0)
      (𝓝 (Real.sqrt (Real.pi / J) ^ d)) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsqd : Tendsto (fun c : ℝ => Real.sqrt c ^ d) (𝓝[>] 0) (𝓝 0) := by
    have := sqrt_tendsto_zero.pow d; rwa [zero_pow (by omega)] at this
  have hfrac : Tendsto (fun c => Real.sqrt (Real.pi / (J * k c))) (𝓝[>] 0)
      (𝓝 (Real.sqrt (Real.pi / J))) := by
    have h1 : Tendsto (fun c => Real.pi / (J * k c)) (𝓝[>] 0) (𝓝 (Real.pi / (J * 1))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.mul hk) (by positivity)
    rw [mul_one] at h1
    exact (Real.continuous_sqrt.tendsto _).comp h1
  have hlow : Tendsto (fun c => Real.sqrt (Real.pi / (J * k c)) ^ d - Real.sqrt c ^ d) (𝓝[>] 0)
      (𝓝 (Real.sqrt (Real.pi / J) ^ d)) := by
    simpa using (hfrac.pow d).sub hsqd
  have hup : Tendsto (fun c => (Real.sqrt c + Real.sqrt (Real.pi / (J * k c))) ^ d
      - Real.sqrt c ^ d) (𝓝[>] 0) (𝓝 (Real.sqrt (Real.pi / J) ^ d)) := by
    simpa using ((sqrt_tendsto_zero.add hfrac).pow d).sub hsqd
  have hid : ∀ c : ℝ, 0 < c →
      Real.sqrt c * Real.sqrt (Real.pi / (J * (c * k c))) = Real.sqrt (Real.pi / (J * k c)) := by
    intro c hc
    have hk0 : 0 < k c := lt_of_lt_of_le one_pos (hk1 c hc)
    rw [← Real.sqrt_mul hc.le]; congr 1; field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : (0 : ℝ) < c := hc
    have hk0 : 0 < k c := lt_of_lt_of_le one_pos (hk1 c hc0)
    have hs : 0 < (J : ℝ) * (c * k c) := by positivity
    have hcd : 0 ≤ Real.sqrt c ^ d := pow_nonneg (Real.sqrt_nonneg _) d
    have h := mul_le_mul_of_nonneg_left (hT.low _ hs) hcd
    rw [← mul_pow, hid c hc0] at h
    rw [thetaM_eq hT hs]; linarith
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : (0 : ℝ) < c := hc
    have hk0 : 0 < k c := lt_of_lt_of_le one_pos (hk1 c hc0)
    have hs : 0 < (J : ℝ) * (c * k c) := by positivity
    have hcd : 0 ≤ Real.sqrt c ^ d := pow_nonneg (Real.sqrt_nonneg _) d
    have h := mul_le_mul_of_nonneg_left (hT.up _ hs) hcd
    rw [← mul_pow, mul_add, mul_one, hid c hc0] at h
    rw [thetaM_eq hT hs]; linarith

/-- Domination of the terms, uniformly in `c`. -/
lemma dom_bound (hd : 2 ≤ d) {c κ b : ℝ} (hc : 0 < c) (hκ : 1 ≤ κ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (J : ℕ) :
    0 ≤ Real.sqrt c ^ d * (2 * fc J * J * b ^ J * thetaM d (J * (c * κ))) ∧
    Real.sqrt c ^ d * (2 * fc J * J * b ^ J * thetaM d (J * (c * κ))) ≤ 2 * Kc d * fc J := by
  have hnn : 0 ≤ thetaM d (J * (c * κ)) := thetaM_nonneg hT _
  have hcd : 0 ≤ Real.sqrt c ^ d := pow_nonneg (Real.sqrt_nonneg _) d
  have hbJ0 : 0 ≤ b ^ J := pow_nonneg hb0 J
  have hbJ1 : b ^ J ≤ 1 := pow_le_one₀ hb0 hb1
  have hfc := fc_nonneg J
  have hJn : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  refine ⟨mul_nonneg hcd (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hfc) hJn)
    hbJ0) hnn), ?_⟩
  rcases Nat.eq_zero_or_pos J with h0 | hJ
  · subst h0; simp [fc_zero]
  · have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hcκ : 0 < c * κ := by nlinarith
    have hs : 0 < (J : ℝ) * (c * κ) := by positivity
    have key := key_bound hT hs
    have hsq : Real.sqrt ((J : ℝ) * (c * κ)) ^ d = Real.sqrt J ^ d * Real.sqrt (c * κ) ^ d := by
      rw [Real.sqrt_mul hJn, mul_pow]
    have hsJ : 1 ≤ Real.sqrt J := by
      have := Real.sqrt_le_sqrt hJ1; rwa [Real.sqrt_one] at this
    have hJd : (J : ℝ) ≤ Real.sqrt J ^ d := by
      have h2 : Real.sqrt J ^ 2 ≤ Real.sqrt J ^ d := pow_le_pow_right₀ hsJ hd
      rwa [Real.sq_sqrt hJn] at h2
    have hcκd : Real.sqrt c ^ d ≤ Real.sqrt (c * κ) ^ d :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by nlinarith)) d
    have hmain : (J : ℝ) * Real.sqrt c ^ d * thetaM d (J * (c * κ)) ≤ Kc d := by
      calc (J : ℝ) * Real.sqrt c ^ d * thetaM d (J * (c * κ))
          ≤ Real.sqrt J ^ d * Real.sqrt (c * κ) ^ d * thetaM d (J * (c * κ)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul hJd hcκd hcd (pow_nonneg (Real.sqrt_nonneg _) d))
              hnn
        _ = Real.sqrt ((J : ℝ) * (c * κ)) ^ d * thetaM d (J * (c * κ)) := by rw [hsq]
        _ ≤ Kc d := key
    have hm0 : 0 ≤ (J : ℝ) * Real.sqrt c ^ d * thetaM d (J * (c * κ)) :=
      mul_nonneg (mul_nonneg hJn hcd) hnn
    calc Real.sqrt c ^ d * (2 * fc J * J * b ^ J * thetaM d (J * (c * κ)))
        = (2 * fc J * b ^ J) * ((J : ℝ) * Real.sqrt c ^ d * thetaM d (J * (c * κ))) := by ring
      _ ≤ (2 * fc J * 1) * Kc d :=
          mul_le_mul (mul_le_mul_of_nonneg_left hbJ1 (by positivity)) hmain hm0 (by positivity)
      _ = 2 * Kc d * fc J := by ring

/-- The limit value `Σ_J 2 f_J J (π/J)^{d/2}`. -/
def Tlim (d : ℕ) : ℝ := ∑' J : ℕ, 2 * fc J * J * Real.sqrt (Real.pi / J) ^ d

/-- **Tannery step.** -/
theorem tannery_theta (hd : 2 ≤ d) (k B : ℝ → ℝ) (hk1 : ∀ c, 0 < c → 1 ≤ k c)
    (hk : Tendsto k (𝓝[>] 0) (𝓝 1)) (hB0 : ∀ c, 0 < c → 0 ≤ B c) (hB1 : ∀ c, 0 < c → B c ≤ 1)
    (hB : Tendsto B (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun c => ∑' J : ℕ, Real.sqrt c ^ d * (2 * fc J * J * B c ^ J * thetaM d (J * (c * k c))))
      (𝓝[>] 0) (𝓝 (Tlim d)) := by
  unfold Tlim
  refine tendsto_tsum_of_dominated_convergence (bound := fun J => 2 * Kc d * fc J)
    (fc_summable.mul_left _) (fun J => ?_) ?_
  · rcases Nat.eq_zero_or_pos J with h0 | hJ
    · subst h0; simp [fc_zero]
    · have hpt := theta_pt hT (by omega) hJ k hk1 hk
      have hBJ : Tendsto (fun c => B c ^ J) (𝓝[>] 0) (𝓝 1) := by simpa using hB.pow J
      have h3 := (hBJ.mul hpt).const_mul (2 * fc J * J)
      rw [one_mul] at h3
      have e : (fun c => Real.sqrt c ^ d * (2 * fc J * J * B c ^ J * thetaM d (J * (c * k c))))
          = fun c => 2 * fc J * J * (B c ^ J * (Real.sqrt c ^ d * thetaM d (J * (c * k c)))) := by
        funext c; ring
      rw [e]; exact h3
  · filter_upwards [self_mem_nhdsWithin] with c hc
    intro J
    have hc0 : (0 : ℝ) < c := hc
    obtain ⟨h1, h2⟩ := dom_bound hT hd hc0 (hk1 c hc0) (hB0 c hc0) (hB1 c hc0) J
    rw [Real.norm_eq_abs, abs_of_nonneg h1]; exact h2

end Lattice


/-! ### Upper and lower bounds of the lattice sum -/

lemma G_upper {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) (m : Fin d → ℤ) :
    Gp (gx c m) (gx c (m + n)) ≤ (hf c 1 m + hf c 1 (m + n)) / 2
      + ((Pi.single (0 : Fin d → ℤ) (2 / Real.sqrt (1 - gx c n)) : (Fin d → ℤ) → ℝ) m
        + (Pi.single (-n) (2 / Real.sqrt (1 - gx c n)) : (Fin d → ℤ) → ℝ) m) := by
  have hw : 0 < Real.sqrt (1 - gx c n) := Real.sqrt_pos.mpr (by linarith [gx_lt_one hc hn])
  have hh1 : 0 ≤ hf c 1 m := hf_nonneg zero_le_one m
  have hh2 : 0 ≤ hf c 1 (m + n) := hf_nonneg zero_le_one _
  have h2w : 0 ≤ 2 / Real.sqrt (1 - gx c n) := by positivity
  have htn : gx c n ≤ 1 := gx_le_one hc.le n
  by_cases hm0 : m = 0
  · subst hm0
    have hne : ¬ ((0 : Fin d → ℤ) = -n) := fun h => hn (by
      have := congrArg Neg.neg h; simpa using this.symm)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne]
    simp only [zero_add, gx_zero] at hh2 ⊢
    have : Gp 1 (gx c n) ≤ 2 / Real.sqrt (1 - gx c n) := by
      unfold Gp; rw [sub_self, Real.sqrt_zero, zero_add]
      exact div_le_div_of_nonneg_right (by linarith) hw.le
    linarith
  · by_cases hmn : m = -n
    · subst hmn
      rw [Pi.single_eq_of_ne hm0, Pi.single_eq_same]
      simp only [neg_add_cancel, gx_zero, gx_neg] at hh2 ⊢
      have : Gp (gx c n) 1 ≤ 2 / Real.sqrt (1 - gx c n) := by
        unfold Gp; rw [sub_self, Real.sqrt_zero, add_zero]
        exact div_le_div_of_nonneg_right (by linarith) hw.le
      linarith
    · have hmn' : m + n ≠ 0 := fun h => hmn (eq_neg_of_add_eq_zero_left h)
      rw [Pi.single_eq_of_ne hm0, Pi.single_eq_of_ne hmn]
      have e1 : hf c 1 m = gq (gx c m) := by unfold hf; rw [if_neg hm0, one_mul]
      have e2 : hf c 1 (m + n) = gq (gx c (m + n)) := by unfold hf; rw [if_neg hmn', one_mul]
      rw [e1, e2]
      have := Gp_le (gx_pos c m).le (gx_lt_one hc hm0) (gx_pos c _).le (gx_lt_one hc hmn')
      linarith

/-- The parameters of the lower bound: `A = c(1+√c)`, `B = e^{−(c+√c)|n|²}`. -/
def Alow (c : ℝ) : ℝ := c * (1 + Real.sqrt c)
def Blow (c : ℝ) (n : Fin d → ℤ) : ℝ := Real.exp (-((c + Real.sqrt c) * nsq n))

lemma Blow_le_one {c : ℝ} (hc : 0 < c) (n : Fin d → ℤ) : Blow c n ≤ 1 := by
  unfold Blow; apply Real.exp_le_one_iff.mpr
  have := Real.sqrt_nonneg c; nlinarith [nsq_nonneg n]

lemma G_lower {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) (m : Fin d → ℤ) :
    hf (Alow c) (Blow c n) m - (Pi.single (-n) (gq (Blow c n * gx (Alow c) n)) : (Fin d → ℤ) → ℝ) m
      ≤ Gp (gx c m) (gx c (m + n)) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hB0 : 0 ≤ Blow c n := (Real.exp_pos _).le
  have hG0 := Gp_nonneg (gx_pos c m).le (gx_pos c (m + n)).le
  have hq0 : 0 ≤ gq (Blow c n * gx (Alow c) n) := gq_nonneg (mul_nonneg hB0 (gx_pos _ n).le)
  by_cases hm0 : m = 0
  · subst hm0
    have hne : ¬ ((0 : Fin d → ℤ) = -n) := fun h => hn (by
      have := congrArg Neg.neg h; simpa using this.symm)
    unfold hf; rw [if_pos rfl, Pi.single_eq_of_ne hne]
    linarith
  · by_cases hmn : m = -n
    · subst hmn
      unfold hf; rw [if_neg hm0, Pi.single_eq_same, gx_neg]; linarith
    · have hmn' : m + n ≠ 0 := fun h => hmn (eq_neg_of_add_eq_zero_left h)
      unfold hf; rw [if_neg hm0, Pi.single_eq_of_ne hmn, sub_zero]
      refine le_Gp (mul_nonneg hB0 (gx_pos _ m).le) ?_ ?_ (gx_lt_one hc hm0) (gx_lt_one hc hmn')
      · calc Blow c n * gx (Alow c) m ≤ gx (Alow c) m :=
              mul_le_of_le_one_left (gx_pos _ m).le (Blow_le_one hc n)
          _ ≤ gx c m := gx_anti (by unfold Alow; nlinarith) m
      · unfold Blow gx Alow
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hpp := mul_le_mul_of_nonneg_left (nsq_add_le m n hsc) hc.le
        have e : c / Real.sqrt c = Real.sqrt c := by
          rw [div_eq_iff hsc.ne', Real.mul_self_sqrt hc.le]
        have e2 : c * (1 + 1 / Real.sqrt c) = c + Real.sqrt c := by
          rw [mul_add, mul_one, mul_one_div, e]
        rw [mul_add, ← mul_assoc, ← mul_assoc, e2] at hpp
        linarith

section Sums
variable (hT : ThetaFacts d)
include hT

lemma hf_shift_summable {c : ℝ} (hc : 0 < c) (n : Fin d → ℤ) :
    Summable fun m : Fin d → ℤ => hf c 1 (m + n) := by
  have h := (Equiv.addRight n).summable_iff.mpr (hf_summable hT hc zero_le_one le_rfl)
  simp only [Function.comp_def, Equiv.coe_addRight] at h
  exact h

lemma hf_shift_tsum (c : ℝ) (n : Fin d → ℤ) :
    ∑' m : Fin d → ℤ, hf c 1 (m + n) = ∑' m : Fin d → ℤ, hf c 1 m := by
  have h := (Equiv.addRight n).tsum_eq (hf c 1)
  simp only [Equiv.coe_addRight] at h
  exact h

lemma upper_rhs_hasSum {c : ℝ} (hc : 0 < c) (n : Fin d → ℤ) (w : ℝ) :
    HasSum (fun m : Fin d → ℤ => (hf c 1 m + hf c 1 (m + n)) / 2
        + ((Pi.single (0 : Fin d → ℤ) w : (Fin d → ℤ) → ℝ) m + (Pi.single (-n) w : (Fin d → ℤ) → ℝ) m))
      ((∑' m : Fin d → ℤ, hf c 1 m + ∑' m : Fin d → ℤ, hf c 1 (m + n)) / 2 + (w + w)) :=
  (((hf_summable hT hc zero_le_one le_rfl).hasSum.add (hf_shift_summable hT hc n).hasSum).div_const 2).add
    ((hasSum_pi_single (0 : Fin d → ℤ) w).add (hasSum_pi_single (-n) w))

lemma G_summable {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) :
    Summable fun m => Gp (gx c m) (gx c (m + n)) :=
  Summable.of_nonneg_of_le (fun m => Gp_nonneg (gx_pos c m).le (gx_pos c (m + n)).le)
    (fun m => G_upper hc hn m) (upper_rhs_hasSum hT hc n (2 / Real.sqrt (1 - gx c n))).summable

lemma Ssum_upper {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) :
    Ssum d c n ≤ (∑' m : Fin d → ℤ, hf c 1 m) + 4 / Real.sqrt (1 - gx c n) := by
  have h := hasSum_le (fun m => G_upper hc hn m) (G_summable hT hc hn).hasSum
    (upper_rhs_hasSum hT hc n (2 / Real.sqrt (1 - gx c n)))
  have e4 : 2 / Real.sqrt (1 - gx c n) + 2 / Real.sqrt (1 - gx c n) = 4 / Real.sqrt (1 - gx c n) := by ring
  unfold Ssum; rw [hf_shift_tsum hT, e4] at h; linarith

lemma Ssum_lower {c : ℝ} (hc : 0 < c) {n : Fin d → ℤ} (hn : n ≠ 0) :
    (∑' m : Fin d → ℤ, hf (Alow c) (Blow c n) m) - gq (Blow c n * gx (Alow c) n) ≤ Ssum d c n := by
  have hA : 0 < Alow c := by unfold Alow; have := Real.sqrt_nonneg c; positivity
  have hh := hf_summable hT hA (Real.exp_pos _).le (Blow_le_one hc n)
  have hR := hh.hasSum.sub (hasSum_pi_single (-n) (gq (Blow c n * gx (Alow c) n)))
  exact hasSum_le (fun m => G_lower hc hn m) hR (G_summable hT hc hn).hasSum

end Sums

/-! ### The two remainder terms -/

lemma rem_upper {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hd : 2 ≤ d) {n : Fin d → ℤ} (hn : n ≠ 0) :
    0 ≤ Real.sqrt c ^ d * (4 / Real.sqrt (1 - gx c n)) ∧
    Real.sqrt c ^ d * (4 / Real.sqrt (1 - gx c n)) ≤ 4 * Real.sqrt (c * (1 + c)) := by
  have hw : 0 < Real.sqrt (1 - gx c n) := Real.sqrt_pos.mpr (by linarith [gx_lt_one hc hn])
  have hcd : 0 ≤ Real.sqrt c ^ d := pow_nonneg (Real.sqrt_nonneg _) d
  refine ⟨mul_nonneg hcd (by positivity), ?_⟩
  have hsc1 : Real.sqrt c ≤ 1 := by
    have := Real.sqrt_le_sqrt hc1; rwa [Real.sqrt_one] at this
  have h1 : Real.sqrt c ^ d ≤ c := by
    have := pow_le_pow_of_le_one (Real.sqrt_nonneg c) hsc1 hd
    rwa [Real.sq_sqrt hc.le] at this
  have hy : 0 < c / (1 + c) := by positivity
  have h2 : Real.sqrt (c / (1 + c)) ≤ Real.sqrt (1 - gx c n) := by
    apply Real.sqrt_le_sqrt
    have := one_sub_exp_neg_ge hc.le
    have h3 : gx c n ≤ Real.exp (-c) := gx_le_exp hc hn
    linarith
  have h4 : 4 / Real.sqrt (1 - gx c n) ≤ 4 / Real.sqrt (c / (1 + c)) :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hy) h2
  have e : c * (4 / Real.sqrt (c / (1 + c))) = 4 * Real.sqrt (c * (1 + c)) := by
    have hsy : 0 < Real.sqrt (c / (1 + c)) := Real.sqrt_pos.mpr hy
    have hm : Real.sqrt (c * (1 + c)) * Real.sqrt (c / (1 + c)) = c := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show c * (1 + c) * (c / (1 + c)) = c ^ 2 by field_simp]
      exact Real.sqrt_sq hc.le
    rw [mul_div_assoc', div_eq_iff hsy.ne']
    nlinarith [hm]
  calc Real.sqrt c ^ d * (4 / Real.sqrt (1 - gx c n)) ≤ c * (4 / Real.sqrt (c / (1 + c))) :=
        mul_le_mul h1 h4 (by positivity) hc.le
    _ = 4 * Real.sqrt (c * (1 + c)) := e

lemma rem_lower {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hd : 1 ≤ d) {n : Fin d → ℤ} (hn : n ≠ 0) :
    0 ≤ Real.sqrt c ^ d * gq (Blow c n * gx (Alow c) n) ∧
    Real.sqrt c ^ d * gq (Blow c n * gx (Alow c) n)
      ≤ Real.sqrt (Real.sqrt c * (1 + Real.sqrt c)) := by
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hcd : 0 ≤ Real.sqrt c ^ d := pow_nonneg (Real.sqrt_nonneg _) d
  set x := Blow c n * gx (Alow c) n with hx
  have hx0 : 0 ≤ x := mul_nonneg (Real.exp_pos _).le (gx_pos _ _).le
  refine ⟨mul_nonneg hcd (gq_nonneg hx0), ?_⟩
  have hsc1 : Real.sqrt c ≤ 1 := by
    have := Real.sqrt_le_sqrt hc1; rwa [Real.sqrt_one] at this
  have hxe : x ≤ Real.exp (-Real.sqrt c) := by
    rw [hx]; unfold Blow gx Alow
    rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
    have hN := nsq_ge_one hn
    have h1 : Real.sqrt c ≤ (c + Real.sqrt c) * nsq n := by nlinarith
    have h2 : 0 ≤ c * (1 + Real.sqrt c) * nsq n := by
      have := nsq_nonneg n; positivity
    nlinarith
  have hy : 0 < Real.sqrt c / (1 + Real.sqrt c) := by positivity
  have hx1 : x < 1 := hxe.trans_lt (exp_neg_lt_one hsc)
  have h3 : Real.sqrt (Real.sqrt c / (1 + Real.sqrt c)) ≤ Real.sqrt (1 - x) := by
    apply Real.sqrt_le_sqrt
    have := one_sub_exp_neg_ge hsc.le
    linarith
  have h4 : gq x ≤ 1 / Real.sqrt (Real.sqrt c / (1 + Real.sqrt c)) :=
    (gq_le_inv hx1.le).trans (one_div_le_one_div_of_le (Real.sqrt_pos.mpr hy) h3)
  have h5 : Real.sqrt c ^ d ≤ Real.sqrt c := pow_le_of_le_one (Real.sqrt_nonneg c) hsc1 (by omega)
  have e : Real.sqrt c * (1 / Real.sqrt (Real.sqrt c / (1 + Real.sqrt c)))
      = Real.sqrt (Real.sqrt c * (1 + Real.sqrt c)) := by
    rw [mul_one_div, ← Real.sqrt_div' _ hy.le]
    congr 1
    have hs2 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
    field_simp
    nlinarith [hs2]
  calc Real.sqrt c ^ d * gq x ≤ Real.sqrt c * (1 / Real.sqrt (Real.sqrt c / (1 + Real.sqrt c))) :=
        mul_le_mul h5 h4 (gq_nonneg hx0) hsc.le
    _ = _ := e

/-! ### The main limit -/

/-- **Continuum limit of the lattice sum** (`d ≥ 2`, `n ≠ 0` fixed, `c → 0⁺`):
`(√c)^d Σ_m G(t_m, t_{m+n}) → Σ_J 2 f_J J (π/J)^{d/2}`. -/
theorem main_limit (hT : ThetaFacts d) (hd : 2 ≤ d) {n : Fin d → ℤ} (hn : n ≠ 0) :
    Tendsto (fun c => Real.sqrt c ^ d * Ssum d c n) (𝓝[>] 0) (𝓝 (Tlim d)) := by
  -- upper
  have hU0 := tannery_theta hT hd (fun _ => 1) (fun _ => 1) (fun _ _ => le_rfl) tendsto_const_nhds
    (fun _ _ => zero_le_one) (fun _ _ => le_rfl) tendsto_const_nhds
  simp only [one_pow, mul_one] at hU0
  have hb2 : Tendsto (fun c : ℝ => 4 * Real.sqrt (c * (1 + c))) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous fun c : ℝ => 4 * Real.sqrt (c * (1 + c)) := by fun_prop
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  have hU := hU0.add hb2
  rw [add_zero] at hU
  -- lower
  have hk : Tendsto (fun c : ℝ => 1 + Real.sqrt c) (𝓝[>] 0) (𝓝 1) := by
    simpa using sqrt_tendsto_zero.const_add 1
  have hB : Tendsto (fun c : ℝ => Blow c n) (𝓝[>] 0) (𝓝 1) := by
    have h : Continuous fun c : ℝ => Real.exp (-((c + Real.sqrt c) * nsq n)) := by fun_prop
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa [Blow] using this
  have hL0 := tannery_theta hT hd (fun c => 1 + Real.sqrt c) (fun c => Blow c n)
    (fun c _ => by have := Real.sqrt_nonneg c; linarith) hk (fun c _ => (Real.exp_pos _).le)
    (fun c hc => Blow_le_one hc n) hB
  have hb1 : Tendsto (fun c : ℝ => Real.sqrt (Real.sqrt c * (1 + Real.sqrt c))) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous fun c : ℝ => Real.sqrt (Real.sqrt c * (1 + Real.sqrt c)) := by fun_prop
    have := (h.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  have hL := hL0.sub hb1
  rw [sub_zero] at hL
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with c hc
    obtain ⟨hc0, hc1⟩ := hc
    have hA : 0 < Alow c := by unfold Alow; have := Real.sqrt_nonneg c; positivity
    have hs := (hf_series hT hA (Real.exp_pos _).le (Blow_le_one hc0 n)).tsum_eq
    have hcd : 0 ≤ Real.sqrt c ^ d := pow_nonneg (Real.sqrt_nonneg _) d
    have h1 := mul_le_mul_of_nonneg_left (Ssum_lower hT hc0 hn) hcd
    rw [mul_sub] at h1
    have h2 := (rem_lower hc0 hc1.le (by omega) hn).2
    have e : ∑' J : ℕ, 2 * fc J * J * Blow c n ^ J * thetaM d (J * (c * (1 + Real.sqrt c)))
        = ∑' m : Fin d → ℤ, hf (Alow c) (Blow c n) m := hs
    rw [tsum_mul_left, e]
    linarith
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with c hc
    obtain ⟨hc0, hc1⟩ := hc
    have hs := (hf_series hT hc0 zero_le_one le_rfl).tsum_eq
    have hcd : 0 ≤ Real.sqrt c ^ d := pow_nonneg (Real.sqrt_nonneg _) d
    have h1 := mul_le_mul_of_nonneg_left (Ssum_upper hT hc0 hn) hcd
    rw [mul_add] at h1
    have h2 := (rem_upper hc0 hc1.le hd hn).2
    simp only [one_pow, mul_one] at hs
    rw [tsum_mul_left, hs]
    linarith

/-! ### The coefficient `c(a)` and `b_R`; the limit `3 (aξ)²` -/

/-- `ζ_{d/2−1} = Σ_J f_J J^{1−d/2}` (the `ζ_{D/2−1}` of `eq:bRgraph`, written with `√J^d`). -/
def zetaP (d : ℕ) : ℝ := ∑' J : ℕ, fc J * J / Real.sqrt J ^ d

lemma zetaP_term_le (hd : 2 ≤ d) (J : ℕ) : fc J * J / Real.sqrt J ^ d ≤ fc J := by
  rcases Nat.eq_zero_or_pos J with h0 | hJ
  · subst h0; simp [fc_zero]
  · have hJ1 : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hJn : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hsJ : 1 ≤ Real.sqrt J := by
      have := Real.sqrt_le_sqrt hJ1; rwa [Real.sqrt_one] at this
    have hJd : (J : ℝ) ≤ Real.sqrt J ^ d := by
      have h2 : Real.sqrt J ^ 2 ≤ Real.sqrt J ^ d := pow_le_pow_right₀ hsJ hd
      rwa [Real.sq_sqrt hJn] at h2
    have hpos : 0 < Real.sqrt J ^ d := by positivity
    rw [div_le_iff₀ hpos]
    exact mul_le_mul_of_nonneg_left hJd (fc_nonneg J)

lemma zetaP_term_nonneg (J : ℕ) : 0 ≤ fc J * J / Real.sqrt J ^ d :=
  div_nonneg (mul_nonneg (fc_nonneg J) (Nat.cast_nonneg J)) (pow_nonneg (Real.sqrt_nonneg _) d)

lemma zetaP_summable (hd : 2 ≤ d) : Summable fun J : ℕ => fc J * J / Real.sqrt J ^ d :=
  Summable.of_nonneg_of_le zetaP_term_nonneg (zetaP_term_le hd) fc_summable

lemma zetaP_ge (hd : 2 ≤ d) : 1 / 2 ≤ zetaP d := by
  have h := (zetaP_summable hd).le_tsum 1 (fun J _ => zetaP_term_nonneg J)
  simpa [fc_one] using h

lemma Tlim_eq : Tlim d = 2 * Real.sqrt Real.pi ^ d * zetaP d := by
  unfold Tlim zetaP
  rw [← tsum_mul_left]
  refine tsum_congr fun J => ?_
  rw [Real.sqrt_div Real.pi_pos.le, div_pow]
  ring

/-- **The coefficient `c(a)` of the paper in lattice form**, symmetrised:
`α(a) I(a)/(√2 ξ a²)` with `α = ½(1−t_n)²`, `I = Σ_m G`, written in `c = 2π²ξ²`, `|n|² = a²/(4π²)`. -/
def cCoefS (d : ℕ) (c : ℝ) (n : Fin d → ℤ) : ℝ :=
  (1 - gx c n) ^ 2 * (Ssum d c n / 2) / (4 * Real.pi * Real.sqrt c * nsq n)

/-- **`b_R` of `eq:bRgraph`** in the variable `c = 2π²ξ²`. -/
def bR (d : ℕ) (c : ℝ) : ℝ := zetaP d * Real.sqrt c / (24 * Real.pi * Real.sqrt (c / Real.pi) ^ d)

/-- `(aξ)² = 2c|n|²`. -/
def aXi2 (d : ℕ) (c : ℝ) (n : Fin d → ℤ) : ℝ := 2 * c * nsq n

/-- The normalisations in the variables of the paper: `c = 2π²ξ²`, `a = 2π|n|`. -/
theorem paper_normalisation {ξ : ℝ} (hξ : 0 < ξ) (n : Fin d → ℤ) :
    cCoefS d (2 * Real.pi ^ 2 * ξ ^ 2) n
        = (1 / 2 * (1 - gx (2 * Real.pi ^ 2 * ξ ^ 2) n) ^ 2) * Ssum d (2 * Real.pi ^ 2 * ξ ^ 2) n
          / (Real.sqrt 2 * ξ * (2 * Real.pi * Real.sqrt (nsq n)) ^ 2) ∧
    bR d (2 * Real.pi ^ 2 * ξ ^ 2)
        = zetaP d * ξ / (12 * Real.sqrt 2 * Real.sqrt (2 * Real.pi * ξ ^ 2) ^ d) ∧
    aXi2 d (2 * Real.pi ^ 2 * ξ ^ 2) n = ((2 * Real.pi * Real.sqrt (nsq n)) * ξ) ^ 2 := by
  have hpi := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hN : Real.sqrt (nsq n) ^ 2 = nsq n := Real.sq_sqrt (nsq_nonneg n)
  have hc : Real.sqrt (2 * Real.pi ^ 2 * ξ ^ 2) = Real.sqrt 2 * Real.pi * ξ := by
    rw [show 2 * Real.pi ^ 2 * ξ ^ 2 = (Real.sqrt 2 * Real.pi * ξ) ^ 2 by
      rw [mul_pow, mul_pow, h22]]
    exact Real.sqrt_sq (by positivity)
  have hcp : (2 * Real.pi ^ 2 * ξ ^ 2) / Real.pi = 2 * Real.pi * ξ ^ 2 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold cCoefS; rw [hc, mul_pow, hN]
    rcases (nsq_nonneg n).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · field_simp; ring
  · unfold bR; rw [hc, hcp]
    have hq : 0 < Real.sqrt (2 * Real.pi * ξ ^ 2) ^ d := by positivity
    have hm2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    rw [div_eq_div_iff (by positivity) (by positivity)]
    linear_combination (12 * zetaP d * Real.pi * ξ * Real.sqrt (2 * Real.pi * ξ ^ 2) ^ d) * hm2
  · unfold aXi2; rw [mul_pow, mul_pow, hN]; ring

lemma ratio_alg {r t S N z p : ℝ} (hr : 0 < r) (hN : 0 < N) (hz : 0 < z) (hp : 0 < p) (d : ℕ) :
    (1 - t) ^ 2 * (S / 2) / (4 * p ^ 2 * r * N)
        / (z * r / (24 * p ^ 2 * (r / p) ^ d) * (2 * r ^ 2 * N))
      = 3 * ((1 - t) / (r ^ 2 * N)) ^ 2 * (r ^ d * S) / (2 * p ^ d * z) := by
  rw [div_pow]
  field_simp
  ring

lemma ratio_eq {c : ℝ} (hc : 0 < c) (hd : 2 ≤ d) {n : Fin d → ℤ} (hn : n ≠ 0) :
    cCoefS d c n / (bR d c * aXi2 d c n)
      = 3 * ((1 - gx c n) / (c * nsq n)) ^ 2 * (Real.sqrt c ^ d * Ssum d c n)
          / (2 * Real.sqrt Real.pi ^ d * zetaP d) := by
  have h := ratio_alg (t := gx c n) (S := Ssum d c n) (Real.sqrt_pos.mpr hc)
    (lt_of_lt_of_le one_pos (nsq_ge_one hn)) (lt_of_lt_of_le (by norm_num) (zetaP_ge hd))
    (Real.sqrt_pos.mpr Real.pi_pos) d
  rw [Real.sq_sqrt hc.le, Real.sq_sqrt Real.pi_pos.le, ← Real.sqrt_div hc.le] at h
  unfold cCoefS bR aXi2
  exact h

lemma quot_limit {N : ℝ} (hN : 0 < N) :
    Tendsto (fun c => (1 - Real.exp (-c * N)) / (c * N)) (𝓝[>] 0) (𝓝 1) := by
  have hlow : Tendsto (fun c : ℝ => 1 / (1 + c * N)) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun c : ℝ => 1 / (1 + c * N)) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop) (by simp)
    have := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : (0 : ℝ) < c := hc
    have hx : 0 < c * N := mul_pos hc0 hN
    have h := one_sub_exp_neg_ge hx.le
    rw [neg_mul]
    rw [le_div_iff₀ hx]
    calc 1 / (1 + c * N) * (c * N) = c * N / (1 + c * N) := by ring
      _ ≤ _ := h
  · filter_upwards [self_mem_nhdsWithin] with c hc
    have hc0 : (0 : ℝ) < c := hc
    have hx : 0 < c * N := mul_pos hc0 hN
    rw [div_le_one hx, neg_mul]
    linarith [Real.add_one_le_exp (-(c * N))]

/-- **The coefficient limit (lattice form):** `c(a)/(b_R (aξ)²) → 3` as `c → 0⁺` (i.e. `ξ → 0`, hence
`aξ → 0`) at fixed `n ≠ 0`, for `d ≥ 2`. -/
theorem ratio_limit (hT : ThetaFacts d) (hd : 2 ≤ d) {n : Fin d → ℤ} (hn : n ≠ 0) :
    Tendsto (fun c => cCoefS d c n / (bR d c * aXi2 d c n)) (𝓝[>] 0) (𝓝 3) := by
  have hN : 0 < nsq n := lt_of_lt_of_le one_pos (nsq_ge_one hn)
  have hq := quot_limit hN
  have hm := main_limit hT hd hn
  have hz : 0 < 2 * Real.sqrt Real.pi ^ d * zetaP d := by
    have := zetaP_ge hd; have := Real.sqrt_pos.mpr Real.pi_pos; positivity
  have h := (((hq.pow 2).const_mul 3).mul hm).div_const (2 * Real.sqrt Real.pi ^ d * zetaP d)
  have hz0 : zetaP d ≠ 0 := by linarith [zetaP_ge hd]
  have hv : 3 * 1 ^ 2 * Tlim d / (2 * Real.sqrt Real.pi ^ d * zetaP d) = 3 := by
    rw [Tlim_eq, div_eq_iff hz.ne']; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [ratio_eq hc hd hn]
  rfl

/-! ### Discharging `ThetaFacts`; the lattice form of `torus_density_response` -/

/-- `ThetaFacts d` holds WITHOUT hypothesis: summability from `ga_summable`, the lower bound
`θ_d(s) ≥ (π/s)^{d/2}` from Poisson summation (`heatTorus_zero_ge`), the upper bound from
`gauss_tsum_le` (second file). -/
theorem thetaFacts (d : ℕ) : ThetaFacts d where
  summ s hs := (CTG.DensityResponseCont.Local.ga_summable hs d).congr fun m =>
    abs_of_pos (gx_pos s m)
  low s hs := by
    have h := CTG.Reals.heatTorus_zero_ge hs d
    have e : theta d s = CTG.Reals.heatTorus d s 0 := by
      unfold theta CTG.Reals.heatTorus; rw [CTG.Reals.cosSeries_zero]; rfl
    have e2 : 1 / (s / Real.pi) ^ (1 / 2 : ℝ) = Real.sqrt (Real.pi / s) := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div hs.le, Real.sqrt_div Real.pi_pos.le, one_div_div]
    rw [e, ← e2]; exact h
  up s hs := CTG.Reals.gauss_tsum_le hs d

/-- **The coefficient `c(a)` in the form of `torus_density_response`:** the derivative there is
`(1 − t_n)² (Σ_m cl(t_m, t_{m+n})) Re χ_n`; `c(a) = ½ω_∞ · (that coefficient)/a²` with
`ω_∞ = √2/ξ`, i.e. the coefficient divided by `√2 ξ a² = 4π√c |n|²`. -/
def cCoef (d : ℕ) (c : ℝ) (n : Fin d → ℤ) : ℝ :=
  (1 - CTG.DensityResponseCont.Local.ga c n) ^ 2
    * (∑' m : Fin d → ℤ, CTG.DensityResponseSum.cl (CTG.DensityResponseCont.Local.ga c m)
        (CTG.DensityResponseCont.Local.ga c (m + n)))
    / (4 * Real.pi * Real.sqrt c * nsq n)

lemma cCoef_eq {c : ℝ} (hc : 0 < c) (n : Fin d → ℤ) : cCoef d c n = cCoefS d c n := by
  unfold cCoef cCoefS Ssum
  rw [CTG.DensityResponseSum.cl_symmetrised hc n]
  show _ = (1 - CTG.DensityResponseCont.Local.ga c n) ^ 2
    * ((∑' m : Fin d → ℤ, (CTG.DensityResponseCont.Local.ga c m
        + CTG.DensityResponseCont.Local.ga c (m + n))
        / (Real.sqrt (1 - CTG.DensityResponseCont.Local.ga c m)
          + Real.sqrt (1 - CTG.DensityResponseCont.Local.ga c (m + n)))) / 2) / _
  ring

/-- **Continuum limit of the lattice sum of `torus_density_response`** (`d ≥ 2`, fixed `n ≠ 0`):
`c^{d/2} Σ_m cl(t_m, t_{m+n}) → π^{d/2} ζ_{d/2−1}` as `c → 0⁺`. -/
theorem lattice_sum_limit (hd : 2 ≤ d) {n : Fin d → ℤ} (hn : n ≠ 0) :
    Tendsto (fun c => Real.sqrt c ^ d * ∑' m : Fin d → ℤ,
        CTG.DensityResponseSum.cl (CTG.DensityResponseCont.Local.ga c m)
          (CTG.DensityResponseCont.Local.ga c (m + n)))
      (𝓝[>] 0) (𝓝 (Real.sqrt Real.pi ^ d * zetaP d)) := by
  have h := (main_limit (thetaFacts d) hd hn).const_mul (1 / 2)
  rw [Tlim_eq] at h
  have hv : 1 / 2 * (2 * Real.sqrt Real.pi ^ d * zetaP d) = Real.sqrt Real.pi ^ d * zetaP d := by
    ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc0 : (0 : ℝ) < c := hc
  rw [CTG.DensityResponseSum.cl_symmetrised hc0 n]
  unfold Ssum
  show _ = Real.sqrt c ^ d * (1 / 2 * ∑' m : Fin d → ℤ, Gp (gx c m) (gx c (m + n)))
  ring

/-- **The coefficient limit of the note after Proposition 9.8, lattice form:**
`c(a)/(b_R (aξ)²) → 3` as `c = 2π²ξ² → 0⁺` at fixed `n ≠ 0` (so `aξ = 2π|n|ξ → 0`), `d ≥ 2`;
`b_R` as in `eq:bRgraph`. No hypothesis. -/
theorem coefficient_limit (hd : 2 ≤ d) {n : Fin d → ℤ} (hn : n ≠ 0) :
    Tendsto (fun c => cCoef d c n / (bR d c * aXi2 d c n)) (𝓝[>] 0) (𝓝 3) := by
  refine (ratio_limit (thetaFacts d) hd hn).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  rw [cCoef_eq hc]

end CTG.DensityCoefficient
