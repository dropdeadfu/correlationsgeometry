/-
Sixty-third file: exchange of the derivative in the density with the sum over the powers for INTEGRAL KERNELS, by a
Doeblin argument on the kernels (no spectral theory of operators), and the local density response of the heat kernel
on the flat torus summed over the powers WITHOUT hypothesis.
Namespaces `CTG.DoeblinKernel`, `CTG.DoeblinKernel.Torus`; imports Mathlib and the compiled modules of the
forty-eighth, fifty-seventh and fifty-fifth files; check with `./check_density_response_kernel.sh`.
Stage 1 (`DHyp`: symmetric bounded kernel `S`, `∫ S(x,y) r(y) dy = r(x)` with `r` bounded above and below, `∫ r² = 1`,
minorisation `S ≥ c r⊗r`, `0 < c ≤ 1/2`): `DHyp.decomp` (`S^{(j)} = r⊗r + R^{(j)}`), `DHyp.geom_weighted`,
`DHyp.geom_sup` (`|R^{(j)}| ≤ C (1−c)^j`); the contraction uses the orthogonality `∫ r(x) R(x,y) dx = 0` (Fubini).
Stage 2 (`FHyp`: Stage 1 uniformly on a ball in `ε`, with bounded measurable derivatives): `Dk_geom`
(`|d/dε R_ε^{(j)}| ≤ (j+1) C (1−c)^j`), `FHyp.deriv_sum_kernels`: the series of the termwise derivatives is summable
and is the derivative at `0` of `ε ↦ Σ_j f_{j+1} S_ε^{(j)}(x,x)` (`f` the coefficients of `1 − √(1−s)`).
Stage 3 (frame `Hyp` of the forty-third file with HYPOTHESIS `κhom` of a homogeneous background, and in addition: `K`
symmetric, `K ≥ kmin > 0`, `μ(E) > 0`): `dHyp3`, `fHyp3`, `density_exchange`.
Stage 4: `heat_min` (positive lower bound of the heat kernel on the compact torus), **`torus_density_response`**: for
`c > 0`, `n ≠ 0`, `n⁰ > 0`, every `x`, `d/dε Σ_j f_{j+1} S_ε^{(j)}(x,x)|₀ = (1 − t_n)² (Σ_m cl(t_m, t_{m+n})) Re χ_n(x)`,
`t_m = exp(−c|m|²)`, no further hypothesis.  This is the derivative of the energy density of the node model with
respect to the density, at first order, as the lattice form of `α(a) I(a)` of the note after Proposition 9.8.
NOT formalised: second-order remainders; kernels without a positive lower bound; the graph without self-loops; the
trace `∫ u_ε`; the passage from the lattice sum to the continuum integral, the coefficient `c(a)` and its limit
`3(aξ)²`; the constants are explicit but not evaluated.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import Mathlib
import CorrelationsToGeometryDensityResponseTrace
import CorrelationsToGeometryDensityResponseExchange
import CorrelationsToGeometryDensityResponseSum

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Metric Function

namespace CTG.DoeblinKernel

open CTG.DensityResponseCont CTG.DensityResponseCont.Trace CTG.SqrtSeries

variable {E : Type*} [MeasurableSpace E]

/-- Composition of two kernels. -/
noncomputable def kmul (μ : Measure E) (A B : E → E → ℝ) (x z : E) : ℝ := ∫ y, A x y * B y z ∂μ

/-- A kernel is good if it is jointly measurable and bounded. -/
def Good (A : E → E → ℝ) : Prop := Measurable (uncurry A) ∧ ∃ M, ∀ x y, |A x y| ≤ M

/-- Iterated left composition `L_0 X = X`, `L_{p+1} X = R ∘ L_p X`. -/
noncomputable def Lp (μ : Measure E) (R X : E → E → ℝ) : ℕ → E → E → ℝ
  | 0 => X
  | p + 1 => kmul μ R (Lp μ R X p)

section Generic

variable (μ : Measure E) [IsFiniteMeasure μ]

lemma Good.row {A : E → E → ℝ} (hA : Good A) (x : E) : Measurable (A x) :=
  hA.1.comp measurable_prodMk_left

lemma Good.col {A : E → E → ℝ} (hA : Good A) (z : E) : Measurable (fun y => A y z) :=
  hA.1.comp (measurable_id.prodMk measurable_const)

lemma Good.intg {A B : E → E → ℝ} (hA : Good A) (hB : Good B) (x z : E) :
    Integrable (fun y => A x y * B y z) μ := by
  obtain ⟨a, ha⟩ := hA.2
  obtain ⟨b, hb⟩ := hB.2
  refine integrable_bdd μ ((hA.row x).mul (hB.col z)) (M := a * b) fun y => ?_
  rw [abs_mul]
  exact mul_le_mul (ha x y) (hb y z) (abs_nonneg _) ((abs_nonneg _).trans (ha x y))

lemma kmul_bdd {A B : E → E → ℝ} {a b : ℝ} (hA : ∀ x y, |A x y| ≤ a) (hB : ∀ x y, |B x y| ≤ b)
    (x z : E) : |kmul μ A B x z| ≤ a * b * μ.real Set.univ := by
  refine int_bound μ (fun y => ?_)
  rw [abs_mul]
  exact mul_le_mul (hA x y) (hB y z) (abs_nonneg _) ((abs_nonneg _).trans (hA x y))

lemma Good.kmul {A B : E → E → ℝ} (hA : Good A) (hB : Good B) : Good (kmul μ A B) := by
  refine ⟨meas_param μ _ ((hA.1.comp (measurable_fst.fst.prodMk measurable_snd)).mul
      (hB.1.comp (measurable_snd.prodMk measurable_fst.snd))), ?_⟩
  obtain ⟨a, ha⟩ := hA.2
  obtain ⟨b, hb⟩ := hB.2
  exact ⟨_, kmul_bdd μ ha hb⟩

lemma Good.add {A B : E → E → ℝ} (hA : Good A) (hB : Good B) : Good (fun x y => A x y + B x y) := by
  refine ⟨hA.1.add hB.1, ?_⟩
  obtain ⟨a, ha⟩ := hA.2
  obtain ⟨b, hb⟩ := hB.2
  exact ⟨a + b, fun x y => (abs_add_le _ _).trans (add_le_add (ha x y) (hb x y))⟩

lemma Good.Lp {R X : E → E → ℝ} (hR : Good R) (hX : Good X) : ∀ p, Good (Lp μ R X p)
  | 0 => hX
  | p + 1 => hR.kmul μ (Good.Lp hR hX p)

lemma kpow_eq_Lp (R : E → E → ℝ) : ∀ j, kpow μ R j = Lp μ R R j
  | 0 => rfl
  | j + 1 => by
    show (fun x z => ∫ y, R x y * kpow μ R j y z ∂μ) = kmul μ R (Lp μ R R j)
    rw [kpow_eq_Lp R j]; rfl

lemma Good.kpow {R : E → E → ℝ} (hR : Good R) (j : ℕ) : Good (kpow μ R j) := by
  rw [kpow_eq_Lp]; exact hR.Lp μ hR j

end Generic

/-! ## Stage 1: Doeblin decomposition of the iterated kernels -/

/-- Hypotheses of the Doeblin argument for one kernel `S` with top eigenfunction `r`. -/
structure DHyp (μ : Measure E) (S : E → E → ℝ) (r : E → ℝ) (c BS rlo rhi : ℝ) : Prop where
  Sm : Measurable (uncurry S)
  rm : Measurable r
  Ssym : ∀ x y, S x y = S y x
  SB : ∀ x y, |S x y| ≤ BS
  rlo0 : 0 < rlo
  rlo_le : ∀ x, rlo ≤ r x
  r_le : ∀ x, r x ≤ rhi
  eig : ∀ x, ∫ y, S x y * r y ∂μ = r x
  nrm : ∫ y, r y * r y ∂μ = 1
  c0 : 0 < c
  c_le : c ≤ 1 / 2
  /-- Minorisation (Doeblin condition). -/
  minor : ∀ x y, c * (r x * r y) ≤ S x y

/-- `R = S − r ⊗ r`. -/
def Rk (S : E → E → ℝ) (r : E → ℝ) (x y : E) : ℝ := S x y - r x * r y

/-- The constant `K0 = (BS + rhi²) μ(E)/rlo`. -/
noncomputable def K0c (μ : Measure E) (BS rlo rhi : ℝ) : ℝ := (BS + rhi * rhi) * μ.real Set.univ / rlo

/-- The constant `Λ = 1 + 2 K0 rhi`. -/
noncomputable def Λc (μ : Measure E) (BS rlo rhi : ℝ) : ℝ := 1 + 2 * K0c μ BS rlo rhi * rhi

section Stage1

variable {μ : Measure E} [IsFiniteMeasure μ] {S : E → E → ℝ} {r : E → ℝ} {c BS rlo rhi : ℝ}
  (h : DHyp μ S r c BS rlo rhi)
include h

lemma DHyp.r_pos (x : E) : 0 < r x := h.rlo0.trans_le (h.rlo_le x)

lemma DHyp.abs_r (x : E) : |r x| ≤ rhi := by rw [abs_of_pos (h.r_pos x)]; exact h.r_le x

lemma DHyp.rhi0 (x : E) : 0 ≤ rhi := (h.r_pos x).le.trans (h.r_le x)

lemma DHyp.BS0 (x : E) : 0 ≤ BS := (abs_nonneg _).trans (h.SB x x)

lemma DHyp.BR0 (x : E) : 0 ≤ BS + rhi * rhi := by
  have := h.BS0 x; have := h.rhi0 x; positivity

lemma DHyp.K00 (x : E) : 0 ≤ K0c μ BS rlo rhi := by
  unfold K0c; have := h.BR0 x; have := h.rlo0.le; positivity

lemma DHyp.Λ1 (x : E) : 1 ≤ Λc μ BS rlo rhi := by
  unfold Λc; have := h.K00 x; have := h.rhi0 x; nlinarith

lemma DHyp.Rk_bdd (x y : E) : |Rk S r x y| ≤ BS + rhi * rhi := by
  unfold Rk
  refine (abs_sub _ _).trans (add_le_add (h.SB x y) ?_)
  rw [abs_mul]
  exact mul_le_mul (h.abs_r x) (h.abs_r y) (abs_nonneg _) (h.rhi0 x)

lemma DHyp.goodS : Good S := ⟨h.Sm, BS, h.SB⟩

lemma DHyp.goodR : Good (Rk S r) :=
  ⟨h.Sm.sub ((h.rm.comp measurable_fst).mul (h.rm.comp measurable_snd)), _, h.Rk_bdd⟩

lemma DHyp.intg_r (f : E → ℝ) (hf : Measurable f) (M : ℝ) (hM : ∀ y, |f y| ≤ M) :
    Integrable (fun y => r y * f y) μ := by
  refine integrable_bdd μ (h.rm.mul hf) (M := rhi * M) fun y => ?_
  rw [abs_mul]
  exact mul_le_mul (h.abs_r y) (hM y) (abs_nonneg _) (h.rhi0 y)

/-- The columns of `R` are orthogonal to `r`. -/
lemma DHyp.col_zero (y : E) : ∫ x, r x * Rk S r x y ∂μ = 0 := by
  have e : (fun x => r x * Rk S r x y) = fun x => S y x * r x - r y * (r x * r x) := by
    funext x; unfold Rk; rw [h.Ssym x y]; ring
  have i1 : Integrable (fun x => S y x * r x) μ := by
    have := h.intg_r (S y) (h.goodS.row y) BS (h.SB y)
    simpa [mul_comm] using this
  have i2 : Integrable (fun x => r x * r x) μ := h.intg_r r h.rm rhi h.abs_r
  rw [e, integral_sub i1 (i2.const_mul _), integral_const_mul, h.eig, h.nrm]
  ring

/-- `⟨r, R g⟩ = 0` for every bounded measurable `g` (the only Fubini step). -/
lemma DHyp.col_comp (g : E → ℝ) (hg : Measurable g) (M : ℝ) (hgM : ∀ y, |g y| ≤ M) :
    ∫ x, r x * (∫ y, Rk S r x y * g y ∂μ) ∂μ = 0 := by
  have e1 : (fun x => r x * ∫ y, Rk S r x y * g y ∂μ) =
      fun x => ∫ y, r x * Rk S r x y * g y ∂μ := by
    funext x; rw [← integral_const_mul]; congr 1; funext y; ring
  have hmeas : Measurable (uncurry fun x y => r x * Rk S r x y * g y) :=
    ((h.rm.comp measurable_fst).mul h.goodR.1).mul (hg.comp measurable_snd)
  rw [e1, swap_bdd μ (fun x y => r x * Rk S r x y * g y) hmeas
    (M := rhi * (BS + rhi * rhi) * M) fun x y => ?_]
  · have e2 : ∀ y, ∫ x, r x * Rk S r x y * g y ∂μ = (∫ x, r x * Rk S r x y ∂μ) * g y :=
      fun y => integral_mul_const _ _
    simp_rw [e2, h.col_zero, zero_mul, integral_zero]
  · rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (h.abs_r x) (h.Rk_bdd x y) (abs_nonneg _) (h.rhi0 x)) (hgM y)
      (abs_nonneg _) (mul_nonneg (h.rhi0 x) (h.BR0 x))

/-- **Weighted contraction.** If `|g| ≤ M r` and `⟨r, g⟩ = 0`, then `|R g| ≤ (1−c) M r`. -/
lemma DHyp.contr (g : E → ℝ) (hg : Measurable g) (M : ℝ) (hgM : ∀ y, |g y| ≤ M * r y)
    (horth : ∫ y, r y * g y ∂μ = 0) (x : E) :
    |∫ y, Rk S r x y * g y ∂μ| ≤ (1 - c) * M * r x := by
  have hM0 : 0 ≤ M := by
    have h1 := (abs_nonneg (g x)).trans (hgM x)
    have h2 := h.r_pos x
    by_contra hn; push Not at hn; nlinarith
  have hgb : ∀ y, |g y| ≤ M * rhi := fun y =>
    (hgM y).trans (mul_le_mul_of_nonneg_left (h.r_le y) hM0)
  set T : E → ℝ := fun y => S x y - c * (r x * r y) with hT
  have hTm : Measurable T := (h.goodS.row x).sub (measurable_const.mul (measurable_const.mul h.rm))
  have hT0 : ∀ y, 0 ≤ T y := fun y => by simp only [hT]; linarith [h.minor x y]
  have hTb : ∀ y, |T y| ≤ BS + c * (rhi * rhi) := fun y => by
    refine (abs_sub _ _).trans (add_le_add (h.SB x y) ?_)
    rw [abs_mul, abs_mul, abs_of_pos h.c0]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (h.abs_r x) (h.abs_r y) (abs_nonneg _) (h.rhi0 x))
      h.c0.le
  have iTg : Integrable (fun y => T y * g y) μ := by
    refine integrable_bdd μ (hTm.mul hg) (M := (BS + c * (rhi * rhi)) * (M * rhi)) fun y => ?_
    rw [abs_mul]; exact mul_le_mul (hTb y) (hgb y) (abs_nonneg _) ((abs_nonneg _).trans (hTb y))
  have irg : Integrable (fun y => r y * g y) μ := h.intg_r g hg _ hgb
  have e : (fun y => Rk S r x y * g y) = fun y => T y * g y - ((1 - c) * r x) * (r y * g y) := by
    funext y; simp only [hT, Rk]; ring
  rw [e, integral_sub iTg (irg.const_mul _), integral_const_mul, horth, mul_zero, sub_zero]
  have iSr : Integrable (fun y => S x y * r y) μ := by
    have := h.intg_r (S x) (h.goodS.row x) BS (h.SB x)
    simpa [mul_comm] using this
  have irr : Integrable (fun y => r y * r y) μ := h.intg_r r h.rm rhi h.abs_r
  have iTr : Integrable (fun y => T y * (M * r y)) μ := by
    have e3 : (fun y => T y * (M * r y)) = fun y => M * (S x y * r y) - (M * c * r x) * (r y * r y) := by
      funext y; simp only [hT]; ring
    rw [e3]; exact (iSr.const_mul _).sub (irr.const_mul _)
  calc |∫ y, T y * g y ∂μ| ≤ ∫ y, |T y * g y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ y, T y * (M * r y) ∂μ := by
        refine integral_mono iTg.abs iTr fun y => ?_
        rw [abs_mul, abs_of_nonneg (hT0 y)]
        exact mul_le_mul_of_nonneg_left (hgM y) (hT0 y)
    _ = M * ∫ y, S x y * r y ∂μ - (M * c * r x) * ∫ y, r y * r y ∂μ := by
        have e3 : (fun y => T y * (M * r y)) =
            fun y => M * (S x y * r y) - (M * c * r x) * (r y * r y) := by
          funext y; simp only [hT]; ring
        rw [e3, integral_sub (iSr.const_mul _) (irr.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = (1 - c) * M * r x := by rw [h.eig, h.nrm]; ring

/-- The columns of `L_{p+1} X` are orthogonal to `r`. -/
lemma DHyp.Lp_col {X : E → E → ℝ} (hX : Good X) (p : ℕ) (z : E) :
    ∫ x, r x * Lp μ (Rk S r) X (p + 1) x z ∂μ = 0 := by
  obtain ⟨M, hM⟩ := (h.goodR.Lp μ hX p).2
  exact h.col_comp (fun y => Lp μ (Rk S r) X p y z) ((h.goodR.Lp μ hX p).col z) M (fun y => hM y z)

/-- **Geometric decay in the weighted norm**: `|L_{p+1} X(x,z)| ≤ (1−c)^p K0 b r(x)`. -/
lemma DHyp.Lp_weighted {X : E → E → ℝ} (hX : Good X) {b : ℝ} (hXb : ∀ x y, |X x y| ≤ b) :
    ∀ p x z, |Lp μ (Rk S r) X (p + 1) x z| ≤ (1 - c) ^ p * (K0c μ BS rlo rhi * b) * r x
  | 0, x, z => by
    show |kmul μ (Rk S r) X x z| ≤ _
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hXb x x)
    refine (kmul_bdd μ h.Rk_bdd hXb x z).trans ?_
    have hK : (BS + rhi * rhi) * b * μ.real Set.univ = K0c μ BS rlo rhi * b * rlo := by
      unfold K0c; field_simp [h.rlo0.ne']
    rw [hK, pow_zero, one_mul]
    exact mul_le_mul_of_nonneg_left (h.rlo_le x) (mul_nonneg (h.K00 x) hb0)
  | p + 1, x, z => by
    show |∫ y, Rk S r x y * Lp μ (Rk S r) X (p + 1) y z ∂μ| ≤ _
    have ih := DHyp.Lp_weighted hX hXb p
    refine (h.contr (fun y => Lp μ (Rk S r) X (p + 1) y z) ((h.goodR.Lp μ hX (p + 1)).col z)
      ((1 - c) ^ p * (K0c μ BS rlo rhi * b)) (fun y => ih y z) (h.Lp_col hX p z) x).trans
      (le_of_eq ?_)
    ring

/-- Sup form: `|L_p X| ≤ b Λ (1−c)^p` for every `p`. -/
lemma DHyp.Lp_sup {X : E → E → ℝ} (hX : Good X) {b : ℝ} (hXb : ∀ x y, |X x y| ≤ b) :
    ∀ p x z, |Lp μ (Rk S r) X p x z| ≤ b * Λc μ BS rlo rhi * (1 - c) ^ p
  | 0, x, z => by
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hXb x x)
    simp only [pow_zero, mul_one]
    exact (hXb x z).trans (le_mul_of_one_le_right hb0 (h.Λ1 x))
  | p + 1, x, z => by
    have hb0 : 0 ≤ b := (abs_nonneg _).trans (hXb x x)
    have hK := h.K00 x
    have hρ0 : 0 ≤ (1 - c) ^ p := pow_nonneg (by linarith [h.c_le]) p
    have h1 := h.Lp_weighted hX hXb p x z
    have h2 : (1 - c) ^ p * (K0c μ BS rlo rhi * b) * r x ≤ (1 - c) ^ p * (K0c μ BS rlo rhi * b) * rhi :=
      mul_le_mul_of_nonneg_left (h.r_le x) (mul_nonneg hρ0 (mul_nonneg hK hb0))
    have h3 : (1 - c) ^ p ≤ 2 * (1 - c) ^ (p + 1) := by
      rw [pow_succ]; nlinarith [h.c_le]
    refine h1.trans (h2.trans ?_)
    unfold Λc
    have hr := h.rhi0 x
    have h4 : 0 ≤ K0c μ BS rlo rhi * b * rhi := mul_nonneg (mul_nonneg hK hb0) hr
    have h5 : 0 ≤ b * (1 - c) ^ (p + 1) := mul_nonneg hb0 (pow_nonneg (by linarith [h.c_le]) _)
    nlinarith

/-- The columns of all iterated kernels of `R` are orthogonal to `r`. -/
lemma DHyp.kpow_col : ∀ (j : ℕ) (y : E), ∫ x, r x * kpow μ (Rk S r) j x y ∂μ = 0
  | 0, y => h.col_zero y
  | j + 1, y => by rw [kpow_eq_Lp]; exact h.Lp_col h.goodR j y

/-- **Stage 1, decomposition.** `S^{(j)}(x,y) = r(x) r(y) + R^{(j)}(x,y)` for every `j`
(`kpow j` has `j+1` factors). -/
theorem DHyp.decomp : ∀ (j : ℕ) (x y : E), kpow μ S j x y = r x * r y + kpow μ (Rk S r) j x y
  | 0, x, y => by show S x y = r x * r y + Rk S r x y; unfold Rk; ring
  | j + 1, x, y => by
    show ∫ z, S x z * kpow μ S j z y ∂μ = r x * r y + ∫ z, Rk S r x z * kpow μ (Rk S r) j z y ∂μ
    have ih := DHyp.decomp j
    have gK := h.goodR.kpow μ j
    have iSK : Integrable (fun z => S x z * kpow μ (Rk S r) j z y) μ := h.goodS.intg μ gK x y
    have iSr : Integrable (fun z => S x z * r z) μ := by
      have := h.intg_r (S x) (h.goodS.row x) BS (h.SB x)
      simpa [mul_comm] using this
    obtain ⟨MK, hMK⟩ := gK.2
    have irK : Integrable (fun z => r z * kpow μ (Rk S r) j z y) μ :=
      h.intg_r _ (gK.col y) MK (fun z => hMK z y)
    have e1 : (fun z => S x z * kpow μ S j z y) =
        fun z => (S x z * r z) * r y + S x z * kpow μ (Rk S r) j z y := by
      funext z; rw [ih z y]; ring
    have e2 : (fun z => Rk S r x z * kpow μ (Rk S r) j z y) =
        fun z => S x z * kpow μ (Rk S r) j z y - r x * (r z * kpow μ (Rk S r) j z y) := by
      funext z; unfold Rk; ring
    rw [e1, e2, integral_add (iSr.mul_const _) iSK, integral_mul_const, h.eig,
      integral_sub iSK (irK.const_mul _), integral_const_mul, h.kpow_col j y]
    ring

/-- **Stage 1, geometric bound, weighted form.** `|R^{(j+1)}(x,y)| ≤ (1−c)^j K0 (BS+rhi²) r(x)`. -/
theorem DHyp.geom_weighted (j : ℕ) (x y : E) :
    |kpow μ (Rk S r) (j + 1) x y| ≤ (1 - c) ^ j * (K0c μ BS rlo rhi * (BS + rhi * rhi)) * r x := by
  rw [kpow_eq_Lp]; exact h.Lp_weighted h.goodR h.Rk_bdd j x y

/-- **Stage 1, geometric bound, sup form.** `|R^{(j)}(x,y)| ≤ (BS+rhi²) Λ (1−c)^j`. -/
theorem DHyp.geom_sup (j : ℕ) (x y : E) :
    |kpow μ (Rk S r) j x y| ≤ (BS + rhi * rhi) * Λc μ BS rlo rhi * (1 - c) ^ j := by
  rw [kpow_eq_Lp]; exact h.Lp_sup h.goodR h.Rk_bdd j x y

end Stage1


/-! ## Stage 2: a differentiable family, exchange of `d/dε` and the sum over the powers -/

/-- Hypotheses for a family `S_ε`, `r_ε` on the ball `|ε| < δ`: the Doeblin hypotheses with UNIFORM constants,
and pointwise derivatives with uniform bounds. -/
structure FHyp (μ : Measure E) (S S' : ℝ → E → E → ℝ) (r r' : ℝ → E → ℝ) (δ c BS rlo rhi BS' Br' : ℝ) :
    Prop where
  δ0 : 0 < δ
  D : ∀ ε ∈ ball (0 : ℝ) δ, DHyp μ (S ε) (r ε) c BS rlo rhi
  S'm : ∀ ε ∈ ball (0 : ℝ) δ, Measurable (uncurry (S' ε))
  r'm : ∀ ε ∈ ball (0 : ℝ) δ, Measurable (r' ε)
  S'B : ∀ ε ∈ ball (0 : ℝ) δ, ∀ x y, |S' ε x y| ≤ BS'
  r'B : ∀ ε ∈ ball (0 : ℝ) δ, ∀ x, |r' ε x| ≤ Br'
  Sd : ∀ ε ∈ ball (0 : ℝ) δ, ∀ x y, HasDerivAt (fun e => S e x y) (S' ε x y) ε
  rd : ∀ ε ∈ ball (0 : ℝ) δ, ∀ x, HasDerivAt (fun e => r e x) (r' ε x) ε

/-- `R_ε = S_ε − r_ε ⊗ r_ε`. -/
def Rf (S : ℝ → E → E → ℝ) (r : ℝ → E → ℝ) (ε : ℝ) : E → E → ℝ := Rk (S ε) (r ε)

/-- Its derivative `R'_ε = S'_ε − r'_ε ⊗ r_ε − r_ε ⊗ r'_ε`. -/
def R'f (S' : ℝ → E → E → ℝ) (r r' : ℝ → E → ℝ) (ε : ℝ) (x y : E) : ℝ :=
  S' ε x y - (r' ε x * r ε y + r ε x * r' ε y)

/-- Derivatives of the iterated kernels of `R_ε`, by the product rule. -/
noncomputable def Dk (μ : Measure E) (S S' : ℝ → E → E → ℝ) (r r' : ℝ → E → ℝ) (ε : ℝ) :
    ℕ → E → E → ℝ
  | 0 => R'f S' r r' ε
  | j + 1 => fun x z => ∫ y, (R'f S' r r' ε x y * kpow μ (Rf S r ε) j y z +
      Rf S r ε x y * Dk μ S S' r r' ε j y z) ∂μ

/-- `Q_0 = R'`, `Q_{m+1} = R' ∘ R^{(m)}`. -/
noncomputable def Qk (μ : Measure E) (S S' : ℝ → E → E → ℝ) (r r' : ℝ → E → ℝ) (ε : ℝ) :
    ℕ → E → E → ℝ
  | 0 => R'f S' r r' ε
  | m + 1 => kmul μ (R'f S' r r' ε) (kpow μ (Rf S r ε) m)

/-- Crude bounds of `Dk`. -/
noncomputable def dk (μ : Measure E) (BR BR' : ℝ) : ℕ → ℝ
  | 0 => BR'
  | j + 1 => (BR' * kB μ BR j + BR * dk μ BR BR' j) * μ.real Set.univ

section Stage2

variable {μ : Measure E} [IsFiniteMeasure μ] {S S' : ℝ → E → E → ℝ} {r r' : ℝ → E → ℝ}
  {δ c BS rlo rhi BS' Br' : ℝ} (h : FHyp μ S S' r r' δ c BS rlo rhi BS' Br')
include h

lemma FHyp.R'_bdd (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) (x y : E) :
    |R'f S' r r' ε x y| ≤ BS' + 2 * (Br' * rhi) := by
  have hD := h.D ε hε
  unfold R'f
  refine (abs_sub _ _).trans (add_le_add (h.S'B ε hε x y) ?_)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 := mul_le_mul (h.r'B ε hε x) (hD.abs_r y) (abs_nonneg _) ((abs_nonneg _).trans (h.r'B ε hε x))
  have h2 := mul_le_mul (hD.abs_r x) (h.r'B ε hε y) (abs_nonneg _) (hD.rhi0 x)
  linarith

lemma FHyp.goodR' (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) : Good (R'f S' r r' ε) := by
  have hD := h.D ε hε
  refine ⟨?_, _, h.R'_bdd ε hε⟩
  exact (h.S'm ε hε).sub ((((h.r'm ε hε).comp measurable_fst).mul ((hD.rm).comp measurable_snd)).add
    (((hD.rm).comp measurable_fst).mul ((h.r'm ε hε).comp measurable_snd)))

lemma FHyp.Rd (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) (x y : E) :
    HasDerivAt (fun e => Rf S r e x y) (R'f S' r r' ε x y) ε :=
  (h.Sd ε hε x y).sub ((h.rd ε hε x).mul (h.rd ε hε y))

lemma FHyp.dk_bdd : ∀ j, ∀ ε ∈ ball (0 : ℝ) δ, ∀ x z,
    |Dk μ S S' r r' ε j x z| ≤ dk μ (BS + rhi * rhi) (BS' + 2 * (Br' * rhi)) j
  | 0, ε, hε, x, z => h.R'_bdd ε hε x z
  | j + 1, ε, hε, x, z => by
    have hD := h.D ε hε
    show |∫ y, _ ∂μ| ≤ _
    refine int_bound μ (fun y => ?_)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (h.R'_bdd ε hε x y) (kpow_bdd μ hD.Rk_bdd j y z) (abs_nonneg _)
        ((abs_nonneg _).trans (h.R'_bdd ε hε x y))
    · rw [abs_mul]
      exact mul_le_mul (hD.Rk_bdd x y) (FHyp.dk_bdd j ε hε y z) (abs_nonneg _) (hD.BR0 x)

lemma FHyp.goodDk (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) : ∀ j, Good (Dk μ S S' r r' ε j)
  | 0 => h.goodR' ε hε
  | j + 1 => by
    have hD := h.D ε hε
    refine ⟨?_, _, h.dk_bdd (j + 1) ε hε⟩
    have g1 := h.goodR' ε hε
    have g2 := hD.goodR.kpow μ j
    have g3 := FHyp.goodDk ε hε j
    show Measurable (uncurry fun x z => ∫ y, (R'f S' r r' ε x y * kpow μ (Rf S r ε) j y z +
      Rf S r ε x y * Dk μ S S' r r' ε j y z) ∂μ)
    exact meas_param μ _
      (((g1.1.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (g2.1.comp (measurable_snd.prodMk measurable_fst.snd))).add
       ((hD.goodR.1.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (g3.1.comp (measurable_snd.prodMk measurable_fst.snd))))

/-- **Derivative of the iterated kernels of `R_ε`**, at every point of the ball. -/
theorem FHyp.kpowR_hasDerivAt : ∀ j, ∀ ε0 ∈ ball (0 : ℝ) δ, ∀ x z,
    HasDerivAt (fun ε => kpow μ (Rf S r ε) j x z) (Dk μ S S' r r' ε0 j x z) ε0
  | 0, ε0, hε0, x, z => h.Rd ε0 hε0 x z
  | j + 1, ε0, hε0, x, z => by
    show HasDerivAt (fun ε => ∫ y, Rf S r ε x y * kpow μ (Rf S r ε) j y z ∂μ)
      (∫ y, (R'f S' r r' ε0 x y * kpow μ (Rf S r ε0) j y z +
        Rf S r ε0 x y * Dk μ S S' r r' ε0 j y z) ∂μ) ε0
    obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball ε0 hε0
    have hD0 := h.D ε0 hε0
    have hx0 : 0 ≤ BS + rhi * rhi := hD0.BR0 x
    have hx1 : 0 ≤ BS' + 2 * (Br' * rhi) := (abs_nonneg _).trans (h.R'_bdd ε0 hε0 x x)
    have hdk0 : 0 ≤ dk μ (BS + rhi * rhi) (BS' + 2 * (Br' * rhi)) j :=
      (abs_nonneg _).trans (h.dk_bdd j ε0 hε0 x x)
    have hF := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
      (F := fun ε y => Rf S r ε x y * kpow μ (Rf S r ε) j y z)
      (F' := fun ε y => R'f S' r r' ε x y * kpow μ (Rf S r ε) j y z +
        Rf S r ε x y * Dk μ S S' r r' ε j y z)
      (x₀ := ε0) (bound := fun _ => (BS' + 2 * (Br' * rhi)) * kB μ (BS + rhi * rhi) j +
        (BS + rhi * rhi) * dk μ (BS + rhi * rhi) (BS' + 2 * (Br' * rhi)) j) (ball_mem_nhds ε0 hη)
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds hε0) fun ε hε =>
        (((h.D ε hε).goodR.row x).mul (((h.D ε hε).goodR.kpow μ j).col z)).aestronglyMeasurable)
      (hD0.goodR.intg μ (hD0.goodR.kpow μ j) x z)
      ((((h.goodR' ε0 hε0).row x).mul ((hD0.goodR.kpow μ j).col z)).add
        ((hD0.goodR.row x).mul ((h.goodDk ε0 hε0 j).col z))).aestronglyMeasurable
      (ae_of_all _ fun y ε hε => ?_) (integrable_const _)
      (ae_of_all _ fun y ε hε => ?_)
    · exact hF.2
    · have hD := h.D ε (hsub hε)
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        exact mul_le_mul (h.R'_bdd ε (hsub hε) x y) (kpow_bdd μ hD.Rk_bdd j y z) (abs_nonneg _) hx1
      · rw [abs_mul]
        exact mul_le_mul (hD.Rk_bdd x y) (h.dk_bdd j ε (hsub hε) y z) (abs_nonneg _) hx0
    · exact (h.Rd ε (hsub hε) x y).mul (FHyp.kpowR_hasDerivAt j ε (hsub hε) y z)

end Stage2

section Gen2

lemma summable_lin_geom {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) (C : ℝ) :
    Summable fun j : ℕ => ((j : ℝ) + 1) * C * ρ ^ j := by
  have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ρ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ)
  have h2 : Summable fun n : ℕ => ρ ^ n := summable_geometric_of_lt_one hρ0 hρ
  convert (h1.add h2).mul_left C using 1
  funext n; simp only [pow_one]; ring

lemma hasSum_fc_succ : HasSum (fun j : ℕ => fc (j + 1)) 1 := by
  have h1 := (hasSum_nat_add_iff' (f := fc) 1).mpr CTG.DensityExchange.hasSum_fc
  simpa [CTG.DensityExchange.fc_zero] using h1

end Gen2

section Stage2b

variable {μ : Measure E} [IsFiniteMeasure μ] {S S' : ℝ → E → E → ℝ} {r r' : ℝ → E → ℝ}
  {δ c BS rlo rhi BS' Br' : ℝ} (h : FHyp μ S S' r r' δ c BS rlo rhi BS' Br')
include h

lemma FHyp.goodQ (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) : ∀ m, Good (Qk μ S S' r r' ε m)
  | 0 => h.goodR' ε hε
  | m + 1 => (h.goodR' ε hε).kmul μ (((h.D ε hε).goodR).kpow μ m)

/-- **Structure of the derivative** (only linearity of the integral): `D_j = Σ_{p ≤ j} L_p(Q_{j−p})`. -/
theorem FHyp.Dk_struct (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) : ∀ j x z,
    Dk μ S S' r r' ε j x z =
      ∑ p ∈ Finset.range (j + 1), Lp μ (Rf S r ε) (Qk μ S S' r r' ε (j - p)) p x z
  | 0, x, z => by simp [Dk, Qk, Lp]
  | j + 1, x, z => by
    have hD := h.D ε hε
    have gRf : Good (Rf S r ε) := hD.goodR
    have ih := FHyp.Dk_struct ε hε j
    show ∫ y, (R'f S' r r' ε x y * kpow μ (Rf S r ε) j y z +
      Rf S r ε x y * Dk μ S S' r r' ε j y z) ∂μ = _
    have hgL : ∀ p, Good (Lp μ (Rf S r ε) (Qk μ S S' r r' ε (j - p)) p) := fun p =>
      gRf.Lp μ (h.goodQ ε hε (j - p)) p
    have e1 : (fun y => Rf S r ε x y * Dk μ S S' r r' ε j y z) =
        fun y => ∑ p ∈ Finset.range (j + 1),
          Rf S r ε x y * Lp μ (Rf S r ε) (Qk μ S S' r r' ε (j - p)) p y z := by
      funext y; rw [ih y z, Finset.mul_sum]
    rw [integral_add ((h.goodR' ε hε).intg μ (gRf.kpow μ j) x z)
      (gRf.intg μ (h.goodDk ε hε j) x z), e1,
      integral_finset_sum _ (fun p _ => gRf.intg μ (hgL p) x z)]
    rw [Finset.sum_range_succ' _ (j + 1)]
    simp only [Nat.sub_zero, Nat.add_sub_add_right]
    rw [add_comm]
    rfl

/-- The precise constant for `Q`. -/
noncomputable def CQc (μ : Measure E) (BS rlo rhi BS' Br' : ℝ) : ℝ :=
  (BS' + 2 * (Br' * rhi)) * (1 + 2 * ((BS + rhi * rhi) * Λc μ BS rlo rhi * μ.real Set.univ))

lemma FHyp.Q_bdd (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) (m : ℕ) (x z : E) :
    |Qk μ S S' r r' ε m x z| ≤ CQc μ BS rlo rhi BS' Br' * (1 - c) ^ m := by
  have hD := h.D ε hε
  have hb0 : 0 ≤ BS' + 2 * (Br' * rhi) := (abs_nonneg _).trans (h.R'_bdd ε hε x x)
  have hBR := hD.BR0 x
  have hΛ := hD.Λ1 x
  have hμ : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hc1 : 0 ≤ 1 - c := by linarith [hD.c_le]
  have hA : 0 ≤ (BS + rhi * rhi) * Λc μ BS rlo rhi * μ.real Set.univ := by positivity
  cases m with
  | zero =>
    simp only [Qk, pow_zero, mul_one, CQc]
    refine (h.R'_bdd ε hε x z).trans (le_mul_of_one_le_right hb0 ?_)
    linarith
  | succ m =>
    show |kmul μ (R'f S' r r' ε) (kpow μ (Rf S r ε) m) x z| ≤ _
    refine (kmul_bdd μ (h.R'_bdd ε hε) (hD.geom_sup m) x z).trans ?_
    have hpm : 0 ≤ (1 - c) ^ m := pow_nonneg hc1 m
    have h3 : (1 - c) ^ m ≤ 2 * (1 - c) ^ (m + 1) := by rw [pow_succ]; nlinarith [hD.c_le]
    unfold CQc
    have : (BS' + 2 * (Br' * rhi)) * ((BS + rhi * rhi) * Λc μ BS rlo rhi * (1 - c) ^ m) *
        μ.real Set.univ = (BS' + 2 * (Br' * rhi)) *
          ((BS + rhi * rhi) * Λc μ BS rlo rhi * μ.real Set.univ) * (1 - c) ^ m := by ring
    rw [this]
    have h5 : 0 ≤ (BS' + 2 * (Br' * rhi)) * ((BS + rhi * rhi) * Λc μ BS rlo rhi * μ.real Set.univ) :=
      mul_nonneg hb0 hA
    have h6 : 0 ≤ (BS' + 2 * (Br' * rhi)) * (1 - c) ^ (m + 1) := mul_nonneg hb0 (pow_nonneg hc1 _)
    nlinarith

/-- **Geometric bound of the derivative**: `|D_j(x,z)| ≤ (j+1) CQ Λ (1−c)^j` on the whole ball. -/
theorem FHyp.Dk_geom (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) δ) (j : ℕ) (x z : E) :
    |Dk μ S S' r r' ε j x z| ≤
      ((j : ℝ) + 1) * (CQc μ BS rlo rhi BS' Br' * Λc μ BS rlo rhi) * (1 - c) ^ j := by
  have hD := h.D ε hε
  rw [h.Dk_struct ε hε j x z]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ p ∈ Finset.range (j + 1),
      |Lp μ (Rf S r ε) (Qk μ S S' r r' ε (j - p)) p x z| ≤
        CQc μ BS rlo rhi BS' Br' * Λc μ BS rlo rhi * (1 - c) ^ j := by
    intro p hp
    have hpj : p ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    have := hD.Lp_sup (h.goodQ ε hε (j - p)) (h.Q_bdd ε hε (j - p)) p x z
    refine this.trans (le_of_eq ?_)
    rw [show (1 - c) ^ j = (1 - c) ^ (j - p) * (1 - c) ^ p by rw [← pow_add, Nat.sub_add_cancel hpj]]
    ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast; ring

/-- Termwise derivative of the iterated kernels of `S_ε` themselves. -/
theorem FHyp.kpowS_hasDerivAt (j : ℕ) (ε0 : ℝ) (hε0 : ε0 ∈ ball (0 : ℝ) δ) (x z : E) :
    HasDerivAt (fun ε => kpow μ (S ε) j x z)
      (r' ε0 x * r ε0 z + r ε0 x * r' ε0 z + Dk μ S S' r r' ε0 j x z) ε0 := by
  obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball ε0 hε0
  have h1 := ((h.rd ε0 hε0 x).mul (h.rd ε0 hε0 z)).add (h.kpowR_hasDerivAt j ε0 hε0 x z)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds ε0 hη] with ε hε
  exact (h.D ε (hsub hε)).decomp j x z

/-- **Stage 2.** Exchange of `d/dε` and the sum over the powers for integral kernels.
`u(ε) = Σ' j, f_{j+1} S_ε^{(j)}(x,x)` is differentiable at `0` and its derivative is the sum of the termwise
derivatives `2 r_0(x) r'_0(x) + D_j(x,x)`. -/
theorem FHyp.deriv_sum_kernels (x : E) :
    Summable (fun j => fc (j + 1) * (2 * (r 0 x * r' 0 x) + Dk μ S S' r r' 0 j x x)) ∧
    HasDerivAt (fun ε => ∑' j, fc (j + 1) * kpow μ (S ε) j x x)
      (∑' j, fc (j + 1) * (2 * (r 0 x * r' 0 x) + Dk μ S S' r r' 0 j x x)) 0 := by
  have h0 : (0 : ℝ) ∈ ball (0 : ℝ) δ := mem_ball_self h.δ0
  have hD0 := h.D 0 h0
  have hρ0 : 0 ≤ 1 - c := by linarith [hD0.c_le]
  have hρ1 : 1 - c < 1 := by linarith [hD0.c0]
  set CD := CQc μ BS rlo rhi BS' Br' * Λc μ BS rlo rhi
  set BG := (BS + rhi * rhi) * Λc μ BS rlo rhi
  have hfc := hasSum_fc_succ
  -- the R-part
  have hu := summable_lin_geom hρ0 hρ1 CD
  have hg' : ∀ (j : ℕ) ε, ε ∈ ball (0 : ℝ) δ →
      ‖fc (j + 1) * Dk μ S S' r r' ε j x x‖ ≤ ((j : ℝ) + 1) * CD * (1 - c) ^ j := by
    intro j ε hε
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fc_nonneg _)]
    have h1 := h.Dk_geom ε hε j x x
    have h2 : 0 ≤ ((j : ℝ) + 1) * CD * (1 - c) ^ j := (abs_nonneg _).trans (h1.trans (le_of_eq (by ring)))
    calc fc (j + 1) * |Dk μ S S' r r' ε j x x| ≤ 1 * (((j : ℝ) + 1) * CD * (1 - c) ^ j) :=
          mul_le_mul (CTG.DensityExchange.fc_le_one _) (h1.trans (le_of_eq (by ring)))
            (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hgR : ∀ ε ∈ ball (0 : ℝ) δ, Summable fun j => fc (j + 1) * kpow μ (Rf S r ε) j x x := by
    intro ε hε
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hρ0 hρ1).mul_left BG) fun j => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (fc_nonneg _)]
    have h1 := (h.D ε hε).geom_sup j x x
    have h2 : 0 ≤ BG * (1 - c) ^ j := (abs_nonneg _).trans h1
    calc fc (j + 1) * |kpow μ (Rf S r ε) j x x| ≤ 1 * (BG * (1 - c) ^ j) :=
          mul_le_mul (CTG.DensityExchange.fc_le_one _) h1 (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hT := hasDerivAt_tsum_of_isPreconnected (g := fun j ε => fc (j + 1) * kpow μ (Rf S r ε) j x x)
    (g' := fun j ε => fc (j + 1) * Dk μ S S' r r' ε j x x) hu isOpen_ball
    (convex_ball (0 : ℝ) δ).isPreconnected
    (fun j ε hε => (h.kpowR_hasDerivAt j ε hε x x).const_mul _) hg' h0 (hgR 0 h0) h0
  have hsD : Summable fun j => fc (j + 1) * Dk μ S S' r r' 0 j x x :=
    Summable.of_norm_bounded hu fun j => hg' j 0 h0
  have hsum_eq : (∑' j, fc (j + 1) * (2 * (r 0 x * r' 0 x) + Dk μ S S' r r' 0 j x x)) =
      2 * (r 0 x * r' 0 x) + ∑' j, fc (j + 1) * Dk μ S S' r r' 0 j x x := by
    have e : (fun j => fc (j + 1) * (2 * (r 0 x * r' 0 x) + Dk μ S S' r r' 0 j x x)) =
        fun j => fc (j + 1) * (2 * (r 0 x * r' 0 x)) + fc (j + 1) * Dk μ S S' r r' 0 j x x := by
      funext j; ring
    rw [e, Summable.tsum_add (hfc.summable.mul_right _) hsD, tsum_mul_right, hfc.tsum_eq, one_mul]
  have hsum' : Summable fun j => fc (j + 1) * (2 * (r 0 x * r' 0 x) + Dk μ S S' r r' 0 j x x) := by
    have e : (fun j => fc (j + 1) * (2 * (r 0 x * r' 0 x) + Dk μ S S' r r' 0 j x x)) =
        fun j => fc (j + 1) * (2 * (r 0 x * r' 0 x)) + fc (j + 1) * Dk μ S S' r r' 0 j x x := by
      funext j; ring
    rw [e]; exact (hfc.summable.mul_right _).add hsD
  refine ⟨hsum', ?_⟩
  rw [hsum_eq]
  have hr2 := (h.rd 0 h0 x).mul (h.rd 0 h0 x)
  have hfull := hr2.add hT
  refine (hfull.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [isOpen_ball.mem_nhds h0] with ε hε
  have hDε := h.D ε hε
  have e : (fun j => fc (j + 1) * kpow μ (S ε) j x x) =
      fun j => fc (j + 1) * (r ε x * r ε x) + fc (j + 1) * kpow μ (Rf S r ε) j x x := by
    funext j; rw [hDε.decomp j x x]; unfold Rf; ring
  rw [e, Summable.tsum_add (hfc.summable.mul_right _) (hgR ε hε), tsum_mul_right, hfc.tsum_eq, one_mul]
  rfl

end Stage2b

/-! ## Stage 3: the frame `Hyp` with a symmetric kernel bounded below -/

section Stage3

open CTG.DensityExchangeCont

variable {μ : Measure E} [IsFiniteMeasure μ] {K : E → E → ℝ} {φ : E → ℝ} {n0 κ B C : ℝ}

/-- `r_ε = A_ε R_ε` (equal to `rc`, see `rr_eq`). -/
noncomputable def rr (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  Aε μ K φ n0 ε y * Rc μ K (nε n0 φ ε) y
noncomputable def rr' (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  Ad μ K φ n0 ε y * Rc μ K (nε n0 φ ε) y + Aε μ K φ n0 ε y * Rd μ K φ n0 ε y
/-- `N_ε = ∫ r_ε²` and its derivative. -/
noncomputable def Nn (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) : ℝ :=
  ∫ y, rr μ K φ n0 ε y * rr μ K φ n0 ε y ∂μ
noncomputable def Nn' (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) : ℝ :=
  ∫ y, (rr' μ K φ n0 ε y * rr μ K φ n0 ε y + rr μ K φ n0 ε y * rr' μ K φ n0 ε y) ∂μ
/-- Normalised top eigenfunction `r̂_ε = r_ε/√N_ε` and its derivative. -/
noncomputable def rh (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  rr μ K φ n0 ε y / Real.sqrt (Nn μ K φ n0 ε)
noncomputable def rh' (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (y : E) : ℝ :=
  (rr' μ K φ n0 ε y * Real.sqrt (Nn μ K φ n0 ε) -
    rr μ K φ n0 ε y * (Nn' μ K φ n0 ε / (2 * Real.sqrt (Nn μ K φ n0 ε)))) /
    Real.sqrt (Nn μ K φ n0 ε) ^ 2
/-- `S_ε` and its derivative. -/
noncomputable def SS (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) : E → E → ℝ :=
  Sc μ K (nε n0 φ ε)
noncomputable def SS' (μ : Measure E) (K : E → E → ℝ) (φ : E → ℝ) (n0 ε : ℝ) (x y : E) : ℝ :=
  Ad μ K φ n0 ε x * K x y * Aε μ K φ n0 ε y + Aε μ K φ n0 ε x * K x y * Ad μ K φ n0 ε y

/-- Upper bound of `R` on `|ε| ≤ 1`. -/
noncomputable def Rup (κ C : ℝ) : ℝ := Real.exp (1 * C) / (Real.exp (-(1 * C)) * κ) * κ
/-- Lower bound of `A` on `|ε| ≤ 1`. -/
noncomputable def Alo (n0 κ C : ℝ) : ℝ :=
  Real.exp ((Real.log n0 - C) / 2 - Real.log (n0 * Real.exp (1 * C) * κ) / 2 - Real.log (Rup κ C) / 2)

variable (h : Hyp μ K φ n0 κ B C)
include h

lemma ball1 {ε : ℝ} (hε : ε ∈ ball (0 : ℝ) 1) : |ε| ≤ 1 := by
  rw [mem_ball, Real.dist_eq, sub_zero] at hε; exact hε.le

lemma Rup_pos : 0 < Rup κ C := by unfold Rup; have := h.κpos; positivity

lemma R_le (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : Rc μ K (nε n0 φ ε) y ≤ Rup κ C := by
  rw [R_eq h ε y]
  exact int_K_upper h y _ (meas_gR h ε) _ (gR_abs_le h ε 1 hε) _ (fun z => (gR_bounds h ε 1 hε z).2)

lemma A_ge (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : Alo n0 κ C ≤ Aε μ K φ n0 ε y := by
  rw [A_eq_exp h ε y]
  unfold Alo
  apply Real.exp_le_exp.mpr
  have h1 : -C ≤ ε * φ y := by
    have : |ε * φ y| ≤ C := by
      rw [abs_mul]; calc |ε| * |φ y| ≤ 1 * C := mul_le_mul hε (h.φC y) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    linarith [neg_abs_le (ε * φ y)]
  have h2 := Real.log_le_log (q_pos h ε y) (q_bounds h ε 1 hε y).2
  have h3 := Real.log_le_log (R_pos h ε y) (R_le h ε hε y)
  linarith

lemma Alo_pos : 0 < Alo n0 κ C := Real.exp_pos _

lemma rr_eq (ε : ℝ) (y : E) : rc μ K (nε n0 φ ε) y = rr μ K φ n0 ε y := by
  have hn := nε_pos h ε y
  have hD := D_pos h ε y
  have hq := q_pos h ε y
  have hR : Rc μ K (nε n0 φ ε) y = Dc μ K (nε n0 φ ε) y * qc μ K (nε n0 φ ε) y := by
    rw [Dc_eq]; field_simp
  have key : ∀ (a q D s : ℝ), 0 < q → 0 < s → s * s = D → a * s = a / (q * s) * (D * q) := by
    rintro a q D s hq hs rfl; field_simp
  unfold rc rr Aε Ac
  rw [Real.sqrt_mul hn.le, hR]
  exact key _ _ _ _ hq (Real.sqrt_pos.mpr hD) (Real.mul_self_sqrt hD.le)

lemma meas_rr (ε : ℝ) : Measurable (rr μ K φ n0 ε) := (meas_A h ε).mul (meas_R h ε)
lemma meas_rr' (ε : ℝ) : Measurable (rr' μ K φ n0 ε) :=
  ((meas_Ad h ε).mul (meas_R h ε)).add ((meas_A h ε).mul (meas_Rd h ε))

lemma rr_pos (ε : ℝ) (y : E) : 0 < rr μ K φ n0 ε y := mul_pos (Aε_pos h ε y) (R_pos h ε y)

lemma rr_ge (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : Alo n0 κ C * Rlo κ C ≤ rr μ K φ n0 ε y :=
  mul_le_mul (A_ge h ε hε y) (R_ge h ε hε y) (Rlo_pos h).le (Aε_pos h ε y).le

lemma rr_le (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : rr μ K φ n0 ε y ≤ Aup n0 κ C * Rup κ C :=
  mul_le_mul (A_le h ε hε y) (R_le h ε hε y) (R_pos h ε y).le (Aup_nonneg h)

lemma rr'_abs (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : |rr' μ K φ n0 ε y| ≤
    AdB μ n0 κ B C * Rup κ C + Aup n0 κ C * (B * gB μ n0 κ B C * μ.real Set.univ) := by
  unfold rr'
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (R_pos h ε y)]
    exact mul_le_mul (Ad_abs h ε hε y) (R_le h ε hε y) (R_pos h ε y).le (AdB_nonneg h)
  · rw [abs_mul, abs_of_pos (Aε_pos h ε y)]
    exact mul_le_mul (A_le h ε hε y) (Rd_abs h ε hε y) (abs_nonneg _) (Aup_nonneg h)

lemma rr_hasDerivAt (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) 1) (y : E) :
    HasDerivAt (fun e => rr μ K φ n0 e y) (rr' μ K φ n0 ε y) ε :=
  (hasDerivAt_A1 h ε hε y).mul (hasDerivAt_R1 h ε hε y)

lemma rr_abs (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : |rr μ K φ n0 ε y| ≤ Aup n0 κ C * Rup κ C := by
  rw [abs_of_pos (rr_pos h ε y)]; exact rr_le h ε hε y

lemma Nn_hasDerivAt (ε0 : ℝ) (hε0 : ε0 ∈ ball (0 : ℝ) 1) :
    HasDerivAt (fun ε => Nn μ K φ n0 ε) (Nn' μ K φ n0 ε0) ε0 := by
  obtain ⟨η, hη, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball ε0 hε0
  set M1 := Aup n0 κ C * Rup κ C
  set M2 := AdB μ n0 κ B C * Rup κ C + Aup n0 κ C * (B * gB μ n0 κ B C * μ.real Set.univ)
  have hM1 : 0 ≤ M1 := mul_nonneg (Aup_nonneg h) (Rup_pos h).le
  have hF := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun ε y => rr μ K φ n0 ε y * rr μ K φ n0 ε y)
    (F' := fun ε y => rr' μ K φ n0 ε y * rr μ K φ n0 ε y + rr μ K φ n0 ε y * rr' μ K φ n0 ε y)
    (x₀ := ε0) (bound := fun _ => M2 * M1 + M1 * M2) (ball_mem_nhds ε0 hη)
    (Eventually.of_forall fun ε => ((meas_rr h ε).mul (meas_rr h ε)).aestronglyMeasurable)
    (integrable_bdd μ ((meas_rr h ε0).mul (meas_rr h ε0)) (M := M1 * M1) fun y => by
      rw [abs_mul]; exact mul_le_mul (rr_abs h ε0 (ball1 h hε0) y) (rr_abs h ε0 (ball1 h hε0) y)
        (abs_nonneg _) hM1)
    ((((meas_rr' h ε0).mul (meas_rr h ε0)).add ((meas_rr h ε0).mul (meas_rr' h ε0)))).aestronglyMeasurable
    (ae_of_all _ fun y ε hε => by
      have hε1 := ball1 h (hsub hε)
      have h2 := rr'_abs h ε hε1 y
      have hM2 : 0 ≤ M2 := (abs_nonneg _).trans h2
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
      · exact mul_le_mul h2 (rr_abs h ε hε1 y) (abs_nonneg _) hM2
      · exact mul_le_mul (rr_abs h ε hε1 y) h2 (abs_nonneg _) hM1)
    (integrable_const _)
    (ae_of_all _ fun y ε hε => (rr_hasDerivAt h ε (hsub hε) y).mul (rr_hasDerivAt h ε (hsub hε) y))
  exact hF.2


/-- Constants of Stage 3. -/
noncomputable def M1c (n0 κ C : ℝ) : ℝ := Aup n0 κ C * Rup κ C
noncomputable def M2c (μ : Measure E) (n0 κ B C : ℝ) : ℝ :=
  AdB μ n0 κ B C * Rup κ C + Aup n0 κ C * (B * gB μ n0 κ B C * μ.real Set.univ)
noncomputable def Nlo (μ : Measure E) (n0 κ C : ℝ) : ℝ :=
  (Alo n0 κ C * Rlo κ C) * (Alo n0 κ C * Rlo κ C) * μ.real Set.univ
noncomputable def Nup (μ : Measure E) (n0 κ C : ℝ) : ℝ := M1c n0 κ C * M1c n0 κ C * μ.real Set.univ
noncomputable def rlo3 (μ : Measure E) (n0 κ C : ℝ) : ℝ := Alo n0 κ C * Rlo κ C / Real.sqrt (Nup μ n0 κ C)
noncomputable def rhi3 (μ : Measure E) (n0 κ C : ℝ) : ℝ := M1c n0 κ C / Real.sqrt (Nlo μ n0 κ C)
noncomputable def N'B (μ : Measure E) (n0 κ B C : ℝ) : ℝ :=
  (M2c μ n0 κ B C * M1c n0 κ C + M1c n0 κ C * M2c μ n0 κ B C) * μ.real Set.univ
noncomputable def r'B3 (μ : Measure E) (n0 κ B C : ℝ) : ℝ :=
  (M2c μ n0 κ B C * Real.sqrt (Nup μ n0 κ C) +
    M1c n0 κ C * (N'B μ n0 κ B C / (2 * Real.sqrt (Nlo μ n0 κ C)))) / Nlo μ n0 κ C
noncomputable def c3 (μ : Measure E) (n0 κ C kmin : ℝ) : ℝ :=
  min (1 / 2) (Alo n0 κ C * Alo n0 κ C * kmin / (rhi3 μ n0 κ C * rhi3 μ n0 κ C))

variable (hμ : 0 < μ.real Set.univ)
include hμ

lemma Nlo_pos : 0 < Nlo μ n0 κ C := by
  unfold Nlo; have := Alo_pos h; have := Rlo_pos h; positivity

lemma M1_pos : 0 < M1c n0 κ C := mul_pos (Real.exp_pos _) (Rup_pos h)

lemma Nup_pos : 0 < Nup μ n0 κ C := by unfold Nup; have := M1_pos h hμ; positivity

lemma Nn_ge (ε : ℝ) (hε : |ε| ≤ 1) : Nlo μ n0 κ C ≤ Nn μ K φ n0 ε := by
  have hl := Alo_pos h; have hR := Rlo_pos h
  have e : Nlo μ n0 κ C = ∫ _ : E, (Alo n0 κ C * Rlo κ C) * (Alo n0 κ C * Rlo κ C) ∂μ := by
    rw [integral_const, smul_eq_mul]; unfold Nlo; ring
  rw [e]
  refine integral_mono (integrable_const _) (integrable_bdd μ ((meas_rr h ε).mul (meas_rr h ε))
    (M := M1c n0 κ C * M1c n0 κ C) fun y => ?_) fun y => ?_
  · rw [abs_mul]; exact mul_le_mul (rr_abs h ε hε y) (rr_abs h ε hε y) (abs_nonneg _)
      (M1_pos h hμ).le
  · have := rr_ge h ε hε y
    exact mul_le_mul this this (by positivity) (rr_pos h ε y).le

lemma Nn_le (ε : ℝ) (hε : |ε| ≤ 1) : Nn μ K φ n0 ε ≤ Nup μ n0 κ C := by
  have e : Nup μ n0 κ C = ∫ _ : E, M1c n0 κ C * M1c n0 κ C ∂μ := by
    rw [integral_const, smul_eq_mul]; unfold Nup; ring
  rw [e]
  refine integral_mono (integrable_bdd μ ((meas_rr h ε).mul (meas_rr h ε))
    (M := M1c n0 κ C * M1c n0 κ C) fun y => ?_) (integrable_const _) fun y => ?_
  · rw [abs_mul]; exact mul_le_mul (rr_abs h ε hε y) (rr_abs h ε hε y) (abs_nonneg _)
      (M1_pos h hμ).le
  · have := rr_le h ε hε y
    exact mul_le_mul this this (rr_pos h ε y).le (M1_pos h hμ).le

lemma Nn_pos (ε : ℝ) (hε : |ε| ≤ 1) : 0 < Nn μ K φ n0 ε := (Nlo_pos h hμ).trans_le (Nn_ge h hμ ε hε)

lemma Nn'_abs (ε : ℝ) (hε : |ε| ≤ 1) : |Nn' μ K φ n0 ε| ≤ N'B μ n0 κ B C := by
  unfold Nn' N'B
  refine int_bound μ fun y => ?_
  have h2 := rr'_abs h ε hε y
  have hM2 : 0 ≤ M2c μ n0 κ B C := (abs_nonneg _).trans h2
  have h1 := rr_abs h ε hε y
  have hM1 := (M1_pos h hμ).le
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
  · exact mul_le_mul h2 h1 (abs_nonneg _) hM2
  · exact mul_le_mul h1 h2 (abs_nonneg _) hM1

lemma rh_ge (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : rlo3 μ n0 κ C ≤ rh μ K φ n0 ε y := by
  unfold rlo3 rh
  have hN := Nn_pos h hμ ε hε
  have hl := Alo_pos h; have hR := Rlo_pos h
  exact div_le_div₀ (rr_pos h ε y).le (rr_ge h ε hε y) (Real.sqrt_pos.mpr hN)
    (Real.sqrt_le_sqrt (Nn_le h hμ ε hε))

lemma rh_le (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : rh μ K φ n0 ε y ≤ rhi3 μ n0 κ C := by
  unfold rhi3 rh
  exact div_le_div₀ (M1_pos h hμ).le (rr_le h ε hε y) (Real.sqrt_pos.mpr (Nlo_pos h hμ))
    (Real.sqrt_le_sqrt (Nn_ge h hμ ε hε))

lemma rlo3_pos : 0 < rlo3 μ n0 κ C := by
  unfold rlo3; have := Alo_pos h; have := Rlo_pos h; have := Real.sqrt_pos.mpr (Nup_pos h hμ)
  positivity

lemma rhi3_pos : 0 < rhi3 μ n0 κ C := by
  unfold rhi3; have := M1_pos h hμ; have := Real.sqrt_pos.mpr (Nlo_pos h hμ); positivity

lemma rh'_abs (ε : ℝ) (hε : |ε| ≤ 1) (y : E) : |rh' μ K φ n0 ε y| ≤ r'B3 μ n0 κ B C := by
  have hN := Nn_pos h hμ ε hε
  have hs := Real.sqrt_pos.mpr hN
  have hsl := Real.sqrt_pos.mpr (Nlo_pos h hμ)
  have hsq : Real.sqrt (Nn μ K φ n0 ε) ^ 2 = Nn μ K φ n0 ε := Real.sq_sqrt hN.le
  unfold rh' r'B3
  rw [hsq, abs_div, abs_of_pos hN]
  have h2 := rr'_abs h ε hε y
  have hM2 : 0 ≤ M2c μ n0 κ B C := (abs_nonneg _).trans h2
  have h1 := rr_abs h ε hε y
  have hM1 := (M1_pos h hμ).le
  have hNB : 0 ≤ N'B μ n0 κ B C := (abs_nonneg _).trans (Nn'_abs h hμ ε hε)
  refine div_le_div₀ (by positivity) ((abs_sub _ _).trans (add_le_add ?_ ?_)) (Nlo_pos h hμ)
    (Nn_ge h hμ ε hε)
  · rw [abs_mul, abs_of_pos hs]
    exact mul_le_mul h2 (Real.sqrt_le_sqrt (Nn_le h hμ ε hε)) hs.le hM2
  · rw [abs_mul]
    refine mul_le_mul h1 ?_ (abs_nonneg _) hM1
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt (Nn μ K φ n0 ε))]
    exact div_le_div₀ hNB (Nn'_abs h hμ ε hε) (by positivity)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nn_ge h hμ ε hε)) zero_le_two)

lemma rh_hasDerivAt (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) 1) (y : E) :
    HasDerivAt (fun e => rh μ K φ n0 e y) (rh' μ K φ n0 ε y) ε := by
  have hN := Nn_pos h hμ ε (ball1 h hε)
  have hs := ((Nn_hasDerivAt h ε hε).sqrt hN.ne')
  exact (rr_hasDerivAt h ε hε y).div hs (Real.sqrt_pos.mpr hN).ne'

lemma SS_eq (ε : ℝ) (x y : E) :
    SS μ K φ n0 ε x y = Aε μ K φ n0 ε x * K x y * Aε μ K φ n0 ε y := Sc_eq h ε x y

lemma SS_hasDerivAt (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) 1) (x y : E) :
    HasDerivAt (fun e => SS μ K φ n0 e x y) (SS' μ K φ n0 ε x y) ε := by
  rw [show (fun e => SS μ K φ n0 e x y) = fun e => Aε μ K φ n0 e x * K x y * Aε μ K φ n0 e y from
    funext fun e => SS_eq h hμ e x y]
  exact ((hasDerivAt_A1 h ε hε x).mul_const (K x y)).mul (hasDerivAt_A1 h ε hε y)

variable {kmin : ℝ} (hKs : ∀ x y, K x y = K y x) (hk : 0 < kmin) (hKmin : ∀ x y, kmin ≤ K x y)
include hKs hk hKmin

lemma c3_pos : 0 < c3 μ n0 κ C kmin := by
  unfold c3
  have := Alo_pos h; have := rhi3_pos h hμ
  exact lt_min (by norm_num) (by positivity)

/-- The Doeblin hypotheses hold for every `|ε| < 1` with uniform constants. -/
theorem dHyp3 (ε : ℝ) (hε : ε ∈ ball (0 : ℝ) 1) :
    DHyp μ (SS μ K φ n0 ε) (rh μ K φ n0 ε) (c3 μ n0 κ C kmin) (Aup n0 κ C * B * Aup n0 κ C)
      (rlo3 μ n0 κ C) (rhi3 μ n0 κ C) := by
  have hε1 := ball1 h hε
  have hN := Nn_pos h hμ ε hε1
  have hs := Real.sqrt_pos.mpr hN
  have hSeq : ∀ x y, SS μ K φ n0 ε x y = Aε μ K φ n0 ε x * K x y * Aε μ K φ n0 ε y := SS_eq h hμ ε
  exact
  { Sm := by
      have : uncurry (SS μ K φ n0 ε) = fun p : E × E =>
          Aε μ K φ n0 ε p.1 * K p.1 p.2 * Aε μ K φ n0 ε p.2 := funext fun p => hSeq p.1 p.2
      rw [this]
      exact (((meas_A h ε).comp measurable_fst).mul h.Km).mul ((meas_A h ε).comp measurable_snd)
    rm := (meas_rr h ε).div_const _
    Ssym := fun x y => Sc_symm μ K _ hKs x y
    SB := fun x y => by
      rw [hSeq, abs_mul, abs_mul, abs_of_pos (Aε_pos h ε x), abs_of_pos (Aε_pos h ε y),
        abs_of_nonneg (h.K0 x y)]
      exact mul_le_mul (mul_le_mul (A_le h ε hε1 x) (h.KB x y) (h.K0 x y) (Aup_nonneg h))
        (A_le h ε hε1 y) (Aε_pos h ε y).le (mul_nonneg (Aup_nonneg h) h.B0)
    rlo0 := rlo3_pos h hμ
    rlo_le := rh_ge h hμ ε hε1
    r_le := rh_le h hμ ε hε1
    eig := fun x => by
      have he := Sc_top_eigen μ K (nε n0 φ ε) (nε_pos h ε) (D_pos h ε) x
      simp only [rr_eq h ε] at he
      unfold rh
      have e : (fun y => SS μ K φ n0 ε x y * (rr μ K φ n0 ε y / Real.sqrt (Nn μ K φ n0 ε))) =
          fun y => Sc μ K (nε n0 φ ε) x y * rr μ K φ n0 ε y / Real.sqrt (Nn μ K φ n0 ε) := by
        funext y; unfold SS; ring
      rw [e, integral_div, he]
    nrm := by
      unfold rh
      have e : (fun y => rr μ K φ n0 ε y / Real.sqrt (Nn μ K φ n0 ε) *
          (rr μ K φ n0 ε y / Real.sqrt (Nn μ K φ n0 ε))) =
          fun y => rr μ K φ n0 ε y * rr μ K φ n0 ε y / Nn μ K φ n0 ε := by
        funext y; rw [div_mul_div_comm, Real.mul_self_sqrt hN.le]
      rw [e, integral_div]; exact div_self hN.ne'
    c0 := c3_pos h hμ hKs hk hKmin
    c_le := min_le_left _ _
    minor := fun x y => by
      have hr1 := rh_le h hμ ε hε1 x
      have hr2 := rh_le h hμ ε hε1 y
      have hp1 := (rlo3_pos h hμ).trans_le (rh_ge h hμ ε hε1 x)
      have hp2 := (rlo3_pos h hμ).trans_le (rh_ge h hμ ε hε1 y)
      have hrh := rhi3_pos h hμ
      have hal := Alo_pos h
      have hc := c3_pos h hμ hKs hk hKmin
      have h1 : c3 μ n0 κ C kmin * (rh μ K φ n0 ε x * rh μ K φ n0 ε y) ≤
          c3 μ n0 κ C kmin * (rhi3 μ n0 κ C * rhi3 μ n0 κ C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hr1 hr2 hp2.le hrh.le) hc.le
      have h2 : c3 μ n0 κ C kmin * (rhi3 μ n0 κ C * rhi3 μ n0 κ C) ≤ Alo n0 κ C * Alo n0 κ C * kmin := by
        have := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ)
          (Alo n0 κ C * Alo n0 κ C * kmin / (rhi3 μ n0 κ C * rhi3 μ n0 κ C)))
          (mul_pos hrh hrh).le
        unfold c3
        rwa [div_mul_cancel₀ _ (mul_pos hrh hrh).ne'] at this
      have h3 : Alo n0 κ C * Alo n0 κ C * kmin ≤ Aε μ K φ n0 ε x * K x y * Aε μ K φ n0 ε y := by
        have a1 := A_ge h ε hε1 x
        have a2 := A_ge h ε hε1 y
        calc Alo n0 κ C * Alo n0 κ C * kmin = Alo n0 κ C * kmin * Alo n0 κ C := by ring
          _ ≤ Aε μ K φ n0 ε x * K x y * Aε μ K φ n0 ε y :=
            mul_le_mul (mul_le_mul a1 (hKmin x y) hk.le (Aε_pos h ε x).le) a2 hal.le
              (mul_nonneg (Aε_pos h ε x).le (h.K0 x y))
      rw [hSeq]; linarith }

/-- The family hypotheses of Stage 2 hold on `|ε| < 1`. -/
theorem fHyp3 : FHyp μ (SS μ K φ n0) (SS' μ K φ n0) (rh μ K φ n0) (rh' μ K φ n0) 1
    (c3 μ n0 κ C kmin) (Aup n0 κ C * B * Aup n0 κ C) (rlo3 μ n0 κ C) (rhi3 μ n0 κ C)
    (2 * (AdB μ n0 κ B C * B * Aup n0 κ C)) (r'B3 μ n0 κ B C) where
  δ0 := one_pos
  D := dHyp3 h hμ hKs hk hKmin
  S'm := fun ε _ => by
    unfold SS'
    exact ((((meas_Ad h ε).comp measurable_fst).mul h.Km).mul ((meas_A h ε).comp measurable_snd)).add
      ((((meas_A h ε).comp measurable_fst).mul h.Km).mul ((meas_Ad h ε).comp measurable_snd))
  r'm := fun ε _ => by
    unfold rh' Nn' Nn
    exact (((meas_rr' h ε).mul_const _).sub ((meas_rr h ε).mul_const _)).div_const _
  S'B := fun ε hε x y => by
    have hε1 := ball1 h hε
    unfold SS'
    have hA1 := A_le h ε hε1 x
    have hA2 := A_le h ε hε1 y
    have hd1 := Ad_abs h ε hε1 x
    have hd2 := Ad_abs h ε hε1 y
    have hK := h.K0 x y
    have hKB := h.KB x y
    have hAp := Aε_pos h ε x
    have hAq := Aε_pos h ε y
    have hu := Aup_nonneg h
    have hdB := AdB_nonneg h
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos hAp, abs_of_pos hAq, abs_of_nonneg hK]
    have e1 : |Ad μ K φ n0 ε x| * K x y * Aε μ K φ n0 ε y ≤ AdB μ n0 κ B C * B * Aup n0 κ C :=
      mul_le_mul (mul_le_mul hd1 hKB hK hdB) hA2 hAq.le (mul_nonneg hdB h.B0)
    have e2 : Aε μ K φ n0 ε x * K x y * |Ad μ K φ n0 ε y| ≤ AdB μ n0 κ B C * B * Aup n0 κ C := by
      calc Aε μ K φ n0 ε x * K x y * |Ad μ K φ n0 ε y| ≤ Aup n0 κ C * B * AdB μ n0 κ B C :=
            mul_le_mul (mul_le_mul hA1 hKB hK hu) hd2 (abs_nonneg _) (mul_nonneg hu h.B0)
        _ = _ := by ring
    linarith
  r'B := fun ε hε x => rh'_abs h hμ ε (ball1 h hε) x
  Sd := fun ε hε x y => SS_hasDerivAt h hμ ε hε x y
  rd := fun ε hε x => rh_hasDerivAt h hμ ε hε x

/-- **Stage 3.** For the density-weighted kernel of `Hyp` with a symmetric kernel `K ≥ kmin > 0`:
for every family `d_j` of termwise derivatives at `0` of `S_ε^{(j)}(x,x)`, the series `Σ f_{j+1} d_j`
converges and is the derivative at `0` of `u(ε) = Σ' j, f_{j+1} S_ε^{(j)}(x,x)`. -/
theorem density_exchange (x : E) (d : ℕ → ℝ)
    (hd : ∀ j, HasDerivAt (fun ε => kpow μ (Sc μ K (nε n0 φ ε)) j x x) (d j) 0) :
    Summable (fun j => fc (j + 1) * d j) ∧
    HasDerivAt (fun ε => ∑' j, fc (j + 1) * kpow μ (Sc μ K (nε n0 φ ε)) j x x)
      (∑' j, fc (j + 1) * d j) 0 := by
  have hF := fHyp3 h hμ hKs hk hKmin
  have h0 : (0 : ℝ) ∈ ball (0 : ℝ) 1 := mem_ball_self one_pos
  have huniq : ∀ j, d j = 2 * (rh μ K φ n0 0 x * rh' μ K φ n0 0 x) +
      Dk μ (SS μ K φ n0) (SS' μ K φ n0) (rh μ K φ n0) (rh' μ K φ n0) 0 j x x := by
    intro j
    refine (hd j).unique ((hF.kpowS_hasDerivAt j 0 h0 x x).congr_deriv (by ring))
  have e : (fun j => fc (j + 1) * d j) = fun j => fc (j + 1) * (2 * (rh μ K φ n0 0 x * rh' μ K φ n0 0 x) +
      Dk μ (SS μ K φ n0) (SS' μ K φ n0) (rh μ K φ n0) (rh' μ K φ n0) 0 j x x) := by
    funext j; rw [huniq j]
  rw [e]
  exact hF.deriv_sum_kernels x

end Stage3

end CTG.DoeblinKernel

open MeasureTheory Filter Topology Metric Function
open CTG.DensityResponseCont CTG.DensityResponseCont.Trace CTG.DensityResponseCont.Local
open CTG.SqrtSeries CTG.DensityResponseSum CTG.Reals

namespace CTG.DoeblinKernel.Torus

/-- The torus kernel has a positive lower bound (continuous, positive, compact torus). -/
lemma heat_min {c : ℝ} (hc : 0 < c) (d : ℕ) :
    ∃ kmin : ℝ, 0 < kmin ∧ ∀ u : FlatTorus d, kmin ≤ heatTorus d c u := by
  obtain ⟨u0, -, hu0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (heatTorus_continuous hc d).continuousOn
  exact ⟨heatTorus d c u0, heatTorus_pos hc d u0, fun u => hu0 (Set.mem_univ u)⟩

/-- **Stage 4 (torus).** Kernel `heatTorus d c`, density `n_ε = n₀ e^{ε Re χ_n}`, `n ≠ 0`:
`u_ε(x) = Σ' j, f_{j+1} S_ε^{(j)}(x,x)` is differentiable at `0` with derivative
`(1 − t_n)² (Σ_m cl(t_m, t_{m+n})) Re χ_n(x)`, `t_m = e^{−c|m|²}`. No hypothesis beyond `c > 0`, `n₀ > 0`. -/
theorem torus_density_response {c : ℝ} (hc : 0 < c) (d : ℕ) {n : Fin d → ℤ} (hn : n ≠ 0)
    {n0 : ℝ} (hn0 : 0 < n0) (x : FlatTorus d) :
    HasDerivAt (fun ε => ∑' j, fc (j + 1) * kpow (flatTorusMeasure d)
        (Sc (flatTorusMeasure d) (fun x y => heatTorus d c (x - y))
          (nε n0 (fun y => (torusChar d n y).re) ε)) j x x)
      ((1 - ga c n) ^ 2 * (∑' m : Fin d → ℤ, cl (ga c m) (ga c (m + n))) * (torusChar d n x).re) 0 := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  set μ := flatTorusMeasure d
  have hcm : Measurable fun y : FlatTorus d => (torusChar d n y).re :=
    (Complex.continuous_re.comp (torusChar_continuous d n)).measurable
  have h : Hyp μ (fun x y => heatTorus d c (x - y)) (fun y => (torusChar d n y).re) n0 1
      ((1 + Real.sqrt (Real.pi / c)) ^ d) 1 :=
    { Km := (heatTorus_continuous hc d).measurable.comp measurable_sub
      K0 := fun x y => heatTorus_nonneg hc d _
      KB := fun x y => heatTorus_le hc d _
      φm := hcm
      φC := fun y => (Complex.abs_re_le_norm _).trans (torusChar_norm d n y).le
      C0 := zero_le_one
      B0 := by positivity
      n0pos := hn0
      κhom := fun x => by rw [conv_homogeneous μ (heatTorus d c) x]; exact heatTorus_mass hc d
      κpos := one_pos }
  have hμ : 0 < μ.real Set.univ := by simp [μ]
  obtain ⟨kmin, hk, hkmin⟩ := heat_min hc d
  have hKs : ∀ x y : FlatTorus d, heatTorus d c (x - y) = heatTorus d c (y - x) := fun x y => by
    rw [← heatTorus_even d c (x - y), neg_sub]
  have hd := fun j => kpow_diag_torus hc d n hn0 j x
  have hex := density_exchange h hμ hKs hk (fun x y => hkmin (x - y)) x _ hd
  have hsum := local_response_sum (d := d) hc hn
  have e : (∑' j, fc (j + 1) * ((1 - ga c n) ^ 2 * ((∑' m : Fin d → ℤ, ga (((j + 1 : ℕ) : ℝ) * c) m) +
        ∑ i ∈ Finset.range j, ∑' m, ga (((i + 1 : ℕ) : ℝ) * c) m * ga (((j - i : ℕ) : ℝ) * c) (m + n))
        * (torusChar d n x).re)) =
      (1 - ga c n) ^ 2 * (∑' m : Fin d → ℤ, cl (ga c m) (ga c (m + n))) * (torusChar d n x).re := by
    have e2 : (fun j => fc (j + 1) * ((1 - ga c n) ^ 2 * ((∑' m : Fin d → ℤ, ga (((j + 1 : ℕ) : ℝ) * c) m) +
        ∑ i ∈ Finset.range j, ∑' m, ga (((i + 1 : ℕ) : ℝ) * c) m * ga (((j - i : ℕ) : ℝ) * c) (m + n))
        * (torusChar d n x).re)) =
        fun j => ((1 - ga c n) ^ 2 * (torusChar d n x).re) * (fc (j + 1) * brk c n j) := by
      funext j; unfold brk; ring
    rw [e2, tsum_mul_left, hsum.tsum_eq]; ring
  rw [← e]
  exact hex.2

end CTG.DoeblinKernel.Torus
