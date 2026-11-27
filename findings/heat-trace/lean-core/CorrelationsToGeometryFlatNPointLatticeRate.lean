/-
Sixty-second file: a rate statement for the time derivative of the sampled operator, for the periodised Gaussian kernel
on the flat torus.  Namespace `CTG.FlatNPointLatticeRate`; imports the compiled module of the sixty-first file; check
with `./check_flat_npoint_lattice_rate.sh`.
`psiT_C11`, `psiLat_C11`: if the sample normalisations are at least `c` on the window, then `τ ↦ L_N f(i)` is `C^{1,1}`
there with constants WITHOUT powers of `N` (only powers of `ξ`).  `deriv_det'`, `flat_npoint_lattice_deriv_sharp`: the
derivative statement of the sixty-first file with this `N`-free constant `Mder` (the good event of the window statement
gives the normalisation bound for every time of the window).
`flat_npoint_lattice_deriv_rate`: with the choice `η₀ = etaStar` and `L = 5 log N`, under the single numerical condition
`92416 Λ¹⁴ · 5 log N ≤ N ξⁿ`, `p < q`, and the HYPOTHESIS that `a'` is Lipschitz: outside a set of (outer) probability at
most `32 Dder²/N²`, with `Dder` explicit and independent of `N`, for every `τ ∈ [p,q]` and every sample point the
derivative `∂_τ L_N f(i)` exists and `|∂_τ L_N f(i) − 2a'(τ) lapG f(X_i)/a(τ)³| ≤ 3E + 2ξ²C₂`, `E = C δ'/ξ` with
`δ' = √(5 log N/(N ξⁿ))`; also `|∂_τ L_N f − ∂_τ L_ξ f| ≤ 3E + 3ξ²C₂` and the difference-quotient inequalities for all
pairs of times of the window.  This is the form `C(δ'/ξ + ξ²)` of the derivative version of Proposition H.33
(`prop:dotLN`) on the flat torus for the periodised Gaussian kernel.
LIMITS: the constant `Dder` (hence the probability constant) is a large negative power of `ξ` (hand estimate of the
sub-task: of the order `ξ^{−O(n)}`), not evaluated; measurability of the exceptional set is not shown; flat torus,
conformal family, Gaussian kernel only; whether `ξ²C₂` is sharp is not addressed.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryFlatNPointLatticeDeriv

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss CTG.FlatNPointGaussFull
  CTG.FlatNPointGaussLattice CTG.FlatNPointLatticePop CTG.FlatNPointLatticeDirect
  CTG.FlatNPointClose CTG.FlatNPointWindow CTG.FlatNPointLatticeWindow CTG.FlatNPointLatticeDeriv

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointLatticeRate

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Stage 1: the sample operator as a C^{1,1} function of the time, on the good event -/

theorem C11_subset {U V : Set ℝ} {φ φ' : ℝ → ℝ} {B0 B1 B2 : ℝ} (h : C11 U φ φ' B0 B1 B2)
    (hVU : V ⊆ U) : C11 V φ φ' B0 B1 B2 :=
  ⟨fun s hs => h.deriv s (hVU hs), fun s hs => h.b0 s (hVU hs), fun s hs => h.b1 s (hVU hs),
    fun s hs t ht => h.lip s (hVU hs) t (hVU ht)⟩

variable {Ω : Type*}

/-- The sample normalisation of a kernel family `K τ` that is `C^{1,1}` in `τ` uniformly in the
two points. -/
theorem sampAvgT_C11 (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) {V : Set ℝ}
    {K K' : ℝ → E → E → ℝ} {G K1 K2 : ℝ}
    (hK : ∀ x z, C11 V (fun τ => K τ x z) (fun τ => K' τ x z) G K1 K2) (j : ℕ) :
    C11 V (fun τ => sampAvg X N (K τ) j ω)
      (fun τ => 1 / (N : ℝ) * ∑ l ∈ Finset.range N, K' τ (X j ω) (X l ω)) G K1 K2 := by
  have h := (C11.sum (Finset.range N) (F := fun l τ => K τ (X j ω) (X l ω))
    (F' := fun l τ => K' τ (X j ω) (X l ω))
    (fun l _ => hK (X j ω) (X l ω))).const_mul (1 / (N : ℝ))
  rw [avg_const hN, avg_const hN, avg_const hN] at h
  exact h.congr fun s => rfl

/-- The weighted sample average, given the lower bound `c` of the normalisations on `V`. -/
theorem sampWT_C11 (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) {V : Set ℝ} (hV : Convex ℝ V)
    {K K' : ℝ → E → E → ℝ} {G K1 K2 c : ℝ}
    (hK : ∀ x z, C11 V (fun τ => K τ x z) (fun τ => K' τ x z) G K1 K2) (hc : 0 < c)
    (hq : ∀ τ ∈ V, ∀ j < N, c ≤ sampAvg X N (K τ) j ω)
    (i : ℕ) (gf : E → E → ℝ) {Bg : ℝ} (hg : ∀ j, |gf (X i ω) (X j ω)| ≤ Bg) :
    ∃ D : ℝ → ℝ, C11 V (fun τ => sampW X N (K τ) gf i ω) D
      (tc0 G Bg c) (tc1 G K1 Bg c) (tc2 G K1 K2 Bg c) := by
  have hterm : ∀ j ∈ Finset.range N, C11 V
      (fun τ => K τ (X i ω) (X j ω) * gf (X i ω) (X j ω) * (1 / sampAvg X N (K τ) j ω))
      (fun τ => K' τ (X i ω) (X j ω) * gf (X i ω) (X j ω) * (1 / sampAvg X N (K τ) j ω)
        + K τ (X i ω) (X j ω) * gf (X i ω) (X j ω)
          * (-(1 / (N : ℝ) * ∑ l ∈ Finset.range N, K' τ (X j ω) (X l ω))
            / sampAvg X N (K τ) j ω ^ 2))
      (tc0 G Bg c) (tc1 G K1 Bg c) (tc2 G K1 K2 Bg c) := by
    intro j hj
    have hkg := (hK (X i ω) (X j ω)).mul_const (hg j)
    have hr := (sampAvgT_C11 X hN ω hK j).inv hV hc
      (fun s hs => hq s hs j (Finset.mem_range.1 hj))
    have hm := hkg.mul hV hr
    refine (hm.mono (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_)).congr fun s => rfl
    · unfold tc0; ring
    · unfold tc1; ring
    · unfold tc2; ring
  have h := (C11.sum (Finset.range N) hterm).const_mul (1 / (N : ℝ))
  rw [avg_const hN, avg_const hN, avg_const hN] at h
  exact ⟨_, h.congr fun s => rfl⟩

/-- **`τ ↦ L_N(τ) f(i)` is C^{1,1} on `V`** with constants `psiB0/1/2 G K1 K2 B c cD`, given the
lower bounds `c` of the normalisations and `cD` of the denominator on `V`. -/
theorem psiT_C11 (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) {V : Set ℝ} (hV : Convex ℝ V)
    {K K' : ℝ → E → E → ℝ} {G K1 K2 c cD m₂ ξ B : ℝ}
    (hK : ∀ x z, C11 V (fun τ => K τ x z) (fun τ => K' τ x z) G K1 K2) (hc : 0 < c) (hcD : 0 < cD)
    (hq : ∀ τ ∈ V, ∀ j < N, c ≤ sampAvg X N (K τ) j ω)
    {f : E → ℝ} (hB : ∀ y, |f y| ≤ B) (i : ℕ)
    (hD : ∀ τ ∈ V, cD ≤ sampW X N (K τ) (fun _ _ => 1) i ω) (hm₂ : 0 < m₂) (hξ : 0 < ξ) :
    ∃ D : ℝ → ℝ, C11 V (fun τ => LNK X N (K τ) m₂ ξ f i ω) D
      (psiB0 G K1 K2 B c cD m₂ ξ) (psiB1 G K1 K2 B c cD m₂ ξ) (psiB2 G K1 K2 B c cD m₂ ξ) := by
  obtain ⟨DN, hNum⟩ := sampWT_C11 X hN ω hV hK hc hq i (gd f)
    (fun j => gd_bound hB (X i ω) (X j ω))
  obtain ⟨DD, hDen⟩ := sampWT_C11 X hN ω hV hK hc hq i (fun _ _ => (1:ℝ)) (Bg := 1)
    (fun j => by simp)
  have hDi := hDen.inv hV hcD hD
  have hm := (hNum.mul hV hDi).const_mul (-(2 / (m₂ * ξ ^ 2)))
  have habs : |-(2 / (m₂ * ξ ^ 2))| = 2 / (m₂ * ξ ^ 2) := by
    rw [abs_neg, abs_of_pos (by positivity)]
  rw [habs] at hm
  refine ⟨_, (hm.mono (le_of_eq ?_) (le_of_eq ?_) (le_of_eq ?_)).congr fun s => ?_⟩
  · unfold psiB0; ring
  · unfold psiB1; ring
  · unfold psiB2; ring
  · unfold LNK; rw [div_eq_mul_one_div (sampW X N (K s) (gd f) i ω)]

/-- Constants of the lattice kernel in time. -/
def K1t (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (a₀ La : ℝ) : ℝ :=
  3 / a₀ * Gb n S a₀ * La
def K2t (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (a₀ La L₂ : ℝ) : ℝ :=
  18 / a₀ ^ 2 * Gb n S a₀ * La * La + 3 / a₀ * Gb n S a₀ * L₂

/-- **The lattice kernel `τ ↦ latK S (ξ/a(τ)) x z` is C^{1,1} on `ℝ`** (HYPOTHESIS `a'` Lipschitz). -/
theorem latT_C11 (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ)
    {a₀ a₁ La L₂ ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁)
    (hLa : ∀ τ, |a' τ| ≤ La) (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|) (hξ : 0 < ξ)
    (hξ1 : ξ ≤ 1) (x z : E) :
    C11 univ (fun τ => latK S (ξ / a τ) x z) (fun τ => kS1 S ξ x z (a τ) * a' τ)
      (Gb n S a₀) (K1t n S a₀ La) (K2t n S a₀ La L₂) := by
  have haC := a_C11 a a' hda ha₀ ha ha₁ hLa hL2
  have hG := Gb_pos S a₀ (n := n)
  have h := haC.comp (U := Icc a₀ a₁) convex_univ (fun τ _ => ⟨ha τ, ha₁ τ⟩)
    (kS_C11 S hξ hξ1 ha₀ x z) (by positivity)
  refine (h.mono le_rfl (le_of_eq ?_) (le_of_eq ?_)).congr fun τ => rfl
  · unfold K1t; ring
  · unfold K2t; ring

/-- The lower bound of the normalisation on the window gives the denominator bound `c/G`. -/
theorem den_lowerK (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E) (a : ℝ → ℝ)
    {a₀ ξ c τ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hc : 0 < c)
    (hq : ∀ j < N, c ≤ sampAvg X N (latK S (ξ / a τ)) j ω) {i : ℕ} (hi : i < N) :
    c / Gb n S a₀ ≤ sampW X N (latK S (ξ / a τ)) (fun _ _ => 1) i ω :=
  den_lower X hN (fun x z => (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).2.1)
    (fun x z => by have := (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).2.2; linarith) hc ω hq hi

/-- **Stage 1 for the lattice kernel**: on `V = Icc p q`, if all normalisations are `≥ c` there,
`τ ↦ L_N(τ) f(i)` is C^{1,1} with constants `psiB0/1/2 G K1t K2t B c (c/G)` (no power of `N`). -/
theorem psiLat_C11 (hn : 1 ≤ n) (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ ξ c B p q : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hc : 0 < c)
    (hq : ∀ τ ∈ Icc p q, ∀ j < N, c ≤ sampAvg X N (latK S (ξ / a τ)) j ω)
    {f : E → ℝ} (hB : ∀ y, |f y| ≤ B) {i : ℕ} (hi : i < N) :
    ∃ D : ℝ → ℝ, C11 (Icc p q) (fun τ => LNK X N (latK S (ξ / a τ)) (gam₂ n) ξ f i ω) D
      (psiB0 (Gb n S a₀) (K1t n S a₀ La) (K2t n S a₀ La L₂) B c (c / Gb n S a₀) (gam₂ n) ξ)
      (psiB1 (Gb n S a₀) (K1t n S a₀ La) (K2t n S a₀ La L₂) B c (c / Gb n S a₀) (gam₂ n) ξ)
      (psiB2 (Gb n S a₀) (K1t n S a₀ La) (K2t n S a₀ La L₂) B c (c / Gb n S a₀) (gam₂ n) ξ) := by
  have hG := Gb_pos S a₀ (n := n)
  exact psiT_C11 X hN ω (convex_Icc p q)
    (K := fun τ => latK S (ξ / a τ)) (K' := fun τ x z => kS1 S ξ x z (a τ) * a' τ)
    (fun x z => C11_subset (latT_C11 S a a' hda ha₀ ha ha₁ hLa hL2 hξ hξ1 x z) (subset_univ _))
    hc (by positivity) hq hB i
    (fun τ hτ => den_lowerK X hN ω S a ha₀ ha hξ hξ1 hc (hq τ hτ) hi) (gam₂_pos hn) hξ

/-! ### Stage 2: the derivative bound with an `N`-free Lipschitz constant -/

/-- The Lipschitz constant of `∂_τ (L_N f(i) + lapG/a²)` on the good event (no power of `N`). -/
def Mder (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a₀ a₁ La L₂ G₂ B ξ c : ℝ) : ℝ :=
  psiB2 (Gb n S a₀) (K1t n S a₀ La) (K2t n S a₀ La L₂) B c (c / Gb n S a₀) (gam₂ n) ξ
    + popB2 a₀ a₁ La L₂ G₂

theorem Mder_nonneg (hn : 1 ≤ n) (S : E ≃L[ℝ] E) {a₀ a₁ La L₂ G₂ B ξ c : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 ≤ a₁) (hLa : 0 ≤ La) (hL₂ : 0 ≤ L₂) (hG₂ : 0 ≤ G₂) (hB : 0 ≤ B) (hξ : 0 < ξ)
    (hc : 0 < c) : 0 ≤ Mder n S a₀ a₁ La L₂ G₂ B ξ c := by
  have hG := Gb_pos S a₀ (n := n)
  have hK1 : 0 ≤ K1t n S a₀ La := by unfold K1t; positivity
  have hK2 : 0 ≤ K2t n S a₀ La L₂ := by unfold K2t; positivity
  obtain ⟨-, h2⟩ := psiB_nonneg hG.le hK1 hK2 hB hc (by positivity : 0 < c / Gb n S a₀)
    (gam₂_pos hn) hξ
  have : 0 ≤ popB2 a₀ a₁ La L₂ G₂ := by unfold popB2; positivity
  unfold Mder; linarith

theorem DerivGood_mono {Ω : Type*} {X : ℕ → Ω → E} {N : ℕ} {S : E ≃L[ℝ] E} {a a' : ℝ → ℝ}
    {ξ : ℝ} {f : E → ℝ} {p q BII BII' C : ℝ} {i : ℕ} {ω : Ω}
    (h : DerivGood X N S a a' ξ f p q BII C i ω) (hle : BII ≤ BII') :
    DerivGood X N S a a' ξ f p q BII' C i ω := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun τ hτ => ?_, fun τa hτa τb hτb hne => ?_⟩
  · obtain ⟨D, hD, hb, DL, hDL, hb2⟩ := h1 τ hτ
    exact ⟨D, hD, hb.trans hle, DL, hDL, by linarith⟩
  · obtain ⟨u, v⟩ := h2 τa hτa τb hτb hne
    exact ⟨by linarith, by linarith⟩

set_option maxHeartbeats 1600000 in
/-- **Deterministic core with the `N`-free constant.**  As `deriv_det`, with the additional
hypothesis that all sample normalisations are `≥ c` on the whole window `[p,q]`; the Lipschitz
constant of the derivative is then `Mder … c` instead of `Mtot`. -/
theorem deriv_det' (hn : 1 ≤ n) (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (ω : Ω) {i : ℕ} (hi : i < N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ B G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (hper : Per f)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    {p q η₀ Er c : ℝ} (hη₀ : 0 < η₀) (hpq : 2 * η₀ ≤ q - p) (hc : 0 < c)
    (hq : ∀ τ ∈ Icc p q, ∀ j < N, c ≤ sampAvg X N (latK S (ξ / a τ)) j ω)
    (hwin : ∀ τa ∈ Icc p q, ∀ τb ∈ Icc p q, η₀ ≤ |τb - τa| →
      |dqIK X N S a ξ f τa τb i ω| ≤ 2 * Er
      ∧ |dqIIK X N S a ξ f τa τb i ω|
        ≤ 2 * Er + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
            (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (τb - τa)) :
    DerivGood X N S a a' ξ f p q
      (2 * Er + 2 * (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S)
        + Mder n S a₀ a₁ La L₂ G₂ B ξ c * η₀)
      (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) i ω := by
  have hm₂ := gam₂_pos hn
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have ha01 : a₀ ≤ a₁ := (ha 0).trans (ha₁ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hL₂ : 0 ≤ L₂ := by
    have := hL2 1 0; simp at this; exact le_trans (abs_nonneg _) this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hG₂0 : 0 ≤ G₂ := le_trans (abs_nonneg _) (hG₂ 0)
  have hk := radK_gauss (n := n)
  have hμ₄ : 0 ≤ gaμ₄ n := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hK₀ := hk.kern.mass_pos
  set C₂ := Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S with hC₂
  have hC2 : 0 ≤ C₂ := by rw [hC₂]; unfold Ctwo; positivity
  set Mt := Mder n S a₀ a₁ La L₂ G₂ B ξ c with hMt
  set L := lapG S f (X i ω) with hLdef
  obtain ⟨Ψ', hΨ⟩ := psiLat_C11 hn X hN ω S a a' hda ha₀ ha ha₁ hLa hL2 hξ hξ1 hc hq hB hi
  have hpop := C11_subset (pop_C11 a a' hda ha₀ ha ha₁ hLa hL2 (L := L) (hG₂ _))
    (subset_univ (Icc p q))
  have hF := hΨ.add hpop
  have hMt0 : 0 ≤ Mt :=
    Mder_nonneg hn S ha₀ (ha₀.le.trans ha01) hLa0 hL₂ hG₂0 hB0 hξ hc
  have hwinII : ∀ τa ∈ Icc p q, ∀ τb ∈ Icc p q, η₀ ≤ |τb - τa| →
      |((LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω + L / a τb ^ 2)
          - (LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω + L / a τa ^ 2)) / (τb - τa)|
        ≤ 2 * Er + 2 * (ξ ^ 2 * C₂) := by
    intro τa hτa τb hτb hη
    have h := (hwin τa hτa τb hτb hη).2
    rw [dqIIK_eq] at h
    have hpe : popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S) C₂ (τb - τa) ≤ ξ ^ 2 * C₂ := by
      unfold popErr; exact mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg ξ)
    exact h.trans (by linarith)
  have hlipF : ∀ s ∈ Icc p q, ∀ t ∈ Icc p q,
      |(Ψ' s + L * (-(a' s * a s + a s * a' s) / (a s * a s) ^ 2))
        - (Ψ' t + L * (-(a' t * a t + a t * a' t) / (a t * a t) ^ 2))| ≤ Mt * |s - t| := by
    intro s hs t ht
    have := hF.lip s hs t ht
    rw [hMt]; unfold Mder; exact this
  have hderII := deriv_from_window hη₀ hpq (fun τ hτ => hF.deriv τ hτ) hlipF hMt0 hwinII
  have hpopd : ∀ τ, L * (-(a' τ * a τ + a τ * a' τ) / (a τ * a τ) ^ 2)
      = -(2 * a' τ * L / a τ ^ 3) := fun τ => by
    have := (hpos τ).ne'; field_simp; ring
  have hD1 : ∀ τ ∈ Icc p q, |Ψ' τ - 2 * a' τ * L / a τ ^ 3|
      ≤ 2 * Er + 2 * (ξ ^ 2 * C₂) + Mt * η₀ := fun τ hτ => by
    have := hderII τ hτ
    rw [hpopd τ] at this
    rwa [show Ψ' τ + -(2 * a' τ * L / a τ ^ 3) = Ψ' τ - 2 * a' τ * L / a τ ^ 3 by ring] at this
  have hdot : ∀ τ, ∃ DL, HasDerivAt (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) DL τ
      ∧ |DL - 2 * a' τ * L / a τ ^ 3| ≤ ξ ^ 2 * C₂ := fun τ =>
    dotL_flat_full hk hm₂ hf hper hM hM₄ S a a' hda ha₀ ha hLa hξ (X i ω) τ
  have hDI : ∀ τ ∈ Icc p q, ∀ DL, |DL - 2 * a' τ * L / a τ ^ 3| ≤ ξ ^ 2 * C₂ →
      |Ψ' τ - DL| ≤ 2 * Er + 2 * (ξ ^ 2 * C₂) + Mt * η₀ + ξ ^ 2 * C₂ := by
    intro τ hτ DL hDL
    have h1 := hD1 τ hτ
    calc |Ψ' τ - DL|
        = |(Ψ' τ - 2 * a' τ * L / a τ ^ 3) - (DL - 2 * a' τ * L / a τ ^ 3)| := by
          congr 1; ring
      _ ≤ |Ψ' τ - 2 * a' τ * L / a τ ^ 3| + |DL - 2 * a' τ * L / a τ ^ 3| := abs_sub _ _
      _ ≤ _ := add_le_add h1 hDL
  refine ⟨fun τ hτ => ⟨Ψ' τ, hΨ.deriv τ hτ, hD1 τ hτ, ?_⟩,
    fun τa hτa τb hτb hne => ⟨?_, ?_⟩⟩
  · obtain ⟨DL, hDL, hb⟩ := hdot τ
    exact ⟨DL, hDL, hDI τ hτ DL hb⟩
  · rw [dqIK_eq]
    refine slope_le (F := fun τ => LNK X N (latK S (ξ / a τ)) (gam₂ n) ξ f i ω
        - Lmet gauss (gam₂ n) S (a τ) ξ f (X i ω))
      (F' := fun τ => Ψ' τ - deriv (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) τ)
      (fun τ hτ => ?_) (fun τ hτ => ?_) hτa hτb hne
    · obtain ⟨DL, hDL, -⟩ := hdot τ
      show HasDerivAt _ (Ψ' τ - deriv (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) τ) τ
      rw [hDL.deriv]
      exact (hΨ.deriv τ hτ).sub hDL
    · obtain ⟨DL, hDL, hb⟩ := hdot τ
      show |Ψ' τ - deriv (fun t => Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) τ| ≤ _
      rw [hDL.deriv]
      exact hDI τ hτ DL hb
  · rw [dqIIK_eq]
    refine slope_le (F := fun τ => LNK X N (latK S (ξ / a τ)) (gam₂ n) ξ f i ω + L / a τ ^ 2)
      (fun τ hτ => hF.deriv τ hτ) (fun τ hτ => ?_) hτa hτb hne
    exact hderII τ hτ

set_option maxHeartbeats 1600000 in
/-- **The time derivative on one event for a whole window, with an `N`-free Lipschitz constant.**
Hypotheses of `flat_npoint_lattice_deriv`; outside the same exceptional set (outer measure, same
probability bound), for every `i < N` the conclusion `DerivGood` holds with
`BII = 2E + 2ξ²C₂ + Mder … (P₀ξⁿ/4) · η₀`. -/
theorem flat_npoint_lattice_deriv_sharp (hn : 1 ≤ n) {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * L ≤ N * ξ ^ n)
    {p q w η₀ : ℝ} (hw : 0 < w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀) (hpq : 2 * η₀ ≤ q - p)
    (hwc : cIk a₀ a₁ La * Gb n S a₀ * w ≤ P0c S a₁ * ξ ^ n / 4)
    (hwE : 4 * (LsK n S a₀ a₁ La Lip ξ (P0c S a₁ * ξ ^ n / 4)
            + (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * w
          ≤ rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ * η₀) :
    μ.real {ω | ∃ i < N, ¬ DerivGood X N S a a' ξ f p q
        (2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ
          + 2 * (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S)
          + Mder n S a₀ a₁ La L₂ G₂ B ξ (P0c S a₁ * ξ ^ n / 4) * η₀)
        (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) i ω}
      ≤ ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) * (N * (2 * Real.exp (-L)))
        + ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
  classical
  have hN0 : 0 < N := by omega
  have hd := dS_pos S
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < P0c S a₁ * ξ ^ n := by unfold P0c; positivity
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hk := radK_gauss (n := n)
  have hm₂ := gam₂_pos hn
  have hμ₄ : 0 ≤ gaμ₄ n := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hK₀ := hk.kern.mass_pos
  have hC2 : 0 ≤ Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S := by unfold Ctwo; positivity
  have hcIG0 : 0 ≤ cIk a₀ a₁ La * Gb n S a₀ := by
    have := Gb_pos S a₀ (n := n); unfold cIk; positivity
  set Kg := ⌊(q - p) / w⌋₊ with hKg
  set T := grid p w Kg with hT
  set Er := rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ with hEr
  set C₁ := Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S with hC₁
  set C₂ := Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S with hC₂
  set Pairs : Finset (ℝ × ℝ) := (T ×ˢ T).filter fun pr => pr.2 ≠ pr.1 with hPairs
  have hcardT : (T.card : ℝ) ≤ (Kg : ℝ) + 1 := by exact_mod_cast grid_card_le p w Kg
  have hcardP : (Pairs.card : ℝ) ≤ ((Kg : ℝ) + 1) ^ 2 := by
    have h1 : Pairs.card ≤ (Kg + 1) ^ 2 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, sq]
      exact Nat.mul_le_mul (grid_card_le p w Kg) (grid_card_le p w Kg)
    exact_mod_cast h1
  have hsub : {ω | ∃ i < N, ¬ DerivGood X N S a a' ξ f p q
        (2 * Er + 2 * (ξ ^ 2 * C₂) + Mder n S a₀ a₁ La L₂ G₂ B ξ (P0c S a₁ * ξ ^ n / 4) * η₀)
        C₂ i ω}
      ⊆ (⋃ g ∈ T, {ω | ∃ j < N, sampAvg X N (latK S (ξ / a g)) j ω < P0c S a₁ * ξ ^ n / 2})
        ∪ (⋃ pr ∈ Pairs, badLK X N S a ξ f pr.1 pr.2 Er C₁ C₂) := by
    intro ω hω
    by_contra hnot
    rw [mem_union, not_or] at hnot
    obtain ⟨hn', hr⟩ := hnot
    obtain ⟨i, hi, hfail⟩ := hω
    apply hfail
    have hnorm : ∀ g ∈ T, ∀ j < N,
        P0c S a₁ * ξ ^ n / 2 ≤ sampAvg X N (latK S (ξ / a g)) j ω := by
      intro g hg j hj
      by_contra hlt
      exact hn' (Set.mem_iUnion₂.2 ⟨g, hg, ⟨j, hj, not_le.1 hlt⟩⟩)
    have hrate : ∀ ga ∈ T, ∀ gb ∈ T, gb ≠ ga → ∀ i < N,
        |dqIK X N S a ξ f ga gb i ω| ≤ Er
        ∧ |dqIIK X N S a ξ f ga gb i ω| ≤ Er + popErr ξ C₁ C₂ (gb - ga) := by
      intro ga hga gb hgb hne i hi
      by_contra hcon
      exact hr (Set.mem_iUnion₂.2 ⟨(ga, gb),
        Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hga, hgb⟩, hne⟩, ⟨i, hi, hcon⟩⟩)
    have hq : ∀ τ ∈ Icc p q, ∀ j < N,
        P0c S a₁ * ξ ^ n / 4 ≤ sampAvg X N (latK S (ξ / a τ)) j ω := by
      intro τ hτ j hj
      obtain ⟨g, hg, hτg⟩ := grid_cover hw hτ
      exact sampAvgK_transfer X hN0 S a a' hda ha₀ ha ha₁ hLa hξ hξ1
        ((mul_le_mul_of_nonneg_left hτg hcIG0).trans hwc) j ω (hnorm g hg j hj)
    refine deriv_det' hn X hN0 ω hi hf hM hM₄ hper hB S hG₂ a a' hda ha₀ ha ha₁ hLa hL2 hξ hξ1
      hη₀ hpq (by positivity) hq (fun τa hτa τb hτb hη => ?_)
    obtain ⟨w1, w2⟩ := window_detK X hN0 hn hf hM hM₄ hper hLip0 hLip S hG₂ a a' hda ha₀ ha ha₁
      hLa hξ hξ1 hc hw.le hη₀ h4 hwc T (fun τ hτ => grid_cover hw hτ) ω hnorm hrate
      hτa hτb hη hi
    have hE1 := (div_le_iff₀ hη₀).2 hwE
    have hE2 : 4 * (LsK n S a₀ a₁ La Lip ξ (P0c S a₁ * ξ ^ n / 4) + G₂ * (2 * La / a₀ ^ 3)) * w / η₀
        ≤ 4 * (LsK n S a₀ a₁ La Lip ξ (P0c S a₁ * ξ ^ n / 4)
            + (ξ ^ 2 * C₂ + G₂ * (2 * La / a₀ ^ 3))) * w / η₀ := by
      refine div_le_div_of_nonneg_right ?_ hη₀.le
      have := mul_nonneg (mul_nonneg (sq_nonneg ξ) hC2) hw.le
      linarith
    exact ⟨by linarith, by linarith⟩
  have hexp : 0 ≤ (N : ℝ) * (2 * Real.exp (-L)) := by positivity
  have h1 : μ.real (⋃ g ∈ T, {ω | ∃ j < N, sampAvg X N (latK S (ξ / a g)) j ω
            < P0c S a₁ * ξ ^ n / 2})
      ≤ ((Kg : ℝ) + 1) * (N * (2 * Real.exp (-L))) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ g ∈ T, μ.real {ω | ∃ j < N, sampAvg X N (latK S (ξ / a g)) j ω
            < P0c S a₁ * ξ ^ n / 2}
        ≤ ∑ g ∈ T, (N * (2 * Real.exp (-L))) := Finset.sum_le_sum fun g _ =>
          normK_event X h_indep hX hlaw N hN S a ha₀ ha ha₁ hξ hξ1 g hL1 hNL
      _ = T.card * (N * (2 * Real.exp (-L))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Kg : ℝ) + 1) * (N * (2 * Real.exp (-L))) := mul_le_mul_of_nonneg_right hcardT hexp
  have h2 : μ.real (⋃ pr ∈ Pairs, badLK X N S a ξ f pr.1 pr.2 Er C₁ C₂)
      ≤ ((Kg : ℝ) + 1) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc ∑ pr ∈ Pairs, μ.real (badLK X N S a ξ f pr.1 pr.2 Er C₁ C₂)
        ≤ ∑ pr ∈ Pairs, (15 * (N * (2 * Real.exp (-L)))) := Finset.sum_le_sum fun pr hpr =>
          rateK_L hn X h_indep hX hlaw N hN hf hM hM₄ hper hLip0 hLip hB S a a' hda
            ha₀ ha ha₁ hLa hξ hξ1 pr.1 pr.2 (Finset.mem_filter.1 hpr).2 hL1 hNL
      _ = Pairs.card * (15 * (N * (2 * Real.exp (-L)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Kg : ℝ) + 1) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) :=
          mul_le_mul_of_nonneg_right hcardP (by positivity)
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add h1 h2))

/-! ### Stage 3: choice of `η₀`, grid width and `L = 5 log N` -/

/-- The minimal separation `η₀* = min((q − p)/2, E/(M + 1))`. -/
def etaStar (p q Er Md : ℝ) : ℝ := min ((q - p) / 2) (Er / (Md + 1))

/-- The explicit constant of the `1/N²` form of the derivative statement; independent of `N`.
`c = P₀ξⁿ`, `BI = cI·G`, `Ls = LsumK …`, `Md = Mder …`. -/
def Dder (p q c BI Ls m₂ Md : ℝ) : ℝ :=
  1 + max (q - p) 0 * (4 * (2 / (q - p)) + 4 * ((Md + 1) * (m₂ / 7320000)) + 4 * (BI + 1) / c
    + 4 * (Ls + 1) * (m₂ / 7320000) * (2 / (q - p) + (Md + 1) * (m₂ / 7320000)))

theorem etaStar_props {p q Er Md : ℝ} (hpq : p < q) (hEr : 0 < Er) (hMd : 0 ≤ Md) :
    0 < etaStar p q Er Md ∧ 2 * etaStar p q Er Md ≤ q - p ∧ Md * etaStar p q Er Md ≤ Er
      ∧ 1 / etaStar p q Er Md ≤ 2 / (q - p) + (Md + 1) * (1 / Er) := by
  have h1 : 0 < (q - p) / 2 := by linarith
  have h2 : 0 < Er / (Md + 1) := div_pos hEr (by linarith)
  refine ⟨lt_min h1 h2, ?_, ?_, ?_⟩
  · have := min_le_left ((q - p) / 2) (Er / (Md + 1)); unfold etaStar; linarith
  · have hle : etaStar p q Er Md ≤ Er / (Md + 1) := min_le_right _ _
    have hm : Md * etaStar p q Er Md ≤ Md * (Er / (Md + 1)) := mul_le_mul_of_nonneg_left hle hMd
    have e : Md * (Er / (Md + 1)) = Er - Er / (Md + 1) := by field_simp; ring
    linarith
  · unfold etaStar
    refine (inv_min_le h1 h2).trans (le_of_eq ?_)
    rw [one_div_div, one_div_div]; field_simp

/-- Abstract arithmetic: `iw ≤ coef · s²` from the three inverse bounds. -/
theorem count_core {iw iη iE α γ Md Ls C s : ℝ} (hs1 : 1 ≤ s) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ)
    (hMd : 0 ≤ Md) (hLs : 0 ≤ Ls) (hC : 0 ≤ C) (hiη0 : 0 ≤ iη)
    (hiw : iw ≤ 4 * iη + C + 4 * (Ls + 1) * (iE * iη))
    (hiη : iη ≤ α + (Md + 1) * iE) (hiE : iE ≤ γ * s) :
    iw ≤ (4 * α + 4 * ((Md + 1) * γ) + C + 4 * (Ls + 1) * γ * (α + (Md + 1) * γ)) * (s * s) := by
  have hM1 : 0 ≤ Md + 1 := by linarith
  have h1 : iη ≤ α + (Md + 1) * γ * s := by
    have := mul_le_mul_of_nonneg_left hiE hM1; linarith
  have h2 : iE * iη ≤ (γ * s) * (α + (Md + 1) * γ * s) :=
    mul_le_mul hiE h1 hiη0 (by positivity)
  have hL : 0 ≤ 4 * (Ls + 1) := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hL
  have hs0 : 0 ≤ s := by linarith
  have hss1 : 1 ≤ s * s := by nlinarith
  have hss2 : s ≤ s * s := by nlinarith
  have e1 : 4 * α ≤ 4 * α * (s * s) := by nlinarith
  have e2 : 4 * ((Md + 1) * γ) * s ≤ 4 * ((Md + 1) * γ) * (s * s) :=
    mul_le_mul_of_nonneg_left hss2 (by positivity)
  have e3 : C ≤ C * (s * s) := by nlinarith
  have e4 : 4 * (Ls + 1) * γ * α * s ≤ 4 * (Ls + 1) * γ * α * (s * s) :=
    mul_le_mul_of_nonneg_left hss2 (by positivity)
  nlinarith

/-- The explicit form needed below. -/
theorem count_le {N : ℕ} (hN : 1 ≤ N) {p q w η Er c BI Ls m₂ Md : ℝ} (hpq : p < q) (hw : 0 < w)
    (hc : 0 < c) (hBI : 0 ≤ BI) (hLs : 0 ≤ Ls) (hm₂ : 0 < m₂) (hMd : 0 ≤ Md) (hEr : 0 < Er)
    (hη : 0 < η)
    (hwinv : 1 / w ≤ 4 / η + 4 * (BI + 1) / c + 4 * (Ls + 1) / (Er * η))
    (hηinv : 1 / η ≤ 2 / (q - p) + (Md + 1) * (1 / Er))
    (hEinv : 1 / Er ≤ m₂ * Real.sqrt N / 7320000) :
    ((⌊(q - p) / w⌋₊ : ℕ) : ℝ) + 1 ≤ Dder p q c BI Ls m₂ Md * N := by
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hN'
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
  have hα0 : 0 ≤ 2 / (q - p) := div_nonneg zero_le_two (by linarith)
  have hγ0 : 0 ≤ m₂ / 7320000 := by positivity
  have hC : 0 ≤ 4 * (BI + 1) / c := by positivity
  have hiE : 1 / Er ≤ m₂ / 7320000 * Real.sqrt N := by
    have e : m₂ * Real.sqrt N / 7320000 = m₂ / 7320000 * Real.sqrt N := by ring
    linarith
  have hiw : 1 / w ≤ 4 * (1 / η) + 4 * (BI + 1) / c + 4 * (Ls + 1) * ((1 / Er) * (1 / η)) := by
    have e1 : 4 / η = 4 * (1 / η) := by ring
    have e2 : 4 * (Ls + 1) / (Er * η) = 4 * (Ls + 1) * ((1 / Er) * (1 / η)) := by
      field_simp
    linarith
  have hk := count_core hs1 hα0 hγ0 hMd hLs hC (by positivity) hiw hηinv hiE
  rw [hss] at hk
  have hfl := floor_succ_le (x := q - p) hw
  have hmx : max (q - p) 0 = q - p := max_eq_left (by linarith)
  rw [hmx] at hfl
  have hcoef0 : 0 ≤ 4 * (2 / (q - p)) + 4 * ((Md + 1) * (m₂ / 7320000)) + 4 * (BI + 1) / c
      + 4 * (Ls + 1) * (m₂ / 7320000) * (2 / (q - p) + (Md + 1) * (m₂ / 7320000)) := by
    positivity
  have h2 := mul_le_mul_of_nonneg_left hk (by linarith : (0:ℝ) ≤ q - p)
  unfold Dder
  rw [hmx]
  have h3 : 0 ≤ (q - p) * (4 * (2 / (q - p)) + 4 * ((Md + 1) * (m₂ / 7320000))
      + 4 * (BI + 1) / c
      + 4 * (Ls + 1) * (m₂ / 7320000) * (2 / (q - p) + (Md + 1) * (m₂ / 7320000))) :=
    mul_nonneg (by linarith) hcoef0
  nlinarith

set_option maxHeartbeats 3200000 in
/-- **Rate statement for the time derivative of the flat N-point operator (periodised Gaussian
kernel), without free parameters.**  Setting of `flat_npoint_lattice_window_N2` with
`L = 5 log N`, a window `p < q`, a bound `M₂` for `‖D²f‖` (used through `G₂ = n‖S‖²M₂`), and the
HYPOTHESIS that `a'` is `L₂`-Lipschitz.  Outside an event of (outer) probability at most
`32 Dder²/N²` (`Dder` explicit, independent of `N`), for every `i < N`: the conclusion `DerivGood`
holds with `BII = 3E + 2ξ²C₂`, `E = rateE n Λ m₂ (5 log N) N ξ`; in particular for every
`τ ∈ [p,q]` the derivative `∂_τ L_N f(i)` exists and
`|∂_τ L_N f(i) − 2a'(τ) lapG f(X_i)/a(τ)³| ≤ 3E + 2ξ²C₂`. -/
theorem flat_npoint_lattice_deriv_rate (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B M₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B) (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La L₂ ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hL2 : ∀ s t, |a' s - a' t| ≤ L₂ * |s - t|)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * (5 * Real.log N) ≤ N * ξ ^ n)
    {p q : ℝ} (hpq : p < q) :
    μ.real {ω | ∃ i < N, ¬ DerivGood X N S a a' ξ f p q
        (3 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) (5 * Real.log N) N ξ
          + 2 * (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S))
        (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) i ω}
      ≤ 32 * Dder p q (P0c S a₁ * ξ ^ n) (cIk a₀ a₁ La * Gb n S a₀)
          (LsumK n S a₀ a₁ La Lip ξ M₄ M₂) (gam₂ n)
          (Mder n S a₀ a₁ La L₂ (Gtwo S M₂) B ξ (P0c S a₁ * ξ ^ n / 4)) ^ 2 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlog2 := Real.log_two_gt_d9
  have hL1 : 1 ≤ 5 * Real.log N := by linarith
  have hm₂ := gam₂_pos hn
  have hd := dS_pos S
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < P0c S a₁ * ξ ^ n := by unfold P0c; positivity
  have hM20 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hL₂ : 0 ≤ L₂ := by
    have := hL2 1 0; simp at this; exact le_trans (abs_nonneg _) this
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hBI0 : 0 ≤ cIk a₀ a₁ La * Gb n S a₀ := by
    have := Gb_pos S a₀ (n := n); unfold cIk; positivity
  have hΛ1 := (dLam_bounds S a₀ a₁ La Lip).1
  have hΛ : 0 < dLam S a₀ a₁ La Lip := lt_of_lt_of_le one_pos hΛ1
  set Er := rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) (5 * Real.log N) N ξ with hErd
  have hEr : 0 < Er := rateE_pos hΛ hm₂ (by linarith) hN0 hξ
  set Ls := LsumK n S a₀ a₁ La Lip ξ M₄ M₂ with hLsd
  have hLs : 0 ≤ Ls := LsumK_nonneg hn S ha₀ ha₁0 hLa0 hLip0 hξ hM₄ hM20
  set c := P0c S a₁ * ξ ^ n with hcd
  set BI := cIk a₀ a₁ La * Gb n S a₀ with hBId
  set Md := Mder n S a₀ a₁ La L₂ (Gtwo S M₂) B ξ (c / 4) with hMdd
  have hMd : 0 ≤ Md := Mder_nonneg hn S ha₀ ha₁0.le hLa0 hL₂ (Gtwo_nonneg S hM20) hB0 hξ
    (by positivity)
  set η := etaStar p q Er Md with hηd
  obtain ⟨hη0, hηpq, hMη, hηinv⟩ := etaStar_props hpq hEr hMd
  set w := wStar η c BI Er Ls with hwd
  obtain ⟨hw, h4, hwc, hwE⟩ := wStar_props hη0 hc hBI0 hEr hLs
  have H := flat_npoint_lattice_deriv_sharp hn X h_indep hX hlaw N hN hf hM hM₄ hper hLip0 hLip
    hB S (lapG_bound S hM₂) a a' hda ha₀ ha ha₁ hLa hL2 hξ hξ1 hL1 hNL hw hη0 h4 hηpq hwc hwE
  have hsub : {ω | ∃ i < N, ¬ DerivGood X N S a a' ξ f p q
        (3 * Er + 2 * (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S))
        (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) i ω}
      ⊆ {ω | ∃ i < N, ¬ DerivGood X N S a a' ξ f p q
        (2 * Er + 2 * (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) + Md * η)
        (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) i ω} := by
    intro ω hω
    obtain ⟨i, hi, hfail⟩ := hω
    exact ⟨i, hi, fun hg => hfail (DerivGood_mono hg (by linarith))⟩
  refine (measureReal_mono hsub).trans (H.trans ?_)
  set K1 : ℝ := ((⌊(q - p) / w⌋₊ : ℕ) : ℝ) + 1 with hK1
  set D := Dder p q c BI Ls (gam₂ n) Md with hDd
  have hK1D : K1 ≤ D * N := by
    have h3 := rateE_lower (n := n) hΛ1 hm₂ hL1 hN0 hξ hξ1 (m₂ := gam₂ n)
    rw [← hErd] at h3
    exact count_le (by omega) hpq hw hc hBI0 hLs hm₂ hMd hEr hη0
      (one_div_wStar_le hη0 hc hBI0 hEr hLs) hηinv h3
  have hK10 : 1 ≤ K1 := by
    rw [hK1]; have := Nat.cast_nonneg (α := ℝ) ⌊(q - p) / w⌋₊; linarith
  have hexp : (N : ℝ) * (2 * Real.exp (-(5 * Real.log N))) = 2 / (N : ℝ) ^ 4 := by
    rw [Real.exp_neg, show (5:ℝ) * Real.log N = ((5:ℕ):ℝ) * Real.log N by norm_num,
      Real.exp_nat_mul, Real.exp_log hN']
    field_simp
  rw [hexp]
  have hK1sq : K1 ^ 2 ≤ D ^ 2 * (N : ℝ) ^ 2 := by
    have hD0 : 0 ≤ D * N := le_trans (by linarith) hK1D
    calc K1 ^ 2 ≤ (D * N) ^ 2 := pow_le_pow_left₀ (by linarith) hK1D 2
      _ = D ^ 2 * (N : ℝ) ^ 2 := by ring
  have hX0 : 0 ≤ 2 / (N : ℝ) ^ 4 := by positivity
  calc K1 * (2 / (N : ℝ) ^ 4) + K1 ^ 2 * (15 * (2 / (N : ℝ) ^ 4))
      ≤ 16 * K1 ^ 2 * (2 / (N : ℝ) ^ 4) := by
        have hk : K1 ≤ K1 ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right hk hX0
        nlinarith
    _ ≤ 16 * (D ^ 2 * (N : ℝ) ^ 2) * (2 / (N : ℝ) ^ 4) := by gcongr
    _ = 32 * D ^ 2 / (N : ℝ) ^ 2 := by field_simp; ring

end CTG.FlatNPointLatticeRate
