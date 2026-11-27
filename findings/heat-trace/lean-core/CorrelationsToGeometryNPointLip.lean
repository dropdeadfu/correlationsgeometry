/-
Nineteenth file: Steps 2–5 of `prop:dotLN-diff` with a LIPSCHITZ test function, namespace
`CTG.NPointLip`.  Builds on `CorrelationsToGeometryNPointSharp.lean` (compiled module
`.tools/leanbuild/CorrelationsToGeometryNPointSharp.olean`); check with `./check_npoint_lip.sh`.
Stages: (a) test kernel `g(x,y) = f(y) − f(x)` with `|f(y) − f(x)| ≤ Lip·d_τ(x,y)`; L¹/L² profile
bounds with the extra factor `d/ξ`, so every test-kernel constant carries a factor `ξ` (`ξ²` for the
second moments); (b) `step5g` / `npoint_step5_lip` / `npoint_step5_lip_sharp`: error `ξ·C·δ'`;
(c) `npoint_step5_lip_norm`: after division by `c_h ξ²/2`, error `(2/c_h)·C·δ'/ξ`;
(d) `npoint_step5_lip_geom_log`: geometry hypotheses discharged, `L = 3 log N`, probability
`1 − 30/N²`.  NOT formalised: Step 6 (comparison with the Laplace–Beltrami operator), uniformity in the
two times, measurability of the exceptional sets; `c_h` is a free parameter; constants are crude.
No `sorry`, no `axiom`, no `native_decide`; remaining assumptions are hypotheses.
Written by a sub-task of an AI session on 26 November 2026.
-/
import CorrelationsToGeometryNPointSharp

open Set MeasureTheory ProbabilityTheory
open CTG.NPoint CTG.NPointSharp

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

/-! ### A130 part 1: abstract layer with a test kernel that has its own template constants -/

namespace CTG.NPointLip

/-- Homogeneity of the Bernstein threshold: `dev(ξB, ξ²v) = ξ dev(B, v)` for `ξ ≥ 0`. -/
theorem dev_scale (N : ℕ) {ξ B v B' v' L : ℝ} (hξ : 0 ≤ ξ) (hB : B' = ξ * B)
    (hv : v' = ξ ^ 2 * v) : dev N B' v' L = ξ * dev N B v L := by
  subst hB hv
  unfold dev
  have e : Real.sqrt (N * (ξ ^ 2 * v) * L) = ξ * Real.sqrt (N * v * L) := by
    rw [show (N:ℝ) * (ξ ^ 2 * v) * L = ξ ^ 2 * (N * v * L) by ring,
      Real.sqrt_mul (sq_nonneg ξ), Real.sqrt_sq hξ]
  rw [e]; ring

/-- Error of the weighted average at one time, for a test kernel `F = K g` with its own template
constants `B_F, v_F` and `L¹` bound `M_F`. -/
def errTg (N : ℕ) (BK vK c L MF BF vF : ℝ) : ℝ :=
  err1 N BK vK c L * (MF + dev N BF vF L) + dev N (BF * (1 / c)) ((1 / c) ^ 2 * vF) L

/-- Error of the difference quotient of the weighted average, with the constants of
`F = K_a g`, `F_I = Δ_ηK g`. -/
def errDg (N : ℕ) (BK vK BI vI MI c L MF BF vF MFi BFi vFi : ℝ) : ℝ :=
  err1 N BK vK c L * (MFi + dev N BFi vFi L)
    + err2' N BK vK BI vI MI c L * (MF + dev N BF vF L)
    + dev N (BFi * (1 / c) + BF * (MI / c ^ 2))
        (2 * ((1 / c) ^ 2 * vFi) + 2 * ((MI / c ^ 2) ^ 2 * vF)) L

/-- Exceptional event of Steps 3/4 for the test kernel. -/
def bad34g {E : Type*} [MeasurableSpace E] {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (m : Measure E)
    (Ka Kb g : E → E → ℝ) (η MI c L BF vF BFi vFi : ℝ) : Set Ω :=
  badSet X N m (fun x z => |Ka x z * g x z|) BF vF L
    ∪ badSet X N m (fun x z => |Kb x z * g x z|) BF vF L
    ∪ badSet X N m (fun x z => |(Kb x z - Ka x z) / η * g x z|) BFi vFi L
    ∪ badSet X N m (wKer m Ka g) (BF * (1 / c)) ((1 / c) ^ 2 * vF) L
    ∪ badSet X N m (wKer m Kb g) (BF * (1 / c)) ((1 / c) ^ 2 * vF) L
    ∪ badSet X N m (dKer m Ka Kb g η) (BFi * (1 / c) + BF * (MI / c ^ 2))
        (2 * ((1 / c) ^ 2 * vFi) + 2 * ((MI / c ^ 2) ^ 2 * vF)) L

/-- Final error of Step 5 for the test kernel (the denominator parts are those of `err5'`). -/
def err5g (N : ℕ) (BK vK BI vI M MI c L MF BF vF MFi BFi vFi cD : ℝ) : ℝ :=
  let a := errTg N BK vK c L MF BF vF + errDg N BK vK BI vI MI c L MF BF vF MFi BFi vFi
  let ε := errT' N BK vK M c L 1 / cD
  let ε' := errD' N BK vK BI vI M MI c L 1
  let B := MF * (1 / c) + (MFi * (1 / c) + MF * (MI / c ^ 2))
  let C := 1 * MI * (1 / c) + 1 * M * (MI / c ^ 2)
  2 * a / cD + 2 * B * ε / cD + 4 * (a * (C + ε') + B * ε') / cD ^ 2 + 6 * B * C * ε / cD ^ 2

/-- **Homogeneity of the final error** in the test-kernel constants: scaling `B_F, M_F, B_{F_I},
M_{F_I}` by `ξ` and `v_F, v_{F_I}` by `ξ²` scales `err5g` by `ξ`. -/
theorem err5g_scale (N : ℕ) {BK vK BI vI M MI c L MF BF vF MFi BFi vFi cD ξ : ℝ} (hξ : 0 ≤ ξ) :
    err5g N BK vK BI vI M MI c L (ξ * MF) (ξ * BF) (ξ ^ 2 * vF) (ξ * MFi) (ξ * BFi) (ξ ^ 2 * vFi) cD
      = ξ * err5g N BK vK BI vI M MI c L MF BF vF MFi BFi vFi cD := by
  have d1 : dev N (ξ * BF) (ξ ^ 2 * vF) L = ξ * dev N BF vF L := dev_scale N hξ rfl rfl
  have d2 : dev N (ξ * BF * (1 / c)) ((1 / c) ^ 2 * (ξ ^ 2 * vF)) L
      = ξ * dev N (BF * (1 / c)) ((1 / c) ^ 2 * vF) L := dev_scale N hξ (by ring) (by ring)
  have d3 : dev N (ξ * BFi) (ξ ^ 2 * vFi) L = ξ * dev N BFi vFi L := dev_scale N hξ rfl rfl
  have d4 : dev N (ξ * BFi * (1 / c) + ξ * BF * (MI / c ^ 2))
      (2 * ((1 / c) ^ 2 * (ξ ^ 2 * vFi)) + 2 * ((MI / c ^ 2) ^ 2 * (ξ ^ 2 * vF))) L
      = ξ * dev N (BFi * (1 / c) + BF * (MI / c ^ 2))
          (2 * ((1 / c) ^ 2 * vFi) + 2 * ((MI / c ^ 2) ^ 2 * vF)) L :=
    dev_scale N hξ (by ring) (by ring)
  simp only [err5g, errTg, errDg]
  rw [d1, d2, d3, d4]
  ring

section AbstractLip

variable {E : Type*} [MeasurableSpace E] {m : Measure E} [IsProbabilityMeasure m]

/-- The six kernels of Steps 3/4 with the template constants of the test kernel. -/
theorem goods34g (Ka Kb g : E → E → ℝ) (η : ℝ) {BK vK BI vI c MI BF vF BFi vFi : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (GFa : Good m (fun x z => Ka x z * g x z) BF vF)
    (GFb : Good m (fun x z => Kb x z * g x z) BF vF)
    (GFi : Good m (fun x z => (Kb x z - Ka x z) / η * g x z) BFi vFi) :
    Good m (fun x z => |Ka x z * g x z|) BF vF
    ∧ Good m (fun x z => |Kb x z * g x z|) BF vF
    ∧ Good m (fun x z => |(Kb x z - Ka x z) / η * g x z|) BFi vFi
    ∧ Good m (wKer m Ka g) (BF * (1 / c)) ((1 / c) ^ 2 * vF)
    ∧ Good m (wKer m Kb g) (BF * (1 / c)) ((1 / c) ^ 2 * vF)
    ∧ Good m (dKer m Ka Kb g η) (BFi * (1 / c) + BF * (MI / c ^ 2))
        (2 * ((1 / c) ^ 2 * vFi) + 2 * ((MI / c ^ 2) ^ 2 * vF)) := by
  have hc1 : (0 : ℝ) ≤ 1 / c := by positivity
  have hWm : Measurable fun p : E × E => (1 / popAvg m Kb p.2 - 1 / popAvg m Ka p.2) / η :=
    ((inv_pop_meas Kb GKb.meas).sub (inv_pop_meas Ka GKa.meas)).div_const η
  refine ⟨GFa.abs, GFb.abs, GFi.abs,
    GFa.mul (fun _ z => 1 / popAvg m Ka z) (inv_pop_meas Ka GKa.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Ka hc hpa z),
    GFb.mul (fun _ z => 1 / popAvg m Kb z) (inv_pop_meas Kb GKb.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Kb hc hpb z), ?_⟩
  exact (GFi.mul (fun _ z => 1 / popAvg m Kb z) (inv_pop_meas Kb GKb.meas) (1 / c) hc1
      (fun x z => inv_pop_bd Kb hc hpb z)).add
    (GFa.mul (fun _ z => (1 / popAvg m Kb z - 1 / popAvg m Ka z) / η) hWm (MI / c ^ 2)
      (by positivity)
      (fun x z => W_bd' Ka Kb GKa GKb GKi hc hpa hpb hMI0 hMI z))

end AbstractLip

section AssemblyLip

variable {E : Type*} [MeasurableSpace E] {m : Measure E} [IsProbabilityMeasure m]

/-- Steps 3 and 4, deterministic part, for a test kernel with its own template constants and
`L¹` bounds. -/
theorem step34_det_g {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (hN : 0 < N) (Ka Kb g : E → E → ℝ)
    (η : ℝ) {BK vK BI vI c L MI MF BF vF MFi BFi vFi : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (GFa : Good m (fun x z => Ka x z * g x z) BF vF)
    (GFb : Good m (fun x z => Kb x z * g x z) BF vF)
    (GFi : Good m (fun x z => (Kb x z - Ka x z) / η * g x z) BFi vFi)
    (hMFa : ∀ x, ∫ z, |Ka x z * g x z| ∂m ≤ MF) (hMFb : ∀ x, ∫ z, |Kb x z * g x z| ∂m ≤ MF)
    (hMFi : ∀ x, ∫ z, |(Kb x z - Ka x z) / η * g x z| ∂m ≤ MFi)
    (hsmall : dev N BK vK L / c ≤ 1 / 2) (ω : Ω)
    (h2 : ω ∉ bad2 X N m Ka Kb η BK vK BI vI L)
    (h34 : ω ∉ bad34g X N m Ka Kb g η MI c L BF vF BFi vFi) (i : ℕ) (hi : i < N) :
    |sampW X N Ka g i ω - popW m Ka g (X i ω)| ≤ errTg N BK vK c L MF BF vF
    ∧ |sampW X N Kb g i ω - popW m Kb g (X i ω)| ≤ errTg N BK vK c L MF BF vF
    ∧ |(sampW X N Kb g i ω - sampW X N Ka g i ω) / η
        - (popW m Kb g (X i ω) - popW m Ka g (X i ω)) / η|
          ≤ errDg N BK vK BI vI MI c L MF BF vF MFi BFi vFi := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ :=
    goods34g Ka Kb g η GKa GKb GKi hc hpa hpb hMI0 hMI GFa GFb GFi
  simp only [bad2, bad34g, mem_union, not_or] at h2 h34
  obtain ⟨⟨hKa, hKb⟩, hKi⟩ := h2
  obtain ⟨⟨⟨⟨⟨b1, b1b⟩, b2⟩, b3a⟩, b3b⟩, b4⟩ := h34
  have hBK := GKa.B_nonneg; have hvK := GKa.v_nonneg
  have hBI := GKi.B_nonneg; have hvI := GKi.v_nonneg
  have heQ := dev_nonneg N hBK hvK hL.le
  have he1 : 0 ≤ err1 N BK vK c L := by unfold err1; positivity
  have he2 : 0 ≤ err2' N BK vK BI vI MI c L := by
    unfold err2'; have := dev_nonneg N hBI hvI hL.le; positivity
  have wa : ∀ j < N, |1 / sampAvg X N Ka j ω - 1 / popAvg m Ka (X j ω)| ≤ err1 N BK vK c L :=
    fun j hj => (inv_close _ _ _ c hc (hpa _) heQ hsmall (not_badSet hKa hj)).2
  have wb : ∀ j < N, |1 / sampAvg X N Kb j ω - 1 / popAvg m Kb (X j ω)| ≤ err1 N BK vK c L :=
    fun j hj => (inv_close _ _ _ c hc (hpb _) heQ hsmall (not_badSet hKb hj)).2
  have wΔ : ∀ j < N, |(1 / sampAvg X N Kb j ω - 1 / sampAvg X N Ka j ω) / η
      - (1 / popAvg m Kb (X j ω) - 1 / popAvg m Ka (X j ω)) / η|
        ≤ err2' N BK vK BI vI MI c L := by
    intro j hj
    have hΔ := not_badSet hKi hj
    rw [sampAvg_inc, ← popAvg_inc' Ka Kb GKa GKb η] at hΔ
    have hB : |(popAvg m Kb (X j ω) - popAvg m Ka (X j ω)) / η| ≤ MI := by
      rw [popAvg_inc' Ka Kb GKa GKb η]
      exact (popAvg_abs_le_L1 (m := m) _ _).trans (hMI _)
    exact inv_inc_perturb _ _ _ _ η _ _ c MI hc (hpa _) (hpb _) heQ hsmall hMI0
      (not_badSet hKa hj) (not_badSet hKb hj) hΔ hB
  have P1a : popAvg m (fun x z => |Ka x z * g x z|) (X i ω) ≤ MF := hMFa _
  have P1b : popAvg m (fun x z => |Kb x z * g x z|) (X i ω) ≤ MF := hMFb _
  have P1i : popAvg m (fun x z => |(Kb x z - Ka x z) / η * g x z|) (X i ω) ≤ MFi := hMFi _
  have hdF := dev_nonneg N G1.B_nonneg G1.v_nonneg hL.le
  have hdFi := dev_nonneg N G2.B_nonneg G2.v_nonneg hL.le
  refine ⟨?_, ?_, ?_⟩
  · have h := weighted_det N hN (fun j => Ka (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Ka j ω) (fun j => 1 / popAvg m Ka (X j ω)) _ _ _ _ _ he1 wa
      (not_badSet b1 hi) (not_badSet b3a hi)
    refine h.trans ?_
    unfold errTg
    gcongr
  · have h := weighted_det N hN (fun j => Kb (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Kb j ω) (fun j => 1 / popAvg m Kb (X j ω)) _ _ _ _ _ he1 wb
      (not_badSet b1b hi) (not_badSet b3b hi)
    refine h.trans ?_
    unfold errTg
    gcongr
  · rw [sampW_inc]
    have hpop : (popW m Kb g (X i ω) - popW m Ka g (X i ω)) / η
        = popAvg m (dKer m Ka Kb g η) (X i ω) := by
      rw [dKer_eq]
      exact (popAvg_inc m (wKer m Ka g) (wKer m Kb g) G3a.meas G3b.meas G3a.bd G3b.bd η
        (X i ω)).symm
    rw [hpop]
    have h := weighted2_det N hN
      (fun j => (Kb (X i ω) (X j ω) - Ka (X i ω) (X j ω)) / η * g (X i ω) (X j ω))
      (fun j => Ka (X i ω) (X j ω) * g (X i ω) (X j ω))
      (fun j => 1 / sampAvg X N Kb j ω) (fun j => 1 / popAvg m Kb (X j ω))
      (fun j => (1 / sampAvg X N Kb j ω - 1 / sampAvg X N Ka j ω) / η)
      (fun j => (1 / popAvg m Kb (X j ω) - 1 / popAvg m Ka (X j ω)) / η)
      _ _ _ _ _ _ _ _ he1 he2 wb wΔ (not_badSet b2 hi) (not_badSet b1 hi) (not_badSet b4 hi)
    refine h.trans ?_
    unfold errDg
    gcongr

theorem bad34g_prob {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb g : E → E → ℝ) (η : ℝ)
    {BK vK BI vI MI c L BF vF BFi vFi : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (GFa : Good m (fun x z => Ka x z * g x z) BF vF)
    (GFb : Good m (fun x z => Kb x z * g x z) BF vF)
    (GFi : Good m (fun x z => (Kb x z - Ka x z) / η * g x z) BFi vFi) :
    μ.real (bad34g X N m Ka Kb g η MI c L BF vF BFi vFi) ≤ 6 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ :=
    goods34g Ka Kb g η GKa GKb GKi hc hpa hpb hMI0 hMI GFa GFb GFi
  have p := fun {F : E → E → ℝ} {B v : ℝ} (hG : Good m F B v) =>
    hG.prob X h_indep hX hlaw N hN hL
  unfold bad34g
  refine (measureReal_union_le _ _).trans ?_
  refine (add_le_add (measureReal_union_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl)
    le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add (measureReal_union_le _ _) le_rfl)
    le_rfl) le_rfl) le_rfl).trans ?_
  linarith [p G1, p G1b, p G2, p G3a, p G3b, p G4]

/-- Population bounds of the weighted average of the test kernel and of its difference quotient,
through the `L¹` bounds `M_F`, `M_{F_I}`. -/
theorem popW_bd_g (Ka Kb g : E → E → ℝ) (η : ℝ) {BK vK BI vI c MI MF BF vF MFi BFi vFi : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (GFa : Good m (fun x z => Ka x z * g x z) BF vF)
    (GFb : Good m (fun x z => Kb x z * g x z) BF vF)
    (GFi : Good m (fun x z => (Kb x z - Ka x z) / η * g x z) BFi vFi)
    (hMFa : ∀ x, ∫ z, |Ka x z * g x z| ∂m ≤ MF)
    (hMFi : ∀ x, ∫ z, |(Kb x z - Ka x z) / η * g x z| ∂m ≤ MFi) (x : E) :
    |popW m Ka g x| ≤ MF * (1 / c)
    ∧ |(popW m Kb g x - popW m Ka g x) / η| ≤ MFi * (1 / c) + MF * (MI / c ^ 2) := by
  obtain ⟨G1, G1b, G2, G3a, G3b, G4⟩ :=
    goods34g Ka Kb g η GKa GKb GKi hc hpa hpb hMI0 hMI GFa GFb GFi
  have hc1 : (0:ℝ) ≤ 1 / c := by positivity
  constructor
  · have h := popAvg_comb_le (m := m) (wKer m Ka g) (fun x z => Ka x z * g x z)
      (fun x z => Ka x z * g x z) G3a GFa GFa hc1 (le_refl 0) hMFa hMFa (fun x z => by
        show |Ka x z * g x z * (1 / popAvg m Ka z)|
          ≤ 1 / c * |Ka x z * g x z| + 0 * |Ka x z * g x z|
        rw [abs_mul (Ka x z * g x z) (1 / popAvg m Ka z), zero_mul, add_zero]
        have := inv_pop_bd Ka hc hpa z
        calc |Ka x z * g x z| * |1 / popAvg m Ka z| ≤ |Ka x z * g x z| * (1 / c) :=
              mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = 1 / c * |Ka x z * g x z| := mul_comm _ _) x
    refine h.trans (le_of_eq ?_)
    ring
  · have hpop : (popW m Kb g x - popW m Ka g x) / η = popAvg m (dKer m Ka Kb g η) x := by
      rw [dKer_eq]
      exact (popAvg_inc m (wKer m Ka g) (wKer m Kb g) G3a.meas G3b.meas G3a.bd G3b.bd η x).symm
    rw [hpop]
    have h := popAvg_comb_le (m := m) (dKer m Ka Kb g η)
      (fun x z => (Kb x z - Ka x z) / η * g x z) (fun x z => Ka x z * g x z)
      G4 GFi GFa hc1 (by positivity : 0 ≤ MI / c ^ 2) hMFi hMFa
      (fun x z => by
        show |(Kb x z - Ka x z) / η * g x z * (1 / popAvg m Kb z)
            + Ka x z * g x z * ((1 / popAvg m Kb z - 1 / popAvg m Ka z) / η)|
          ≤ 1 / c * |(Kb x z - Ka x z) / η * g x z| + MI / c ^ 2 * |Ka x z * g x z|
        have w1 := inv_pop_bd Kb hc hpb z
        have w2 := W_bd' Ka Kb GKa GKb GKi hc hpa hpb hMI0 hMI z
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul ((Kb x z - Ka x z) / η * g x z) (1 / popAvg m Kb z),
          abs_mul (Ka x z * g x z) ((1 / popAvg m Kb z - 1 / popAvg m Ka z) / η)]
        have e1 : |(Kb x z - Ka x z) / η * g x z| * |1 / popAvg m Kb z|
            ≤ |(Kb x z - Ka x z) / η * g x z| * (1 / c) :=
          mul_le_mul_of_nonneg_left w1 (abs_nonneg _)
        have e2 : |Ka x z * g x z| * |(1 / popAvg m Kb z - 1 / popAvg m Ka z) / η|
            ≤ |Ka x z * g x z| * (MI / c ^ 2) :=
          mul_le_mul_of_nonneg_left w2 (abs_nonneg _)
        linarith [mul_comm (|(Kb x z - Ka x z) / η * g x z|) (1 / c),
          mul_comm (|Ka x z * g x z|) (MI / c ^ 2)]) x
    refine h.trans (le_of_eq ?_)
    ring

theorem errTg_nonneg' (N : ℕ) {BK vK c L MF BF vF : ℝ} (hBK : 0 ≤ BK) (hvK : 0 ≤ vK)
    (hc : 0 < c) (hL : 0 ≤ L) (hMF : 0 ≤ MF) (hBF : 0 ≤ BF) (hvF : 0 ≤ vF) :
    0 ≤ errTg N BK vK c L MF BF vF := by
  unfold errTg err1
  have := dev_nonneg N hBK hvK hL
  have := dev_nonneg N hBF hvF hL
  have := dev_nonneg N (by positivity : 0 ≤ BF * (1 / c)) (by positivity : 0 ≤ (1 / c) ^ 2 * vF) hL
  positivity

theorem errDg_nonneg' (N : ℕ) {BK vK BI vI MI c L MF BF vF MFi BFi vFi : ℝ} (hBK : 0 ≤ BK)
    (hvK : 0 ≤ vK) (hBI : 0 ≤ BI) (hvI : 0 ≤ vI) (hMI : 0 ≤ MI) (hc : 0 < c) (hL : 0 ≤ L)
    (hMF : 0 ≤ MF) (hBF : 0 ≤ BF) (hvF : 0 ≤ vF) (hMFi : 0 ≤ MFi) (hBFi : 0 ≤ BFi)
    (hvFi : 0 ≤ vFi) :
    0 ≤ errDg N BK vK BI vI MI c L MF BF vF MFi BFi vFi := by
  unfold errDg err1 err2'
  have := dev_nonneg N hBK hvK hL
  have := dev_nonneg N hBI hvI hL
  have := dev_nonneg N hBF hvF hL
  have := dev_nonneg N hBFi hvFi hL
  have := dev_nonneg N (by positivity : 0 ≤ BFi * (1 / c) + BF * (MI / c ^ 2))
    (by positivity : 0 ≤ 2 * ((1 / c) ^ 2 * vFi) + 2 * ((MI / c ^ 2) ^ 2 * vF)) hL
  positivity

/-- **Steps 2–5 for a test kernel with its own template constants.**  As
`CTG.NPointSharp.step5'`, but the numerator kernels `K_a g`, `K_b g`, `Δ_ηK g` carry their own
HYPOTHESES (`Good` and `L¹` bounds) in place of `|g| ≤ B_g`. -/
theorem step5g {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N) (Ka Kb gf : E → E → ℝ) (η : ℝ)
    {BK vK BI vI c L cD M MI MF BF vF MFi BFi vFi : ℝ}
    (GKa : Good m Ka BK vK) (GKb : Good m Kb BK vK)
    (GKi : Good m (fun x z => (Kb x z - Ka x z) / η) BI vI) (hc : 0 < c) (hL : 0 < L)
    (hpa : ∀ y, c ≤ popAvg m Ka y) (hpb : ∀ y, c ≤ popAvg m Kb y)
    (hM0 : 0 ≤ M) (hMa : ∀ x, ∫ z, |Ka x z| ∂m ≤ M) (hMb : ∀ x, ∫ z, |Kb x z| ∂m ≤ M)
    (hMI0 : 0 ≤ MI) (hMI : ∀ x, ∫ z, |(Kb x z - Ka x z) / η| ∂m ≤ MI)
    (GFa : Good m (fun x z => Ka x z * gf x z) BF vF)
    (GFb : Good m (fun x z => Kb x z * gf x z) BF vF)
    (GFi : Good m (fun x z => (Kb x z - Ka x z) / η * gf x z) BFi vFi)
    (hMF0 : 0 ≤ MF) (hMFa : ∀ x, ∫ z, |Ka x z * gf x z| ∂m ≤ MF)
    (hMFb : ∀ x, ∫ z, |Kb x z * gf x z| ∂m ≤ MF)
    (hMFi0 : 0 ≤ MFi) (hMFi : ∀ x, ∫ z, |(Kb x z - Ka x z) / η * gf x z| ∂m ≤ MFi)
    (hcD : 0 < cD) (hDa : ∀ x, cD ≤ popW m Ka (fun _ _ => 1) x)
    (hDb : ∀ x, cD ≤ popW m Kb (fun _ _ => 1) x)
    (hsmall : dev N BK vK L / c ≤ 1 / 2) (hsmallD : errT' N BK vK M c L 1 / cD ≤ 1 / 2) :
    μ.real {ω | ∃ i < N, err5g N BK vK BI vI M MI c L MF BF vF MFi BFi vFi cD
        < |(sampW X N Kb gf i ω / sampW X N Kb (fun _ _ => 1) i ω
              - sampW X N Ka gf i ω / sampW X N Ka (fun _ _ => 1) i ω) / η
          - (popW m Kb gf (X i ω) / popW m Kb (fun _ _ => 1) (X i ω)
              - popW m Ka gf (X i ω) / popW m Ka (fun _ _ => 1) (X i ω)) / η|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  set g1 : E → E → ℝ := fun _ _ => 1
  have hg1 : Measurable fun p : E × E => g1 p.1 p.2 := measurable_const
  have hg1b : ∀ x z, |g1 x z| ≤ 1 := fun x z => by simp [g1]
  have hsub : {ω | ∃ i < N, err5g N BK vK BI vI M MI c L MF BF vF MFi BFi vFi cD
        < |(sampW X N Kb gf i ω / sampW X N Kb g1 i ω
              - sampW X N Ka gf i ω / sampW X N Ka g1 i ω) / η
          - (popW m Kb gf (X i ω) / popW m Kb g1 (X i ω)
              - popW m Ka gf (X i ω) / popW m Ka g1 (X i ω)) / η|}
      ⊆ bad2 X N m Ka Kb η BK vK BI vI L ∪ bad34g X N m Ka Kb gf η MI c L BF vF BFi vFi
        ∪ bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1 := by
    intro ω ⟨i, hi, hlt⟩
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨h2, h34f⟩, h341⟩ := hcon
    obtain ⟨eNa, -, eΔN⟩ := step34_det_g X N hN Ka Kb gf η GKa GKb GKi hc hL hpa hpb
      hMI0 hMI GFa GFb GFi hMFa hMFb hMFi hsmall ω h2 h34f i hi
    obtain ⟨eDa, eDb, eΔD⟩ := step34_det' X N hN Ka Kb g1 η GKa GKb GKi hc hL hpa hpb hMa hMb
      hMI0 hMI hg1 zero_le_one hg1b hsmall ω h2 h341 i hi
    obtain ⟨bn, bx⟩ := popW_bd_g Ka Kb gf η GKa GKb GKi hc hpa hpb hMI0 hMI GFa GFb GFi hMFa
      hMFi (X i ω)
    obtain ⟨-, by'⟩ := popW_bd' Ka Kb g1 η GKa GKb GKi hc hpa hpb hMa hMI0 hMI hg1 zero_le_one
      hg1b (X i ω)
    have hBK := GKa.B_nonneg; have hBI := GKi.B_nonneg
    have hvK := GKa.v_nonneg; have hvI := GKi.v_nonneg
    have hT1 := Ctx.errT'_nonneg N hBK hvK hc hL.le zero_le_one hM0
    have hD1 := Ctx.errD'_nonneg N hBK hvK hBI hvI hc hL.le zero_le_one hM0 hMI0
    have hTf := errTg_nonneg' N hBK hvK hc hL.le hMF0 GFa.B_nonneg GFa.v_nonneg
    have hDf := errDg_nonneg' N hBK hvK hBI hvI hMI0 hc hL.le hMF0 GFa.B_nonneg GFa.v_nonneg
      hMFi0 GFi.B_nonneg GFi.v_nonneg
    set a := errTg N BK vK c L MF BF vF + errDg N BK vK BI vI MI c L MF BF vF MFi BFi vFi
      with ha
    set ε := errT' N BK vK M c L 1 / cD with hε
    set ε' := errD' N BK vK BI vI M MI c L 1 with hε'
    set B := MF * (1 / c) + (MFi * (1 / c) + MF * (MI / c ^ 2)) with hB
    set C := 1 * MI * (1 / c) + 1 * M * (MI / c ^ 2) with hC
    have hrel : ∀ (Dv dv : ℝ), cD ≤ dv → |Dv - dv| ≤ errT' N BK vK M c L 1 →
        |Dv - dv| ≤ ε * dv :=
      fun Dv dv hdv h => by
        refine h.trans ?_
        rw [hε, div_mul_eq_mul_div, le_div_iff₀ hcD]
        exact mul_le_mul_of_nonneg_left hdv hT1
    have hda := hDa (X i ω); have hdb := hDb (X i ω)
    have rDa := hrel _ _ hda eDa; have rDb := hrel _ _ hdb eDb
    have hεnn : 0 ≤ ε := div_nonneg hT1 hcD.le
    obtain ⟨hDa0, -, -⟩ := CTG.Reals2.TimeAppendix4.inv_perturb _ _ cD ε hcD hda hεnn hsmallD rDa
    obtain ⟨hDb0, -, -⟩ := CTG.Reals2.TimeAppendix4.inv_perturb _ _ cD ε hcD hdb hεnn hsmallD rDb
    have hda0 : 0 < popW m Ka g1 (X i ω) := lt_of_lt_of_le hcD hda
    have hdb0 : 0 < popW m Kb g1 (X i ω) := lt_of_lt_of_le hcD hdb
    have hq := CTG.Reals2.TimeAppendix4.quotient_dq_perturb
      ((sampW X N Kb gf i ω - sampW X N Ka gf i ω) / η)
      ((popW m Kb gf (X i ω) - popW m Ka gf (X i ω)) / η)
      (sampW X N Ka gf i ω) (popW m Ka gf (X i ω))
      ((sampW X N Kb g1 i ω - sampW X N Ka g1 i ω) / η)
      ((popW m Kb g1 (X i ω) - popW m Ka g1 (X i ω)) / η)
      (sampW X N Ka g1 i ω) (popW m Ka g1 (X i ω))
      (sampW X N Kb g1 i ω) (popW m Kb g1 (X i ω)) a B C cD ε ε' hcD hda hdb hεnn hsmallD
      (by positivity) (by positivity) (by positivity) hD1 rDa rDb
      (eΔN.trans (by linarith)) (eNa.trans (by linarith)) eΔD
      (bx.trans (by have : 0 ≤ MF * (1 / c) := by positivity
                    linarith))
      (bn.trans (by have : 0 ≤ MFi * (1 / c) + MF * (MI / c ^ 2) := by positivity
                    linarith))
      by'
    rw [← CTG.Reals2.TimeAppendix4.dq_quotient _ _ _ _ η hDa0.ne' hDb0.ne',
      ← CTG.Reals2.TimeAppendix4.dq_quotient _ _ _ _ η hda0.ne' hdb0.ne'] at hq
    have : err5g N BK vK BI vI M MI c L MF BF vF MFi BFi vFi cD
        = 2 * a / cD + 2 * B * ε / cD + 4 * (a * (C + ε') + B * ε') / cD ^ 2
          + 6 * B * C * ε / cD ^ 2 := rfl
    rw [this] at hlt
    linarith
  calc μ.real _ ≤ μ.real (bad2 X N m Ka Kb η BK vK BI vI L
        ∪ bad34g X N m Ka Kb gf η MI c L BF vF BFi vFi
        ∪ bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real (bad2 X N m Ka Kb η BK vK BI vI L ∪ bad34g X N m Ka Kb gf η MI c L BF vF BFi vFi)
        + μ.real (bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1) := measureReal_union_le _ _
    _ ≤ (μ.real (bad2 X N m Ka Kb η BK vK BI vI L)
          + μ.real (bad34g X N m Ka Kb gf η MI c L BF vF BFi vFi))
        + μ.real (bad34' X N m Ka Kb g1 η BK vK BI vI MI c L 1) :=
        add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ 3 * (N * (2 * Real.exp (-L))) + 6 * (N * (2 * Real.exp (-L)))
        + 6 * (N * (2 * Real.exp (-L))) := by
        linarith [bad2_prob X h_indep hX hlaw N hN Ka Kb η GKa GKb GKi hL,
          bad34g_prob X h_indep hX hlaw N hN Ka Kb gf η GKa GKb GKi hc hL hpa hpb hMI0 hMI
            GFa GFb GFi,
          bad34'_prob X h_indep hX hlaw N hN Ka Kb g1 η GKa GKb GKi hc hL hpa hpb hMI0 hMI hg1
            zero_le_one hg1b]
    _ = 15 * (N * (2 * Real.exp (-L))) := by ring

end AssemblyLip

end CTG.NPointLip
/-! ### A130 part 2: arithmetic of the test-kernel errors -/

namespace CTG.NPointLip

variable {N : ℕ} {Λ x y δ L : ℝ}

theorem bracketF_le (C : Ctx N Λ x y δ L) {B v MM : ℝ} (hB : 0 ≤ B) (hB' : B ≤ Λ)
    (hv : 0 ≤ v) (hv' : v ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MM) (hM : MM ≤ Λ * x) :
    MM + dev N B v L ≤ 9 * Λ ^ 2 * x := by
  have h := C.bracket'_le hB hB' hv hv' zero_le_one C.hΛ hM0 hM
  simpa only [one_mul, mul_one, one_pow] using h

theorem errTg_le (C : Ctx N Λ x y δ L) {A vK c MF BF vF : ℝ} (hA : 0 ≤ A) (hA' : A ≤ Λ)
    (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y)
    (hB : 0 ≤ BF) (hB' : BF ≤ Λ) (hw : 0 ≤ vF) (hw' : vF ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MF)
    (hM : MF ≤ Λ * x) :
    errTg N A vK c L MF BF vF ≤ 152 * Λ ^ 5 * δ := by
  unfold errTg
  have he1 := C.err1_le hA hA' hv hv' hc hci
  have hbr := bracketF_le C hB hB' hw hw' hM0 hM
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have hy := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hbr0 : 0 ≤ MF + dev N BF vF L := by have := dev_nonneg N hB hw hL0; positivity
  have hB2 : BF * (1 / c) ≤ Λ ^ 3 * y := by
    rw [one_div]
    have h1 : BF * c⁻¹ ≤ Λ * (Λ * y) := by gcongr
    have h2 : Λ * (Λ * y) = Λ ^ 2 * y := by ring
    have h3 : Λ ^ 2 * y ≤ Λ ^ 3 * y :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ C.hΛ (by norm_num)) hy.le
    linarith
  have hv2 : (1 / c) ^ 2 * vF * x ≤ (Λ ^ 3) ^ 2 := by
    rw [one_div]
    have h1 : c⁻¹ ^ 2 * vF * x ≤ (Λ * y) ^ 2 * (Λ ^ 2 * x) * x := by gcongr
    have e : (Λ * y) ^ 2 * (Λ ^ 2 * x) * x = Λ ^ 4 := by
      linear_combination (Λ ^ 4 * (x * y + 1)) * C.hxy
    have m : Λ ^ 4 ≤ (Λ ^ 3) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_right₀ C.hΛ (by norm_num)
    linarith
  have hd2 := dev_le' N C.hN (by positivity : 0 ≤ BF * (1 / c))
    (by positivity : 0 ≤ (1 / c) ^ 2 * vF) C.hL C.hx C.hδ0 C.hδ hB2 (by positivity) hv2
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [C.hδ1]
  have h3 : 6 * (Λ ^ 3 * y) * x * δ ^ 2 ≤ 6 * Λ ^ 3 * δ := by
    have e : 6 * (Λ ^ 3 * y) * x * δ ^ 2 = 6 * Λ ^ 3 * δ ^ 2 := by
      linear_combination (6 * Λ ^ 3 * δ ^ 2) * C.hxy
    rw [e]; have : 0 ≤ Λ ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hδ2 this
    linarith
  have hprod : err1 N A vK c L * (MF + dev N BF vF L)
      ≤ (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) := mul_le_mul he1 hbr hbr0 (by positivity)
  have e3 : (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) = 144 * (Λ ^ 5 * δ) := by
    linear_combination (144 * Λ ^ 5 * δ) * C.hxy
  have m1 := C.monoΛ (i := 3) (k := 5) (by norm_num)
  linarith

set_option maxHeartbeats 800000 in
theorem errDg_le (C : Ctx N Λ x y δ L) {A vK BI vI MI c MF BF vF MFi BFi vFi : ℝ}
    (hA : 0 ≤ A) (hA' : A ≤ Λ) (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI)
    (hBI' : BI ≤ Λ) (hw : 0 ≤ vI) (hw' : vI ≤ Λ ^ 2 * x) (hMI0 : 0 ≤ MI) (hMI : MI ≤ Λ * x)
    (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y)
    (hB : 0 ≤ BF) (hB' : BF ≤ Λ) (hvF : 0 ≤ vF) (hvF' : vF ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MF)
    (hM : MF ≤ Λ * x)
    (hBi : 0 ≤ BFi) (hBi' : BFi ≤ Λ) (hvi : 0 ≤ vFi) (hvi' : vFi ≤ Λ ^ 2 * x) (hMi0 : 0 ≤ MFi)
    (hMi : MFi ≤ Λ * x) :
    errDg N A vK BI vI MI c L MF BF vF MFi BFi vFi ≤ 880 * Λ ^ 7 * δ := by
  unfold errDg
  have he1 := C.err1_le hA hA' hv hv' hc hci
  have he2 := C.err2'_le hA hA' hv hv' hBI hBI' hw hw' hMI0 hMI hc hci
  have hbrI := bracketF_le C hBi hBi' hvi hvi' hMi0 hMi
  have hbr := bracketF_le C hB hB' hvF hvF' hM0 hM
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have hy := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have he10 : 0 ≤ err1 N A vK c L := by
    unfold err1; have := dev_nonneg N hA hv hL0; positivity
  have he20 : 0 ≤ err2' N A vK BI vI MI c L := by
    unfold err2'; have := dev_nonneg N hA hv hL0; have := dev_nonneg N hBI hw hL0; positivity
  have hbr0 : 0 ≤ MF + dev N BF vF L := by have := dev_nonneg N hB hvF hL0; positivity
  have hbrI0 : 0 ≤ MFi + dev N BFi vFi L := by have := dev_nonneg N hBi hvi hL0; positivity
  have hB2 : BFi * (1 / c) + BF * (MI / c ^ 2) ≤ 2 * Λ ^ 5 * y := by
    have e : BFi * (1 / c) + BF * (MI / c ^ 2) = BFi * c⁻¹ + BF * MI * c⁻¹ ^ 2 := by ring
    rw [e]
    have h1 : BFi * c⁻¹ ≤ Λ * (Λ * y) := by gcongr
    have h2 : BF * MI * c⁻¹ ^ 2 ≤ Λ * (Λ * x) * (Λ * y) ^ 2 := by gcongr
    have e1 : Λ * (Λ * y) = Λ ^ 2 * y := by ring
    have e2 : Λ * (Λ * x) * (Λ * y) ^ 2 = Λ ^ 4 * y := by
      linear_combination (Λ ^ 4 * y) * C.hxy
    have m1 : Λ ^ 2 * y ≤ Λ ^ 5 * y :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ C.hΛ (by norm_num)) hy.le
    have m2 : Λ ^ 4 * y ≤ Λ ^ 5 * y :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ C.hΛ (by norm_num)) hy.le
    linarith
  have hv2 : (2 * ((1 / c) ^ 2 * vFi) + 2 * ((MI / c ^ 2) ^ 2 * vF)) * x ≤ (2 * Λ ^ 5) ^ 2 := by
    have e : (2 * ((1 / c) ^ 2 * vFi) + 2 * ((MI / c ^ 2) ^ 2 * vF)) * x
        = 2 * (c⁻¹ ^ 2 * vFi * x) + 2 * (MI ^ 2 * c⁻¹ ^ 4 * vF * x) := by ring
    rw [e]
    have h1 : c⁻¹ ^ 2 * vFi * x ≤ (Λ * y) ^ 2 * (Λ ^ 2 * x) * x := by gcongr
    have h2 : MI ^ 2 * c⁻¹ ^ 4 * vF * x ≤ (Λ * x) ^ 2 * (Λ * y) ^ 4 * (Λ ^ 2 * x) * x := by gcongr
    have e1 : (Λ * y) ^ 2 * (Λ ^ 2 * x) * x = Λ ^ 4 := by
      linear_combination (Λ ^ 4 * (x * y + 1)) * C.hxy
    have e2 : (Λ * x) ^ 2 * (Λ * y) ^ 4 * (Λ ^ 2 * x) * x = Λ ^ 8 := by
      linear_combination (Λ ^ 8 * (x * y + 1) * (x ^ 2 * y ^ 2 + 1)) * C.hxy
    have m1 : Λ ^ 4 ≤ Λ ^ 10 := pow_le_pow_right₀ C.hΛ (by norm_num)
    have m2 : Λ ^ 8 ≤ Λ ^ 10 := pow_le_pow_right₀ C.hΛ (by norm_num)
    have e3 : (2 * Λ ^ 5) ^ 2 = 4 * Λ ^ 10 := by ring
    linarith
  have hd2 := dev_le' N C.hN (by positivity) (by positivity) C.hL C.hx C.hδ0 C.hδ hB2
    (by positivity) hv2
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith [C.hδ1]
  have h3 : 6 * (2 * Λ ^ 5 * y) * x * δ ^ 2 ≤ 12 * Λ ^ 5 * δ := by
    have e : 6 * (2 * Λ ^ 5 * y) * x * δ ^ 2 = 12 * Λ ^ 5 * δ ^ 2 := by
      linear_combination (12 * Λ ^ 5 * δ ^ 2) * C.hxy
    rw [e]; have : 0 ≤ Λ ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_left hδ2 this
    linarith
  have hp1 : err1 N A vK c L * (MFi + dev N BFi vFi L)
      ≤ (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) := mul_le_mul he1 hbrI hbrI0 (by positivity)
  have hp2 : err2' N A vK BI vI MI c L * (MF + dev N BF vF L)
      ≤ (80 * Λ ^ 5 * y * δ) * (9 * Λ ^ 2 * x) := mul_le_mul he2 hbr hbr0 (by positivity)
  have e3 : (16 * Λ ^ 3 * y * δ) * (9 * Λ ^ 2 * x) = 144 * (Λ ^ 5 * δ) := by
    linear_combination (144 * Λ ^ 5 * δ) * C.hxy
  have e4 : (80 * Λ ^ 5 * y * δ) * (9 * Λ ^ 2 * x) = 720 * (Λ ^ 7 * δ) := by
    linear_combination (720 * Λ ^ 7 * δ) * C.hxy
  have m1 := C.monoΛ (i := 5) (k := 7) (by norm_num)
  linarith

set_option maxHeartbeats 800000 in
/-- **Arithmetic core for the test kernel**: with every test-kernel constant bounded like the
kernel constants (`B ≤ Λ`, `v ≤ Λ² x`, `M ≤ Λ x`), `err5g ≤ 3 660 000 Λ²⁰ δ`. -/
theorem err5g_le (C : Ctx N Λ x y δ L) {A vK BI vI MM MI c cD MF BF vF MFi BFi vFi : ℝ}
    (hA : 0 ≤ A) (hA' : A ≤ Λ) (hv : 0 ≤ vK) (hv' : vK ≤ Λ ^ 2 * x) (hBI : 0 ≤ BI)
    (hBI' : BI ≤ Λ) (hw : 0 ≤ vI) (hw' : vI ≤ Λ ^ 2 * x) (hM0 : 0 ≤ MM) (hM : MM ≤ Λ * x)
    (hMI0 : 0 ≤ MI) (hMI : MI ≤ Λ * x) (hc : 0 < c) (hci : c⁻¹ ≤ Λ * y)
    (hcD : 0 < cD) (hcDi : cD⁻¹ ≤ Λ ^ 2)
    (hB : 0 ≤ BF) (hB' : BF ≤ Λ) (hvF : 0 ≤ vF) (hvF' : vF ≤ Λ ^ 2 * x) (hMF0 : 0 ≤ MF)
    (hMF : MF ≤ Λ * x)
    (hBi : 0 ≤ BFi) (hBi' : BFi ≤ Λ) (hvi : 0 ≤ vFi) (hvi' : vFi ≤ Λ ^ 2 * x) (hMi0 : 0 ≤ MFi)
    (hMi : MFi ≤ Λ * x) :
    err5g N A vK BI vI MM MI c L MF BF vF MFi BFi vFi cD ≤ 3660000 * Λ ^ 20 * δ := by
  have hL0 : (0:ℝ) ≤ L := by linarith [C.hL]
  have := C.Λ0; have hx := C.hx; have := C.hδ0; have hy := C.y_pos
  have hci0 : 0 ≤ c⁻¹ := (inv_pos.2 hc).le
  have hu0 : 0 ≤ cD⁻¹ := (inv_pos.2 hcD).le
  have h1Λ : (1:ℝ) ≤ Λ := C.hΛ
  have hT := errTg_le C hA hA' hv hv' hc hci hB hB' hvF hvF' hMF0 hMF
  have hD := errDg_le C hA hA' hv hv' hBI hBI' hw hw' hMI0 hMI hc hci hB hB' hvF hvF' hMF0 hMF
    hBi hBi' hvi hvi' hMi0 hMi
  have hT1 := C.errT'_le hA hA' hv hv' hM0 hM hc hci zero_le_one h1Λ
  have hD1 := C.errD'_le hA hA' hv hv' hBI hBI' hw hw' hM0 hM hMI0 hMI hc hci zero_le_one h1Λ
  have hT0 := errTg_nonneg' N hA hv hc hL0 hMF0 hB hvF
  have hD0 := errDg_nonneg' N hA hv hBI hw hMI0 hc hL0 hMF0 hB hvF hMi0 hBi hvi
  have hT10 := Ctx.errT'_nonneg N hA hv hc hL0 zero_le_one hM0
  have hD10 := Ctx.errD'_nonneg N hA hv hBI hw hc hL0 zero_le_one hM0 hMI0
  set a := errTg N A vK c L MF BF vF + errDg N A vK BI vI MI c L MF BF vF MFi BFi vFi with ha
  set e1 := errT' N A vK MM c L 1 with he1
  set e' := errD' N A vK BI vI MM MI c L 1 with he'
  set B := MF * (1 / c) + (MFi * (1 / c) + MF * (MI / c ^ 2)) with hBdef
  set Cc := 1 * MI * (1 / c) + 1 * MM * (MI / c ^ 2) with hCdef
  have m57 := C.monoΛ (i := 5) (k := 7) (by norm_num)
  have ha0 : a ≤ 1032 * (Λ ^ 7 * δ) := by linarith
  have ha00 : 0 ≤ a := by linarith
  have hBb : B ≤ 3 * Λ ^ 5 := by
    have e : B = MF * c⁻¹ + MFi * c⁻¹ + MF * MI * c⁻¹ ^ 2 := by rw [hBdef]; ring
    rw [e]
    have h1 : MF * c⁻¹ ≤ (Λ * x) * (Λ * y) := by gcongr
    have h2 : MFi * c⁻¹ ≤ (Λ * x) * (Λ * y) := by gcongr
    have h3 : MF * MI * c⁻¹ ^ 2 ≤ (Λ * x) * (Λ * x) * (Λ * y) ^ 2 := by gcongr
    have e1' : (Λ * x) * (Λ * y) = Λ ^ 2 := by linear_combination (Λ ^ 2) * C.hxy
    have e2' : (Λ * x) * (Λ * x) * (Λ * y) ^ 2 = Λ ^ 4 := by
      linear_combination (Λ ^ 4 * (x * y + 1)) * C.hxy
    have m : Λ ^ 2 ≤ Λ ^ 5 := pow_le_pow_right₀ C.hΛ (by norm_num)
    have m' : Λ ^ 4 ≤ Λ ^ 5 := pow_le_pow_right₀ C.hΛ (by norm_num)
    linarith
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hCc : Cc ≤ 2 * Λ ^ 4 := by
    have e : Cc = MI * c⁻¹ + MM * MI * c⁻¹ ^ 2 := by rw [hCdef]; ring
    rw [e]
    have h1 : MI * c⁻¹ ≤ (Λ * x) * (Λ * y) := by gcongr
    have h2 : MM * MI * c⁻¹ ^ 2 ≤ (Λ * x) * (Λ * x) * (Λ * y) ^ 2 := by gcongr
    have e1' : (Λ * x) * (Λ * y) = Λ ^ 2 := by linear_combination (Λ ^ 2) * C.hxy
    have e2' : (Λ * x) * (Λ * x) * (Λ * y) ^ 2 = Λ ^ 4 := by
      linear_combination (Λ ^ 4 * (x * y + 1)) * C.hxy
    have m : Λ ^ 2 ≤ Λ ^ 4 := pow_le_pow_right₀ C.hΛ (by norm_num)
    linarith
  have hCc0 : 0 ≤ Cc := by rw [hCdef]; positivity
  have he'1 : e' ≤ 880 * Λ ^ 7 := by
    have : Λ ^ 7 * δ ≤ Λ ^ 7 * 1 := mul_le_mul_of_nonneg_left C.hδ1 (by positivity)
    linarith
  have hCe : Cc + e' ≤ 882 * Λ ^ 7 := by
    have m : Λ ^ 4 ≤ Λ ^ 7 := pow_le_pow_right₀ C.hΛ (by norm_num)
    linarith
  have eE : err5g N A vK BI vI MM MI c L MF BF vF MFi BFi vFi cD
      = 2 * a * cD⁻¹ + 2 * B * e1 * cD⁻¹ ^ 2 + 4 * (a * (Cc + e') + B * e') * cD⁻¹ ^ 2
        + 6 * B * Cc * e1 * cD⁻¹ ^ 3 := by
    dsimp only [err5g]; rw [ha, he1, he', hBdef, hCdef]; ring
  rw [eE]
  have t1 : 2 * a * cD⁻¹ ≤ 2 * (1032 * (Λ ^ 7 * δ)) * Λ ^ 2 := by gcongr
  have t2 : 2 * B * e1 * cD⁻¹ ^ 2 ≤ 2 * (3 * Λ ^ 5) * (152 * Λ ^ 5 * δ) * (Λ ^ 2) ^ 2 := by
    gcongr
  have t3 : 4 * (a * (Cc + e') + B * e') * cD⁻¹ ^ 2
      ≤ 4 * ((1032 * (Λ ^ 7 * δ)) * (882 * Λ ^ 7) + (3 * Λ ^ 5) * (880 * Λ ^ 7 * δ))
        * (Λ ^ 2) ^ 2 := by
    have hCe0 : 0 ≤ Cc + e' := by linarith
    gcongr
  have t4 : 6 * B * Cc * e1 * cD⁻¹ ^ 3 ≤ 6 * (3 * Λ ^ 5) * (2 * Λ ^ 4) * (152 * Λ ^ 5 * δ)
      * (Λ ^ 2) ^ 3 := by gcongr
  have m1 := C.monoΛ (i := 9) (k := 20) (by norm_num)
  have m2 := C.monoΛ (i := 14) (k := 20) (by norm_num)
  have m3 := C.monoΛ (i := 18) (k := 20) (by norm_num)
  have m4 := C.monoΛ (i := 16) (k := 20) (by norm_num)
  have r1 : 2 * (1032 * (Λ ^ 7 * δ)) * Λ ^ 2 = 2064 * (Λ ^ 9 * δ) := by ring
  have r2 : 2 * (3 * Λ ^ 5) * (152 * Λ ^ 5 * δ) * (Λ ^ 2) ^ 2 = 912 * (Λ ^ 14 * δ) := by ring
  have r3 : 4 * ((1032 * (Λ ^ 7 * δ)) * (882 * Λ ^ 7) + (3 * Λ ^ 5) * (880 * Λ ^ 7 * δ))
        * (Λ ^ 2) ^ 2 = 3640896 * (Λ ^ 18 * δ) + 10560 * (Λ ^ 16 * δ) := by ring
  have r4 : 6 * (3 * Λ ^ 5) * (2 * Λ ^ 4) * (152 * Λ ^ 5 * δ) * (Λ ^ 2) ^ 3
      = 5472 * (Λ ^ 20 * δ) := by ring
  have hP : 0 ≤ Λ ^ 20 * δ := by positivity
  linarith

end CTG.NPointLip
/-! ### A130 part 3: Lipschitz test function on the manifold -/

namespace CTG.NPointLip

theorem sexp_one (t : ℝ) : t * Real.exp (-1 * t) ≤ 1 := by
  have h1 := Real.add_one_le_exp t
  have h2 : Real.exp (-1 * t) * Real.exp t = 1 := by
    rw [← Real.exp_add, show -1 * t + t = 0 by ring, Real.exp_zero]
  have h3 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-1 * t)).le
  have h4 := Real.exp_pos (-1 * t)
  nlinarith

theorem sq_sexp_le (t : ℝ) (ht : 0 ≤ t) : t ^ 2 * Real.exp (-Real.exp (-1) * t) ≤ 4 := by
  have h := sexp_le_one (t / 2) (by positivity)
  have e : Real.exp (-Real.exp (-1) * t) = Real.exp (-Real.exp (-1) * (t / 2)) ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have h0 : 0 ≤ t / 2 * Real.exp (-Real.exp (-1) * (t / 2)) := by positivity
  have h2 := pow_le_pow_left₀ h0 h 2
  have e2 : (t / 2 * Real.exp (-Real.exp (-1) * (t / 2))) ^ 2
      = t ^ 2 * Real.exp (-Real.exp (-1) * (t / 2)) ^ 2 / 4 := by ring
  rw [e]
  rw [e2, one_pow] at h2
  linarith

/-- **`L¹` and `L²` bounds of a kernel with an extra factor `ξ`**: if `|F| ≤ ξ c (ρ/ξ)^j e^{−bρ/ξ}`,
then `∫|F| ≤ ξ · profC c b j · ξ^d` and `∫F² ≤ ξ² · profC c² (2b) (2j) · ξ^d` under upper volume
growth (HYPOTHESIS `hgrowth`). -/
theorem prof_bounds {X : Type*} [MeasurableSpace X] (m : Measure X) [IsProbabilityMeasure m]
    (ρ : X → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hgrowth : ∀ r, 0 < r → r ≤ r₀ → m {y | ρ y < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (c b : ℝ) (j : ℕ) (hc : 0 ≤ c) (hb : 0 < b) (S : ℝ)
    (hS : ∀ t, 0 ≤ t → t ^ j * Real.exp (-b * t) ≤ S)
    (b2 : ℝ) (j2 : ℕ) (hb2 : 2 * b = b2) (hj2 : 2 * j = j2)
    (F : X → ℝ) (hFm : Measurable F)
    (hF : ∀ y, |F y| ≤ ξ * (c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ))))) :
    ∫ y, |F y| ∂m ≤ ξ * (profC c b j d Am r₀ * ξ ^ d)
    ∧ ∫ y, F y ^ 2 ∂m ≤ ξ ^ 2 * (profC (c ^ 2) b2 j2 d Am r₀ * ξ ^ d) := by
  subst hb2 hj2
  have hPm : Measurable fun y => c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ))) :=
    measurable_const.mul (((hρm.div_const ξ).pow_const j).mul
      (measurable_const.mul (hρm.div_const ξ)).exp)
  have hP0 : ∀ y, 0 ≤ c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ))) := fun y => by
    have := hρ0 y; positivity
  have hPS : ∀ y, c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ))) ≤ c * S := fun y =>
    mul_le_mul_of_nonneg_left (hS _ (div_nonneg (hρ0 y) hξ.le)) hc
  have iP : Integrable (fun y => c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ)))) m :=
    bdd_integrable m _ hPm (c * S) (fun y => by rw [abs_of_nonneg (hP0 y)]; exact hPS y)
  have hFS : ∀ y, |F y| ≤ ξ * (c * S) := fun y =>
    (hF y).trans (mul_le_mul_of_nonneg_left (hPS y) hξ.le)
  have hL1 := profile_L1 m ρ hρm hρ0 d Am r₀ ξ hAm hr₀ hξ hgrowth c b j hc hb
  have hL2 := profile_L1 m ρ hρm hρ0 d Am r₀ ξ hAm hr₀ hξ hgrowth (c ^ 2) (2 * b) (2 * j)
    (sq_nonneg c) (by positivity)
  constructor
  · have i1 : Integrable (fun y => |F y|) m :=
      bdd_integrable m _ hFm.abs (ξ * (c * S)) (fun y => by rw [abs_abs]; exact hFS y)
    calc ∫ y, |F y| ∂m
        ≤ ∫ y, ξ * (c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ)))) ∂m :=
          integral_mono i1 (iP.const_mul ξ) hF
      _ = ξ * ∫ y, c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ))) ∂m := integral_const_mul _ _
      _ ≤ ξ * (profC c b j d Am r₀ * ξ ^ d) := mul_le_mul_of_nonneg_left hL1 hξ.le
  · have hP2 : ∀ y, c ^ 2 * ((ρ y / ξ) ^ (2 * j) * Real.exp (-(2 * b) * (ρ y / ξ)))
        = (c * ((ρ y / ξ) ^ j * Real.exp (-b * (ρ y / ξ)))) ^ 2 := fun y => by
      have e1 : Real.exp (-(2 * b) * (ρ y / ξ)) = Real.exp (-b * (ρ y / ξ)) ^ 2 := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      have e2 : (ρ y / ξ) ^ (2 * j) = ((ρ y / ξ) ^ j) ^ 2 := by rw [← pow_mul, mul_comm]
      rw [e1, e2]; ring
    have i2 : Integrable (fun y => F y ^ 2) m :=
      bdd_integrable m _ (hFm.pow_const 2) ((ξ * (c * S)) ^ 2) (fun y => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hFS y) 2)
    have hP2m : Measurable fun y =>
        c ^ 2 * ((ρ y / ξ) ^ (2 * j) * Real.exp (-(2 * b) * (ρ y / ξ))) :=
      measurable_const.mul (((hρm.div_const ξ).pow_const _).mul
        (measurable_const.mul (hρm.div_const ξ)).exp)
    have i3 : Integrable (fun y => ξ ^ 2 *
        (c ^ 2 * ((ρ y / ξ) ^ (2 * j) * Real.exp (-(2 * b) * (ρ y / ξ))))) m := by
      refine (bdd_integrable m _ hP2m ((c * S) ^ 2) (fun y => ?_)).const_mul _
      rw [hP2 y, abs_pow, abs_of_nonneg (hP0 y)]
      exact pow_le_pow_left₀ (hP0 y) (hPS y) 2
    calc ∫ y, F y ^ 2 ∂m
        ≤ ∫ y, ξ ^ 2 * (c ^ 2 * ((ρ y / ξ) ^ (2 * j) * Real.exp (-(2 * b) * (ρ y / ξ)))) ∂m :=
          integral_mono i2 i3 (fun y => by
            show F y ^ 2
              ≤ ξ ^ 2 * (c ^ 2 * ((ρ y / ξ) ^ (2 * j) * Real.exp (-(2 * b) * (ρ y / ξ))))
            rw [hP2 y, ← mul_pow, ← sq_abs (F y)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hF y) 2)
      _ = ξ ^ 2 * ∫ y, c ^ 2 * ((ρ y / ξ) ^ (2 * j) * Real.exp (-(2 * b) * (ρ y / ξ))) ∂m :=
          integral_const_mul _ _
      _ ≤ ξ ^ 2 * (profC (c ^ 2) (2 * b) (2 * j) d Am r₀ * ξ ^ d) :=
          mul_le_mul_of_nonneg_left hL2 (by positivity)

section ManifoldLip

open Bundle Manifold CTG.ManifoldDistance

variable {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EE H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle EE (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {s : Set ℝ}

/-- Pointwise bound of `K^τ(x,y)(f(y) − f(x))` for `f` Lipschitz in `d_τ` (HYPOTHESIS `hL`):
`≤ ξ · A Lip · s e^{−s}` with `s = d_τ/ξ`. -/
theorem lip_kern_pt (G : TimeMetric I M s) (h : ℝ → ℝ) (A ξ τ : ℝ) (hξ : 0 < ξ) (hA : 0 ≤ A)
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (f : M → ℝ) (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hL : ∀ x y, |f y - f x| ≤ Lip * G.dist x y τ) (x y : M) :
    |kern G h ξ τ x y * (f y - f x)|
      ≤ ξ * ((A * Lip) * ((G.dist x y τ / ξ) ^ 1 * Real.exp (-1 * (G.dist x y τ / ξ)))) := by
  have ht : 0 ≤ G.dist x y τ / ξ := div_nonneg (G.dist_nonneg x y τ) hξ.le
  have hξ0 : ξ ≠ 0 := hξ.ne'
  have hc : ξ * (G.dist x y τ / ξ) = G.dist x y τ := by field_simp
  have hd : Lip * G.dist x y τ = Lip * ξ * (G.dist x y τ / ξ) := by rw [mul_assoc, hc]
  rw [abs_mul, pow_one, neg_one_mul]
  calc |kern G h ξ τ x y| * |f y - f x|
      ≤ (A * Real.exp (-(G.dist x y τ / ξ))) * (Lip * G.dist x y τ) :=
        mul_le_mul (hh _ ht) (hL x y) (abs_nonneg _) (by positivity)
    _ = ξ * ((A * Lip) * (G.dist x y τ / ξ * Real.exp (-(G.dist x y τ / ξ)))) := by
        rw [hd]; ring

/-- Pointwise bound of `Δ_ηK(x,y)(f(y) − f(x))` for `f` Lipschitz in `d_a`:
`≤ ξ · 2κA Lip · s² e^{−s/e}` with `s = d_a/ξ`. -/
theorem lip_inc_pt (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (h h' : ℝ → ℝ) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (f : M → ℝ) (Lip : ℝ) (hLip : 0 ≤ Lip) (hL : ∀ x y, |f y - f x| ≤ Lip * G.dist x y a)
    (x y : M) :
    |(kern G h ξ b x y - kern G h ξ a x y) / (b - a) * (f y - f x)|
      ≤ ξ * ((2 * G.κ * A * Lip)
          * ((G.dist x y a / ξ) ^ 2 * Real.exp (-Real.exp (-1) * (G.dist x y a / ξ)))) := by
  have hk := G.kernel_increment_le ha hb hab x y (G.riemannianEDist_ne_top ha₀ ha hcont x y)
    h h' A ξ hA hξ hder hbd
  have hd : 0 < |b - a| := abs_pos.2 (sub_ne_zero.2 hne)
  have hκ := G.κ_nonneg
  have ht : 0 ≤ G.dist x y a / ξ := div_nonneg (G.dist_nonneg x y a) hξ.le
  have hξ0 : ξ ≠ 0 := hξ.ne'
  have hq : |(kern G h ξ b x y - kern G h ξ a x y) / (b - a)|
      ≤ 2 * G.κ * A * ((G.dist x y a / ξ) ^ 1
          * Real.exp (-Real.exp (-1) * (G.dist x y a / ξ))) := by
    unfold kern
    rw [abs_div, div_le_iff₀ hd]
    refine hk.trans (le_of_eq ?_)
    ring
  have hc : ξ * (G.dist x y a / ξ) = G.dist x y a := by field_simp
  have hdl : Lip * G.dist x y a = Lip * ξ * (G.dist x y a / ξ) := by rw [mul_assoc, hc]
  rw [abs_mul]
  calc _ ≤ (2 * G.κ * A * ((G.dist x y a / ξ) ^ 1
            * Real.exp (-Real.exp (-1) * (G.dist x y a / ξ)))) * (Lip * G.dist x y a) :=
        mul_le_mul hq (hL x y) (abs_nonneg _) (by positivity)
    _ = _ := by rw [hdl]; ring

/-- The test kernel `K^τ(x,z)(f(z) − f(x))` satisfies the template with `B = ξ A Lip`,
`v = ξ² profC (A Lip)² 2 2 ξ^d`, and has `L¹` norm `≤ ξ profC (A Lip) 1 1 ξ^d`. -/
theorem good_lip (G : TimeMetric I M s) {a₀ τ : ℝ} (ha₀ : a₀ ∈ s) (hτ : τ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hgrowth : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y τ < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h : ℝ → ℝ) (hhc : Continuous h) (A : ℝ) (hA : 0 ≤ A)
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t))
    (f : M → ℝ) (hf : Measurable f) (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hL : ∀ x y, |f y - f x| ≤ Lip * G.dist x y τ) :
    Good m (fun x z => kern G h ξ τ x z * (f z - f x)) (ξ * (A * Lip))
      (ξ ^ 2 * (profC ((A * Lip) ^ 2) 2 2 d Am r₀ * ξ ^ d))
    ∧ ∀ x, ∫ z, |kern G h ξ τ x z * (f z - f x)| ∂m
        ≤ ξ * (profC (A * Lip) 1 1 d Am r₀ * ξ ^ d) := by
  have hρm : ∀ x, Measurable (fun y => G.dist x y τ) := fun x =>
    ((G.dist_continuous_pair ha₀ hτ hcont).comp (continuous_const.prodMk continuous_id)).measurable
  have hK := kern_measurable G ha₀ hτ hcont h hhc ξ
  have hALip : 0 ≤ A * Lip := mul_nonneg hA hLip
  have hpb := fun x => prof_bounds m (fun y => G.dist x y τ) (hρm x)
    (fun y => G.dist_nonneg x y τ) d Am r₀ ξ hAm hr₀ hξ (hgrowth x) (A * Lip) 1 1 hALip one_pos 1
    (fun t ht => by rw [pow_one]; exact sexp_one t) 2 2 (by norm_num) (by norm_num)
    (fun z => kern G h ξ τ x z * (f z - f x))
    ((hK.comp (measurable_const.prodMk measurable_id)).mul (hf.sub measurable_const))
    (fun z => lip_kern_pt G h A ξ τ hξ hA hh f Lip hLip hL x z)
  have hv0 : 0 ≤ ξ ^ 2 * (profC ((A * Lip) ^ 2) 2 2 d Am r₀ * ξ ^ d) :=
    mul_nonneg (sq_nonneg ξ) (mul_nonneg (profC_nonneg 2 d (sq_nonneg _) (by norm_num) hAm hr₀)
      (pow_pos hξ d).le)
  refine ⟨⟨hK.mul ((hf.comp measurable_snd).sub (hf.comp measurable_fst)),
    mul_nonneg hξ.le hALip, hv0, fun x z => ?_, fun x => (hpb x).2⟩, fun x => (hpb x).1⟩
  have ht : 0 ≤ G.dist x z τ / ξ := div_nonneg (G.dist_nonneg x z τ) hξ.le
  refine (lip_kern_pt G h A ξ τ hξ hA hh f Lip hLip hL x z).trans
    (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hALip ?_) hξ.le)
  rw [pow_one]; exact sexp_one _

/-- The test kernel of the increment `Δ_ηK(x,z)(f(z) − f(x))` satisfies the template with
`B = ξ · 8κA Lip`, `v = ξ² profC (2κA Lip)² (2/e) 4 ξ^d`, and has `L¹` norm
`≤ ξ profC (2κA Lip) e⁻¹ 2 ξ^d`. -/
theorem good_lip_inc (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am)
    (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hgrowth : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (f : M → ℝ) (hf : Measurable f) (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hL : ∀ x y, |f y - f x| ≤ Lip * G.dist x y a) :
    Good m (fun x z => (kern G h ξ b x z - kern G h ξ a x z) / (b - a) * (f z - f x))
      (ξ * (2 * G.κ * A * Lip * 4))
      (ξ ^ 2 * (profC ((2 * G.κ * A * Lip) ^ 2) (2 * Real.exp (-1)) 4 d Am r₀ * ξ ^ d))
    ∧ ∀ x, ∫ z, |(kern G h ξ b x z - kern G h ξ a x z) / (b - a) * (f z - f x)| ∂m
        ≤ ξ * (profC (2 * G.κ * A * Lip) (Real.exp (-1)) 2 d Am r₀ * ξ ^ d) := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have hρm : ∀ x, Measurable (fun y => G.dist x y a) := fun x =>
    ((G.dist_continuous_pair ha₀ ha hcont).comp (continuous_const.prodMk continuous_id)).measurable
  have hKa := kern_measurable G ha₀ ha hcont h hhc ξ
  have hKb := kern_measurable G ha₀ hb hcont h hhc ξ
  have hκ := G.κ_nonneg
  have hc0 : 0 ≤ 2 * G.κ * A * Lip := by positivity
  have hpb := fun x => prof_bounds m (fun y => G.dist x y a) (hρm x)
    (fun y => G.dist_nonneg x y a) d Am r₀ ξ hAm hr₀ hξ (hgrowth x) (2 * G.κ * A * Lip)
    (Real.exp (-1)) 2 hc0 (Real.exp_pos _) 4 (fun t ht => sq_sexp_le t ht)
    (2 * Real.exp (-1)) 4 rfl (by norm_num)
    (fun z => (kern G h ξ b x z - kern G h ξ a x z) / (b - a) * (f z - f x))
    ((((hKb.comp (measurable_const.prodMk measurable_id)).sub
      (hKa.comp (measurable_const.prodMk measurable_id))).div_const _).mul
        (hf.sub measurable_const))
    (fun z => lip_inc_pt G ha₀ hcont ha hb hab hne h h' A ξ hA hξ hder hbd f Lip hLip hL x z)
  have hv0 : 0 ≤ ξ ^ 2 * (profC ((2 * G.κ * A * Lip) ^ 2) (2 * Real.exp (-1)) 4 d Am r₀ * ξ ^ d) :=
    mul_nonneg (sq_nonneg ξ) (mul_nonneg (profC_nonneg 4 d (sq_nonneg _) (by positivity) hAm hr₀)
      (pow_pos hξ d).le)
  refine ⟨⟨((hKb.sub hKa).div_const _).mul
      ((hf.comp measurable_snd).sub (hf.comp measurable_fst)),
    mul_nonneg hξ.le (by positivity), hv0, fun x z => ?_, fun x => (hpb x).2⟩, fun x => (hpb x).1⟩
  have ht : 0 ≤ G.dist x z a / ξ := div_nonneg (G.dist_nonneg x z a) hξ.le
  exact (lip_inc_pt G ha₀ hcont ha hb hab hne h h' A ξ hA hξ hder hbd f Lip hLip hL x z).trans
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sq_sexp_le _ ht) hc0) hξ.le)

/-- **Steps 2–5 of `prop:dotLN-diff` for a Lipschitz test function**, manifold form with the
growth HYPOTHESES of `npoint_step5'`.  The test function enters through `g(x,y) = f(y) − f(x)` with
`|f(y) − f(x)| ≤ Lip·d_τ(x,y)` at `τ = a` and `τ = b` (HYPOTHESES `hLa`, `hLb`); the error is
`ξ · err5g(…)` where `err5g` is evaluated at the `ξ`-free constants of the test kernels. -/
theorem npoint_step5_lip {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (f : M → ℝ) (hf : Measurable f) (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hLa : ∀ x y, |f y - f x| ≤ Lip * G.dist x y a)
    (hLb : ∀ x y, |f y - f x| ≤ Lip * G.dist x y b)
    (c : ℝ) (hc : 0 < c)
    (hqa : ∀ y, c ≤ popNorm G h ξ a m y) (hqb : ∀ y, c ≤ popNorm G h ξ b m y)
    (L : ℝ) (hL : 0 < L)
    (hsmall : dev N A (vKern d Am r₀ ξ A) L / c ≤ 1 / 2)
    (hsmallD : errT' N A (vKern d Am r₀ ξ A) (profC A 1 0 d Am r₀ * ξ ^ d) c L 1
      / (c / (profC A 1 0 d Am r₀ * ξ ^ d)) ≤ 1 / 2) :
    μ.real {ω | ∃ i < N,
        ξ * err5g N A (vKern d Am r₀ ξ A) (2 * G.κ * A) (vInc G.κ d Am r₀ ξ A a b)
          (profC A 1 0 d Am r₀ * ξ ^ d) (profC (2 * G.κ * A) (Real.exp (-1)) 1 d Am r₀ * ξ ^ d)
          c L (profC (A * Lip) 1 1 d Am r₀ * ξ ^ d) (A * Lip)
          (profC ((A * Lip) ^ 2) 2 2 d Am r₀ * ξ ^ d)
          (profC (2 * G.κ * A * Lip) (Real.exp (-1)) 2 d Am r₀ * ξ ^ d) (2 * G.κ * A * Lip * 4)
          (profC ((2 * G.κ * A * Lip) ^ 2) (2 * Real.exp (-1)) 4 d Am r₀ * ξ ^ d)
          (c / (profC A 1 0 d Am r₀ * ξ ^ d))
        < |(sampW X N (kern G h ξ b) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ b) (fun _ _ => 1) i ω
              - sampW X N (kern G h ξ a) (fun x y => f y - f x) i ω
                / sampW X N (kern G h ξ a) (fun _ _ => 1) i ω) / (b - a)
          - (popW m (kern G h ξ b) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ b) (fun _ _ => 1) (X i ω)
              - popW m (kern G h ξ a) (fun x y => f y - f x) (X i ω)
                / popW m (kern G h ξ a) (fun _ _ => 1) (X i ω)) / (b - a)|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have GKa := good_kern G ha₀ ha hcont m d Am r₀ ξ hAm hr₀ hξ hga h hhc A hA.le hh
  have GKb := good_kern G ha₀ hb hcont m d Am r₀ ξ hAm hr₀ hξ hgb h hhc A hA.le hh
  have GKi := good_inc G ha₀ hcont ha hb hab hne m d Am r₀ ξ hAm hr₀ hξ hga h h' A hA.le hder hbd
  have hMpos : 0 < profC A 1 0 d Am r₀ * ξ ^ d :=
    mul_pos (profC_pos 0 d hA one_pos hAm hr₀) (pow_pos hξ d)
  have hκ := G.κ_nonneg
  have hMI0 : 0 ≤ profC (2 * G.κ * A) (Real.exp (-1)) 1 d Am r₀ * ξ ^ d :=
    mul_nonneg (profC_nonneg 1 d (by positivity) (Real.exp_pos _) hAm hr₀) (pow_pos hξ d).le
  have hMa := fun x => kern_L1 G ha₀ ha hcont m d Am r₀ ξ hAm hr₀ hξ x (hga x) h hhc A hA.le hh
  have hMb := fun x => kern_L1 G ha₀ hb hcont m d Am r₀ ξ hAm hr₀ hξ x (hgb x) h hhc A hA.le hh
  have hMI := fun x => kernInc_L1 G ha₀ hcont ha hb hab hne m d Am r₀ ξ hAm hr₀ hξ x (hga x)
    h h' A hA.le hder hbd
  obtain ⟨GFa, hMFa⟩ := good_lip G ha₀ ha hcont m d Am r₀ ξ hAm hr₀ hξ hga h hhc A hA.le hh
    f hf Lip hLip hLa
  obtain ⟨GFb, hMFb⟩ := good_lip G ha₀ hb hcont m d Am r₀ ξ hAm hr₀ hξ hgb h hhc A hA.le hh
    f hf Lip hLip hLb
  obtain ⟨GFi, hMFi⟩ := good_lip_inc G ha₀ hcont ha hb hab hne m d Am r₀ ξ hAm hr₀ hξ hga h h'
    A hA.le hder hbd f hf Lip hLip hLa
  have hMF0 : 0 ≤ ξ * (profC (A * Lip) 1 1 d Am r₀ * ξ ^ d) :=
    mul_nonneg hξ.le (mul_nonneg (profC_nonneg 1 d (mul_nonneg hA.le hLip) one_pos hAm hr₀)
      (pow_pos hξ d).le)
  have hMFi0 : 0 ≤ ξ * (profC (2 * G.κ * A * Lip) (Real.exp (-1)) 2 d Am r₀ * ξ ^ d) :=
    mul_nonneg hξ.le (mul_nonneg (profC_nonneg 2 d (by positivity) (Real.exp_pos _) hAm hr₀)
      (pow_pos hξ d).le)
  have h5 := step5g X h_indep hX hlaw N hN (kern G h ξ a) (kern G h ξ b)
    (fun x y => f y - f x) (b - a) GKa GKb GKi hc hL hqa hqb hMpos.le hMa hMb hMI0 hMI
    GFa GFb GFi hMF0 hMFa hMFb hMFi0 hMFi (div_pos hc hMpos)
    (fun x => popW_one_ge' _ GKa hc (fun x y => hh0 _) hqa hMa x)
    (fun x => popW_one_ge' _ GKb hc (fun x y => hh0 _) hqb hMb x)
    hsmall hsmallD
  rw [err5g_scale N hξ.le] at h5
  exact h5

end ManifoldLip

end CTG.NPointLip
/-! ### A130 part 4: the rate `ξ·δ'`, the normalised form `δ'/ξ`, and the geometric version -/

namespace CTG.NPointLip

/-- The single constant `Λ` of the Lipschitz version: `sharpLam` (with `B_f = 0`) together with the
constants of the two test kernels. -/
def lipLam (d : ℕ) (Am r₀ A κ q Lip : ℝ) : ℝ :=
  max (sharpLam d Am r₀ A κ 0 q)
    (max (max (A * Lip) (2 * κ * A * Lip * 4))
      (max (max (Real.sqrt (profC ((A * Lip) ^ 2) 2 2 d Am r₀))
          (Real.sqrt (profC ((2 * κ * A * Lip) ^ 2) (2 * Real.exp (-1)) 4 d Am r₀)))
        (max (profC (A * Lip) 1 1 d Am r₀) (profC (2 * κ * A * Lip) (Real.exp (-1)) 2 d Am r₀))))

section LipLamFacts
variable (d : ℕ) (Am r₀ A κ q Lip : ℝ)
theorem llam_s : sharpLam d Am r₀ A κ 0 q ≤ lipLam d Am r₀ A κ q Lip := le_max_left _ _
theorem llam_BF : A * Lip ≤ lipLam d Am r₀ A κ q Lip :=
  (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
theorem llam_BFi : 2 * κ * A * Lip * 4 ≤ lipLam d Am r₀ A κ q Lip :=
  (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
theorem llam_vF : Real.sqrt (profC ((A * Lip) ^ 2) 2 2 d Am r₀) ≤ lipLam d Am r₀ A κ q Lip :=
  (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
theorem llam_vFi : Real.sqrt (profC ((2 * κ * A * Lip) ^ 2) (2 * Real.exp (-1)) 4 d Am r₀)
    ≤ lipLam d Am r₀ A κ q Lip :=
  (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
theorem llam_MF : profC (A * Lip) 1 1 d Am r₀ ≤ lipLam d Am r₀ A κ q Lip :=
  (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
theorem llam_MFi : profC (2 * κ * A * Lip) (Real.exp (-1)) 2 d Am r₀ ≤ lipLam d Am r₀ A κ q Lip :=
  (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
end LipLamFacts

/-- **Deterministic part of the rate, Lipschitz version.**  For `0 < ξ ≤ 1`, `L ≥ 1`, `c = q ξᵈ`,
and `92416 Λ¹⁴ L ≤ N ξᵈ` (`Λ = lipLam`): both smallness conditions hold and the `ξ`-free error
`err5g` is at most `3 660 000 Λ²⁰ √(L/(N ξᵈ))`. -/
theorem rate_bounds_lip (N : ℕ) (hN : 0 < N) (d : ℕ) {Am r₀ ξ A κ q L a b Lip : ℝ}
    (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hA : 0 < A) (hκ : 0 ≤ κ)
    (hLip : 0 ≤ Lip) (hq : 0 < q) (hne : b ≠ a) (hL : 1 ≤ L)
    (hNL : 92416 * lipLam d Am r₀ A κ q Lip ^ 14 * L ≤ N * ξ ^ d) :
    dev N A (vKern d Am r₀ ξ A) L / (q * ξ ^ d) ≤ 1 / 2 ∧
    errT' N A (vKern d Am r₀ ξ A) (profC A 1 0 d Am r₀ * ξ ^ d) (q * ξ ^ d) L 1
      / (q * ξ ^ d / (profC A 1 0 d Am r₀ * ξ ^ d)) ≤ 1 / 2 ∧
    err5g N A (vKern d Am r₀ ξ A) (2 * κ * A) (vInc κ d Am r₀ ξ A a b)
        (profC A 1 0 d Am r₀ * ξ ^ d) (profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀ * ξ ^ d)
        (q * ξ ^ d) L (profC (A * Lip) 1 1 d Am r₀ * ξ ^ d) (A * Lip)
        (profC ((A * Lip) ^ 2) 2 2 d Am r₀ * ξ ^ d)
        (profC (2 * κ * A * Lip) (Real.exp (-1)) 2 d Am r₀ * ξ ^ d) (2 * κ * A * Lip * 4)
        (profC ((2 * κ * A * Lip) ^ 2) (2 * Real.exp (-1)) 4 d Am r₀ * ξ ^ d)
        (q * ξ ^ d / (profC A 1 0 d Am r₀ * ξ ^ d))
      ≤ 3660000 * lipLam d Am r₀ A κ q Lip ^ 20 * Real.sqrt (L / (N * ξ ^ d)) := by
  set Λ := lipLam d Am r₀ A κ q Lip with hΛdef
  set x := ξ ^ d with hxdef
  set δ := Real.sqrt (L / (N * x)) with hδdef
  have hs := llam_s d Am r₀ A κ q Lip
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hx : 0 < x := pow_pos hξ d
  have hx1 : x ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hΛ : 1 ≤ Λ := (slam_one d Am r₀ A κ 0 q).trans hs
  have hΛ0 : 0 < Λ := by linarith
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδ : δ ^ 2 * (N * x) = L := by
    rw [hδdef, Real.sq_sqrt (by positivity)]; field_simp
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hP : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * x) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ 1 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((1 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hP] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ hΛ
    nlinarith
  have C : Ctx N Λ x x⁻¹ δ L :=
    { hN := hN, hΛ := hΛ, hx := hx, hx1 := hx1, hxy := mul_inv_cancel₀ hx.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL }
  have hv0 := vKern_nonneg d (r₀ := r₀) (A := A) hAm hξ
  have hw0 := vInc_nonneg κ d (r₀ := r₀) (A := A) (a := a) (b := b) hAm hξ
  have hv' : vKern d Am r₀ ξ A ≤ Λ ^ 2 * x :=
    (vKern_le d hAm hr₀ hξ).trans (mul_le_mul_of_nonneg_right
      (sq_le_of_sqrt_le (cV_nonneg d hAm hr₀) ((slam_cV d Am r₀ A κ 0 q).trans hs)) hx.le)
  have hw' : vInc κ d Am r₀ ξ A a b ≤ Λ ^ 2 * x :=
    (vInc_le κ d hAm hr₀ hξ hne).trans (mul_le_mul_of_nonneg_right
      (sq_le_of_sqrt_le (cV'_nonneg κ d hAm hr₀) ((slam_cV' d Am r₀ A κ 0 q).trans hs)) hx.le)
  have hM1 : 0 < profC A 1 0 d Am r₀ := profC_pos 0 d hA one_pos hAm hr₀
  have hM0 : 0 ≤ profC A 1 0 d Am r₀ * x := by positivity
  have hM : profC A 1 0 d Am r₀ * x ≤ Λ * x :=
    mul_le_mul_of_nonneg_right ((slam_M d Am r₀ A κ 0 q).trans hs) hx.le
  have hMI0 : 0 ≤ profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀ * x :=
    mul_nonneg (profC_nonneg 1 d (by positivity) (Real.exp_pos _) hAm hr₀) hx.le
  have hMI : profC (2 * κ * A) (Real.exp (-1)) 1 d Am r₀ * x ≤ Λ * x :=
    mul_le_mul_of_nonneg_right ((slam_MI d Am r₀ A κ 0 q).trans hs) hx.le
  have hc : 0 < q * x := by positivity
  have hci : (q * x)⁻¹ ≤ Λ * x⁻¹ := by
    rw [mul_inv]
    exact mul_le_mul_of_nonneg_right ((slam_q d Am r₀ A κ 0 q).trans hs) (by positivity)
  have hcD : 0 < q * x / (profC A 1 0 d Am r₀ * x) := by positivity
  have hcDi : (q * x / (profC A 1 0 d Am r₀ * x))⁻¹ ≤ Λ ^ 2 := by
    rw [inv_div, div_eq_mul_inv]
    calc profC A 1 0 d Am r₀ * x * (q * x)⁻¹ ≤ (Λ * x) * (Λ * x⁻¹) :=
          mul_le_mul hM hci (by positivity) (by positivity)
      _ = Λ ^ 2 := by field_simp
  have hBI0 : 0 ≤ 2 * κ * A := by positivity
  have hBI' : 2 * κ * A ≤ Λ := (slam_BI d Am r₀ A κ 0 q).trans hs
  have hA' : A ≤ Λ := (slam_A d Am r₀ A κ 0 q).trans hs
  -- the test-kernel constants
  have hBF0 : 0 ≤ A * Lip := mul_nonneg hA.le hLip
  have hBFi0 : 0 ≤ 2 * κ * A * Lip * 4 := by positivity
  have hpV1 := profC_nonneg 2 d (sq_nonneg (A * Lip)) (by norm_num : (0:ℝ) < 2) hAm hr₀
  have hpV2 := profC_nonneg 4 d (sq_nonneg (2 * κ * A * Lip))
    (by positivity : (0:ℝ) < 2 * Real.exp (-1)) hAm hr₀
  have hpM1 := profC_nonneg 1 d hBF0 (one_pos) hAm hr₀
  have hpM2 := profC_nonneg 2 d (by positivity : (0:ℝ) ≤ 2 * κ * A * Lip) (Real.exp_pos (-1))
    hAm hr₀
  have hvF' : profC ((A * Lip) ^ 2) 2 2 d Am r₀ * x ≤ Λ ^ 2 * x :=
    mul_le_mul_of_nonneg_right (sq_le_of_sqrt_le hpV1 (llam_vF d Am r₀ A κ q Lip)) hx.le
  have hvFi' : profC ((2 * κ * A * Lip) ^ 2) (2 * Real.exp (-1)) 4 d Am r₀ * x ≤ Λ ^ 2 * x :=
    mul_le_mul_of_nonneg_right (sq_le_of_sqrt_le hpV2 (llam_vFi d Am r₀ A κ q Lip)) hx.le
  have hMF : profC (A * Lip) 1 1 d Am r₀ * x ≤ Λ * x :=
    mul_le_mul_of_nonneg_right (llam_MF d Am r₀ A κ q Lip) hx.le
  have hMFi : profC (2 * κ * A * Lip) (Real.exp (-1)) 2 d Am r₀ * x ≤ Λ * x :=
    mul_le_mul_of_nonneg_right (llam_MFi d Am r₀ A κ q Lip) hx.le
  have hsmall := C.small'_le hA.le hA' hv0 hv' hM0 hM hc hci hcD hcDi hsm
  have he := err5g_le C hA.le hA' hv0 hv' hBI0 hBI' hw0 hw' hM0 hM hMI0 hMI hc hci hcD hcDi
    hBF0 (llam_BF d Am r₀ A κ q Lip) (by positivity) hvF' (by positivity) hMF
    hBFi0 (llam_BFi d Am r₀ A κ q Lip) (by positivity) hvFi' (by positivity) hMFi
  exact ⟨hsmall.1, hsmall.2, he⟩

/-- The difference quotient of the sample quotient minus the population one, for the test
function `g(x,y) = f(y) − f(x)` (this is `−(c_h ξ²/2)` times `Δ_η(L_N f)(i) − Δ_η(L_ξ f)(X_i)`). -/
def qDiff {E : Type*} [MeasurableSpace E] {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (m : Measure E)
    (Ka Kb : E → E → ℝ) (f : E → ℝ) (η : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (sampW X N Kb (fun x y => f y - f x) i ω / sampW X N Kb (fun _ _ => 1) i ω
      - sampW X N Ka (fun x y => f y - f x) i ω / sampW X N Ka (fun _ _ => 1) i ω) / η
    - (popW m Kb (fun x y => f y - f x) (X i ω) / popW m Kb (fun _ _ => 1) (X i ω)
      - popW m Ka (fun x y => f y - f x) (X i ω) / popW m Ka (fun _ _ => 1) (X i ω)) / η

/-- `K/ξ` against `|Q|/(c_h ξ²/2)` is `ξ K` against `|Q|` (with `K` multiplied by `2/c_h`). -/
theorem norm_step {ξ ch K Q : ℝ} (hξ : 0 < ξ) (hch : 0 < ch)
    (h : 2 / ch * K / ξ < |Q| / (ch * ξ ^ 2 / 2)) : ξ * K < |Q| := by
  have hpos : 0 < ch * ξ ^ 2 / 2 := by positivity
  rw [lt_div_iff₀ hpos] at h
  have e : 2 / ch * K / ξ * (ch * ξ ^ 2 / 2) = ξ * K := by
    have := hξ.ne'; have := hch.ne'
    field_simp
  rw [e] at h
  exact h

section ManifoldLipRate

open Bundle Manifold CTG.ManifoldDistance

variable {EE : Type*} [NormedAddCommGroup EE] [NormedSpace ℝ EE]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EE H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle EE (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {s : Set ℝ}

/-- **(b) Steps 2–5 for a Lipschitz test function with the rate `ξ·δ'`.**  Setting and HYPOTHESES
as `npoint_step5_lip` (upper growth at both times, `q ξᵈ ≤ q^τ`, `f` `Lip`-Lipschitz in `d_a` and in
`d_b`), with `ξ ≤ 1`, `L ≥ 1` and `92416 Λ¹⁴ L ≤ N ξᵈ` (`Λ = lipLam d A_m r₀ A κ q Lip`).  With
probability at least `1 − 15N·2e^{−L}`, for all `i < N`: `|qDiff| ≤ ξ · 3 660 000 Λ²⁰ √(L/(N ξᵈ))`. -/
theorem npoint_step5_lip_sharp {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (f : M → ℝ) (hf : Measurable f) (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hLa : ∀ x y, |f y - f x| ≤ Lip * G.dist x y a)
    (hLb : ∀ x y, |f y - f x| ≤ Lip * G.dist x y b)
    (q : ℝ) (hq : 0 < q)
    (hqa : ∀ y, q * ξ ^ d ≤ popNorm G h ξ a m y) (hqb : ∀ y, q * ξ ^ d ≤ popNorm G h ξ b m y)
    (L : ℝ) (hL : 1 ≤ L)
    (hNL : 92416 * lipLam d Am r₀ A G.κ q Lip ^ 14 * L ≤ N * ξ ^ d) :
    μ.real {ω | ∃ i < N,
        ξ * (3660000 * lipLam d Am r₀ A G.κ q Lip ^ 20 * Real.sqrt (L / (N * ξ ^ d)))
        < |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω|}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨hs1, hs2, he⟩ := rate_bounds_lip N hN d (a := a) (b := b) hAm hr₀ hξ hξ1 hA
    G.κ_nonneg hLip hq hne hL hNL
  have h5 := npoint_step5_lip G ha₀ hcont ha hb hab hne m X h_indep hX hlaw N hN d Am r₀ ξ hAm
    hr₀ hξ hga hgb h h' A hA hder hbd hh hh0 f hf Lip hLip hLa hLb (q * ξ ^ d) (by positivity)
    hqa hqb L (by linarith) hs1 hs2
  refine le_trans (measureReal_mono ?_) h5
  rintro ω ⟨i, hi, hlt⟩
  exact ⟨i, hi, lt_of_le_of_lt (mul_le_mul_of_nonneg_left he hξ.le) hlt⟩

/-- **(c) The first inequality of `prop:dotLN-diff` in the form `C δ'/ξ`.**  With
`L_N = (2/(c_h ξ²))(I − P)` and its population analogue (`c_h > 0` a parameter), the left side
`|qDiff|/(c_h ξ²/2)` is `max_i |Δ_η(L_N f)(i) − Δ_η(L_ξ f)(X_i)|`.  Same HYPOTHESES as
`npoint_step5_lip_sharp`; with probability at least `1 − 15N·2e^{−L}`, for all `i < N` it is at most
`(2/c_h) · 3 660 000 Λ²⁰ √(L/(N ξᵈ)) / ξ`. -/
theorem npoint_step5_lip_norm {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (G : TimeMetric I M s) {a₀ a b : ℝ} (ha₀ : a₀ ∈ s)
    (hcont : Continuous (fun x ↦ TotalSpace.mk' (EE →L[ℝ] EE →L[ℝ] ℝ) x (G.g a₀ x)))
    (ha : a ∈ s) (hb : b ∈ s) (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m]
    (X : ℕ → Ω → M) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = m) (N : ℕ) (hN : 0 < N)
    (d : ℕ) (Am r₀ ξ : ℝ) (hAm : 0 ≤ Am) (hr₀ : 0 < r₀) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hga : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y a < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (hgb : ∀ x r, 0 < r → r ≤ r₀ → m {y | G.dist x y b < r} ≤ ENNReal.ofReal (Am * r ^ d))
    (h h' : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
    (hder : ∀ t, HasDerivAt h (h' t) t) (hbd : ∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t))
    (hh : ∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) (hh0 : ∀ t, 0 ≤ h t)
    (f : M → ℝ) (hf : Measurable f) (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hLa : ∀ x y, |f y - f x| ≤ Lip * G.dist x y a)
    (hLb : ∀ x y, |f y - f x| ≤ Lip * G.dist x y b)
    (q : ℝ) (hq : 0 < q)
    (hqa : ∀ y, q * ξ ^ d ≤ popNorm G h ξ a m y) (hqb : ∀ y, q * ξ ^ d ≤ popNorm G h ξ b m y)
    (L : ℝ) (hL : 1 ≤ L)
    (hNL : 92416 * lipLam d Am r₀ A G.κ q Lip ^ 14 * L ≤ N * ξ ^ d) (ch : ℝ) (hch : 0 < ch) :
    μ.real {ω | ∃ i < N,
        2 / ch * (3660000 * lipLam d Am r₀ A G.κ q Lip ^ 20 * Real.sqrt (L / (N * ξ ^ d))) / ξ
        < |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω| / (ch * ξ ^ 2 / 2)}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  refine le_trans (measureReal_mono ?_) (npoint_step5_lip_sharp G ha₀ hcont ha hb hab hne m X
    h_indep hX hlaw N hN d Am r₀ ξ hAm hr₀ hξ hξ1 hga hgb h h' A hA hder hbd hh hh0 f hf Lip
    hLip hLa hLb q hq hqa hqb L hL hNL)
  rintro ω ⟨i, hi, hlt⟩
  exact ⟨i, hi, norm_step hξ hch hlt⟩

end ManifoldLipRate

section GeomLip

open Bundle Manifold CTG.ManifoldDistance CTG.ManifoldVolume CTG.NPointGeom
open scoped Manifold ENNReal

universe u

variable {n : ℕ} {M : Type*} [EMetricSpace M] [ChartedSpace (Fin n → ℝ) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) 1 M]
  [IsContinuousRiemannianBundle (Fin n → ℝ) (fun (x : M) ↦ TangentSpace 𝓘(ℝ, Fin n → ℝ) x)]
  [IsRiemannianManifold 𝓘(ℝ, Fin n → ℝ) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [PreconnectedSpace M]

/-- Lipschitz in `d_a` gives Lipschitz in `d_b` with constant `e·Lip` when `κ|b − a| ≤ 1`. -/
theorem lip_two_times {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (hab : G.κ * |b - a| ≤ 1) (f : M → ℝ) (Lip : ℝ) (hLip : 0 ≤ Lip)
    (hLa : ∀ x y, |f y - f x| ≤ Lip * G.dist x y a) :
    (∀ x y, |f y - f x| ≤ Lip * Real.exp 1 * G.dist x y a)
    ∧ ∀ x y, |f y - f x| ≤ Lip * Real.exp 1 * G.dist x y b := by
  have he1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  constructor
  · intro x y
    have hd := G.dist_nonneg x y a
    calc |f y - f x| ≤ Lip * G.dist x y a := hLa x y
      _ = Lip * 1 * G.dist x y a := by ring
      _ ≤ Lip * Real.exp 1 * G.dist x y a := by gcongr
  · intro x y
    have hd := G.dist_nonneg x y b
    have hE : Real.exp (G.κ * |b - a|) ≤ Real.exp 1 := Real.exp_le_exp.2 hab
    calc |f y - f x| ≤ Lip * G.dist x y a := hLa x y
      _ ≤ Lip * (Real.exp (G.κ * |b - a|) * G.dist x y b) :=
          mul_le_mul_of_nonneg_left (dist_le_exp_dist G ha hb hcont x y) hLip
      _ ≤ Lip * (Real.exp 1 * G.dist x y b) := by gcongr
      _ = Lip * Real.exp 1 * G.dist x y b := by ring

/-- **(d) The first inequality of `prop:dotLN-diff`, form `C δ'/ξ`, ALL geometric hypotheses
discharged.**  Compact connected Riemannian manifold modelled on `Fin n → ℝ`, `TimeMetric`
continuous in the base point at time `a`, sampling law `m₀ μH[n] ≤ m ≤ m₁ μH[n]` (`μH[n]` the
Hausdorff measure; NOT identified with the Riemannian volume), `s₀ > 0`.  There are `A_m ≥ 0`,
`r₀ > 0`, `c_q > 0`, `ξ₀ ∈ (0,1]` such that for every sample, `N ≥ 2`, `0 < ξ ≤ ξ₀`, profile `h ≥ 0`
with `|h|, |h'| ≤ A e^{−t}` (`A > 0`), `h ≥ h₀ > 0` on `[0, s₀]`, measurable `f` that is
`Lip`-Lipschitz in `d_a` (HYPOTHESIS), `c_h > 0`, and `92416 Λ¹⁴ · 3 log N ≤ N ξⁿ`
(`Λ = lipLam n A_m r₀ A κ (c_q h₀) (e·Lip)`): with probability at least `1 − 30/N²`, for all `i < N`,
`|Δ_η(L_N f)(i) − Δ_η(L_ξ f)(X_i)| ≤ (2/c_h) · 3 660 000 Λ²⁰ √(3 log N/(N ξⁿ)) / ξ`. -/
theorem npoint_step5_lip_geom_log {s : Set ℝ} (G : TimeMetric 𝓘(ℝ, Fin n → ℝ) M s) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s)
    (hcont : Continuous (fun x ↦
      TotalSpace.mk' ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) x (G.g a x)))
    (hab : G.κ * |b - a| ≤ 1) (hne : b ≠ a)
    (m : Measure M) [IsProbabilityMeasure m] (m₀ m₁ : ℝ) (hm₀ : 0 < m₀) (hm₁ : 0 ≤ m₁)
    (hlow : ∀ t, ENNReal.ofReal m₀ * μH[(n:ℝ)] t ≤ m t)
    (hup : ∀ t, m t ≤ ENNReal.ofReal m₁ * μH[(n:ℝ)] t) (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ Am ≥ (0:ℝ), ∃ r₀ > (0:ℝ), ∃ cq > (0:ℝ), ∃ ξ₀ > (0:ℝ), ξ₀ ≤ 1 ∧
      ∀ (Ω : Type u) [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → M), iIndepFun X μ → (∀ j, Measurable (X j)) → (∀ j, μ.map (X j) = m) →
      ∀ (N : ℕ), 2 ≤ N → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
      ∀ (h h' : ℝ → ℝ) (A h₀ : ℝ), 0 < A → (∀ t, HasDerivAt h (h' t) t) →
        (∀ t, 0 ≤ t → |h' t| ≤ A * Real.exp (-t)) → (∀ t, 0 ≤ t → |h t| ≤ A * Real.exp (-t)) →
        (∀ t, 0 ≤ h t) → 0 < h₀ → (∀ t, 0 ≤ t → t ≤ s₀ → h₀ ≤ h t) →
      ∀ (f : M → ℝ), Measurable f → ∀ Lip : ℝ, 0 ≤ Lip →
        (∀ x y, |f y - f x| ≤ Lip * G.dist x y a) →
      ∀ ch : ℝ, 0 < ch →
      92416 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 14 * (3 * Real.log N)
        ≤ N * ξ ^ n →
      μ.real {ω | ∃ i < N,
        2 / ch * (3660000 * lipLam n Am r₀ A G.κ (cq * h₀) (Lip * Real.exp 1) ^ 20
          * Real.sqrt (3 * Real.log N / (N * ξ ^ n))) / ξ
        < |qDiff X N m (kern G h ξ a) (kern G h ξ b) f (b - a) i ω| / (ch * ξ ^ 2 / 2)}
        ≤ 30 / (N : ℝ) ^ 2 := by
  obtain ⟨Am, hAm, r₀, hr₀, hga, hgb⟩ := growth_two_times G ha hb hcont m m₁ hm₁ hup
  obtain ⟨cq, hcq, ξ₀, hξ₀, hq⟩ := popNorm_lower_two_times G ha hb hcont m m₀ hm₀ hlow s₀ hs₀
  refine ⟨Am, hAm, r₀, hr₀, cq, hcq, min ξ₀ 1, lt_min hξ₀ one_pos, min_le_right _ _, ?_⟩
  intro Ω mΩ μ _ X h_indep hX hlaw N hN ξ hξ hξξ₀ h h' A h₀ hA hder hbd hh hh0 hh₀ hlo
    f hf Lip hLip hLa ch hch hNL
  have hN0 : 0 < N := by omega
  have hhc : Continuous h := continuous_iff_continuousAt.2 fun t => (hder t).continuousAt
  have hqab := hq h A h₀ hhc hA.le hh hh0 hh₀.le hlo ξ hξ (hξξ₀.trans (min_le_left _ _))
  obtain ⟨hLa', hLb'⟩ := lip_two_times G ha hb hcont hab f Lip hLip hLa
  rw [← exp_neg_three_log N hN0]
  exact npoint_step5_lip_norm G ha hcont ha hb hab hne m X h_indep hX hlaw N hN0 n Am r₀ ξ hAm
    hr₀ hξ (hξξ₀.trans (min_le_right _ _)) hga hgb h h' A hA hder hbd hh hh0 f hf
    (Lip * Real.exp 1) (by positivity) hLa' hLb' (cq * h₀) (by positivity)
    (fun y => (hqab y).1) (fun y => (hqab y).2) (3 * Real.log N) (three_log_ge_one N hN) hNL
    ch hch

end GeomLip

end CTG.NPointLip
