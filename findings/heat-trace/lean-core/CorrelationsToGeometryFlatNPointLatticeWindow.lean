/-
Fifty-sixth file: the window statement for the periodised Gaussian kernel (lattice sum `latK`) on the flat torus.
Namespace `CTG.FlatNPointLatticeWindow`; imports the fifty-second file (compiled module); check with
`./check_flat_npoint_lattice_window.sh`.
`rateK_L`: the one-pair statement of the fifty-second file with a general `L ≥ 1` (probability `≥ 1 − 15 N·2e^{−L}`).
`normK_event`: lower bound of the sample normalisation at a fixed time.  `LNK_lip`: Lipschitz dependence of the sample
operator on the time, pointwise in the sample, without powers of `N`.  `window_detK`: the grid argument.
`flat_npoint_lattice_window`: for ALL pairs of times `τa, τb ∈ [p, q]` with `|τb − τa| ≥ η₀`, on one event, both
inequalities with the factor 2 (grid width `w` a parameter with three conditions).
`flat_npoint_lattice_window_N2`: the same without free parameters, `L = 4 log N`, single numerical condition
`92416 Λ¹⁴ · 4 log N ≤ N ξⁿ`, exceptional probability `≤ 32 D²/N²` with `D = Dwin …` independent of `N`.
HYPOTHESES on `f`: periodic, `C⁴` with bounded fourth derivative, Lipschitz, bounded; in the window statement a bound
`G₂` for `lapG S f`, in the parameter-free form a bound `M₂` for the second derivative.
NOT shown: measurability of the exceptional set (an uncountable union; the bounds are for the outer measure); pairs
with `|τb − τa| < η₀`; the form with `m₂ = 1` inserted (`gam₂_eq_one` of the fifty-third file is not used here); the
constants are not evaluated, `D` is large and contains negative powers of `ξ`.  Several auxiliary statements are
copies from the forty-first file, which has no compiled module.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 27 November 2026; read by nobody.
-/
import CorrelationsToGeometryFlatNPointLatticeDirect

open MeasureTheory ProbabilityTheory Set Filter Topology
open CTG.NPoint CTG.NPointSharp CTG.NPointLip CTG.FlatLB CTG.FlatLB2 CTG.FlatLB3 CTG.FlatLB4
  CTG.FlatNPoint CTG.FlatNPointRate CTG.FlatNPointFinal CTG.FlatNPointGauss CTG.FlatNPointGaussFull
  CTG.FlatNPointGaussLattice CTG.FlatNPointLatticePop CTG.FlatNPointLatticeDirect
  CTG.FlatNPointClose CTG.FlatNPointWindow

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace CTG.FlatNPointLatticeWindow

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-! ### Stage 1: the single-pair statement with a general Bernstein parameter `L` -/

set_option maxHeartbeats 3200000 in
theorem rateK_L_raw (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (τa τb : ℝ) (hne : τb ≠ τa) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * L ≤ N * ξ ^ n) :
    μ.real {ω | ∃ i < N, ¬ (
        |(LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω) / (τb - τa)
          - (Lmet gauss (gam₂ n) S (a τb) ξ f (X i ω)
              - Lmet gauss (gam₂ n) S (a τa) ξ f (X i ω)) / (τb - τa)|
        ≤ 7320000 * dLam S a₀ a₁ La Lip ^ 20 / gam₂ n
            * Real.sqrt (L / (N * ξ ^ n)) / ξ
      ∧ |(LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω
              - LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω) / (τb - τa)
          + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)|
        ≤ 7320000 * dLam S a₀ a₁ La Lip ^ 20 / gam₂ n
            * Real.sqrt (L / (N * ξ ^ n)) / ξ
          + ξ ^ 2 * min (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gaμ₄ n
                / (6 * gam₂ n * gaK₀ n * a₀ ^ 4) / |τb - τa|)
              (M₄ * ‖(S : E →L[ℝ] E)‖ ^ 4 * gaμ₄ n * La / (3 * gam₂ n * gaK₀ n * a₀ ^ 5)))}
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  obtain ⟨l1, lG, lIG, lI, lII, lP0, lFG, lFI, lFiG, lFiI⟩ := dLam_bounds S a₀ a₁ La Lip
  set Λ := dLam S a₀ a₁ La Lip with hΛ
  set xn := ξ ^ n with hx
  set δ := Real.sqrt (L / (N * xn)) with hδdef
  set G := Gb n S a₀ with hG
  set I := Ic n S a₀ with hI
  set P0 := P0c S a₁ with hP0
  set cI := 3 * a₁ * La / a₀ ^ 2 with hcI
  set cF := 4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀ with hcF
  set cFi := 18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3 with hcFi
  set m₂ := gam₂ n with hm₂def
  set η := τb - τa with hη
  have hm₂ : 0 < m₂ := gam₂_pos hn
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hx0 : 0 < xn := pow_pos hξ n
  have hx1 : xn ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hd := dS_pos S
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hfc : Continuous f := hf.continuous
  have hη0 : η ≠ 0 := sub_ne_zero.2 hne
  have hdiff : |a τb - a τa| ≤ La * |η| := a_lip a a' hda hLa τa τb
  have hG0 : 0 < G := Gb_pos S a₀
  have hI0 : 0 < I := Ic_pos S ha₀
  have hP00 : 0 < P0 := by simp only [hP0, P0c]; positivity
  have hcI0 : 0 ≤ cI := by rw [hcI]; positivity
  have hcF0 : 0 ≤ cF := by rw [hcF]; positivity
  have hcFi0 : 0 ≤ cFi := by rw [hcFi]; positivity
  have hΛ0 : 0 < Λ := by linarith
  have hIx0 : 0 ≤ I * xn := by positivity
  -- measurability
  have hKm : ∀ τ, Measurable fun p : E × E => latK S (ξ / a τ) p.1 p.2 := fun τ =>
    latS_measurable (ΦK_meas S ξ (a τ)) fun x z => (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).1
  have hgm : Measurable fun p : E × E => gd f p.1 p.2 :=
    (hfc.measurable.comp measurable_snd).sub (hfc.measurable.comp measurable_fst)
  -- the kernels
  have bK : ∀ τ x z, |latK S (ξ / a τ) x z| ≤ G := fun τ x z => by
    obtain ⟨-, h0, h1⟩ := latK_nonneg S hξ hξ1 ha₀ (ha τ) x z
    rw [abs_of_nonneg h0, hG]; linarith
  have LK : ∀ τ x, ∫ z, |latK S (ξ / a τ) x z| ∂mT ≤ I * xn := fun τ x' => by
    have := lat_L1 S hξ hξ1 ha₀ (ha τ) zero_le_one (ΦK_meas S ξ (a τ)) (ΦK_nonneg S ξ (a τ))
      (ΦK_dom S hξ (hpos τ)) (fun x z => le_of_eq (abs_of_nonneg
        (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).2.1)) x'
    rw [hI, hx]; exact this.trans (le_of_eq (one_mul _))
  have GK : ∀ τ, Good mT (latK S (ξ / a τ)) G (G * (I * xn)) := fun τ =>
    good_of _ (hKm τ) hG0.le (bK τ) hIx0 (LK τ)
  -- the kernels times the test increment
  have bF : ∀ τ x z, |latK S (ξ / a τ) x z * gd f x z| ≤ ξ * (cF * G) := fun τ x z => by
    have h1 := latK_test S hξ hξ1 ha₀ (ha τ) hLip0 hper hLip x z
    have h2 := (lat_bound S hξ hξ1 ha₀ (ha τ) (by positivity) (Φ1_nonneg S ξ (a τ) hLip0)
      (Φ1_dom S hξ ha₀ (ha τ) hLip0) x z).2.2
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = ξ * (cF * G) := by rw [hcF, hG]; ring
  have hFm : ∀ τ, Measurable fun p : E × E => latK S (ξ / a τ) p.1 p.2 * gd f p.1 p.2 :=
    fun τ => (hKm τ).mul hgm
  have LF : ∀ τ x, ∫ z, |latK S (ξ / a τ) x z * gd f x z| ∂mT ≤ ξ * (cF * (I * xn)) :=
    fun τ x' => by
      have := lat_L1 S hξ hξ1 ha₀ (ha τ) (by positivity) (Φ1_meas S ξ (a τ) Lip)
        (Φ1_nonneg S ξ (a τ) hLip0) (Φ1_dom S hξ ha₀ (ha τ) hLip0)
        (fun x z => latK_test S hξ hξ1 ha₀ (ha τ) hLip0 hper hLip x z) x'
      calc _ ≤ _ := this
        _ = ξ * (cF * (I * xn)) := by rw [hcF, hI, hx]; ring
  have GF : ∀ τ, Good mT (fun x z => latK S (ξ / a τ) x z * gd f x z) (ξ * (cF * G))
      (ξ ^ 2 * (cF * G * (cF * (I * xn)))) := fun τ =>
    good_mono (good_of _ (hFm τ) (by positivity) (bF τ) (by positivity) (LF τ)) le_rfl
      (le_of_eq (by ring))
  -- the time difference quotient
  have bD : ∀ x z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η| ≤ cI * G := fun x z => by
    have h1 := latK_dq S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff x z
    have h2 := (lat_bound S hξ hξ1 ha₀ le_rfl hcI0 (ΦD_nonneg S ξ a₀ ha₁0.le hLa0)
      (ΦD_dom S hξ ha₀ ha₁0.le hLa0) x z).2.2
    rw [hcI, hG]; exact h1.trans h2
  have hDm : Measurable fun p : E × E => (latK S (ξ / a τb) p.1 p.2 - latK S (ξ / a τa) p.1 p.2) / η :=
    ((hKm τb).sub (hKm τa)).div_const _
  have LD : ∀ x, ∫ z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η| ∂mT ≤ cI * (I * xn) :=
    fun x' => by
      have := lat_L1 S hξ hξ1 ha₀ le_rfl (by positivity) (ΦD_meas S ξ a₀ a₁ La)
        (ΦD_nonneg S ξ a₀ ha₁0.le hLa0) (ΦD_dom S hξ ha₀ ha₁0.le hLa0)
        (fun x z => latK_dq S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff x z) x'
      rw [hcI, hI, hx]; exact this
  have GD : Good mT (fun x z => (latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η) (cI * G)
      (cI * G * (cI * (I * xn))) :=
    good_of _ hDm (by positivity) bD (by positivity) LD
  have bDt : ∀ x z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η * gd f x z|
      ≤ ξ * (cFi * G) := fun x z => by
    have h1 := latK_dq_test S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff hLip0
      hper hLip x z
    have h2 := (lat_bound S hξ hξ1 ha₀ le_rfl (by positivity) (ΦDt_nonneg S ξ a₀ ha₁0.le hLa0 hLip0)
      (ΦDt_dom S hξ ha₀ ha₁0.le hLa0 hLip0) x z).2.2
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ = ξ * (cFi * G) := by rw [hcFi, hG]; ring
  have hDtm : Measurable fun p : E × E =>
      (latK S (ξ / a τb) p.1 p.2 - latK S (ξ / a τa) p.1 p.2) / η * gd f p.1 p.2 := hDm.mul hgm
  have LDt : ∀ x, ∫ z, |(latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η * gd f x z| ∂mT
      ≤ ξ * (cFi * (I * xn)) := fun x' => by
    have := lat_L1 S hξ hξ1 ha₀ le_rfl (by positivity) (ΦDt_meas S ξ a₀ a₁ La Lip)
      (ΦDt_nonneg S ξ a₀ ha₁0.le hLa0 hLip0) (ΦDt_dom S hξ ha₀ ha₁0.le hLa0 hLip0)
      (fun x z => latK_dq_test S hξ hξ1 ha₀ (ha τa) (ha₁ τa) (ha τb) (ha₁ τb) hLa0 hη0 hdiff
        hLip0 hper hLip x z) x'
    calc _ ≤ _ := this
      _ = ξ * (cFi * (I * xn)) := by rw [hcFi, hI, hx]; ring
  have GDt : Good mT (fun x z => (latK S (ξ / a τb) x z - latK S (ξ / a τa) x z) / η * gd f x z)
      (ξ * (cFi * G)) (ξ ^ 2 * (cFi * G * (cFi * (I * xn)))) :=
    good_mono (good_of _ hDtm (by positivity) bDt (by positivity) LDt) le_rfl (le_of_eq (by ring))
  -- normalisations
  have hc : 0 < P0 * xn := mul_pos hP00 hx0
  have hpa : ∀ y, P0 * xn ≤ popAvg mT (latK S (ξ / a τa)) y := fun y =>
    popAvg_latK_ge S hξ (hpos τa) (ha₁ τa) y
  have hpb : ∀ y, P0 * xn ≤ popAvg mT (latK S (ξ / a τb)) y := fun y =>
    popAvg_latK_ge S hξ (hpos τb) (ha₁ τb) y
  have hDa : ∀ y, (1:ℝ) ≤ popW mT (latK S (ξ / a τa)) (fun _ _ => 1) y := fun y => by
    rw [popW_latK_one S (div_pos hξ (hpos τa))]
  have hDb : ∀ y, (1:ℝ) ≤ popW mT (latK S (ξ / a τb)) (fun _ _ => 1) y := fun y => by
    rw [popW_latK_one S (div_pos hξ (hpos τb))]
  -- smallness and Ctx
  have hNx : (N : ℝ) * xn ≠ 0 := (mul_pos hN' hx0).ne'
  have hδ : δ ^ 2 * (N * xn) = L := by
    rw [hδdef, Real.sq_sqrt (div_nonneg (by linarith) (mul_pos hN' hx0).le)]; field_simp
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hPp : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * xn) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ 1 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((1 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hPp] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ l1
    nlinarith
  have C : Ctx N Λ xn xn⁻¹ δ L :=
    { hN := hN0, hΛ := l1, hx := hx0, hx1 := hx1, hxy := mul_inv_cancel₀ hx0.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL1 }
  have hvK : G * (I * xn) ≤ Λ ^ 2 * xn := by
    calc G * (I * xn) ≤ Λ * (Λ * xn) := mul_le_mul lG (mul_le_mul_of_nonneg_right lI hx0.le)
          hIx0 hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have hM' : I * xn ≤ Λ * xn := mul_le_mul_of_nonneg_right lI hx0.le
  have hci : (P0 * xn)⁻¹ ≤ Λ * xn⁻¹ := by
    rw [mul_inv]; exact mul_le_mul_of_nonneg_right lP0 (by positivity)
  have hcD1 : (1:ℝ)⁻¹ ≤ Λ ^ 2 := by rw [inv_one]; nlinarith
  have hsmall := C.small'_le hG0.le lG (by positivity) hvK hIx0 hM' hc hci one_pos hcD1 hsm
  have hMI : cI * (I * xn) ≤ Λ * xn := by
    calc cI * (I * xn) = cI * I * xn := by ring
      _ ≤ Λ * xn := mul_le_mul_of_nonneg_right lII hx0.le
  have hvI : cI * G * (cI * (I * xn)) ≤ Λ ^ 2 * xn := by
    calc cI * G * (cI * (I * xn)) ≤ Λ * (Λ * xn) := mul_le_mul lIG hMI (by positivity) hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have hMF : cF * (I * xn) ≤ Λ * xn := by
    calc cF * (I * xn) = cF * I * xn := by ring
      _ ≤ Λ * xn := mul_le_mul_of_nonneg_right lFI hx0.le
  have hvF : cF * G * (cF * (I * xn)) ≤ Λ ^ 2 * xn := by
    calc cF * G * (cF * (I * xn)) ≤ Λ * (Λ * xn) := mul_le_mul lFG hMF (by positivity) hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have hMFi : cFi * (I * xn) ≤ Λ * xn := by
    calc cFi * (I * xn) = cFi * I * xn := by ring
      _ ≤ Λ * xn := mul_le_mul_of_nonneg_right lFiI hx0.le
  have hvFi : cFi * G * (cFi * (I * xn)) ≤ Λ ^ 2 * xn := by
    calc cFi * G * (cFi * (I * xn)) ≤ Λ * (Λ * xn) := mul_le_mul lFiG hMFi (by positivity) hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have he := err5g_le C hG0.le lG (by positivity) hvK (by positivity) lIG (by positivity) hvI
    hIx0 hM' (by positivity) hMI hc hci one_pos hcD1
    (by positivity) lFG (by positivity) hvF (by positivity) hMF
    (by positivity) lFiG (by positivity) hvFi (by positivity) hMFi
  -- the template
  have H := step5g X h_indep hX hlaw N hN0 (latK S (ξ / a τa)) (latK S (ξ / a τb)) (gd f) η
    (GK τa) (GK τb) GD hc (by linarith) hpa hpb hIx0 (LK τa) (LK τb) (by positivity) LD
    (GF τa) (GF τb) GDt (by positivity) (LF τa) (LF τb) (by positivity) LDt one_pos hDa hDb
    hsmall.1 hsmall.2
  rw [err5g_scale N hξ.le] at H
  refine le_trans (measureReal_mono ?_) H
  intro ω hω
  obtain ⟨i, hi, hfail⟩ := hω
  refine ⟨i, hi, ?_⟩
  by_contra hle
  push_neg at hle
  apply hfail
  set e := err5g N G (G * (I * xn)) (cI * G) (cI * G * (cI * (I * xn))) (I * xn) (cI * (I * xn))
    (P0 * xn) L (cF * (I * xn)) (cF * G) (cF * G * (cF * (I * xn))) (cFi * (I * xn)) (cFi * G)
    (cFi * G * (cFi * (I * xn))) 1 with he_def
  set k := 2 / (m₂ * ξ ^ 2) with hk'
  have hk0 : 0 < k := by positivity
  set y := X i ω
  set rb := sampW X N (latK S (ξ / a τb)) (gd f) i ω / sampW X N (latK S (ξ / a τb)) (fun _ _ => 1) i ω
  set ra := sampW X N (latK S (ξ / a τa)) (gd f) i ω / sampW X N (latK S (ξ / a τa)) (fun _ _ => 1) i ω
  set Pb := popW mT (latK S (ξ / a τb)) (gd f) y / popW mT (latK S (ξ / a τb)) (fun _ _ => 1) y
  set Pa := popW mT (latK S (ξ / a τa)) (gd f) y / popW mT (latK S (ξ / a τa)) (fun _ _ => 1) y
  have eLb : LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω = -k * rb := rfl
  have eLa : LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω = -k * ra := rfl
  have eMb : Lmet gauss m₂ S (a τb) ξ f y = -k * Pb :=
    Lmet_pop_lat m₂ S (hpos τb) hξ hfc hB hper y
  have eMa : Lmet gauss m₂ S (a τa) ξ f y = -k * Pa :=
    Lmet_pop_lat m₂ S (hpos τa) hξ hfc hB hper y
  have key : (LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η
      = -k * ((rb - ra) / η - (Pb - Pa) / η) := by
    rw [eLb, eLa, eMb, eMa]; field_simp; ring
  have hbound : k * (ξ * e) ≤ 7320000 * Λ ^ 20 / m₂ * δ / ξ := by
    have h1 : k * (ξ * e) = 2 / m₂ * e / ξ := by rw [hk']; field_simp
    rw [h1]
    have h2 : 2 / m₂ * e ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    calc 2 / m₂ * e / ξ ≤ 2 / m₂ * (3660000 * Λ ^ 20 * δ) / ξ :=
          div_le_div_of_nonneg_right h2 hξ.le
      _ = 7320000 * Λ ^ 20 / m₂ * δ / ξ := by ring
  have hI' : |(LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η|
      ≤ 7320000 * Λ ^ 20 / m₂ * δ / ξ := by
    rw [key, abs_mul, abs_neg, abs_of_pos hk0]
    exact (mul_le_mul_of_nonneg_left hle hk0.le).trans hbound
  refine ⟨hI', ?_⟩
  have hpop := metric_dq_min (radK_gauss (n := n)) hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ y τa τb hne
  have tri := abs_add_le
    ((LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η)
    ((Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η
      + (lapG S f y / a τb ^ 2 - lapG S f y / a τa ^ 2) / η)
  have e2 : (LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      + (lapG S f y / a τb ^ 2 - lapG S f y / a τa ^ 2) / η
      = ((LNK X N (latK S (ξ / a τb)) m₂ ξ f i ω - LNK X N (latK S (ξ / a τa)) m₂ ξ f i ω) / η
      - (Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η)
      + ((Lmet gauss m₂ S (a τb) ξ f y - Lmet gauss m₂ S (a τa) ξ f y) / η
      + (lapG S f y / a τb ^ 2 - lapG S f y / a τa ^ 2) / η) := by ring
  rw [e2]
  exact le_trans tri (add_le_add hI' hpop)
/-- `rateK_L_raw` in a named-set form, with the abbreviations of the window file. -/
def dqIK {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (τa τb : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω - LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω)
      / (τb - τa)
    - (Lmet gauss (gam₂ n) S (a τb) ξ f (X i ω) - Lmet gauss (gam₂ n) S (a τa) ξ f (X i ω))
      / (τb - τa)

def dqIIK {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (τa τb : ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (LNK X N (latK S (ξ / a τb)) (gam₂ n) ξ f i ω - LNK X N (latK S (ξ / a τa)) (gam₂ n) ξ f i ω)
      / (τb - τa)
    + (lapG S f (X i ω) / a τb ^ 2 - lapG S f (X i ω) / a τa ^ 2) / (τb - τa)

def FIK {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (i : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  LNK X N (latK S (ξ / a τ)) (gam₂ n) ξ f i ω - Lmet gauss (gam₂ n) S (a τ) ξ f (X i ω)

def FIIK {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (i : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  LNK X N (latK S (ξ / a τ)) (gam₂ n) ξ f i ω + lapG S f (X i ω) / a τ ^ 2

theorem dqIK_eq {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ)
    (f : E → ℝ) (τa τb : ℝ) (i : ℕ) (ω : Ω) :
    dqIK X N S a ξ f τa τb i ω = (FIK X N S a ξ f i ω τb - FIK X N S a ξ f i ω τa) / (τb - τa) := by
  unfold dqIK FIK; ring

theorem dqIIK_eq {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ)
    (f : E → ℝ) (τa τb : ℝ) (i : ℕ) (ω : Ω) :
    dqIIK X N S a ξ f τa τb i ω
      = (FIIK X N S a ξ f i ω τb - FIIK X N S a ξ f i ω τa) / (τb - τa) := by
  unfold dqIIK FIIK; ring

/-- The exceptional set of one pair of times for the lattice kernel. -/
def badLK {Ω : Type*} (X : ℕ → Ω → E) (N : ℕ) (S : E ≃L[ℝ] E) (a : ℝ → ℝ) (ξ : ℝ) (f : E → ℝ)
    (τa τb Er C₁ C₂ : ℝ) : Set Ω :=
  {ω | ∃ i < N, ¬ (|dqIK X N S a ξ f τa τb i ω| ≤ Er
      ∧ |dqIIK X N S a ξ f τa τb i ω| ≤ Er + popErr ξ C₁ C₂ (τb - τa))}

/-- **Single pair, general `L`, named form.** -/
theorem rateK_L (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B : ℝ} (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (τa τb : ℝ) (hne : τb ≠ τa) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * L ≤ N * ξ ^ n) :
    μ.real (badLK X N S a ξ f τa τb (rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ)
        (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S) (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S))
      ≤ 15 * (N * (2 * Real.exp (-L))) := by
  unfold badLK dqIK dqIIK popErr rateE Cone Ctwo
  exact rateK_L_raw hn X h_indep hX hlaw N hN hf hM hM₄ hper hLip0 hLip hB S a a' hda ha₀ ha ha₁
    hLa hξ hξ1 τa τb hne hL1 hNL

/-! ### Stage 2: kernel bounds in time, the normalisation event, Lipschitz bound in time -/

/-- `cI = 3 a₁ L_a/a₀²`. -/
def cIk (a₀ a₁ La : ℝ) : ℝ := 3 * a₁ * La / a₀ ^ 2
/-- `cF = 4 Lip ‖S‖/a₀`. -/
def cFk (S : E ≃L[ℝ] E) (a₀ Lip : ℝ) : ℝ := 4 * Lip * ‖(S : E →L[ℝ] E)‖ / a₀
/-- `cFi = 18 Lip ‖S‖ a₁ L_a/a₀³`. -/
def cFik (S : E ≃L[ℝ] E) (a₀ a₁ La Lip : ℝ) : ℝ :=
  18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3

/-- **The lattice kernel is Lipschitz in time**: `|latK(τ=t) − latK(τ=s)| ≤ cI·G·|t − s|`. -/
theorem latK_tlip (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ)
    {a₀ a₁ La ξ : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (s t : ℝ) (x z : E) :
    |latK S (ξ / a t) x z - latK S (ξ / a s) x z| ≤ cIk a₀ a₁ La * Gb n S a₀ * |t - s| := by
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  by_cases hts : t = s
  · subst hts; simp only [sub_self, abs_zero, mul_zero, le_refl]
  · have hη : t - s ≠ 0 := sub_ne_zero.2 hts
    have h1 := latK_dq S hξ hξ1 ha₀ (ha s) (ha₁ s) (ha t) (ha₁ t) hLa0 hη
      (a_lip a a' hda hLa s t) x z
    have h2 := (lat_bound S hξ hξ1 ha₀ le_rfl (by positivity : 0 ≤ 3 * a₁ * La / a₀ ^ 2)
      (ΦD_nonneg S ξ a₀ ha₁0.le hLa0) (ΦD_dom S hξ ha₀ ha₁0.le hLa0) x z).2.2
    have h3 := h1.trans h2
    rw [abs_div, div_le_iff₀ (abs_pos.2 hη)] at h3
    unfold cIk; exact h3

/-- The lattice kernel times the test increment: `|latK · (f(z) − f(x))| ≤ ξ·cF·G`. -/
theorem latK_gd_bound (S : E ≃L[ℝ] E) {ξ a a₀ Lip : ℝ} (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (ha₀ : 0 < a₀)
    (ha : a₀ ≤ a) (hL : 0 ≤ Lip) {f : E → ℝ} (hper : Per f)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖) (x z : E) :
    |latK S (ξ / a) x z * gd f x z| ≤ ξ * (cFk S a₀ Lip * Gb n S a₀) := by
  have h1 := latK_test S hξ hξ1 ha₀ ha hL hper hLip x z
  have h2 := (lat_bound S hξ hξ1 ha₀ ha (by positivity) (Φ1_nonneg S ξ a hL)
    (Φ1_dom S hξ ha₀ ha hL) x z).2.2
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ = ξ * (cFk S a₀ Lip * Gb n S a₀) := by unfold cFk; ring

/-- Time increment of the lattice kernel times the test increment. -/
theorem latK_tlip_test (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ)
    {a₀ a₁ La ξ Lip : ℝ} (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁)
    (hLa : ∀ τ, |a' τ| ≤ La) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hL : 0 ≤ Lip) {f : E → ℝ}
    (hper : Per f) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖) (s t : ℝ) (x z : E) :
    |latK S (ξ / a t) x z * gd f x z - latK S (ξ / a s) x z * gd f x z|
      ≤ ξ * (cFik S a₀ a₁ La Lip * Gb n S a₀) * |t - s| := by
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  by_cases hts : t = s
  · subst hts; simp only [sub_self, abs_zero, mul_zero, le_refl]
  · have hη : t - s ≠ 0 := sub_ne_zero.2 hts
    have h1 := latK_dq_test S hξ hξ1 ha₀ (ha s) (ha₁ s) (ha t) (ha₁ t) hLa0 hη
      (a_lip a a' hda hLa s t) hL hper hLip x z
    have h2 := (lat_bound S hξ hξ1 ha₀ le_rfl
      (by positivity : 0 ≤ ξ * (18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3))
      (ΦDt_nonneg S ξ a₀ ha₁0.le hLa0 hL) (ΦDt_dom S hξ ha₀ ha₁0.le hLa0 hL) x z).2.2
    have e : latK S (ξ / a t) x z * gd f x z - latK S (ξ / a s) x z * gd f x z
        = (latK S (ξ / a t) x z - latK S (ξ / a s) x z) / (t - s) * gd f x z * (t - s) := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hη, sub_mul]
    rw [e, abs_mul]
    calc _ ≤ ξ * (18 * Lip * ‖(S : E →L[ℝ] E)‖ * a₁ * La / a₀ ^ 3) * Gb n S a₀ * |t - s| :=
          mul_le_mul_of_nonneg_right (h1.trans h2) (abs_nonneg _)
      _ = ξ * (cFik S a₀ a₁ La Lip * Gb n S a₀) * |t - s| := by unfold cFik; ring

set_option maxHeartbeats 1600000 in
/-- **Lower bound of the sample normalisation of `latK` at one time `g`**: outside an event of
probability `≤ N·2e^{−L}`, all `q_j(g) ≥ P₀ ξⁿ/2` (`P₀ = (2π)^{n/2}|det S|/a₁ⁿ`). -/
theorem normK_event {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    (S : E ≃L[ℝ] E) (a : ℝ → ℝ) {a₀ a₁ La Lip ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (g : ℝ) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * L ≤ N * ξ ^ n) :
    μ.real {ω | ∃ j < N, sampAvg X N (latK S (ξ / a g)) j ω < P0c S a₁ * ξ ^ n / 2}
      ≤ N * (2 * Real.exp (-L)) := by
  obtain ⟨l1, lG, -, lI, -, lP0, -, -, -, -⟩ := dLam_bounds S a₀ a₁ La Lip
  set Λ := dLam S a₀ a₁ La Lip with hΛ
  set xn := ξ ^ n with hx
  set δ := Real.sqrt (L / (N * xn)) with hδdef
  set G := Gb n S a₀ with hG
  set I := Ic n S a₀ with hI
  set P0 := P0c S a₁ with hP0
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hx0 : 0 < xn := pow_pos hξ n
  have hx1 : xn ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hd := dS_pos S
  have hpos : ∀ τ, 0 < a τ := fun τ => lt_of_lt_of_le ha₀ (ha τ)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hG0 : 0 < G := Gb_pos S a₀
  have hI0 : 0 < I := Ic_pos S ha₀
  have hP00 : 0 < P0 := by simp only [hP0, P0c]; positivity
  have hΛ0 : 0 < Λ := by linarith
  have hIx0 : 0 ≤ I * xn := by positivity
  have hKm : Measurable fun p : E × E => latK S (ξ / a g) p.1 p.2 :=
    latS_measurable (ΦK_meas S ξ (a g)) fun x z => (latK_nonneg S hξ hξ1 ha₀ (ha g) x z).1
  have bK : ∀ x z, |latK S (ξ / a g) x z| ≤ G := fun x z => by
    obtain ⟨-, h0, h1⟩ := latK_nonneg S hξ hξ1 ha₀ (ha g) x z
    rw [abs_of_nonneg h0, hG]; linarith
  have LK : ∀ x, ∫ z, |latK S (ξ / a g) x z| ∂mT ≤ I * xn := fun x' => by
    have := lat_L1 S hξ hξ1 ha₀ (ha g) zero_le_one (ΦK_meas S ξ (a g)) (ΦK_nonneg S ξ (a g))
      (ΦK_dom S hξ (hpos g)) (fun x z => le_of_eq (abs_of_nonneg
        (latK_nonneg S hξ hξ1 ha₀ (ha g) x z).2.1)) x'
    rw [hI, hx]; exact this.trans (le_of_eq (one_mul _))
  have GK : Good mT (latK S (ξ / a g)) G (G * (I * xn)) := good_of _ hKm hG0.le bK hIx0 LK
  have hc : 0 < P0 * xn := mul_pos hP00 hx0
  have hci : (P0 * xn)⁻¹ ≤ Λ * xn⁻¹ := by
    rw [mul_inv]; exact mul_le_mul_of_nonneg_right lP0 (by positivity)
  have hδ : δ ^ 2 * (N * xn) = L := by
    rw [hδdef, Real.sq_sqrt (div_nonneg (by linarith) (mul_pos hN' hx0).le)]; field_simp
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hsm : 304 * Λ ^ 7 * δ ≤ 1 := by
    have hPp : (0:ℝ) < 304 * Λ ^ 7 := by positivity
    have h1 : L / (N * xn) ≤ (1 / (304 * Λ ^ 7)) ^ 2 := by
      rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      have : (304 * Λ ^ 7) ^ 2 = 92416 * Λ ^ 14 := by ring
      rw [this]; nlinarith
    have h2 : δ ≤ 1 / (304 * Λ ^ 7) := by
      calc δ ≤ Real.sqrt ((1 / (304 * Λ ^ 7)) ^ 2) := Real.sqrt_le_sqrt h1
        _ = 1 / (304 * Λ ^ 7) := Real.sqrt_sq (by positivity)
    rw [le_div_iff₀ hPp] at h2; linarith
  have hδ1 : δ ≤ 1 := by
    have : 1 ≤ Λ ^ 7 := one_le_pow₀ l1
    nlinarith
  have C : Ctx N Λ xn xn⁻¹ δ L :=
    { hN := hN0, hΛ := l1, hx := hx0, hx1 := hx1, hxy := mul_inv_cancel₀ hx0.ne', hδ0 := hδ0,
      hδ1 := hδ1, hδ := hδ, hL := hL1 }
  have hvK : G * (I * xn) ≤ Λ ^ 2 * xn := by
    calc G * (I * xn) ≤ Λ * (Λ * xn) := mul_le_mul lG (mul_le_mul_of_nonneg_right lI hx0.le)
          hIx0 hΛ0.le
      _ = Λ ^ 2 * xn := by ring
  have hM' : I * xn ≤ Λ * xn := mul_le_mul_of_nonneg_right lI hx0.le
  have hcD1 : (1:ℝ)⁻¹ ≤ Λ ^ 2 := by rw [inv_one]; nlinarith
  have hsmall := (C.small'_le hG0.le lG (by positivity) hvK hIx0 hM' hc hci one_pos hcD1 hsm).1
  have hdev : dev N G (G * (I * xn)) L ≤ P0 * xn / 2 := by
    rw [div_le_iff₀ hc] at hsmall; linarith
  have Hp := GK.prob X h_indep hX hlaw N hN0 (by linarith : 0 < L)
  refine le_trans (measureReal_mono ?_) Hp
  intro ω hω
  obtain ⟨j, hj, hlt⟩ := hω
  refine ⟨j, hj, ?_⟩
  have hpop := popAvg_latK_ge S hξ (hpos g) (ha₁ g) (X j ω)
  calc dev N G (G * (I * xn)) L ≤ P0 * xn / 2 := hdev
    _ < popAvg mT (latK S (ξ / a g)) (X j ω) - sampAvg X N (latK S (ξ / a g)) j ω := by linarith
    _ ≤ |sampAvg X N (latK S (ξ / a g)) j ω - popAvg mT (latK S (ξ / a g)) (X j ω)| := by
        rw [abs_sub_comm]; exact le_abs_self _

/-- `ratio_lip` with separate bounds `U` for `|Ks g|` and `D` for `|Kt g − Ks g|`. -/
theorem ratio_lip2 {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) {Ks Kt g : E → E → ℝ}
    {A U D e c : ℝ} (hc : 0 < c) (hU : 0 ≤ U)
    (hsn : ∀ x z, 0 ≤ Ks x z) (hsA : ∀ x z, Ks x z ≤ A)
    (htn : ∀ x z, 0 ≤ Kt x z) (htA : ∀ x z, Kt x z ≤ A)
    (hlip : ∀ x z, |Kt x z - Ks x z| ≤ e)
    (hsg : ∀ x z, |Ks x z * g x z| ≤ U)
    (hdg : ∀ x z, |Kt x z * g x z - Ks x z * g x z| ≤ D)
    (ω : Ω) (hqs : ∀ j < N, c ≤ sampAvg X N Ks j ω) (hqt : ∀ j < N, c ≤ sampAvg X N Kt j ω)
    {i : ℕ} (hi : i < N) :
    |sampW X N Kt g i ω / sampW X N Kt (fun _ _ => 1) i ω
        - sampW X N Ks g i ω / sampW X N Ks (fun _ _ => 1) i ω|
      ≤ (D / c + U * e / c ^ 2) / (c / A)
        + U / c * (e / c + A * e / c ^ 2) / (c / A) ^ 2 := by
  have hqsA := fun j => sampAvg_le X hN hsn hsA j ω
  have hA : 0 < A := lt_of_lt_of_le hc ((hqs i hi).trans (hqsA i))
  have hqd : ∀ j, |sampAvg X N Kt j ω - sampAvg X N Ks j ω| ≤ e := fun j =>
    sampAvg_close X hN hlip j ω
  have hNum : |sampW X N Kt g i ω - sampW X N Ks g i ω| ≤ D / c + U * e / c ^ 2 :=
    avgN_close hN
      (F := fun j => Kt (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Kt j ω))
      (G := fun j => Ks (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Ks j ω))
      fun j hj => term_close hc (hqs j hj) (hqt j hj) (hsg _ _) (hdg _ _) (hqd j)
  have hDen : |sampW X N Kt (fun _ _ => 1) i ω - sampW X N Ks (fun _ _ => 1) i ω|
      ≤ e / c + A * e / c ^ 2 :=
    avgN_close hN
      (F := fun j => Kt (X i ω) (X j ω) * 1 * (1 / sampAvg X N Kt j ω))
      (G := fun j => Ks (X i ω) (X j ω) * 1 * (1 / sampAvg X N Ks j ω))
      fun j hj => term_close hc (hqs j hj) (hqt j hj)
        (by rw [mul_one, abs_of_nonneg (hsn _ _)]; exact hsA _ _)
        (by rw [mul_one, mul_one]; exact hlip _ _) (hqd j)
  have hNs : |sampW X N Ks g i ω| ≤ U / c :=
    avgN_abs_le hN
      (F := fun j => Ks (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Ks j ω))
      fun j hj => by
        have hq0 : 0 < sampAvg X N Ks j ω := lt_of_lt_of_le hc (hqs j hj)
        show |Ks (X i ω) (X j ω) * g (X i ω) (X j ω) * (1 / sampAvg X N Ks j ω)| ≤ U / c
        rw [abs_mul, abs_of_pos (one_div_pos.2 hq0), div_eq_mul_one_div U c]
        exact mul_le_mul (hsg _ _) (one_div_le_one_div_of_le hc (hqs j hj))
          (one_div_pos.2 hq0).le hU
  have hDs := den_lower X hN hsn hsA hc ω hqs hi
  have hDt := den_lower X hN htn htA hc ω hqt hi
  rw [div_eq_mul_one_div (sampW X N Kt g i ω), div_eq_mul_one_div (sampW X N Ks g i ω)]
  exact term_close (div_pos hc hA) hDs hDt hNs hNum hDen

/-- The Lipschitz constant in time of the lattice sample operator, given `q_j ≥ c`. -/
def LNlipK (m₂ ξ A U e D c : ℝ) : ℝ :=
  2 / (m₂ * ξ ^ 2) * ((D / c + U * e / c ^ 2) / (c / A)
    + U / c * (e / c + A * e / c ^ 2) / (c / A) ^ 2)

/-- The constant `LNlipK` with the lattice-kernel bounds plugged in. -/
def LsK (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a₀ a₁ La Lip ξ c : ℝ) : ℝ :=
  LNlipK (gam₂ n) ξ (Gb n S a₀) (ξ * (cFk S a₀ Lip * Gb n S a₀)) (cIk a₀ a₁ La * Gb n S a₀)
    (ξ * (cFik S a₀ a₁ La Lip * Gb n S a₀)) c

theorem LsK_nonneg (hn : 1 ≤ n) (S : E ≃L[ℝ] E) {a₀ a₁ La Lip ξ c : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 ≤ a₁) (hLa : 0 ≤ La) (hLip : 0 ≤ Lip) (hξ : 0 < ξ) (hc : 0 < c) :
    0 ≤ LsK n S a₀ a₁ La Lip ξ c := by
  have := gam₂_pos hn
  have := Gb_pos S a₀
  unfold LsK LNlipK cFk cIk cFik; positivity

/-- **`τ ↦ L_N(τ) f(i)` for the lattice kernel is Lipschitz between two times at which all sample
normalisations are `≥ c`**, with constant `LsK` (no power of `N`). -/
theorem LNK_lip {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (hn : 1 ≤ n)
    {f : E → ℝ} {Lip : ℝ} (hper : Per f) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {c : ℝ} (hc : 0 < c) (s t : ℝ) (ω : Ω)
    (hqs : ∀ j < N, c ≤ sampAvg X N (latK S (ξ / a s)) j ω)
    (hqt : ∀ j < N, c ≤ sampAvg X N (latK S (ξ / a t)) j ω) {i : ℕ} (hi : i < N) :
    |LNK X N (latK S (ξ / a t)) (gam₂ n) ξ f i ω - LNK X N (latK S (ξ / a s)) (gam₂ n) ξ f i ω|
      ≤ LsK n S a₀ a₁ La Lip ξ c * |t - s| := by
  have hm₂ := gam₂_pos hn
  have hG0 := Gb_pos S a₀
  have hU0 : 0 ≤ ξ * (cFk S a₀ Lip * Gb n S a₀) := by unfold cFk; positivity
  have hnn : ∀ τ x z, 0 ≤ latK S (ξ / a τ) x z := fun τ x z =>
    (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).2.1
  have hle : ∀ τ x z, latK S (ξ / a τ) x z ≤ Gb n S a₀ := fun τ x z => by
    have := (latK_nonneg S hξ hξ1 ha₀ (ha τ) x z).2.2; linarith
  have key := ratio_lip2 X hN (Ks := latK S (ξ / a s)) (Kt := latK S (ξ / a t)) (g := gd f)
    (A := Gb n S a₀) (U := ξ * (cFk S a₀ Lip * Gb n S a₀))
    (D := ξ * (cFik S a₀ a₁ La Lip * Gb n S a₀) * |t - s|)
    (e := cIk a₀ a₁ La * Gb n S a₀ * |t - s|) hc hU0 (hnn s) (hle s) (hnn t) (hle t)
    (fun x z => latK_tlip S a a' hda ha₀ ha ha₁ hLa hξ hξ1 s t x z)
    (fun x z => latK_gd_bound S hξ hξ1 ha₀ (ha s) hLip0 hper hLip x z)
    (fun x z => latK_tlip_test S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hLip0 hper hLip s t x z)
    ω hqs hqt hi
  have eL : LNK X N (latK S (ξ / a t)) (gam₂ n) ξ f i ω
        - LNK X N (latK S (ξ / a s)) (gam₂ n) ξ f i ω
      = -(2 / (gam₂ n * ξ ^ 2))
        * (sampW X N (latK S (ξ / a t)) (gd f) i ω
            / sampW X N (latK S (ξ / a t)) (fun _ _ => 1) i ω
          - sampW X N (latK S (ξ / a s)) (gd f) i ω
            / sampW X N (latK S (ξ / a s)) (fun _ _ => 1) i ω) := by
    unfold LNK; ring
  have hk0 : (0:ℝ) < 2 / (gam₂ n * ξ ^ 2) := by positivity
  rw [eL, abs_mul, abs_neg, abs_of_pos hk0]
  refine (mul_le_mul_of_nonneg_left key hk0.le).trans (le_of_eq ?_)
  unfold LsK LNlipK; ring

/-- **Transfer of the lower bound of the sample normalisation of `latK`** from a grid time `g` to a
time `τ` with `cI·G·|τ − g| ≤ c/4`. -/
theorem sampAvgK_transfer {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N)
    (S : E ≃L[ℝ] E) (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {c g τ : ℝ}
    (hgr : cIk a₀ a₁ La * Gb n S a₀ * |τ - g| ≤ c / 4) (j : ℕ) (ω : Ω)
    (hg : c / 2 ≤ sampAvg X N (latK S (ξ / a g)) j ω) :
    c / 4 ≤ sampAvg X N (latK S (ξ / a τ)) j ω := by
  have := sampAvg_close X hN (fun x z => latK_tlip S a a' hda ha₀ ha ha₁ hLa hξ hξ1 g τ x z) j ω
  have := (abs_le.1 this).1
  linarith

/-! ### Stage 3: grid argument and window statement -/

set_option maxHeartbeats 800000 in
/-- **Deterministic window statement for the lattice kernel.**  Fix `ω`.  `T` a finite set of times
covering `[p, q]` with mesh `w`, `4w ≤ η₀`, `cI·G·w ≤ c/4`.  If at every time of `T` all sample
normalisations are `≥ c/2` and at every pair of distinct times of `T` the two inequalities hold with
error `Er`, then for all `τa, τb ∈ [p,q]` with `|τb − τa| ≥ η₀` they hold with the additional term
`4ℒw/η₀` and `2·popErr`. -/
theorem window_detK {Ω : Type*} (X : ℕ → Ω → E) {N : ℕ} (hN : 0 < N) (hn : 1 ≤ n)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄) (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂) (a a' : ℝ → ℝ)
    (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    {c w η₀ p q Er : ℝ} (hc : 0 < c) (hw : 0 ≤ w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀)
    (hwc : cIk a₀ a₁ La * Gb n S a₀ * w ≤ c / 4)
    (T : Finset ℝ) (hcov : ∀ τ ∈ Icc p q, ∃ g ∈ T, |τ - g| ≤ w) (ω : Ω)
    (hnorm : ∀ g ∈ T, ∀ j < N, c / 2 ≤ sampAvg X N (latK S (ξ / a g)) j ω)
    (hrate : ∀ ga ∈ T, ∀ gb ∈ T, gb ≠ ga → ∀ i < N,
      |dqIK X N S a ξ f ga gb i ω| ≤ Er
      ∧ |dqIIK X N S a ξ f ga gb i ω|
          ≤ Er + popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
            (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (gb - ga))
    {τa τb : ℝ} (hτa : τa ∈ Icc p q) (hτb : τb ∈ Icc p q) (hη : η₀ ≤ |τb - τa|)
    {i : ℕ} (hi : i < N) :
    |dqIK X N S a ξ f τa τb i ω|
        ≤ Er + 4 * (LsK n S a₀ a₁ La Lip ξ (c / 4)
            + (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + G₂ * (2 * La / a₀ ^ 3)))
            * w / η₀
    ∧ |dqIIK X N S a ξ f τa τb i ω|
        ≤ Er + 4 * (LsK n S a₀ a₁ La Lip ξ (c / 4) + G₂ * (2 * La / a₀ ^ 3)) * w / η₀
          + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
              (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (τb - τa) := by
  have hk := radK_gauss (n := n)
  have hm₂ := gam₂_pos hn
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hG0 : 0 ≤ G₂ := le_trans (abs_nonneg _) (hG₂ 0)
  have hμ₄ : 0 ≤ gaμ₄ n := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hK₀ := hk.kern.mass_pos
  have hC1 : 0 ≤ Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S := by unfold Cone; positivity
  have hC2 : 0 ≤ Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S := by unfold Ctwo; positivity
  have hc4 : 0 < c / 4 := by linarith
  have hGG0 : 0 ≤ G₂ * (2 * La / a₀ ^ 3) := by positivity
  have hLL0 : 0 ≤ LsK n S a₀ a₁ La Lip ξ (c / 4) :=
    LsK_nonneg hn S ha₀ ha₁0.le hLa0 hLip0 hξ hc4
  have hcIG0 : 0 ≤ cIk a₀ a₁ La * Gb n S a₀ := by
    have := Gb_pos S a₀; unfold cIk; positivity
  obtain ⟨ga, hga, hda'⟩ := hcov τa hτa
  obtain ⟨gb, hgb, hdb'⟩ := hcov τb hτb
  have hq : ∀ τ g, g ∈ T → |τ - g| ≤ w →
      ∀ j < N, c / 4 ≤ sampAvg X N (latK S (ξ / a τ)) j ω := by
    intro τ g hg hτg j hj
    exact sampAvgK_transfer X hN S a a' hda ha₀ ha ha₁ hLa hξ hξ1
      ((mul_le_mul_of_nonneg_left hτg hcIG0).trans hwc) j ω (hnorm g hg j hj)
  have hqa := hq τa ga hga hda'
  have hqb := hq τb gb hgb hdb'
  have hqga := hq ga ga hga (by rw [sub_self, abs_zero]; exact hw)
  have hqgb := hq gb gb hgb (by rw [sub_self, abs_zero]; exact hw)
  have hLN : ∀ s t, (∀ j < N, c / 4 ≤ sampAvg X N (latK S (ξ / a s)) j ω) →
      (∀ j < N, c / 4 ≤ sampAvg X N (latK S (ξ / a t)) j ω) →
      |LNK X N (latK S (ξ / a s)) (gam₂ n) ξ f i ω - LNK X N (latK S (ξ / a t)) (gam₂ n) ξ f i ω|
        ≤ LsK n S a₀ a₁ La Lip ξ (c / 4) * |s - t| := fun s t hs ht =>
    LNK_lip X hN hn hper hLip0 hLip S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hc4 t s ω ht hs hi
  have hLm : ∀ s t, |Lmet gauss (gam₂ n) S (a s) ξ f (X i ω) - Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)|
      ≤ (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + G₂ * (2 * La / a₀ ^ 3)) * |s - t| :=
    fun s t => Lmet_lip hk hm₂ hf hM hM₄ S a a' hda ha₀ ha hLa hξ (X i ω) (hG₂ _) t s
  have hLg : ∀ s t, |lapG S f (X i ω) / a s ^ 2 - lapG S f (X i ω) / a t ^ 2|
      ≤ G₂ * (2 * La / a₀ ^ 3) * |s - t| := fun s t =>
    lapterm_lip a a' hda ha₀ ha hLa (hG₂ _) t s
  have hF1 : ∀ s t, (∀ j < N, c / 4 ≤ sampAvg X N (latK S (ξ / a s)) j ω) →
      (∀ j < N, c / 4 ≤ sampAvg X N (latK S (ξ / a t)) j ω) →
      |FIK X N S a ξ f i ω s - FIK X N S a ξ f i ω t|
        ≤ (LsK n S a₀ a₁ La Lip ξ (c / 4)
          + (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + G₂ * (2 * La / a₀ ^ 3)))
            * |s - t| := by
    intro s t hs ht
    have e : FIK X N S a ξ f i ω s - FIK X N S a ξ f i ω t
        = (LNK X N (latK S (ξ / a s)) (gam₂ n) ξ f i ω - LNK X N (latK S (ξ / a t)) (gam₂ n) ξ f i ω)
          - (Lmet gauss (gam₂ n) S (a s) ξ f (X i ω) - Lmet gauss (gam₂ n) S (a t) ξ f (X i ω)) := by
      unfold FIK; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have h1 := hLN s t hs ht
    have h2 := hLm s t
    linarith
  have hF2 : ∀ s t, (∀ j < N, c / 4 ≤ sampAvg X N (latK S (ξ / a s)) j ω) →
      (∀ j < N, c / 4 ≤ sampAvg X N (latK S (ξ / a t)) j ω) →
      |FIIK X N S a ξ f i ω s - FIIK X N S a ξ f i ω t|
        ≤ (LsK n S a₀ a₁ La Lip ξ (c / 4) + G₂ * (2 * La / a₀ ^ 3)) * |s - t| := by
    intro s t hs ht
    have e : FIIK X N S a ξ f i ω s - FIIK X N S a ξ f i ω t
        = (LNK X N (latK S (ξ / a s)) (gam₂ n) ξ f i ω - LNK X N (latK S (ξ / a t)) (gam₂ n) ξ f i ω)
          + (lapG S f (X i ω) / a s ^ 2 - lapG S f (X i ω) / a t ^ 2) := by
      unfold FIIK; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have h1 := hLN s t hs ht
    have h2 := hLg s t
    linarith
  have hgap := grid_gap h4 hda' hdb' hη
  have hηpos : 0 < |τb - τa| := lt_of_lt_of_le hη₀ hη
  have hne : gb ≠ ga := by
    intro h0
    rw [h0, sub_self, abs_zero] at hgap
    linarith
  obtain ⟨r1, r2⟩ := hrate ga hga gb hgb hne i hi
  have g1 := grid_compare3 (F := FIK X N S a ξ f i ω)
    (add_nonneg hLL0 (add_nonneg (mul_nonneg (sq_nonneg ξ) hC2) hGG0))
    (hF1 τb gb hqb hqgb) (hF1 τa ga hqa hqga) (hF1 gb ga hqgb hqga) hη₀ hw h4 hda' hdb' hη
  have g2 := grid_compare3 (F := FIIK X N S a ξ f i ω) (add_nonneg hLL0 hGG0)
    (hF2 τb gb hqb hqgb) (hF2 τa ga hqa hqga) (hF2 gb ga hqgb hqga) hη₀ hw h4 hda' hdb' hη
  rw [dqIK_eq] at r1
  rw [dqIIK_eq] at r2
  rw [dqIK_eq, dqIIK_eq]
  refine ⟨tri_helper g1 r1, ?_⟩
  have hp := popErr_double (ξ := ξ) hC1 hC2 hηpos hgap
  have := tri_helper g2 r2
  linarith

set_option maxHeartbeats 1600000 in
/-- **The window statement for the lattice-sum Gaussian kernel** (`prop:dotLN-diff`, flat periodic
case, all pairs of times of a window on one event).  Setting of `flat_npoint_lattice_direct`; in
addition a bound `G₂` on `|lapG S f|` (HYPOTHESIS), a window `[p, q]`, a minimal separation
`η₀ > 0`, a Bernstein parameter `L ≥ 1` with `92416 Λ¹⁴ L ≤ N ξⁿ`, and a grid width `w > 0` with
`4w ≤ η₀`, `cI·G·w ≤ P₀ξⁿ/4` and `4(ℒ_N + ξ²C₂ + 2G₂L_a/a₀³)·w ≤ E·η₀`
(`E = (7320000 Λ²⁰/m₂) √(L/(N ξⁿ))/ξ`, `ℒ_N = LsK …(P₀ξⁿ/4)`).  Then outside an event of (outer)
probability at most `(K+1)·N·2e^{−L} + (K+1)²·15·N·2e^{−L}`, `K = ⌊(q−p)/w⌋`, for ALL
`τa, τb ∈ [p, q]` with `|τb − τa| ≥ η₀` and all `i < N`: `|dqIK| ≤ 2E` and
`|dqIIK| ≤ 2E + 2ξ² min{C₁/|η|, C₂}`. -/
theorem flat_npoint_lattice_window (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B G₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B) (S : E ≃L[ℝ] E) (hG₂ : ∀ x, |lapG S f x| ≤ G₂)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * L ≤ N * ξ ^ n)
    {p q w η₀ : ℝ} (hw : 0 < w) (hη₀ : 0 < η₀) (h4 : 4 * w ≤ η₀)
    (hwc : cIk a₀ a₁ La * Gb n S a₀ * w ≤ P0c S a₁ * ξ ^ n / 4)
    (hwE : 4 * (LsK n S a₀ a₁ La Lip ξ (P0c S a₁ * ξ ^ n / 4)
            + (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + G₂ * (2 * La / a₀ ^ 3))) * w
          ≤ rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ * η₀) :
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqIK X N S a ξ f τa τb i ω| ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ
        ∧ |dqIIK X N S a ξ f τa τb i ω|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ
            + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
                (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (τb - τa))}
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
  have hsub : {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqIK X N S a ξ f τa τb i ω| ≤ 2 * Er
        ∧ |dqIIK X N S a ξ f τa τb i ω| ≤ 2 * Er + 2 * popErr ξ C₁ C₂ (τb - τa))}
      ⊆ (⋃ g ∈ T, {ω | ∃ j < N, sampAvg X N (latK S (ξ / a g)) j ω < P0c S a₁ * ξ ^ n / 2})
        ∪ (⋃ pr ∈ Pairs, badLK X N S a ξ f pr.1 pr.2 Er C₁ C₂) := by
    intro ω hω
    by_contra hnot
    rw [mem_union, not_or] at hnot
    obtain ⟨hn', hr⟩ := hnot
    obtain ⟨τa, hτa, τb, hτb, hη, i, hi, hfail⟩ := hω
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

/-! ### Stage 3 (b): the window statement without free parameters (`L = 4 log N`)

The auxiliary statements `iter2_bound_of_per`, `Gtwo`, `lapG_bound`, `wStar`, `wStar_props`, `inv_min_le`,
`one_div_wStar_le`, `floor_succ_le`, `rateE_pos`, `rateE_lower`, `Dwin` are verbatim copies of those of the
forty-first file `CorrelationsToGeometryFlatNPointWindow2.lean` (namespace `CTG.FlatNPointWindow2`, no compiled
module); they do not refer to the profile. -/

/-- A periodic `C²` function has a bounded second derivative (copy). -/
theorem iter2_bound_of_per {f : E → ℝ} (hf : ContDiff ℝ 2 f) (hper : Per f) :
    ∃ M₂, 0 ≤ M₂ ∧ ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂ := by
  have hc : Continuous fun y => iteratedFDeriv ℝ 2 f y :=
    hf.continuous_iteratedFDeriv (by norm_num)
  obtain ⟨C, hC⟩ := cube_compact.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  set g := y - fr y
  have hg : g ∈ Lat (n := n) := sub_fr_mem y
  have hfun : (fun w => f (g + w)) = f := funext fun w => hper g hg w
  have e : iteratedFDeriv ℝ 2 f y = iteratedFDeriv ℝ 2 f (fr y) := by
    have := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) 2 g (fr y)
    rw [hfun] at this
    rw [this]; congr 1; simp [g]
  rw [e]
  exact (hC _ (fr_mem_cube y)).trans (le_max_left _ _)

/-- `G₂ = n ‖S‖² M₂` (copy). -/
def Gtwo (S : E ≃L[ℝ] E) (M₂ : ℝ) : ℝ := (n : ℝ) * (‖(S : E →L[ℝ] E)‖ ^ 2 * M₂)

theorem Gtwo_nonneg (S : E ≃L[ℝ] E) {M₂ : ℝ} (hM₂ : 0 ≤ M₂) : 0 ≤ Gtwo S M₂ := by
  unfold Gtwo; positivity

/-- `|lapG S f x| ≤ n ‖S‖² M₂` if `‖D²f‖ ≤ M₂` (copy). -/
theorem lapG_bound (S : E ≃L[ℝ] E) {f : E → ℝ} {M₂ : ℝ}
    (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂) (x : E) : |lapG S f x| ≤ Gtwo S M₂ := by
  have hM0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  unfold lapG Gtwo
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i : Fin n, |iteratedFDeriv ℝ 2 f x (fun _ => S (eb i))|
      ≤ ‖(S : E →L[ℝ] E)‖ ^ 2 * M₂ := by
    intro i
    have h1 := (iteratedFDeriv ℝ 2 f x).le_opNorm (fun _ => S (eb i))
    rw [← Real.norm_eq_abs]
    refine h1.trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hS : ‖S (eb i)‖ ≤ ‖(S : E →L[ℝ] E)‖ := by
      have h1 : ‖(S : E →L[ℝ] E) (eb i)‖ ≤ ‖(S : E →L[ℝ] E)‖ * ‖eb i‖ :=
        (S : E →L[ℝ] E).le_opNorm (eb i)
      have h2 : ‖eb (n := n) i‖ = 1 := by
        rw [EuclideanSpace.norm_single]; exact norm_one
      rw [h2, mul_one] at h1
      exact h1
    calc ‖iteratedFDeriv ℝ 2 f x‖ * ‖S (eb i)‖ ^ 2 ≤ M₂ * ‖(S : E →L[ℝ] E)‖ ^ 2 :=
        mul_le_mul (hM₂ x) (pow_le_pow_left₀ (norm_nonneg _) hS 2) (by positivity) hM0
      _ = ‖(S : E →L[ℝ] E)‖ ^ 2 * M₂ := by ring
  calc ∑ i, |iteratedFDeriv ℝ 2 f x (fun _ => S (eb i))|
      ≤ ∑ _i : Fin n, ‖(S : E →L[ℝ] E)‖ ^ 2 * M₂ := Finset.sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) * (‖(S : E →L[ℝ] E)‖ ^ 2 * M₂) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The grid width `w* = min{η₀/4, c/(4(BI+1)), Er η₀/(4(Ls+1))}` (copy). -/
def wStar (η₀ c BI Er Ls : ℝ) : ℝ :=
  min (η₀ / 4) (min (c / (4 * (BI + 1))) (Er * η₀ / (4 * (Ls + 1))))

theorem wStar_props {η₀ c BI Er Ls : ℝ} (hη₀ : 0 < η₀) (hc : 0 < c) (hBI : 0 ≤ BI)
    (hEr : 0 < Er) (hLs : 0 ≤ Ls) :
    0 < wStar η₀ c BI Er Ls ∧ 4 * wStar η₀ c BI Er Ls ≤ η₀
      ∧ BI * wStar η₀ c BI Er Ls ≤ c / 4 ∧ 4 * Ls * wStar η₀ c BI Er Ls ≤ Er * η₀ := by
  set w := wStar η₀ c BI Er Ls with hw
  have h1 : w ≤ η₀ / 4 := min_le_left _ _
  have h2 : w ≤ c / (4 * (BI + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : w ≤ Er * η₀ / (4 * (Ls + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hpos : 0 < w := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  refine ⟨hpos, by linarith, ?_, ?_⟩
  · have e : (BI + 1) * (c / (4 * (BI + 1))) = c / 4 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ BI + 1)]
  · have e : 4 * (Ls + 1) * (Er * η₀ / (4 * (Ls + 1))) = Er * η₀ := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 4 * (Ls + 1))]

theorem inv_min_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 1 / min x y ≤ 1 / x + 1 / y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]; have : 0 < 1 / y := by positivity
    linarith
  · rw [min_eq_right h]; have : 0 < 1 / x := by positivity
    linarith

theorem one_div_wStar_le {η₀ c BI Er Ls : ℝ} (hη₀ : 0 < η₀) (hc : 0 < c) (hBI : 0 ≤ BI)
    (hEr : 0 < Er) (hLs : 0 ≤ Ls) :
    1 / wStar η₀ c BI Er Ls ≤ 4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) / (Er * η₀) := by
  unfold wStar
  refine (inv_min_le (by positivity) (lt_min (by positivity) (by positivity))).trans ?_
  have h1 := inv_min_le (x := c / (4 * (BI + 1))) (y := Er * η₀ / (4 * (Ls + 1)))
    (by positivity) (by positivity)
  have e1 : 1 / (η₀ / 4) = 4 / η₀ := one_div_div _ _
  have e2 : 1 / (c / (4 * (BI + 1))) = 4 * (BI + 1) / c := one_div_div _ _
  have e3 : 1 / (Er * η₀ / (4 * (Ls + 1))) = 4 * (Ls + 1) / (Er * η₀) := one_div_div _ _
  rw [e2, e3] at h1
  rw [e1]
  linarith

theorem floor_succ_le {x w : ℝ} (hw : 0 < w) :
    ((⌊x / w⌋₊ : ℕ) : ℝ) + 1 ≤ 1 + max x 0 * (1 / w) := by
  have h1 : ((⌊x / w⌋₊ : ℕ) : ℝ) ≤ max x 0 / w := by
    calc ((⌊x / w⌋₊ : ℕ) : ℝ) ≤ ((⌊max x 0 / w⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast Nat.floor_mono (div_le_div_of_nonneg_right (le_max_left _ _) hw.le)
      _ ≤ max x 0 / w := Nat.floor_le (div_nonneg (le_max_right _ _) hw.le)
  have e : max x 0 / w = max x 0 * (1 / w) := by ring
  linarith

theorem rateE_pos {Λ m₂ L ξ : ℝ} {N : ℕ} (hΛ : 0 < Λ) (hm₂ : 0 < m₂) (hL : 0 < L)
    (hN : 0 < N) (hξ : 0 < ξ) : 0 < rateE n Λ m₂ L N ξ := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  unfold rateE
  have : 0 < Real.sqrt (L / (N * ξ ^ n)) := Real.sqrt_pos.2 (by positivity)
  positivity

/-- The explicit constant of the `1/N²` form (copy). -/
def Dwin (η₀ c BI Ls m₂ p q : ℝ) : ℝ :=
  1 + max (q - p) 0 * (4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) * m₂ / (7320000 * η₀))

theorem rateE_lower {Λ m₂ L ξ : ℝ} {N : ℕ} (hΛ : 1 ≤ Λ) (hm₂ : 0 < m₂) (hL : 1 ≤ L)
    (hN : 0 < N) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    1 / rateE n Λ m₂ L N ξ ≤ m₂ * Real.sqrt N / 7320000 := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < ξ ^ n := pow_pos hξ n
  have hx1 : ξ ^ n ≤ 1 := pow_le_one₀ hξ.le hξ1
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN'
  have hs1 : 1 / Real.sqrt N ≤ Real.sqrt (L / (N * ξ ^ n)) := by
    rw [← Real.sqrt_one, ← Real.sqrt_div' 1 hN'.le]
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hN' (by positivity)]
    nlinarith
  have hΛ20 : 1 ≤ Λ ^ 20 := one_le_pow₀ hΛ
  have hlow : 7320000 / (m₂ * Real.sqrt N) ≤ rateE n Λ m₂ L N ξ := by
    unfold rateE
    have hξi : 1 ≤ 1 / ξ := by rw [le_div_iff₀ hξ]; linarith
    calc 7320000 / (m₂ * Real.sqrt N) = 7320000 * 1 / m₂ * (1 / Real.sqrt N) / 1 := by
          field_simp
      _ ≤ 7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n)) / ξ := by
          rw [div_eq_mul_one_div (7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n))) ξ,
            div_one]
          have h1 : 7320000 * 1 / m₂ ≤ 7320000 * Λ ^ 20 / m₂ := by
            apply div_le_div_of_nonneg_right _ hm₂.le; linarith
          have h2 : 7320000 * 1 / m₂ * (1 / Real.sqrt N)
              ≤ 7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n)) :=
            mul_le_mul h1 hs1 (by positivity) (by positivity)
          have h3 : 0 ≤ 7320000 * Λ ^ 20 / m₂ * Real.sqrt (L / (N * ξ ^ n)) := by positivity
          nlinarith
  have hpos : 0 < 7320000 / (m₂ * Real.sqrt N) := by positivity
  calc 1 / rateE n Λ m₂ L N ξ ≤ 1 / (7320000 / (m₂ * Real.sqrt N)) :=
        one_div_le_one_div_of_le hpos hlow
    _ = m₂ * Real.sqrt N / 7320000 := by rw [one_div_div]

/-- The sum of the Lipschitz constants in the condition on the grid width (lattice kernel). -/
def LsumK (n : ℕ) (S : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (a₀ a₁ La Lip ξ M₄ M₂ : ℝ) : ℝ :=
  LsK n S a₀ a₁ La Lip ξ (P0c S a₁ * ξ ^ n / 4)
    + (ξ ^ 2 * Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S + Gtwo S M₂ * (2 * La / a₀ ^ 3))

theorem LsumK_nonneg (hn : 1 ≤ n) (S : E ≃L[ℝ] E) {a₀ a₁ La Lip ξ M₄ M₂ : ℝ} (ha₀ : 0 < a₀)
    (ha₁ : 0 < a₁) (hLa : 0 ≤ La) (hLip : 0 ≤ Lip) (hξ : 0 < ξ) (hM₄ : 0 ≤ M₄) (hM₂ : 0 ≤ M₂) :
    0 ≤ LsumK n S a₀ a₁ La Lip ξ M₄ M₂ := by
  have hk := radK_gauss (n := n)
  have hm₂ := gam₂_pos hn
  have hμ₄ : 0 ≤ gaμ₄ n := by
    rw [← hk.mom4]
    exact integral_nonneg fun z => mul_nonneg (by positivity) (hk.kern.nonneg z)
  have hK₀ := hk.kern.mass_pos
  have hd := dS_pos S
  have hc : 0 < P0c S a₁ * ξ ^ n / 4 := by unfold P0c; positivity
  have h1 := LsK_nonneg hn S ha₀ ha₁.le hLa hLip hξ hc
  have h2 : 0 ≤ Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S := by unfold Ctwo; positivity
  have h3 := Gtwo_nonneg S hM₂
  unfold LsumK; positivity

set_option maxHeartbeats 1600000 in
/-- **The lattice window statement without free grid width**, with `G₂ = n‖S‖²M₂`
(`M₂` bounds `‖D²f‖`), grid width `w* = wStar η₀ (P₀ξⁿ) (cI·G) E Ls`. -/
theorem flat_npoint_lattice_window_auto (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B M₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B) (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {L : ℝ} (hL1 : 1 ≤ L)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * L ≤ N * ξ ^ n)
    {p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    let w := wStar η₀ (P0c S a₁ * ξ ^ n) (cIk a₀ a₁ La * Gb n S a₀)
      (rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ) (LsumK n S a₀ a₁ La Lip ξ M₄ M₂)
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqIK X N S a ξ f τa τb i ω| ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ
        ∧ |dqIIK X N S a ξ f τa τb i ω|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) L N ξ
            + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
                (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (τb - τa))}
      ≤ ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) * (N * (2 * Real.exp (-L)))
        + ((⌊(q - p) / w⌋₊ : ℕ) + 1 : ℝ) ^ 2 * (15 * (N * (2 * Real.exp (-L)))) := by
  intro w
  have hN0 : 0 < N := by omega
  have hd := dS_pos S
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < P0c S a₁ * ξ ^ n := by unfold P0c; positivity
  have hM20 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hBI0 : 0 ≤ cIk a₀ a₁ La * Gb n S a₀ := by
    have := Gb_pos S a₀; unfold cIk; positivity
  have hΛ : 0 < dLam S a₀ a₁ La Lip :=
    lt_of_lt_of_le one_pos (dLam_bounds S a₀ a₁ La Lip).1
  have hEr := rateE_pos (n := n) hΛ (gam₂_pos hn) (by linarith : (0:ℝ) < L) hN0 hξ
  have hLs := LsumK_nonneg hn S ha₀ ha₁0 hLa0 hLip0 hξ hM₄ hM20 (a₁ := a₁)
  obtain ⟨hw, h4, hwc, hwE⟩ := wStar_props hη₀ hc hBI0 hEr hLs
  refine flat_npoint_lattice_window hn X h_indep hX hlaw N hN hf hM hM₄ hper hLip0 hLip hB S
    (lapG_bound S hM₂) a a' hda ha₀ ha ha₁ hLa hξ hξ1 hL1 hNL hw hη₀ h4 hwc ?_
  exact hwE

set_option maxHeartbeats 1600000 in
/-- **The lattice window statement with probability `≤ 32 D²/N²`** (`L = 4 log N`, grid width
`w*`); `D = Dwin η₀ (P₀ξⁿ) (cI·G) Ls m₂ p q` does not depend on `N`. -/
theorem flat_npoint_lattice_window_N2 (hn : 1 ≤ n) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → E) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = mT) (N : ℕ) (hN : 2 ≤ N)
    {f : E → ℝ} (hf : ContDiff ℝ 4 f) {M₄ Lip B M₂ : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 4 f y‖ ≤ M₄)
    (hM₄ : 0 ≤ M₄) (hper : Per f) (hLip0 : 0 ≤ Lip) (hLip : ∀ x y, |f y - f x| ≤ Lip * ‖y - x‖)
    (hB : ∀ y, |f y| ≤ B) (hM₂ : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M₂) (S : E ≃L[ℝ] E)
    (a a' : ℝ → ℝ) (hda : ∀ τ, HasDerivAt a (a' τ) τ) {a₀ a₁ La ξ : ℝ}
    (ha₀ : 0 < a₀) (ha : ∀ τ, a₀ ≤ a τ) (ha₁ : ∀ τ, a τ ≤ a₁) (hLa : ∀ τ, |a' τ| ≤ La)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hNL : 92416 * dLam S a₀ a₁ La Lip ^ 14 * (4 * Real.log N) ≤ N * ξ ^ n)
    {p q η₀ : ℝ} (hη₀ : 0 < η₀) :
    μ.real {ω | ∃ τa ∈ Icc p q, ∃ τb ∈ Icc p q, η₀ ≤ |τb - τa| ∧ ∃ i < N, ¬ (
        |dqIK X N S a ξ f τa τb i ω|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) (4 * Real.log N) N ξ
        ∧ |dqIIK X N S a ξ f τa τb i ω|
          ≤ 2 * rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) (4 * Real.log N) N ξ
            + 2 * popErr ξ (Cone M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ S)
                (Ctwo M₄ (gaμ₄ n) (gam₂ n) (gaK₀ n) a₀ La S) (τb - τa))}
      ≤ 32 * Dwin η₀ (P0c S a₁ * ξ ^ n) (cIk a₀ a₁ La * Gb n S a₀)
          (LsumK n S a₀ a₁ La Lip ξ M₄ M₂) (gam₂ n) p q ^ 2 / (N : ℝ) ^ 2 := by
  have hN0 : 0 < N := by omega
  have hN' : (0:ℝ) < N := by exact_mod_cast hN0
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlog2 := Real.log_two_gt_d9
  have hL1 : 1 ≤ 4 * Real.log N := by linarith
  have H := flat_npoint_lattice_window_auto hn X h_indep hX hlaw N hN hf hM hM₄ hper hLip0 hLip
    hB hM₂ S a a' hda ha₀ ha ha₁ hLa hξ hξ1 hL1 hNL (p := p) (q := q) hη₀
  simp only at H
  have hm₂ := gam₂_pos hn
  have hd := dS_pos S
  have ha₁0 : 0 < a₁ := lt_of_lt_of_le ha₀ ((ha 0).trans (ha₁ 0))
  have hc : 0 < P0c S a₁ * ξ ^ n := by unfold P0c; positivity
  have hM20 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0)
  have hLa0 : 0 ≤ La := le_trans (abs_nonneg _) (hLa 0)
  have hBI0 : 0 ≤ cIk a₀ a₁ La * Gb n S a₀ := by
    have := Gb_pos S a₀; unfold cIk; positivity
  have hΛ1 := (dLam_bounds S a₀ a₁ La Lip).1
  have hΛ : 0 < dLam S a₀ a₁ La Lip := lt_of_lt_of_le one_pos hΛ1
  set Er := rateE n (dLam S a₀ a₁ La Lip) (gam₂ n) (4 * Real.log N) N ξ with hErd
  have hEr : 0 < Er := rateE_pos hΛ hm₂ (by linarith) hN0 hξ
  set Ls := LsumK n S a₀ a₁ La Lip ξ M₄ M₂ with hLsd
  have hLs : 0 ≤ Ls := LsumK_nonneg hn S ha₀ ha₁0 hLa0 hLip0 hξ hM₄ hM20
  set c := P0c S a₁ * ξ ^ n with hcd
  set BI := cIk a₀ a₁ La * Gb n S a₀ with hBId
  set m₂ := gam₂ n with hm₂d
  set w := wStar η₀ c BI Er Ls with hwd
  have hw := (wStar_props hη₀ hc hBI0 hEr hLs).1
  set K1 : ℝ := ((⌊(q - p) / w⌋₊ : ℕ) : ℝ) + 1 with hK1
  set mx := max (q - p) 0 with hmx
  have hmx0 : 0 ≤ mx := le_max_right _ _
  set D := Dwin η₀ c BI Ls m₂ p q with hDd
  have hsN : 1 ≤ Real.sqrt N := by
    rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hK1D : K1 ≤ D * Real.sqrt N := by
    have h1 := floor_succ_le (x := q - p) hw
    have h2 := one_div_wStar_le hη₀ hc hBI0 hEr hLs
    have h3 := rateE_lower (n := n) hΛ1 hm₂ hL1 hN0 hξ hξ1 (m₂ := m₂)
    rw [← hErd] at h3
    have h4 : 4 * (Ls + 1) / (Er * η₀) ≤ 4 * (Ls + 1) * m₂ / (7320000 * η₀) * Real.sqrt N := by
      have e1 : 4 * (Ls + 1) / (Er * η₀) = 4 * (Ls + 1) / η₀ * (1 / Er) := by field_simp
      have e2 : 4 * (Ls + 1) * m₂ / (7320000 * η₀) * Real.sqrt N
          = 4 * (Ls + 1) / η₀ * (m₂ * Real.sqrt N / 7320000) := by field_simp
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have ha0 : 0 ≤ 4 / η₀ := by positivity
    have hb0 : 0 ≤ 4 * (BI + 1) / c := by positivity
    have hc0 : 0 ≤ 4 * (Ls + 1) * m₂ / (7320000 * η₀) := by positivity
    have h5 : 1 / w ≤ (4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) * m₂ / (7320000 * η₀))
        * Real.sqrt N := by
      have := h2.trans (add_le_add_right h4 _)
      nlinarith
    have h6 : mx * (1 / w) ≤ mx * ((4 / η₀ + 4 * (BI + 1) / c
        + 4 * (Ls + 1) * m₂ / (7320000 * η₀)) * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left h5 hmx0
    rw [hDd]; unfold Dwin
    have h7 : 0 ≤ mx * (4 / η₀ + 4 * (BI + 1) / c + 4 * (Ls + 1) * m₂ / (7320000 * η₀)) := by
      positivity
    rw [← hmx]
    nlinarith
  have hK10 : 1 ≤ K1 := by
    rw [hK1]; have := Nat.cast_nonneg (α := ℝ) ⌊(q - p) / w⌋₊; linarith
  have hexp : (N : ℝ) * (2 * Real.exp (-(4 * Real.log N))) = 2 / (N : ℝ) ^ 3 := by
    rw [Real.exp_neg, show (4:ℝ) * Real.log N = ((4:ℕ):ℝ) * Real.log N by norm_num,
      Real.exp_nat_mul, Real.exp_log hN']
    field_simp
  rw [hexp] at H
  refine H.trans ?_
  have hK1sq : K1 ^ 2 ≤ D ^ 2 * N := by
    have hD0 : 0 ≤ D * Real.sqrt N := le_trans (by linarith) hK1D
    calc K1 ^ 2 ≤ (D * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (by linarith) hK1D 2
      _ = D ^ 2 * N := by rw [mul_pow, Real.sq_sqrt hN'.le]
  have hX0 : 0 ≤ 2 / (N : ℝ) ^ 3 := by positivity
  calc K1 * (2 / (N : ℝ) ^ 3) + K1 ^ 2 * (15 * (2 / (N : ℝ) ^ 3))
      ≤ 16 * K1 ^ 2 * (2 / (N : ℝ) ^ 3) := by
        have hk : K1 ≤ K1 ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right hk hX0
        nlinarith
    _ ≤ 16 * (D ^ 2 * N) * (2 / (N : ℝ) ^ 3) := by gcongr
    _ = 32 * D ^ 2 / (N : ℝ) ^ 2 := by field_simp; ring

end CTG.FlatNPointLatticeWindow
