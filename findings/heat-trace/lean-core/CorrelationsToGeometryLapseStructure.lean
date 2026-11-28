/-
Eighty-fifth Lean file (after version 4). Structure statement for the response of a quadratic system to a pure
lapse perturbation, H = Σ_x N(x) ℋ(x), N = 1 + ε cos(Q·x). Only Mathlib. Written by a subagent of the author-side
session (task A199), checked here; the hand computation of the numerical task N3 is confirmed.

M k q: bilinear form of the gradient energy in momentum space, symmetric and parity invariant; W k = M k (−k) + m²,
om = √W, F k Q = M k (Q−k) + m² − om k · om (Q−k). `F_zero` (F k 0 = 0), `key_step`, `F_hasFDerivAt_zero`
(the derivative of F in Q vanishes at Q = 0), `F_quadratic` (|F k Q| ≤ C‖Q‖² near 0 for M of class C², W k > 0).
`E2` is a DEFINITION, −(1/16)∫F²/(ω_k ω_{Q−k}(ω_k+ω_{Q−k})); `E2_bound`, `E2_no_Q2` (E2(Q)/‖Q‖² → 0: no term of
order Q², for every dispersion). Node model: `structure_LA`, `structure_LB`, `FA_eq`, `FB_eq`, `FA_uniform`.

HYPOTHESES in `E2_bound`, `E2_no_Q2`: ω ≥ μ0 > 0 and an integrable majorant, |F k Q| ≤ c(k)‖Q‖² with ∫c² < ∞.
NOT shown: the perturbation formula for the second-order energy (quantum mechanics); the covariant counterpart
(√(−g)·R = N√h R_h − 2√h Δ_h N); the majorant for the node model on ℝ^D (for the realisation L-B the continuum
integral diverges, only the pointwise statement holds there); the case of a position-dependent gap.
No sorry, no axiom, no native_decide.
-/
import Mathlib

open Filter Topology Set Metric MeasureTheory

namespace CTG.LapseStructure

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `W(k) = M(k,−k) + m²` (dispersion relation ω_k² = W(k)). -/
def W (M : E → E → ℝ) (m : ℝ) (k : E) : ℝ := M k (-k) + m ^ 2

/-- `ω_k = √W(k)`. -/
noncomputable def om (M : E → E → ℝ) (m : ℝ) (k : E) : ℝ := √(W M m k)

/-- `F(k,Q) = M(k,Q−k) + m² − ω_k ω_{Q−k}`. -/
noncomputable def F (M : E → E → ℝ) (m : ℝ) (k Q : E) : ℝ :=
  M k (Q - k) + m ^ 2 - om M m k * om M m (Q - k)

variable {M : E → E → ℝ} {m : ℝ}

lemma W_neg (hsym : ∀ x y, M x y = M y x) (k : E) : W M m (-k) = W M m k := by
  simp only [W, neg_neg, hsym (-k) k]

lemma om_neg (hsym : ∀ x y, M x y = M y x) (k : E) : om M m (-k) = om M m k := by
  simp only [om, W_neg hsym]

/-- Structure theorem, part 1: `F(k,0) = 0` (needs only symmetry and `W(k) ≥ 0`). -/
theorem F_zero (hsym : ∀ x y, M x y = M y x) (k : E) (hW : 0 ≤ W M m k) :
    F M m k 0 = 0 := by
  unfold F om
  rw [zero_sub, W_neg hsym, Real.mul_self_sqrt hW]
  simp [W]

/-- Key step: with `Mu(x,y) = M x y`, symmetry and parity give `L(v,0) = −L(0,v)` for the
derivative `L` of `Mu` at `(k,−k)`.  (Equivalently ∂₂M(k,−k) = −½ DW(k).) -/
theorem key_step (hsym : ∀ x y, M x y = M y x) (hpar : ∀ x y, M (-x) (-y) = M x y)
    {k : E} {L : E × E →L[ℝ] ℝ}
    (hM : HasFDerivAt (fun p : E × E => M p.1 p.2) L (k, -k)) (v : E) :
    L (v, 0) = - L (0, v) := by
  -- line in the first slot
  have h1 : HasDerivAt (fun s : ℝ => M (k + s • v) (-k)) (L (v, 0)) 0 := by
    have hγ : HasDerivAt (fun s : ℝ => ((k, -k) : E × E) + s • ((v, 0) : E × E))
        ((1 : ℝ) • ((v, 0) : E × E)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const ((v, 0) : E × E)).const_add _
    have hM' : HasFDerivAt (fun p : E × E => M p.1 p.2) L
        (((k, -k) : E × E) + (0 : ℝ) • ((v, 0) : E × E)) := by simpa using hM
    have := hM'.comp_hasDerivAt (0 : ℝ) hγ
    simpa [Function.comp_def] using this
  -- the same function, written with the second slot
  have h2 : HasDerivAt (fun s : ℝ => M (k + s • v) (-k)) (L (0, -v)) 0 := by
    have hγ : HasDerivAt (fun s : ℝ => ((k, -k) : E × E) + s • ((0, -v) : E × E))
        ((1 : ℝ) • ((0, -v) : E × E)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).smul_const ((0, -v) : E × E)).const_add _
    have hM' : HasFDerivAt (fun p : E × E => M p.1 p.2) L
        (((k, -k) : E × E) + (0 : ℝ) • ((0, -v) : E × E)) := by simpa using hM
    have h := hM'.comp_hasDerivAt (0 : ℝ) hγ
    have hfun : (fun s : ℝ => M (k + s • v) (-k)) =
        (fun p : E × E => M p.1 p.2) ∘ (fun s : ℝ => ((k, -k) : E × E) + s • ((0, -v) : E × E)) := by
      funext s
      simp only [Function.comp_def, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_zero, add_zero,
        smul_neg]
      rw [hsym, ← hpar]
      congr 1 <;> abel
    rw [hfun]
    simpa using h
  have := h1.unique h2
  rw [this]
  have : ((0 : E), -v) = -((0 : E), v) := by simp
  rw [this, map_neg]

/-- Structure theorem, part 2: the Q-derivative of `F(k,·)` at `Q = 0` vanishes. -/
theorem F_hasFDerivAt_zero (hsym : ∀ x y, M x y = M y x) (hpar : ∀ x y, M (-x) (-y) = M x y)
    {k : E} {L : E × E →L[ℝ] ℝ}
    (hM : HasFDerivAt (fun p : E × E => M p.1 p.2) L (k, -k)) (hW : 0 < W M m k) :
    HasFDerivAt (F M m k) (0 : E →L[ℝ] ℝ) 0 := by
  set Mu : E × E → ℝ := fun p => M p.1 p.2 with hMu
  let ℓ1 : E →L[ℝ] E × E := ContinuousLinearMap.inr ℝ E E
  let ℓ2 : E →L[ℝ] E × E := (-ContinuousLinearMap.id ℝ E).prod (ContinuousLinearMap.id ℝ E)
  have hfun : F M m k = fun Q => Mu ((k, -k) + ℓ1 Q) + m ^ 2
      - om M m k * √(Mu ((k, -k) + ℓ2 Q) + m ^ 2) := by
    funext Q
    simp only [F, hMu, ℓ1, ℓ2, ContinuousLinearMap.inr_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.mk_add_mk, add_zero]
    have e2 : om M m (Q - k) = √(M (k + -Q) (Q - k) + m ^ 2) := by
      rw [show Q - k = -(k + -Q) by abel, om_neg hsym, om, W]
    rw [e2, show -k + Q = Q - k by abel]
  have hA : HasFDerivAt (fun Q => Mu ((k, -k) + ℓ1 Q)) (L.comp ℓ1) 0 := by
    have hM' : HasFDerivAt Mu L ((k, -k) + ℓ1 0) := by simpa using hM
    exact hM'.comp (0 : E) (ℓ1.hasFDerivAt.const_add _)
  have hB : HasFDerivAt (fun Q => Mu ((k, -k) + ℓ2 Q)) (L.comp ℓ2) 0 := by
    have hM' : HasFDerivAt Mu L ((k, -k) + ℓ2 0) := by simpa using hM
    exact hM'.comp (0 : E) (ℓ2.hasFDerivAt.const_add _)
  have hval : Mu ((k, -k) + ℓ2 0) + m ^ 2 = W M m k := by simp [hMu, ℓ2, W]
  have hB' := (hB.add_const (m ^ 2)).sqrt (by rw [hval]; exact hW.ne')
  have hall := (hA.add_const (m ^ 2)).sub (hB'.const_mul (om M m k))
  rw [hfun]
  refine hall.congr_fderiv ?_
  ext v
  have hk := key_step hsym hpar hM v
  have hsq : om M m k = √(W M m k) := rfl
  have hpos : 0 < √(W M m k) := Real.sqrt_pos.mpr hW
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.zero_apply]
  rw [hval, hsq]
  have h2 : ℓ2 v = (-v, 0) + ((0 : E), v) := by simp [ℓ2]
  have h3 : (-v, (0 : E)) = -(v, 0) := by simp
  rw [h2, map_add, h3, map_neg, hk]
  simp only [ℓ1, ContinuousLinearMap.inr_apply]
  field_simp
  ring

/-- Consequence: `F(k,Q) = o(‖Q‖)`. -/
theorem F_isLittleO (hsym : ∀ x y, M x y = M y x) (hpar : ∀ x y, M (-x) (-y) = M x y)
    {k : E} {L : E × E →L[ℝ] ℝ}
    (hM : HasFDerivAt (fun p : E × E => M p.1 p.2) L (k, -k)) (hW : 0 < W M m k) :
    (F M m k) =o[𝓝 0] (fun Q => Q) := by
  have h := (F_hasFDerivAt_zero hsym hpar hM hW).isLittleO
  have h0 := F_zero (m := m) hsym k hW.le
  simpa [h0] using h

/-- Abstract quadratic bound: `g(0) = 0`, `Dg(0) = 0`, `Dg` K-Lipschitz on `ball 0 r`
⇒ `|g Q| ≤ K ‖Q‖²` on `ball 0 r`. -/
theorem quad_bound {g : E → ℝ} {r : ℝ} {K : NNReal}
    (hd : ∀ x ∈ ball (0 : E) r, DifferentiableAt ℝ g x)
    (hL : LipschitzOnWith K (fderiv ℝ g) (ball (0 : E) r))
    (h0 : g 0 = 0) (hd0 : fderiv ℝ g 0 = 0) :
    ∀ Q : E, ‖Q‖ < r → |g Q| ≤ K * ‖Q‖ ^ 2 := by
  intro Q hQ
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) hQ
  have hsub : closedBall (0 : E) ‖Q‖ ⊆ ball 0 r := closedBall_subset_ball hQ
  have hbound : ∀ x ∈ closedBall (0 : E) ‖Q‖, ‖fderiv ℝ g x‖ ≤ K * ‖Q‖ := by
    intro x hx
    have h0b : (0 : E) ∈ ball (0 : E) r := mem_ball_self hr
    have := hL.norm_sub_le (hsub hx) h0b
    rw [hd0, sub_zero, sub_zero] at this
    have hx' : ‖x‖ ≤ ‖Q‖ := by simpa using hx
    calc ‖fderiv ℝ g x‖ ≤ K * ‖x‖ := this
      _ ≤ K * ‖Q‖ := mul_le_mul_of_nonneg_left hx' K.2
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x hx => hd x (hsub hx)) hbound
    (convex_closedBall 0 ‖Q‖) (mem_closedBall_self (norm_nonneg Q))
    (by simp : Q ∈ closedBall (0 : E) ‖Q‖)
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at this
  calc |g Q| ≤ K * ‖Q‖ * ‖Q‖ := this
    _ = K * ‖Q‖ ^ 2 := by ring

/-- `F(k,·)` is C² at `0` when `M` is C² and `W(k) > 0`. -/
theorem F_contDiffAt (hsym : ∀ x y, M x y = M y x) {k : E}
    (hM : ContDiff ℝ 2 (fun p : E × E => M p.1 p.2)) (hW : 0 < W M m k) :
    ContDiffAt ℝ 2 (F M m k) 0 := by
  have hW' : ContDiff ℝ 2 (W M m) := by
    have : W M m = fun x => (fun p : E × E => M p.1 p.2) (x, -x) + m ^ 2 := rfl
    rw [this]
    exact (hM.comp (contDiff_id.prodMk contDiff_neg)).add contDiff_const
  have h1 : ContDiff ℝ 2 (fun Q : E => M k (Q - k)) :=
    hM.comp (contDiff_const.prodMk (contDiff_id.sub contDiff_const))
  have h2 : ContDiffAt ℝ 2 (fun Q : E => om M m (Q - k)) 0 := by
    have hne : W M m (0 - k) ≠ 0 := by rw [zero_sub, W_neg hsym]; exact hW.ne'
    exact ((hW'.comp (contDiff_id.sub contDiff_const)).contDiffAt).sqrt hne
  exact ((h1.add contDiff_const).contDiffAt).sub (contDiffAt_const.mul h2)

/-- Structure theorem, part 3 (local quadratic bound): for `M` C², symmetric, parity-invariant
and `W(k) > 0` there are `C, r > 0` with `|F(k,Q)| ≤ C ‖Q‖²` for `‖Q‖ < r`. -/
theorem F_quadratic (hsym : ∀ x y, M x y = M y x) (hpar : ∀ x y, M (-x) (-y) = M x y)
    {k : E} (hM : ContDiff ℝ 2 (fun p : E × E => M p.1 p.2)) (hW : 0 < W M m k) :
    ∃ C r : ℝ, 0 < r ∧ ∀ Q : E, ‖Q‖ < r → |F M m k Q| ≤ C * ‖Q‖ ^ 2 := by
  have hc := F_contDiffAt hsym hM hW
  have hD : HasFDerivAt (fun p : E × E => M p.1 p.2)
      (fderiv ℝ (fun p : E × E => M p.1 p.2) (k, -k)) (k, -k) :=
    ((hM.differentiable (by norm_num)) _).hasFDerivAt
  have hF0 := F_hasFDerivAt_zero hsym hpar hD hW
  have hc1 : ContDiffAt ℝ 1 (fderiv ℝ (F M m k)) 0 := hc.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hLip⟩ := hc1.exists_lipschitzOnWith
  have hev : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 2 (F M m k) y := hc.eventually (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem ht hev)
  refine ⟨K, r, hr, quad_bound (fun x hx =>
    (show ContDiffAt ℝ 2 (F M m k) x from (hball hx).2).differentiableAt (by simp))
    (hLip.mono (fun x hx => (hball hx).1)) (F_zero hsym k hW.le) hF0.fderiv⟩

/-- Same, as an `IsBigO` statement: `F(k,Q) = O(‖Q‖²)`. -/
theorem F_isBigO (hsym : ∀ x y, M x y = M y x) (hpar : ∀ x y, M (-x) (-y) = M x y)
    {k : E} (hM : ContDiff ℝ 2 (fun p : E × E => M p.1 p.2)) (hW : 0 < W M m k) :
    (F M m k) =O[𝓝 0] (fun Q => ‖Q‖ ^ 2) := by
  obtain ⟨C, r, hr, h⟩ := F_quadratic hsym hpar hM hW
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [ball_mem_nhds (0 : E) hr] with Q hQ
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Q‖)] using h Q (by simpa using hQ)

/-- Uniform version: if for every `k` the map `F(k,·)` is differentiable on `ball 0 r` with
K-Lipschitz derivative (HYPOTHESIS, `K` independent of `k`), then `|F(k,Q)| ≤ K‖Q‖²` for all `k`. -/
theorem F_quadratic_uniform (hsym : ∀ x y, M x y = M y x) (hpar : ∀ x y, M (-x) (-y) = M x y)
    {r : ℝ} {K : NNReal}
    (hMd : ∀ k, DifferentiableAt ℝ (fun p : E × E => M p.1 p.2) (k, -k))
    (hW : ∀ k, 0 < W M m k)
    (hd : ∀ k, ∀ x ∈ ball (0 : E) r, DifferentiableAt ℝ (F M m k) x)
    (hL : ∀ k, LipschitzOnWith K (fderiv ℝ (F M m k)) (ball (0 : E) r)) :
    ∀ k Q, ‖Q‖ < r → |F M m k Q| ≤ K * ‖Q‖ ^ 2 := fun k =>
  quad_bound (hd k) (hL k) (F_zero hsym k (hW k).le)
    (F_hasFDerivAt_zero hsym hpar (hMd k).hasFDerivAt (hW k)).fderiv

/-! ### The second-order energy -/

/-- `E₂(Q)/(ε² Vol)` as a DEFINITION (the perturbative derivation is not formalised). -/
noncomputable def E2 [MeasurableSpace E] (μ : Measure E) (M : E → E → ℝ) (m : ℝ) (Q : E) : ℝ :=
  -(1 / 16) * ∫ k, F M m k Q ^ 2 /
    (om M m k * om M m (Q - k) * (om M m k + om M m (Q - k))) ∂μ

lemma integrand_bound {f a b c μ0 : ℝ} (hμ0 : 0 < μ0) (ha : μ0 ≤ a) (hb : μ0 ≤ b)
    (hf : |f| ≤ c) : f ^ 2 / (a * b * (a + b)) ≤ c ^ 2 / (2 * μ0 ^ 3) := by
  have ha0 : 0 < a := lt_of_lt_of_le hμ0 ha
  have hb0 : 0 < b := lt_of_lt_of_le hμ0 hb
  have hden : 2 * μ0 ^ 3 ≤ a * b * (a + b) := by
    have h1 : μ0 * μ0 ≤ a * b := mul_le_mul ha hb hμ0.le ha0.le
    have h2 : 2 * μ0 ≤ a + b := by linarith
    nlinarith [mul_le_mul h1 h2 (by positivity) (by positivity)]
  have hf2 : f ^ 2 ≤ c ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le hf) (le_of_abs_le hf); simpa using this
  calc f ^ 2 / (a * b * (a + b)) ≤ c ^ 2 / (a * b * (a + b)) :=
        div_le_div_of_nonneg_right hf2 (by positivity)
    _ ≤ c ^ 2 / (2 * μ0 ^ 3) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden

/-- Quartic bound for `E₂`.  HYPOTHESES: `ω ≥ μ0 > 0` everywhere, `|F(k,Q)| ≤ c(k)‖Q‖²`
at this `Q`, and `c²` integrable (integrable majorant). -/
theorem E2_bound [MeasurableSpace E] {μ : Measure E} {μ0 : ℝ} (hμ0 : 0 < μ0)
    (hom : ∀ k, μ0 ≤ om M m k) {c : E → ℝ} (hc : Integrable (fun k => c k ^ 2) μ) {Q : E}
    (hF : ∀ k, |F M m k Q| ≤ c k * ‖Q‖ ^ 2) :
    |E2 μ M m Q| ≤ ‖Q‖ ^ 4 / (32 * μ0 ^ 3) * ∫ k, c k ^ 2 ∂μ := by
  have hpt : ∀ k, ‖F M m k Q ^ 2 / (om M m k * om M m (Q - k) * (om M m k + om M m (Q - k)))‖
      ≤ ‖Q‖ ^ 4 / (2 * μ0 ^ 3) * c k ^ 2 := by
    intro k
    have hnn : 0 ≤ F M m k Q ^ 2 / (om M m k * om M m (Q - k) * (om M m k + om M m (Q - k))) := by
      have := lt_of_lt_of_le hμ0 (hom k)
      have := lt_of_lt_of_le hμ0 (hom (Q - k))
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have := integrand_bound hμ0 (hom k) (hom (Q - k)) (hF k)
    calc _ ≤ (c k * ‖Q‖ ^ 2) ^ 2 / (2 * μ0 ^ 3) := this
      _ = ‖Q‖ ^ 4 / (2 * μ0 ^ 3) * c k ^ 2 := by ring
  have hint := norm_integral_le_of_norm_le (hc.const_mul (‖Q‖ ^ 4 / (2 * μ0 ^ 3)))
    (Eventually.of_forall hpt)
  rw [integral_const_mul] at hint
  unfold E2
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 16)]
  rw [Real.norm_eq_abs] at hint
  calc 1 / 16 * |∫ k, _ ∂μ| ≤ 1 / 16 * (‖Q‖ ^ 4 / (2 * μ0 ^ 3) * ∫ k, c k ^ 2 ∂μ) := by
        gcongr
    _ = _ := by ring

/-- No `Q²` term: under the HYPOTHESES of `E2_bound` for all `‖Q‖ < r`,
`E₂(Q)/‖Q‖² → 0` as `Q → 0`. -/
theorem E2_no_Q2 [MeasurableSpace E] {μ : Measure E} {μ0 r : ℝ} (hμ0 : 0 < μ0) (hr : 0 < r)
    (hom : ∀ k, μ0 ≤ om M m k) {c : E → ℝ} (hc : Integrable (fun k => c k ^ 2) μ)
    (hF : ∀ Q : E, ‖Q‖ < r → ∀ k, |F M m k Q| ≤ c k * ‖Q‖ ^ 2) :
    Tendsto (fun Q => E2 μ M m Q / ‖Q‖ ^ 2) (𝓝 0) (𝓝 0) := by
  set A := (∫ k, c k ^ 2 ∂μ) / (32 * μ0 ^ 3)
  have hA : 0 ≤ A := div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)
  have hlim : Tendsto (fun Q : E => A * ‖Q‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have : Tendsto (fun Q : E => ‖Q‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : E))
    simpa using (this.pow 2).const_mul A
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [ball_mem_nhds (0 : E) hr] with Q hQ
  have hQ' : ‖Q‖ < r := by simpa using hQ
  have hb := E2_bound hμ0 hom hc (hF Q hQ')
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖Q‖ ^ 2)]
  rcases eq_or_lt_of_le (sq_nonneg ‖Q‖) with h | h
  · rw [← h, div_zero]; positivity
  · rw [div_le_iff₀ h]
    calc |E2 μ M m Q| ≤ ‖Q‖ ^ 4 / (32 * μ0 ^ 3) * ∫ k, c k ^ 2 ∂μ := hb
      _ = A * ‖Q‖ ^ 2 * ‖Q‖ ^ 2 := by simp only [A]; ring

end General

/-! ### Instances: the kernel graph, realisations (L-A) and (L-B) -/

section Instance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Gaussian symbol `g(k) = exp(−ξ²‖k‖²/2)`. -/
noncomputable def gK (ξ : ℝ) (k : E) : ℝ := Real.exp (-(ξ ^ 2 * ‖k‖ ^ 2) / 2)

/-- `λ(k) = (2/ξ²)(1 − g(k))`. -/
noncomputable def lam (ξ : ℝ) (k : E) : ℝ := 2 / ξ ^ 2 * (1 - gK ξ k)

/-- (L-A): `h_A = π²/2 + φ(Lφ)/2 + m²φ²/2`, `M_A(k,q) = (λ(k)+λ(q))/2`. -/
noncomputable def MA (ξ : ℝ) (k q : E) : ℝ := (lam ξ k + lam ξ q) / 2

/-- (L-B): edge energy split between the endpoints,
`M_B(k,q) = (1 + g(k+q) − g(k) − g(q))/ξ²` (derived by hand, see a199/plan.md). -/
noncomputable def MB (ξ : ℝ) (k q : E) : ℝ := (1 + gK ξ (k + q) - gK ξ k - gK ξ q) / ξ ^ 2

lemma gK_neg (ξ : ℝ) (k : E) : gK ξ (-k) = gK ξ k := by simp [gK]
lemma gK_zero (ξ : ℝ) : gK ξ (0 : E) = 1 := by simp [gK]
lemma gK_le_one (ξ : ℝ) (k : E) : gK ξ k ≤ 1 := by
  unfold gK; rw [Real.exp_le_one_iff]
  have : 0 ≤ ξ ^ 2 * ‖k‖ ^ 2 := by positivity
  linarith
lemma lam_nonneg (ξ : ℝ) (k : E) : 0 ≤ lam ξ k := by
  unfold lam; have := gK_le_one ξ k
  exact mul_nonneg (by positivity) (by linarith)

lemma MA_symm (ξ : ℝ) (x y : E) : MA ξ x y = MA ξ y x := by unfold MA; ring
lemma MA_par (ξ : ℝ) (x y : E) : MA ξ (-x) (-y) = MA ξ x y := by simp [MA, lam, gK_neg]
lemma MB_symm (ξ : ℝ) (x y : E) : MB ξ x y = MB ξ y x := by
  unfold MB; rw [add_comm x y]; ring
lemma MB_par (ξ : ℝ) (x y : E) : MB ξ (-x) (-y) = MB ξ x y := by
  unfold MB; rw [← neg_add, gK_neg, gK_neg, gK_neg]

lemma W_MA (ξ m : ℝ) (k : E) : W (MA ξ) m k = lam ξ k + m ^ 2 := by
  simp [W, MA, lam, gK_neg]
lemma W_MB (ξ m : ℝ) (hξ : ξ ≠ 0) (k : E) : W (MB ξ) m k = lam ξ k + m ^ 2 := by
  simp only [W, MB, lam, add_neg_cancel, gK_zero, gK_neg]
  field_simp; ring

/-- Dispersion ω² = (2/ξ²)(1 − e^{−ξ²‖k‖²/2}) + m² > 0 for `m ≠ 0`. -/
lemma W_pos (ξ m : ℝ) (hm : m ≠ 0) (k : E) : 0 < lam ξ k + m ^ 2 := by
  have := lam_nonneg ξ k; have : 0 < m ^ 2 := by positivity
  linarith

lemma gK_contDiff (ξ : ℝ) : ContDiff ℝ ⊤ (gK (E := E) ξ) := by
  unfold gK
  exact Real.contDiff_exp.comp (((contDiff_const.mul (contDiff_norm_sq ℝ)).neg).div_const _)

lemma MA_contDiff (ξ : ℝ) : ContDiff ℝ 2 (fun p : E × E => MA ξ p.1 p.2) := by
  unfold MA lam
  have hg : ContDiff ℝ 2 (gK (E := E) ξ) := (gK_contDiff ξ).of_le le_top
  exact (((contDiff_const.mul (contDiff_const.sub (hg.comp contDiff_fst))).add
    (contDiff_const.mul (contDiff_const.sub (hg.comp contDiff_snd)))).div_const _)

lemma MB_contDiff (ξ : ℝ) : ContDiff ℝ 2 (fun p : E × E => MB ξ p.1 p.2) := by
  unfold MB
  have hg : ContDiff ℝ 2 (gK (E := E) ξ) := (gK_contDiff ξ).of_le le_top
  exact ((((contDiff_const.add (hg.comp (contDiff_fst.add contDiff_snd))).sub
    (hg.comp contDiff_fst)).sub (hg.comp contDiff_snd)).div_const _)

/-- (L-A): `F_A(k,Q) = (ω_k − ω_{Q−k})²/2`. -/
theorem FA_eq (ξ m : ℝ) (k Q : E) :
    F (MA ξ) m k Q = (om (MA ξ) m k - om (MA ξ) m (Q - k)) ^ 2 / 2 := by
  have h1 : ∀ x : E, om (MA ξ) m x ^ 2 = lam ξ x + m ^ 2 := by
    intro x; rw [om, W_MA, Real.sq_sqrt (add_nonneg (lam_nonneg ξ x) (sq_nonneg m))]
  have := h1 k; have := h1 (Q - k)
  unfold F
  rw [show MA ξ k (Q - k) = (lam ξ k + lam ξ (Q - k)) / 2 from rfl]
  nlinarith

/-- (L-B): `F_B = F_A + (e^{−ξ²‖Q‖²/2} − 1)/ξ²` (the report's formula). -/
theorem FB_eq (ξ m : ℝ) (hξ : ξ ≠ 0) (k Q : E) :
    F (MB ξ) m k Q = F (MA ξ) m k Q + (gK ξ Q - 1) / ξ ^ 2 := by
  have hom : ∀ x : E, om (MB ξ) m x = om (MA ξ) m x := by
    intro x; simp only [om, W_MB ξ m hξ, W_MA]
  unfold F; rw [hom, hom]
  simp only [MB, MA, lam, add_sub_cancel]
  field_simp; ring

/-- The extra term of (L-B) is itself O(Q²): `|(g(Q) − 1)/ξ²| ≤ ‖Q‖²/2`. -/
lemma FB_extra_bound (ξ : ℝ) (hξ : ξ ≠ 0) (Q : E) : |(gK ξ Q - 1) / ξ ^ 2| ≤ ‖Q‖ ^ 2 / 2 := by
  have hξ2 : 0 < ξ ^ 2 := by positivity
  have h1 := gK_le_one ξ Q
  have h2 : 1 - ξ ^ 2 * ‖Q‖ ^ 2 / 2 ≤ gK ξ Q := by
    unfold gK; have := Real.add_one_le_exp (-(ξ ^ 2 * ‖Q‖ ^ 2) / 2); linarith
  rw [abs_div, abs_of_pos hξ2, abs_of_nonpos (by linarith), div_le_iff₀ hξ2]
  nlinarith

/-- Structure theorem for (L-A): `F_A(k,0) = 0`, `D_Q F_A(k,0) = 0`, `F_A = O(‖Q‖²)`. -/
theorem structure_LA (ξ m : ℝ) (hm : m ≠ 0) (k : E) :
    F (MA ξ) m k 0 = 0 ∧ HasFDerivAt (F (MA ξ) m k) (0 : E →L[ℝ] ℝ) 0 ∧
    (F (MA ξ) m k) =O[𝓝 0] (fun Q => ‖Q‖ ^ 2) := by
  have hW : 0 < W (MA ξ) m k := by rw [W_MA]; exact W_pos ξ m hm k
  have hD : HasFDerivAt (fun p : E × E => MA ξ p.1 p.2)
      (fderiv ℝ (fun p : E × E => MA ξ p.1 p.2) (k, -k)) (k, -k) :=
    (((MA_contDiff ξ).differentiable (by norm_num)) _).hasFDerivAt
  exact ⟨F_zero (MA_symm ξ) k hW.le, F_hasFDerivAt_zero (MA_symm ξ) (MA_par ξ) hD hW,
    F_isBigO (MA_symm ξ) (MA_par ξ) (MA_contDiff ξ) hW⟩

/-- Structure theorem for (L-B): the general theorem applies directly, since `M_B` itself is
symmetric, parity-invariant, C² and has the same dispersion. -/
theorem structure_LB (ξ m : ℝ) (hξ : ξ ≠ 0) (hm : m ≠ 0) (k : E) :
    F (MB ξ) m k 0 = 0 ∧ HasFDerivAt (F (MB ξ) m k) (0 : E →L[ℝ] ℝ) 0 ∧
    (F (MB ξ) m k) =O[𝓝 0] (fun Q => ‖Q‖ ^ 2) := by
  have hW : 0 < W (MB ξ) m k := by rw [W_MB ξ m hξ]; exact W_pos ξ m hm k
  have hD : HasFDerivAt (fun p : E × E => MB ξ p.1 p.2)
      (fderiv ℝ (fun p : E × E => MB ξ p.1 p.2) (k, -k)) (k, -k) :=
    (((MB_contDiff ξ).differentiable (by norm_num)) _).hasFDerivAt
  exact ⟨F_zero (MB_symm ξ) k hW.le, F_hasFDerivAt_zero (MB_symm ξ) (MB_par ξ) hD hW,
    F_isBigO (MB_symm ξ) (MB_par ξ) (MB_contDiff ξ) hW⟩

/-- (L-A) with a Lipschitz frequency (HYPOTHESIS `hlip`): `|F_A(k,Q)| ≤ ℓ²‖Q‖²/2` for all `k,Q`. -/
theorem FA_uniform (ξ m : ℝ) {ℓ : ℝ}
    (hlip : ∀ x y : E, |om (MA ξ) m x - om (MA ξ) m y| ≤ ℓ * ‖x - y‖) (k Q : E) :
    |F (MA ξ) m k Q| ≤ ℓ ^ 2 * ‖Q‖ ^ 2 / 2 := by
  rw [FA_eq]
  have hsym := om_neg (m := m) (MA_symm ξ) (k - Q)
  have h := hlip k (k - Q)
  rw [show Q - k = -(k - Q) by abel, hsym]
  have hk : ‖k - (k - Q)‖ = ‖Q‖ := by rw [sub_sub_cancel]
  rw [hk] at h
  have hsq : (om (MA ξ) m k - om (MA ξ) m (k - Q)) ^ 2 ≤ (ℓ * ‖Q‖) ^ 2 := by
    have := sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h); simpa using this
  rw [abs_of_nonneg (by positivity)]
  nlinarith

end Instance

end CTG.LapseStructure

