/-
Thirty-fourth file: deterministic part of "at least `2l+1` eigenvalues of the sample matrix on `S²` near `s_l`".
Imports `CorrelationsToGeometryFunkHeckeSampleEig` and `CorrelationsToGeometryFunkHeckeMult` (compiled modules
under `.tools/leanbuild`); namespace `CTG.FunkHecke.SampleMult`; check with `./check_funk_hecke_sample_mult.sh`.
`multi_near`: for a real symmetric matrix, `m` approximate eigenvectors with a frame bound `γ` give at least `m`
eigenvalues (indices of the eigenbasis) within `ε √(m/γ)`; `Pinf_multiplicity_cont` (the `2l+1` independent
eigenfunctions are continuous); `gram_lower` (their `L²(σ)` Gram form is bounded below by a positive constant);
`sample_gram_det`; `mult_det`: for ANY points `y_1..y_N`, degrees `≥ dmin`, one-step walk errors `≤ E` for `m`
functions bounded by `Fe`, and a lower bound `N g ∑c² ≤ ∑_i (∑_r c_r e_r(y_i))²` of the sampled Gram form imply
at least `m` eigenvalues of `Smat` within `N E Fe √m/(dmin g)` of `s`.
NOT formalised: the probability that these hypotheses hold for random points (Hoeffding for the sampled Gram
form, union with the degree and walk events), hence NO statement about samples; exactly `2l+1`.
This file is the state of an interrupted sub-task, accepted by Lean as it stands.
No sorry, no axiom, no native_decide.  Written by a sub-task of an AI session on 26 November 2026.
-/
import Mathlib
import CorrelationsToGeometryFunkHeckeSampleEig
import CorrelationsToGeometryFunkHeckeMult

/-!
# A144: at least `2l+1` eigenvalues of the sample matrix near `s_l` (sphere, FIXED scale)

Scratch block (namespace `CTG.FunkHecke.SampleMult`), importing Mathlib and the Lean files
`CorrelationsToGeometryFunkHeckeSampleEig` and `CorrelationsToGeometryFunkHeckeMult`.
-/

open MeasureTheory ProbabilityTheory Set Metric Real Filter Matrix
open scoped RealInnerProductSpace ENNReal NNReal

namespace CTG.FunkHecke.SampleMult

open CTG.FunkHecke CTG.FunkHecke.Sample CTG.FunkHecke.SampleEig

/-! ## (1) Deterministic: many approximate eigenvectors ⇒ many eigenvalues -/

theorem eig_coeff {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (w : n → ℝ) (lam : ℝ) (j : n) :
    ⇑(hA.eigenvectorBasis j) ⬝ᵥ (fun i => (A *ᵥ w) i - lam * w i)
      = (hA.eigenvalues j - lam) * (⇑(hA.eigenvectorBasis j) ⬝ᵥ w) := by
  have hT : Aᵀ = A := by
    have := hA.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have h1 : ⇑(hA.eigenvectorBasis j) ⬝ᵥ (A *ᵥ w)
      = hA.eigenvalues j * (⇑(hA.eigenvectorBasis j) ⬝ᵥ w) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, hA.mulVec_eigenvectorBasis, smul_dotProduct,
      smul_eq_mul]
  have h2 : (fun i => (A *ᵥ w) i - lam * w i) = A *ᵥ w - lam • w := by
    funext i; simp [Pi.sub_apply, Pi.smul_apply]
  rw [h2, dotProduct_sub, dotProduct_smul, h1, smul_eq_mul]
  ring

/-- **Many approximate eigenvectors ⇒ many eigenvalues.** For a real symmetric `A`, vectors
`u_1, …, u_m` with `∑ (A u_r - λ u_r)² ≤ ε² ∑ u_r²`, `u_r ≠ 0`, and the frame condition
`γ ∑_r c_r² ‖u_r‖² ≤ ‖∑_r c_r u_r‖²` for all `c` (`γ > 0`): at least `m` eigenvalues (counted
with multiplicity, i.e. indices of the eigenbasis) lie within `ε √(m/γ)` of `λ`. -/
theorem multi_near {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) {m : ℕ} (u : Fin m → n → ℝ) (lam ε γ : ℝ) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hu : ∀ r, 0 < ∑ i, u r i ^ 2)
    (happ : ∀ r, ∑ i, ((A *ᵥ u r) i - lam * u r i) ^ 2 ≤ ε ^ 2 * ∑ i, u r i ^ 2)
    (hframe : ∀ c : Fin m → ℝ,
      γ * ∑ r, c r ^ 2 * ∑ i, u r i ^ 2 ≤ ∑ i, (∑ r, c r * u r i) ^ 2) :
    m ≤ (Finset.univ.filter (fun j => |hA.eigenvalues j - lam| ≤ ε * √(m / γ))).card := by
  by_contra hlt
  push_neg at hlt
  set ε' := ε * √(m / γ) with hε'
  have hε'0 : 0 ≤ ε' := by positivity
  have hε'2 : ε' ^ 2 = ε ^ 2 * (m / γ) := by
    rw [hε', mul_pow, Real.sq_sqrt (by positivity)]
  set J := Finset.univ.filter (fun j => |hA.eigenvalues j - lam| ≤ ε')
  set b := hA.eigenvectorBasis
  let M : Matrix J (Fin m) ℝ := fun j r => ⇑(b j) ⬝ᵥ u r
  have hrank : Module.finrank ℝ (J → ℝ) < Module.finrank ℝ (Fin m → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, Fintype.card_coe]
    exact hlt
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := M.mulVecLin) hrank
  obtain ⟨c, hcker, hc0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hMc : ∀ j ∈ J, ∑ r, (⇑(b j) ⬝ᵥ u r) * c r = 0 := by
    intro j hj
    have h0 : (M *ᵥ c) ⟨j, hj⟩ = 0 := by
      rw [← Matrix.mulVecLin_apply, LinearMap.mem_ker.mp hcker]; rfl
    exact h0
  set v : n → ℝ := fun i => ∑ r, c r * u r i
  have hd : ∀ j, ⇑(b j) ⬝ᵥ v = ∑ r, (⇑(b j) ⬝ᵥ u r) * c r := by
    intro j
    simp only [dotProduct, v, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => by ring
  have hdJ : ∀ j ∈ J, ⇑(b j) ⬝ᵥ v = 0 := fun j hj => by rw [hd j]; exact hMc j hj
  -- v ≠ 0
  have hcr : ∃ r, c r ≠ 0 := by
    by_contra h; push_neg at h; exact hc0 (funext h)
  have hcu : 0 < ∑ r, c r ^ 2 * ∑ i, u r i ^ 2 := by
    obtain ⟨r0, hr0⟩ := hcr
    exact lt_of_lt_of_le (mul_pos (by positivity) (hu r0))
      (Finset.single_le_sum (fun r _ => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)) (Finset.mem_univ r0))
  have hv : 0 < ∑ i, v i ^ 2 := lt_of_lt_of_le (mul_pos hγ hcu) (hframe c)
  -- lower bound
  have hP1 := parseval b (fun i => (A *ᵥ v) i - lam * v i)
  have hP2 : ∑ j, (⇑(b j) ⬝ᵥ v) ^ 2 = ∑ i, v i ^ 2 := parseval b v
  have hP1' : ∑ j, ((hA.eigenvalues j - lam) * (⇑(b j) ⬝ᵥ v)) ^ 2
      = ∑ i, ((A *ᵥ v) i - lam * v i) ^ 2 := by
    rw [← hP1]
    exact Finset.sum_congr rfl fun j _ => (congrArg (fun t => t ^ 2) (eig_coeff A hA v lam j)).symm
  have hdj : ∃ j, ⇑(b j) ⬝ᵥ v ≠ 0 := by
    by_contra h; push_neg at h
    have : ∑ j, (⇑(b j) ⬝ᵥ v) ^ 2 = 0 := Finset.sum_eq_zero fun j _ => by rw [h j]; ring
    rw [hP2] at this; linarith
  obtain ⟨j0, hj0⟩ := hdj
  have hj0J : j0 ∉ J := fun h => hj0 (hdJ j0 h)
  have hlow : ε' ^ 2 * ∑ i, v i ^ 2 < ∑ i, ((A *ᵥ v) i - lam * v i) ^ 2 := by
    rw [← hP2, ← hP1', Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro j _
      by_cases hj : j ∈ J
      · have h0 : ⇑(b j) ⬝ᵥ v = 0 := hdJ j hj
        rw [h0]; simp
      · have hgt : ε' < |hA.eigenvalues j - lam| := by
          simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj; exact hj
        rw [mul_pow (hA.eigenvalues j - lam)]
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        nlinarith [abs_nonneg (hA.eigenvalues j - lam), sq_abs (hA.eigenvalues j - lam)]
    · refine ⟨j0, Finset.mem_univ _, ?_⟩
      have hgt : ε' < |hA.eigenvalues j0 - lam| := by
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj0J; exact hj0J
      rw [mul_pow (hA.eigenvalues j0 - lam)]
      apply mul_lt_mul_of_pos_right _ (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj0)))
      nlinarith [abs_nonneg (hA.eigenvalues j0 - lam), sq_abs (hA.eigenvalues j0 - lam)]
  -- upper bound
  set w : Fin m → n → ℝ := fun r i => (A *ᵥ u r) i - lam * u r i
  have hAv : ∀ i, (A *ᵥ v) i - lam * v i = ∑ r, c r * w r i := by
    intro i
    have h1 : (A *ᵥ v) i = ∑ r, c r * (A *ᵥ u r) i := by
      simp only [mulVec, dotProduct, v, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => by ring
    have h2 : lam * v i = ∑ r, c r * (lam * u r i) := by
      simp only [v, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [h1, h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by simp only [w]; ring
  have hup : ∑ i, ((A *ᵥ v) i - lam * v i) ^ 2 ≤ ε' ^ 2 * ∑ i, v i ^ 2 := by
    simp_rw [hAv]
    have hcs : ∀ i, (∑ r, c r * w r i) ^ 2 ≤ m * ∑ r, (c r * w r i) ^ 2 := by
      intro i
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1:ℝ))
        (fun r => c r * w r i)
      simpa using this
    calc ∑ i, (∑ r, c r * w r i) ^ 2 ≤ ∑ i, (m:ℝ) * ∑ r, (c r * w r i) ^ 2 :=
          Finset.sum_le_sum fun i _ => hcs i
      _ = (m:ℝ) * ∑ r, c r ^ 2 * ∑ i, w r i ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ (m:ℝ) * ∑ r, c r ^ 2 * (ε ^ 2 * ∑ i, u r i ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (happ r) (sq_nonneg _)
      _ = ε ^ 2 * (m / γ) * (γ * ∑ r, c r ^ 2 * ∑ i, u r i ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          field_simp
      _ ≤ ε ^ 2 * (m / γ) * ∑ i, v i ^ 2 :=
          mul_le_mul_of_nonneg_left (hframe c) (by positivity)
      _ = ε' ^ 2 * ∑ i, v i ^ 2 := by rw [hε'2]
  linarith

/-! ## (2) Continuous independent eigenfunctions and the population Gram matrix -/

/-- `Pinf_multiplicity` with continuity of the eigenfunctions (same proof). -/
theorem Pinf_multiplicity_cont (ξ : ℝ) (l : ℕ) :
    ∃ e : Fin (2 * l + 1) → (S2 → ℝ), LinearIndependent ℝ e ∧ (∀ i, Continuous (e i)) ∧
      ∀ i x, Pinf (gk ξ) (e i) x = sphS ξ l * e i x := by
  set u : Fin (2 * l + 1) → S2 → ℝ :=
    fun j y => (cdot Mult.eZero (Mult.qv (Mult.angle l j)) y ^ l).re with hu
  set v : Fin (2 * l + 1) → S2 → ℝ :=
    fun j y => (cdot Mult.eZero (Mult.qv (Mult.angle l j)) y ^ l).im with hv
  obtain ⟨e, he, hspan⟩ := Mult.real_extract u v (fun c hc => Mult.F_indep l c (fun y => by
    have := hc y
    rw [← this]; refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    simp only [hu, hv, Mult.F]
    rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm))
  set μ := (1/2) * ∫ t in (-1:ℝ)..1, gk ξ t * legP l t with hμ
  have hint : ∀ f : S2 → ℝ, Continuous f → ∀ x : S2,
      Integrable (fun y : S2 => gk ξ ⟪(x : E3), (y : E3)⟫ * f y) sigma := fun f hf x =>
    Sample.integrable_cont _ (((gk_continuous ξ).comp
      (continuous_const.inner continuous_subtype_val)).mul hf)
  have key : ∀ f ∈ Submodule.span ℝ (Set.range (Sum.elim u v)),
      Continuous f ∧ ∀ x, zonalOp (gk ξ) f x = μ * f x := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨s, rfl⟩ := hg
      rcases s with j | j
      · refine ⟨Complex.continuous_re.comp
          (((continuous_cdot _ _).comp continuous_subtype_val).pow l), fun x => ?_⟩
        exact zonalOp_harmonic _ (gk_continuous ξ).measurable 1 (abs_gk_le ξ) _ _
          (Mult.isotropic_family _) l x
      · refine ⟨Complex.continuous_im.comp
          (((continuous_cdot _ _).comp continuous_subtype_val).pow l), fun x => ?_⟩
        exact Mult.zonalOp_harmonic_im _ (gk_continuous ξ).measurable 1 (abs_gk_le ξ) _ _
          (Mult.isotropic_family _) l x
    | zero => exact ⟨continuous_const, fun x => by simp [zonalOp]⟩
    | add f h _ _ ihf ihh =>
      refine ⟨ihf.1.add ihh.1, fun x => ?_⟩
      have e1 := ihf.2 x
      have e2 := ihh.2 x
      unfold zonalOp at e1 e2 ⊢
      simp only [Pi.add_apply, mul_add]
      rw [integral_add (hint _ ihf.1 x) (hint _ ihh.1 x), e1, e2]
    | smul a f _ ihf =>
      refine ⟨ihf.1.const_smul a, fun x => ?_⟩
      have e1 := ihf.2 x
      unfold zonalOp at e1 ⊢
      simp only [Pi.smul_apply, smul_eq_mul]
      simp_rw [mul_left_comm _ a]
      rw [integral_const_mul, e1]
  exact ⟨e, he, fun i => (key _ (hspan i)).1,
    fun i x => Mult.Pinf_of_eigen ξ l (e i) x ((key _ (hspan i)).2 x)⟩

/-- The Gram quadratic form. -/
noncomputable def gramQ {m : ℕ} (e : Fin m → S2 → ℝ) (c : Fin m → ℝ) : ℝ :=
  ∑ r, ∑ s, c r * c s * ∫ y, e r y * e s y ∂sigma

theorem gramQ_eq {m : ℕ} (e : Fin m → S2 → ℝ) (he : ∀ r, Continuous (e r)) (c : Fin m → ℝ) :
    ∫ y, (∑ r, c r * e r y) ^ 2 ∂sigma = gramQ e c := by
  have hsq : ∀ y, (∑ r, c r * e r y) ^ 2 = ∑ r, ∑ s, c r * c s * (e r y * e s y) := by
    intro y
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
  simp_rw [hsq]
  unfold gramQ
  have hI : ∀ r s, Integrable (fun y => e r y * e s y) sigma := fun r s =>
    Sample.integrable_cont (fun y => e r y * e s y) ((he r).mul (he s))
  rw [integral_finset_sum _ (fun r _ => integrable_finset_sum _ fun s _ =>
    (hI r s).const_mul (c r * c s))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_finset_sum _ (fun s _ => (hI r s).const_mul (c r * c s))]
  exact Finset.sum_congr rfl fun s _ => integral_const_mul _ _

/-- **The population Gram matrix of continuous independent functions is uniformly positive.** -/
theorem gram_lower {m : ℕ} (e : Fin m → S2 → ℝ) (he : ∀ r, Continuous (e r))
    (hli : LinearIndependent ℝ e) :
    ∃ γ0 > 0, ∀ c : Fin m → ℝ, γ0 * ∑ r, c r ^ 2 ≤ gramQ e c := by
  have hpos : ∀ c : Fin m → ℝ, c ≠ 0 → 0 < gramQ e c := by
    intro c hc
    rw [← gramQ_eq e he]
    have hcont : Continuous (fun y => (∑ r, c r * e r y) ^ 2) :=
      (continuous_finset_sum _ fun r _ => continuous_const.mul (he r)).pow 2
    have hne : ∃ y, ∑ r, c r * e r y ≠ 0 := by
      by_contra h; push_neg at h
      have := (Fintype.linearIndependent_iff.mp hli) c (by
        funext y; simpa [Finset.sum_apply] using h y)
      exact hc (funext this)
    obtain ⟨y0, hy0⟩ := hne
    exact integral_pos_of_integrable_nonneg_nonzero (x := y0) hcont
      (Sample.integrable_cont _ hcont) (fun y => sq_nonneg _) (pow_ne_zero 2 hy0)
  have hQnn : ∀ c, 0 ≤ gramQ e c := by
    intro c; rw [← gramQ_eq e he]; exact integral_nonneg fun y => sq_nonneg _
  set K : Set (Fin m → ℝ) := {c | ∑ r, c r ^ 2 = 1}
  have hQc : Continuous (gramQ e) := by
    unfold gramQ
    exact continuous_finset_sum _ fun r _ => continuous_finset_sum _ fun s _ =>
      ((continuous_apply r).mul (continuous_apply s)).mul continuous_const
  by_cases hK : K.Nonempty
  · have hKc : IsCompact K := by
      refine Metric.isCompact_of_isClosed_isBounded
        (isClosed_eq (continuous_finset_sum _ fun r _ => (continuous_apply r).pow 2)
          continuous_const) ?_
      refine (Metric.isBounded_closedBall (x := (0 : Fin m → ℝ)) (r := 1)).subset ?_
      intro c hc
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro r
      have h1 : c r ^ 2 ≤ 1 := by
        rw [← (show ∑ r, c r ^ 2 = 1 from hc)]
        exact Finset.single_le_sum (fun s _ => sq_nonneg (c s)) (Finset.mem_univ r)
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg (c r), sq_abs (c r)]
    obtain ⟨c0, hc0K, hmin⟩ := hKc.exists_isMinOn hK hQc.continuousOn
    have hc0 : c0 ≠ 0 := by
      intro h; have := (show ∑ r, c0 r ^ 2 = 1 from hc0K); rw [h] at this; simp at this
    refine ⟨gramQ e c0, hpos c0 hc0, fun c => ?_⟩
    by_cases hc : c = 0
    · rw [hc]; simp only [Pi.zero_apply]; simp; exact hQnn 0
    · set t := √(∑ r, c r ^ 2)
      have hS : 0 < ∑ r, c r ^ 2 := by
        obtain ⟨r0, hr0⟩ : ∃ r, c r ≠ 0 := by
          by_contra h; push_neg at h; exact hc (funext h)
        exact lt_of_lt_of_le (by positivity)
          (Finset.single_le_sum (fun s _ => sq_nonneg (c s)) (Finset.mem_univ r0))
      have ht : 0 < t := Real.sqrt_pos.mpr hS
      have ht2 : t ^ 2 = ∑ r, c r ^ 2 := Real.sq_sqrt hS.le
      set c' : Fin m → ℝ := fun r => c r / t
      have hc'K : c' ∈ K := by
        show ∑ r, (c r / t) ^ 2 = 1
        simp_rw [div_pow]; rw [← Finset.sum_div, ← ht2]; field_simp
      have hQ' : gramQ e c = t ^ 2 * gramQ e c' := by
        unfold gramQ; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [c']; field_simp
      rw [hQ', ← ht2]
      rw [mul_comm (gramQ e c0)]
      exact mul_le_mul_of_nonneg_left (isMinOn_iff.mp hmin c' hc'K) (sq_nonneg _)
  · refine ⟨1, one_pos, fun c => ?_⟩
    have hz : ∑ r, c r ^ 2 = 0 := by
      by_contra hne
      apply hK
      have hS : 0 < ∑ r, c r ^ 2 := lt_of_le_of_ne
        (Finset.sum_nonneg fun r _ => sq_nonneg _) (Ne.symm hne)
      refine ⟨fun r => c r / √(∑ r, c r ^ 2), ?_⟩
      show ∑ r, (c r / √(∑ r, c r ^ 2)) ^ 2 = 1
      simp_rw [div_pow]; rw [← Finset.sum_div, Real.sq_sqrt hS.le]; field_simp
    rw [hz, mul_zero]; exact hQnn c

/-! ## (3) The sample Gram matrix -/

/-- Deterministic: entrywise closeness of the sample Gram matrix ⇒ uniform lower bound. -/
theorem sample_gram_det {m N : ℕ} (e : Fin m → S2 → ℝ) (he : ∀ r, Continuous (e r))
    {γ0 δ : ℝ} (hγ0 : ∀ c : Fin m → ℝ, γ0 * ∑ r, c r ^ 2 ≤ gramQ e c) (hδ : 0 ≤ δ)
    (z : ℕ → S2)
    (hG : ∀ r s, |∑ j ∈ Finset.range N, (e r (z j) * e s (z j) - ∫ y, e r y * e s y ∂sigma)|
      < N * δ) (c : Fin m → ℝ) :
    N * (γ0 - m * δ) * ∑ r, c r ^ 2 ≤ ∑ j ∈ Finset.range N, (∑ r, c r * e r (z j)) ^ 2 := by
  set G : Fin m → Fin m → ℝ := fun r s => ∫ y, e r y * e s y ∂sigma
  set Dev : Fin m → Fin m → ℝ := fun r s =>
    ∑ j ∈ Finset.range N, e r (z j) * e s (z j) - N * G r s
  have hDev : ∀ r s, |Dev r s| ≤ N * δ := by
    intro r s
    have := (hG r s).le
    rwa [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hexp : ∑ j ∈ Finset.range N, (∑ r, c r * e r (z j)) ^ 2
      = N * gramQ e c + ∑ r, ∑ s, c r * c s * Dev r s := by
    have h1 : ∀ j, (∑ r, c r * e r (z j)) ^ 2
        = ∑ r, ∑ s, c r * c s * (e r (z j) * e s (z j)) := by
      intro j; rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => by ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    unfold gramQ
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Dev, G]
    rw [← Finset.mul_sum]
    ring
  have hcs : (∑ r, |c r|) ^ 2 ≤ m * ∑ r, c r ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin m => (1:ℝ)) (fun r => |c r|)
    simpa [sq_abs] using this
  have hdevsum : |∑ r, ∑ s, c r * c s * Dev r s| ≤ N * δ * (∑ r, |c r|) ^ 2 := by
    calc |∑ r, ∑ s, c r * c s * Dev r s| ≤ ∑ r, ∑ s, |c r| * |c s| * (N * δ) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
          rw [abs_mul, abs_mul]
          exact mul_le_mul_of_nonneg_left (hDev r s) (by positivity)
      _ = N * δ * (∑ r, |c r|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun r _ => by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
  rw [hexp]
  have h1 := mul_le_mul_of_nonneg_left (hγ0 c) hN
  have h2 := mul_le_mul_of_nonneg_left hcs (mul_nonneg hN hδ)
  have h3 := (abs_le.mp hdevsum).1
  nlinarith

/-! ## (4) Deterministic multiplicity on the sample -/

theorem radius_eq {N m : ℕ} {E Fe dmin g : ℝ} (hE : 0 ≤ E) (hFe : 0 < Fe) (hd : 0 < dmin)
    (hg : 0 < g) (hN : 0 < N) :
    √(N * E ^ 2 / (dmin * g)) * √(m / (dmin * g / (N * Fe ^ 2)))
      ≤ N * E * Fe * √m / (dmin * g) := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) (two_ne_zero), mul_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), div_pow, mul_pow, mul_pow,
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  apply le_of_eq
  field_simp

/-- **Deterministic multiplicity.** Degrees `≥ dmin`, one-step walk errors `≤ E` for `m` functions
`e_r` with `|e_r| ≤ Fe` and a uniform lower bound `N g ∑ c² ≤ ∑_i (∑_r c_r e_r(y_i))²` ⇒ at least
`m` eigenvalues of `S_N` (with multiplicity) within `N E Fe √m / (dmin g)` of `s`. -/
theorem mult_det {N m : ℕ} (hN : 0 < N) (ξ : ℝ) (y : Fin N → S2) (e : Fin m → S2 → ℝ) (s : ℝ)
    {E Fe dmin g : ℝ} (hE : 0 ≤ E) (hFe : 0 < Fe) (hd : 0 < dmin) (hg : 0 < g)
    (hdeg : ∀ i, dmin ≤ deg ξ y i)
    (herr : ∀ r i, |(∑ j, Kx ξ (y i) (y j) * e r (y j)) / deg ξ y i - s * e r (y i)| ≤ E)
    (hbd : ∀ r z, |e r z| ≤ Fe)
    (hgram : ∀ c : Fin m → ℝ, N * g * ∑ r, c r ^ 2 ≤ ∑ i, (∑ r, c r * e r (y i)) ^ 2) :
    m ≤ (Finset.univ.filter (fun j => |(Smat_hermitian ξ y).eigenvalues j - s|
      ≤ N * E * Fe * √m / (dmin * g))).card := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  set u : Fin m → Fin N → ℝ := fun r i => √(deg ξ y i) * e r (y i)
  have hsqD : ∀ i, √(deg ξ y i) ^ 2 = deg ξ y i := fun i => Real.sq_sqrt (deg_pos ξ y i).le
  have hu2 : ∀ r, ∑ i, u r i ^ 2 = ∑ i, deg ξ y i * e r (y i) ^ 2 := fun r =>
    Finset.sum_congr rfl fun i _ => by simp only [u]; rw [mul_pow, hsqD]
  have hcomb : ∀ c : Fin m → ℝ, ∑ i, (∑ r, c r * u r i) ^ 2
      = ∑ i, deg ξ y i * (∑ r, c r * e r (y i)) ^ 2 := by
    intro c
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ r, c r * u r i = √(deg ξ y i) * ∑ r, c r * e r (y i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by simp only [u]; ring
    rw [this, mul_pow, hsqD]
  have hlowc : ∀ c : Fin m → ℝ, dmin * (N * g * ∑ r, c r ^ 2) ≤ ∑ i, (∑ r, c r * u r i) ^ 2 := by
    intro c
    rw [hcomb]
    calc dmin * (N * g * ∑ r, c r ^ 2) ≤ dmin * ∑ i, (∑ r, c r * e r (y i)) ^ 2 :=
          mul_le_mul_of_nonneg_left (hgram c) hd.le
      _ = ∑ i, dmin * (∑ r, c r * e r (y i)) ^ 2 := Finset.mul_sum _ _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hdeg i) (sq_nonneg _)
  -- single r: c = indicator
  have hur : ∀ r, dmin * (N * g) ≤ ∑ i, u r i ^ 2 := by
    intro r
    have h := hlowc (fun r' => if r' = r then 1 else 0)
    have e1 : ∑ r', (if r' = r then (1:ℝ) else 0) ^ 2 = 1 := by simp
    have e2 : ∀ i, ∑ r', (if r' = r then (1:ℝ) else 0) * u r' i = u r i := fun i => by simp
    rw [e1, mul_one] at h
    simp_rw [e2] at h
    exact h
  have hupD : ∀ r, ∑ i, u r i ^ 2 ≤ N * (N * Fe ^ 2) := by
    intro r
    rw [hu2]
    calc ∑ i, deg ξ y i * e r (y i) ^ 2 ≤ ∑ _i : Fin N, (N:ℝ) * Fe ^ 2 := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul (deg_le ξ y i) ?_ (sq_nonneg _)
            hN'.le
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd r _) 2
      _ = N * (N * Fe ^ 2) := by simp
  set ε := √(N * E ^ 2 / (dmin * g))
  set γ := dmin * g / (N * Fe ^ 2)
  have hγ : 0 < γ := by positivity
  have hmain := multi_near (Smat ξ y) (Smat_hermitian ξ y) u s ε γ (Real.sqrt_nonneg _) hγ
    (fun r => lt_of_lt_of_le (by positivity) (hur r))
    (fun r => by
      simp_rw [u, Smat_mulVec]
      have h1 : ∑ i, (√(deg ξ y i) * ((∑ j, Kx ξ (y i) (y j) * e r (y j)) / deg ξ y i
          - s * e r (y i))) ^ 2 ≤ N * (N * E ^ 2) := by
        calc _ ≤ ∑ _i : Fin N, (N:ℝ) * E ^ 2 := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [mul_pow, hsqD]
              refine mul_le_mul (deg_le ξ y i) ?_ (sq_nonneg _) hN'.le
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (herr r i) 2
          _ = N * (N * E ^ 2) := by simp
      have h2 := hur r
      have hε2 : ε ^ 2 * (dmin * (N * g)) = N * (N * E ^ 2) := by
        simp only [ε]; rw [Real.sq_sqrt (by positivity)]; field_simp
      calc _ ≤ N * (N * E ^ 2) := h1
        _ = ε ^ 2 * (dmin * (N * g)) := hε2.symm
        _ ≤ ε ^ 2 * ∑ i, u r i ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
    (fun c => by
      calc γ * ∑ r, c r ^ 2 * ∑ i, u r i ^ 2 ≤ γ * ∑ r, c r ^ 2 * (N * (N * Fe ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hγ.le
            exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hupD r) (sq_nonneg _)
        _ = dmin * (N * g * ∑ r, c r ^ 2) := by
            rw [← Finset.sum_mul]; simp only [γ]; field_simp
        _ ≤ _ := hlowc c)
  refine hmain.trans (Finset.card_le_card fun j hj => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans (radius_eq hE hFe hd hg hN)

end CTG.FunkHecke.SampleMult
