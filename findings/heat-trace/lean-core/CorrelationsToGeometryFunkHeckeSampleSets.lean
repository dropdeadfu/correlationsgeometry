/-
Seventy-fourth file (A187, written by a subagent of the author-side session, checked by that session; read by nobody
else). Measurability of the exceptional sets of four sample theorems on `S²`, the set expressions token-identical with
those of the target theorems: `LB_sample_set_measurable`, `walk_one_step_set_measurable`,
`sample_eigenvalue_set_measurable`, `sample_mult_gen_set_measurable`. Assumptions: the sample points are measurable
(plus the smoothness of f for the first two). Imports Mathlib, the second file (`eigTot`) and the compiled modules
`…FunkHeckeLBSample`, `…FunkHeckeSampleEig`, `…FunkHeckeSampleMultProb`. Check with `./check_funk_hecke_sample_sets.sh`.
NOT shown: the sets of the almost-sure versions (`LB_sample_ae`, `LB_sample_joint`, …), of `…FunkHeckePowers`,
`…FunkHeckeSampleMult(AE)`, and of the intermediate events. No sorry, no axiom, no native_decide.
-/
import Mathlib
import CorrelationsToGeometryReal
import CorrelationsToGeometryFunkHeckeLBSample
import CorrelationsToGeometryFunkHeckeSampleEig
import CorrelationsToGeometryFunkHeckeSampleMultProb

open MeasureTheory Set Real
open scoped RealInnerProductSpace

namespace CTG.FunkHecke.A187

open CTG.FunkHecke CTG.FunkHecke.Sample CTG.FunkHecke.SampleEig
open CTG.FunkHecke.LBSample (LN)
open CTG.FunkHecke.SphereLaplace (sphLapS)
open CTG.FunkHecke.SphereLinComb (SphC2)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Measurable building blocks -/

theorem Kx_comp_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j)) (ξ : ℝ) (i j : ℕ) :
    Measurable (fun ω => Kx ξ (X i ω) (X j ω)) := by
  have hi : Measurable (fun ω => ((X i ω : S2) : E3)) := measurable_subtype_coe.comp (hX i)
  have hj : Measurable (fun ω => ((X j ω : S2) : E3)) := measurable_subtype_coe.comp (hX j)
  unfold Kx
  exact (gk_continuous ξ).measurable.comp (hi.inner hj)

theorem walk_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j)) (ξ : ℝ) {f : S2 → ℝ}
    (hf : Continuous f) (N i : ℕ) : Measurable (fun ω => walk ξ f X N ω i) := by
  unfold walk
  exact (Finset.measurable_sum _ fun j _ =>
      (Kx_comp_measurable X hX ξ i j).mul (hf.measurable.comp (hX j))).div
    (Finset.measurable_sum _ fun j _ => Kx_comp_measurable X hX ξ i j)

/-- `P_∞ f` is measurable (indeed continuous numerator and denominator) for continuous `f`. -/
theorem Pinf_measurable (ξ : ℝ) {f : S2 → ℝ} (hf : Continuous f) :
    Measurable (Pinf (gk ξ) f) := by
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hint : ∀ g : S2 → ℝ, Continuous g → (∀ z, |g z| ≤ max B 1) →
      Continuous (fun x => ∫ z, Kx ξ x z * g z ∂sigma) := by
    intro g hg hgB
    refine param_continuous (fun x z => Kx ξ x z * g z)
      ((Kx_continuous ξ).mul (hg.comp continuous_snd)) (B := max B 1) (fun x z => ?_)
    rw [abs_mul, abs_of_pos (Kx_pos ξ x z)]
    calc Kx ξ x z * |g z| ≤ 1 * |g z| :=
          mul_le_mul_of_nonneg_right (Kx_le_one ξ x z) (abs_nonneg _)
      _ ≤ max B 1 := by rw [one_mul]; exact hgB z
  have h1 := hint f hf (fun z => by
    have := hB z (mem_univ z); rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _))
  have h2 := hint (fun _ => (1:ℝ)) continuous_const (fun z => by
    simp only [abs_one]; exact le_max_right _ _)
  have e : Pinf (gk ξ) f = fun x =>
      (∫ z, Kx ξ x z * f z ∂sigma) / ∫ z, Kx ξ x z * (fun _ => (1:ℝ)) z ∂sigma := by
    funext x; unfold Pinf; rw [zonal_eq, zonal_eq]
  rw [e]
  exact h1.measurable.div h2.measurable

theorem exists_lt_range_measurable (N : ℕ) (P : ℕ → Ω → Prop)
    (hP : ∀ i, MeasurableSet {ω | P i ω}) : MeasurableSet {ω | ∃ i < N, P i ω} := by
  have e : {ω | ∃ i < N, P i ω} = ⋃ i ∈ Finset.range N, {ω | P i ω} := by
    ext ω; simp
  rw [e]
  exact Finset.measurableSet_biUnion _ fun i _ => hP i

/-! ## (1) `LB_sample` -/

theorem LN_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j)) (ξ : ℝ) {f : S2 → ℝ}
    (hf : Continuous f) (N i : ℕ) : Measurable (fun ω => LN ξ f X N ω i) := by
  unfold LN
  exact ((hf.measurable.comp (hX i)).sub (walk_measurable X hX ξ hf N i)).const_mul _

/-- The exceptional set of `LB_sample` is measurable (hypotheses: measurable samples and the
smoothness hypothesis of `LB_sample`, of which only `j = 0, 1` is used). -/
theorem LB_sample_set_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j)) {f : S2 → ℝ}
    (hf : ∀ j < 4, ∀ x, SphC2 (sphLapS^[j] f) x) (C F ξ : ℝ) (N : ℕ) (η : ℝ) :
    MeasurableSet {ω | ∃ i < N, 2 / ξ ^ 2 * (4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ) + C * ξ ^ 2
          < |LN ξ f X N ω i + sphLapS f (X i ω)|} := by
  have hf0 : ∀ x, SphC2 f x := by simpa using hf 0 (by norm_num)
  have hf1 : ∀ x, SphC2 (sphLapS f) x := by simpa using hf 1 (by norm_num)
  have hc0 := CTG.FunkHecke.Green.sphC2_cont hf0
  have hc1 := CTG.FunkHecke.Green.sphC2_cont hf1
  refine exists_lt_range_measurable N _ fun i => ?_
  exact measurableSet_lt measurable_const
    ((LN_measurable X hX ξ hc0 N i).add (hc1.measurable.comp (hX i))).abs

/-! ## (2) `walk_one_step` -/

theorem walk_one_step_set_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j)) (ξ : ℝ)
    (f : S2 → ℝ) (hf : Continuous f) (F : ℝ) (N : ℕ) (η : ℝ) :
    MeasurableSet {ω | ∃ i < N, 4 * (η * (1 + F) + 2 * F / (N - 1)) / sphZ ξ
        < |walk ξ f X N ω i - Pinf (gk ξ) f (X i ω)|} := by
  refine exists_lt_range_measurable N _ fun i => ?_
  exact measurableSet_lt measurable_const
    ((walk_measurable X hX ξ hf N i).sub ((Pinf_measurable ξ hf).comp (hX i))).abs

/-! ## (3) Eigenvalue sets -/

theorem Smat_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j)) (ξ : ℝ) (N : ℕ) :
    Measurable (fun ω => fun a b : Fin N => Smat ξ (fun i : Fin N => X i ω) a b) := by
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
  have hdeg : ∀ c : Fin N, Measurable (fun ω => deg ξ (fun i : Fin N => X i ω) c) := fun c => by
    unfold deg
    exact Finset.measurable_sum _ fun j _ => Kx_comp_measurable X hX ξ c j
  unfold Smat
  exact (Kx_comp_measurable X hX ξ a b).div
    (((hdeg a).sqrt).mul ((hdeg b).sqrt))

theorem eig_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j)) (ξ : ℝ) (N : ℕ)
    (j : Fin N) :
    Measurable (fun ω => (Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j) := by
  have e : (fun ω => (Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j)
      = fun ω => CTG.Reals.ExceptionalSets.eigTot N ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)
          (fun a b => Smat ξ (fun i : Fin N => X i ω) a b) := by
    funext ω
    rw [CTG.Reals.ExceptionalSets.eigTot_eq _ (Smat_hermitian ξ (fun i : Fin N => X i ω))]
    rfl
  rw [e]
  exact CTG.Reals.ExceptionalSets.eigTot_measurable_comp _ _ (Smat_measurable X hX ξ N)
    (fun ω => Smat_hermitian ξ (fun i : Fin N => X i ω))

theorem sample_eigenvalue_set_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j))
    (ξ : ℝ) (l : ℕ) (N : ℕ) (η : ℝ) :
    MeasurableSet {ω | ¬ ∃ j : Fin N,
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
          ≤ 4 * errE ξ (harmF pE qE l) η N / √(sphZ ξ * mE l)} := by
  have h : MeasurableSet {ω | ∃ j : Fin N,
      |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - sphS ξ l|
        ≤ 4 * errE ξ (harmF pE qE l) η N / √(sphZ ξ * mE l)} := by
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion fun j =>
      measurableSet_le ((eig_measurable X hX ξ N j).sub_const _).abs measurable_const
  exact h.compl

theorem card_filter_measurable {N : ℕ} (m : ℕ) (P : Ω → Fin N → Prop)
    [∀ ω, DecidablePred (P ω)] (hP : ∀ j, MeasurableSet {ω | P ω j}) :
    MeasurableSet {ω | m ≤ (Finset.univ.filter (P ω)).card} := by
  have e : {ω | m ≤ (Finset.univ.filter (P ω)).card}
      = ⋃ T : Finset (Fin N), ⋃ (_ : m ≤ T.card), ⋂ j ∈ T, {ω | P ω j} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro h; exact ⟨_, h, fun j hj => (Finset.mem_filter.1 hj).2⟩
    · rintro ⟨T, hT, hP'⟩
      exact hT.trans (Finset.card_le_card fun j hj =>
        Finset.mem_filter.2 ⟨Finset.mem_univ _, hP' j hj⟩)
  rw [e]
  exact MeasurableSet.iUnion fun T => MeasurableSet.iUnion fun _ =>
    Finset.measurableSet_biInter _ fun j _ => hP j

theorem sample_mult_gen_set_measurable (X : ℕ → Ω → S2) (hX : ∀ j, Measurable (X j))
    (ξ : ℝ) (m : ℕ) (s F γ0 : ℝ) (N : ℕ) (η δ : ℝ) :
    MeasurableSet {ω | ¬ (m ≤ (Finset.univ.filter (fun j : Fin N =>
        |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - s|
          ≤ N * errE ξ F η N * F * √(m:ℝ)
              / ((((N:ℝ) - 1) * sphZ ξ / 4) * (γ0 - m * δ)))).card)} := by
  have h := card_filter_measurable (Ω := Ω) (N := N) m
    (fun ω j => |(Smat_hermitian ξ (fun i : Fin N => X i ω)).eigenvalues j - s|
          ≤ N * errE ξ F η N * F * √(m:ℝ)
              / ((((N:ℝ) - 1) * sphZ ξ / 4) * (γ0 - m * δ)))
    (fun j => measurableSet_le ((eig_measurable X hX ξ N j).sub_const _).abs measurable_const)
  exact h.compl

end CTG.FunkHecke.A187

#print axioms CTG.FunkHecke.A187.LB_sample_set_measurable
#print axioms CTG.FunkHecke.A187.walk_one_step_set_measurable
#print axioms CTG.FunkHecke.A187.sample_eigenvalue_set_measurable
#print axioms CTG.FunkHecke.A187.sample_mult_gen_set_measurable
