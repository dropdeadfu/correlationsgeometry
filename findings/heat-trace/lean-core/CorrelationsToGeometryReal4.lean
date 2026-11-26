/-
From Correlations to Geometry -- tenth Lean file (Mathlib v4.29.0, Lean 4.29.0).
It imports the eleventh file `CorrelationsToGeometryReal3b.lean` (and through it the seventh, the third,
the second and the core file) and continues it.  The four namespaces
`VarianceGeneral`, `VarianceGeneral2`, `BiasNoLoops`, `VarianceGeneral3` were moved here UNCHANGED from
the end of the seventh file on 25 November 2026 (they were accepted there in a full run, state of 1669
statements): with them the compiled module of the seventh file could no longer be written on the
machine at hand (the kernel ended the process for lack of memory three times).  Check with `cd lean && ./check_real4.sh` (against
the COMPILED seventh and eleventh files in `../.tools/leanbuild/`).
No `sorry`, no `axiom`, no `native_decide`.  Every statement is a FORM of a statement of the paper
with the constants and exceptional events of these files; none of them is "the theorem of the paper,
machine-checked".  See the comments at the namespaces.
-/
import CorrelationsToGeometryReal3b

open MeasureTheory ProbabilityTheory CTG.Reals Matrix

namespace CTG.Reals2

namespace VarianceGeneral

open PiBound CTG.Reals.TorusReduction BiasVariance VarianceOne

/-! ## Part 1: the pair kernel `H_k` for every `k` -/

section PairKernel

/-- `𝒫ʲ f`, `(𝒫 f)(u) = ∫ p(u - z) f(z) dz`, `p = pker d σ`. -/
noncomputable def Pop (d : ℕ) (σ : ℝ) : ℕ → (FlatTorus d → ℝ) → FlatTorus d → ℝ
  | 0, f => f
  | j + 1, f => fun u => ∫ z, pker d σ (u - z) * Pop d σ j f z ∂flatTorusMeasure d

/-- `Γ_k = ∑_{l=1}^{k-1} p_l p_{k-l}` (`Γ_1 = 0`). -/
noncomputable def gam (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : ℝ :=
  ∑ l ∈ Finset.Ico 1 k, pker d ((l : ℝ) * σ) u * pker d (((k - l : ℕ) : ℝ) * σ) u

/-- `(1 - 𝒫)⁴ f`. -/
noncomputable def diff4 (d : ℕ) (σ : ℝ) (f : FlatTorus d → ℝ) (u : FlatTorus d) : ℝ :=
  Pop d σ 0 f u - 4 * Pop d σ 1 f u + 6 * Pop d σ 2 f u - 4 * Pop d σ 3 f u + Pop d σ 4 f u

/-- `(1 - 𝒫)³ f`. -/
noncomputable def diff3 (d : ℕ) (σ : ℝ) (f : FlatTorus d → ℝ) (u : FlatTorus d) : ℝ :=
  Pop d σ 0 f u - 3 * Pop d σ 1 f u + 3 * Pop d σ 2 f u - Pop d σ 3 f u

/-- **The pair kernel of `prop:variance`**:
    `H_k = k (1 - 𝒫)⁴ Γ_k - 2 k μ_k (1 - 𝒫)³ p`, `μ_k = m_k = torusM d σ k`. -/
noncomputable def Hk (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : ℝ :=
  (k : ℝ) * diff4 d σ (gam d σ k) u - 2 * k * torusM d σ k * diff3 d σ (pker d σ) u

theorem Pop_zero (d : ℕ) (σ : ℝ) (f : FlatTorus d → ℝ) : Pop d σ 0 f = f := rfl

theorem Pop_succ (d : ℕ) (σ : ℝ) (j : ℕ) (f : FlatTorus d → ℝ) (u : FlatTorus d) :
    Pop d σ (j + 1) f u = ∫ z, pker d σ (u - z) * Pop d σ j f z ∂flatTorusMeasure d := rfl

/-- `𝒫ʲ p = p_{j+1}`. -/
theorem Pop_pker {σ : ℝ} (hσ : 0 < σ) (d j : ℕ) :
    Pop d σ j (pker d σ) = pker d (((j + 1 : ℕ) : ℝ) * σ) := by
  induction j with
  | zero => funext u; simp [Pop_zero]
  | succ j ih =>
    funext u
    rw [Pop_succ, ih]
    have hτ : 0 < ((j + 1 : ℕ) : ℝ) * σ := by positivity
    have h := semigroup_all hσ hτ d u 0
    simp only [sub_zero] at h
    unfold pker
    rw [h]
    congr 2
    push_cast; ring

/-- `-(1 - 𝒫)³ p = ψ` of `VarianceOne` (`ψ = -k₀ + 3k₁ - 3k₂ + k₃`, `k_j = p_{j+1} - 1`). -/
theorem diff3_pker {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (u : FlatTorus d) :
    diff3 d σ (pker d σ) u = -VarianceOne.psiK (kT d σ) u := by
  unfold diff3 VarianceOne.psiK kT
  rw [Pop_pker hσ d 0, Pop_pker hσ d 1, Pop_pker hσ d 2, Pop_pker hσ d 3]
  ring

/-- The pair kernel in the form used in the files: `H_k = k (1 - 𝒫)⁴ Γ_k + 2 k m_k ψ`. -/
theorem Hk_eq {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (u : FlatTorus d) :
    Hk d σ k u = (k : ℝ) * diff4 d σ (gam d σ k) u + 2 * k * torusM d σ k * VarianceOne.psiK (kT d σ) u := by
  unfold Hk; rw [diff3_pker hσ]; ring

/-! ### continuity, evenness, mean -/

theorem Pop_cont {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    ∀ j, Continuous (Pop d σ j f) := by
  intro j
  induction j with
  | zero => exact hf
  | succ j ih =>
    have hu : Continuous (Function.uncurry fun (u z : FlatTorus d) =>
        pker d σ (u - z) * Pop d σ j f z) :=
      ((pker_continuous hσ d).comp (continuous_fst.sub continuous_snd)).mul
        (ih.comp continuous_snd)
    have h := continuous_parametric_integral_of_continuous (μ := flatTorusMeasure d) hu
      (isCompact_univ (X := FlatTorus d))
    simp only [Measure.restrict_univ] at h
    exact h

theorem neg_inv_int (d : ℕ) (g : FlatTorus d → ℝ) :
    ∫ z, g (-z) ∂flatTorusMeasure d = ∫ z, g z ∂flatTorusMeasure d := by
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  exact integral_neg_eq_self g (flatTorusMeasure d)

theorem Pop_even (d : ℕ) (σ : ℝ) {f : FlatTorus d → ℝ} (hf : ∀ u, f (-u) = f u) :
    ∀ j u, Pop d σ j f (-u) = Pop d σ j f u := by
  intro j
  induction j with
  | zero => exact hf
  | succ j ih =>
    intro u
    rw [Pop_succ, Pop_succ, ← neg_inv_int d]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show pker d σ (-u - -z) * Pop d σ j f (-z) = pker d σ (u - z) * Pop d σ j f z
    rw [ih z, show -u - -z = -(u - z) by abel]
    unfold pker
    rw [heatTorus_even]

theorem prod_integrable (d : ℕ) {F : FlatTorus d × FlatTorus d → ℝ} (hF : Continuous F) :
    Integrable F ((flatTorusMeasure d).prod (flatTorusMeasure d)) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `∫ 𝒫ʲ f = ∫ f`. -/
theorem Pop_int {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    ∀ j, ∫ u, Pop d σ j f u ∂flatTorusMeasure d = ∫ u, f u ∂flatTorusMeasure d := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]
    simp_rw [Pop_succ]
    have hc : Continuous (Function.uncurry fun (u z : FlatTorus d) =>
        pker d σ (u - z) * Pop d σ j f z) :=
      ((pker_continuous hσ d).comp (continuous_fst.sub continuous_snd)).mul
        ((Pop_cont hσ d hf j).comp continuous_snd)
    rw [integral_integral_swap (prod_integrable d hc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ∫ u, pker d σ (u - z) * Pop d σ j f z ∂flatTorusMeasure d = Pop d σ j f z
    rw [integral_mul_const]
    have e : ∀ u, pker d σ (u - z) = pker d σ (z - u) := fun u => pker_even' d σ u z
    simp_rw [e]
    rw [pker_mass hσ d z, one_mul]

theorem gam_cont {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) : Continuous (gam d σ k) := by
  unfold gam
  refine continuous_finset_sum _ fun l hl => ?_
  have hl' := Finset.mem_Ico.mp hl
  have h1 : 0 < (l : ℝ) * σ := by
    have : (0 : ℝ) < l := by exact_mod_cast hl'.1
    positivity
  have h2 : 0 < ((k - l : ℕ) : ℝ) * σ := by
    have : (0 : ℝ) < ((k - l : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - l)
    positivity
  exact (pker_continuous h1 d).mul (pker_continuous h2 d)

theorem gam_even (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : gam d σ k (-u) = gam d σ k u := by
  unfold gam pker
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [heatTorus_even, heatTorus_even]

theorem diff4_cont {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    Continuous (diff4 d σ f) := by
  have c := Pop_cont hσ d hf
  unfold diff4
  exact ((((c 0).sub (continuous_const.mul (c 1))).add (continuous_const.mul (c 2))).sub
    (continuous_const.mul (c 3))).add (c 4)

theorem diff3_cont {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    Continuous (diff3 d σ f) := by
  have c := Pop_cont hσ d hf
  unfold diff3
  exact (((c 0).sub (continuous_const.mul (c 1))).add (continuous_const.mul (c 2))).sub (c 3)

theorem Hk_cont {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) : Continuous (Hk d σ k) := by
  unfold Hk
  exact (continuous_const.mul (diff4_cont hσ d (gam_cont hσ d k))).sub
    (continuous_const.mul (diff3_cont hσ d (pker_continuous hσ d)))

theorem Hk_even (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) : Hk d σ k (-u) = Hk d σ k u := by
  have e1 := Pop_even d σ (gam_even d σ k)
  have e2 := Pop_even d σ (f := pker d σ) (fun u => by unfold pker; exact heatTorus_even d _ u)
  unfold Hk diff4 diff3
  rw [e1 0, e1 1, e1 2, e1 3, e1 4, e2 0, e2 1, e2 2, e2 3]

theorem diff4_int {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    ∫ u, diff4 d σ f u ∂flatTorusMeasure d = 0 := by
  have c := Pop_cont hσ d hf
  have i : ∀ j, Integrable (Pop d σ j f) (flatTorusMeasure d) := fun j => flat_integrable d _ (c j)
  have hI := Pop_int hσ d hf
  have j1 : Integrable (fun u => Pop d σ 0 f u - 4 * Pop d σ 1 f u) (flatTorusMeasure d) :=
    (i 0).sub ((i 1).const_mul 4)
  have j2 : Integrable (fun u => Pop d σ 0 f u - 4 * Pop d σ 1 f u + 6 * Pop d σ 2 f u)
      (flatTorusMeasure d) := j1.add ((i 2).const_mul 6)
  have j3 : Integrable (fun u => Pop d σ 0 f u - 4 * Pop d σ 1 f u + 6 * Pop d σ 2 f u
      - 4 * Pop d σ 3 f u) (flatTorusMeasure d) := j2.sub ((i 3).const_mul 4)
  unfold diff4
  rw [integral_add j3 (i 4), integral_sub j2 ((i 3).const_mul 4), integral_add j1 ((i 2).const_mul 6),
    integral_sub (i 0) ((i 1).const_mul 4),
    integral_const_mul, integral_const_mul, integral_const_mul, hI 0, hI 1, hI 2, hI 3, hI 4]
  ring

theorem diff3_int {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    ∫ u, diff3 d σ f u ∂flatTorusMeasure d = 0 := by
  have c := Pop_cont hσ d hf
  have i : ∀ j, Integrable (Pop d σ j f) (flatTorusMeasure d) := fun j => flat_integrable d _ (c j)
  have hI := Pop_int hσ d hf
  have j1 : Integrable (fun u => Pop d σ 0 f u - 3 * Pop d σ 1 f u) (flatTorusMeasure d) :=
    (i 0).sub ((i 1).const_mul 3)
  have j2 : Integrable (fun u => Pop d σ 0 f u - 3 * Pop d σ 1 f u + 3 * Pop d σ 2 f u)
      (flatTorusMeasure d) := j1.add ((i 2).const_mul 3)
  unfold diff3
  rw [integral_sub j2 (i 3), integral_add j1 ((i 2).const_mul 3),
    integral_sub (i 0) ((i 1).const_mul 3),
    integral_const_mul, integral_const_mul, hI 0, hI 1, hI 2, hI 3]
  ring

/-- **`∫ H_k = 0`** (`prop:variance`). -/
theorem Hk_int {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) : ∫ u, Hk d σ k u ∂flatTorusMeasure d = 0 := by
  have c4 := diff4_cont hσ d (gam_cont hσ d k)
  have c3 := diff3_cont hσ d (pker_continuous hσ d)
  unfold Hk
  rw [integral_sub ((flat_integrable d _ c4).const_mul _) ((flat_integrable d _ c3).const_mul _),
    integral_const_mul, integral_const_mul, diff4_int hσ d (gam_cont hσ d k),
    diff3_int hσ d (pker_continuous hσ d)]
  ring

/-- **`∫ H_k(x - z) dz = 0` for every `x`** (degeneracy). -/
theorem Hk_mean {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) (x : FlatTorus d) :
    ∫ z, Hk d σ k (x - z) ∂flatTorusMeasure d = 0 := by
  rw [(torus_vk (d := d) hσ).inv (Hk d σ k) (Hk_cont hσ d k).measurable x]
  exact Hk_int hσ d k

end PairKernel


/-! ## Part 2: the degenerate two-point statistic `U_k`, `v_k`, and `Var U_k` exactly -/

section Ustat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `U_k = (1/(2N²)) ∑_{i≠j} H_k(X_i - X_j)`. -/
noncomputable def Uk (d : ℕ) (σ : ℝ) (k : ℕ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) : ℝ :=
  1 / (2 * (N : ℝ) ^ 2) * Soff (Hk d σ k) X N ω

/-- `v_k = ½ ∫ H_k²`. -/
noncomputable def vk (d : ℕ) (σ : ℝ) (k : ℕ) : ℝ := 1 / 2 * ∫ u, Hk d σ k u ^ 2 ∂flatTorusMeasure d

theorem bound_of_cont (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    ∃ C, ∀ u, |f u| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := FlatTorus d)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, fun u => by simpa [Real.norm_eq_abs] using hC u (Set.mem_univ u)⟩

theorem vk_nonneg (d : ℕ) (σ : ℝ) (k : ℕ) : 0 ≤ vk d σ k := by
  unfold vk
  have : 0 ≤ ∫ u, Hk d σ k u ^ 2 ∂flatTorusMeasure d :=
    integral_nonneg fun u => _root_.sq_nonneg (Hk d σ k u)
  positivity

/-- **`E U_k = 0` and `Var U_k = v_k (N-1)/N³` exactly** (independent uniform points). -/
theorem Uk_var [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (k N : ℕ) :
    BM (Uk d σ k X N) ∧ ∫ ω, Uk d σ k X N ω ∂μ = 0
      ∧ cv μ (Uk d σ k X N) = vk d σ k * ((N : ℝ) - 1) / (N : ℝ) ^ 3 := by
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  have V := torus_vk (d := d) hσ
  obtain ⟨C, hC⟩ := bound_of_cont d (Hk_cont hσ d k)
  have Dψ : Deg2 μ (flatTorusMeasure d) X (Hk d σ k) C (C ^ 2) :=
    deg2_of H (Hk_cont hσ d k).measurable hC (Hk_even d σ k) (Hk_mean hσ d k)
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = ∫ u, Hk d σ k u ^ 2 ∂flatTorusMeasure d := ⟨_, rfl⟩
  have hW : ∀ x, ∫ z, Hk d σ k (x - z) ^ 2 ∂flatTorusMeasure d = W := fun x => by
    rw [hWd]; exact V.inv (fun u => Hk d σ k u ^ 2) ((Hk_cont hσ d k).measurable.pow_const 2) x
  have sm := deg_second_moment Dψ hW N
  have mz := deg_mean Dψ N
  have bS : BM (Soff (Hk d σ k) X N) :=
    ⟨OracleTwo.Soff_meas Dψ N, _, OracleTwo.Soff_bound Dψ N⟩
  have bU : BM (Uk d σ k X N) := BM.const_mul _ bS
  have hU0 : ∫ ω, Uk d σ k X N ω ∂μ = 0 := by
    unfold Uk; rw [integral_const_mul, mz, mul_zero]
  refine ⟨bU, hU0, ?_⟩
  rw [cv_of_mean_zero bU hU0]
  have hv : vk d σ k = 1 / 2 * W := by rw [hWd]; rfl
  have e : ∀ ω, Uk d σ k X N ω ^ 2 = (1 / (2 * (N : ℝ) ^ 2)) ^ 2 * Soff (Hk d σ k) X N ω ^ 2 :=
    fun ω => by unfold Uk; ring
  simp_rw [e]
  rw [integral_const_mul, sm, hv]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

end Ustat

/-! ## Part 3: agreement with `k = 1` (`VarianceOne`) and `k = 2` (`VarianceTwo`) -/

section Agree

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem Pop_zero_fn (d : ℕ) (σ : ℝ) : ∀ j u, Pop d σ j (fun _ => (0 : ℝ)) u = 0 := by
  intro j
  induction j with
  | zero => intro u; rfl
  | succ j ih => intro u; rw [Pop_succ]; simp [ih]

theorem gam_one (d : ℕ) (σ : ℝ) : gam d σ 1 = fun _ => 0 := by
  funext u; simp [gam]

theorem gam_two (d : ℕ) (σ : ℝ) : gam d σ 2 = fun u => pker d σ u ^ 2 := by
  funext u; simp [gam, pow_two]

/-- **`H₁ = 2 m₁ ψ`** (the pair kernel of `VarianceOne`). -/
theorem Hk_one {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (u : FlatTorus d) :
    Hk d σ 1 u = 2 * torusM d σ 1 * VarianceOne.psiK (kT d σ) u := by
  rw [Hk_eq hσ, gam_one]
  unfold diff4
  simp only [Pop_zero_fn]
  push_cast; ring

theorem Soff_smul {G : Type*} [AddCommGroup G] (a : ℝ) (f : G → ℝ) (X : ℕ → Ω → G) (N : ℕ)
    (ω : Ω) : Soff (fun u => a * f u) X N ω = a * Soff f X N ω := by
  unfold Soff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aT
  split_ifs <;> ring

theorem Uk_one {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    Uk d σ 1 X N ω = Ustat (torusM d σ 1) (kT d σ) X N ω := by
  have e : Hk d σ 1 = fun u => (2 * torusM d σ 1) * VarianceOne.psiK (kT d σ) u :=
    funext (Hk_one hσ d)
  unfold Uk Ustat
  rw [e, Soff_smul]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

theorem vk_one {σ : ℝ} (hσ : 0 < σ) (d : ℕ) : vk d σ 1 = v1 d σ := by
  unfold vk v1
  simp_rw [Hk_one hσ d]
  have e : ∀ u, (2 * torusM d σ 1 * VarianceOne.psiK (kT d σ) u) ^ 2
      = (4 * torusM d σ 1 ^ 2) * VarianceOne.psiK (kT d σ) u ^ 2 := fun u => by ring
  simp_rw [e]
  rw [integral_const_mul]; ring


theorem bm_cont (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) : BM f :=
  ⟨hf.measurable, bound_of_cont d hf⟩

/-- `w_j = 𝒫ʲ p² - m₂` (the family `wT` of `VarianceTwo`). -/
theorem wT_eq {σ : ℝ} (hσ : 0 < σ) (d : ℕ) :
    ∀ j u, VarianceTwo.wT d σ j u = Pop d σ j (fun v => pker d σ v ^ 2) u - torusM d σ 2 := by
  have W := VarianceTwo.torus_wk (d := d) hσ
  intro j
  induction j with
  | zero => intro u; rfl
  | succ j ih =>
    intro u
    have hm : ∫ z, VarianceTwo.wT d σ j z ∂flatTorusMeasure d = 0 := by
      have h := W.mean j 0
      simp only [zero_sub] at h
      rw [← neg_inv_int d]
      exact h
    have bw : BM (VarianceTwo.wT d σ j) := ⟨W.meas j, _, W.bound j⟩
    have cp : Continuous fun z : FlatTorus d => pker d σ (u - z) :=
      (pker_continuous hσ d).comp (continuous_const.sub continuous_id)
    have cq := Pop_cont hσ d (f := fun v => pker d σ v ^ 2) ((pker_continuous hσ d).pow 2) j
    have i1 : Integrable (fun z => pker d σ (u - z) * Pop d σ j (fun v => pker d σ v ^ 2) z)
        (flatTorusMeasure d) := flat_integrable d _ (cp.mul cq)
    have i2 : Integrable (fun z => torusM d σ 2 * pker d σ (u - z)) (flatTorusMeasure d) :=
      (flat_integrable d _ cp).const_mul _
    have i3 : Integrable (VarianceTwo.wT d σ j) (flatTorusMeasure d) := bw.integrable
    show VarianceTwo.cconv (flatTorusMeasure d) (kT d σ 0) (VarianceTwo.wT d σ j) u = _
    unfold VarianceTwo.cconv
    rw [kT_zero]
    unfold cK
    have e : ∀ z, VarianceTwo.wT d σ j z * (pker d σ (u - z) - 1)
        = pker d σ (u - z) * Pop d σ j (fun v => pker d σ v ^ 2) z
          - torusM d σ 2 * pker d σ (u - z) - VarianceTwo.wT d σ j z := fun z => by
      rw [ih z]; ring
    simp_rw [e]
    have i12 : Integrable (fun z => pker d σ (u - z) * Pop d σ j (fun v => pker d σ v ^ 2) z
        - torusM d σ 2 * pker d σ (u - z)) (flatTorusMeasure d) := i1.sub i2
    rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, pker_mass hσ d u, hm,
      Pop_succ]
    ring

theorem phiW_eq {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (u : FlatTorus d) :
    VarianceTwo.phiW (VarianceTwo.wT d σ) u = diff4 d σ (fun v => pker d σ v ^ 2) u := by
  unfold VarianceTwo.phiW diff4
  rw [wT_eq hσ d 0, wT_eq hσ d 1, wT_eq hσ d 2, wT_eq hσ d 3, wT_eq hσ d 4]
  ring

/-- **`H₂ = 2 Ψ₂`** (the pair kernel of `VarianceTwo`). -/
theorem Hk_two {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (u : FlatTorus d) :
    Hk d σ 2 u = 2 * VarianceTwo.psi2 (torusM d σ 2) (kT d σ) (VarianceTwo.wT d σ) u := by
  rw [Hk_eq hσ, gam_two]
  unfold VarianceTwo.psi2
  rw [phiW_eq hσ d u]
  push_cast; ring

theorem Uk_two {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    Uk d σ 2 X N ω = VarianceTwo.U2 (torusM d σ 2) (kT d σ) (VarianceTwo.wT d σ) X N ω := by
  have e : Hk d σ 2
      = fun u => 2 * VarianceTwo.psi2 (torusM d σ 2) (kT d σ) (VarianceTwo.wT d σ) u :=
    funext (Hk_two hσ d)
  unfold Uk VarianceTwo.U2
  rw [e, Soff_smul]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

theorem vk_two {σ : ℝ} (hσ : 0 < σ) (d : ℕ) : vk d σ 2 = VarianceTwo.v2 d σ := by
  unfold vk VarianceTwo.v2
  simp_rw [Hk_two hσ d]
  have e : ∀ u, (2 * VarianceTwo.psi2 (torusM d σ 2) (kT d σ) (VarianceTwo.wT d σ) u) ^ 2
      = 4 * VarianceTwo.psi2 (torusM d σ 2) (kT d σ) (VarianceTwo.wT d σ) u ^ 2 := fun u => by ring
  simp_rw [e]
  rw [integral_const_mul]; ring

end Agree


/-! ## Part 4: `β_k = ½ H_k(0)` (last sentence of `prop:variance`) -/

section Beta

/-- `𝒫^{c+1} f = p_{(c+1)σ} * f` for continuous `f` (semigroup and Fubini). -/
theorem Pop_conv {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {f : FlatTorus d → ℝ} (hf : Continuous f) :
    ∀ c u, Pop d σ (c + 1) f u
      = ∫ z, pker d (((c + 1 : ℕ) : ℝ) * σ) (u - z) * f z ∂flatTorusMeasure d := by
  intro c
  induction c with
  | zero => intro u; rw [Pop_succ]; simp [Pop_zero]
  | succ c ih =>
    intro u
    have hτ : 0 < ((c + 1 : ℕ) : ℝ) * σ := by positivity
    rw [Pop_succ]
    simp_rw [ih]
    have e1 : ∀ z, pker d σ (u - z) * ∫ y, pker d (((c + 1 : ℕ) : ℝ) * σ) (z - y) * f y
          ∂flatTorusMeasure d
        = ∫ y, pker d σ (u - z) * (pker d (((c + 1 : ℕ) : ℝ) * σ) (z - y) * f y)
          ∂flatTorusMeasure d := fun z => (integral_const_mul _ _).symm
    simp_rw [e1]
    have hc : Continuous (Function.uncurry fun (z y : FlatTorus d) =>
        pker d σ (u - z) * (pker d (((c + 1 : ℕ) : ℝ) * σ) (z - y) * f y)) :=
      ((pker_continuous hσ d).comp (continuous_const.sub continuous_fst)).mul
        (((pker_continuous hτ d).comp (continuous_fst.sub continuous_snd)).mul
          (hf.comp continuous_snd))
    rw [integral_integral_swap (prod_integrable d hc)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ∫ z, pker d σ (u - z) * (pker d (((c + 1 : ℕ) : ℝ) * σ) (z - y) * f y)
        ∂flatTorusMeasure d = pker d (((c + 1 + 1 : ℕ) : ℝ) * σ) (u - y) * f y
    have e2 : ∀ z, pker d σ (u - z) * (pker d (((c + 1 : ℕ) : ℝ) * σ) (z - y) * f y)
        = (pker d σ (u - z) * pker d (((c + 1 : ℕ) : ℝ) * σ) (z - y)) * f y := fun z => by ring
    simp_rw [e2]
    rw [integral_mul_const]
    have h := semigroup_all hσ hτ d u y
    unfold pker
    rw [h]
    congr 3
    push_cast; ring

theorem pker_zero_eq (d : ℕ) (σ : ℝ) (s : ℕ) : pker d ((s : ℝ) * σ) 0 = torusM d σ s := rfl

theorem gam_zero (d : ℕ) (σ : ℝ) (k : ℕ) : gam d σ k 0 = BiasGeneral.sig0 d σ k := by
  unfold gam BiasGeneral.sig0
  rfl

/-- `(𝒫^c Γ_k)(0) = Σ_c` of `prop:bias` (`c ≥ 1`). -/
theorem Pop_gam_zero {σ : ℝ} (hσ : 0 < σ) (d k c : ℕ) :
    Pop d σ (c + 1) (gam d σ k) 0 = BiasGeneral.sigC d σ k (c + 1) := by
  rw [Pop_conv hσ d (gam_cont hσ d k)]
  unfold BiasGeneral.sigC gam
  have ev : ∀ z : FlatTorus d, pker d (((c + 1 : ℕ) : ℝ) * σ) (0 - z)
      = pker d (((c + 1 : ℕ) : ℝ) * σ) z := fun z => by
    rw [zero_sub]; unfold pker; exact heatTorus_even d _ z
  simp_rw [ev, Finset.mul_sum]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show pker d (((c + 1 : ℕ) : ℝ) * σ) z * (pker d ((l : ℝ) * σ) z
        * pker d (((k - l : ℕ) : ℝ) * σ) z)
      = pker d ((l : ℝ) * σ) z * pker d (((k - l : ℕ) : ℝ) * σ) z
        * pker d (((c + 1 : ℕ) : ℝ) * σ) z
    ring
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have h0 : 0 < ((c + 1 : ℕ) : ℝ) * σ := by positivity
    have h1 : 0 < (l : ℝ) * σ := by
      have : (0 : ℝ) < l := by exact_mod_cast hl'.1
      positivity
    have h2 : 0 < ((k - l : ℕ) : ℝ) * σ := by
      have : (0 : ℝ) < ((k - l : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - l)
      positivity
    exact flat_integrable d _ ((pker_continuous h0 d).mul
      ((pker_continuous h1 d).mul (pker_continuous h2 d)))

/-- **`β_k = ½ H_k(0)`** (`prop:variance`, last sentence; `β_k = betaK d σ k` of `prop:bias` with
    self-loops, `ρ = p(0)`), every `k`. -/
theorem betaK_eq_half_Hk {σ : ℝ} (hσ : 0 < σ) (d k : ℕ) :
    BiasGeneral.betaK d σ k = 1 / 2 * Hk d σ k 0 := by
  unfold Hk diff4 diff3
  rw [Pop_zero, Pop_zero, gam_zero, Pop_gam_zero hσ d k 0, Pop_gam_zero hσ d k 1,
    Pop_gam_zero hσ d k 2, Pop_gam_zero hσ d k 3, Pop_pker hσ d 1, Pop_pker hσ d 2,
    Pop_pker hσ d 3, pker_zero_eq, pker_zero_eq, pker_zero_eq]
  have h1 : pker d σ 0 = torusM d σ 1 := by
    rw [← pker_zero_eq]; simp
  rw [h1]
  unfold BiasGeneral.betaK
  ring

end Beta


/-! ## Part 5: `E (Tr P^k - Q)²` on the normalisation event (Step 1 of the proof), every `k` -/

section Step1

open WalkCount BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 BiasGeneral6
  BiasVariance BiasVariance4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The polynomial statistic `QT` (`Q₀ + Q₁ + Q₂ + Q₃` of `prop:bias`) is bounded and measurable. -/
theorem QT_bm [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (hX : ∀ j, Measurable (X j)) {N n : ℕ} :
    BM (fun ω => QT d σ N n (fun j => X j ω)) := by
  have hM := torusM_one_ge hσ d
  have hPB := fun l => phi_bounds hσ d n l
  have hB4M : torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 ≤ B4 d σ n := by
    unfold B4
    have h1 : torusM d σ 1 ≤ torusM d σ 1 ^ 2 := by nlinarith
    have h2 : torusM d σ 1 ^ 2 ≤ torusM d σ 1 ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    have : 0 ≤ torusM d σ 1 ^ (n + 1) := by positivity
    calc torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1
        = torusM d σ 1 ^ (n + 1) * torusM d σ 1 ^ 2 := by ring
      _ ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 ^ 4 := mul_le_mul_of_nonneg_left h2 this
  have hPA : ∀ p, |PhiA d σ n p| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 := by
    intro p; unfold PhiA
    rw [abs_mul, abs_of_nonneg (cyT_bounds hσ d p.1).1]
    exact mul_le_mul (cyT_bounds hσ d p.1).2 (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  have hPBb : ∀ p, |PhiB d σ n p| ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1 := by
    intro p
    unfold PhiB
    rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1,
      abs_of_nonneg (heatP_nonneg hσ d 1 _)]
    exact mul_le_mul (mul_le_mul (cyT_bounds hσ d _).2 (heatP_le hσ d le_rfl _)
      (heatP_nonneg hσ d 1 _) (by positivity)) (cK_bound hσ d _) (abs_nonneg _) (by positivity)
  -- integrability
  have i0 : BM (fun ω => (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω))
      / (N : ℝ) ^ (n + 1)) :=
    ((BM.sum _ _ fun v _ => (⟨(cyT_meas hσ d n).comp (measurable_pi_lambda _ fun a => hX _),
      torusM d σ 1 ^ (n + 1), fun ω => by
        rw [abs_of_nonneg (cyT_bounds hσ d _).1]; exact (cyT_bounds hσ d _).2⟩ :
          BM fun ω => cyT d σ (fun a => X (v a) ω))).div_const _)
  have iA : BM (fun ω => gA d σ N n (fun j => X j ω)) :=
    ((bm2 X hX _ (PhiA_meas hσ d n) hPA).div_const _)
  have iB : BM (fun ω => gB d σ N n (fun j => X j ω)) :=
    ((bm2 X hX _ (PhiB_meas hσ d n) hPBb).div_const _)
  have i3 : ∀ {s : ℕ} (Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ),
      Measurable Φ → (∀ p, |Φ p| ≤ B4 d σ n) →
      BM (fun ω => g3 N Φ (fun j => X j ω)) :=
    fun Φ hΦ hB => ((bm3 X hX Φ hΦ hB).div_const _)
  have iEE := i3 _ (PhiEE_meas hσ d n) (hPB 0).1
  have iEB := i3 _ (PhiEB_meas hσ d n) (hPB 0).2.1
  have iBB := i3 _ (PhiBB_meas hσ d n) (hPB 0).2.2.1
  have iS := i3 _ (PhiS_meas hσ d n) (hPB 0).2.2.2.1
  have iqee := fun l => i3 _ (PhiQee_meas hσ d n l) (hPB l).2.2.2.2.1
  have iqeb := fun l => i3 _ (PhiQeb_meas hσ d n l) (hPB l).2.2.2.2.2.1
  have iqbe := fun l => i3 _ (PhiQbe_meas hσ d n l) (hPB l).2.2.2.2.2.2.1
  have iqbb := fun l => i3 _ (PhiQbb_meas hσ d n l) (hPB l).2.2.2.2.2.2.2
  have kG : BM (fun ω => -2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω)) :=
    ((((((BM.const_mul (-2) iA).add iB).add (BM.const_mul 3 iEE)).sub (BM.const_mul 3 iEB)).add iBB).sub iS)
  have kHl : ∀ l : Fin (n + 1), BM (fun ω => 4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)) := fun l =>
    (((BM.const_mul 4 (iqee l)).sub (BM.const_mul 2 (iqeb l))).sub (BM.const_mul 2 (iqbe l))).add (iqbb l)
  have kH : BM (fun ω => ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω))) :=
    BM.sum _ _ fun l _ => kHl l
  have eQ : (fun ω => QT d σ N n (fun j => X j ω)) = fun ω =>
      (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω)) / (N : ℝ) ^ (n + 1)
      + ((n : ℝ) + 1) * (-2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω))
      + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)) := by
    funext ω; rfl
  have kG' : BM (fun ω => ((n : ℝ) + 1) * (-2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω))) := BM.const_mul _ kG
  have kH' : BM (fun ω => ((n : ℝ) + 1) / 2 * (∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * g3 N (PhiQee d σ n l) (fun j => X j ω)
      - 2 * g3 N (PhiQeb d σ n l) (fun j => X j ω) - 2 * g3 N (PhiQbe d σ n l) (fun j => X j ω)
      + g3 N (PhiQbb d σ n l) (fun j => X j ω)))) := BM.const_mul _ kH
  have kL : BM (fun ω => (∑ v : Fin (n + 1) → Fin N, cyT d σ (fun a => X (v a) ω)) / (N : ℝ) ^ (n + 1) + ((n : ℝ) + 1) * (-2 * gA d σ N n (fun j => X j ω) + gB d σ N n (fun j => X j ω)
      + 3 * g3 N (PhiEE d σ n) (fun j => X j ω) - 3 * g3 N (PhiEB d σ n) (fun j => X j ω)
      + g3 N (PhiBB d σ n) (fun j => X j ω) - g3 N (PhiS d σ n) (fun j => X j ω))) := i0.add kG'
  rw [eQ]
  exact kL.add kH'

theorem trace_pow_bm {σ : ℝ} (hσ : 0 < σ) {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (hX : ∀ j, Measurable (X j)) (N k : ℕ) :
    BM (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ k).trace)
      ∧ ∀ ω, |((torusWalk d σ N (fun j => X j ω)) ^ k).trace| ≤ N := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hT01 : ∀ ω (a : Fin N), 0 ≤ ((torusWalk d σ N (fun j => X j ω)) ^ k) a a
      ∧ ((torusWalk d σ N (fun j => X j ω)) ^ k) a a ≤ 1 := fun ω a =>
    BiasVariance4.walk_pow_diag_unit _ _ (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) k a
  have hTb : ∀ ω, |((torusWalk d σ N (fun j => X j ω)) ^ k).trace| ≤ N := by
    intro ω
    have h0 : 0 ≤ ((torusWalk d σ N (fun j => X j ω)) ^ k).trace :=
      Finset.sum_nonneg fun a _ => (hT01 ω a).1
    rw [abs_of_nonneg h0]
    calc ((torusWalk d σ N (fun j => X j ω)) ^ k).trace
        ≤ ∑ _a : Fin N, (1 : ℝ) := Finset.sum_le_sum fun a _ => (hT01 ω a).2
      _ = N := by simp
  exact ⟨⟨Finset.measurable_sum _ fun a _ => walk_pow_entry_measurable hσ d X hX N k a a, N, hTb⟩,
    hTb⟩

theorem sq_step {T Q A S δ : ℝ} (hA : 0 ≤ A) (hS : 0 ≤ S) (hSδ : S ≤ δ ^ 2)
    (h : |T - Q| ≤ A * S) : (T - Q) ^ 2 ≤ A ^ 2 * δ ^ 2 * S := by
  have h1 : (T - Q) ^ 2 ≤ (A * S) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h2 : (A * S) ^ 2 ≤ A ^ 2 * δ ^ 2 * S := by
    have : A ^ 2 * S * S ≤ A ^ 2 * S * δ ^ 2 :=
      mul_le_mul_of_nonneg_left hSδ (mul_nonneg (_root_.sq_nonneg A) hS)
    nlinarith only [this]
  linarith only [h1, h2]

/-- **Step 1 of the proof of `prop:variance` for every `k = n + 1`** (with self-loops, heat kernel
    on the flat torus, general normalisation event): for independent uniform points, `N ≥ 1`,
    `0 ≤ δ ≤ 1/8`:
    `E (Tr P^k - QT)² ≤ (gK δ m₁)² δ² (2 m₁²/N) + (N + CQT)² P(max_a |ρ_a - 1| > δ)`,
    `QT` the polynomial statistic of `prop:bias` (`BiasGeneral6.QT`). -/
theorem trace_QT_sq [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (n : ℕ) :
    ∫ ω, (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - QT d σ N n (fun j => X j ω)) ^ 2 ∂μ
      ≤ (gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
        + (N + CQT d σ n) ^ 2
          * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
  have H := torus_bvk X h_indep hX hlaw hσ
  have hN' : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  obtain ⟨bT, hTb⟩ := trace_pow_bm hσ X hX N (n + 1)
  have bQ := QT_bm (μ := μ) hσ d X hX (N := N) (n := n)
  have hGm : MeasurableSet {ω | ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => measurableSet_le
      (continuous_abs.measurable.comp
        ((heatRho_sample_measurable hσ d X hX N a).sub measurable_const)) measurable_const
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Set Ω,
      Gc = {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  have hGcm : MeasurableSet Gc := by rw [hGc]; exact hGm.compl
  rw [← hGc, ← hMd]
  have bS2 : BM (fun ω => ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) :=
    BM.sum _ _ fun q _ => (H.bmH N q).mul (H.bmH N q)
  have hS2n : ∀ ω, 0 ≤ ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω := fun ω =>
    Finset.sum_nonneg fun q _ => _root_.mul_self_nonneg _
  have hgK := gK_nonneg n
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = gK n * δ * M := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact mul_nonneg (mul_nonneg hgK hδ0) hM0
  have hpt : ∀ ω, (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - QT d σ N n (fun j => X j ω)) ^ 2
      ≤ A ^ 2 * δ ^ 2 * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
          Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω)
        + (N + CQT d σ n) ^ 2 * Gc.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    have hS0 : 0 ≤ 1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
        Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω := mul_nonneg (by positivity) (hS2n ω)
    by_cases hω : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ
    · have hnot : ω ∉ Gc := by rw [hGc]; exact fun h => h hω
      rw [Set.indicator_of_notMem hnot, mul_zero, add_zero]
      have h := trace_QT_good hσ hN' n (fun j => X j ω) hδ hω
      have hSδ : 1 / (N : ℝ) * ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2 ≤ δ ^ 2 := by
        have hi : ∀ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2 ≤ δ ^ 2 := fun i => by
          have e := eps_row d σ hN' (fun j => X j ω) i
          have hb := hω i
          unfold eV
          rw [← e, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        calc 1 / (N : ℝ) * ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2
            ≤ 1 / (N : ℝ) * ∑ _i : Fin N, δ ^ 2 :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) (by positivity)
          _ = δ ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
      rw [eV_sq_sum σ hN' X ω] at h hSδ
      have h' : |((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - QT d σ N n (fun j => X j ω)| ≤ A * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
            Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) := by
        refine h.trans (le_of_eq ?_)
        rw [hA, ← hMd]; unfold gK; ring
      exact sq_step hA0 hS0 hSδ h'
    · have hin : ω ∈ Gc := by rw [hGc]; exact hω
      rw [Set.indicator_of_mem hin, mul_one]
      have hq := QT_abs hσ d hN n (fun j => X j ω)
      have h0 : 0 ≤ A ^ 2 * δ ^ 2 * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
          Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) := by positivity
      have hab : |((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - QT d σ N n (fun j => X j ω)| ≤ N + CQT d σ n :=
        (abs_sub _ _).trans (add_le_add (hTb ω) hq)
      have hsq : (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - QT d σ N n (fun j => X j ω)) ^ 2 ≤ (N + CQT d σ n) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hab 2
      linarith only [hsq, h0]
  have bg1 := BM.const_mul (A ^ 2 * δ ^ 2) (BM.const_mul (1 / (N : ℝ) ^ 3) bS2)
  have ig2 : Integrable (fun ω => (N + CQT d σ n) ^ 2 * Gc.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hGcm).const_mul _
  have iL : Integrable (fun ω => (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - QT d σ N n (fun j => X j ω)) ^ 2) μ := (bT.sub bQ).sqr.integrable
  have ig : Integrable (fun ω => A ^ 2 * δ ^ 2 * (1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
          Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω)
        + (N + CQT d σ n) ^ 2 * Gc.indicator (fun _ => (1 : ℝ)) ω) μ := bg1.integrable.add ig2
  have hint := integral_mono iL ig hpt
  rw [integral_add bg1.integrable ig2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator_const (1 : ℝ) hGcm, smul_eq_mul, mul_one] at hint
  have e2 := H.mean_E2 N
  have r := H.rs_le hN
  rw [← hMd] at r
  have hS2 : ∫ ω, ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ ≤ N * (2 * N * M ^ 2) := by
    rw [e2]; exact mul_le_mul_of_nonneg_left r hNpos.le
  have h1 : 1 / (N : ℝ) ^ 3 * ∫ ω, ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω ∂μ ≤ 2 * M ^ 2 / N := by
    have h1 := mul_le_mul_of_nonneg_left hS2 (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 3)
    have e : 1 / (N : ℝ) ^ 3 * (N * (2 * N * M ^ 2)) = 2 * M ^ 2 / N := by field_simp
    linarith only [h1, e]
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ A ^ 2 * δ ^ 2)
  rw [hA] at h2 hint
  linarith only [hint, h2]

/-! ## Part 6: the conclusion, given the pair projection of `QT` (HYPOTHESIS) -/

/-- **`prop:variance` for every `k = n + 1`, CONDITIONAL.**  For independent uniform points,
    `N ≥ 1`, `0 ≤ δ ≤ 1/8`, `θ > 0`, and a number `R` with the
    HYPOTHESIS `Var(QT - U_k) ≤ R` (the pair projection of the polynomial statistic of
    `prop:bias` is `U_k` up to `R`; this is Steps 2–4 of the proof, NOT proved here for `k ≥ 3`):
    `Var U_k = v_k (N-1)/N³` exactly, `Var(Tr P^k - U_k) ≤ 2 E₁ + 2R` and
    `|Var Tr P^k - v_k (N-1)/N³| ≤ θ v_k (N-1)/N³ + (1 + 1/θ)(2 E₁ + 2R)`, with
    `E₁ = (gK δ m₁)² δ² (2m₁²/N) + (N + CQT)² P(max|ρ - 1| > δ)` from `trace_QT_sq`. -/
theorem variance_general_cond [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (n : ℕ) {θ : ℝ} (hθ : 0 < θ) {R : ℝ}
    (hR : cv μ (fun ω => QT d σ N n (fun j => X j ω) - Uk d σ (n + 1) X N ω) ≤ R) :
    cv μ (Uk d σ (n + 1) X N) = vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3
    ∧ cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace - Uk d σ (n + 1) X N ω)
        ≤ 2 * ((gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2
            * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ}) + 2 * R
    ∧ |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * (2 * ((gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2
            * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ}) + 2 * R) := by
  obtain ⟨bU, _, hcvU⟩ := Uk_var X h_indep hX hlaw hσ (n + 1) N
  obtain ⟨bT, _⟩ := trace_pow_bm hσ X hX N (n + 1)
  have bQ := QT_bm (μ := μ) hσ d X hX (N := N) (n := n)
  have hsq := trace_QT_sq X h_indep hX hlaw hσ N hN hδ0 hδ n
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = (gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2
      * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2
        * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  rw [← hE1] at hsq ⊢
  have bTQ : BM (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - QT d σ N n (fun j => X j ω)) := bT.sub bQ
  have bQU : BM (fun ω => QT d σ N n (fun j => X j ω) - Uk d σ (n + 1) X N ω) := bQ.sub bU
  have hTQ := cv_le_sq (μ := μ) bTQ
  have hg : cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - Uk d σ (n + 1) X N ω) ≤ 2 * E1 + 2 * R := by
    have e : (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - Uk d σ (n + 1) X N ω)
        = fun ω => (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - QT d σ N n (fun j => X j ω))
          + (QT d σ N n (fun j => X j ω) - Uk d σ (n + 1) X N ω) := by funext ω; ring
    rw [e]
    have := cv_add_le (μ := μ) bTQ bQU
    linarith only [this, hTQ, hsq, hR]
  refine ⟨hcvU, hg, ?_⟩
  have hper := cv_perturb (μ := μ) bU (bT.sub bU) hθ
  have e : (fun ω => Uk d σ (n + 1) X N ω + (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - Uk d σ (n + 1) X N ω)) = fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace := by
    funext ω; ring
  rw [e, hcvU] at hper
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left hg hθ'
  linarith only [hper, this]

end Step1

end VarianceGeneral

namespace VarianceGeneral2

open PiBound VarianceOne VarianceTwo

/-! # A104 (a): the Hoeffding decomposition of tuple statistics of any arity

For a bounded measurable kernel `F : (Fin n → G) → ℝ` and a probability measure `ν` on `G`:
* `Av ν v F` integrates out the coordinate `v`; `AW ν W F` integrates out the coordinates in `W`
  (well defined: the single integrations commute on bounded measurable functions, `Av_comm`).
* `hG ν F T = ∑_{S ⊆ T} (-1)^{|T|-|S|} AW ν Sᶜ F` (the Hoeffding component of `F` for the set `T`);
  `hG_sum`: `∑_T hG T = F`; `hG_deg`: `hG T` is degenerate in every coordinate of `T`.
* `hoeffding_var`: the statistic `N⁻ⁿ ∑_ι F(X_ι)` minus the same statistic of the low part
  `lowG F = ∑_{|T| ≤ 2} hG T` has variance `≤ 10 n⁶ 16ⁿ ‖F‖² / N³` (via `VarianceTwo.tstat_var`). -/

section Hoeffding

variable {G : Type*} [MeasurableSpace G] {ν : Measure G}

/-- Integrating out the coordinate `v`. -/
noncomputable def Av (ν : Measure G) {n : ℕ} (v : Fin n) (F : (Fin n → G) → ℝ)
    (x : Fin n → G) : ℝ :=
  ∫ z, F (Function.update x v z) ∂ν

theorem Av_bound [IsProbabilityMeasure ν] {n : ℕ} (v : Fin n) {F : (Fin n → G) → ℝ} {B : ℝ}
    (hB : ∀ x, |F x| ≤ B) (x : Fin n → G) : |Av ν v F x| ≤ B := by
  unfold Av
  have h := norm_integral_le_of_norm_le (μ := ν) (integrable_const B)
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hB (Function.update x v z))
  rw [Real.norm_eq_abs] at h
  simpa using h

theorem Av_bm [IsProbabilityMeasure ν] {n : ℕ} (v : Fin n) {F : (Fin n → G) → ℝ} (hF : BM F) :
    BM (Av ν v F) := by
  obtain ⟨B, hB⟩ := hF.bdd
  refine ⟨?_, B, Av_bound v hB⟩
  have hm : StronglyMeasurable (fun p : (Fin n → G) × G => F (Function.update p.1 v p.2)) :=
    (hF.meas.comp measurable_update').stronglyMeasurable
  exact (hm.integral_prod_right' (ν := ν)).measurable

theorem Av_update {n : ℕ} (v : Fin n) (F : (Fin n → G) → ℝ) (x : Fin n → G) (z : G) :
    Av ν v F (Function.update x v z) = Av ν v F x := by
  unfold Av; simp [Function.update_idem]

theorem upd2_meas {n : ℕ} (u v : Fin n) (x : Fin n → G) :
    Measurable (fun p : G × G => Function.update (Function.update x u p.1) v p.2) :=
  measurable_update'.comp
    (((measurable_update'.comp (measurable_const.prodMk measurable_fst))).prodMk measurable_snd)

/-- The single integrations commute on bounded measurable functions (Fubini). -/
theorem Av_comm [IsProbabilityMeasure ν] {n : ℕ} (u v : Fin n) {F : (Fin n → G) → ℝ}
    (hF : BM F) : Av ν u (Av ν v F) = Av ν v (Av ν u F) := by
  by_cases huv : u = v
  · subst huv; rfl
  funext x
  unfold Av
  have hb : BM (fun p : G × G => F (Function.update (Function.update x u p.1) v p.2)) :=
    ⟨hF.meas.comp (upd2_meas u v x), hF.bdd.imp fun _ h p => h _⟩
  have hi : Integrable (Function.uncurry fun (z w : G) =>
      F (Function.update (Function.update x u z) v w)) (ν.prod ν) := hb.integrable
  rw [integral_integral_swap hi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show F (Function.update (Function.update x u z) v w)
    = F (Function.update (Function.update x v w) u z)
  rw [Function.update_comm huv]

/-- Integrating out the coordinates of a list, in order. -/
noncomputable def Alist (ν : Measure G) {n : ℕ} (l : List (Fin n)) (F : (Fin n → G) → ℝ) :
    (Fin n → G) → ℝ :=
  l.foldr (fun v H => Av ν v H) F

theorem Alist_cons {n : ℕ} (v : Fin n) (l : List (Fin n)) (F : (Fin n → G) → ℝ) :
    Alist ν (v :: l) F = Av ν v (Alist ν l F) := rfl

theorem Alist_bm [IsProbabilityMeasure ν] {n : ℕ} (l : List (Fin n)) {F : (Fin n → G) → ℝ}
    (hF : BM F) : BM (Alist ν l F) := by
  induction l with
  | nil => exact hF
  | cons v l ih => rw [Alist_cons]; exact Av_bm v ih

theorem Alist_bound [IsProbabilityMeasure ν] {n : ℕ} (l : List (Fin n)) {F : (Fin n → G) → ℝ}
    {B : ℝ} (hB : ∀ x, |F x| ≤ B) : ∀ x, |Alist ν l F x| ≤ B := by
  induction l with
  | nil => exact hB
  | cons v l ih => rw [Alist_cons]; exact Av_bound v ih

theorem Alist_perm [IsProbabilityMeasure ν] {n : ℕ} {l₁ l₂ : List (Fin n)} (h : l₁.Perm l₂)
    {F : (Fin n → G) → ℝ} (hF : BM F) : Alist ν l₁ F = Alist ν l₂ F := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [Alist_cons, Alist_cons, ih]
  | swap x y l =>
    rw [Alist_cons, Alist_cons, Alist_cons, Alist_cons]
    exact Av_comm y x (Alist_bm l hF)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- Integrating out the coordinates in `W`. -/
noncomputable def AW (ν : Measure G) {n : ℕ} (W : Finset (Fin n)) (F : (Fin n → G) → ℝ) :
    (Fin n → G) → ℝ :=
  Alist ν W.toList F

theorem AW_bm [IsProbabilityMeasure ν] {n : ℕ} (W : Finset (Fin n)) {F : (Fin n → G) → ℝ}
    (hF : BM F) : BM (AW ν W F) := Alist_bm _ hF

theorem AW_bound [IsProbabilityMeasure ν] {n : ℕ} (W : Finset (Fin n)) {F : (Fin n → G) → ℝ}
    {B : ℝ} (hB : ∀ x, |F x| ≤ B) : ∀ x, |AW ν W F x| ≤ B := Alist_bound _ hB

theorem AW_empty {n : ℕ} (F : (Fin n → G) → ℝ) : AW ν (∅ : Finset (Fin n)) F = F := by
  unfold AW; rw [Finset.toList_empty]; rfl

theorem AW_insert [IsProbabilityMeasure ν] {n : ℕ} {v : Fin n} {W : Finset (Fin n)}
    (hv : v ∉ W) {F : (Fin n → G) → ℝ} (hF : BM F) :
    AW ν (insert v W) F = Av ν v (AW ν W F) := by
  unfold AW
  rw [Alist_perm (Finset.toList_insert hv) hF, Alist_cons]

theorem AW_update [IsProbabilityMeasure ν] {n : ℕ} {v : Fin n} {W : Finset (Fin n)}
    (hv : v ∈ W) {F : (Fin n → G) → ℝ} (hF : BM F) (x : Fin n → G) (z : G) :
    AW ν W F (Function.update x v z) = AW ν W F x := by
  have e : W = insert v (W.erase v) := (Finset.insert_erase hv).symm
  rw [e, AW_insert (Finset.notMem_erase v W) hF, Av_update]

theorem Av_AW_mem [IsProbabilityMeasure ν] {n : ℕ} {v : Fin n} {W : Finset (Fin n)}
    (hv : v ∈ W) {F : (Fin n → G) → ℝ} (hF : BM F) : Av ν v (AW ν W F) = AW ν W F := by
  funext x
  unfold Av
  simp_rw [AW_update hv hF x]
  simp

/-- The Hoeffding component `F_T = ∑_{S ⊆ T} (-1)^{|T|-|S|} E[F | x_S]`. -/
noncomputable def hG (ν : Measure G) {n : ℕ} (F : (Fin n → G) → ℝ) (T : Finset (Fin n))
    (x : Fin n → G) : ℝ :=
  ∑ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) * AW ν Sᶜ F x

theorem hG_bm [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F)
    (T : Finset (Fin n)) : BM (hG ν F T) :=
  BM.sum _ _ fun S _ => BM.const_mul _ (AW_bm _ hF)

theorem hG_bound [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin n → G) → ℝ} {B : ℝ}
    (hB : ∀ x, |F x| ≤ B) (T : Finset (Fin n)) (x : Fin n → G) :
    |hG ν F T x| ≤ 2 ^ n * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB x)
  unfold hG
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ S ∈ T.powerset, |(-1 : ℝ) ^ (T.card - S.card) * AW ν Sᶜ F x| ≤ B := fun S _ => by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]; exact AW_bound _ hB x
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
  have hT : T.card ≤ n := by simpa using Finset.card_le_univ T
  have : (2 : ℝ) ^ T.card ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hT
  push_cast
  exact mul_le_mul_of_nonneg_right this hB0

/-- **Möbius inversion on the subsets**: `∑_{T ⊆ U} ∑_{S ⊆ T} (-1)^{|T|-|S|} a(S) = a(U)`. -/
theorem mobius {α : Type*} [DecidableEq α] (U : Finset α) :
    ∀ a : Finset α → ℝ,
      ∑ T ∈ U.powerset, ∑ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) * a S = a U := by
  induction U using Finset.induction_on with
  | empty => intro a; simp
  | insert u U hu ih =>
    intro a
    rw [Finset.sum_powerset_insert hu]
    have e : ∀ T ∈ U.powerset, ∑ S ∈ (insert u T).powerset,
        (-1 : ℝ) ^ ((insert u T).card - S.card) * a S
        = -(∑ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) * a S)
          + ∑ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) * a (insert u S) := by
      intro T hT
      have huT : u ∉ T := fun h => hu (Finset.mem_powerset.mp hT h)
      rw [Finset.sum_powerset_insert huT, Finset.card_insert_of_notMem huT, ← Finset.sum_neg_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun S hS => ?_
        have hST : S.card ≤ T.card := Finset.card_le_card (Finset.mem_powerset.mp hS)
        rw [show T.card + 1 - S.card = (T.card - S.card) + 1 by omega, pow_succ]
        ring
      · refine Finset.sum_congr rfl fun S hS => ?_
        have huS : u ∉ S := fun h => huT (Finset.mem_powerset.mp hS h)
        rw [Finset.card_insert_of_notMem huS]
        congr 2
        omega
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_neg_distrib, ih a,
      ih (fun S => a (insert u S))]
    ring

/-- **`∑_T F_T = F`.** -/
theorem hG_sum {n : ℕ} (F : (Fin n → G) → ℝ) (x : Fin n → G) :
    ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset, hG ν F T x = F x := by
  unfold hG
  rw [mobius Finset.univ (fun S => AW ν Sᶜ F x), Finset.compl_univ, AW_empty]

/-- **`F_T` is degenerate in every coordinate of `T`.** -/
theorem hG_deg [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F)
    {T : Finset (Fin n)} {v : Fin n} (hv : v ∈ T) (x : Fin n → G) :
    ∫ z, hG ν F T (Function.update x v z) ∂ν = 0 := by
  have hbm : ∀ S : Finset (Fin n), Integrable (fun z => AW ν Sᶜ F (Function.update x v z)) ν :=
    fun S => (⟨(AW_bm Sᶜ hF).meas.comp (measurable_update x),
      (AW_bm Sᶜ hF).bdd.imp fun _ h z => h _⟩ : BM fun z => AW ν Sᶜ F (Function.update x v z)).integrable
  unfold hG
  rw [integral_finset_sum _ fun S _ => (hbm S).const_mul _]
  simp_rw [integral_const_mul]
  have hA : ∀ S : Finset (Fin n), ∫ z, AW ν Sᶜ F (Function.update x v z) ∂ν
      = Av ν v (AW ν Sᶜ F) x := fun S => rfl
  simp_rw [hA]
  have e : T = insert v (T.erase v) := (Finset.insert_erase hv).symm
  rw [e, Finset.sum_powerset_insert (Finset.notMem_erase v T)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun S hS => ?_
  have hvS : v ∉ S := fun h => Finset.notMem_erase v T (Finset.mem_powerset.mp hS h)
  have hST : S.card ≤ (T.erase v).card := Finset.card_le_card (Finset.mem_powerset.mp hS)
  have h1 : Av ν v (AW ν Sᶜ F) = AW ν Sᶜ F :=
    Av_AW_mem (Finset.mem_compl.mpr hvS) hF
  have hc : (insert v S)ᶜ = Sᶜ.erase v := by
    ext w; simp [Finset.mem_compl, Finset.mem_erase]
  have h2 : Av ν v (AW ν (insert v S)ᶜ F) = AW ν Sᶜ F := by
    rw [hc, ← AW_insert (Finset.notMem_erase v _) hF, Finset.insert_erase
      (Finset.mem_compl.mpr hvS)]
  rw [h1, h2, Finset.card_insert_of_notMem (Finset.notMem_erase v T),
    Finset.card_insert_of_notMem hvS,
    show (T.erase v).card + 1 - S.card = ((T.erase v).card - S.card) + 1 by omega,
    show (T.erase v).card + 1 - (S.card + 1) = (T.erase v).card - S.card by omega, pow_succ]
  ring

/-- The low part `∑_{|T| ≤ 2} F_T`. -/
noncomputable def lowG (ν : Measure G) {n : ℕ} (F : (Fin n → G) → ℝ) (x : Fin n → G) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun T => T.card ≤ 2), hG ν F T x

/-- The high part `∑_{|T| ≥ 3} F_T`. -/
noncomputable def highG (ν : Measure G) {n : ℕ} (F : (Fin n → G) → ℝ) (x : Fin n → G) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun T => ¬ T.card ≤ 2), hG ν F T x

theorem low_add_high {n : ℕ} (F : (Fin n → G) → ℝ) (x : Fin n → G) :
    lowG ν F x + highG ν F x = F x := by
  unfold lowG highG
  rw [Finset.sum_filter_add_sum_filter_not, hG_sum]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ℕ → Ω → G}

omit [MeasurableSpace G] in
theorem sAll_fsum {κ : Type*} (X : ℕ → Ω → G) (N : ℕ) {n : ℕ} (s : Finset κ)
    (f : κ → (Fin n → G) → ℝ) (ω : Ω) :
    sAll X N (fun x => ∑ T ∈ s, f T x) ω = ∑ T ∈ s, sAll X N (f T) ω := by
  unfold sAll; exact Finset.sum_comm

/-- **(a) The variance of the part of order `≥ 3`.** For an independent sample with law `ν`,
    `N ≥ 1` and a bounded measurable kernel `F` (`|F| ≤ B`):
    `Var(N⁻ⁿ ∑_ι F(X_ι) - N⁻ⁿ ∑_ι lowG F(X_ι)) ≤ 10 n⁶ 16ⁿ B² / N³`. -/
theorem hoeffding_var [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (H : SP μ ν X)
    {N : ℕ} (hN : 0 < N) {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) {B : ℝ}
    (hB : ∀ x, |F x| ≤ B) :
    cv μ (fun ω => 1 / (N : ℝ) ^ n * sAll X N F ω - 1 / (N : ℝ) ^ n * sAll X N (lowG ν F) ω)
      ≤ 10 * (n : ℝ) ^ 6 * 16 ^ n * B ^ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨s, hs⟩ : ∃ s : Finset (Finset (Fin n)), s
      = (Finset.univ : Finset (Fin n)).powerset.filter (fun T => ¬ T.card ≤ 2) := ⟨_, rfl⟩
  have e : (fun ω => 1 / (N : ℝ) ^ n * sAll X N F ω - 1 / (N : ℝ) ^ n * sAll X N (lowG ν F) ω)
      = fun ω => ∑ T ∈ s, 1 / (N : ℝ) ^ n * sAll X N (hG ν F T) ω := by
    funext ω
    have hsplit : sAll X N F ω = sAll X N (lowG ν F) ω + sAll X N (highG ν F) ω := by
      rw [← sAll_add]
      exact congrArg (fun f => sAll X N f ω) (funext fun x => (low_add_high F x).symm)
    rw [hsplit, ← Finset.mul_sum, hs]
    unfold highG
    rw [sAll_fsum]
    ring
  rw [e]
  have hbm : ∀ T, BM (fun ω => 1 / (N : ℝ) ^ n * sAll X N (hG ν F T) ω) := fun T =>
    BM.const_mul _ (H.sAll_bm N (hG_bm hF T))
  have h1 := cv_sum_le (μ := μ) s (fun T ω => 1 / (N : ℝ) ^ n * sAll X N (hG ν F T) ω) hbm
  have hc : ∀ T ∈ s, cv μ (fun ω => 1 / (N : ℝ) ^ n * sAll X N (hG ν F T) ω)
      ≤ 10 * (n : ℝ) ^ 6 * (2 ^ n * B) ^ 2 / (N : ℝ) ^ 3 := by
    intro T hT
    rw [hs, Finset.mem_filter] at hT
    have h3 : 3 ≤ T.card := by omega
    obtain ⟨D, hDT, hD⟩ := Finset.exists_subset_card_eq h3
    have hn : 3 ≤ n := by
      have := Finset.card_le_univ T; simp at this; omega
    exact tstat_var H hN hn (hG ν F T) (hG_bm hF T) (hG_bound hB T) D hD
      (fun v hv x => hG_deg hF (hDT hv) x)
  have hsc : (s.card : ℝ) ≤ 2 ^ n := by
    have : s.card ≤ ((Finset.univ : Finset (Fin n)).powerset).card := by
      rw [hs]; exact Finset.card_filter_le _ _
    rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have h2 : ∑ T ∈ s, cv μ (fun ω => 1 / (N : ℝ) ^ n * sAll X N (hG ν F T) ω)
      ≤ s.card * (10 * (n : ℝ) ^ 6 * (2 ^ n * B) ^ 2 / (N : ℝ) ^ 3) := by
    have := Finset.sum_le_sum hc
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hq : 0 ≤ 10 * (n : ℝ) ^ 6 * (2 ^ n * B) ^ 2 / (N : ℝ) ^ 3 := by positivity
  have h3 : (s.card : ℝ) * (s.card * (10 * (n : ℝ) ^ 6 * (2 ^ n * B) ^ 2 / (N : ℝ) ^ 3))
      ≤ 2 ^ n * (2 ^ n * (10 * (n : ℝ) ^ 6 * (2 ^ n * B) ^ 2 / (N : ℝ) ^ 3)) := by
    have hs0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
    exact mul_le_mul hsc (mul_le_mul_of_nonneg_right hsc hq) (by positivity) (by positivity)
  have e2 : (2 : ℝ) ^ n * (2 ^ n * (10 * (n : ℝ) ^ 6 * (2 ^ n * B) ^ 2 / (N : ℝ) ^ 3))
      = 10 * (n : ℝ) ^ 6 * 16 ^ n * B ^ 2 / (N : ℝ) ^ 3 := by
    rw [show (16 : ℝ) ^ n = 2 ^ n * 2 ^ n * (2 ^ n * 2 ^ n) by
      rw [show (16 : ℝ) = 2 * 2 * (2 * 2) by norm_num, mul_pow, mul_pow]]
    ring
  have h4 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg s.card)
  linarith only [h1, h4, h3, e2]

end Hoeffding


/-! ## A104 (c), generic part: the pair projection of a translation-invariant statistic

`G` an additive group, `ν` translation invariant (HYPOTHESIS `hinv`, discharged on the flat torus
in `torus_hinv`), `F` translation invariant (`TI F`: `F(x + c) = F(x)`).  Then the components of
order one vanish, and the low part is `c₀ + ∑_{|T| = 2} (I_T(x_α - x_β) - c₀)`. -/

section Pairs

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] {ν : Measure G}

/-- Translation invariance of a kernel. -/
def TI {n : ℕ} (F : (Fin n → G) → ℝ) : Prop := ∀ (x : Fin n → G) (c : G), F (fun i => x i + c) = F x

theorem update_shift {n : ℕ} (x : Fin n → G) (v : Fin n) (z c : G) :
    Function.update (fun i => x i + c) v (z + c) = fun i => Function.update x v z i + c := by
  funext i
  by_cases h : i = v
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem Av_TI (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {n : ℕ} (v : Fin n) {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F) : TI (Av ν v F) := by
  intro x c
  unfold Av
  have hm : Measurable (fun z => F (Function.update (fun i => x i + c) v z)) :=
    hF.meas.comp (measurable_update _)
  rw [← hinv _ hm c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show F (Function.update (fun i => x i + c) v (z + c)) = F (Function.update x v z)
  rw [update_shift, hT]

theorem Alist_TI [IsProbabilityMeasure ν]
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {n : ℕ} (l : List (Fin n)) {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F) :
    TI (Alist ν l F) := by
  induction l with
  | nil => exact hT
  | cons v l ih => rw [Alist_cons]; exact Av_TI hinv v (Alist_bm l hF) ih

theorem AW_TI [IsProbabilityMeasure ν]
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {n : ℕ} (W : Finset (Fin n)) {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F) :
    TI (AW ν W F) := Alist_TI hinv _ hF hT

/-- A function invariant under updates at the coordinates of `W` depends only on the others. -/
theorem off_eq {n : ℕ} (H : (Fin n → G) → ℝ) (W : Finset (Fin n))
    (hW : ∀ w ∈ W, ∀ x z, H (Function.update x w z) = H x) :
    ∀ x y : Fin n → G, (∀ i, i ∉ W → x i = y i) → H x = H y := by
  induction W using Finset.induction_on with
  | empty =>
    intro x y h
    congr 1; funext i; exact h i (Finset.notMem_empty i)
  | insert w W hw ih =>
    intro x y h
    have hW' : ∀ w' ∈ W, ∀ x z, H (Function.update x w' z) = H x :=
      fun w' hw' => hW w' (Finset.mem_insert_of_mem hw')
    rw [← hW w (Finset.mem_insert_self w W) x (y w)]
    refine ih hW' _ _ fun i hi => ?_
    by_cases hiw : i = w
    · subst hiw; simp
    · rw [Function.update_of_ne hiw]
      exact h i (by simp [hiw, hi])

theorem AW_off [IsProbabilityMeasure ν] {n : ℕ} (W : Finset (Fin n)) {F : (Fin n → G) → ℝ}
    (hF : BM F) : ∀ x y : Fin n → G, (∀ i, i ∉ W → x i = y i) → AW ν W F x = AW ν W F y :=
  off_eq _ W fun _ hw x z => AW_update hw hF x z

variable [IsProbabilityMeasure ν]
  (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
include hinv

/-- `E[F | x_v]` is constant: `AW {v}ᶜ F = c₀`. -/
theorem AW_le1_const {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F)
    {S : Finset (Fin n)} (hS : S.card ≤ 1) (x : Fin n → G) :
    AW ν Sᶜ F x = AW ν Finset.univ F 0 := by
  have hTI := AW_TI hinv Sᶜ hF hT
  by_cases hSe : S = ∅
  · subst hSe
    simp only [Finset.compl_empty]
    exact AW_off _ hF _ _ fun i hi => absurd (Finset.mem_univ i) hi
  obtain ⟨v, hvS⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  have hv : ∀ i ∈ S, i = v := fun i hi => Finset.card_le_one.mp hS i hi v hvS
  have h1 : AW ν Sᶜ F x = AW ν Sᶜ F (fun i => x i + -x v) := (hTI x (-x v)).symm
  have h2 : AW ν Sᶜ F (fun i => x i + -x v) = AW ν Sᶜ F 0 := by
    refine AW_off Sᶜ hF _ _ fun i hi => ?_
    have hiS : i ∈ S := by simpa using hi
    have : i = v := hv i hiS
    subst this; simp
  rw [h1, h2]
  have hvc : v ∉ Sᶜ := by simpa using hvS
  have hu : (Finset.univ : Finset (Fin n)) = insert v Sᶜ := by
    ext i; by_cases hi : i = v
    · subst hi; simp
    · have : i ∉ S := fun h => hi (hv i h)
      simp [this]
  rw [hu, AW_insert hvc hF]
  unfold Av
  have hc : ∀ z, AW ν Sᶜ F (Function.update 0 v z) = AW ν Sᶜ F 0 := fun z => by
    have := hTI (Function.update 0 v z) (-z)
    rw [← this]
    refine AW_off Sᶜ hF _ _ fun i hi => ?_
    have hiS : i ∈ S := by simpa using hi
    have : i = v := hv i hiS
    subst this; simp
  simp_rw [hc]
  simp

omit hinv in
theorem alt_sum_zero {n : ℕ} {T : Finset (Fin n)} (hT : T.Nonempty) :
    ∑ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) = 0 := by
  have h : ∑ S ∈ T.powerset, (-1 : ℤ) ^ S.card = 0 := by
    rw [Finset.sum_powerset_neg_one_pow_card, if_neg hT.ne_empty]
  have e : ∀ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) = (-1) ^ T.card * ((-1 : ℤ) ^ S.card : ℤ) := by
    intro S hS
    have hST : S.card ≤ T.card := Finset.card_le_card (Finset.mem_powerset.mp hS)
    push_cast
    have : (-1 : ℝ) ^ T.card = (-1) ^ (T.card - S.card) * (-1) ^ S.card := by
      rw [← pow_add]; congr 1; omega
    rw [this, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  have h' : (∑ S ∈ T.powerset, (((-1 : ℤ) ^ S.card : ℤ) : ℝ)) = 0 := by exact_mod_cast h
  rw [h', mul_zero]

/-- **The components of order `≤ 2`**: `F_T = AW Tᶜ F - c₀` for `1 ≤ |T| ≤ 2` (and `F_∅ = c₀`),
    with `c₀ = E F`; for `|T| = 1` this is zero. -/
theorem hG_low {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F) {T : Finset (Fin n)}
    (hT1 : T.Nonempty) (hT2 : T.card ≤ 2) (x : Fin n → G) :
    hG ν F T x = AW ν Tᶜ F x - AW ν Finset.univ F 0 := by
  unfold hG
  obtain ⟨c, hc⟩ : ∃ c, c = AW ν Finset.univ F 0 := ⟨_, rfl⟩
  rw [← hc]
  have e : ∀ S ∈ T.powerset, (-1 : ℝ) ^ (T.card - S.card) * AW ν Sᶜ F x
      = (-1 : ℝ) ^ (T.card - S.card) * (AW ν Sᶜ F x - c) + (-1 : ℝ) ^ (T.card - S.card) * c :=
    fun S _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.sum_mul, alt_sum_zero hT1, zero_mul,
    add_zero, ← Finset.add_sum_erase _ _ (Finset.mem_powerset_self T), Nat.sub_self, pow_zero,
    one_mul]
  have hz : ∑ S ∈ T.powerset.erase T, (-1 : ℝ) ^ (T.card - S.card) * (AW ν Sᶜ F x - c) = 0 := by
    refine Finset.sum_eq_zero fun S hS => ?_
    have hS' := Finset.mem_erase.mp hS
    have hsub : S ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hS'.2, hS'.1⟩
    have hc1 : S.card ≤ 1 := by have := Finset.card_lt_card hsub; omega
    rw [hc, AW_le1_const hinv hF hT hc1 x, sub_self, mul_zero]
  rw [hz, add_zero]

theorem hG_empty_eq {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F) (x : Fin n → G) :
    hG ν F ∅ x = AW ν Finset.univ F 0 := by
  unfold hG
  simp only [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, Nat.sub_self,
    pow_zero, one_mul, Finset.compl_empty]
  exact AW_off _ hF _ _ fun i hi => absurd (Finset.mem_univ i) hi

theorem hG_one_eq {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F) {T : Finset (Fin n)}
    (hT1 : T.card = 1) (x : Fin n → G) : hG ν F T x = 0 := by
  rw [hG_low hinv hF hT (Finset.card_pos.mp (by omega)) (by omega),
    AW_le1_const hinv hF hT (by omega) x, sub_self]

end Pairs


/-! ### counting tuples with two prescribed coordinates -/

theorem count_card {N n : ℕ} {α β : Fin n} (h : α ≠ β) (i j : Fin N) :
    ((Finset.univ : Finset (Fin n → Fin N)).filter (fun ι => (ι α, ι β) = (i, j))).card
      = N ^ (n - 2) := by
  classical
  have e : (Finset.univ : Finset (Fin n → Fin N)).filter (fun ι => (ι α, ι β) = (i, j))
      = Fintype.piFinset (fun k => if k = α then {i} else if k = β then {j} else Finset.univ) := by
    ext ι
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = α
      · subst hk; simp [h1]
      · by_cases hk' : k = β
        · subst hk'; simp [hk, h2]
        · simp [hk, hk']
    · intro hk
      have h1 := hk α
      have h2 := hk β
      simp at h1
      simp only [if_neg (Ne.symm h)] at h2
      simp at h2
      exact ⟨h1, h2⟩
  rw [e, Fintype.card_piFinset]
  have hc : ∀ k, (if k = α then ({i} : Finset (Fin N)) else if k = β then {j} else Finset.univ).card
      = if k ∈ ({α, β} : Finset (Fin n)) then 1 else N := by
    intro k
    by_cases hk : k = α
    · subst hk; simp
    · by_cases hk' : k = β
      · subst hk'; simp [hk]
      · simp [hk, hk']
  simp_rw [hc]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter (fun k => k ∉ ({α, β} : Finset (Fin n)))) = ({α, β} : Finset (Fin n))ᶜ := by
    ext k; simp
  rw [this, Finset.card_compl, Fintype.card_fin, Finset.card_pair h]

theorem count_pair {N n : ℕ} {α β : Fin n} (h : α ≠ β) (g : Fin N → Fin N → ℝ) :
    ∑ ι : Fin n → Fin N, g (ι α) (ι β) = (N : ℝ) ^ (n - 2) * ∑ i : Fin N, ∑ j : Fin N, g i j := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin n → Fin N)) (fun ι => (ι α, ι β))
    (fun ι => g (ι α) (ι β))]
  have e : ∀ p : Fin N × Fin N, ∑ ι ∈ (Finset.univ : Finset (Fin n → Fin N)).filter
      (fun ι => (ι α, ι β) = p), g (ι α) (ι β) = (N : ℝ) ^ (n - 2) * g p.1 p.2 := by
    intro p
    rw [Finset.sum_congr rfl (g := fun _ => g p.1 p.2) (fun ι hι => by
      have := (Finset.mem_filter.mp hι).2
      rw [Prod.ext_iff] at this
      simp only at this
      rw [this.1, this.2])]
    rw [Finset.sum_const, nsmul_eq_mul, count_card h p.1 p.2]
    push_cast; ring
  rw [Finset.sum_congr rfl fun p _ => e p, ← Finset.mul_sum, Fintype.sum_prod_type]

/-! ### the pair kernel and the low statistic -/

section PairStat

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] {ν : Measure G}

/-- Ordered pairs `α < β` of positions. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2)

/-- **The pair kernel of a statistic**: `h_F(y) = ∑_{α<β} (I_{αβ}(y) - c₀)`,
    `I_{αβ}(y) = E[F | x_α - x_β = y]` (the integral over all positions except `α, β`, at the point
    `x_α = y`, `x_β = 0`), `c₀ = E F`. -/
noncomputable def hpair (ν : Measure G) {n : ℕ} (F : (Fin n → G) → ℝ) (y : G) : ℝ :=
  ∑ p ∈ pairs n, (AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F (Function.update 0 p.1 y)
    - AW ν Finset.univ F 0)

theorem lowG_pairs [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin n → G) → ℝ} (x : Fin n → G)
    (hF : BM F) (hT : TI F)
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν) :
    lowG ν F x = AW ν Finset.univ F 0
      + ∑ p ∈ pairs n, (AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F
          (Function.update 0 p.1 (x p.1 - x p.2)) - AW ν Finset.univ F 0) := by
  classical
  unfold lowG
  -- split off `T = ∅`, the singletons, and the pairs
  have hsplit : (Finset.univ : Finset (Fin n)).powerset.filter (fun T => T.card ≤ 2)
      = insert ∅ ((Finset.univ : Finset (Fin n)).powerset.filter (fun T => 1 ≤ T.card ∧ T.card ≤ 2)) := by
    ext T; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hT0 : T = ∅
      · exact Or.inl hT0
      · exact Or.inr ⟨h1, Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hT0), h2⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · subst h; simp
      · exact ⟨h1, h3⟩
  have hne : (∅ : Finset (Fin n)) ∉ (Finset.univ : Finset (Fin n)).powerset.filter
      (fun T => 1 ≤ T.card ∧ T.card ≤ 2) := by simp
  rw [hsplit, Finset.sum_insert hne, hG_empty_eq hinv hF hT]
  congr 1
  rw [Finset.sum_filter]
  have e1 : ∀ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      (if 1 ≤ T.card ∧ T.card ≤ 2 then hG ν F T x else 0)
        = if T.card = 2 then AW ν Tᶜ F x - AW ν Finset.univ F 0 else 0 := by
    intro T _
    by_cases h2 : T.card = 2
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h2,
        hG_low hinv hF hT (Finset.card_pos.mp (by omega)) (by omega)]
    · rw [if_neg h2]
      by_cases h1 : 1 ≤ T.card ∧ T.card ≤ 2
      · rw [if_pos h1, hG_one_eq hinv hF hT (by omega)]
      · rw [if_neg h1]
  rw [Finset.sum_congr rfl e1, ← Finset.sum_filter]
  -- reindex the two-element sets by ordered pairs
  symm
  refine Finset.sum_bij (fun p _ => ({p.1, p.2} : Finset (Fin n))) ?_ ?_ ?_ ?_
  · intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    simp [Finset.card_pair hlt.ne]
  · intro p hp q hq hpq
    simp only at hpq
    have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hq' : q.1 < q.2 := (Finset.mem_filter.mp hq).2
    have h1 : p.1 ∈ ({q.1, q.2} : Finset (Fin n)) := by rw [← hpq]; simp
    have h2 : p.2 ∈ ({q.1, q.2} : Finset (Fin n)) := by rw [← hpq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1, h2] at hp'; exact absurd hp' (lt_irrefl _)
    · exact Prod.ext h1 h2
    · rw [h1, h2] at hp'; exact absurd hp' (lt_asymm hq')
    · rw [h1, h2] at hp'; exact absurd hp' (lt_irrefl _)
  · intro T hT
    have hT2 : T.card = 2 := (Finset.mem_filter.mp hT).2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT2
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
    · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, Finset.pair_comm b a⟩
  · intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    congr 1
    have hTI := AW_TI hinv ({p.1, p.2} : Finset (Fin n))ᶜ hF hT
    rw [← hTI x (-x p.2)]
    refine AW_off _ hF _ _ fun i hi => ?_
    have hi' : i = p.1 ∨ i = p.2 := by
      by_contra hc
      push_neg at hc
      exact hi (by simp [hc.1, hc.2])
    rcases hi' with h | h
    · subst h; simp [sub_eq_add_neg]
    · subst h; simp [Function.update_of_ne hlt.ne', add_neg_cancel]


theorem lowG_stat [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (hT : TI F)
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {Ω : Type*} (X : ℕ → Ω → G) {N : ℕ} (hN : 0 < N) (ω : Ω) :
    1 / (N : ℝ) ^ n * sAll X N (lowG ν F) ω
      = AW ν Finset.univ F 0
        + 1 / (N : ℝ) ^ 2 * ∑ i : Fin N, ∑ j : Fin N, hpair ν F (X i ω - X j ω) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨c, hc⟩ : ∃ c, c = AW ν Finset.univ F 0 := ⟨_, rfl⟩
  obtain ⟨Gp, hGp⟩ : ∃ Gp : Fin n × Fin n → Fin N → Fin N → ℝ, Gp = fun (p : Fin n × Fin n) (i j : Fin N) =>
      AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F (Function.update 0 p.1 (X i ω - X j ω)) - c :=
    ⟨_, rfl⟩
  have hL : sAll X N (lowG ν F) ω
      = (N : ℝ) ^ n * c + ∑ p ∈ pairs n, (N : ℝ) ^ (n - 2) * ∑ i : Fin N, ∑ j : Fin N, Gp p i j := by
    unfold sAll
    simp_rw [lowG_pairs _ hF hT hinv]
    rw [← hc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, Finset.sum_comm]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.ne
    rw [hGp]
    exact count_pair hne (fun i j => AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F
      (Function.update 0 p.1 (X i ω - X j ω)) - c)
  have hR : ∑ i : Fin N, ∑ j : Fin N, hpair ν F (X i ω - X j ω)
      = ∑ p ∈ pairs n, ∑ i : Fin N, ∑ j : Fin N, Gp p i j := by
    rw [hGp]
    unfold hpair
    rw [← hc]
    rw [Finset.sum_congr rfl fun (i : Fin N) _ => Finset.sum_comm]
    exact Finset.sum_comm
  rw [hL, hR, ← hc, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · field_simp
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hn2 : 2 ≤ n := by
      have h1 : (p.1 : ℕ) < p.2 := (Finset.mem_filter.mp hp).2
      have h2 : (p.2 : ℕ) < n := p.2.isLt
      omega
    have e : (N : ℝ) ^ n = (N : ℝ) ^ (n - 2) * (N : ℝ) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    field_simp

/-- **(c), generic: the pair projection of a translation-invariant statistic of any arity.**
    For an independent sample with a translation-invariant law `ν` (HYPOTHESIS `hinv`), `N ≥ 1`
    and a bounded (`|F| ≤ B`), measurable, translation-invariant kernel `F`:
    `Var(N⁻ⁿ ∑_ι F(X_ι) - N⁻² ∑_{i≠j} h_F(X_i - X_j)) ≤ 10 n⁶ 16ⁿ B² / N³`,
    with the pair kernel `h_F = hpair ν F`. -/
theorem pair_projection {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : ℕ → Ω → G} (H : SP μ ν X)
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {N : ℕ} (hN : 0 < N) {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) {B : ℝ}
    (hB : ∀ x, |F x| ≤ B) (hT : TI F) :
    cv μ (fun ω => 1 / (N : ℝ) ^ n * sAll X N F ω - 1 / (N : ℝ) ^ 2 * Soff (hpair ν F) X N ω)
      ≤ 10 * (n : ℝ) ^ 6 * 16 ^ n * B ^ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := hoeffding_var H hN hF hB
  have e : (fun ω => 1 / (N : ℝ) ^ n * sAll X N F ω - 1 / (N : ℝ) ^ 2 * Soff (hpair ν F) X N ω)
      = fun ω => (1 / (N : ℝ) ^ n * sAll X N F ω - 1 / (N : ℝ) ^ n * sAll X N (lowG ν F) ω)
        + (AW ν Finset.univ F 0 + hpair ν F 0 / N) := by
    funext ω
    rw [lowG_stat hF hT hinv X hN ω, pair_eq_soff]
    field_simp
    ring
  have bL : BM (lowG ν F) := BM.sum _ _ fun T _ => hG_bm hF T
  rw [e, cv_add_const ((BM.const_mul _ (H.sAll_bm N hF)).sub (BM.const_mul _ (H.sAll_bm N bL)))]
  exact h

end PairStat

/-- The HYPOTHESIS `hinv` holds on the flat torus. -/
theorem torus_hinv (d : ℕ) (f : FlatTorus d → ℝ) (hf : Measurable f) (c : FlatTorus d) :
    ∫ z, f (z + c) ∂flatTorusMeasure d = ∫ z, f z ∂flatTorusMeasure d := by
  have h1 := VarianceGeneral.neg_inv_int d (fun z => f (z + c))
  simp only at h1
  rw [← h1]
  haveI : (flatTorusMeasure d).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular (flatTorusMeasure d)
  have e : ∀ z : FlatTorus d, f (-z + c) = f (c - z) := fun z => by rw [neg_add_eq_sub]
  simp_rw [e]
  exact integral_sub_left_eq_self f (flatTorusMeasure d) c

end VarianceGeneral2

namespace BiasNoLoops

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 BiasGeneral6
  PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance4 NoLoops

/-! # A103: `prop:bias` for the graph WITHOUT self-loops (`ρ = 0`), every `k ≥ 2`

Route: comparison of the walk without self-loops `P°` with the walk with self-loops `P`.
Both traces are expanded with `trace_expansion` (which needs only a symmetric kernel with values
in `[0, M]`, so it applies to the kernel with zero diagonal); the two polynomial statistics differ
by `Tr P̃°^k - Tr P̃^k + k c Tr P̃^k` up to `O(c δ)`, `c = m₁/N`; `P̃° = P̃ - c·1`, so the first
difference is a binomial sum. -/

section Det

/-- Removing the diagonal from a row sum. -/
theorem sum_offdiag {N : ℕ} (K K' : Fin N → Fin N → ℝ) (hK' : ∀ i j, K' i j = if i = j then 0 else K i j)
    (f : Fin N → ℝ) (i : Fin N) :
    ∑ l, K' i l * f l = ∑ l, K i l * f l - K i i * f i := by
  have h : ∀ l, K' i l * f l = K i l * f l - (if i = l then K i l * f l else 0) := by
    intro l; rw [hK']; split_ifs with h <;> simp [h]
  rw [Finset.sum_congr rfl fun l _ => h l, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  simp

set_option maxHeartbeats 1000000 in
/-- The vertex bounds: `φ¹ = -2e + b`, `φ¹° = -2(e-c) + b°`, `φ²`, `φ²°` with `b° = b - c(1+e) - c(e-c)`,
    `s° = s - 2cb + c²(1+e) - c(e-c)²`. -/
theorem vertex_alg {e b s c δ u b0 s0 : ℝ} (hc : 0 ≤ c) (hδ0 : 0 ≤ δ) (hδc : δ + c ≤ u)
    (hu : u ≤ 1 / 8) (he : |e| ≤ δ) (hb : |b| ≤ 9 / 8 * δ)
    (hb0 : b0 = b - c * (1 + e) - c * (e - c))
    (hs0 : s0 = s - 2 * c * b + c ^ 2 * (1 + e) - c * (e - c) ^ 2)
    (hb0b : |b0| ≤ 9 / 8 * u) (hs0n : 0 ≤ s0) (hs0b : s0 ≤ 9 / 8 * u ^ 2) :
    |-2 * e + b| ≤ 4 * u
    ∧ |-2 * (e - c) + b0| ≤ 4 * u
    ∧ |3 * (e - c) ^ 2 - 3 * (e - c) * b0 + b0 ^ 2 - s0| ≤ 2 * u
    ∧ |(-2 * (e - c) + b0) - (-2 * e + b)| ≤ 2 * c
    ∧ |((-2 * (e - c) + b0) + (3 * (e - c) ^ 2 - 3 * (e - c) * b0 + b0 ^ 2 - s0))
        - ((-2 * e + b) + (3 * e ^ 2 - 3 * e * b + b ^ 2 - s)) - c| ≤ 50 * c * u := by
  obtain ⟨e1, e2⟩ := abs_le.mp he
  obtain ⟨b1, b2⟩ := abs_le.mp hb
  obtain ⟨d1, d2⟩ := abs_le.mp hb0b
  have hu0 : 0 ≤ u := by linarith
  have hcu : c ≤ u := by linarith
  have heu : |e| ≤ u := he.trans (by linarith)
  have hbu : |b| ≤ 2 * u := hb.trans (by linarith)
  have hecu : |e - c| ≤ u := by rw [abs_le]; constructor <;> linarith
  have huu : u * u ≤ u * (1 / 8) := mul_le_mul_of_nonneg_left hu hu0
  have hcuu : c * u ≤ c * (1 / 8) := mul_le_mul_of_nonneg_left hu hc
  have hcc : c * c ≤ c * u := mul_le_mul_of_nonneg_left hcu hc
  have hce : |c * e| ≤ c * u := by
    rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left heu hc
  obtain ⟨ce1, ce2⟩ := abs_le.mp hce
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · obtain ⟨f1, f2⟩ := abs_le.mp hecu
    rw [abs_le]; constructor <;> linarith
  · have q1 : (e - c) ^ 2 ≤ u ^ 2 := sq_le_sq' (abs_le.mp hecu).1 (abs_le.mp hecu).2
    have q2 : |(e - c) * b0| ≤ u * (9 / 8 * u) := by
      rw [abs_mul]; exact mul_le_mul hecu hb0b (abs_nonneg _) hu0
    have q3 : b0 ^ 2 ≤ (9 / 8 * u) ^ 2 := sq_le_sq' d1 d2
    have q0 : 0 ≤ (e - c) ^ 2 := _root_.sq_nonneg _
    have q4 : 0 ≤ b0 ^ 2 := _root_.sq_nonneg _
    obtain ⟨r1, r2⟩ := abs_le.mp q2
    rw [abs_le]; constructor <;> linarith
  · have hc0' : 0 ≤ c * c := mul_self_nonneg c
    rw [hb0, abs_le]; constructor <;> linarith
  · obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = c * (1 + 2 * e - c) := ⟨_, rfl⟩
    have hb0' : b0 = b - β := by rw [hb0, hβ]; ring
    have hβ0 : 0 ≤ β := by rw [hβ]; exact mul_nonneg hc (by linarith)
    have hβ2 : β ≤ 2 * c := by
      rw [hβ]
      have : 1 + 2 * e - c ≤ 2 := by linarith
      have := mul_le_mul_of_nonneg_left this hc
      linarith
    have key : ((-2 * (e - c) + b0) + (3 * (e - c) ^ 2 - 3 * (e - c) * b0 + b0 ^ 2 - s0))
        - ((-2 * e + b) + (3 * e ^ 2 - 3 * e * b + b ^ 2 - s)) - c
        = (c - β) + 3 * (c * c) - 6 * (c * e) + 3 * (e * β) + 3 * (c * b) - 3 * (c * β)
          + β * β - 2 * (b * β) + 2 * (c * b) - c * c * (1 + e) + c * ((e - c) * (e - c)) := by
      rw [hb0', hs0]; ring
    have hA : |c - β| ≤ 3 * (c * u) := by
      have e' : c - β = c * (c - 2 * e) := by rw [hβ]; ring
      rw [e', abs_mul, abs_of_nonneg hc]
      have : |c - 2 * e| ≤ 3 * u := by rw [abs_le]; constructor <;> linarith
      have := mul_le_mul_of_nonneg_left this hc
      linarith
    have heβ : |e * β| ≤ u * (2 * c) := by
      rw [abs_mul, abs_of_nonneg hβ0]; exact mul_le_mul heu hβ2 hβ0 hu0
    have hcb : |c * b| ≤ c * (2 * u) := by
      rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_left hbu hc
    have hbβ : |b * β| ≤ (2 * u) * (2 * c) := by
      rw [abs_mul, abs_of_nonneg hβ0]; exact mul_le_mul hbu hβ2 hβ0 (by linarith)
    have hcβ0 : 0 ≤ c * β := mul_nonneg hc hβ0
    have hcβ1 : c * β ≤ c * (2 * c) := mul_le_mul_of_nonneg_left hβ2 hc
    have hββ0 : 0 ≤ β * β := mul_nonneg hβ0 hβ0
    have hββ1 : β * β ≤ (2 * c) * (2 * c) := mul_le_mul hβ2 hβ2 hβ0 (by linarith)
    have hc2e0 : 0 ≤ c * c * (1 + e) := mul_nonneg (mul_nonneg hc hc) (by linarith)
    have hc2e1 : c * c * (1 + e) ≤ c * c * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hc)
    have hee0 : 0 ≤ (e - c) * (e - c) := mul_self_nonneg _
    have hee1 : (e - c) * (e - c) ≤ u * u := by
      have := sq_le_sq' (abs_le.mp hecu).1 (abs_le.mp hecu).2
      linarith
    have hcee0 : 0 ≤ c * ((e - c) * (e - c)) := mul_nonneg hc hee0
    have hcee1 : c * ((e - c) * (e - c)) ≤ c * (u * u) := mul_le_mul_of_nonneg_left hee1 hc
    have hcuu2 : c * (u * u) ≤ c * (u * (1 / 8)) := mul_le_mul_of_nonneg_left huu hc
    obtain ⟨a1, a2⟩ := abs_le.mp hA
    obtain ⟨g1, g2⟩ := abs_le.mp heβ
    obtain ⟨h1, h2⟩ := abs_le.mp hcb
    obtain ⟨k1, k2⟩ := abs_le.mp hbβ
    rw [key, abs_le]
    constructor <;> linarith

/-- `|∑_t f t| ≤ k B` if every `|f t| ≤ B`. -/
theorem sum_abs_bound {k : ℕ} (f : Fin k → ℝ) {B : ℝ} (h : ∀ t, |f t| ≤ B) :
    |∑ t, f t| ≤ k * B := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun t _ => h t).trans ?_)
  simp

set_option maxHeartbeats 1000000 in
/-- The walk factors `G = 1 + ∑ (φ¹+φ²) + pairs` with and without self-loops. -/
theorem G_bounds {k : ℕ} (x y p q : Fin k → ℝ) {u c : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8)
    (hc : 0 ≤ c)
    (hx : ∀ t, |x t| ≤ 4 * u) (hy : ∀ t, |y t| ≤ 4 * u) (hp : ∀ t, |p t| ≤ 2 * u)
    (hxy : ∀ t, |x t - y t| ≤ 2 * c) (hr : ∀ t, |x t + p t - (y t + q t) - c| ≤ 50 * c * u) :
    |(1 + ∑ t, (x t + p t) + ((∑ t, x t) ^ 2 - ∑ t, x t ^ 2) / 2) - 1|
        ≤ ((k : ℝ) ^ 2 + 7 * k) * u
    ∧ |(1 + ∑ t, (x t + p t) + ((∑ t, x t) ^ 2 - ∑ t, x t ^ 2) / 2)
        - (1 + ∑ t, (y t + q t) + ((∑ t, y t) ^ 2 - ∑ t, y t ^ 2) / 2) - k * c|
        ≤ (58 * k + 8 * (k : ℝ) ^ 2) * c * u := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : |∑ t, (x t + p t)| ≤ k * (6 * u) := sum_abs_bound _ fun t =>
    (abs_add_le _ _).trans (by linarith [hx t, hp t])
  have h2 : |∑ t, x t| ≤ k * (4 * u) := sum_abs_bound _ hx
  have h3 : (∑ t, x t) ^ 2 ≤ (k * (4 * u)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have h4 : 0 ≤ ∑ t, x t ^ 2 := Finset.sum_nonneg fun t _ => _root_.sq_nonneg _
  have h5 : ∑ t, x t ^ 2 ≤ k * (4 * u) ^ 2 := by
    have := sum_abs_bound (fun t => x t ^ 2) (B := (4 * u) ^ 2) fun t => by
      show |x t ^ 2| ≤ (4 * u) ^ 2
      rw [abs_of_nonneg (_root_.sq_nonneg _)]
      exact sq_le_sq' (abs_le.mp (hx t)).1 (abs_le.mp (hx t)).2
    rw [abs_of_nonneg h4] at this; exact this
  have huu : u * u ≤ u * (1 / 8) := mul_le_mul_of_nonneg_left hu hu0
  have hk2 : (k : ℝ) ^ 2 * (u * u) ≤ (k : ℝ) ^ 2 * (u * (1 / 8)) :=
    mul_le_mul_of_nonneg_left huu (by positivity)
  have hk1 : (k : ℝ) * (u * u) ≤ (k : ℝ) * (u * (1 / 8)) := mul_le_mul_of_nonneg_left huu hk0
  have h6 : 0 ≤ (∑ t, x t) ^ 2 := _root_.sq_nonneg _
  refine ⟨?_, ?_⟩
  · obtain ⟨a1, a2⟩ := abs_le.mp h1
    rw [abs_le]; constructor <;> linarith
  · have e1 : (1 + ∑ t, (x t + p t) + ((∑ t, x t) ^ 2 - ∑ t, x t ^ 2) / 2)
        - (1 + ∑ t, (y t + q t) + ((∑ t, y t) ^ 2 - ∑ t, y t ^ 2) / 2) - k * c
        = ∑ t, (x t + p t - (y t + q t) - c)
          + ((∑ t, (x t - y t)) * (∑ t, (x t + y t)) - ∑ t, (x t - y t) * (x t + y t)) / 2 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : ∀ t, (x t - y t) * (x t + y t) = x t ^ 2 - y t ^ 2 := fun t => by ring
      simp only [this, Finset.sum_sub_distrib]
      ring
    have g1 : |∑ t, (x t + p t - (y t + q t) - c)| ≤ k * (50 * c * u) := sum_abs_bound _ hr
    have g2 : |∑ t, (x t - y t)| ≤ k * (2 * c) := sum_abs_bound _ hxy
    have g3 : |∑ t, (x t + y t)| ≤ k * (8 * u) := sum_abs_bound _ fun t =>
      (abs_add_le _ _).trans (by linarith [hx t, hy t])
    have g4 : |(∑ t, (x t - y t)) * (∑ t, (x t + y t))| ≤ (k * (2 * c)) * (k * (8 * u)) := by
      rw [abs_mul]; exact mul_le_mul g2 g3 (abs_nonneg _) (by positivity)
    have g5 : |∑ t, (x t - y t) * (x t + y t)| ≤ k * ((2 * c) * (8 * u)) := sum_abs_bound _ fun t => by
      rw [abs_mul]
      exact mul_le_mul (hxy t) ((abs_add_le _ _).trans (by linarith [hx t, hy t]))
        (abs_nonneg _) (by positivity)
    rw [e1]
    obtain ⟨a1, a2⟩ := abs_le.mp g1
    obtain ⟨b1, b2⟩ := abs_le.mp g4
    obtain ⟨c1, c2⟩ := abs_le.mp g5
    rw [abs_le]; constructor <;> linarith

/-- The comparison of two weighted sums. -/
theorem F_comp {ι : Type*} [Fintype ι] (w0 w G0 G : ι → ℝ) {A Bc κ : ℝ}
    (hw0 : ∀ v, 0 ≤ w0 v) (hww : ∀ v, w0 v ≤ w v) (hA : ∀ v, |G0 v - 1| ≤ A)
    (hB : ∀ v, |G0 v - G v - κ| ≤ Bc) :
    |∑ v, w0 v * G0 v - ∑ v, w v * G v - (∑ v, w0 v - ∑ v, w v) - κ * ∑ v, w v|
      ≤ (∑ v, w v - ∑ v, w0 v) * A + (∑ v, w v) * Bc := by
  have e : ∑ v, w0 v * G0 v - ∑ v, w v * G v - (∑ v, w0 v - ∑ v, w v) - κ * ∑ v, w v
      = ∑ v, ((w0 v - w v) * (G0 v - 1) + w v * (G0 v - G v - κ)) := by
    rw [show (∑ v, ((w0 v - w v) * (G0 v - 1) + w v * (G0 v - G v - κ)))
        = ∑ v, (w0 v * G0 v - w v * G v - (w0 v - w v) - κ * w v) from
        Finset.sum_congr rfl fun v _ => by ring]
    simp only [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [e]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ v, |(w0 v - w v) * (G0 v - 1) + w v * (G0 v - G v - κ)|
      ≤ (w v - w0 v) * A + w v * Bc := by
    intro v
    have hw : 0 ≤ w v := (hw0 v).trans (hww v)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonpos (by linarith [hww v]), neg_sub]
      exact mul_le_mul_of_nonneg_left (hA v) (by linarith [hww v])
    · rw [abs_mul, abs_of_nonneg hw]; exact mul_le_mul_of_nonneg_left (hB v) hw
  refine (Finset.sum_le_sum fun v _ => hb v).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib]

end Det

section Mat

theorem cw_mono {α : Type*} [Fintype α] (B B' : α → α → ℝ) (h0 : ∀ i j, 0 ≤ B' i j)
    (h1 : ∀ i j, B' i j ≤ B i j) {n : ℕ} (v : Fin (n + 1) → α) : cw B' v ≤ cw B v :=
  Finset.prod_le_prod (fun a _ => h0 _ _) (fun a _ => h1 _ _)

/-- `0 ≤ Tr B^{j+1} ≤ M^{j+1}` for a matrix with entries in `[0, M/N]`. -/
theorem trB_le {N : ℕ} (hN : 0 < N) (B : Matrix (Fin N) (Fin N) ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hB0 : ∀ i j, 0 ≤ B i j) (hBM : ∀ i j, B i j ≤ M / N) (j : ℕ) :
    0 ≤ (B ^ (j + 1)).trace ∧ (B ^ (j + 1)).trace ≤ M ^ (j + 1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [trace_pow_cw]
  refine ⟨Finset.sum_nonneg fun v _ => cw_nonneg _ hB0 v, ?_⟩
  have hrow : ∀ i, ∑ l, B i l ≤ M := fun i => by
    calc ∑ l, B i l ≤ ∑ _l : Fin N, M / N := Finset.sum_le_sum fun l _ => hBM i l
      _ = M := by simp; field_simp
  have h := sum_cw_pos_le (B : Fin N → Fin N → ℝ) hB0 hBM hrow (div_nonneg hM hNp.le) hM
    (n := j) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) 0
  simp only [mul_one] at h
  refine h.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  ring

theorem trace_mul_natCast {N : ℕ} (k : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) :
    (A * (k : Matrix (Fin N) (Fin N) ℝ)).trace = (k : ℝ) * A.trace := by
  rw [← Nat.smul_one_eq_cast, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, nsmul_eq_mul]

/-- The binomial expansion of the trace of `(B - c·1)^k`. -/
theorem trace_sub_pow {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) (n : ℕ) :
    ((B - c • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ n).trace
      = ∑ m ∈ Finset.range (n + 1), (n.choose m : ℝ) * (-c) ^ (n - m) * (B ^ m).trace := by
  rw [sub_eq_add_neg, ← neg_smul,
    (Commute.smul_right (Commute.one_right B) (-c)).add_pow, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_pow, one_pow]
  simp only [Matrix.trace_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_eq_mul]
  rw [trace_mul_natCast]
  ring

/-- **The difference of the traces of `P̃°^k = (P̃ - c·1)^k` and `P̃^k`**, `k = n + 1 ≥ 2`:
    `Tr P̃°^k - Tr P̃^k = -k c Tr P̃^{k-1} + [k = 2] c² N + O(c²)`. -/
theorem D_expand {N : ℕ} (hN : 0 < N) (B : Matrix (Fin N) (Fin N) ℝ) {M c : ℝ}
    (hB0 : ∀ i j, 0 ≤ B i j) (hBM : ∀ i j, B i j ≤ M / N) (hM : 1 ≤ M) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hcN : c * N ≤ M) (n : ℕ) (hn : 1 ≤ n) :
    |((B - c • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace - (B ^ (n + 1)).trace
        + ((n : ℝ) + 1) * c * (B ^ n).trace - (if n = 1 then c ^ 2 * N else 0)|
      ≤ c ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M) := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  rw [trace_sub_pow, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, mul_one,
    Nat.choose_succ_self_right, show n + 1 - n = 1 by omega, pow_one]
  push_cast
  obtain ⟨R, hR⟩ : ∃ R, R = ∑ m ∈ Finset.range n, ((n + 1).choose m : ℝ) * (-c) ^ (n + 1 - m)
      * (B ^ m).trace := ⟨_, rfl⟩
  rw [← hR]
  have e : R + (↑n + 1) * -c * (B ^ n).trace + (B ^ (n + 1)).trace - (B ^ (n + 1)).trace
      + (↑n + 1) * c * (B ^ n).trace - (if n = 1 then c ^ 2 * ↑N else 0)
      = R - (if n = 1 then c ^ 2 * ↑N else 0) := by ring
  rw [e]
  have hRHS : 0 ≤ c ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M) := by positivity
  by_cases h1 : n = 1
  · subst h1
    rw [if_pos rfl, hR]
    simp [Matrix.trace_one]
    exact hRHS
  · rw [if_neg h1, sub_zero, hR]
    have hn2 : 2 ≤ n := by omega
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ m ∈ Finset.range n, |((n + 1).choose m : ℝ) * (-c) ^ (n + 1 - m) * (B ^ m).trace|
        ≤ ((n + 1).choose m : ℝ) * (c ^ 2 * M ^ (n + 1)) + (if m = 0 then c ^ 2 * M else 0) := by
      intro m hm
      have hmn : m < n := Finset.mem_range.mp hm
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hc0, Nat.abs_cast]
      by_cases hm0 : m = 0
      · subst hm0
        simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, Matrix.trace_one,
          Fintype.card_fin, ↓reduceIte, Nat.sub_zero]
        rw [abs_of_nonneg (Nat.cast_nonneg N)]
        have h2 : c ^ (n + 1) * N = c ^ n * (c * N) := by ring
        have h3 : c ^ n ≤ c ^ 2 := pow_le_pow_of_le_one hc0 hc1 hn2
        have h4 : c ^ (n + 1) * N ≤ c ^ 2 * M := by
          rw [h2]
          exact mul_le_mul h3 hcN (by positivity) (by positivity)
        have h5 : 0 ≤ c ^ 2 * M ^ (n + 1) := by positivity
        linarith
      · rw [if_neg hm0, add_zero]
        obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have ht := trB_le hN B hM0 hB0 hBM j
        rw [abs_of_nonneg ht.1]
        have h3 : c ^ (n + 1 - (j + 1)) ≤ c ^ 2 := pow_le_pow_of_le_one hc0 hc1 (by omega)
        have h4 : M ^ (j + 1) ≤ M ^ (n + 1) := pow_le_pow_right₀ hM (by omega)
        have h5 : c ^ (n + 1 - (j + 1)) * (B ^ (j + 1)).trace ≤ c ^ 2 * M ^ (n + 1) :=
          mul_le_mul h3 (ht.2.trans h4) ht.1 (by positivity)
        have h6 : (0 : ℝ) ≤ ((n + 1).choose (j + 1) : ℝ) := Nat.cast_nonneg _
        calc ((n + 1).choose (j + 1) : ℝ) * c ^ (n + 1 - (j + 1)) * (B ^ (j + 1)).trace
            = ((n + 1).choose (j + 1) : ℝ) * (c ^ (n + 1 - (j + 1)) * (B ^ (j + 1)).trace) := by
              ring
          _ ≤ _ := mul_le_mul_of_nonneg_left h5 h6
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_ite_eq' (Finset.range n) 0,
      if_pos (Finset.mem_range.mpr (by omega))]
    have hch : ∑ m ∈ Finset.range n, ((n + 1).choose m : ℝ) ≤ 2 ^ (n + 1) := by
      have h := Nat.sum_range_choose (n + 1)
      have h' : ((∑ m ∈ Finset.range (n + 1 + 1), (n + 1).choose m : ℕ) : ℝ) = 2 ^ (n + 1) := by
        rw [h]; push_cast; ring
      push_cast at h'
      rw [← h']
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        fun _ _ _ => Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right hch (by positivity : 0 ≤ c ^ 2 * M ^ (n + 1))
    nlinarith

end Mat

section DetNoLoop

set_option maxHeartbeats 4000000 in
/-- **Deterministic comparison of the walks with and without self-loops**, every `k = n + 1`.
    `K` symmetric with values in `[0, M]` and constant diagonal `κ`; `K'` the same kernel with the
    diagonal removed, `ρ' = ρ - κ/N` its normalisation (`ρ_i = (1/N) ∑_l K_il = 1 + ε_i`),
    `|ε_i| ≤ δ`, `δ + κ/N ≤ 1/8`.  With `P̃ = K/N`, `P̃° = K'/N`, `c = κ/N`:
    `|Tr P°^k - Tr P^k - (Tr P̃°^k - Tr P̃^k) - k c Tr P̃^k|
       ≤ gK (δ+c) M (1/N)∑(ε-c)² + gK δ M (1/N)∑ε²
         + (Tr P̃^k - Tr P̃°^k) (k² + 7k)(δ+c) + Tr P̃^k (58k + 8k²) c (δ+c)`. -/
theorem det_noloop {N : ℕ} (hN : 0 < N) (K K' : Fin N → Fin N → ℝ) (ρ ρ' ε bv sv : Fin N → ℝ)
    {M δ κ : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hKM : ∀ i j, K i j ≤ M) (hsym : ∀ i j, K i j = K j i)
    (hdiag : ∀ i, K i i = κ) (hK' : ∀ i j, K' i j = if i = j then 0 else K i j)
    (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hρ' : ∀ i, ρ' i = ρ i - κ / N) (hε : ∀ i, ε i = ρ i - 1)
    (hbv : ∀ i, bv i = 1 / (N : ℝ) * ∑ l, K i l * ε l)
    (hsv : ∀ i, sv i = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    (hκ : 0 ≤ κ) (hδ0 : 0 ≤ δ) (hu : δ + κ / N ≤ 1 / 8) (hεδ : ∀ i, |ε i| ≤ δ) (n : ℕ) :
    |((walkMatrix K' ρ') ^ (n + 1)).trace - ((walkMatrix K ρ) ^ (n + 1)).trace
        - ((Matrix.of (fun i j => K' i j / (N : ℝ)) ^ (n + 1)).trace
          - (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace)
        - ((n : ℝ) + 1) * (κ / N) * (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace|
      ≤ gK n * ((δ + κ / N) * M * (1 / (N : ℝ) * ∑ i, (ε i - κ / N) ^ 2))
        + gK n * (δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2))
        + ((Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace
            - (Matrix.of (fun i j => K' i j / (N : ℝ)) ^ (n + 1)).trace)
          * ((((n : ℝ) + 1) ^ 2 + 7 * ((n : ℝ) + 1)) * (δ + κ / N))
        + (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace
          * ((58 * ((n : ℝ) + 1) + 8 * ((n : ℝ) + 1) ^ 2) * (κ / N) * (δ + κ / N)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNp.ne'
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = κ / N := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u : ℝ, u = δ + κ / N := ⟨_, rfl⟩
  rw [← hcd] at hu ⊢
  rw [← hcd] at hud
  rw [← hud]
  have hc0 : 0 ≤ c := by rw [hcd]; exact div_nonneg hκ hNp.le
  have hu8 : u ≤ 1 / 8 := by rw [hud]; exact hu
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hκN : κ = c * N := by rw [hcd]; field_simp
  have hM0 : 0 ≤ M := (hK0 ⟨0, hN⟩ ⟨0, hN⟩).trans (hKM _ _)
  -- the kernel without the diagonal
  have hK'0 : ∀ i j, 0 ≤ K' i j := fun i j => by rw [hK']; split_ifs; exacts [le_rfl, hK0 i j]
  have hK'M : ∀ i j, K' i j ≤ M := fun i j => by rw [hK']; split_ifs; exacts [hM0, hKM i j]
  have hK'K : ∀ i j, K' i j ≤ K i j := fun i j => by
    rw [hK']; split_ifs; exacts [hK0 i j, le_rfl]
  have hK'sym : ∀ i j, K' i j = K' j i := fun i j => by
    rw [hK', hK']
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), hsym]
  have hρ'sum : ∀ i, ∑ l, K' i l = N * ρ' i := fun i => by
    have h := sum_offdiag K K' hK' (fun _ => (1 : ℝ)) i
    simp only [mul_one] at h
    rw [h, hρ i, hdiag i, hρ' i, hκN, mul_div_cancel_right₀ c hN0]
    ring
  obtain ⟨ε', hε'd⟩ : ∃ ε' : Fin N → ℝ, ε' = fun i => ε i - c := ⟨_, rfl⟩
  have hε'i : ∀ i, ε' i = ε i - c := fun i => by rw [hε'd]
  have hε'ρ : ∀ i, ε' i = ρ' i - 1 := fun i => by rw [hε'i, hε i, hρ' i, ← hcd]; ring
  have hε'δ : ∀ i, |ε' i| ≤ u := fun i => by
    rw [hε'i]
    obtain ⟨a1, a2⟩ := abs_le.mp (hεδ i)
    rw [abs_le]; constructor <;> linarith
  obtain ⟨bv', hbv'd⟩ : ∃ bv' : Fin N → ℝ, bv' = fun i => 1 / (N : ℝ) * ∑ l, K' i l * ε' l :=
    ⟨_, rfl⟩
  obtain ⟨sv', hsv'd⟩ : ∃ sv' : Fin N → ℝ, sv' = fun i => 1 / (N : ℝ) * ∑ l, K' i l * ε' l ^ 2 :=
    ⟨_, rfl⟩
  have hbv'i : ∀ i, bv' i = 1 / (N : ℝ) * ∑ l, K' i l * ε' l := fun i => by rw [hbv'd]
  have hsv'i : ∀ i, sv' i = 1 / (N : ℝ) * ∑ l, K' i l * ε' l ^ 2 := fun i => by rw [hsv'd]
  -- the two expansions
  have h1 := trace_expansion hN K ρ ε bv sv hK0 hKM hsym hρ hε hbv hsv hδ8 hεδ n
  have h2 := trace_expansion hN K' ρ' ε' bv' sv' (M := M) (δ := u) hK'0 hK'M hK'sym hρ'sum
    hε'ρ hbv'i hsv'i hu8 hε'δ n
  -- the vertex bounds
  have hvert : ∀ i, |-2 * ε i + bv i| ≤ 4 * u
      ∧ |-2 * ε' i + bv' i| ≤ 4 * u
      ∧ |3 * ε' i ^ 2 - 3 * ε' i * bv' i + bv' i ^ 2 - sv' i| ≤ 2 * u
      ∧ |(-2 * ε' i + bv' i) - (-2 * ε i + bv i)| ≤ 2 * c
      ∧ |((-2 * ε' i + bv' i) + (3 * ε' i ^ 2 - 3 * ε' i * bv' i + bv' i ^ 2 - sv' i))
          - ((-2 * ε i + bv i) + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i)) - c|
        ≤ 50 * c * u := by
    intro i
    have G1 := BiasVariance2.gamma_vertex hN K ρ ε hK0 hρ hε hδ8 hεδ i
    rw [← hbv i] at G1
    have G2 := BiasVariance2.gamma_vertex hN K' ρ' ε' hK'0 hρ'sum hε'ρ hu8 hε'δ i
    rw [← hbv'i i, ← hsv'i i] at G2
    have hb0 : bv' i = bv i - c * (1 + ε i) - c * (ε i - c) := by
      rw [hbv'i, sum_offdiag K K' hK' ε' i, hdiag i, hε'i i]
      have e1 : ∑ l, K i l * ε' l = ∑ l, K i l * ε l - c * (N * ρ i) := by
        rw [← hρ i, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun l _ => by rw [hε'i]; ring
      rw [e1, hbv i, hκN]
      have : ρ i = 1 + ε i := by rw [hε i]; ring
      rw [this]
      field_simp
    have hs0 : sv' i = sv i - 2 * c * bv i + c ^ 2 * (1 + ε i) - c * (ε i - c) ^ 2 := by
      rw [hsv'i, sum_offdiag K K' hK' (fun l => ε' l ^ 2) i, hdiag i, hε'i i]
      have e1 : ∑ l, K i l * ε' l ^ 2
          = ∑ l, K i l * ε l ^ 2 - 2 * c * ∑ l, K i l * ε l + c ^ 2 * (N * ρ i) := by
        rw [← hρ i, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by rw [hε'i]; ring
      rw [e1, hsv i, hbv i, hκN]
      have : ρ i = 1 + ε i := by rw [hε i]; ring
      rw [this]
      field_simp
    have hδc : δ + c ≤ u := by rw [hud]
    have := vertex_alg (s := sv i) hc0 hδ0 hδc hu8 (hεδ i) G1.2.1 hb0 hs0 G2.2.1 G2.2.2.2.1
      G2.2.2.2.2
    rw [← hε'i i] at this
    exact this
  -- the comparison of the two polynomial statistics
  obtain ⟨Bf, hBf⟩ : ∃ Bf : Fin N → Fin N → ℝ, Bf = fun i j => K i j / (N : ℝ) := ⟨_, rfl⟩
  obtain ⟨Bf', hBf'⟩ : ∃ Bf' : Fin N → Fin N → ℝ, Bf' = fun i j => K' i j / (N : ℝ) := ⟨_, rfl⟩
  have hB0 : ∀ i j, 0 ≤ Bf i j := fun i j => by rw [hBf]; exact div_nonneg (hK0 i j) hNp.le
  have hB'0 : ∀ i j, 0 ≤ Bf' i j := fun i j => by rw [hBf']; exact div_nonneg (hK'0 i j) hNp.le
  have hB'B : ∀ i j, Bf' i j ≤ Bf i j := fun i j => by
    rw [hBf, hBf']; exact div_le_div_of_nonneg_right (hK'K i j) hNp.le
  obtain ⟨G, hG⟩ : ∃ G : (Fin (n + 1) → Fin N) → ℝ, G = fun v =>
      1 + ∑ t, ((-2 * ε (v t) + bv (v t))
            + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
        + ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2 - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2) / 2 :=
    ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ : ∃ G' : (Fin (n + 1) → Fin N) → ℝ, G' = fun v =>
      1 + ∑ t, ((-2 * ε' (v t) + bv' (v t))
            + (3 * ε' (v t) ^ 2 - 3 * ε' (v t) * bv' (v t) + bv' (v t) ^ 2 - sv' (v t)))
        + ((∑ t, (-2 * ε' (v t) + bv' (v t))) ^ 2 - ∑ t, (-2 * ε' (v t) + bv' (v t)) ^ 2) / 2 :=
    ⟨_, rfl⟩
  have hGb : ∀ v : Fin (n + 1) → Fin N,
      |G' v - 1| ≤ ((((n + 1 : ℕ) : ℝ)) ^ 2 + 7 * ((n + 1 : ℕ) : ℝ)) * u
      ∧ |G' v - G v - ((n + 1 : ℕ) : ℝ) * c|
        ≤ (58 * ((n + 1 : ℕ) : ℝ) + 8 * (((n + 1 : ℕ) : ℝ)) ^ 2) * c * u := by
    intro v
    have h := G_bounds (k := n + 1) (fun t => -2 * ε' (v t) + bv' (v t))
      (fun t => -2 * ε (v t) + bv (v t))
      (fun t => 3 * ε' (v t) ^ 2 - 3 * ε' (v t) * bv' (v t) + bv' (v t) ^ 2 - sv' (v t))
      (fun t => 3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t))
      hu0 hu8 hc0 (fun t => (hvert (v t)).2.1) (fun t => (hvert (v t)).1)
      (fun t => (hvert (v t)).2.2.1) (fun t => (hvert (v t)).2.2.2.1)
      (fun t => (hvert (v t)).2.2.2.2)
    rw [hG, hG']
    exact h
  have hF := F_comp (fun v => cw Bf' v) (fun v => cw Bf v) G' G
    (A := ((((n + 1 : ℕ) : ℝ)) ^ 2 + 7 * ((n + 1 : ℕ) : ℝ)) * u)
    (Bc := (58 * ((n + 1 : ℕ) : ℝ) + 8 * (((n + 1 : ℕ) : ℝ)) ^ 2) * c * u)
    (κ := ((n + 1 : ℕ) : ℝ) * c)
    (fun v => cw_nonneg _ hB'0 v) (fun v => cw_mono Bf Bf' hB'0 hB'B v)
    (fun v => (hGb v).1) (fun v => (hGb v).2)
  beta_reduce at hF
  have eQ : ∑ v : Fin (n + 1) → Fin N, cw (fun i j => K i j / (N : ℝ)) v
        * (1 + ∑ t, ((-2 * ε (v t) + bv (v t))
            + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
          + ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2 - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2) / 2)
      = ∑ v, cw Bf v * G v := by rw [hG, hBf]
  have eQ' : ∑ v : Fin (n + 1) → Fin N, cw (fun i j => K' i j / (N : ℝ)) v
        * (1 + ∑ t, ((-2 * ε' (v t) + bv' (v t))
            + (3 * ε' (v t) ^ 2 - 3 * ε' (v t) * bv' (v t) + bv' (v t) ^ 2 - sv' (v t)))
          + ((∑ t, (-2 * ε' (v t) + bv' (v t))) ^ 2 - ∑ t, (-2 * ε' (v t) + bv' (v t)) ^ 2) / 2)
      = ∑ v, cw Bf' v * G' v := by rw [hG', hBf']
  rw [eQ] at h1
  rw [eQ'] at h2
  have eS : (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace
      = ∑ v : Fin (n + 1) → Fin N, cw Bf v := by
    rw [trace_pow_cw, hBf]; rfl
  have eS' : (Matrix.of (fun i j => K' i j / (N : ℝ)) ^ (n + 1)).trace
      = ∑ v : Fin (n + 1) → Fin N, cw Bf' v := by
    rw [trace_pow_cw, hBf']; rfl
  rw [eS, eS']
  have hS0 : 0 ≤ ∑ v : Fin (n + 1) → Fin N, cw Bf v := Finset.sum_nonneg fun v _ => cw_nonneg _ hB0 v
  have hgK : gK n * ((δ) * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2))
      = gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * (17 / 8)
          * (δ * M * (1 / (N : ℝ) * ∑ i, ε i ^ 2)) := by unfold gK; try ring
  have hgK' : gK n * (u * M * (1 / (N : ℝ) * ∑ i, (ε i - c) ^ 2))
      = gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * (17 / 8)
          * (u * M * (1 / (N : ℝ) * ∑ i, ε' i ^ 2)) := by
    unfold gK; simp only [hε'i]; try ring
  rw [hgK, hgK']
  push_cast at hF
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  obtain ⟨f1, f2⟩ := abs_le.mp hF
  rw [abs_le]; constructor <;> linarith

end DetNoLoop

section Torus

/-- `P̃ = (p(x_a - x_b)/N)` with the diagonal `p(0)/N = m₁/N` (the matrix of `mean_Q0`). -/
noncomputable def Bh (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun a b : Fin N => heatP d σ 1 (x a - x b) / N

/-- The constant of the deterministic comparison. -/
noncomputable def CdetT (n : ℕ) (M : ℝ) : ℝ :=
  ((((n : ℝ) + 1) + 2 + 2 ^ (n + 1)) * (((n : ℝ) + 1) ^ 2 + 7 * ((n : ℝ) + 1))
    + (58 * ((n : ℝ) + 1) + 8 * ((n : ℝ) + 1) ^ 2)) * M ^ (n + 1)

theorem CdetT_nonneg (n : ℕ) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ CdetT n M := by
  unfold CdetT; positivity

theorem heatP_zero (d : ℕ) (σ : ℝ) : heatP d σ 1 0 = torusM d σ 1 := by
  rw [heatP_eq_pker d σ le_rfl, torusM_eq_pker]

theorem Bh_entries {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (x : ℕ → FlatTorus d) (a b : Fin N) :
    0 ≤ Bh d σ N x a b ∧ Bh d σ N x a b ≤ torusM d σ 1 / N := by
  unfold Bh
  simp only [Matrix.of_apply]
  exact ⟨div_nonneg (heatP_nonneg hσ d 1 _) (Nat.cast_nonneg N),
    div_le_div_of_nonneg_right (heatP_le hσ d le_rfl _) (Nat.cast_nonneg N)⟩

/-- `P̃° = P̃ - (m₁/N)·1` is the matrix of the kernel with the diagonal removed. -/
theorem Bh_noloop (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) :
    Matrix.of (fun i j : Fin N => (if i = j then 0 else heatTorus d (2 * Real.pi ^ 2 * σ)
        (x i - x j)) / (N : ℝ))
      = Bh d σ N x - (torusM d σ 1 / N) • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  simp only [Bh, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases h : i = j
  · subst h; simp [heatP_zero]
  · simp [h, heatTorus_eq_heatP]

theorem Bh_noloop_entries {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (x : ℕ → FlatTorus d) (a b : Fin N) :
    0 ≤ (Bh d σ N x - (torusM d σ 1 / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) a b
    ∧ (Bh d σ N x - (torusM d σ 1 / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) a b
        ≤ torusM d σ 1 / N := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  rw [← Bh_noloop]
  simp only [Matrix.of_apply]
  by_cases h : a = b
  · simp only [if_pos h, zero_div]
    exact ⟨le_rfl, div_nonneg (zero_le_one.trans (torusM_one_ge hσ d)) (Nat.cast_nonneg N)⟩
  · simp only [if_neg h]
    refine ⟨div_nonneg (heatTorus_nonneg hc d _) (Nat.cast_nonneg N),
      div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)⟩
    rw [torusM_one]; exact heatTorus_le_zero hc d _

/-- **The deterministic comparison on the flat torus**, `k = n + 1`, on the normalisation event
    `|ρ_a - 1| ≤ δ` with `δ + m₁/N ≤ 1/8`; `c = m₁/N`, `Sε = (1/N) ∑ ε_a²`:
    `|Tr P°^k - Tr P^k - (Tr (P̃ - c)^k - Tr P̃^k) - k c Tr P̃^k|
       ≤ gK (δ+c) m₁ (2 Sε + 2c²) + gK δ m₁ Sε + CdetT · c (δ + c)`. -/
theorem det_torus {σ : ℝ} (hσ : 0 < σ) {d N : ℕ} (hN : 0 < N) (x : ℕ → FlatTorus d)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hu : δ + torusM d σ 1 / N ≤ 1 / 8)
    (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ) (n : ℕ) (hn : 1 ≤ n) :
    |((noloopWalk d σ N x) ^ (n + 1)).trace - ((torusWalk d σ N x) ^ (n + 1)).trace
        - (((Bh d σ N x - (torusM d σ 1 / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace
          - ((Bh d σ N x) ^ (n + 1)).trace)
        - ((n : ℝ) + 1) * (torusM d σ 1 / N) * ((Bh d σ N x) ^ (n + 1)).trace|
      ≤ gK n * ((δ + torusM d σ 1 / N) * torusM d σ 1
            * (2 * (1 / (N : ℝ) * ∑ i : Fin N, eV d σ N x i ^ 2) + 2 * (torusM d σ 1 / N) ^ 2))
        + gK n * (δ * torusM d σ 1 * (1 / (N : ℝ) * ∑ i : Fin N, eV d σ N x i ^ 2))
        + CdetT n (torusM d σ 1) * (torusM d σ 1 / N) * (δ + torusM d σ 1 / N) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNp.ne'
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  rw [← hMd] at hu ⊢
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hc0 : 0 ≤ M / N := div_nonneg hM0 hNp.le
  have hc1 : M / N ≤ 1 := by linarith
  have hcN : M / N * N = M := by field_simp
  have hK0 : ∀ i j : Fin N, 0 ≤ torusK d σ N x i j := fun i j => heatTorus_nonneg hc d _
  have hKM : ∀ i j : Fin N, torusK d σ N x i j ≤ M := fun i j => by
    show heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j) ≤ M
    rw [hMd, torusM_one]; exact heatTorus_le_zero hc d _
  have h := det_noloop hN (torusK d σ N x)
    (fun i j : Fin N => if i = j then 0 else heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j))
    (torusRho d σ N x) (fun a : Fin N => heatRho d σ N x a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N)
    (fun i => eV d σ N x i) (fun i => bV d σ N x i) (fun i => sV d σ N x i)
    (M := M) (δ := δ) (κ := M)
    hK0 hKM
    (fun i j => by
      show heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j)
        = heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x i)
      rw [← neg_sub (x j) (x i), heatTorus_even])
    (fun i => by
      show heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x i) = M
      rw [sub_self, hMd, torusM_one])
    (fun i j => by show _ = _; rfl)
    (fun i => by
      show ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l) = N * heatRho d σ N x i
      rw [Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) N]
      unfold heatRho
      field_simp)
    (fun i => by
      show heatRho d σ N x i - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N = heatRho d σ N x i - M / N
      rw [hMd, torusM_one])
    (fun i => (eps_row d σ hN x i).symm)
    (fun i => by
      show 1 / (N : ℝ) * ∑ q : Fin N, heatP d σ 1 (x i - x q) * eV d σ N x q
        = 1 / (N : ℝ) * ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l) * eV d σ N x l
      simp only [heatTorus_eq_heatP])
    (fun i => by
      show 1 / (N : ℝ) * ∑ q : Fin N, heatP d σ 1 (x i - x q) * eV d σ N x q ^ 2
        = 1 / (N : ℝ) * ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)
          * eV d σ N x l ^ 2
      simp only [heatTorus_eq_heatP])
    hM0 hδ0 hu
    (fun i => by
      show |eV d σ N x i| ≤ δ
      rw [show eV d σ N x i = heatRho d σ N x i - 1 from (eps_row d σ hN x i).symm]
      exact hρ i) n
  -- identify the matrices
  have eB : Matrix.of (fun i j : Fin N => torusK d σ N x i j / (N : ℝ)) = Bh d σ N x := by
    ext i j; simp only [Bh, Matrix.of_apply, torusK, heatTorus_eq_heatP]
  have eB' := Bh_noloop d σ N x
  rw [← hMd] at eB'
  rw [eB, eB'] at h
  have eW : walkMatrix (fun i j : Fin N => if i = j then 0 else heatTorus d (2 * Real.pi ^ 2 * σ)
      (x i - x j)) (fun a : Fin N => heatRho d σ N x a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N)
      = noloopWalk d σ N x := rfl
  rw [eW] at h
  change |((noloopWalk d σ N x) ^ (n + 1)).trace - ((torusWalk d σ N x) ^ (n + 1)).trace - _ - _|
    ≤ _ at h
  -- the trace bounds
  have hBe := fun a b => Bh_entries hσ d N x a b
  have hB'e := fun a b => Bh_noloop_entries hσ d N x a b
  rw [← hMd] at hBe hB'e
  have hS := trB_le hN (Bh d σ N x) hM0 (fun a b => (hBe a b).1) (fun a b => (hBe a b).2) n
  have hSn : (Bh d σ N x ^ n).trace ≤ M ^ n := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    exact (trB_le hN (Bh d σ N x) hM0 (fun a b => (hBe a b).1) (fun a b => (hBe a b).2) j).2
  have hSn0 : 0 ≤ (Bh d σ N x ^ n).trace := by
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    exact (trB_le hN (Bh d σ N x) hM0 (fun a b => (hBe a b).1) (fun a b => (hBe a b).2) j).1
  have hD := D_expand hN (Bh d σ N x) (fun a b => (hBe a b).1) (fun a b => (hBe a b).2) hM1 hc0
    hc1 (le_of_eq hcN) n hn
  -- |D| ≤ c (k + 2 + 2^k) M^k
  have hMn : M ^ n ≤ M ^ (n + 1) := pow_le_pow_right₀ hM1 (by omega)
  have hMk : M ≤ M ^ (n + 1) := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ (n + 1) := pow_le_pow_right₀ hM1 (by omega)
  have hcc : (M / N) ^ 2 ≤ M / N := by
    rw [sq]; exact mul_le_of_le_one_left hc0 hc1
  have hite : 0 ≤ (if n = 1 then (M / N) ^ 2 * N else 0) ∧
      (if n = 1 then (M / N) ^ 2 * N else 0) ≤ M / N * M := by
    split_ifs
    · constructor
      · positivity
      · rw [sq, mul_assoc, hcN]
    · exact ⟨le_rfl, mul_nonneg hc0 hM0⟩
  obtain ⟨D, hDd⟩ : ∃ D, D = ((Bh d σ N x - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace
      - (Bh d σ N x ^ (n + 1)).trace := ⟨_, rfl⟩
  rw [← hDd] at h
  have hDabs : |D| ≤ M / N * ((((n : ℝ) + 1) + 2 + 2 ^ (n + 1)) * M ^ (n + 1)) := by
    rw [hDd]
    obtain ⟨d1, d2⟩ := abs_le.mp hD
    have p1 : ((n : ℝ) + 1) * (M / N) * (Bh d σ N x ^ n).trace
        ≤ ((n : ℝ) + 1) * (M / N) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (hSn.trans hMn) (by positivity)
    have p1' : 0 ≤ ((n : ℝ) + 1) * (M / N) * (Bh d σ N x ^ n).trace :=
      mul_nonneg (by positivity) hSn0
    have p2 : (M / N) ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M)
        ≤ M / N * (2 ^ (n + 1) * M ^ (n + 1) + M ^ (n + 1)) := by
      have := mul_le_mul_of_nonneg_right hcc (by positivity : 0 ≤ 2 ^ (n + 1) * M ^ (n + 1) + M)
      have h2 : M / N * (2 ^ (n + 1) * M ^ (n + 1) + M)
          ≤ M / N * (2 ^ (n + 1) * M ^ (n + 1) + M ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc0
      linarith
    have p3 : M / N * M ≤ M / N * M ^ (n + 1) := mul_le_mul_of_nonneg_left hMk hc0
    have e : M / N * ((((n : ℝ) + 1) + 2 + 2 ^ (n + 1)) * M ^ (n + 1))
        = ((n : ℝ) + 1) * (M / N) * M ^ (n + 1) + M / N * M ^ (n + 1)
          + M / N * (2 ^ (n + 1) * M ^ (n + 1) + M ^ (n + 1)) := by ring
    rw [e, abs_le]
    constructor <;> linarith [hite.1, hite.2]
  -- the sum of squares of `ε - c`
  have hsq : 1 / (N : ℝ) * ∑ i : Fin N, (eV d σ N x i - M / N) ^ 2
      ≤ 2 * (1 / (N : ℝ) * ∑ i : Fin N, eV d σ N x i ^ 2) + 2 * (M / N) ^ 2 := by
    have h1 : ∑ i : Fin N, (eV d σ N x i - M / N) ^ 2
        ≤ ∑ i : Fin N, (2 * eV d σ N x i ^ 2 + 2 * (M / N) ^ 2) :=
      Finset.sum_le_sum fun i _ => by nlinarith [_root_.sq_nonneg (eV d σ N x i + M / N)]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / N)
    have e : 1 / (N : ℝ) * (2 * ∑ i : Fin N, eV d σ N x i ^ 2 + N * (2 * (M / N) ^ 2))
        = 2 * (1 / (N : ℝ) * ∑ i : Fin N, eV d σ N x i ^ 2) + 2 * (M / N) ^ 2 := by
      field_simp
    linarith
  have hgK := gK_nonneg n
  have hA1 : gK n * ((δ + M / N) * M * (1 / (N : ℝ) * ∑ i : Fin N, (eV d σ N x i - M / N) ^ 2))
      ≤ gK n * ((δ + M / N) * M
          * (2 * (1 / (N : ℝ) * ∑ i : Fin N, eV d σ N x i ^ 2) + 2 * (M / N) ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) hgK
  have hu0 : 0 ≤ δ + M / N := by positivity
  have hA : (Bh d σ N x ^ (n + 1)).trace
        - ((Bh d σ N x - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace
      ≤ M / N * ((((n : ℝ) + 1) + 2 + 2 ^ (n + 1)) * M ^ (n + 1)) := by
    have : (Bh d σ N x ^ (n + 1)).trace
        - ((Bh d σ N x - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace = -D := by
      rw [hDd]; ring
    rw [this]; exact (neg_le_abs D).trans hDabs
  have hA2 := mul_le_mul_of_nonneg_right hA
    (by positivity : 0 ≤ ((((n : ℝ) + 1) ^ 2 + 7 * ((n : ℝ) + 1)) * (δ + M / N)))
  have hB2 := mul_le_mul_of_nonneg_right hS.2
    (by positivity : 0 ≤ (58 * ((n : ℝ) + 1) + 8 * ((n : ℝ) + 1) ^ 2) * (M / N) * (δ + M / N))
  have eC : CdetT n M * (M / N) * (δ + M / N)
      = M / N * ((((n : ℝ) + 1) + 2 + 2 ^ (n + 1)) * M ^ (n + 1))
          * ((((n : ℝ) + 1) ^ 2 + 7 * ((n : ℝ) + 1)) * (δ + M / N))
        + M ^ (n + 1) * ((58 * ((n : ℝ) + 1) + 8 * ((n : ℝ) + 1) ^ 2) * (M / N) * (δ + M / N)) := by
    unfold CdetT; ring
  rw [eC, ← hDd]
  linarith

end Torus

section Final

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`β_k` of `prop:bias` for `ρ = 0` (graph without self-loops)**, every `k ≥ 2`:
    `β°_k = β_k - k m₁ (m_{k-1} - m_k) + [k = 2] m₁²`, with `β_k = betaK` (the coefficient for
    `ρ = p(0)`).  For `k ≥ 3` this is the formula of `rem:bias`(ii); for `k = 2` it is
    `β₂ - m₁² + 2 m₁ m₂`, the value of the formula of the proposition at `ρ = 0`. -/
noncomputable def betaNL (d : ℕ) (σ : ℝ) (k : ℕ) : ℝ :=
  betaK d σ k - k * torusM d σ 1 * (torusM d σ (k - 1) - torusM d σ k)
    + (if k = 2 then torusM d σ 1 ^ 2 else 0)

/-- `β°_k` written as the formula of the proposition with `ρ = 0` (`μ₁ = 0`, `μ_k = m_k`):
    `k [Σ°₀/2 - 2Σ₁ + 3Σ₂ - 2Σ₃ + Σ₄/2] + k m_k (m₄ - 3m₃ + 3m₂)` with
    `Σ°₀ = ∑_{l=2}^{k-2} m_l m_{k-l}` (the terms `l = 1`, `l = k-1` vanish). -/
theorem betaNL_eq_formula (d : ℕ) (σ : ℝ) (k : ℕ) (hk : 2 ≤ k) :
    betaNL d σ k = k * ((∑ l ∈ Finset.Ico 1 k,
          (if l = 1 then 0 else torusM d σ l) * (if k - l = 1 then 0 else torusM d σ (k - l))) / 2
        - 2 * sigC d σ k 1 + 3 * sigC d σ k 2 - 2 * sigC d σ k 3 + sigC d σ k 4 / 2)
      + k * torusM d σ k * (torusM d σ 4 - 3 * torusM d σ 3 + 3 * torusM d σ 2) := by
  have hs : sig0 d σ k = ∑ l ∈ Finset.Ico 1 k,
        (if l = 1 then 0 else torusM d σ l) * (if k - l = 1 then 0 else torusM d σ (k - l))
      + (if k = 2 then torusM d σ 1 ^ 2 else 2 * torusM d σ 1 * torusM d σ (k - 1)) := by
    unfold sig0
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rcases Nat.eq_zero_or_pos j with h0 | hj
    · subst h0; simp [Finset.sum_Ico_succ_top]; ring
    · rw [if_neg (by omega)]
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ j + 1), Finset.sum_eq_sum_Ico_succ_bot
        (by omega : 1 < j + 1)]
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ j + 1), Finset.sum_eq_sum_Ico_succ_bot
        (by omega : 1 < j + 1)]
      have e : ∀ l ∈ Finset.Ico 2 (j + 1), torusM d σ l * torusM d σ (j + 2 - l)
          = (if l = 1 then 0 else torusM d σ l) * (if j + 2 - l = 1 then 0 else torusM d σ (j + 2 - l)) := by
        intro l hl
        have := Finset.mem_Ico.mp hl
        rw [if_neg (by omega), if_neg (by omega)]
      rw [Finset.sum_congr rfl e]
      simp only [↓reduceIte, show j + 2 - 1 = j + 1 by omega, show j + 2 - (j + 1) = 1 by omega,
        if_neg (show ¬ (j + 1 = 1) by omega), if_neg (show ¬ (j + 2 - 1 = 1) by omega)]
      ring
  unfold betaNL betaK
  rw [hs]
  by_cases h2 : k = 2
  · subst h2; simp; ring
  · rw [if_neg h2, if_neg h2]; ring

/-- The constant of `|E Tr P̃^j - m_j|`. -/
noncomputable def CSt (d : ℕ) (σ : ℝ) (j : ℕ) : ℝ :=
  ((Prs j).card : ℝ) * torusM d σ j + |∑ p ∈ Prs j, Ip (torusM d σ) j p|
    + (torusM d σ 1 + torusM d σ 1 * torusM d σ 1 + 2 * torusM d σ 1 ^ j) * ((Prs j).card : ℝ) ^ 2

end Final

section Final2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem CSt_nonneg {σ : ℝ} (hσ : 0 < σ) (d j : ℕ) (hj : 1 ≤ j) : 0 ≤ CSt d σ j := by
  have h1 := (torusRK hσ d).m_nonneg j hj
  have hM := torusM_one_ge hσ d
  unfold CSt; positivity

theorem Bh_entry_measurable {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d)
    (hX : ∀ j, Measurable (X j)) (N : ℕ) (a b : Fin N) :
    Measurable fun ω => Bh d σ N (fun j => X j ω) a b := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have e : (fun ω => Bh d σ N (fun j => X j ω) a b)
      = fun ω => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X b ω) / N := by
    funext ω; simp only [Bh, Matrix.of_apply, heatTorus_eq_heatP]
  rw [e]
  exact (heatTorus_sample_measurable hc d X hX a b).div_const _

/-- **`E Tr P̃^j = m_j + O(1/N)`** on the flat torus, every `j ≥ 1` (for `j = 1` exactly). -/
theorem mean_trB [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N)
    (j : ℕ) (hj : 1 ≤ j) :
    |∫ ω, ((Bh d σ N (fun i => X i ω)) ^ j).trace ∂μ - torusM d σ j| ≤ CSt d σ j / N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hC := CSt_nonneg hσ d j hj
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    have e : ∀ ω, ((Bh d σ N (fun i => X i ω)) ^ (0 + 1)).trace = torusM d σ 1 := by
      intro ω
      rw [zero_add, pow_one, Matrix.trace]
      simp only [Matrix.diag_apply, Bh, Matrix.of_apply, sub_self, heatP_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simp only [e, integral_const, probReal_univ, one_smul, sub_self, abs_zero]
    exact div_nonneg hC hNp.le
  · have h := mean_Q0 (torusRK hσ d) X h_indep hX hlaw (N := N) (n := m) hN hm
    have e : ∫ ω, ((Bh d σ N (fun i => X i ω)) ^ (m + 1)).trace ∂μ
        = ∫ ω, ((Matrix.of (fun a b : Fin N =>
            (fun i (x y : FlatTorus d) => heatP d σ i (x - y)) 1 (X a ω) (X b ω) / N)) ^ (m + 1)).trace ∂μ :=
      rfl
    rw [e]
    obtain ⟨E, hE⟩ : ∃ E, E = ∫ ω, ((Matrix.of (fun a b : Fin N =>
            (fun i (x y : FlatTorus d) => heatP d σ i (x - y)) 1 (X a ω) (X b ω) / N)) ^ (m + 1)).trace ∂μ :=
      ⟨_, rfl⟩
    rw [← hE] at h ⊢
    obtain ⟨h1, h2⟩ := abs_le.mp h
    have hM := torusM_one_ge hσ d
    have hcard : (0 : ℝ) ≤ ((Prs (m + 1)).card : ℝ) := Nat.cast_nonneg _
    have hm0 := (torusRK hσ d).m_nonneg (m + 1) (by omega)
    have hB0 : 0 ≤ (torusM d σ 1 + torusM d σ 1 * torusM d σ 1 + 2 * torusM d σ 1 ^ (m + 1))
        * ((Prs (m + 1)).card : ℝ) ^ 2 := by positivity
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hq : (torusM d σ 1 + torusM d σ 1 * torusM d σ 1 + 2 * torusM d σ 1 ^ (m + 1))
        * ((Prs (m + 1)).card : ℝ) ^ 2 / (N : ℝ) ^ 2
        ≤ (torusM d σ 1 + torusM d σ 1 * torusM d σ 1 + 2 * torusM d σ 1 ^ (m + 1))
        * ((Prs (m + 1)).card : ℝ) ^ 2 / N := div_le_div_of_nonneg_left hB0 hNp hNN
    have hI1 := neg_abs_le (∑ p ∈ Prs (m + 1), Ip (torusM d σ) (m + 1) p)
    have hI2 := le_abs_self (∑ p ∈ Prs (m + 1), Ip (torusM d σ) (m + 1) p)
    have eC : CSt d σ (m + 1) / N = ((Prs (m + 1)).card : ℝ) * torusM d σ (m + 1) / N
        + |∑ p ∈ Prs (m + 1), Ip (torusM d σ) (m + 1) p| / N
        + (torusM d σ 1 + torusM d σ 1 * torusM d σ 1 + 2 * torusM d σ 1 ^ (m + 1))
          * ((Prs (m + 1)).card : ℝ) ^ 2 / N := by unfold CSt; ring
    have hd1 : (∑ p ∈ Prs (m + 1), Ip (torusM d σ) (m + 1) p) / N
        ≤ |∑ p ∈ Prs (m + 1), Ip (torusM d σ) (m + 1) p| / N :=
      div_le_div_of_nonneg_right hI2 hNp.le
    have hd2 : -(|∑ p ∈ Prs (m + 1), Ip (torusM d σ) (m + 1) p| / N)
        ≤ (∑ p ∈ Prs (m + 1), Ip (torusM d σ) (m + 1) p) / N := by
      rw [← neg_div]; exact div_le_div_of_nonneg_right hI1 hNp.le
    have hd3 : 0 ≤ ((Prs (m + 1)).card : ℝ) * torusM d σ (m + 1) / N := by positivity
    rw [eC, abs_le]; constructor <;> linarith

theorem rho_noloop_nonneg {σ : ℝ} (hσ : 0 < σ) {d N : ℕ} (x : ℕ → FlatTorus d) (a : Fin N) :
    0 ≤ heatRho d σ N x a - heatTorus d (2 * Real.pi ^ 2 * σ) 0 / N := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  unfold heatRho
  have h := Finset.single_le_sum (f := fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x l))
    (fun l _ => heatTorus_nonneg hc d _) (Finset.mem_range.mpr a.2)
  simp only [sub_self] at h
  rw [← sub_div]
  exact div_nonneg (by linarith) (Nat.cast_nonneg N)

theorem trace_unit_bound {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (h : ∀ a, 0 ≤ A a a ∧ A a a ≤ 1) : |A.trace| ≤ N := by
  have h0 : 0 ≤ A.trace := Finset.sum_nonneg fun a _ => (h a).1
  rw [abs_of_nonneg h0]
  calc A.trace ≤ ∑ _a : Fin N, (1 : ℝ) := Finset.sum_le_sum fun a _ => (h a).2
    _ = N := by simp

/-- The error term of `bias_noloops_general` (without the bad-event term); `M = m₁`, `c = M/N`. -/
noncomputable def errNL (d : ℕ) (σ : ℝ) (N n : ℕ) (δ : ℝ) : ℝ :=
  4 * gK n * δ * torusM d σ 1 ^ 3 / N
    + gK n * (δ + torusM d σ 1 / N) * torusM d σ 1
        * (4 * torusM d σ 1 ^ 2 / N + 2 * (torusM d σ 1 / N) ^ 2)
    + CdetT n (torusM d σ 1) * (torusM d σ 1 / N) * (δ + torusM d σ 1 / N)
    + Ctot d σ n / (N : ℝ) ^ 2
    + ((n : ℝ) + 1) * torusM d σ 1 * (CSt d σ n + CSt d σ (n + 1)) / (N : ℝ) ^ 2
    + (torusM d σ 1 / N) ^ 2 * (2 ^ (n + 1) * torusM d σ 1 ^ (n + 1) + torusM d σ 1)

set_option maxHeartbeats 4000000 in
/-- **`prop:bias` for the graph WITHOUT self-loops (`ρ = 0`), every `k = n + 1 ≥ 2`, heat kernel
    on the flat torus, general normalisation event.** For independent uniform points, `N ≥ 1`,
    `0 ≤ δ`, `δ + m₁/N ≤ 1/8`:
    `|E Tr P°^k - m_k - β°_k/N| ≤ errNL + (3N + CQT + 2 m₁^k + k m₁^{k+1}) · P(max_a |ρ_a - 1| > δ)`
    with `β°_k = betaNL d σ k` (`= β_k - k m₁(m_{k-1} - m_k) + [k=2] m₁²`, see
    `betaNL_eq_formula` for the formula of the proposition at `ρ = 0`); `ρ_a` is the
    normalisation WITH self-loops (`ρ°_a = ρ_a - m₁/N`). -/
theorem bias_noloops_general [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hu : δ + torusM d σ 1 / N ≤ 1 / 8) (n : ℕ) (hn : 1 ≤ n) :
    |∫ ω, ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - (torusM d σ (n + 1) + betaNL d σ (n + 1) / N)|
      ≤ errNL d σ N n δ
        + (3 * N + CQT d σ n + 2 * torusM d σ 1 ^ (n + 1) + ((n : ℝ) + 1) * torusM d σ 1 ^ (n + 2))
          * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hN' : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have H := torus_bvk X h_indep hX hlaw hσ
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hδ8 : δ ≤ 1 / 8 := by
    have : 0 ≤ torusM d σ 1 / N := div_nonneg (zero_le_one.trans (torusM_one_ge hσ d)) hNp.le
    linarith
  -- the five random variables
  obtain ⟨T0, hT0⟩ : ∃ T0 : Ω → ℝ, T0 = fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Ω → ℝ, T = fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Ω → ℝ, S = fun ω => ((Bh d σ N (fun j => X j ω)) ^ (n + 1)).trace :=
    ⟨_, rfl⟩
  obtain ⟨Sn, hSn⟩ : ∃ Sn : Ω → ℝ, Sn = fun ω => ((Bh d σ N (fun j => X j ω)) ^ n).trace :=
    ⟨_, rfl⟩
  obtain ⟨Dx, hDx⟩ : ∃ Dx : Ω → ℝ, Dx = fun ω =>
      ((Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace
        - ((Bh d σ N (fun j => X j ω)) ^ (n + 1)).trace := ⟨_, rfl⟩
  -- entry bounds
  have hBe : ∀ ω (a b : Fin N), 0 ≤ Bh d σ N (fun j => X j ω) a b
      ∧ Bh d σ N (fun j => X j ω) a b ≤ M / N := fun ω a b => by
    rw [hMd]; exact Bh_entries hσ d N _ a b
  have hB'e : ∀ ω (a b : Fin N),
      0 ≤ (Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) a b
      ∧ (Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) a b ≤ M / N :=
    fun ω a b => by rw [hMd]; exact Bh_noloop_entries hσ d N _ a b
  have hSb : ∀ ω, 0 ≤ S ω ∧ S ω ≤ M ^ (n + 1) := fun ω => by
    rw [hS]; exact trB_le hN' _ hM0 (fun a b => (hBe ω a b).1) (fun a b => (hBe ω a b).2) n
  have hSnb : ∀ ω, 0 ≤ Sn ω ∧ Sn ω ≤ M ^ n := fun ω => by
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [hSn]; simp only; rw [hj]
    exact trB_le hN' _ hM0 (fun a b => (hBe ω a b).1) (fun a b => (hBe ω a b).2) j
  have hS'b : ∀ ω, 0 ≤ ((Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ))
        ^ (n + 1)).trace
      ∧ ((Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace
        ≤ M ^ (n + 1) := fun ω =>
    trB_le hN' _ hM0 (fun a b => (hB'e ω a b).1) (fun a b => (hB'e ω a b).2) n
  have hDb : ∀ ω, |Dx ω| ≤ 2 * M ^ (n + 1) := fun ω => by
    rw [hDx]; simp only
    obtain ⟨a1, a2⟩ := hS'b ω
    obtain ⟨b1, b2⟩ := hSb ω
    rw [hS] at b1 b2; simp only at b1 b2
    rw [abs_le]; constructor <;> linarith
  have hT0b : ∀ ω, |T0 ω| ≤ N := fun ω => by
    rw [hT0]
    exact trace_unit_bound _ fun a => walk_pow_diag_unit _ _
      (fun i j => by split_ifs; exacts [le_rfl, heatTorus_nonneg hc d _])
      (fun i => rho_noloop_nonneg hσ _ i) (n + 1) a
  have hTb : ∀ ω, |T ω| ≤ N := fun ω => by
    rw [hT]
    exact trace_unit_bound _ fun a => walk_pow_diag_unit _ _ (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) (n + 1) a
  -- measurability
  have mBh : ∀ a b : Fin N, Measurable fun ω => Bh d σ N (fun j => X j ω) a b :=
    fun a b => Bh_entry_measurable hσ d X hX N a b
  have mBh' : ∀ a b : Fin N, Measurable fun ω =>
      (Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) a b := fun a b => by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (mBh a b).sub_const _
  have bT0 : BM T0 := ⟨by
      rw [hT0]
      exact ExceptionalSets.pow_trace_measurable (fun ω => noloopWalk d σ N (fun j => X j ω))
        (fun a b => Reals2Sets.noloop_entry_measurable hσ d X hX N a b) (n + 1), N, hT0b⟩
  have bT : BM T := ⟨by
      rw [hT]
      exact Finset.measurable_sum _ fun a _ => walk_pow_entry_measurable hσ d X hX N (n + 1) a a,
    N, hTb⟩
  have bS : BM S := ⟨by
      rw [hS]
      exact ExceptionalSets.pow_trace_measurable (fun ω => Bh d σ N (fun j => X j ω)) mBh (n + 1),
    M ^ (n + 1), fun ω => by rw [abs_of_nonneg (hSb ω).1]; exact (hSb ω).2⟩
  have bSn : BM Sn := ⟨by
      rw [hSn]
      exact ExceptionalSets.pow_trace_measurable (fun ω => Bh d σ N (fun j => X j ω)) mBh n,
    M ^ n, fun ω => by rw [abs_of_nonneg (hSnb ω).1]; exact (hSnb ω).2⟩
  have bDx : BM Dx := ⟨by
      rw [hDx]
      exact (ExceptionalSets.pow_trace_measurable (fun ω => Bh d σ N (fun j => X j ω)
        - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) mBh' (n + 1)).sub
        (ExceptionalSets.pow_trace_measurable (fun ω => Bh d σ N (fun j => X j ω)) mBh (n + 1)),
    2 * M ^ (n + 1), hDb⟩
  -- (1) the walk with self-loops
  have hE1 := bias_general X h_indep hX hlaw hσ N hN hδ0 hδ8 n hn
  rw [← hMd] at hE1
  have eT : ∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ = ∫ ω, T ω ∂μ := by
    rw [hT]
  rw [eT] at hE1
  -- (2) the mean of `Tr P̃^k` and `Tr P̃^{k-1}`
  have hE2 := mean_trB X h_indep hX hlaw hσ hN (n + 1) (by omega)
  have hE3 := mean_trB X h_indep hX hlaw hσ hN n hn
  have eS : ∫ ω, ((Bh d σ N (fun i => X i ω)) ^ (n + 1)).trace ∂μ = ∫ ω, S ω ∂μ := by rw [hS]
  have eSn : ∫ ω, ((Bh d σ N (fun i => X i ω)) ^ n).trace ∂μ = ∫ ω, Sn ω ∂μ := by rw [hSn]
  rw [eS] at hE2
  rw [eSn] at hE3
  -- (3) the binomial remainder
  obtain ⟨ite1, hite1⟩ : ∃ t : ℝ, t = if n = 1 then (M / N) ^ 2 * N else 0 := ⟨_, rfl⟩
  have hRp : ∀ ω, |Dx ω + ((n : ℝ) + 1) * (M / N) * Sn ω - ite1|
      ≤ (M / N) ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M) := fun ω => by
    have h := D_expand hN' (Bh d σ N (fun j => X j ω)) (fun a b => (hBe ω a b).1)
      (fun a b => (hBe ω a b).2) hM1 (div_nonneg hM0 hNp.le) (by
        have : M / N ≤ 1 / 8 := by rw [hMd]; linarith
        linarith) (le_of_eq (by field_simp)) n hn
    rw [hDx, hSn, hite1]; simp only
    convert h using 2
  have hE4 := abs_int_le_B (μ := μ) hRp
  have iR : ∫ ω, (Dx ω + ((n : ℝ) + 1) * (M / N) * Sn ω - ite1) ∂μ
      = ∫ ω, Dx ω ∂μ + ((n : ℝ) + 1) * (M / N) * ∫ ω, Sn ω ∂μ - ite1 := by
    have i1 : Integrable (fun ω => Dx ω + ((n : ℝ) + 1) * (M / N) * Sn ω) μ :=
      bDx.integrable.add (bSn.integrable.const_mul _)
    have i2 : Integrable (fun ω => ((n : ℝ) + 1) * (M / N) * Sn ω) μ :=
      bSn.integrable.const_mul _
    rw [integral_sub i1 (integrable_const _), integral_add bDx.integrable i2, integral_const_mul,
      integral_const, probReal_univ, one_smul]
  rw [iR] at hE4
  -- (4) the comparison, pointwise
  have hGm : MeasurableSet {ω | ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => measurableSet_le
      (continuous_abs.measurable.comp
        ((heatRho_sample_measurable hσ d X hX N a).sub measurable_const)) measurable_const
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Set Ω,
      Gc = {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  have hGcm : MeasurableSet Gc := by rw [hGc]; exact hGm.compl
  rw [← hGc]
  have bS2 : BM (fun ω => ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω) :=
    BM.sum _ _ fun q _ => (H.bmH N q).mul (H.bmH N q)
  have hS2n : ∀ ω, 0 ≤ ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω := fun ω =>
    Finset.sum_nonneg fun q _ => _root_.mul_self_nonneg _
  have hgK := gK_nonneg n
  have hCd := CdetT_nonneg n hM0
  obtain ⟨Sε, hSε⟩ : ∃ Sε : Ω → ℝ, Sε = fun ω => 1 / (N : ℝ) ^ 3 * ∑ q ∈ Finset.range N,
      Hrow (cK d σ) X N q ω * Hrow (cK d σ) X N q ω := ⟨_, rfl⟩
  have hSε0 : ∀ ω, 0 ≤ Sε ω := fun ω => by rw [hSε]; exact mul_nonneg (by positivity) (hS2n ω)
  obtain ⟨g, hg⟩ : ∃ g : Ω → ℝ, g = fun ω =>
      (gK n * ((δ + M / N) * M * 2) + gK n * (δ * M)) * Sε ω
        + (gK n * ((δ + M / N) * M * (2 * (M / N) ^ 2)) + CdetT n M * (M / N) * (δ + M / N))
        + (2 * N + 2 * M ^ (n + 1) + ((n : ℝ) + 1) * M ^ (n + 2))
          * Gc.indicator (fun _ => (1 : ℝ)) ω := ⟨_, rfl⟩
  have hcoef0 : 0 ≤ gK n * ((δ + M / N) * M * 2) + gK n * (δ * M) := by positivity
  have hconst0 : 0 ≤ gK n * ((δ + M / N) * M * (2 * (M / N) ^ 2))
      + CdetT n M * (M / N) * (δ + M / N) := by positivity
  have hpt : ∀ ω, |T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω| ≤ g ω := by
    intro ω
    by_cases hω : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ
    · have hnot : ω ∉ Gc := by rw [hGc]; exact fun h => h hω
      rw [hg]; simp only
      rw [Set.indicator_of_notMem hnot, mul_zero, add_zero]
      have h := det_torus hσ hN' (fun j => X j ω) hδ0 hu hω n hn
      rw [← hMd, eV_sq_sum σ hN' X ω] at h
      rw [hT0, hT, hDx, hS]; simp only
      rw [hSε]; simp only
      refine h.trans (le_of_eq ?_)
      ring
    · have hin : ω ∈ Gc := by rw [hGc]; exact hω
      rw [hg]; simp only
      rw [Set.indicator_of_mem hin, mul_one]
      have a0 := mul_nonneg hcoef0 (hSε0 ω)
      have hcS : ((n : ℝ) + 1) * (M / N) * |S ω| ≤ ((n : ℝ) + 1) * M ^ (n + 2) := by
        rw [abs_of_nonneg (hSb ω).1]
        have hc1 : M / N ≤ M := div_le_self hM0 hN1
        have : (M / N) * S ω ≤ M * M ^ (n + 1) :=
          mul_le_mul hc1 (hSb ω).2 (hSb ω).1 hM0
        rw [pow_succ, mul_comm (M ^ (n + 1)) M, mul_assoc]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have e1 := hT0b ω
      have e2 := hTb ω
      have e3 := hDb ω
      have e4 : |((n : ℝ) + 1) * (M / N) * S ω| = ((n : ℝ) + 1) * (M / N) * |S ω| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * (M / N))]
      calc |T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω|
          ≤ |T0 ω| + |T ω| + |Dx ω| + |((n : ℝ) + 1) * (M / N) * S ω| := by
            have := abs_sub (T0 ω - T ω - Dx ω) (((n : ℝ) + 1) * (M / N) * S ω)
            have := abs_sub (T0 ω - T ω) (Dx ω)
            have := abs_sub (T0 ω) (T ω)
            linarith
        _ ≤ _ := by rw [e4]; linarith
  -- integrate the pointwise bound
  have iW : Integrable (fun ω => T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω) μ :=
    ((bT0.integrable.sub bT.integrable).sub bDx.integrable).sub (bS.integrable.const_mul _)
  have bSε : BM Sε := by rw [hSε]; exact BM.const_mul _ bS2
  have iInd : Integrable (fun ω => Gc.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hGcm
  have ig : Integrable g μ := by
    rw [hg]
    exact ((bSε.integrable.const_mul _).add (integrable_const _)).add (iInd.const_mul _)
  have k1 : Integrable (fun ω => (gK n * ((δ + M / N) * M * 2) + gK n * (δ * M)) * Sε ω) μ :=
    bSε.integrable.const_mul _
  have k2 : Integrable (fun ω => (gK n * ((δ + M / N) * M * 2) + gK n * (δ * M)) * Sε ω
      + (gK n * ((δ + M / N) * M * (2 * (M / N) ^ 2)) + CdetT n M * (M / N) * (δ + M / N))) μ :=
    k1.add (integrable_const _)
  have k3 : Integrable (fun ω => (2 * N + 2 * M ^ (n + 1) + ((n : ℝ) + 1) * M ^ (n + 2))
      * Gc.indicator (fun _ => (1 : ℝ)) ω) μ := iInd.const_mul _
  have hint := abs_int_le_int iW ig hpt
  have j1 : Integrable (fun ω => T0 ω - T ω) μ := bT0.integrable.sub bT.integrable
  have j2 : Integrable (fun ω => T0 ω - T ω - Dx ω) μ := j1.sub bDx.integrable
  have j3 : Integrable (fun ω => ((n : ℝ) + 1) * (M / N) * S ω) μ := bS.integrable.const_mul _
  rw [integral_sub j2 j3, integral_sub j1 bDx.integrable,
    integral_sub bT0.integrable bT.integrable, integral_const_mul] at hint
  have eg : ∫ ω, g ω ∂μ
      = (gK n * ((δ + M / N) * M * 2) + gK n * (δ * M)) * ∫ ω, Sε ω ∂μ
        + (gK n * ((δ + M / N) * M * (2 * (M / N) ^ 2)) + CdetT n M * (M / N) * (δ + M / N))
        + (2 * N + 2 * M ^ (n + 1) + ((n : ℝ) + 1) * M ^ (n + 2)) * μ.real Gc := by
    rw [hg, integral_add k2 k3, integral_add k1 (integrable_const _),
      integral_const_mul, integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_const (1 : ℝ) hGcm, smul_eq_mul, mul_one]
  rw [eg] at hint
  have hISε : ∫ ω, Sε ω ∂μ ≤ 2 * M ^ 2 / N := by
    rw [hSε, integral_const_mul, H.mean_E2 N]
    have r := H.rs_le hN
    rw [← hMd] at r
    have h1 := mul_le_mul_of_nonneg_left r hNp.le
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ 3)
    refine h2.trans (le_of_eq ?_)
    field_simp
  have hcoefS := mul_le_mul_of_nonneg_left hISε hcoef0
  -- the coefficient
  have hβ : betaNL d σ (n + 1) / N = betaK d σ (n + 1) / N
      - ((n : ℝ) + 1) * (M / N) * (torusM d σ n - torusM d σ (n + 1)) + ite1 := by
    unfold betaNL
    rw [hite1, Nat.add_sub_cancel, ← hMd]
    by_cases h : n = 1
    · subst h; push_cast; field_simp; ring
    · rw [if_neg (by omega : ¬ (n + 1 = 2)), if_neg h]; push_cast; field_simp; ring
  rw [hβ]
  -- the products with `k c`
  have hkc : (0 : ℝ) ≤ ((n : ℝ) + 1) * (M / N) := by positivity
  have p2 : |((n : ℝ) + 1) * (M / N) * (∫ ω, S ω ∂μ - torusM d σ (n + 1))|
      ≤ ((n : ℝ) + 1) * (M / N) * (CSt d σ (n + 1) / N) := by
    rw [abs_mul, abs_of_nonneg hkc]; exact mul_le_mul_of_nonneg_left hE2 hkc
  have p3 : |((n : ℝ) + 1) * (M / N) * (∫ ω, Sn ω ∂μ - torusM d σ n)|
      ≤ ((n : ℝ) + 1) * (M / N) * (CSt d σ n / N) := by
    rw [abs_mul, abs_of_nonneg hkc]; exact mul_le_mul_of_nonneg_left hE3 hkc
  obtain ⟨q1, q2⟩ := abs_le.mp p2
  obtain ⟨q3, q4⟩ := abs_le.mp p3
  obtain ⟨r1, r2⟩ := abs_le.mp hint
  obtain ⟨s1, s2⟩ := abs_le.mp hE1
  obtain ⟨t1, t2⟩ := abs_le.mp hE4
  have eT0 : ∫ ω, ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ = ∫ ω, T0 ω ∂μ := by
    rw [hT0]
  rw [eT0]
  have eErr : errNL d σ N n δ
      = 4 * gK n * δ * M ^ 3 / N
        + gK n * (δ + M / N) * M * (4 * M ^ 2 / N + 2 * (M / N) ^ 2)
        + CdetT n M * (M / N) * (δ + M / N)
        + Ctot d σ n / (N : ℝ) ^ 2
        + ((n : ℝ) + 1) * (M / N) * (CSt d σ n / N) + ((n : ℝ) + 1) * (M / N) * (CSt d σ (n + 1) / N)
        + (M / N) ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M) := by
    unfold errNL; rw [← hMd]; field_simp; ring
  rw [← hGc] at hE1
  rw [eErr, ← hMd]
  have key : ∫ ω, T0 ω ∂μ - (torusM d σ (n + 1) + (betaK d σ (n + 1) / N
        - ((n : ℝ) + 1) * (M / N) * (torusM d σ n - torusM d σ (n + 1)) + ite1))
      = (∫ ω, T0 ω ∂μ - ∫ ω, T ω ∂μ - ∫ ω, Dx ω ∂μ - ((n : ℝ) + 1) * (M / N) * ∫ ω, S ω ∂μ)
        + (∫ ω, T ω ∂μ - (torusM d σ (n + 1) + betaK d σ (n + 1) / N))
        + (∫ ω, Dx ω ∂μ + ((n : ℝ) + 1) * (M / N) * ∫ ω, Sn ω ∂μ - ite1)
        - ((n : ℝ) + 1) * (M / N) * (∫ ω, Sn ω ∂μ - torusM d σ n)
        + ((n : ℝ) + 1) * (M / N) * (∫ ω, S ω ∂μ - torusM d σ (n + 1)) := by ring
  rw [key]
  have tri : ∀ a b c e f : ℝ, |a + b + c - e + f| ≤ |a| + |b| + |c| + |e| + |f| := by
    intro a b c e f
    have h1 := abs_add_le (a + b + c - e) f
    have h2 := abs_sub (a + b + c) e
    have h3 := abs_add_le (a + b) c
    have h4 := abs_add_le a b
    linarith
  refine (tri _ _ _ _ _).trans ?_
  refine (add_le_add (add_le_add (add_le_add (add_le_add hint hE1) hE4) p3) p2).trans ?_
  have fin : (gK n * ((δ + M / N) * M * 2) + gK n * (δ * M)) * (2 * M ^ 2 / N)
        + (gK n * ((δ + M / N) * M * (2 * (M / N) ^ 2)) + CdetT n M * (M / N) * (δ + M / N))
        + (2 * N + 2 * M ^ (n + 1) + ((n : ℝ) + 1) * M ^ (n + 2)) * μ.real Gc
        + (2 * gK n * δ * M ^ 3 / N + Ctot d σ n / (N : ℝ) ^ 2 + (N + CQT d σ n) * μ.real Gc)
        + (M / N) ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M)
        + ((n : ℝ) + 1) * (M / N) * (CSt d σ n / N)
        + ((n : ℝ) + 1) * (M / N) * (CSt d σ (n + 1) / N)
      = 4 * gK n * δ * M ^ 3 / N
          + gK n * (δ + M / N) * M * (4 * M ^ 2 / N + 2 * (M / N) ^ 2)
          + CdetT n M * (M / N) * (δ + M / N)
          + Ctot d σ n / (N : ℝ) ^ 2
          + ((n : ℝ) + 1) * (M / N) * (CSt d σ n / N)
          + ((n : ℝ) + 1) * (M / N) * (CSt d σ (n + 1) / N)
          + (M / N) ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M)
        + (3 * N + CQT d σ n + 2 * M ^ (n + 1) + ((n : ℝ) + 1) * M ^ (n + 2)) * μ.real Gc := by
    ring
  rw [← fin]
  linarith [hcoefS]

end Final2

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`prop:bias` for the graph without self-loops, every `k = n + 1 ≥ 2`, sample form.** Under
    the hypotheses of `norm_sample` (`σ ≤ 1`, `d ≥ 1`, `N ≥ 2`, `kernelC1 d · δ' ≤ 1`,
    `δ' = √(m₁ log N / N)`) and, ADDITIONALLY, `normC d · δ' + m₁/N ≤ 1/8`:
    `|E Tr P°^k - m_k - β°_k/N| ≤ errNL(normC δ') + (3N + CQT + 2 m₁^k + k m₁^{k+1})/N³`. -/
theorem bias_noloops_sample [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1)
    (hu : TorusReductionL1.normC d * δp + torusM d σ 1 / N ≤ 1 / 8)
    (n : ℕ) (hn : 1 ≤ n) :
    |∫ ω, ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - (torusM d σ (n + 1) + betaNL d σ (n + 1) / N)|
      ≤ errNL d σ N n (TorusReductionL1.normC d * δp)
        + (3 * N + CQT d σ n + 2 * torusM d σ 1 ^ (n + 1) + ((n : ℝ) + 1) * torusM d σ 1 ^ (n + 2))
          * (1 / (N : ℝ) ^ 3) := by
  have hr : kernelC1 d * δp * Real.sqrt ((1 : ℕ) : ℝ) ≤ 1 := by
    rw [Nat.cast_one, Real.sqrt_one, mul_one]; exact hrange
  obtain ⟨_, hp⟩ := TorusReductionL1.norm_sample hσ hσ1 d hd X h_indep hX hlaw N 1 hN2
    Nat.one_pos hMp hδp hr
  have hδ0 : 0 ≤ TorusReductionL1.normC d * δp := by
    rw [hδp]; exact mul_nonneg (TorusReductionL1.normC_nonneg d) (Real.sqrt_nonneg _)
  have h := bias_noloops_general X h_indep hX hlaw hσ N (by omega) hδ0 hu n hn
  have hM := torusM_one_ge hσ d
  have hc : (0 : ℝ) ≤ 3 * N + CQT d σ n + 2 * torusM d σ 1 ^ (n + 1)
      + ((n : ℝ) + 1) * torusM d σ 1 ^ (n + 2) := by
    have := B4_nonneg hσ d n
    unfold CQT; positivity
  have := mul_le_mul_of_nonneg_left hp hc
  linarith only [h, this]

end Sample

end BiasNoLoops

namespace VarianceGeneral3

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open BiasGeneral BiasGeneral2 BiasGeneral4 BiasGeneral5 BiasGeneral6

/-! # A105 (1): `QT` as a combination of tuple statistics of translation-invariant kernels -/

section Reindex

variable {G : Type*}

/-- `∑_{ι : Fin (s+1) → Fin N} g ι = ∑_u ∑_w g (cons u w)`. -/
theorem sum_cons_split {N s : ℕ} (g : (Fin (s + 1) → Fin N) → ℝ) :
    ∑ ι : Fin (s + 1) → Fin N, g ι = ∑ u : Fin N, ∑ w : Fin s → Fin N, g (Fin.cons u w) := by
  rw [← (Fin.consEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The kernel of a statistic `∑_w ∑_u Φ(x_w, x_u)`. -/
def K1 {s : ℕ} (Φ : (Fin s → G) × G → ℝ) (y : Fin (s + 1) → G) : ℝ := Φ (Fin.tail y, y 0)

/-- The kernel of a statistic `∑_w ∑_u ∑_{u'} Φ(x_w, x_u, x_{u'})`. -/
def K2 {s : ℕ} (Φ : (Fin s → G) × G × G → ℝ) (y : Fin (s + 2) → G) : ℝ :=
  Φ (Fin.tail (Fin.tail y), y 0, y 1)

variable {Ω : Type*}

theorem sAll_K1 (X : ℕ → Ω → G) (N : ℕ) {s : ℕ} (Φ : (Fin s → G) × G → ℝ) (ω : Ω) :
    sAll X N (K1 Φ) ω = ∑ w : Fin s → Fin N, ∑ u : Fin N, Φ (fun a => X (w a) ω, X u ω) := by
  unfold sAll
  rw [sum_cons_split, Finset.sum_comm]
  rfl

theorem sAll_K2 (X : ℕ → Ω → G) (N : ℕ) {s : ℕ} (Φ : (Fin s → G) × G × G → ℝ) (ω : Ω) :
    sAll X N (K2 Φ) ω
      = ∑ w : Fin s → Fin N, ∑ u : Fin N, ∑ u' : Fin N, Φ (fun a => X (w a) ω, X u ω, X u' ω) := by
  unfold sAll
  rw [sum_cons_split]
  simp_rw [sum_cons_split]
  calc _ = ∑ u : Fin N, ∑ u' : Fin N, ∑ w : Fin s → Fin N,
        Φ (fun a => X (w a) ω, X u ω, X u' ω) := rfl
    _ = ∑ u : Fin N, ∑ w : Fin s → Fin N, ∑ u' : Fin N,
        Φ (fun a => X (w a) ω, X u ω, X u' ω) :=
      Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

end Reindex

section TIsec

variable {G : Type*} [AddCommGroup G]

/-- Translation invariance of a kernel with one extra point. -/
def TI1 {s : ℕ} (Φ : (Fin s → G) × G → ℝ) : Prop :=
  ∀ (y : Fin s → G) (z c : G), Φ (fun i => y i + c, z + c) = Φ (y, z)

/-- Translation invariance of a kernel with two extra points. -/
def TI2 {s : ℕ} (Φ : (Fin s → G) × G × G → ℝ) : Prop :=
  ∀ (y : Fin s → G) (z z' c : G), Φ (fun i => y i + c, z + c, z' + c) = Φ (y, z, z')

theorem K1_TI {s : ℕ} {Φ : (Fin s → G) × G → ℝ} (h : TI1 Φ) : VarianceGeneral2.TI (K1 Φ) :=
  fun y c => h (Fin.tail y) (y 0) c

theorem K2_TI {s : ℕ} {Φ : (Fin s → G) × G × G → ℝ} (h : TI2 Φ) : VarianceGeneral2.TI (K2 Φ) :=
  fun y c => h (Fin.tail (Fin.tail y)) (y 0) (y 1) c

end TIsec

section TorusKernels

variable {d : ℕ} {σ : ℝ}

theorem cyT_TI {n : ℕ} (y : Fin (n + 1) → FlatTorus d) (c : FlatTorus d) :
    cyT d σ (fun i => y i + c) = cyT d σ y := by
  unfold cyT cycP; simp only [add_sub_add_right_eq_sub]

theorem cy2_TI {n : ℕ} (y : Fin (n + 2) → FlatTorus d) (c : FlatTorus d) :
    cy2 d σ (fun i => y i + c) = cy2 d σ y := by
  unfold cy2; exact cyT_TI (fun a : Fin (n + 1) => y a.castSucc) c

theorem cy3_TI {n : ℕ} (y : Fin (n + 3) → FlatTorus d) (c : FlatTorus d) :
    cy3 d σ (fun i => y i + c) = cy3 d σ y := by
  unfold cy3; exact cyT_TI (fun a : Fin (n + 1) => y a.castSucc.castSucc) c

theorem PhiA_TI (n : ℕ) : TI1 (PhiA d σ n) := fun y z c => by
  unfold PhiA; simp only [add_sub_add_right_eq_sub]; rw [cyT_TI]

theorem PhiB_TI (n : ℕ) : TI1 (PhiB d σ n) := fun y z c => by
  unfold PhiB; simp only [add_sub_add_right_eq_sub]
  rw [cyT_TI (fun i : Fin (n + 1) => y i.castSucc)]

theorem PhiEE_TI (n : ℕ) : TI2 (PhiEE d σ n) := fun y z z' c => by
  unfold PhiEE; simp only [add_sub_add_right_eq_sub]; rw [cyT_TI]

theorem PhiEB_TI (n : ℕ) : TI2 (PhiEB d σ n) := fun y z z' c => by
  unfold PhiEB; simp only [add_sub_add_right_eq_sub]; rw [cy2_TI]

theorem PhiS_TI (n : ℕ) : TI2 (PhiS d σ n) := fun y z z' c => by
  unfold PhiS; simp only [add_sub_add_right_eq_sub]; rw [cy2_TI]

theorem PhiBB_TI (n : ℕ) : TI2 (PhiBB d σ n) := fun y z z' c => by
  unfold PhiBB; simp only [add_sub_add_right_eq_sub]; rw [cy3_TI]

theorem PhiQee_TI (n : ℕ) (l : Fin (n + 1)) : TI2 (PhiQee d σ n l) := fun y z z' c => by
  unfold PhiQee; simp only [add_sub_add_right_eq_sub]; rw [cyT_TI]

theorem PhiQeb_TI (n : ℕ) (l : Fin (n + 1)) : TI2 (PhiQeb d σ n l) := fun y z z' c => by
  unfold PhiQeb; simp only [add_sub_add_right_eq_sub]; rw [cy2_TI]

theorem PhiQbe_TI (n : ℕ) (l : Fin (n + 1)) : TI2 (PhiQbe d σ n l) := fun y z z' c => by
  unfold PhiQbe; simp only [add_sub_add_right_eq_sub]; rw [cy2_TI]

theorem PhiQbb_TI (n : ℕ) (l : Fin (n + 1)) : TI2 (PhiQbb d σ n l) := fun y z z' c => by
  unfold PhiQbb; simp only [add_sub_add_right_eq_sub]; rw [cy3_TI]

end TorusKernels




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open BiasGeneral BiasGeneral2 BiasGeneral4 BiasGeneral5 BiasGeneral6

section Bounds

variable {G : Type*} [MeasurableSpace G]

theorem K1_bm {s : ℕ} {Φ : (Fin s → G) × G → ℝ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ p, |Φ p| ≤ C) : BM (K1 Φ) ∧ ∀ y, |K1 Φ y| ≤ C :=
  ⟨⟨hΦ.comp ((measurable_pi_lambda _ fun i => measurable_pi_apply _).prodMk
      (measurable_pi_apply 0)), C, fun y => hC _⟩, fun y => hC _⟩

theorem K2_bm {s : ℕ} {Φ : (Fin s → G) × G × G → ℝ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ p, |Φ p| ≤ C) : BM (K2 Φ) ∧ ∀ y, |K2 Φ y| ≤ C :=
  ⟨⟨hΦ.comp ((measurable_pi_lambda _ fun i => measurable_pi_apply _).prodMk
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))), C, fun y => hC _⟩,
    fun y => hC _⟩

end Bounds

section QTStat

variable {d : ℕ} {σ : ℝ}

theorem cyT_le_B4 (hσ : 0 < σ) (n : ℕ) (y : Fin (n + 1) → FlatTorus d) :
    |cyT d σ y| ≤ B4 d σ n := by
  have hM := torusM_one_ge hσ d
  rw [abs_of_nonneg (cyT_bounds hσ d y).1]
  refine (cyT_bounds hσ d y).2.trans ?_
  unfold B4
  have h1 : (1 : ℝ) ≤ torusM d σ 1 ^ 4 := one_le_pow₀ hM
  have h0 : 0 ≤ torusM d σ 1 ^ (n + 1) := by positivity
  nlinarith

theorem PhiA_le_B4 (hσ : 0 < σ) (n : ℕ) (p : (Fin (n + 1) → FlatTorus d) × FlatTorus d) :
    |PhiA d σ n p| ≤ B4 d σ n := by
  have hM := torusM_one_ge hσ d
  unfold PhiA
  rw [abs_mul, abs_of_nonneg (cyT_bounds hσ d p.1).1]
  have h1 := mul_le_mul (cyT_bounds hσ d p.1).2 (cK_bound hσ d (p.1 0 - p.2)) (abs_nonneg _)
    (by positivity)
  refine h1.trans ?_
  unfold B4
  have h2 : torusM d σ 1 ≤ torusM d σ 1 ^ 4 := by
    calc torusM d σ 1 = torusM d σ 1 ^ 1 := (pow_one _).symm
      _ ≤ torusM d σ 1 ^ 4 := pow_le_pow_right₀ hM (by norm_num)
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

theorem PhiB_le_B4 (hσ : 0 < σ) (n : ℕ) (p : (Fin (n + 2) → FlatTorus d) × FlatTorus d) :
    |PhiB d σ n p| ≤ B4 d σ n := by
  have hM := torusM_one_ge hσ d
  unfold PhiB
  rw [abs_mul, abs_mul, abs_of_nonneg (cyT_bounds hσ d _).1,
    abs_of_nonneg (heatP_nonneg hσ d 1 _)]
  have h1 := mul_le_mul (mul_le_mul (cyT_bounds hσ d (fun i : Fin (n + 1) => p.1 i.castSucc)).2
      (heatP_le hσ d le_rfl (p.1 0 - p.1 (Fin.last (n + 1))))
      (heatP_nonneg hσ d 1 _) (by positivity))
      (cK_bound hσ d (p.1 (Fin.last (n + 1)) - p.2)) (abs_nonneg _) (by positivity)
  refine h1.trans ?_
  unfold B4
  have h2 : torusM d σ 1 * torusM d σ 1 ≤ torusM d σ 1 ^ 4 := by
    calc torusM d σ 1 * torusM d σ 1 = torusM d σ 1 ^ 2 := by ring
      _ ≤ torusM d σ 1 ^ 4 := pow_le_pow_right₀ hM (by norm_num)
  have h0 : 0 ≤ torusM d σ 1 ^ (n + 1) := by positivity
  calc torusM d σ 1 ^ (n + 1) * torusM d σ 1 * torusM d σ 1
      = torusM d σ 1 ^ (n + 1) * (torusM d σ 1 * torusM d σ 1) := by ring
    _ ≤ torusM d σ 1 ^ (n + 1) * torusM d σ 1 ^ 4 := mul_le_mul_of_nonneg_left h2 h0

variable {Ω : Type*}

/-- **`QT` as a combination of normalised tuple statistics** (every `k = n + 1`). -/
theorem QT_eq_stat (N n : ℕ) (X : ℕ → Ω → FlatTorus d) (ω : Ω) :
    QT d σ N n (fun j => X j ω)
      = 1 / (N : ℝ) ^ (n + 1) * sAll X N (cyT d σ (n := n)) ω
        + ((n : ℝ) + 1) * (-2 * (1 / (N : ℝ) ^ (n + 1 + 1) * sAll X N (K1 (PhiA d σ n)) ω)
          + 1 / (N : ℝ) ^ (n + 2 + 1) * sAll X N (K1 (PhiB d σ n)) ω
          + 3 * (1 / (N : ℝ) ^ (n + 1 + 2) * sAll X N (K2 (PhiEE d σ n)) ω)
          - 3 * (1 / (N : ℝ) ^ (n + 2 + 2) * sAll X N (K2 (PhiEB d σ n)) ω)
          + 1 / (N : ℝ) ^ (n + 3 + 2) * sAll X N (K2 (PhiBB d σ n)) ω
          - 1 / (N : ℝ) ^ (n + 2 + 2) * sAll X N (K2 (PhiS d σ n)) ω)
        + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
            (4 * (1 / (N : ℝ) ^ (n + 1 + 2) * sAll X N (K2 (PhiQee d σ n l)) ω)
              - 2 * (1 / (N : ℝ) ^ (n + 2 + 2) * sAll X N (K2 (PhiQeb d σ n l)) ω)
              - 2 * (1 / (N : ℝ) ^ (n + 2 + 2) * sAll X N (K2 (PhiQbe d σ n l)) ω)
              + 1 / (N : ℝ) ^ (n + 3 + 2) * sAll X N (K2 (PhiQbb d σ n l)) ω) := by
  unfold QT gA gB g3
  simp only [sAll_K1, sAll_K2]
  unfold sAll
  ring

end QTStat




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open BiasGeneral BiasGeneral2 BiasGeneral4 BiasGeneral5 BiasGeneral6

section SoffLin

variable {Ω G : Type*} [AddCommGroup G]

theorem Soff_add (f g : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Soff (fun u => f u + g u) X N ω = Soff f X N ω + Soff g X N ω := by
  unfold Soff
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aT; split_ifs <;> ring

theorem Soff_sub (f g : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Soff (fun u => f u - g u) X N ω = Soff f X N ω - Soff g X N ω := by
  unfold Soff
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aT; split_ifs <;> ring

theorem Soff_mul (a : ℝ) (f : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Soff (fun u => a * f u) X N ω = a * Soff f X N ω :=
  VarianceGeneral.Soff_smul a f X N ω

theorem Soff_fsum {κ : Type*} (s : Finset κ) (f : κ → G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Soff (fun u => ∑ l ∈ s, f l u) X N ω = ∑ l ∈ s, Soff (f l) X N ω := by
  unfold Soff
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm (s := s)]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold aT; split_ifs
  · simp
  · rfl

theorem Soff_bm [MeasurableSpace G] [MeasurableSub₂ G] {mΩ : MeasurableSpace Ω}
    {X : ℕ → Ω → G} (hX : ∀ j, Measurable (X j)) {h : G → ℝ} (hm : Measurable h) {C : ℝ}
    (hC : ∀ y, |h y| ≤ C) (N : ℕ) : BM (Soff h X N) := by
  refine BM.sum _ _ fun i _ => BM.sum _ _ fun j _ => ?_
  by_cases hij : i = j
  · have e : aT h X i j = fun _ => (0 : ℝ) := by funext ω; simp [aT, hij]
    rw [e]; exact BM.const 0
  · have e : aT h X i j = fun ω => h (X i ω - X j ω) := by funext ω; simp [aT, hij]
    rw [e]
    exact ⟨hm.comp ((hX i).sub (hX j)), C, fun ω => hC _⟩

end SoffLin

section HpairBM

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] {ν : Measure G}

theorem hpair_bm [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) {B : ℝ}
    (hB : ∀ x, |F x| ≤ B) :
    Measurable (VarianceGeneral2.hpair ν F)
      ∧ ∀ y, |VarianceGeneral2.hpair ν F y| ≤ (VarianceGeneral2.pairs n).card * (2 * B) := by
  constructor
  · unfold VarianceGeneral2.hpair
    exact Finset.measurable_sum _ fun p _ =>
      ((VarianceGeneral2.AW_bm _ hF).meas.comp (measurable_update 0)).sub measurable_const
  · intro y
    unfold VarianceGeneral2.hpair
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ p ∈ VarianceGeneral2.pairs n,
        |VarianceGeneral2.AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F (Function.update 0 p.1 y)
          - VarianceGeneral2.AW ν Finset.univ F 0| ≤ 2 * B := fun p _ => by
      have a1 := VarianceGeneral2.AW_bound (ν := ν) ({p.1, p.2} : Finset (Fin n))ᶜ hB
        (Function.update 0 p.1 y)
      have a2 := VarianceGeneral2.AW_bound (ν := ν) (Finset.univ : Finset (Fin n)) hB 0
      calc _ ≤ |VarianceGeneral2.AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F (Function.update 0 p.1 y)|
            + |VarianceGeneral2.AW ν Finset.univ F 0| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]

theorem pairs_card_le (n : ℕ) : ((VarianceGeneral2.pairs n).card : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h : (VarianceGeneral2.pairs n).card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h
  have : ((VarianceGeneral2.pairs n).card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast h
  rw [Nat.cast_mul] at this; nlinarith

end HpairBM

/-! ## One block: `D_F = N^{-a} ∑_ι F(X_ι) - N^{-2} ∑_{i≠j} h_F(X_i - X_j)` -/

section Block

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The pair kernel on the flat torus. -/
noncomputable def hp {d a : ℕ} (F : (Fin a → FlatTorus d) → ℝ) : FlatTorus d → ℝ :=
  VarianceGeneral2.hpair (flatTorusMeasure d) F

/-- The block statistic minus its pair projection. -/
noncomputable def Dblk {d a : ℕ} (F : (Fin a → FlatTorus d) → ℝ) (X : ℕ → Ω → FlatTorus d)
    (N : ℕ) (ω : Ω) : ℝ :=
  1 / (N : ℝ) ^ a * sAll X N F ω - 1 / (N : ℝ) ^ 2 * Soff (hp F) X N ω

/-- The constant `10 (n+5)⁶ 16^{n+5}` (arity at most `n + 5`). -/
noncomputable def cA (n : ℕ) : ℝ := 10 * ((n : ℝ) + 5) ^ 6 * 16 ^ (n + 5)

theorem cA_nonneg (n : ℕ) : 0 ≤ cA n := by unfold cA; positivity

theorem block_var [IsProbabilityMeasure μ] {d : ℕ} {X : ℕ → Ω → FlatTorus d}
    (H : SP μ (flatTorusMeasure d) X) {N : ℕ} (hN : 0 < N) (n : ℕ) {a : ℕ} (ha : a ≤ n + 5)
    {F : (Fin a → FlatTorus d) → ℝ} (hF : BM F) {B : ℝ} (hB : ∀ x, |F x| ≤ B)
    (hT : VarianceGeneral2.TI F) :
    BM (Dblk F X N) ∧ cv μ (Dblk F X N) ≤ cA n * B ^ 2 / (N : ℝ) ^ 3 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hm, hb⟩ := hpair_bm (ν := flatTorusMeasure d) hF hB
  refine ⟨(BM.const_mul _ (H.sAll_bm N hF)).sub (BM.const_mul _ (Soff_bm H.meas hm hb N)), ?_⟩
  have h := VarianceGeneral2.pair_projection H (VarianceGeneral2.torus_hinv d) hN hF hB hT
  refine h.trans ?_
  have hc : 10 * (a : ℝ) ^ 6 * 16 ^ a ≤ cA n := by
    unfold cA
    have h1 : (a : ℝ) ≤ (n : ℝ) + 5 := by exact_mod_cast ha
    have h2 : (a : ℝ) ^ 6 ≤ ((n : ℝ) + 5) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 6
    have h3 : (16 : ℝ) ^ a ≤ 16 ^ (n + 5) := pow_le_pow_right₀ (by norm_num) ha
    have := mul_le_mul h2 h3 (by positivity) (by positivity)
    nlinarith
  have hB2 : 0 ≤ B ^ 2 / (N : ℝ) ^ 3 := by positivity
  have := mul_le_mul_of_nonneg_right hc hB2
  calc 10 * (a : ℝ) ^ 6 * 16 ^ a * B ^ 2 / (N : ℝ) ^ 3
      = 10 * (a : ℝ) ^ 6 * 16 ^ a * (B ^ 2 / (N : ℝ) ^ 3) := by ring
    _ ≤ cA n * (B ^ 2 / (N : ℝ) ^ 3) := this
    _ = cA n * B ^ 2 / (N : ℝ) ^ 3 := by ring

end Block

/-! ## variance arithmetic -/

section CvArith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {f g : Ω → ℝ}

theorem cv_add_bd (hf : BM f) (hg : BM g) {a b : ℝ} (ha : cv μ f ≤ a) (hb : cv μ g ≤ b) :
    cv μ (fun ω => f ω + g ω) ≤ 2 * a + 2 * b := by
  have := cv_add_le (μ := μ) hf hg; linarith

theorem cv_sub_bd (hf : BM f) (hg : BM g) {a b : ℝ} (ha : cv μ f ≤ a) (hb : cv μ g ≤ b) :
    cv μ (fun ω => f ω - g ω) ≤ 2 * a + 2 * b := by
  have e : (fun ω => f ω - g ω) = fun ω => f ω + (-1) * g ω := by funext ω; ring
  rw [e]
  have h2 : cv μ (fun ω => (-1) * g ω) ≤ b := by rw [cv_const_mul]; norm_num; exact hb
  exact cv_add_bd hf (BM.const_mul _ hg) ha h2

theorem cv_mul_bd (c : ℝ) {a : ℝ} (ha : cv μ f ≤ a) : cv μ (fun ω => c * f ω) ≤ c ^ 2 * a := by
  rw [cv_const_mul]; exact mul_le_mul_of_nonneg_left ha (_root_.sq_nonneg c)

end CvArith




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open BiasGeneral BiasGeneral2 BiasGeneral4 BiasGeneral5 BiasGeneral6

section QTpair

variable {d : ℕ} {σ : ℝ}

/-- **The pair kernel of `QT`** (every `k = n + 1`): the same linear combination of the pair kernels
    `hpair` of the blocks as in `QT_eq_stat`. -/
noncomputable def hQT (d : ℕ) (σ : ℝ) (n : ℕ) (u : FlatTorus d) : ℝ :=
  hp (cyT d σ (n := n)) u
    + ((n : ℝ) + 1) * (-2 * hp (K1 (PhiA d σ n)) u + hp (K1 (PhiB d σ n)) u
      + 3 * hp (K2 (PhiEE d σ n)) u - 3 * hp (K2 (PhiEB d σ n)) u
      + hp (K2 (PhiBB d σ n)) u - hp (K2 (PhiS d σ n)) u)
    + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
        (4 * hp (K2 (PhiQee d σ n l)) u - 2 * hp (K2 (PhiQeb d σ n l)) u
          - 2 * hp (K2 (PhiQbe d σ n l)) u + hp (K2 (PhiQbb d σ n l)) u)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

theorem Soff_hQT (n : ℕ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    Soff (hQT d σ n) X N ω
      = Soff (hp (cyT d σ (n := n))) X N ω
        + ((n : ℝ) + 1) * (-2 * Soff (hp (K1 (PhiA d σ n))) X N ω + Soff (hp (K1 (PhiB d σ n))) X N ω
          + 3 * Soff (hp (K2 (PhiEE d σ n))) X N ω - 3 * Soff (hp (K2 (PhiEB d σ n))) X N ω
          + Soff (hp (K2 (PhiBB d σ n))) X N ω - Soff (hp (K2 (PhiS d σ n))) X N ω)
        + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
            (4 * Soff (hp (K2 (PhiQee d σ n l))) X N ω - 2 * Soff (hp (K2 (PhiQeb d σ n l))) X N ω
              - 2 * Soff (hp (K2 (PhiQbe d σ n l))) X N ω + Soff (hp (K2 (PhiQbb d σ n l))) X N ω) := by
  unfold hQT
  simp only [Soff_add, Soff_sub, Soff_mul, Soff_fsum]

/-- **`QT - N⁻² ∑_{i≠j} h_QT(X_i - X_j)` is the same combination of the block remainders.** -/
theorem QT_sub_eq (n : ℕ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    QT d σ N n (fun j => X j ω) - 1 / (N : ℝ) ^ 2 * Soff (hQT d σ n) X N ω
      = Dblk (cyT d σ (n := n)) X N ω
        + ((n : ℝ) + 1) * (-2 * Dblk (K1 (PhiA d σ n)) X N ω + Dblk (K1 (PhiB d σ n)) X N ω
          + 3 * Dblk (K2 (PhiEE d σ n)) X N ω - 3 * Dblk (K2 (PhiEB d σ n)) X N ω
          + Dblk (K2 (PhiBB d σ n)) X N ω - Dblk (K2 (PhiS d σ n)) X N ω)
        + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
            (4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
              - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω) := by
  rw [QT_eq_stat, Soff_hQT]
  have key : ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
        (4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
          - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω)
      = ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
          (4 * (1 / (N : ℝ) ^ (n + 1 + 2) * sAll X N (K2 (PhiQee d σ n l)) ω)
            - 2 * (1 / (N : ℝ) ^ (n + 2 + 2) * sAll X N (K2 (PhiQeb d σ n l)) ω)
            - 2 * (1 / (N : ℝ) ^ (n + 2 + 2) * sAll X N (K2 (PhiQbe d σ n l)) ω)
            + 1 / (N : ℝ) ^ (n + 3 + 2) * sAll X N (K2 (PhiQbb d σ n l)) ω)
        - 1 / (N : ℝ) ^ 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
            (4 * Soff (hp (K2 (PhiQee d σ n l))) X N ω - 2 * Soff (hp (K2 (PhiQeb d σ n l))) X N ω
              - 2 * Soff (hp (K2 (PhiQbe d σ n l))) X N ω
              + Soff (hp (K2 (PhiQbb d σ n l))) X N ω) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    unfold Dblk; ring
  unfold Dblk at key ⊢
  linear_combination (-(((n : ℝ) + 1) / 2)) * key

/-- The constant of `QT_pair`. -/
noncomputable def Cq (n : ℕ) : ℝ :=
  4 + 1528 * ((n : ℝ) + 1) ^ 2 + 89 * ((n : ℝ) + 1) ^ 2 * (n : ℝ) ^ 2

/-- **(1): `Var(QT - N⁻² ∑_{i≠j} h_QT(X_i - X_j)) = O(N⁻³)` for every `k = n + 1`**, with
    `R = Cq n · cA n · B4² / N³` (independent uniform points on the flat torus, `N ≥ 1`). -/
theorem QT_pair [IsProbabilityMeasure μ] (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) (n : ℕ) :
    BM (fun ω => QT d σ N n (fun j => X j ω) - 1 / (N : ℝ) ^ 2 * Soff (hQT d σ n) X N ω)
    ∧ cv μ (fun ω => QT d σ N n (fun j => X j ω) - 1 / (N : ℝ) ^ 2 * Soff (hQT d σ n) X N ω)
      ≤ Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3) := by
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3 := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 ≤ r := by rw [hr]; have := cA_nonneg n; positivity
  have hPB := fun l => phi_bounds hσ d n l
  -- the blocks
  obtain ⟨b0, v0⟩ := block_var H hN n (a := n + 1) (by omega) (F := cyT d σ (n := n))
    ⟨cyT_meas hσ d n, _, cyT_le_B4 hσ n⟩ (cyT_le_B4 hσ n) (fun y c => cyT_TI y c)
  obtain ⟨kA, kAb⟩ := K1_bm (PhiA_meas hσ d n) (PhiA_le_B4 hσ n)
  obtain ⟨bA, vA⟩ := block_var H hN n (by omega) kA kAb (K1_TI (PhiA_TI n))
  obtain ⟨kB, kBb⟩ := K1_bm (PhiB_meas hσ d n) (PhiB_le_B4 hσ n)
  obtain ⟨bB, vB⟩ := block_var H hN n (by omega) kB kBb (K1_TI (PhiB_TI n))
  obtain ⟨kEE, kEEb⟩ := K2_bm (PhiEE_meas hσ d n) (hPB 0).1
  obtain ⟨bEE, vEE⟩ := block_var H hN n (by omega) kEE kEEb (K2_TI (PhiEE_TI n))
  obtain ⟨kEB, kEBb⟩ := K2_bm (PhiEB_meas hσ d n) (hPB 0).2.1
  obtain ⟨bEB, vEB⟩ := block_var H hN n (by omega) kEB kEBb (K2_TI (PhiEB_TI n))
  obtain ⟨kBB, kBBb⟩ := K2_bm (PhiBB_meas hσ d n) (hPB 0).2.2.1
  obtain ⟨bBB, vBB⟩ := block_var H hN n (by omega) kBB kBBb (K2_TI (PhiBB_TI n))
  obtain ⟨kS, kSb⟩ := K2_bm (PhiS_meas hσ d n) (hPB 0).2.2.2.1
  obtain ⟨bS, vS⟩ := block_var H hN n (by omega) kS kSb (K2_TI (PhiS_TI n))
  have bl : ∀ l : Fin (n + 1),
      (BM (Dblk (K2 (PhiQee d σ n l)) X N) ∧ cv μ (Dblk (K2 (PhiQee d σ n l)) X N) ≤ r)
      ∧ (BM (Dblk (K2 (PhiQeb d σ n l)) X N) ∧ cv μ (Dblk (K2 (PhiQeb d σ n l)) X N) ≤ r)
      ∧ (BM (Dblk (K2 (PhiQbe d σ n l)) X N) ∧ cv μ (Dblk (K2 (PhiQbe d σ n l)) X N) ≤ r)
      ∧ (BM (Dblk (K2 (PhiQbb d σ n l)) X N) ∧ cv μ (Dblk (K2 (PhiQbb d σ n l)) X N) ≤ r) := by
    intro l
    rw [hr]
    obtain ⟨k1, k1b⟩ := K2_bm (PhiQee_meas hσ d n l) (hPB l).2.2.2.2.1
    obtain ⟨k2, k2b⟩ := K2_bm (PhiQeb_meas hσ d n l) (hPB l).2.2.2.2.2.1
    obtain ⟨k3, k3b⟩ := K2_bm (PhiQbe_meas hσ d n l) (hPB l).2.2.2.2.2.2.1
    obtain ⟨k4, k4b⟩ := K2_bm (PhiQbb_meas hσ d n l) (hPB l).2.2.2.2.2.2.2
    exact ⟨block_var H hN n (by omega) k1 k1b (K2_TI (PhiQee_TI n l)),
      block_var H hN n (by omega) k2 k2b (K2_TI (PhiQeb_TI n l)),
      block_var H hN n (by omega) k3 k3b (K2_TI (PhiQbe_TI n l)),
      block_var H hN n (by omega) k4 k4b (K2_TI (PhiQbb_TI n l))⟩
  rw [← hr] at v0 vA vB vEE vEB vBB vS
  -- the first group
  have g1 := cv_mul_bd (μ := μ) (-2) vA
  have g2 := cv_add_bd (BM.const_mul (-2) bA) bB g1 vB
  have g3 := cv_add_bd ((BM.const_mul (-2) bA).add bB) (BM.const_mul 3 bEE) g2
    (cv_mul_bd (μ := μ) 3 vEE)
  have g4 := cv_sub_bd (((BM.const_mul (-2) bA).add bB).add (BM.const_mul 3 bEE))
    (BM.const_mul 3 bEB) g3 (cv_mul_bd (μ := μ) 3 vEB)
  have bG4 := ((((BM.const_mul (-2) bA).add bB).add (BM.const_mul 3 bEE)).sub
    (BM.const_mul 3 bEB))
  have g5 := cv_add_bd bG4 bBB g4 vBB
  have g6 := cv_sub_bd (bG4.add bBB) bS g5 vS
  have bG1 := (bG4.add bBB).sub bS
  -- the second group, for each `l`
  have gl : ∀ l : Fin (n + 1),
      BM (fun ω => 4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
        - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω)
      ∧ cv μ (fun ω => 4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
        - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω) ≤ 178 * r := by
    intro l
    obtain ⟨⟨b1, v1⟩, ⟨b2, v2⟩, ⟨b3, v3⟩, ⟨b4, v4⟩⟩ := bl l
    have h1 := cv_sub_bd (BM.const_mul 4 b1) (BM.const_mul 2 b2) (cv_mul_bd (μ := μ) 4 v1)
      (cv_mul_bd (μ := μ) 2 v2)
    have h2 := cv_sub_bd ((BM.const_mul 4 b1).sub (BM.const_mul 2 b2)) (BM.const_mul 2 b3) h1
      (cv_mul_bd (μ := μ) 2 v3)
    have h3 := cv_add_bd (((BM.const_mul 4 b1).sub (BM.const_mul 2 b2)).sub (BM.const_mul 2 b3))
      b4 h2 v4
    refine ⟨(((BM.const_mul 4 b1).sub (BM.const_mul 2 b2)).sub (BM.const_mul 2 b3)).add b4,
      h3.trans (le_of_eq (by ring))⟩
  have bG2 : BM (fun ω => ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
        - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω)) :=
    BM.sum _ _ fun l _ => (gl l).1
  have vG2 := cv_sum_le (μ := μ) (Finset.univ.erase (0 : Fin (n + 1)))
    (fun l ω => 4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
        - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω)
    (fun l => (gl l).1)
  have hE : ((Finset.univ.erase (0 : Fin (n + 1))).card : ℝ) = n := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    push_cast; ring
  have hsum : ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      cv μ (fun ω => 4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
        - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω)
      ≤ n * (178 * r) := by
    have := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ.erase (0 : Fin (n + 1))) => (gl l).2
    rwa [Finset.sum_const, nsmul_eq_mul, hE] at this
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have vG2' : cv μ (fun ω => ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
        - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω))
      ≤ n * (n * (178 * r)) := by
    rw [hE] at vG2
    exact vG2.trans (mul_le_mul_of_nonneg_left hsum hn0)
  -- the total
  have t1 := cv_add_bd b0 (BM.const_mul ((n : ℝ) + 1) bG1) v0
    (cv_mul_bd (μ := μ) ((n : ℝ) + 1) g6)
  have t2 := cv_add_bd (b0.add (BM.const_mul ((n : ℝ) + 1) bG1))
    (BM.const_mul (((n : ℝ) + 1) / 2) bG2) t1 (cv_mul_bd (μ := μ) (((n : ℝ) + 1) / 2) vG2')
  have bT := (b0.add (BM.const_mul ((n : ℝ) + 1) bG1)).add (BM.const_mul (((n : ℝ) + 1) / 2) bG2)
  have e : (fun ω => QT d σ N n (fun j => X j ω) - 1 / (N : ℝ) ^ 2 * Soff (hQT d σ n) X N ω)
      = fun ω => Dblk (cyT d σ (n := n)) X N ω
        + ((n : ℝ) + 1) * (-2 * Dblk (K1 (PhiA d σ n)) X N ω + Dblk (K1 (PhiB d σ n)) X N ω
          + 3 * Dblk (K2 (PhiEE d σ n)) X N ω - 3 * Dblk (K2 (PhiEB d σ n)) X N ω
          + Dblk (K2 (PhiBB d σ n)) X N ω - Dblk (K2 (PhiS d σ n)) X N ω)
        + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
            (4 * Dblk (K2 (PhiQee d σ n l)) X N ω - 2 * Dblk (K2 (PhiQeb d σ n l)) X N ω
              - 2 * Dblk (K2 (PhiQbe d σ n l)) X N ω + Dblk (K2 (PhiQbb d σ n l)) X N ω) :=
    funext fun ω => QT_sub_eq n X N ω
  rw [e]
  refine ⟨bT, t2.trans ?_⟩
  unfold Cq
  rw [← hr]
  exact le_of_eq (by ring)

end QTpair




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open BiasGeneral BiasGeneral2 BiasGeneral4 BiasGeneral5 BiasGeneral6

/-! ## (3): the pair kernel of `QT` is bounded, measurable, of mean zero; its symmetrisation gives a
degenerate two-point statistic with exact variance; the unconditional variance theorem with the
coefficient `v'_k = 2 ∫ hsym²` (its identification with `v_k = ½ ∫ H_k²` is OPEN) -/

section MeanZero

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] {ν : Measure G}

/-- **`∫ h_F = 0`** for a translation-invariant bounded measurable kernel. -/
theorem hpair_int [IsProbabilityMeasure ν]
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (hT : VarianceGeneral2.TI F) :
    ∫ y, VarianceGeneral2.hpair ν F y ∂ν = 0 := by
  classical
  have hbm : ∀ p : Fin n × Fin n, BM (fun y =>
      VarianceGeneral2.AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F (Function.update 0 p.1 y)) :=
    fun p => ⟨(VarianceGeneral2.AW_bm _ hF).meas.comp (measurable_update 0),
      ((VarianceGeneral2.AW_bm (ν := ν) ({p.1, p.2} : Finset (Fin n))ᶜ hF).bdd).imp
        fun C h y => h _⟩
  have hint : ∀ p : Fin n × Fin n, Integrable (fun y =>
      VarianceGeneral2.AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F (Function.update 0 p.1 y)
        - VarianceGeneral2.AW ν Finset.univ F 0) ν := fun p =>
    ((hbm p).sub (BM.const _)).integrable
  unfold VarianceGeneral2.hpair
  rw [integral_finset_sum _ fun p _ => hint p]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.ne
  rw [integral_sub (hbm p).integrable (integrable_const _), integral_const, probReal_univ,
    one_smul]
  have e : ∫ y, VarianceGeneral2.AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F (Function.update 0 p.1 y) ∂ν
      = VarianceGeneral2.Av ν p.1 (VarianceGeneral2.AW ν ({p.1, p.2} : Finset (Fin n))ᶜ F) 0 := rfl
  have hv : p.1 ∉ ({p.1, p.2} : Finset (Fin n))ᶜ := by simp
  rw [e, ← VarianceGeneral2.AW_insert hv hF]
  have hc : insert p.1 ({p.1, p.2} : Finset (Fin n))ᶜ = ({p.2} : Finset (Fin n))ᶜ := by
    ext i
    by_cases h1 : i = p.1
    · subst h1; simp [hne]
    · by_cases h2 : i = p.2
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [hc, VarianceGeneral2.AW_le1_const hinv hF hT (S := {p.2}) (by simp) 0, sub_self]

end MeanZero




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction BiasVariance
open BiasGeneral BiasGeneral2 BiasGeneral4 BiasGeneral5 BiasGeneral6

section SymKernel

variable {d : ℕ} {σ : ℝ}

/-- Bounded measurable with mean zero on the torus. -/
def ZM (d : ℕ) (f : FlatTorus d → ℝ) : Prop := BM f ∧ ∫ u, f u ∂flatTorusMeasure d = 0

theorem ZM_add {f g : FlatTorus d → ℝ} (hf : ZM d f) (hg : ZM d g) : ZM d (fun u => f u + g u) :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1.integrable hg.1.integrable, hf.2, hg.2, add_zero]⟩

theorem ZM_sub {f g : FlatTorus d → ℝ} (hf : ZM d f) (hg : ZM d g) : ZM d (fun u => f u - g u) :=
  ⟨hf.1.sub hg.1, by rw [integral_sub hf.1.integrable hg.1.integrable, hf.2, hg.2, sub_zero]⟩

theorem ZM_mul (c : ℝ) {f : FlatTorus d → ℝ} (hf : ZM d f) : ZM d (fun u => c * f u) :=
  ⟨BM.const_mul c hf.1, by rw [integral_const_mul, hf.2, mul_zero]⟩

theorem ZM_sum {κ : Type*} (s : Finset κ) {f : κ → FlatTorus d → ℝ} (hf : ∀ l, ZM d (f l)) :
    ZM d (fun u => ∑ l ∈ s, f l u) :=
  ⟨BM.sum _ _ fun l _ => (hf l).1, by
    rw [integral_finset_sum _ fun l _ => (hf l).1.integrable]
    exact Finset.sum_eq_zero fun l _ => (hf l).2⟩

theorem hp_ZM {a : ℕ} {F : (Fin a → FlatTorus d) → ℝ} (hF : BM F) {B : ℝ}
    (hB : ∀ x, |F x| ≤ B) (hT : VarianceGeneral2.TI F) : ZM d (hp F) := by
  obtain ⟨hm, hb⟩ := hpair_bm (ν := flatTorusMeasure d) hF hB
  exact ⟨⟨hm, _, hb⟩, hpair_int (VarianceGeneral2.torus_hinv d) hF hT⟩

theorem hQT_ZM (hσ : 0 < σ) (n : ℕ) : ZM d (hQT d σ n) := by
  have hPB := fun l => phi_bounds hσ d n l
  have z0 : ZM d (hp (cyT d σ (n := n))) :=
    hp_ZM ⟨cyT_meas hσ d n, _, cyT_le_B4 hσ n⟩ (cyT_le_B4 hσ n) (fun y c => cyT_TI y c)
  have zA := hp_ZM (K1_bm (PhiA_meas hσ d n) (PhiA_le_B4 hσ n)).1
    (K1_bm (PhiA_meas hσ d n) (PhiA_le_B4 hσ n)).2 (K1_TI (PhiA_TI n))
  have zB := hp_ZM (K1_bm (PhiB_meas hσ d n) (PhiB_le_B4 hσ n)).1
    (K1_bm (PhiB_meas hσ d n) (PhiB_le_B4 hσ n)).2 (K1_TI (PhiB_TI n))
  have zEE := hp_ZM (K2_bm (PhiEE_meas hσ d n) (hPB 0).1).1
    (K2_bm (PhiEE_meas hσ d n) (hPB 0).1).2 (K2_TI (PhiEE_TI n))
  have zEB := hp_ZM (K2_bm (PhiEB_meas hσ d n) (hPB 0).2.1).1
    (K2_bm (PhiEB_meas hσ d n) (hPB 0).2.1).2 (K2_TI (PhiEB_TI n))
  have zBB := hp_ZM (K2_bm (PhiBB_meas hσ d n) (hPB 0).2.2.1).1
    (K2_bm (PhiBB_meas hσ d n) (hPB 0).2.2.1).2 (K2_TI (PhiBB_TI n))
  have zS := hp_ZM (K2_bm (PhiS_meas hσ d n) (hPB 0).2.2.2.1).1
    (K2_bm (PhiS_meas hσ d n) (hPB 0).2.2.2.1).2 (K2_TI (PhiS_TI n))
  have zl : ∀ l : Fin (n + 1), ZM d (fun u => 4 * hp (K2 (PhiQee d σ n l)) u
      - 2 * hp (K2 (PhiQeb d σ n l)) u - 2 * hp (K2 (PhiQbe d σ n l)) u
      + hp (K2 (PhiQbb d σ n l)) u) := by
    intro l
    have z1 := hp_ZM (K2_bm (PhiQee_meas hσ d n l) (hPB l).2.2.2.2.1).1
      (K2_bm (PhiQee_meas hσ d n l) (hPB l).2.2.2.2.1).2 (K2_TI (PhiQee_TI n l))
    have z2 := hp_ZM (K2_bm (PhiQeb_meas hσ d n l) (hPB l).2.2.2.2.2.1).1
      (K2_bm (PhiQeb_meas hσ d n l) (hPB l).2.2.2.2.2.1).2 (K2_TI (PhiQeb_TI n l))
    have z3 := hp_ZM (K2_bm (PhiQbe_meas hσ d n l) (hPB l).2.2.2.2.2.2.1).1
      (K2_bm (PhiQbe_meas hσ d n l) (hPB l).2.2.2.2.2.2.1).2 (K2_TI (PhiQbe_TI n l))
    have z4 := hp_ZM (K2_bm (PhiQbb_meas hσ d n l) (hPB l).2.2.2.2.2.2.2).1
      (K2_bm (PhiQbb_meas hσ d n l) (hPB l).2.2.2.2.2.2.2).2 (K2_TI (PhiQbb_TI n l))
    exact ZM_add (ZM_sub (ZM_sub (ZM_mul 4 z1) (ZM_mul 2 z2)) (ZM_mul 2 z3)) z4
  have zG1 := ZM_sub (ZM_add (ZM_sub (ZM_add (ZM_add (ZM_mul (-2) zA) zB) (ZM_mul 3 zEE))
    (ZM_mul 3 zEB)) zBB) zS
  have zG2 := ZM_sum (Finset.univ.erase (0 : Fin (n + 1))) zl
  exact ZM_add (ZM_add z0 (ZM_mul ((n : ℝ) + 1) zG1)) (ZM_mul (((n : ℝ) + 1) / 2) zG2)

/-- The symmetrised pair kernel `hsym(u) = ½ (h_QT(u) + h_QT(-u))`. -/
noncomputable def hS (d : ℕ) (σ : ℝ) (n : ℕ) (u : FlatTorus d) : ℝ :=
  1 / 2 * (hQT d σ n u + hQT d σ n (-u))

/-- **`v'_k = 2 ∫ hsym²`**, the variance coefficient of `QT` (`k = n + 1`). -/
noncomputable def vq (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ := 2 * ∫ u, hS d σ n u ^ 2 ∂flatTorusMeasure d

theorem Soff_neg {Ω G : Type*} [AddCommGroup G] (f : G → ℝ) (X : ℕ → Ω → G) (N : ℕ) (ω : Ω) :
    Soff (fun u => f (-u)) X N ω = Soff f X N ω := by
  unfold Soff
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  unfold aT
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]
    show f (-(X i ω - X j ω)) = f (X j ω - X i ω)
    rw [neg_sub]

theorem Soff_hS {Ω : Type*} (n : ℕ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) :
    Soff (hS d σ n) X N ω = Soff (hQT d σ n) X N ω := by
  unfold hS
  rw [Soff_mul, Soff_add, Soff_neg]
  ring

theorem hS_deg2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → FlatTorus d} (H : SP μ (flatTorusMeasure d) X) (hσ : 0 < σ) (n : ℕ) :
    ∃ C, Deg2 μ (flatTorusMeasure d) X (hS d σ n) C (C ^ 2) := by
  obtain ⟨⟨hm, C, hC⟩, h0⟩ := hQT_ZM (d := d) hσ n
  have hmS : Measurable (hS d σ n) := by
    unfold hS; exact (hm.add (hm.comp measurable_neg)).const_mul _
  refine ⟨C, deg2_of H hmS (fun u => ?_) (fun u => ?_) (fun x => ?_)⟩
  · unfold hS
    have h1 := abs_le.mp (hC u)
    have h2 := abs_le.mp (hC (-u))
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · unfold hS; rw [neg_neg]; ring
  · rw [(torus_vk (d := d) hσ).inv (hS d σ n) hmS x]
    unfold hS
    have i1 : Integrable (hQT d σ n) (flatTorusMeasure d) := (⟨hm, C, hC⟩ : BM _).integrable
    have i2 : Integrable (fun u => hQT d σ n (-u)) (flatTorusMeasure d) :=
      (⟨hm.comp measurable_neg, C, fun u => hC _⟩ : BM _).integrable
    rw [integral_const_mul, integral_add i1 i2,
      VarianceGeneral.neg_inv_int d (hQT d σ n), h0]
    ring

end SymKernel

/-! ## the degenerate statistic `U'_k = N⁻² ∑_{i≠j} hsym(X_i - X_j)` and the final theorems -/

section Final

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `U'_k = N⁻² ∑_{i≠j} hsym(X_i - X_j)` (`k = n + 1`). -/
noncomputable def Uq (d : ℕ) (σ : ℝ) (n : ℕ) (X : ℕ → Ω → FlatTorus d) (N : ℕ) (ω : Ω) : ℝ :=
  1 / (N : ℝ) ^ 2 * Soff (hS d σ n) X N ω

theorem Uq_var [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (n N : ℕ) :
    BM (Uq d σ n X N) ∧ cv μ (Uq d σ n X N) = vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3 := by
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  have V := torus_vk (d := d) hσ
  obtain ⟨C, Dψ⟩ := hS_deg2 H hσ n
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = ∫ u, hS d σ n u ^ 2 ∂flatTorusMeasure d := ⟨_, rfl⟩
  have hW : ∀ x, ∫ z, hS d σ n (x - z) ^ 2 ∂flatTorusMeasure d = W := fun x => by
    rw [hWd]; exact V.inv (fun u => hS d σ n u ^ 2) (Dψ.psi_meas.pow_const 2) x
  have sm := deg_second_moment Dψ hW N
  have mz := deg_mean Dψ N
  have bS : BM (Soff (hS d σ n) X N) :=
    ⟨OracleTwo.Soff_meas Dψ N, _, OracleTwo.Soff_bound Dψ N⟩
  have bU : BM (Uq d σ n X N) := BM.const_mul _ bS
  have hU0 : ∫ ω, Uq d σ n X N ω ∂μ = 0 := by
    unfold Uq; rw [integral_const_mul, mz, mul_zero]
  refine ⟨bU, ?_⟩
  rw [cv_of_mean_zero bU hU0]
  have hv : vq d σ n = 2 * W := by rw [hWd]; rfl
  have e : ∀ ω, Uq d σ n X N ω ^ 2 = (1 / (N : ℝ) ^ 2) ^ 2 * Soff (hS d σ n) X N ω ^ 2 :=
    fun ω => by unfold Uq; ring
  simp_rw [e]
  rw [integral_const_mul, sm, hv]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    field_simp

/-- **`prop:variance` for every `k = n + 1` with the coefficient `v'_k = vq d σ n`
    (UNCONDITIONAL; heat kernel on the flat torus, self-loops, general normalisation event).**
    For independent uniform points, `N ≥ 1`, `0 ≤ δ ≤ 1/8`, `θ > 0`:
    `Var U'_k = v'_k (N-1)/N³` exactly, and
    `|Var Tr P^k - v'_k (N-1)/N³| ≤ θ v'_k (N-1)/N³ + (1 + 1/θ)(2 E₁ + 2 R)` with
    `E₁ = (gK δ m₁)² δ² (2 m₁²/N) + (N + CQT)² P(max|ρ - 1| > δ)` (`trace_QT_sq`) and
    `R = Cq n · cA n · B4² / N³` (`QT_pair`).  `v'_k = 2 ∫ hsym²` with `hsym` the symmetrised pair
    kernel of `QT`; that `hsym = H_k / 2`, i.e. `v'_k = v_k` of the paper, is NOT proved here. -/
theorem variance_general_v' [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    cv μ (Uq d σ n X N) = vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3
    ∧ |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * (2 * ((gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2
            * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ})
          + 2 * (Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))) := by
  have hN' : 0 < N := hN
  obtain ⟨bU, hcvU⟩ := Uq_var X h_indep hX hlaw hσ n N
  obtain ⟨bT, _⟩ := VarianceGeneral.trace_pow_bm hσ X hX N (n + 1)
  have bQ := VarianceGeneral.QT_bm (μ := μ) hσ d X hX (N := N) (n := n)
  have hsq := VarianceGeneral.trace_QT_sq X h_indep hX hlaw hσ N hN hδ0 hδ n
  obtain ⟨_, hR⟩ := QT_pair X h_indep hX hlaw hσ hN' n
  have eU : ∀ ω, Uq d σ n X N ω = 1 / (N : ℝ) ^ 2 * Soff (hQT d σ n) X N ω := fun ω => by
    unfold Uq; rw [Soff_hS]
  have hR' : cv μ (fun ω => QT d σ N n (fun j => X j ω) - Uq d σ n X N ω)
      ≤ Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3) := by
    simp_rw [eU]; exact hR
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = (gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2
      * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2
        * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3) := ⟨_, rfl⟩
  rw [← hE1] at hsq ⊢
  rw [← hRd] at hR' ⊢
  have bTQ : BM (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - QT d σ N n (fun j => X j ω)) := bT.sub bQ
  have bQU : BM (fun ω => QT d σ N n (fun j => X j ω) - Uq d σ n X N ω) := bQ.sub bU
  have hTQ := cv_le_sq (μ := μ) bTQ
  have hg : cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - Uq d σ n X N ω) ≤ 2 * E1 + 2 * R := by
    have e : (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace - Uq d σ n X N ω)
        = fun ω => (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - QT d σ N n (fun j => X j ω))
          + (QT d σ N n (fun j => X j ω) - Uq d σ n X N ω) := by funext ω; ring
    rw [e]
    have := cv_add_le (μ := μ) bTQ bQU
    linarith only [this, hTQ, hsq, hR']
  refine ⟨hcvU, ?_⟩
  have hper := cv_perturb (μ := μ) bU (bT.sub bU) hθ
  have e : (fun ω => Uq d σ n X N ω + (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - Uq d σ n X N ω)) = fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace := by
    funext ω; ring
  rw [e, hcvU] at hper
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left hg hθ'
  linarith only [hper, this]

/-- **The same with the normalisation event of `norm_sample`** (`σ ≤ 1`, `d ≥ 1`, `N ≥ 2`,
    `kernelC1 d · δ' ≤ 1`, `δ' = √(m₁ log N / N)`): the probability term is at most `1/N³`. -/
theorem variance_general_v'_sample [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1)
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * (2 * ((gK n * (TorusReductionL1.normC d * δp) * torusM d σ 1) ^ 2
            * (TorusReductionL1.normC d * δp) ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 3))
          + 2 * (Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))) := by
  have hr : kernelC1 d * δp * Real.sqrt ((1 : ℕ) : ℝ) ≤ 1 := by
    rw [Nat.cast_one, Real.sqrt_one, mul_one]; exact hrange
  obtain ⟨h8, hp⟩ := TorusReductionL1.norm_sample hσ hσ1 d hd X h_indep hX hlaw N 1 hN2
    Nat.one_pos hMp hδp hr
  have hδ0 : 0 ≤ TorusReductionL1.normC d * δp := by
    rw [hδp]; exact mul_nonneg (TorusReductionL1.normC_nonneg d) (Real.sqrt_nonneg _)
  obtain ⟨_, h⟩ := variance_general_v' X h_indep hX hlaw hσ N (by omega) hδ0 h8 n hθ
  refine h.trans ?_
  have hc : (0 : ℝ) ≤ (N + CQT d σ n) ^ 2 := _root_.sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hp hc
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : 2 * ((gK n * (TorusReductionL1.normC d * δp)
      * torusM d σ 1) ^ 2 * (TorusReductionL1.normC d * δp) ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
      + (N + CQT d σ n) ^ 2 * μ.real {ω | ¬ ∀ a : Fin N,
        |heatRho d σ N (fun j => X j ω) a - 1| ≤ TorusReductionL1.normC d * δp})
      + 2 * (Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))
      ≤ 2 * ((gK n * (TorusReductionL1.normC d * δp) * torusM d σ 1) ^ 2
            * (TorusReductionL1.normC d * δp) ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 3))
          + 2 * (Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))) hθ'
  linarith

end Final




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction BiasVariance
open BiasGeneral BiasGeneral2 BiasGeneral4 BiasGeneral5 BiasGeneral6

/-! ## (2), the remaining identification, stated as a HYPOTHESIS -/

/-- If the symmetrised pair kernel of `QT` is `H_k / 2` (Steps 3–4 of the paper; NOT proved here),
    then `v'_k = v_k`. -/
theorem vq_eq_vk {d : ℕ} {σ : ℝ} (n : ℕ)
    (hid : ∀ u, hS d σ n u = 1 / 2 * VarianceGeneral.Hk d σ (n + 1) u) :
    vq d σ n = VarianceGeneral.vk d σ (n + 1) := by
  unfold vq VarianceGeneral.vk
  simp_rw [hid]
  have e : ∀ u, (1 / 2 * VarianceGeneral.Hk d σ (n + 1) u) ^ 2
      = 1 / 4 * VarianceGeneral.Hk d σ (n + 1) u ^ 2 := fun u => by ring
  simp_rw [e]
  rw [integral_const_mul]; ring

/-- **`prop:variance` for every `k = n + 1` with `v_k = ½ ∫ H_k²`, CONDITIONAL only on the
    identification `hsym = H_k / 2` (HYPOTHESIS `hid`)**, with the normalisation event of
    `norm_sample`. -/
theorem variance_general_of_ident {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1)
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ)
    (hid : ∀ u, hS d σ n u = 1 / 2 * VarianceGeneral.Hk d σ (n + 1) u) :
    |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * (2 * ((gK n * (TorusReductionL1.normC d * δp) * torusM d σ 1) ^ 2
            * (TorusReductionL1.normC d * δp) ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 3))
          + 2 * (Cq n * (cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))) := by
  rw [← vq_eq_vk n hid]
  exact variance_general_v'_sample hσ hσ1 d hd X h_indep hX hlaw N hN2 hMp hδp hrange n hθ

end VarianceGeneral3

namespace VarianceGeneral4

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction

/-! # A106 (a): the integrals `AW` as integrals over the product measure, and the pair marginal of a
translation-invariant kernel as an integral over the sample -/

section PiForm

variable {G : Type*} [MeasurableSpace G] {ν : Measure G}

/-- Replacing one coordinate by an independent point preserves the product measure. -/
theorem update_map [IsProbabilityMeasure ν] {n : ℕ} (v : Fin n) :
    Measure.map (fun p : (Fin n → G) × G => Function.update p.1 v p.2)
      ((Measure.pi fun _ : Fin n => ν).prod ν) = Measure.pi fun _ : Fin n => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have e : (fun p : (Fin n → G) × G => Function.update p.1 v p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (Function.update s v Set.univ)) ×ˢ (s v) := by
    ext ⟨z, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h v⟩
      by_cases hi : i = v
      · subst hi; simp
      · have := h i; rw [Function.update_of_ne hi] at this ⊢; exact this
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = v
      · subst hi; simpa using h2
      · have := h1 i; rw [Function.update_of_ne hi] at this ⊢; exact this
  rw [e, Measure.prod_prod, Measure.pi_pi]
  have e2 : ∀ i, ν (Function.update s v Set.univ i)
      = Function.update (fun i => ν (s i)) v 1 i := by
    intro i
    by_cases hi : i = v
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  simp_rw [e2]
  rw [Finset.prod_update_of_mem (Finset.mem_univ v), one_mul,
    ← Finset.mul_prod_erase Finset.univ (fun i => ν (s i)) (Finset.mem_univ v),
    Finset.sdiff_singleton_eq_erase, mul_comm]

/-- The point with the coordinates in `W` taken from `z` and the others from `x`. -/
def pw {n : ℕ} (W : Finset (Fin n)) (z x : Fin n → G) : Fin n → G :=
  fun i => if i ∈ W then z i else x i

theorem pw_meas {n : ℕ} (W : Finset (Fin n)) (x : Fin n → G) :
    Measurable fun z : Fin n → G => pw W z x := by
  refine measurable_pi_lambda _ fun i => ?_
  by_cases h : i ∈ W
  · simp only [pw, h, if_true]; exact measurable_pi_apply i
  · simp only [pw, h, if_false]; exact measurable_const

/-- `∫_t ∫_z H(update z v t) = ∫ H` for bounded measurable `H`. -/
theorem int_update [IsProbabilityMeasure ν] {n : ℕ} (v : Fin n) {H : (Fin n → G) → ℝ}
    (hHm : Measurable H) (hHb : ∃ B, ∀ z, |H z| ≤ B) :
    ∫ t, ∫ z, H (Function.update z v t) ∂Measure.pi (fun _ : Fin n => ν) ∂ν
      = ∫ z, H z ∂Measure.pi (fun _ : Fin n => ν) := by
  obtain ⟨B, hB⟩ := hHb
  have hU : Measurable fun p : (Fin n → G) × G => Function.update p.1 v p.2 := measurable_update'
  have hbm : BM fun p : (Fin n → G) × G => H (Function.update p.1 v p.2) :=
    ⟨hHm.comp hU, B, fun p => hB _⟩
  conv_rhs => rw [← update_map (ν := ν) v]
  rw [integral_map hU.aemeasurable hHm.aestronglyMeasurable, integral_prod _ hbm.integrable]
  have hbm' : BM fun p : G × (Fin n → G) => H (Function.update p.2 v p.1) :=
    ⟨hHm.comp (hU.comp measurable_swap), B, fun p => hB _⟩
  exact integral_integral_swap (f := fun (t : G) (z : Fin n → G) => H (Function.update z v t))
    hbm'.integrable

/-- **`AW` is the integral over the product measure of the integrated coordinates.** -/
theorem AW_pi [IsProbabilityMeasure ν] {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F)
    (W : Finset (Fin n)) : ∀ x,
    VarianceGeneral2.AW ν W F x = ∫ z, F (pw W z x) ∂Measure.pi (fun _ : Fin n => ν) := by
  induction W using Finset.induction_on with
  | empty =>
    intro x
    rw [VarianceGeneral2.AW_empty]
    have e : ∀ z : Fin n → G, pw ∅ z x = x := fun z => by funext i; simp [pw]
    simp_rw [e]
    simp
  | insert v W hv ih =>
    intro x
    rw [VarianceGeneral2.AW_insert hv hF]
    unfold VarianceGeneral2.Av
    simp_rw [ih]
    have hpw : ∀ (z : Fin n → G) (t : G),
        pw W z (Function.update x v t) = pw (insert v W) (Function.update z v t) x := by
      intro z t
      funext i
      unfold pw
      by_cases h : i = v
      · subst h; simp [hv]
      · simp [Function.update_of_ne h, Finset.mem_insert, h]
    simp_rw [hpw]
    exact int_update v (hF.meas.comp (pw_meas _ x)) (hF.bdd.imp fun C h z => h _)

end PiForm

/-! ### `AW` of a product with a factor that does not depend on the integrated coordinates -/

section Factor

variable {G : Type*} [MeasurableSpace G] {ν : Measure G}

theorem Av_mul_inv {n : ℕ} (v : Fin n) (F h : (Fin n → G) → ℝ)
    (hh : ∀ x z, h (Function.update x v z) = h x) :
    VarianceGeneral2.Av ν v (fun x => F x * h x) = fun x => VarianceGeneral2.Av ν v F x * h x := by
  funext x
  unfold VarianceGeneral2.Av
  simp_rw [hh x]
  exact integral_mul_const _ _

theorem AW_mul_inv [IsProbabilityMeasure ν] {n : ℕ} {F h : (Fin n → G) → ℝ} (hF : BM F)
    (hhb : BM h) (W : Finset (Fin n)) (hh : ∀ w ∈ W, ∀ x z, h (Function.update x w z) = h x) :
    VarianceGeneral2.AW ν W (fun x => F x * h x)
      = fun x => VarianceGeneral2.AW ν W F x * h x := by
  induction W using Finset.induction_on with
  | empty => rw [VarianceGeneral2.AW_empty, VarianceGeneral2.AW_empty]
  | insert v W hv ih =>
    have hh' : ∀ w ∈ W, ∀ x z, h (Function.update x w z) = h x :=
      fun w hw => hh w (Finset.mem_insert_of_mem hw)
    rw [VarianceGeneral2.AW_insert hv (hF.mul hhb), VarianceGeneral2.AW_insert hv hF, ih hh']
    exact Av_mul_inv v _ h (hh v (Finset.mem_insert_self v W))

end Factor

/-! ### the pair marginal as an integral over the sample -/

section PairMarginal

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSub₂ G] [MeasurableAdd₂ G]
  {ν : Measure G}

/-- The pair marginal `J_{αβ}(y) = E[F | x_α - x_β = y]`, as in `hpair`. -/
noncomputable def Jp (ν : Measure G) {n : ℕ} (F : (Fin n → G) → ℝ) (α β : Fin n) (y : G) : ℝ :=
  VarianceGeneral2.AW ν ({α, β} : Finset (Fin n))ᶜ F (Function.update 0 α y)

/-- **The pair marginal tested against `g`**: for a translation-invariant bounded measurable
    kernel `F`, `α ≠ β` and bounded measurable `g`:
    `∫ J_{αβ}(y) g(y) dν(y) = ∫ F(x) g(x_α - x_β) dν^n(x)`. -/
theorem Jp_test [IsProbabilityMeasure ν]
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (hT : VarianceGeneral2.TI F) {α β : Fin n}
    (hab : α ≠ β) {g : G → ℝ} (hg : BM g) :
    ∫ y, Jp ν F α β y * g y ∂ν
      = ∫ x, F x * g (x α - x β) ∂Measure.pi (fun _ : Fin n => ν) := by
  classical
  obtain ⟨W, hW⟩ : ∃ W : Finset (Fin n), W = ({α, β} : Finset (Fin n))ᶜ := ⟨_, rfl⟩
  have hαW : α ∉ W := by rw [hW]; simp
  have hβW : β ∉ W := by rw [hW]; simp
  have hβW' : β ∉ insert α W := by simp [hβW, Ne.symm hab]
  have hu : (Finset.univ : Finset (Fin n)) = insert β (insert α W) := by
    ext i; rw [hW]; by_cases h1 : i = α
    · subst h1; simp
    · by_cases h2 : i = β
      · subst h2; simp
      · simp [h1, h2]
  -- the factor `g(x_α - x_β)`
  have hhb : BM fun x : Fin n → G => g (x α - x β) :=
    ⟨hg.meas.comp ((measurable_pi_apply α).sub (measurable_pi_apply β)),
      hg.bdd.imp fun C h x => h _⟩
  have hinvW : ∀ w ∈ W, ∀ (x : Fin n → G) z,
      g (Function.update x w z α - Function.update x w z β) = g (x α - x β) := by
    intro w hw x z
    have h1 : w ≠ α := fun e => hαW (e ▸ hw)
    have h2 : w ≠ β := fun e => hβW (e ▸ hw)
    rw [Function.update_of_ne (Ne.symm h1), Function.update_of_ne (Ne.symm h2)]
  have hFg : BM fun x => F x * g (x α - x β) := hF.mul hhb
  -- step 1: integrate the coordinates of `W`
  have s1 := AW_mul_inv (ν := ν) hF hhb W hinvW
  -- step 2: the conditional integral is `J(x_α - x_β)`
  have hJ : ∀ x : Fin n → G, VarianceGeneral2.AW ν W F x = Jp ν F α β (x α - x β) := by
    intro x
    unfold Jp
    rw [← hW, ← VarianceGeneral2.AW_TI hinv W hF hT x (-x β)]
    refine VarianceGeneral2.AW_off W hF _ _ fun i hi => ?_
    have hi' : i = α ∨ i = β := by
      by_contra hc; push Not at hc; exact hi (by rw [hW]; simp [hc.1, hc.2])
    rcases hi' with h | h
    · subst h; simp [sub_eq_add_neg]
    · subst h; simp [Function.update_of_ne (Ne.symm hab)]
  -- the whole integral via `AW univ`
  have hall := AW_pi (ν := ν) hFg Finset.univ 0
  have hpwu : ∀ z : Fin n → G, pw Finset.univ z 0 = z := fun z => by funext i; simp [pw]
  simp_rw [hpwu] at hall
  rw [← hall, hu, VarianceGeneral2.AW_insert hβW' hFg, VarianceGeneral2.AW_insert hαW hFg, s1]
  unfold VarianceGeneral2.Av
  simp only [Function.update_self]
  -- the inner integral over `x_α`
  have hφm : Measurable fun y => Jp ν F α β y * g y := by
    have hm : Measurable (Jp ν F α β) :=
      (VarianceGeneral2.AW_bm _ hF).meas.comp (measurable_update 0)
    exact hm.mul hg.meas
  have inner : ∀ t : G, ∫ s, VarianceGeneral2.AW ν W F
        (Function.update (Function.update (0 : Fin n → G) β t) α s)
        * g (s - Function.update (Function.update (0 : Fin n → G) β t) α s β) ∂ν
      = ∫ y, Jp ν F α β y * g y ∂ν := by
    intro t
    have e : ∀ s : G, s - Function.update (Function.update (0 : Fin n → G) β t) α s β
        = s + -t := by
      intro s
      rw [Function.update_of_ne (Ne.symm hab), Function.update_self, sub_eq_add_neg]
    simp_rw [hJ, Function.update_self, e]
    exact hinv (fun y => Jp ν F α β y * g y) hφm (-t)
  simp_rw [inner]
  simp

end PairMarginal




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4

/-! ## (a), cycle: the pair marginals of the closed walk `cyT` -/

section AeTest

variable {G : Type*} [MeasurableSpace G] {ν : Measure G}

/-- Two bounded measurable functions with the same integrals against all bounded measurable
    `g ≥ 0` agree almost everywhere. -/
theorem ae_of_test [IsFiniteMeasure ν] {A B : G → ℝ} (hA : BM A) (hB : BM B)
    (h : ∀ g : G → ℝ, Measurable g → (∀ u, 0 ≤ g u) → (∃ C, ∀ u, g u ≤ C) →
      ∫ u, A u * g u ∂ν = ∫ u, B u * g u ∂ν) : A =ᵐ[ν] B := by
  obtain ⟨CA, hCA⟩ := hA.bdd
  obtain ⟨CB, hCB⟩ := hB.bdd
  have key : ∀ {A B : G → ℝ}, BM A → BM B → (∀ u, |A u| ≤ CA + CB) → (∀ u, |B u| ≤ CA + CB) →
      ∫ u, A u * max (A u - B u) 0 ∂ν = ∫ u, B u * max (A u - B u) 0 ∂ν →
      ∀ᵐ u ∂ν, A u ≤ B u := by
    intro A B hA hB hAb hBb hE
    have hm : Measurable fun u => max (A u - B u) 0 := (hA.meas.sub hB.meas).max measurable_const
    have hbm : BM fun u => max (A u - B u) 0 * max (A u - B u) 0 :=
      ⟨hm.mul hm, (2 * (CA + CB)) ^ 2, fun u => by
        have h1 := abs_le.mp (hAb u); have h2 := abs_le.mp (hBb u)
        have h3 : 0 ≤ max (A u - B u) 0 := le_max_right _ _
        have h4 : max (A u - B u) 0 ≤ 2 * (CA + CB) := max_le (by linarith) (by linarith)
        rw [abs_of_nonneg (mul_nonneg h3 h3)]
        nlinarith⟩
    have e : ∀ u, max (A u - B u) 0 * max (A u - B u) 0
        = A u * max (A u - B u) 0 - B u * max (A u - B u) 0 := fun u => by
      rcases le_total (A u - B u) 0 with h | h
      · rw [max_eq_right h]; ring
      · rw [max_eq_left h]; ring
    have iA : Integrable (fun u => A u * max (A u - B u) 0) ν :=
      (hA.mul ⟨hm, 2 * (CA + CB), fun u => by
        have h1 := abs_le.mp (hAb u); have h2 := abs_le.mp (hBb u)
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (by linarith)⟩).integrable
    have iB : Integrable (fun u => B u * max (A u - B u) 0) ν :=
      (hB.mul ⟨hm, 2 * (CA + CB), fun u => by
        have h1 := abs_le.mp (hAb u); have h2 := abs_le.mp (hBb u)
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (by linarith)⟩).integrable
    have h0 : ∫ u, max (A u - B u) 0 * max (A u - B u) 0 ∂ν = 0 := by
      simp_rw [e]; rw [integral_sub iA iB, hE, sub_self]
    have hz := (integral_eq_zero_iff_of_nonneg (fun u => mul_self_nonneg _)
      hbm.integrable).mp h0
    filter_upwards [hz] with u hu
    have : max (A u - B u) 0 = 0 := mul_self_eq_zero.mp hu
    have := le_max_left (A u - B u) 0
    linarith
  have hAb : ∀ u, |A u| ≤ CA + CB := fun u => by
    have := hCA u; have := abs_nonneg (B u); have := hCB u; linarith
  have hBb : ∀ u, |B u| ≤ CA + CB := fun u => by
    have := hCB u; have := abs_nonneg (A u); have := hCA u; linarith
  have g1 : ∀ {P Q : G → ℝ}, BM P → BM Q → (∀ u, |P u| ≤ CA + CB) → (∀ u, |Q u| ≤ CA + CB) →
      Measurable fun u => max (P u - Q u) 0 := fun hP hQ _ _ =>
    (hP.meas.sub hQ.meas).max measurable_const
  have test : ∀ {P Q : G → ℝ}, BM P → BM Q → (∀ u, |P u| ≤ CA + CB) → (∀ u, |Q u| ≤ CA + CB) →
      ∃ C, ∀ u, max (P u - Q u) 0 ≤ C := fun {P Q} _ _ hPb hQb =>
    ⟨2 * (CA + CB), fun u => by
      have h1 := abs_le.mp (hPb u); have h2 := abs_le.mp (hQb u)
      exact max_le (by linarith) (by linarith)⟩
  have h1 := key hA hB hAb hBb (h _ (g1 hA hB hAb hBb) (fun u => le_max_right _ _)
    (test hA hB hAb hBb))
  have h2 := key hB hA hBb hAb (h _ (g1 hB hA hBb hAb) (fun u => le_max_right _ _)
    (test hB hA hBb hAb)).symm
  filter_upwards [h1, h2] with u a b
  exact le_antisymm a b

end AeTest

section Rotation

variable {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]

/-- Rotating the coordinates of `Fin (n+1)` preserves the product measure. -/
theorem int_rot {n : ℕ} (s : Fin (n + 1)) (F : (Fin (n + 1) → G) → ℝ) :
    ∫ x, F (fun a => x (a + s)) ∂Measure.pi (fun _ : Fin (n + 1) => ν)
      = ∫ x, F x ∂Measure.pi (fun _ : Fin (n + 1) => ν) := by
  have h := measurePreserving_piCongrLeft (fun _ : Fin (n + 1) => ν) (Equiv.subRight s)
  have e : ∀ x : Fin (n + 1) → G,
      MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) => G) (Equiv.subRight s) x
        = fun a => x (a + s) := by
    intro x
    funext b
    have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (n + 1) => G)
      (Equiv.subRight s) x (b + s)
    simpa using this
  rw [← h.integral_comp' F]
  simp_rw [e]

end Rotation

section CycleMarginal

variable {d : ℕ} {σ : ℝ}

theorem cyT_bm (hσ : 0 < σ) (n : ℕ) : BM (cyT d σ (n := n)) :=
  ⟨cyT_meas hσ d n, _, VarianceGeneral3.cyT_le_B4 hσ n⟩

/-- **The closed walk tested on a pair of positions**: for `α ≠ β` and bounded measurable `g ≥ 0`,
    `∫ cycle(x) g(x_α - x_β) = ∫ p_l p_{k-l} g` with `l = (β - α : Fin k)`. -/
theorem cyc_pair_test (hσ : 0 < σ) {n : ℕ} {α β : Fin (n + 1)} (hab : α ≠ β)
    (g : FlatTorus d → ℝ) (hg : Measurable g) (hg0 : ∀ u, 0 ≤ g u) {C : ℝ} (hgC : ∀ u, g u ≤ C) :
    ∫ x, cyT d σ x * g (x α - x β) ∂Measure.pi (fun _ : Fin (n + 1) => flatTorusMeasure d)
      = ∫ u, heatP d σ (β - α).val u * heatP d σ (n + 1 - (β - α).val) u * g u
          ∂flatTorusMeasure d := by
  have hl : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have e : ∀ x : Fin (n + 1) → FlatTorus d, cyT d σ x * g (x α - x β)
      = (fun y : Fin (n + 1) → FlatTorus d =>
          cycP (fun x z => heatP d σ 1 (x - z)) y * g (y 0 - y (β - α))) (fun a => x (a + α)) := by
    intro x
    simp only [zero_add, sub_add_cancel]
    unfold cyT
    rw [cycP_rot]
  simp_rw [e]
  rw [int_rot α (fun y : Fin (n + 1) → FlatTorus d =>
    cycP (fun x z => heatP d σ 1 (x - z)) y * g (y 0 - y (β - α)))]
  exact torus_chord hσ d n (β - α) hl g hg hg0 hgC

/-- **The pair marginal of the closed walk**: `J_{αβ}(cyT) = p_l p_{k-l}` almost everywhere,
    `l = (β - α : Fin k)`. -/
theorem cyc_Jp (hσ : 0 < σ) {n : ℕ} {α β : Fin (n + 1)} (hab : α ≠ β) :
    Jp (flatTorusMeasure d) (cyT d σ (n := n)) α β
      =ᵐ[flatTorusMeasure d] fun u => heatP d σ (β - α).val u * heatP d σ (n + 1 - (β - α).val) u := by
  have hbmJ : BM (Jp (flatTorusMeasure d) (cyT d σ (n := n)) α β) :=
    ⟨(VarianceGeneral2.AW_bm _ (cyT_bm hσ n)).meas.comp (measurable_update 0),
      ((VarianceGeneral2.AW_bm (ν := flatTorusMeasure d) _ (cyT_bm hσ n)).bdd).imp
        fun C h y => h _⟩
  have hP : ∀ s : ℕ, BM (heatP d σ s) := fun s => by
    by_cases hs : s = 0
    · subst hs
      have e0 : heatP d σ 0 = fun _ => 0 := by funext u; simp [heatP]
      rw [e0]; exact BM.const 0
    · exact ⟨(heatP_cont hσ d (by omega)).measurable, torusM d σ 1, fun u => by
        rw [abs_of_nonneg (heatP_nonneg hσ d s u)]
        exact (heatP_le hσ d (by omega) u).trans (torusM_anti hσ d le_rfl (by omega))⟩
  refine ae_of_test hbmJ ((hP _).mul (hP _)) fun g hg hg0 hgC => ?_
  obtain ⟨C, hC⟩ := hgC
  have hgb : BM g := ⟨hg, C, fun u => by rw [abs_of_nonneg (hg0 u)]; exact hC u⟩
  rw [Jp_test (VarianceGeneral2.torus_hinv d) (cyT_bm hσ n)
    (fun y c => VarianceGeneral3.cyT_TI y c) hab hgb,
    cyc_pair_test hσ hab g hg hg0 hC]

end CycleMarginal




open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4

section CycleBlock

variable {d : ℕ} {σ : ℝ}

theorem cyc_mean (hσ : 0 < σ) (n : ℕ) :
    VarianceGeneral2.AW (flatTorusMeasure d) Finset.univ (cyT d σ (n := n)) 0 = torusM d σ (n + 1) := by
  rw [AW_pi (cyT_bm hσ n) Finset.univ 0]
  have hpwu : ∀ z : Fin (n + 1) → FlatTorus d, pw Finset.univ z 0 = z := fun z => by
    funext i; simp [pw]
  simp_rw [hpwu]
  exact cycP_int (torusRK hσ d) n

/-- The summand of the cycle block after the reflection. -/
noncomputable def fcyc (d : ℕ) (σ : ℝ) (k l : ℕ) (u : FlatTorus d) : ℝ :=
  heatP d σ l u * heatP d σ (k - l) u - torusM d σ k

/-- **Step 3, line `Q₀`, for every `k = n + 1`: the pair kernel of the closed-walk block is
    `½ H_{Q₀} = ½ (k Γ_k - k(k-1) μ_k)` almost everywhere.** -/
theorem hp_cyc (hσ : 0 < σ) (n : ℕ) :
    VarianceGeneral3.hp (cyT d σ (n := n))
      =ᵐ[flatTorusMeasure d] fun u => 1 / 2 * (((n : ℝ) + 1) * VarianceGeneral.gam d σ (n + 1) u
        - ((n : ℝ) + 1) * n * torusM d σ (n + 1)) := by
  have hall : ∀ᵐ u ∂flatTorusMeasure d, ∀ p ∈ VarianceGeneral2.pairs (n + 1),
      Jp (flatTorusMeasure d) (cyT d σ (n := n)) p.1 p.2 u
        = heatP d σ (p.2 - p.1).val u * heatP d σ (n + 1 - (p.2 - p.1).val) u := by
    rw [Filter.eventually_all_finset]
    intro p hp
    exact cyc_Jp hσ (Finset.mem_filter.mp hp).2.ne
  filter_upwards [hall] with u hu
  unfold VarianceGeneral3.hp VarianceGeneral2.hpair
  have e1 : ∀ p ∈ VarianceGeneral2.pairs (n + 1),
      VarianceGeneral2.AW (flatTorusMeasure d) ({p.1, p.2} : Finset (Fin (n + 1)))ᶜ
          (cyT d σ (n := n)) (Function.update 0 p.1 u)
        - VarianceGeneral2.AW (flatTorusMeasure d) (Finset.univ : Finset (Fin (n + 1)))
          (cyT d σ (n := n)) 0
      = fcyc d σ (n + 1) (p.2.val - p.1.val) u := by
    intro p hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hv : (p.2 - p.1).val = p.2.val - p.1.val := Fin.sub_val_of_le hlt.le
    have := hu p hp
    unfold Jp at this
    rw [this, cyc_mean hσ n, hv]
    rfl
  rw [Finset.sum_congr rfl e1]
  have h1 := sum_Prs_diff (n + 1) (fun l => fcyc d σ (n + 1) l u)
  have hPrs : VarianceGeneral2.pairs (n + 1) = Prs (n + 1) := rfl
  rw [hPrs, h1]
  have h2 := sum_reflect (n + 1) (fun l => fcyc d σ (n + 1) l u) (fun l hl => by
    have hl' := Finset.mem_Ico.mp hl
    simp only [fcyc]
    rw [show n + 1 - (n + 1 - l) = l by omega]; ring)
  have hgam : VarianceGeneral.gam d σ (n + 1) u
      = ∑ l ∈ Finset.Ico 1 (n + 1), heatP d σ l u * heatP d σ (n + 1 - l) u := by
    unfold VarianceGeneral.gam
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_Ico.mp hl
    rw [BiasGeneral6.heatP_eq_pker d σ hl'.1, BiasGeneral6.heatP_eq_pker d σ (by omega : 1 ≤ n + 1 - l)]
  have hsum : ∑ l ∈ Finset.Ico 1 (n + 1), fcyc d σ (n + 1) l u
      = VarianceGeneral.gam d σ (n + 1) u - n * torusM d σ (n + 1) := by
    unfold fcyc
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, hgam, nsmul_eq_mul]
    simp
  rw [hsum] at h2
  push_cast at h2 ⊢
  linarith

end CycleBlock

end VarianceGeneral4

namespace VarianceGeneral5

/-! # Steps 3–4 of `prop:variance` for every `k`: the symmetrised pair kernel is `H_k / 2`

(A107.)  For every `k = n + 1`, with the Gaussian kernel on the flat torus and self-loops:
(a) the pair kernels of all blocks of `QT` (lines `Q₀`–`Q₃` of Step 3), tested against even bounded
measurable `g` (`block_A`, `block_B`, `block_EE`, `block_EB`, `block_S`, `block_BB`, `block_Qee`,
`block_Qeb`, `block_Qbe`, `block_Qbb`; `Q₀` is `VarianceGeneral4.hp_cyc`); (b) their sum
`hQT_test`: `∫ h_QT g = ∫ (H_k/2) g`; (c) `hS_ae`: `hsym = H_k / 2` almost everywhere and
`vq_eq_vk_ae`: `v'_k = v_k`; (d) `variance_general`: `prop:variance` with `v_k`, without hypothesis.
Route: test functions instead of conditional expectations; attached vertices are integrated out
one by one (`int_c`, `int_p`), the remaining cycle is evaluated on a chord (`cyc_f`). -/

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 VarianceGeneral

/-! ## Operators on the torus: `𝒫 = Pop d σ 1`, integration lemmas -/

section Ops

variable {d : ℕ} {σ : ℝ}

theorem hp1 (d : ℕ) (σ : ℝ) : heatP d σ 1 = pker d σ := by
  funext u; rw [BiasGeneral6.heatP_eq_pker d σ le_rfl u]; norm_num

theorem pker_bd (hσ : 0 < σ) (u : FlatTorus d) : 0 ≤ pker d σ u ∧ pker d σ u ≤ torusM d σ 1 := by
  have h0 := heatP_nonneg hσ d 1 u
  have h1 := heatP_le hσ d le_rfl u
  rw [hp1] at h0 h1; exact ⟨h0, h1⟩

theorem pker_bm (hσ : 0 < σ) : BM (pker d σ) :=
  ⟨(pker_continuous hσ d).measurable, torusM d σ 1, fun u => by
    rw [abs_of_nonneg (pker_bd hσ u).1]; exact (pker_bd hσ u).2⟩

theorem pker_ev (d : ℕ) (σ : ℝ) (u : FlatTorus d) : pker d σ (-u) = pker d σ u := by
  unfold pker; rw [heatTorus_even]

theorem pker_sw (d : ℕ) (σ : ℝ) (a b : FlatTorus d) : pker d σ (a - b) = pker d σ (b - a) := by
  rw [← neg_sub, pker_ev]

theorem bm_comp {f : FlatTorus d → ℝ} (hf : BM f) {φ : FlatTorus d → FlatTorus d}
    (hφ : Measurable φ) : BM (fun z => f (φ z)) :=
  ⟨hf.meas.comp hφ, hf.bdd.imp fun C h z => h _⟩

theorem pkb (hσ : 0 < σ) (u : FlatTorus d) : BM (fun z => pker d σ (u - z)) :=
  bm_comp (pker_bm hσ) (measurable_const.sub measurable_id)

theorem Pop_one (g : FlatTorus d → ℝ) (u : FlatTorus d) :
    Pop d σ 1 g u = ∫ z, pker d σ (u - z) * g z ∂flatTorusMeasure d := rfl

theorem Pop_succ' (j : ℕ) (g : FlatTorus d → ℝ) : Pop d σ (j + 1) g = Pop d σ 1 (Pop d σ j g) :=
  rfl

theorem conv_bm (hσ : 0 < σ) {h : FlatTorus d → ℝ} (hh : BM h) : BM (Pop d σ 1 h) := by
  obtain ⟨C, hC⟩ := hh.bdd
  have hm : Measurable (Function.uncurry fun (u z : FlatTorus d) => pker d σ (u - z) * h z) :=
    ((pker_continuous hσ d).measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hh.meas.comp measurable_snd)
  refine ⟨(hm.stronglyMeasurable.integral_prod_right).measurable, C, fun u => ?_⟩
  rw [Pop_one]
  have hi : Integrable (fun z => pker d σ (u - z) * C) (flatTorusMeasure d) :=
    ((pkb hσ _).mul
      (BM.const C)).integrable
  have h1 : ‖∫ z, pker d σ (u - z) * h z ∂flatTorusMeasure d‖
      ≤ ∫ z, pker d σ (u - z) * C ∂flatTorusMeasure d := by
    refine norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pker_bd hσ _).1]
    exact mul_le_mul_of_nonneg_left (hC z) (pker_bd hσ _).1
  rw [Real.norm_eq_abs, integral_mul_const, pker_mass hσ d u, one_mul] at h1
  exact h1

theorem Pop_bm (hσ : 0 < σ) {h : FlatTorus d → ℝ} (hh : BM h) : ∀ j, BM (Pop d σ j h) := by
  intro j
  induction j with
  | zero => exact hh
  | succ j ih => rw [Pop_succ']; exact conv_bm hσ ih

theorem prod_bm {F : FlatTorus d × FlatTorus d → ℝ} (hF : BM F) :
    Integrable F ((flatTorusMeasure d).prod (flatTorusMeasure d)) := hF.integrable

/-- Self-adjointness of `𝒫`. -/
theorem Pop_adj (hσ : 0 < σ) {f h : FlatTorus d → ℝ} (hf : BM f) (hh : BM h) :
    ∫ u, Pop d σ 1 f u * h u ∂flatTorusMeasure d = ∫ u, f u * Pop d σ 1 h u ∂flatTorusMeasure d := by
  obtain ⟨Cf, hCf⟩ := hf.bdd
  obtain ⟨Ch, hCh⟩ := hh.bdd
  have hF : BM (Function.uncurry fun (u z : FlatTorus d) => pker d σ (u - z) * f z * h u) :=
    ⟨(((pker_continuous hσ d).measurable.comp (measurable_fst.sub measurable_snd)).mul
      (hf.meas.comp measurable_snd)).mul (hh.meas.comp measurable_fst),
      torusM d σ 1 * Cf * Ch, fun p => by
        show |pker d σ (p.1 - p.2) * f p.2 * h p.1| ≤ _
        rw [abs_mul, abs_mul, abs_of_nonneg (pker_bd hσ _).1]
        have h1 := (pker_bd hσ (p.1 - p.2)).2
        have h2 := hCf p.2
        have h3 := hCh p.1
        have h4 := (pker_bd hσ (p.1 - p.2)).1
        have h5 := abs_nonneg (f p.2)
        have h6 := abs_nonneg (h p.1)
        calc pker d σ (p.1 - p.2) * |f p.2| * |h p.1|
            ≤ torusM d σ 1 * Cf * Ch := by
              apply mul_le_mul (mul_le_mul h1 h2 h5 (h4.trans h1)) h3 h6
              exact mul_nonneg (h4.trans h1) (h5.trans h2)⟩
  have e1 : ∀ u, Pop d σ 1 f u * h u = ∫ z, pker d σ (u - z) * f z * h u ∂flatTorusMeasure d :=
    fun u => by rw [Pop_one, ← integral_mul_const]
  simp_rw [e1]
  rw [integral_integral_swap (prod_bm hF)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show ∫ u, pker d σ (u - z) * f z * h u ∂flatTorusMeasure d = f z * Pop d σ 1 h z
  rw [Pop_one, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show pker d σ (u - z) * f z * h u = f z * (pker d σ (z - u) * h u)
  rw [pker_sw]; ring

theorem Pop_const (hσ : 0 < σ) (c : ℝ) (u : FlatTorus d) : Pop d σ 1 (fun _ => c) u = c := by
  rw [Pop_one, integral_mul_const, pker_mass hσ d u, one_mul]

theorem Pop_sub_const (hσ : 0 < σ) {f : FlatTorus d → ℝ} (hf : BM f) (c : ℝ) (u : FlatTorus d) :
    Pop d σ 1 (fun z => f z - c) u = Pop d σ 1 f u - c := by
  rw [Pop_one, Pop_one]
  have e : ∀ z, pker d σ (u - z) * (f z - c) = pker d σ (u - z) * f z - pker d σ (u - z) * c :=
    fun z => by ring
  simp_rw [e]
  rw [integral_sub ((pkb hσ _).mul hf).integrable
    ((pkb hσ _).mul (BM.const c)).integrable,
    integral_mul_const, pker_mass hσ d u, one_mul]

theorem Pop_mean (hσ : 0 < σ) {f : FlatTorus d → ℝ} (hf : BM f) :
    ∫ u, Pop d σ 1 f u ∂flatTorusMeasure d = ∫ u, f u ∂flatTorusMeasure d := by
  have h := Pop_adj hσ hf (BM.const (1 : ℝ))
  simp only [mul_one, Pop_const hσ] at h
  exact h

theorem Pop_at0 (hσ : 0 < σ) (h : FlatTorus d → ℝ) :
    ∫ z, pker d σ z * h z ∂flatTorusMeasure d = Pop d σ 1 h 0 := by
  rw [Pop_one]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show pker d σ z * h z = pker d σ (0 - z) * h z
  rw [zero_sub, pker_ev]

/-- Integrating a vertex attached by a `p`-edge: `∫ p(x - q) h(q - y) dq = (𝒫h)(x - y)`. -/
theorem int_p (hσ : 0 < σ) {h : FlatTorus d → ℝ} (hh : BM h) (x y : FlatTorus d) :
    ∫ q, pker d σ (x - q) * h (q - y) ∂flatTorusMeasure d = Pop d σ 1 h (x - y) := by
  rw [Pop_one]
  have hm : Measurable fun w => pker d σ (x - y - w) * h w :=
    ((pker_continuous hσ d).measurable.comp (measurable_const.sub measurable_id)).mul hh.meas
  have h1 := VarianceGeneral2.torus_hinv d (fun w => pker d σ (x - y - w) * h w) hm (-y)
  rw [← h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show pker d σ (x - q) * h (q - y) = pker d σ (x - y - (q + -y)) * h (q + -y)
  rw [← sub_eq_add_neg, show x - y - (q - y) = x - q by abel]

theorem int_shift {h : FlatTorus d → ℝ} (hh : BM h) (y : FlatTorus d) :
    ∫ q, h (q - y) ∂flatTorusMeasure d = ∫ q, h q ∂flatTorusMeasure d := by
  have h1 := VarianceGeneral2.torus_hinv d h hh.meas (-y)
  simp_rw [sub_eq_add_neg]; exact h1

/-- Integrating a vertex attached by a `c`-edge: `∫ (p(x - z) - 1) h(z - y) dz = (𝒫h)(x - y) - ∫ h`. -/
theorem int_c (hσ : 0 < σ) {h : FlatTorus d → ℝ} (hh : BM h) (x y : FlatTorus d) :
    ∫ z, (pker d σ (x - z) - 1) * h (z - y) ∂flatTorusMeasure d
      = Pop d σ 1 h (x - y) - ∫ q, h q ∂flatTorusMeasure d := by
  have e : ∀ z, (pker d σ (x - z) - 1) * h (z - y) = pker d σ (x - z) * h (z - y) - h (z - y) :=
    fun z => by ring
  simp_rw [e]
  have hb : BM fun z => h (z - y) := bm_comp hh (measurable_id.sub measurable_const)
  rw [integral_sub ((pkb hσ _).mul hb).integrable
    hb.integrable, int_p hσ hh, int_shift hh]

/-- A free `c`-vertex integrates to zero. -/
theorem int_c0 (hσ : 0 < σ) (x : FlatTorus d) :
    ∫ z, (pker d σ (x - z) - 1) ∂flatTorusMeasure d = 0 := by
  rw [integral_sub (pkb hσ _).integrable
    (integrable_const 1), pker_mass hσ d x]
  simp

theorem int_p1 (hσ : 0 < σ) (x : FlatTorus d) :
    ∫ z, pker d σ (x - z) ∂flatTorusMeasure d = 1 := pker_mass hσ d x

end Ops

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 VarianceGeneral

/-! ## Integrating one coordinate of the product measure; the pairs of `Fin (s+1)` -/

section Prod

variable {G : Type*} [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]

theorem int_ins {s : ℕ} (i : Fin (s + 1)) {F : (Fin (s + 1) → G) → ℝ} (hF : BM F) :
    ∫ x, F x ∂Measure.pi (fun _ : Fin (s + 1) => ν)
      = ∫ v, ∫ z, F (Fin.insertNth i z v) ∂ν ∂Measure.pi (fun _ : Fin s => ν) := by
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin (s + 1) => ν) i
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (s + 1) => G) i with he
  have hb : BM fun p : G × (Fin s → G) => F (e.symm p) :=
    ⟨hF.meas.comp e.symm.measurable, hF.bdd.imp fun C h p => h _⟩
  have h1 : ∫ x, F x ∂Measure.pi (fun _ : Fin (s + 1) => ν)
      = ∫ p, F (e.symm p) ∂(ν.prod (Measure.pi fun _ : Fin s => ν)) := by
    rw [← h.integral_comp' (fun p => F (e.symm p))]
    simp
  rw [h1, integral_prod _ hb.integrable, integral_integral_swap hb.integrable]
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  rfl

theorem bm_cons {s : ℕ} {F : (Fin (s + 1) → G) → ℝ} (hF : BM F) :
    BM fun v : Fin s → G => ∫ z, F (Fin.cons z v) ∂ν := by
  obtain ⟨C, hC⟩ := hF.bdd
  have hm : Measurable fun p : (Fin s → G) × G => (Fin.cons p.2 p.1 : Fin (s + 1) → G) := by
    refine measurable_pi_lambda _ fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using measurable_snd
    · simpa using (measurable_pi_apply j).comp measurable_fst
  refine ⟨(StronglyMeasurable.integral_prod_right
    (f := fun (v : Fin s → G) (z : G) => F (Fin.cons z v))
    (hF.meas.comp hm).stronglyMeasurable).measurable, C, fun v => ?_⟩
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ z, |F (Fin.cons z v)| ∂ν ≤ ∫ _z, C ∂ν :=
        integral_mono (BM.integrable ⟨(hF.meas.comp hm).comp
          (measurable_const.prodMk measurable_id), C, fun z => hC _⟩).abs
          (integrable_const C) fun z => hC _
    _ = C := by simp

end Prod

theorem pairs_succ {s : ℕ} (f : Fin (s + 1) → Fin (s + 1) → ℝ) :
    ∑ p ∈ VarianceGeneral2.pairs (s + 1), f p.1 p.2
      = ∑ b : Fin s, f 0 b.succ + ∑ p ∈ VarianceGeneral2.pairs s, f p.1.succ p.2.succ := by
  unfold VarianceGeneral2.pairs
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fin.sum_univ_succ]
  simp [Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.succ_pos]

section HpTest

variable {d : ℕ}

theorem AW_univ_eq {a : ℕ} {F : (Fin a → FlatTorus d) → ℝ} (hF : BM F) :
    VarianceGeneral2.AW (flatTorusMeasure d) Finset.univ F 0
      = ∫ x, F x ∂Measure.pi (fun _ : Fin a => flatTorusMeasure d) := by
  rw [VarianceGeneral4.AW_pi hF Finset.univ 0]
  have hpwu : ∀ z : Fin a → FlatTorus d, VarianceGeneral4.pw Finset.univ z 0 = z := fun z => by
    funext i; simp [VarianceGeneral4.pw]
  simp_rw [hpwu]

/-- **The pair kernel tested against `g`**: `∫ h_F g = ∑_{α<β} (∫ F(x) g(x_α - x_β) - E F · ∫ g)`. -/
theorem hp_test {a : ℕ} {F : (Fin a → FlatTorus d) → ℝ} (hF : BM F) (hT : VarianceGeneral2.TI F)
    {g : FlatTorus d → ℝ} (hg : BM g) :
    ∫ u, VarianceGeneral3.hp F u * g u ∂flatTorusMeasure d
      = ∑ p ∈ VarianceGeneral2.pairs a,
          (∫ x, F x * g (x p.1 - x p.2) ∂Measure.pi (fun _ : Fin a => flatTorusMeasure d)
            - (∫ x, F x ∂Measure.pi (fun _ : Fin a => flatTorusMeasure d))
              * ∫ u, g u ∂flatTorusMeasure d) := by
  have hJ : ∀ p : Fin a × Fin a,
      BM (VarianceGeneral4.Jp (flatTorusMeasure d) F p.1 p.2) := fun p =>
    ⟨(VarianceGeneral2.AW_bm _ hF).meas.comp (measurable_update 0),
      ((VarianceGeneral2.AW_bm (ν := flatTorusMeasure d) _ hF).bdd).imp fun C h y => h _⟩
  have e : ∀ u, VarianceGeneral3.hp F u * g u
      = ∑ p ∈ VarianceGeneral2.pairs a,
          (VarianceGeneral4.Jp (flatTorusMeasure d) F p.1 p.2 u * g u
            - VarianceGeneral2.AW (flatTorusMeasure d) Finset.univ F 0 * g u) := fun u => by
    unfold VarianceGeneral3.hp VarianceGeneral2.hpair VarianceGeneral4.Jp
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ (fun p _ => (((hJ p).mul hg).sub
    ((BM.const (VarianceGeneral2.AW (flatTorusMeasure d) Finset.univ F 0)).mul hg)).integrable)]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hab : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.ne
  rw [integral_sub ((hJ p).mul hg).integrable ((BM.const _).mul hg).integrable,
    integral_const_mul, VarianceGeneral4.Jp_test (VarianceGeneral2.torus_hinv d) hF hT hab hg,
    AW_univ_eq hF]

end HpTest

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 VarianceGeneral

/-! ## Blocks with attached vertices: the generic computation (rule (b) and the attached
    vertices integrated out) -/

section Generic

variable {d : ℕ} {σ : ℝ}

theorem int_K1 {s : ℕ} {F : (Fin (s + 1) → FlatTorus d) → ℝ} (hF : BM F) :
    ∫ x, F x ∂Measure.pi (fun _ : Fin (s + 1) => flatTorusMeasure d)
      = ∫ v, ∫ z, F (Fin.cons z v) ∂flatTorusMeasure d
          ∂Measure.pi (fun _ : Fin s => flatTorusMeasure d) := by
  rw [int_ins 0 hF]; simp_rw [Fin.insertNth_zero']

theorem int_K2 {s : ℕ} {F : (Fin (s + 2) → FlatTorus d) → ℝ} (hF : BM F) :
    ∫ x, F x ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d)
      = ∫ v, ∫ z', ∫ z, F (Fin.cons z (Fin.cons z' v)) ∂flatTorusMeasure d ∂flatTorusMeasure d
          ∂Measure.pi (fun _ : Fin s => flatTorusMeasure d) := by
  rw [int_K1 hF, int_K1 (bm_cons hF)]

theorem bm_diff {a : ℕ} {g : FlatTorus d → ℝ} (hg : BM g) (α β : Fin a) :
    BM fun x : Fin a → FlatTorus d => g (x α - x β) :=
  ⟨hg.meas.comp ((measurable_pi_apply α).sub (measurable_pi_apply β)), hg.bdd.imp fun C h x => h _⟩

theorem c_bm (hσ : 0 < σ) {a : ℕ} (i : Fin a) (φ : (Fin a → FlatTorus d) → FlatTorus d)
    (hφ : Measurable φ) : BM fun x : Fin a → FlatTorus d => pker d σ (x i - φ x) - 1 :=
  (⟨(pker_bm hσ).meas.comp ((measurable_pi_apply i).sub hφ), (pker_bm hσ (d := d)).bdd.imp
    fun C h x => h _⟩ : BM fun x : Fin a → FlatTorus d => pker d σ (x i - φ x)).sub (BM.const 1)

theorem K1_gen (hσ : 0 < σ) {s : ℕ} {Φ : (Fin s → FlatTorus d) × FlatTorus d → ℝ}
    {A : (Fin s → FlatTorus d) → ℝ} (hA : BM A) (i : Fin s)
    (hΦ : ∀ v z, Φ (v, z) = A v * (pker d σ (v i - z) - 1))
    {g : FlatTorus d → ℝ} (hg : BM g) :
    BM (VarianceGeneral3.K1 Φ)
    ∧ (∫ x, VarianceGeneral3.K1 Φ x ∂Measure.pi (fun _ : Fin (s + 1) => flatTorusMeasure d) = 0)
    ∧ ∑ p ∈ VarianceGeneral2.pairs (s + 1),
        ∫ x, VarianceGeneral3.K1 Φ x * g (x p.1 - x p.2)
          ∂Measure.pi (fun _ : Fin (s + 1) => flatTorusMeasure d)
      = ∑ b : Fin s, ∫ v, A v * (Pop d σ 1 g (v i - v b) - ∫ u, g u ∂flatTorusMeasure d)
          ∂Measure.pi (fun _ : Fin s => flatTorusMeasure d) := by
  have hK : ∀ x : Fin (s + 1) → FlatTorus d,
      VarianceGeneral3.K1 Φ x = A (Fin.tail x) * (pker d σ (x i.succ - x 0) - 1) := fun x => by
    unfold VarianceGeneral3.K1; rw [hΦ]; rfl
  have htail : Measurable fun x : Fin (s + 1) → FlatTorus d => Fin.tail x :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hKb : BM (VarianceGeneral3.K1 Φ) := by
    have : BM fun x : Fin (s + 1) → FlatTorus d => A (Fin.tail x) * (pker d σ (x i.succ - x 0) - 1) :=
      (⟨hA.meas.comp htail, hA.bdd.imp fun C h x => h _⟩ : BM fun x : Fin (s + 1) → FlatTorus d =>
        A (Fin.tail x)).mul (c_bm hσ i.succ (fun x => x 0) (measurable_pi_apply 0))
    simpa only [← hK] using this
  have hcons : ∀ (v : Fin s → FlatTorus d) z, VarianceGeneral3.K1 Φ (Fin.cons z v) = Φ (v, z) :=
    fun v z => by unfold VarianceGeneral3.K1; simp
  refine ⟨hKb, ?_, ?_⟩
  · rw [int_K1 hKb]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
    show ∫ z, VarianceGeneral3.K1 Φ (Fin.cons z v) ∂flatTorusMeasure d = 0
    simp_rw [hcons, hΦ]
    rw [integral_const_mul, int_c0 hσ, mul_zero]
  · rw [pairs_succ (fun a b => ∫ x, VarianceGeneral3.K1 Φ x * g (x a - x b)
      ∂Measure.pi (fun _ : Fin (s + 1) => flatTorusMeasure d))]
    have h2 : ∑ p ∈ VarianceGeneral2.pairs s, ∫ x, VarianceGeneral3.K1 Φ x
        * g (x p.1.succ - x p.2.succ) ∂Measure.pi (fun _ : Fin (s + 1) => flatTorusMeasure d) = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [int_K1 (hKb.mul (bm_diff hg _ _))]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
      show ∫ z, VarianceGeneral3.K1 Φ (Fin.cons z v) * g ((Fin.cons z v : Fin (s + 1) → FlatTorus d) p.1.succ
        - (Fin.cons z v : Fin (s + 1) → FlatTorus d) p.2.succ) ∂flatTorusMeasure d = 0
      simp only [hcons, hΦ, Fin.cons_succ]
      have e : ∀ z, A v * (pker d σ (v i - z) - 1) * g (v p.1 - v p.2)
          = A v * g (v p.1 - v p.2) * (pker d σ (v i - z) - 1) := fun z => by ring
      simp_rw [e]
      rw [integral_const_mul, int_c0 hσ, mul_zero]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [int_K1 (hKb.mul (bm_diff hg _ _))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show ∫ z, VarianceGeneral3.K1 Φ (Fin.cons z v) * g ((Fin.cons z v : Fin (s + 1) → FlatTorus d) 0
        - (Fin.cons z v : Fin (s + 1) → FlatTorus d) b.succ) ∂flatTorusMeasure d = _
    simp only [hcons, hΦ, Fin.cons_succ, Fin.cons_zero]
    have e : ∀ z, A v * (pker d σ (v i - z) - 1) * g (z - v b)
        = A v * ((pker d σ (v i - z) - 1) * g (z - v b)) := fun z => by ring
    simp_rw [e]
    rw [integral_const_mul, int_c hσ hg]

/-- The function `𝒬g = 𝒫g - ∫ g` and its iterate in the form used below. -/
theorem Q2_eval (hσ : 0 < σ) {g : FlatTorus d → ℝ} (hg : BM g) (hge : ∀ u, g (-u) = g u)
    (x y : FlatTorus d) :
    ∫ z', (pker d σ (x - z') - 1) * (Pop d σ 1 g (y - z') - ∫ u, g u ∂flatTorusMeasure d)
        ∂flatTorusMeasure d
      = Pop d σ 1 (Pop d σ 1 g) (y - x) - ∫ u, g u ∂flatTorusMeasure d := by
  have hQ : BM fun w => Pop d σ 1 g w - ∫ u, g u ∂flatTorusMeasure d :=
    (conv_bm hσ hg).sub (BM.const _)
  have ev : ∀ z', Pop d σ 1 g (y - z') - ∫ u, g u ∂flatTorusMeasure d
      = (fun w => Pop d σ 1 g w - ∫ u, g u ∂flatTorusMeasure d) (z' - y) := fun z' => by
    show Pop d σ 1 g (y - z') - _ = Pop d σ 1 g (z' - y) - _
    rw [show y - z' = -(z' - y) by abel, Pop_even d σ hge 1]
  simp_rw [ev]
  rw [int_c hσ hQ, Pop_sub_const hσ (conv_bm hσ hg)]
  rw [integral_sub (conv_bm hσ hg).integrable (integrable_const _), Pop_mean hσ hg]
  rw [show x - y = -(y - x) by abel, ← Pop_succ', Pop_even d σ hge 2, Pop_succ']
  simp

theorem K2_gen (hσ : 0 < σ) {s : ℕ} {Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ}
    {A : (Fin s → FlatTorus d) → ℝ} (hA : BM A) (i j : Fin s)
    (hΦ : ∀ v z z', Φ (v, z, z') = A v * (pker d σ (v i - z) - 1) * (pker d σ (v j - z') - 1))
    {g : FlatTorus d → ℝ} (hg : BM g) (hge : ∀ u, g (-u) = g u) :
    BM (VarianceGeneral3.K2 Φ)
    ∧ (∫ x, VarianceGeneral3.K2 Φ x ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d) = 0)
    ∧ ∑ p ∈ VarianceGeneral2.pairs (s + 2),
        ∫ x, VarianceGeneral3.K2 Φ x * g (x p.1 - x p.2)
          ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d)
      = ∫ v, A v * (Pop d σ 1 (Pop d σ 1 g) (v i - v j) - ∫ u, g u ∂flatTorusMeasure d)
          ∂Measure.pi (fun _ : Fin s => flatTorusMeasure d) := by
  have hK : ∀ x : Fin (s + 2) → FlatTorus d,
      VarianceGeneral3.K2 Φ x = A (Fin.tail (Fin.tail x)) * (pker d σ (x i.succ.succ - x 0) - 1)
        * (pker d σ (x j.succ.succ - x 1) - 1) := fun x => by
    unfold VarianceGeneral3.K2; rw [hΦ]; rfl
  have htail : Measurable fun x : Fin (s + 2) → FlatTorus d => Fin.tail (Fin.tail x) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hKb : BM (VarianceGeneral3.K2 Φ) := by
    have : BM fun x : Fin (s + 2) → FlatTorus d => A (Fin.tail (Fin.tail x))
        * (pker d σ (x i.succ.succ - x 0) - 1) * (pker d σ (x j.succ.succ - x 1) - 1) :=
      ((⟨hA.meas.comp htail, hA.bdd.imp fun C h x => h _⟩ : BM fun x : Fin (s + 2) → FlatTorus d =>
        A (Fin.tail (Fin.tail x))).mul (c_bm hσ i.succ.succ (fun x => x 0) (measurable_pi_apply 0))).mul
        (c_bm hσ j.succ.succ (fun x => x 1) (measurable_pi_apply 1))
    simpa only [← hK] using this
  have hcons : ∀ (v : Fin s → FlatTorus d) z z',
      VarianceGeneral3.K2 Φ (Fin.cons z (Fin.cons z' v)) = Φ (v, z, z') :=
    fun v z z' => by unfold VarianceGeneral3.K2; simp
  -- a free `z`: the inner integral vanishes
  have freez : ∀ (v : Fin s → FlatTorus d) z' (K : ℝ),
      ∫ z, A v * (pker d σ (v i - z) - 1) * (pker d σ (v j - z') - 1) * K ∂flatTorusMeasure d = 0 :=
    fun v z' K => by
      have e : ∀ z, A v * (pker d σ (v i - z) - 1) * (pker d σ (v j - z') - 1) * K
          = (A v * (pker d σ (v j - z') - 1) * K) * (pker d σ (v i - z) - 1) := fun z => by ring
      simp_rw [e]; rw [integral_const_mul, int_c0 hσ, mul_zero]
  refine ⟨hKb, ?_, ?_⟩
  · rw [int_K2 hKb]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
    refine (integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)).trans (integral_zero _ _)
    show ∫ z, VarianceGeneral3.K2 Φ (Fin.cons z (Fin.cons z' v)) ∂flatTorusMeasure d = 0
    have := freez v z' 1
    simp_rw [mul_one] at this
    simp_rw [hcons, hΦ]; exact this
  · rw [pairs_succ (fun a b => ∫ x, VarianceGeneral3.K2 Φ x * g (x a - x b)
      ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d)), Fin.sum_univ_succ,
      pairs_succ (fun a b => ∫ x, VarianceGeneral3.K2 Φ x * g (x a.succ - x b.succ)
      ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d))]
    -- the vanishing terms
    have z1 : ∀ b : Fin s, ∫ x, VarianceGeneral3.K2 Φ x * g (x 0 - x b.succ.succ)
        ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d) = 0 := fun b => by
      rw [int_K2 (hKb.mul (bm_diff hg _ _))]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
      show ∫ z', ∫ z, VarianceGeneral3.K2 Φ (Fin.cons z (Fin.cons z' v))
        * g ((Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) 0
          - (Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) b.succ.succ)
          ∂flatTorusMeasure d ∂flatTorusMeasure d = 0
      simp only [hcons, hΦ, Fin.cons_succ, Fin.cons_zero]
      have e : ∀ z' z, A v * (pker d σ (v i - z) - 1) * (pker d σ (v j - z') - 1) * g (z - v b)
          = (pker d σ (v j - z') - 1) * (A v * ((pker d σ (v i - z) - 1) * g (z - v b))) :=
        fun z' z => by ring
      simp_rw [e, integral_const_mul]
      rw [integral_mul_const, int_c0 hσ, zero_mul]
    have z2 : ∀ b : Fin s, ∫ x, VarianceGeneral3.K2 Φ x * g (x (0 : Fin (s + 1)).succ - x b.succ.succ)
        ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d) = 0 := fun b => by
      rw [int_K2 (hKb.mul (bm_diff hg _ _))]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
      refine (integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)).trans (integral_zero _ _)
      show ∫ z, VarianceGeneral3.K2 Φ (Fin.cons z (Fin.cons z' v))
        * g ((Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) (0 : Fin (s + 1)).succ
          - (Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) b.succ.succ) ∂flatTorusMeasure d = 0
      simp only [hcons, hΦ, Fin.cons_succ, Fin.cons_zero]
      exact freez v z' _
    have z3 : ∀ p ∈ VarianceGeneral2.pairs s, ∫ x, VarianceGeneral3.K2 Φ x
        * g (x p.1.succ.succ - x p.2.succ.succ)
        ∂Measure.pi (fun _ : Fin (s + 2) => flatTorusMeasure d) = 0 := fun p _ => by
      rw [int_K2 (hKb.mul (bm_diff hg _ _))]
      refine (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)).trans (integral_zero _ _)
      refine (integral_congr_ae (Filter.Eventually.of_forall fun z' => ?_)).trans (integral_zero _ _)
      show ∫ z, VarianceGeneral3.K2 Φ (Fin.cons z (Fin.cons z' v))
        * g ((Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) p.1.succ.succ
          - (Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) p.2.succ.succ) ∂flatTorusMeasure d = 0
      simp only [hcons, hΦ, Fin.cons_succ]
      exact freez v z' _
    rw [Finset.sum_eq_zero (fun b _ => z1 b), Finset.sum_eq_zero (fun b _ => z2 b),
      Finset.sum_eq_zero z3]
    simp only [add_zero]
    -- the pair `(z, z')`
    rw [int_K2 (hKb.mul (bm_diff hg _ _))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show ∫ z', ∫ z, VarianceGeneral3.K2 Φ (Fin.cons z (Fin.cons z' v))
        * g ((Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) 0
          - (Fin.cons z (Fin.cons z' v) : Fin (s + 2) → FlatTorus d) (0 : Fin (s + 1)).succ)
          ∂flatTorusMeasure d ∂flatTorusMeasure d = _
    simp only [hcons, hΦ, Fin.cons_succ, Fin.cons_zero]
    have e : ∀ z' z, A v * (pker d σ (v i - z) - 1) * (pker d σ (v j - z') - 1) * g (z - z')
        = (A v * (pker d σ (v j - z') - 1)) * ((pker d σ (v i - z) - 1) * g (z - z')) :=
      fun z' z => by ring
    simp_rw [e, integral_const_mul, int_c hσ hg]
    have e2 : ∀ z', A v * (pker d σ (v j - z') - 1) * (Pop d σ 1 g (v i - z') - ∫ u, g u ∂flatTorusMeasure d)
        = A v * ((pker d σ (v j - z') - 1) * (Pop d σ 1 g (v i - z') - ∫ u, g u ∂flatTorusMeasure d)) :=
      fun z' => by ring
    simp_rw [e2]
    rw [integral_const_mul, Q2_eval hσ hg hge]

end Generic

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 VarianceGeneral

/-! ## The closed walk with a test function on a chord; attached `p`-vertices -/

section Chords

variable {d : ℕ} {σ : ℝ}

/-- The chord functional: `m_k f(0)` for `r = 0`, `∫ p_r p_{k-r} f` otherwise (`k = n + 1`). -/
noncomputable def chordF (d : ℕ) (σ : ℝ) (n : ℕ) (r : Fin (n + 1)) (f : FlatTorus d → ℝ) : ℝ :=
  if r = 0 then torusM d σ (n + 1) * f 0
  else ∫ u, heatP d σ r.val u * heatP d σ (n + 1 - r.val) u * f u ∂flatTorusMeasure d

theorem cyT_int (hσ : 0 < σ) (n : ℕ) :
    ∫ v, cyT d σ v ∂Measure.pi (fun _ : Fin (n + 1) => flatTorusMeasure d) = torusM d σ (n + 1) :=
  cycP_int (torusRK hσ d) n

theorem heatP_bm (hσ : 0 < σ) (s : ℕ) : BM (heatP d σ s) := by
  by_cases hs : s = 0
  · subst hs
    have e0 : heatP d σ 0 = fun _ => 0 := by funext u; simp [heatP]
    rw [e0]; exact BM.const 0
  · exact ⟨(heatP_cont hσ d (by omega)).measurable, torusM d σ 1, fun u => by
      rw [abs_of_nonneg (heatP_nonneg hσ d s u)]
      exact (heatP_le hσ d (by omega) u).trans (torusM_anti hσ d le_rfl (by omega))⟩

/-- **The closed walk tested on any chord, signed test functions**. -/
theorem cyc_f (hσ : 0 < σ) {n : ℕ} {f : FlatTorus d → ℝ} (hf : BM f) (a b : Fin (n + 1)) :
    ∫ v, cyT d σ v * f (v a - v b) ∂Measure.pi (fun _ : Fin (n + 1) => flatTorusMeasure d)
      = chordF d σ n (b - a) f := by
  unfold chordF
  by_cases hab : a = b
  · subst hab
    simp only [sub_self, if_true]
    rw [integral_mul_const, cyT_int hσ n]
  · have hl : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    rw [if_neg hl]
    obtain ⟨C, hC⟩ := hf.bdd
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hcy := VarianceGeneral4.cyT_bm (d := d) hσ n
    have hP := (heatP_bm (d := d) hσ (b - a).val).mul (heatP_bm (d := d) hσ (n + 1 - (b - a).val))
    have t1 := VarianceGeneral4.cyc_pair_test hσ hab (fun u => f u + C) (hf.meas.add_const C)
      (fun u => by have := abs_le.mp (hC u); linarith) (C := 2 * C)
      (fun u => by have := abs_le.mp (hC u); linarith)
    have t2 := VarianceGeneral4.cyc_pair_test (d := d) hσ hab (fun _ => C) measurable_const
      (fun _ => hC0) (C := C) (fun _ => le_rfl)
    have e1 : ∀ v : Fin (n + 1) → FlatTorus d, cyT d σ v * f (v a - v b)
        = cyT d σ v * (f (v a - v b) + C) - cyT d σ v * C := fun v => by ring
    have e2 : ∀ u, heatP d σ (b - a).val u * heatP d σ (n + 1 - (b - a).val) u * f u
        = heatP d σ (b - a).val u * heatP d σ (n + 1 - (b - a).val) u * (f u + C)
          - heatP d σ (b - a).val u * heatP d σ (n + 1 - (b - a).val) u * C := fun u => by ring
    simp_rw [e1, e2]
    rw [integral_sub (hcy.mul ((bm_diff hf a b).add (BM.const C))).integrable
      (hcy.mul (BM.const C)).integrable, integral_sub (hP.mul (hf.add (BM.const C))).integrable
      (hP.mul (BM.const C)).integrable, t1, t2]

theorem chordF_sub (hσ : 0 < σ) {n : ℕ} {f : FlatTorus d → ℝ} (hf : BM f) (c : ℝ)
    (r : Fin (n + 1)) :
    chordF d σ n r (fun u => f u - c) = chordF d σ n r f - torusM d σ (n + 1) * c := by
  have h := cyc_f hσ (hf.sub (BM.const c)) 0 r
  have h1 := cyc_f hσ hf 0 r
  have hcy := VarianceGeneral4.cyT_bm (d := d) hσ n
  simp only [sub_zero] at h h1
  rw [← h, ← h1]
  have e : ∀ v : Fin (n + 1) → FlatTorus d, cyT d σ v * (f (v 0 - v r) - c)
      = cyT d σ v * f (v 0 - v r) - cyT d σ v * c := fun v => by ring
  simp_rw [e]
  rw [integral_sub (hcy.mul (bm_diff hf 0 r)).integrable (hcy.mul (BM.const c)).integrable,
    integral_mul_const, cyT_int hσ n]

end Chords

section Attached

variable {d : ℕ} {σ : ℝ}

theorem int_last {s : ℕ} {F : (Fin (s + 1) → FlatTorus d) → ℝ} (hF : BM F) :
    ∫ x, F x ∂Measure.pi (fun _ : Fin (s + 1) => flatTorusMeasure d)
      = ∫ v, ∫ q, F (Fin.snoc v q) ∂flatTorusMeasure d
          ∂Measure.pi (fun _ : Fin s => flatTorusMeasure d) := by
  rw [int_ins (Fin.last s) hF]; simp_rw [Fin.insertNth_last']

/-- The cycle with one vertex `q` attached to `v_a` by a `p`-edge. -/
noncomputable def A2 (d : ℕ) (σ : ℝ) (n : ℕ) (a : Fin (n + 1)) (w : Fin (n + 2) → FlatTorus d) : ℝ :=
  cy2 d σ w * pker d σ (w a.castSucc - w (Fin.last (n + 1)))

/-- The cycle with `q` attached to `v_0` and `q'` attached to `v_l`. -/
noncomputable def A3 (d : ℕ) (σ : ℝ) (n : ℕ) (l : Fin (n + 1)) (w : Fin (n + 3) → FlatTorus d) : ℝ :=
  cy3 d σ w * pker d σ (w (0 : Fin (n + 1)).castSucc.castSucc - w (Fin.last (n + 1)).castSucc)
    * pker d σ (w l.castSucc.castSucc - w (Fin.last (n + 2)))

theorem cy2_bm (hσ : 0 < σ) (n : ℕ) : BM (cy2 d σ (n := n)) :=
  ⟨cy2_meas hσ d n, _, fun w => VarianceGeneral3.cyT_le_B4 hσ n _⟩

theorem cy3_bm (hσ : 0 < σ) (n : ℕ) : BM (cy3 d σ (n := n)) :=
  ⟨cy3_meas hσ d n, _, fun w => VarianceGeneral3.cyT_le_B4 hσ n _⟩

theorem pk_bm2 (hσ : 0 < σ) {a : ℕ} (i j : Fin a) :
    BM fun w : Fin a → FlatTorus d => pker d σ (w i - w j) :=
  ⟨(pker_bm hσ).meas.comp ((measurable_pi_apply i).sub (measurable_pi_apply j)),
    (pker_bm hσ (d := d)).bdd.imp fun C h x => h _⟩

theorem A2_bm (hσ : 0 < σ) (n : ℕ) (a : Fin (n + 1)) : BM (A2 d σ n a) :=
  (cy2_bm hσ n).mul (pk_bm2 hσ _ _)

theorem A3_bm (hσ : 0 < σ) (n : ℕ) (l : Fin (n + 1)) : BM (A3 d σ n l) :=
  ((cy3_bm hσ n).mul (pk_bm2 hσ _ _)).mul (pk_bm2 hσ _ _)

theorem A2_snoc (n : ℕ) (a : Fin (n + 1)) (v : Fin (n + 1) → FlatTorus d) (q : FlatTorus d) :
    A2 d σ n a (Fin.snoc v q) = cyT d σ v * pker d σ (v a - q) := by
  unfold A2 cy2; simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem A2_f (hσ : 0 < σ) {n : ℕ} (a b : Fin (n + 1)) {f : FlatTorus d → ℝ} (hf : BM f) :
    ∫ w, A2 d σ n a w * f (w (Fin.last (n + 1)) - w b.castSucc)
        ∂Measure.pi (fun _ : Fin (n + 2) => flatTorusMeasure d)
      = ∫ v, cyT d σ v * Pop d σ 1 f (v a - v b)
          ∂Measure.pi (fun _ : Fin (n + 1) => flatTorusMeasure d) := by
  rw [int_last ((A2_bm hσ n a).mul (bm_diff hf _ _))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ∫ q, A2 d σ n a (Fin.snoc v q) * f ((Fin.snoc v q : Fin (n + 2) → FlatTorus d) (Fin.last (n + 1))
    - (Fin.snoc v q : Fin (n + 2) → FlatTorus d) b.castSucc) ∂flatTorusMeasure d = _
  simp only [A2_snoc, Fin.snoc_castSucc, Fin.snoc_last]
  have e : ∀ q, cyT d σ v * pker d σ (v a - q) * f (q - v b)
      = cyT d σ v * (pker d σ (v a - q) * f (q - v b)) := fun q => by ring
  simp_rw [e]
  rw [integral_const_mul, int_p hσ hf]

theorem A2_c (hσ : 0 < σ) {n : ℕ} (a : Fin (n + 1)) (K : ℝ) :
    ∫ w, A2 d σ n a w * K ∂Measure.pi (fun _ : Fin (n + 2) => flatTorusMeasure d)
      = torusM d σ (n + 1) * K := by
  rw [int_last ((A2_bm hσ n a).mul (BM.const K))]
  have e : ∀ v : Fin (n + 1) → FlatTorus d,
      ∫ q, A2 d σ n a (Fin.snoc v q) * K ∂flatTorusMeasure d = cyT d σ v * K := fun v => by
    simp only [A2_snoc]
    have e1 : ∀ q, cyT d σ v * pker d σ (v a - q) * K = (cyT d σ v * K) * pker d σ (v a - q) :=
      fun q => by ring
    simp_rw [e1]
    rw [integral_const_mul, int_p1 hσ, mul_one]
  simp_rw [e]
  rw [integral_mul_const, cyT_int hσ n]

theorem A3_snoc (n : ℕ) (l : Fin (n + 1)) (w : Fin (n + 2) → FlatTorus d) (q : FlatTorus d) :
    A3 d σ n l (Fin.snoc w q) = A2 d σ n 0 w * pker d σ (w l.castSucc - q) := by
  unfold A3 A2 cy3 cy2; simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem A3_f (hσ : 0 < σ) {n : ℕ} (l : Fin (n + 1)) {f : FlatTorus d → ℝ} (hf : BM f)
    (hfe : ∀ u, f (-u) = f u) :
    ∫ w, A3 d σ n l w * f (w (Fin.last (n + 1)).castSucc - w (Fin.last (n + 2)))
        ∂Measure.pi (fun _ : Fin (n + 3) => flatTorusMeasure d)
      = ∫ v, cyT d σ v * Pop d σ 1 (Pop d σ 1 f) (v 0 - v l)
          ∂Measure.pi (fun _ : Fin (n + 1) => flatTorusMeasure d) := by
  rw [int_last ((A3_bm hσ n l).mul (bm_diff hf _ _)), ← A2_f hσ 0 l (conv_bm hσ hf)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  show ∫ q, A3 d σ n l (Fin.snoc w q) * f ((Fin.snoc w q : Fin (n + 3) → FlatTorus d)
    (Fin.last (n + 1)).castSucc - (Fin.snoc w q : Fin (n + 3) → FlatTorus d) (Fin.last (n + 2)))
    ∂flatTorusMeasure d = _
  simp only [A3_snoc, Fin.snoc_castSucc, Fin.snoc_last]
  have e : ∀ q, A2 d σ n 0 w * pker d σ (w l.castSucc - q) * f (w (Fin.last (n + 1)) - q)
      = A2 d σ n 0 w * (pker d σ (w l.castSucc - q) * f (q - w (Fin.last (n + 1)))) := fun q => by
    rw [show w (Fin.last (n + 1)) - q = -(q - w (Fin.last (n + 1))) by abel, hfe]; ring
  simp_rw [e]
  rw [integral_const_mul, int_p hσ hf,
    show w l.castSucc - w (Fin.last (n + 1)) = -(w (Fin.last (n + 1)) - w l.castSucc) by abel,
    Pop_even d σ hfe 1]

end Attached

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 VarianceGeneral

/-! ## (a) The pair kernels of the blocks with attached vertices, tested against even `g`
    (Step 3, lines `Q₁`, `Q₂`, `Q₃`, every `k = n + 1`) -/

section Blocks

variable {d : ℕ} {σ : ℝ}

theorem hp_test0 {a : ℕ} {F : (Fin a → FlatTorus d) → ℝ} (hF : BM F) (hT : VarianceGeneral2.TI F)
    (h0 : ∫ x, F x ∂Measure.pi (fun _ : Fin a => flatTorusMeasure d) = 0)
    {g : FlatTorus d → ℝ} (hg : BM g) :
    ∫ u, VarianceGeneral3.hp F u * g u ∂flatTorusMeasure d
      = ∑ p ∈ VarianceGeneral2.pairs a,
          ∫ x, F x * g (x p.1 - x p.2) ∂Measure.pi (fun _ : Fin a => flatTorusMeasure d) := by
  rw [hp_test hF hT hg, h0]; simp

/-- `𝒬g = 𝒫g - ∫ g`. -/
noncomputable def qg (d : ℕ) (σ : ℝ) (g : FlatTorus d → ℝ) (u : FlatTorus d) : ℝ :=
  Pop d σ 1 g u - ∫ z, g z ∂flatTorusMeasure d

/-- `𝒬²g = 𝒫²g - ∫ g`. -/
noncomputable def q2 (d : ℕ) (σ : ℝ) (g : FlatTorus d → ℝ) (u : FlatTorus d) : ℝ :=
  Pop d σ 1 (Pop d σ 1 g) u - ∫ z, g z ∂flatTorusMeasure d

theorem qg_bm (hσ : 0 < σ) {g : FlatTorus d → ℝ} (hg : BM g) : BM (qg d σ g) :=
  (conv_bm hσ hg).sub (BM.const _)

theorem q2_bm (hσ : 0 < σ) {g : FlatTorus d → ℝ} (hg : BM g) : BM (q2 d σ g) :=
  (conv_bm hσ (conv_bm hσ hg)).sub (BM.const _)

theorem qg_ev {g : FlatTorus d → ℝ} (hge : ∀ u, g (-u) = g u) (u : FlatTorus d) :
    qg d σ g (-u) = qg d σ g u := by unfold qg; rw [Pop_even d σ hge 1]

theorem q2_ev {g : FlatTorus d → ℝ} (hge : ∀ u, g (-u) = g u) (u : FlatTorus d) :
    q2 d σ g (-u) = q2 d σ g u := by
  unfold q2; rw [← Pop_succ', Pop_even d σ hge 2]

theorem P1_ev {f : FlatTorus d → ℝ} (hfe : ∀ u, f (-u) = f u) (u : FlatTorus d) :
    Pop d σ 1 f (-u) = Pop d σ 1 f u := Pop_even d σ hfe 1 u

theorem swap_ev {f : FlatTorus d → ℝ} (hfe : ∀ u, f (-u) = f u) (x y : FlatTorus d) :
    f (x - y) = f (y - x) := by rw [← neg_sub, hfe]

/-- Block `A` (line `Q₁`): `T_A(g) = ∑_{b} chord_b(𝒬g)`. -/
theorem block_A (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K1 (PhiA d σ n)) u * g u ∂flatTorusMeasure d
      = ∑ b : Fin (n + 1), chordF d σ n b (qg d σ g) := by
  have hΦ : ∀ v z, PhiA d σ n (v, z) = cyT d σ v * (pker d σ (v 0 - z) - 1) := fun v z => by
    unfold PhiA; rw [hp1]
  obtain ⟨hb, h0, hs⟩ := K1_gen hσ (VarianceGeneral4.cyT_bm hσ n) 0 hΦ hg
  rw [hp_test0 hb (VarianceGeneral3.K1_TI (VarianceGeneral3.PhiA_TI n)) h0 hg, hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := cyc_f hσ (qg_bm hσ hg) 0 b
  simp only [qg, sub_zero] at h
  exact h

/-- Block `B` (line `Q₁`): `T_B(g) = ∑_r chord_r(𝒫𝒬g) + m_k (𝒬g)(0)`. -/
theorem block_B (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K1 (PhiB d σ n)) u * g u ∂flatTorusMeasure d
      = ∑ r : Fin (n + 1), chordF d σ n r (Pop d σ 1 (qg d σ g))
        + torusM d σ (n + 1) * qg d σ g 0 := by
  have hΦ : ∀ v z, PhiB d σ n (v, z)
      = A2 d σ n 0 v * (pker d σ (v (Fin.last (n + 1)) - z) - 1) := fun v z => by
    unfold PhiB A2 cy2; rw [hp1]; simp
  obtain ⟨hb, h0, hs⟩ := K1_gen hσ (A2_bm hσ n 0) (Fin.last (n + 1)) hΦ hg
  rw [hp_test0 hb (VarianceGeneral3.K1_TI (VarianceGeneral3.PhiB_TI n)) h0 hg, hs,
    Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun r _ => ?_
    have h1 := A2_f hσ 0 r (qg_bm hσ hg)
    have h2 := cyc_f hσ (conv_bm hσ (qg_bm hσ hg)) 0 r
    simp only [qg, sub_zero] at h1 h2
    rw [h1, h2]
  · have h1 := A2_c hσ (d := d) (n := n) 0 (qg d σ g 0)
    simp only [sub_self]
    simp only [qg] at h1 ⊢
    exact h1

theorem fin00 (n : ℕ) : (0 : Fin (n + 1)) - 0 = 0 := sub_self 0

/-- Block `ε²` (line `Q₂`): `T(g) = chord_0(𝒬²g) = m_k (𝒬²g)(0)`. -/
theorem block_EE (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiEE d σ n)) u * g u ∂flatTorusMeasure d
      = chordF d σ n 0 (q2 d σ g) := by
  have hΦ : ∀ v z z', PhiEE d σ n (v, z, z')
      = cyT d σ v * (pker d σ (v 0 - z) - 1) * (pker d σ (v 0 - z') - 1) := fun v z z' => by
    unfold PhiEE; rw [hp1]
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (VarianceGeneral4.cyT_bm hσ n) 0 0 hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiEE_TI n)) h0 hg, hs]
  have h := cyc_f hσ (q2_bm hσ hg) (0 : Fin (n + 1)) 0
  rw [fin00] at h
  exact h

/-- Block `ε (P̃ε)` (line `Q₂`): `T(g) = chord_0(𝒫𝒬²g)`. -/
theorem block_EB (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiEB d σ n)) u * g u ∂flatTorusMeasure d
      = chordF d σ n 0 (Pop d σ 1 (q2 d σ g)) := by
  have hΦ : ∀ v z z', PhiEB d σ n (v, z, z')
      = A2 d σ n 0 v * (pker d σ (v (0 : Fin (n + 1)).castSucc - z) - 1)
        * (pker d σ (v (Fin.last (n + 1)) - z') - 1) := fun v z z' => by
    unfold PhiEB A2; rw [hp1]; ring
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (A2_bm hσ n 0) _ _ hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiEB_TI n)) h0 hg, hs]
  have e1 : ∀ w : Fin (n + 2) → FlatTorus d,
      A2 d σ n 0 w * (Pop d σ 1 (Pop d σ 1 g) (w (0 : Fin (n + 1)).castSucc - w (Fin.last (n + 1)))
        - ∫ u, g u ∂flatTorusMeasure d)
      = A2 d σ n 0 w * q2 d σ g (w (Fin.last (n + 1)) - w (0 : Fin (n + 1)).castSucc) := fun w => by
    rw [swap_ev (q2_ev hge) (w (Fin.last (n + 1)))]; rfl
  simp_rw [e1]
  rw [A2_f hσ 0 0 (q2_bm hσ hg)]
  have h := cyc_f hσ (conv_bm hσ (q2_bm hσ hg)) (0 : Fin (n + 1)) 0
  rw [fin00] at h
  exact h

/-- Block `P̃ε²` (line `Q₂`): `T(g) = m_k (𝒬²g)(0)`. -/
theorem block_S (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiS d σ n)) u * g u ∂flatTorusMeasure d
      = torusM d σ (n + 1) * q2 d σ g 0 := by
  have hΦ : ∀ v z z', PhiS d σ n (v, z, z')
      = A2 d σ n 0 v * (pker d σ (v (Fin.last (n + 1)) - z) - 1)
        * (pker d σ (v (Fin.last (n + 1)) - z') - 1) := fun v z z' => by
    unfold PhiS A2; rw [hp1]
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (A2_bm hσ n 0) _ _ hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiS_TI n)) h0 hg, hs]
  simp only [sub_self]
  exact A2_c hσ (d := d) (n := n) 0 (q2 d σ g 0)

/-- Block `(P̃ε)²` (line `Q₂`): `T(g) = chord_0(𝒫²𝒬²g)`. -/
theorem block_BB (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiBB d σ n)) u * g u ∂flatTorusMeasure d
      = chordF d σ n 0 (Pop d σ 1 (Pop d σ 1 (q2 d σ g))) := by
  have hΦ : ∀ v z z', PhiBB d σ n (v, z, z')
      = A3 d σ n 0 v * (pker d σ (v (Fin.last (n + 1)).castSucc - z) - 1)
        * (pker d σ (v (Fin.last (n + 2)) - z') - 1) := fun v z z' => by
    unfold PhiBB A3; rw [hp1]; ring
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (A3_bm hσ n 0) _ _ hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiBB_TI n)) h0 hg, hs]
  show ∫ w, A3 d σ n 0 w * q2 d σ g (w (Fin.last (n + 1)).castSucc - w (Fin.last (n + 2)))
    ∂Measure.pi (fun _ : Fin (n + 3) => flatTorusMeasure d) = _
  rw [A3_f hσ 0 (q2_bm hσ hg) (q2_ev hge)]
  have h := cyc_f hσ (conv_bm hσ (conv_bm hσ (q2_bm hσ hg))) (0 : Fin (n + 1)) 0
  rw [fin00] at h
  exact h

/-- Block `ε_{v₀} ε_{v_l}` (line `Q₃`): `T(g) = chord_l(𝒬²g)`. -/
theorem block_Qee (hσ : 0 < σ) (n : ℕ) (l : Fin (n + 1)) {g : FlatTorus d → ℝ} (hg : BM g)
    (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQee d σ n l)) u * g u ∂flatTorusMeasure d
      = chordF d σ n l (q2 d σ g) := by
  have hΦ : ∀ v z z', PhiQee d σ n l (v, z, z')
      = cyT d σ v * (pker d σ (v 0 - z) - 1) * (pker d σ (v l - z') - 1) := fun v z z' => by
    unfold PhiQee; rw [hp1]
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (VarianceGeneral4.cyT_bm hσ n) 0 l hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiQee_TI n l)) h0 hg, hs]
  have h := cyc_f hσ (q2_bm hσ hg) (0 : Fin (n + 1)) l
  rw [sub_zero] at h
  exact h

/-- Block `ε_{v₀} (P̃ε)_{v_l}` (line `Q₃`): `T(g) = chord_l(𝒫𝒬²g)`. -/
theorem block_Qeb (hσ : 0 < σ) (n : ℕ) (l : Fin (n + 1)) {g : FlatTorus d → ℝ} (hg : BM g)
    (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQeb d σ n l)) u * g u ∂flatTorusMeasure d
      = chordF d σ n l (Pop d σ 1 (q2 d σ g)) := by
  have hΦ : ∀ v z z', PhiQeb d σ n l (v, z, z')
      = A2 d σ n l v * (pker d σ (v (0 : Fin (n + 1)).castSucc - z) - 1)
        * (pker d σ (v (Fin.last (n + 1)) - z') - 1) := fun v z z' => by
    unfold PhiQeb A2; rw [hp1]; ring
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (A2_bm hσ n l) _ _ hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiQeb_TI n l)) h0 hg, hs]
  have e1 : ∀ w : Fin (n + 2) → FlatTorus d,
      A2 d σ n l w * (Pop d σ 1 (Pop d σ 1 g) (w (0 : Fin (n + 1)).castSucc - w (Fin.last (n + 1)))
        - ∫ u, g u ∂flatTorusMeasure d)
      = A2 d σ n l w * q2 d σ g (w (Fin.last (n + 1)) - w (0 : Fin (n + 1)).castSucc) := fun w => by
    rw [swap_ev (q2_ev hge) (w (Fin.last (n + 1)))]; rfl
  simp_rw [e1]
  rw [A2_f hσ l 0 (q2_bm hσ hg)]
  have e2 : ∀ v : Fin (n + 1) → FlatTorus d, cyT d σ v * Pop d σ 1 (q2 d σ g) (v l - v 0)
      = cyT d σ v * Pop d σ 1 (q2 d σ g) (v 0 - v l) := fun v => by
    rw [swap_ev (P1_ev (q2_ev hge)) (v l)]
  simp_rw [e2]
  have h := cyc_f hσ (conv_bm hσ (q2_bm hσ hg)) (0 : Fin (n + 1)) l
  rw [sub_zero] at h
  exact h

/-- Block `(P̃ε)_{v₀} ε_{v_l}` (line `Q₃`): `T(g) = chord_l(𝒫𝒬²g)`. -/
theorem block_Qbe (hσ : 0 < σ) (n : ℕ) (l : Fin (n + 1)) {g : FlatTorus d → ℝ} (hg : BM g)
    (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbe d σ n l)) u * g u ∂flatTorusMeasure d
      = chordF d σ n l (Pop d σ 1 (q2 d σ g)) := by
  have hΦ : ∀ v z z', PhiQbe d σ n l (v, z, z')
      = A2 d σ n 0 v * (pker d σ (v (Fin.last (n + 1)) - z) - 1)
        * (pker d σ (v l.castSucc - z') - 1) := fun v z z' => by
    unfold PhiQbe A2; rw [hp1]
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (A2_bm hσ n 0) _ _ hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiQbe_TI n l)) h0 hg, hs]
  show ∫ w, A2 d σ n 0 w * q2 d σ g (w (Fin.last (n + 1)) - w l.castSucc)
    ∂Measure.pi (fun _ : Fin (n + 2) => flatTorusMeasure d) = _
  rw [A2_f hσ 0 l (q2_bm hσ hg)]
  have h := cyc_f hσ (conv_bm hσ (q2_bm hσ hg)) (0 : Fin (n + 1)) l
  rw [sub_zero] at h
  exact h

/-- Block `(P̃ε)_{v₀} (P̃ε)_{v_l}` (line `Q₃`): `T(g) = chord_l(𝒫²𝒬²g)`. -/
theorem block_Qbb (hσ : 0 < σ) (n : ℕ) (l : Fin (n + 1)) {g : FlatTorus d → ℝ} (hg : BM g)
    (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbb d σ n l)) u * g u ∂flatTorusMeasure d
      = chordF d σ n l (Pop d σ 1 (Pop d σ 1 (q2 d σ g))) := by
  have hΦ : ∀ v z z', PhiQbb d σ n l (v, z, z')
      = A3 d σ n l v * (pker d σ (v (Fin.last (n + 1)).castSucc - z) - 1)
        * (pker d σ (v (Fin.last (n + 2)) - z') - 1) := fun v z z' => by
    unfold PhiQbb A3; rw [hp1]; ring
  obtain ⟨hb, h0, hs⟩ := K2_gen hσ (A3_bm hσ n l) _ _ hΦ hg hge
  rw [hp_test0 hb (VarianceGeneral3.K2_TI (VarianceGeneral3.PhiQbb_TI n l)) h0 hg, hs]
  show ∫ w, A3 d σ n l w * q2 d σ g (w (Fin.last (n + 1)).castSucc - w (Fin.last (n + 2)))
    ∂Measure.pi (fun _ : Fin (n + 3) => flatTorusMeasure d) = _
  rw [A3_f hσ l (q2_bm hσ hg) (q2_ev hge)]
  have h := cyc_f hσ (conv_bm hσ (conv_bm hσ (q2_bm hσ hg))) (0 : Fin (n + 1)) l
  rw [sub_zero] at h
  exact h

end Blocks

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 VarianceGeneral

/-! ## (b) Summation: `∫ h_QT g = ∫ (H_k/2) g` for every even bounded measurable `g` -/

section Sum

variable {d : ℕ} {σ : ℝ}

theorem int_comb {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → FlatTorus d → ℝ)
    (hF : ∀ i, BM (F i)) :
    ∫ u, ∑ i ∈ s, c i * F i u ∂flatTorusMeasure d = ∑ i ∈ s, c i * ∫ u, F i u ∂flatTorusMeasure d := by
  rw [integral_finset_sum _ (fun i _ => ((BM.const (c i)).mul (hF i)).integrable)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem hp_bm' {a : ℕ} {F : (Fin a → FlatTorus d) → ℝ} (hF : BM F) : BM (VarianceGeneral3.hp F) := by
  obtain ⟨B, hB⟩ := hF.bdd
  obtain ⟨hm, hb⟩ := VarianceGeneral3.hpair_bm (ν := flatTorusMeasure d) hF hB
  exact ⟨hm, _, hb⟩

theorem Pop_comm (h : FlatTorus d → ℝ) : ∀ j, Pop d σ j (Pop d σ 1 h) = Pop d σ (j + 1) h := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih => rw [Pop_succ', ih]; rfl

theorem Pop_adj_n (hσ : 0 < σ) : ∀ j {f h : FlatTorus d → ℝ}, BM f → BM h →
    ∫ u, Pop d σ j f u * h u ∂flatTorusMeasure d = ∫ u, f u * Pop d σ j h u ∂flatTorusMeasure d := by
  intro j
  induction j with
  | zero => intro f h _ _; rfl
  | succ j ih =>
    intro f h hf hh
    rw [Pop_succ', Pop_adj hσ (Pop_bm hσ hf j) hh, ih hf (conv_bm hσ hh), Pop_comm]

/-- `S_j = ∑_{l=1}^{k-1} ∫ p_l p_{k-l} 𝒫ʲg` (`k = n + 1`). -/
noncomputable def Sg (d : ℕ) (σ : ℝ) (n j : ℕ) (g : FlatTorus d → ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico 1 (n + 1),
    ∫ u, heatP d σ l u * heatP d σ (n + 1 - l) u * Pop d σ j g u ∂flatTorusMeasure d

theorem gam_bm (hσ : 0 < σ) (k : ℕ) : BM (gam d σ k) := by
  obtain ⟨C, hC⟩ := bound_of_cont d (gam_cont hσ d k)
  exact ⟨(gam_cont hσ d k).measurable, C, hC⟩

theorem gam_test (hσ : 0 < σ) (n : ℕ) {h : FlatTorus d → ℝ} (hh : BM h) :
    ∫ u, gam d σ (n + 1) u * h u ∂flatTorusMeasure d
      = ∑ l ∈ Finset.Ico 1 (n + 1),
          ∫ u, heatP d σ l u * heatP d σ (n + 1 - l) u * h u ∂flatTorusMeasure d := by
  have e : ∀ u, gam d σ (n + 1) u * h u = ∑ l ∈ Finset.Ico 1 (n + 1),
      heatP d σ l u * heatP d σ (n + 1 - l) u * h u := fun u => by
    unfold gam
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_Ico.mp hl
    rw [BiasGeneral6.heatP_eq_pker d σ hl'.1, BiasGeneral6.heatP_eq_pker d σ (by omega : 1 ≤ n + 1 - l)]
  simp_rw [e]
  exact integral_finset_sum _ fun l _ =>
    (((heatP_bm hσ l).mul (heatP_bm hσ (n + 1 - l))).mul hh).integrable

theorem pker_test (hσ : 0 < σ) (j : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) :
    ∫ u, Pop d σ j (pker d σ) u * g u ∂flatTorusMeasure d = Pop d σ (j + 1) g 0 := by
  rw [Pop_adj_n hσ j (pker_bm hσ) hg, Pop_at0 hσ]; rfl

theorem gamPop_test (hσ : 0 < σ) (n j : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) :
    ∫ u, Pop d σ j (gam d σ (n + 1)) u * g u ∂flatTorusMeasure d = Sg d σ n j g := by
  rw [Pop_adj_n hσ j (gam_bm hσ (n + 1)) hg, gam_test hσ n (Pop_bm hσ hg j)]; rfl

/-- **The target**: `∫ (H_k/2) g = (k/2)(S₀ - 4S₁ + 6S₂ - 4S₃ + S₄) - k m_k (e₁ - 3e₂ + 3e₃ - e₄)`,
    `e_j = (𝒫ʲg)(0)`. -/
theorem target_test (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) :
    ∫ u, 1 / 2 * Hk d σ (n + 1) u * g u ∂flatTorusMeasure d
      = ((n : ℝ) + 1) / 2 * (Sg d σ n 0 g - 4 * Sg d σ n 1 g + 6 * Sg d σ n 2 g
          - 4 * Sg d σ n 3 g + Sg d σ n 4 g)
        - ((n : ℝ) + 1) * torusM d σ (n + 1) * (Pop d σ 1 g 0 - 3 * Pop d σ 2 g 0
          + 3 * Pop d σ 3 g 0 - Pop d σ 4 g 0) := by
  set k : ℝ := (n : ℝ) + 1 with hk
  set m := torusM d σ (n + 1)
  let F : Fin 9 → FlatTorus d → ℝ := ![fun u => Pop d σ 0 (gam d σ (n + 1)) u * g u,
    fun u => Pop d σ 1 (gam d σ (n + 1)) u * g u, fun u => Pop d σ 2 (gam d σ (n + 1)) u * g u,
    fun u => Pop d σ 3 (gam d σ (n + 1)) u * g u, fun u => Pop d σ 4 (gam d σ (n + 1)) u * g u,
    fun u => Pop d σ 0 (pker d σ) u * g u, fun u => Pop d σ 1 (pker d σ) u * g u,
    fun u => Pop d σ 2 (pker d σ) u * g u, fun u => Pop d σ 3 (pker d σ) u * g u]
  let c : Fin 9 → ℝ := ![k / 2, -4 * (k / 2), 6 * (k / 2), -4 * (k / 2), k / 2,
    -(k * m), 3 * (k * m), -3 * (k * m), k * m]
  have hF : ∀ i, BM (F i) := by
    intro i
    fin_cases i
    · exact (Pop_bm hσ (gam_bm hσ (n + 1)) 0).mul hg
    · exact (Pop_bm hσ (gam_bm hσ (n + 1)) 1).mul hg
    · exact (Pop_bm hσ (gam_bm hσ (n + 1)) 2).mul hg
    · exact (Pop_bm hσ (gam_bm hσ (n + 1)) 3).mul hg
    · exact (Pop_bm hσ (gam_bm hσ (n + 1)) 4).mul hg
    · exact (Pop_bm hσ (pker_bm hσ) 0).mul hg
    · exact (Pop_bm hσ (pker_bm hσ) 1).mul hg
    · exact (Pop_bm hσ (pker_bm hσ) 2).mul hg
    · exact (Pop_bm hσ (pker_bm hσ) 3).mul hg
  have e : ∀ u, 1 / 2 * Hk d σ (n + 1) u * g u = ∑ i : Fin 9, c i * F i u := fun u => by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, c, F, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    unfold Hk diff4 diff3
    simp only [hk, m]
    push_cast
    ring
  simp_rw [e]
  rw [int_comb _ c F hF]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, c, F, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rw [gamPop_test hσ n 0 hg, gamPop_test hσ n 1 hg, gamPop_test hσ n 2 hg, gamPop_test hσ n 3 hg,
    gamPop_test hσ n 4 hg, pker_test hσ 0 hg, pker_test hσ 1 hg, pker_test hσ 2 hg,
    pker_test hσ 3 hg]
  ring

theorem chord_sum (n : ℕ) (f : FlatTorus d → ℝ) :
    ∑ b : Fin (n + 1), chordF d σ n b f
      = torusM d σ (n + 1) * f 0 + ∑ l ∈ Finset.Ico 1 (n + 1),
          ∫ u, heatP d σ l u * heatP d σ (n + 1 - l) u * f u ∂flatTorusMeasure d := by
  rw [Fin.sum_univ_succ]
  unfold chordF
  simp only [Fin.succ_ne_zero, if_false, Fin.val_succ]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range, Fin.sum_univ_eq_sum_range
    (fun i => ∫ u, heatP d σ (i + 1) u * heatP d σ (n + 1 - (i + 1)) u * f u ∂flatTorusMeasure d) n,
    show n + 1 - 1 = n by omega]
  exact Finset.sum_congr rfl fun i _ => by rw [add_comm 1 i]

theorem chord_sum' (n : ℕ) (f : FlatTorus d → ℝ) :
    ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), chordF d σ n l f
      = ∑ l ∈ Finset.Ico 1 (n + 1),
          ∫ u, heatP d σ l u * heatP d σ (n + 1 - l) u * f u ∂flatTorusMeasure d := by
  have h := Finset.sum_erase_eq_sub (s := Finset.univ) (f := fun l => chordF d σ n l f)
    (Finset.mem_univ (0 : Fin (n + 1)))
  rw [h, chord_sum]
  unfold chordF; simp

theorem Pop1_R (hσ : 0 < σ) {g : FlatTorus d → ℝ} (hg : BM g) (j : ℕ) (a : ℝ) :
    Pop d σ 1 (fun u => Pop d σ j g u - a) = fun u => Pop d σ (j + 1) g u - a := by
  funext u; rw [Pop_sub_const hσ (Pop_bm hσ hg j)]; rfl

theorem chord_R_sum (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) (j : ℕ) (a : ℝ) :
    ∑ b : Fin (n + 1), chordF d σ n b (fun u => Pop d σ j g u - a)
      = torusM d σ (n + 1) * Pop d σ j g 0 + Sg d σ n j g
        - ((n : ℝ) + 1) * (torusM d σ (n + 1) * a) := by
  simp_rw [chordF_sub hσ (Pop_bm hσ hg j) a]
  rw [Finset.sum_sub_distrib, chord_sum]
  simp [Sg]

theorem chord_R_sum' (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) (j : ℕ) (a : ℝ) :
    ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), chordF d σ n l (fun u => Pop d σ j g u - a)
      = Sg d σ n j g - (n : ℝ) * (torusM d σ (n + 1) * a) := by
  simp_rw [chordF_sub hσ (Pop_bm hσ hg j) a]
  rw [Finset.sum_sub_distrib, chord_sum']
  simp [Sg, Finset.card_erase_of_mem]

theorem chord_R0 (n : ℕ) {g : FlatTorus d → ℝ} (j : ℕ) (a : ℝ) :
    chordF d σ n 0 (fun u => Pop d σ j g u - a) = torusM d σ (n + 1) * (Pop d σ j g 0 - a) := by
  unfold chordF; simp

/-- **(b) for every `k = n + 1`**: the pair kernel of `QT` tested against an even bounded
    measurable `g` gives the same value as `H_k / 2`. -/
theorem hQT_test (hσ : 0 < σ) (n : ℕ) {g : FlatTorus d → ℝ} (hg : BM g) (hge : ∀ u, g (-u) = g u) :
    ∫ u, VarianceGeneral3.hQT d σ n u * g u ∂flatTorusMeasure d
      = ((n : ℝ) + 1) / 2 * (Sg d σ n 0 g - 4 * Sg d σ n 1 g + 6 * Sg d σ n 2 g
          - 4 * Sg d σ n 3 g + Sg d σ n 4 g)
        - ((n : ℝ) + 1) * torusM d σ (n + 1) * (Pop d σ 1 g 0 - 3 * Pop d σ 2 g 0
          + 3 * Pop d σ 3 g 0 - Pop d σ 4 g 0) := by
  set a := ∫ u, g u ∂flatTorusMeasure d with ha
  set m := torusM d σ (n + 1) with hm
  have hq1 : Pop d σ 1 (qg d σ g) = fun u => Pop d σ 2 g u - a := Pop1_R hσ hg 1 a
  have hq2 : Pop d σ 1 (q2 d σ g) = fun u => Pop d σ 3 g u - a := Pop1_R hσ hg 2 a
  -- the block values
  have vA : ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K1 (PhiA d σ n)) u * g u ∂flatTorusMeasure d
      = m * Pop d σ 1 g 0 + Sg d σ n 1 g - ((n : ℝ) + 1) * (m * a) := by
    rw [block_A hσ n hg]; exact chord_R_sum hσ n hg 1 a
  have vB : ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K1 (PhiB d σ n)) u * g u ∂flatTorusMeasure d
      = m * Pop d σ 2 g 0 + Sg d σ n 2 g - ((n : ℝ) + 1) * (m * a) + m * (Pop d σ 1 g 0 - a) := by
    rw [block_B hσ n hg, hq1, chord_R_sum hσ n hg 2 a]
    rfl
  have vEE : ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiEE d σ n)) u * g u ∂flatTorusMeasure d
      = m * (Pop d σ 2 g 0 - a) := by
    rw [block_EE hσ n hg hge]; exact chord_R0 n 2 a
  have vEB : ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiEB d σ n)) u * g u ∂flatTorusMeasure d
      = m * (Pop d σ 3 g 0 - a) := by
    rw [block_EB hσ n hg hge, hq2]
    exact chord_R0 n 3 a
  have vS : ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiS d σ n)) u * g u ∂flatTorusMeasure d
      = m * (Pop d σ 2 g 0 - a) := by
    rw [block_S hσ n hg hge]; rfl
  have vBB : ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiBB d σ n)) u * g u ∂flatTorusMeasure d
      = m * (Pop d σ 4 g 0 - a) := by
    rw [block_BB hσ n hg hge, hq2, Pop1_R hσ hg 3 a]
    exact chord_R0 n 4 a
  have vQ : ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (4 * ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQee d σ n l)) u * g u ∂flatTorusMeasure d
        - 2 * ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQeb d σ n l)) u * g u ∂flatTorusMeasure d
        - 2 * ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbe d σ n l)) u * g u ∂flatTorusMeasure d
        + ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbb d σ n l)) u * g u ∂flatTorusMeasure d)
      = 4 * (Sg d σ n 2 g - n * (m * a)) - 4 * (Sg d σ n 3 g - n * (m * a))
        + (Sg d σ n 4 g - n * (m * a)) := by
    have e : ∀ l : Fin (n + 1),
        4 * ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQee d σ n l)) u * g u ∂flatTorusMeasure d
          - 2 * ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQeb d σ n l)) u * g u ∂flatTorusMeasure d
          - 2 * ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbe d σ n l)) u * g u ∂flatTorusMeasure d
          + ∫ u, VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbb d σ n l)) u * g u ∂flatTorusMeasure d
        = 4 * chordF d σ n l (fun u => Pop d σ 2 g u - a)
          - 4 * chordF d σ n l (fun u => Pop d σ 3 g u - a)
          + chordF d σ n l (fun u => Pop d σ 4 g u - a) := fun l => by
      rw [block_Qee hσ n l hg hge, block_Qeb hσ n l hg hge, block_Qbe hσ n l hg hge,
        block_Qbb hσ n l hg hge, hq2, Pop1_R hσ hg 3 a]
      have : chordF d σ n l (q2 d σ g) = chordF d σ n l (fun u => Pop d σ 2 g u - a) := rfl
      rw [this]; ring
    rw [Finset.sum_congr rfl fun l _ => e l, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, chord_R_sum' hσ n hg 2 a,
      chord_R_sum' hσ n hg 3 a, chord_R_sum' hσ n hg 4 a]
  have vC : ∫ u, VarianceGeneral3.hp (cyT d σ (n := n)) u * g u ∂flatTorusMeasure d
      = ((n : ℝ) + 1) / 2 * Sg d σ n 0 g - ((n : ℝ) + 1) / 2 * n * (m * a) := by
    have h1 : ∫ u, VarianceGeneral3.hp (cyT d σ (n := n)) u * g u ∂flatTorusMeasure d
        = ∫ u, (1 / 2 * (((n : ℝ) + 1) * gam d σ (n + 1) u - ((n : ℝ) + 1) * n * m)) * g u
          ∂flatTorusMeasure d :=
      integral_congr_ae ((VarianceGeneral4.hp_cyc (d := d) hσ n).mono fun u hu => by
        show VarianceGeneral3.hp (cyT d σ (n := n)) u * g u = _
        rw [hu])
    have e : ∀ u, (1 / 2 * (((n : ℝ) + 1) * gam d σ (n + 1) u - ((n : ℝ) + 1) * n * m)) * g u
        = ((n : ℝ) + 1) / 2 * (gam d σ (n + 1) u * g u) - ((n : ℝ) + 1) / 2 * n * m * g u :=
      fun u => by ring
    rw [h1]; simp_rw [e]
    rw [integral_sub (((gam_bm hσ (n + 1)).mul hg).const_mul _).integrable
      ((BM.const _).mul hg).integrable, integral_const_mul, integral_const_mul,
      gam_test hσ n hg]
    unfold Sg; simp only [Pop_zero]; ring
  -- the linear split of `∫ h_QT g`
  let F : Fin 7 → FlatTorus d → ℝ := ![
    fun u => VarianceGeneral3.hp (cyT d σ (n := n)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K1 (PhiA d σ n)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K1 (PhiB d σ n)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiEE d σ n)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiEB d σ n)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiBB d σ n)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiS d σ n)) u * g u]
  let c : Fin 7 → ℝ := ![1, -2 * ((n : ℝ) + 1), (n : ℝ) + 1, 3 * ((n : ℝ) + 1),
    -3 * ((n : ℝ) + 1), (n : ℝ) + 1, -((n : ℝ) + 1)]
  let G : Fin (n + 1) → Fin 4 → FlatTorus d → ℝ := fun l => ![
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQee d σ n l)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQeb d σ n l)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbe d σ n l)) u * g u,
    fun u => VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbb d σ n l)) u * g u]
  let c' : Fin 4 → ℝ := ![4, -2, -2, 1]
  have hbA := (VarianceGeneral3.K1_bm (PhiA_meas hσ d n) (VarianceGeneral3.PhiA_le_B4 hσ n)).1
  have hbB := (VarianceGeneral3.K1_bm (PhiB_meas hσ d n) (VarianceGeneral3.PhiB_le_B4 hσ n)).1
  have hb2 : ∀ {s : ℕ} {Φ : (Fin s → FlatTorus d) × FlatTorus d × FlatTorus d → ℝ},
      Measurable Φ → (∃ C, ∀ p, |Φ p| ≤ C) → BM (VarianceGeneral3.K2 Φ) := fun hΦ ⟨C, hC⟩ =>
    (VarianceGeneral3.K2_bm hΦ hC).1
  have hF : ∀ i, BM (F i) := by
    have hPB := fun l => BiasGeneral6.phi_bounds hσ d n l
    intro i
    fin_cases i
    · exact (hp_bm' (VarianceGeneral4.cyT_bm hσ n)).mul hg
    · exact (hp_bm' hbA).mul hg
    · exact (hp_bm' hbB).mul hg
    · exact (hp_bm' (hb2 (PhiEE_meas hσ d n) ⟨_, (hPB 0).1⟩)).mul hg
    · exact (hp_bm' (hb2 (PhiEB_meas hσ d n) ⟨_, (hPB 0).2.1⟩)).mul hg
    · exact (hp_bm' (hb2 (PhiBB_meas hσ d n) ⟨_, (hPB 0).2.2.1⟩)).mul hg
    · exact (hp_bm' (hb2 (PhiS_meas hσ d n) ⟨_, (hPB 0).2.2.2.1⟩)).mul hg
  have hG : ∀ l i, BM (G l i) := by
    have hPB := fun l => BiasGeneral6.phi_bounds hσ d n l
    intro l i
    fin_cases i
    · exact (hp_bm' (hb2 (PhiQee_meas hσ d n l) ⟨_, (hPB l).2.2.2.2.1⟩)).mul hg
    · exact (hp_bm' (hb2 (PhiQeb_meas hσ d n l) ⟨_, (hPB l).2.2.2.2.2.1⟩)).mul hg
    · exact (hp_bm' (hb2 (PhiQbe_meas hσ d n l) ⟨_, (hPB l).2.2.2.2.2.2.1⟩)).mul hg
    · exact (hp_bm' (hb2 (PhiQbb_meas hσ d n l) ⟨_, (hPB l).2.2.2.2.2.2.2⟩)).mul hg
  have hsum : ∀ u, ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), ∑ i : Fin 4, c' i * G l i u
      = (∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
          (4 * VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQee d σ n l)) u
            - 2 * VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQeb d σ n l)) u
            - 2 * VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbe d σ n l)) u
            + VarianceGeneral3.hp (VarianceGeneral3.K2 (PhiQbb d σ n l)) u)) * g u := fun u => by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, c', G, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  have e : ∀ u, VarianceGeneral3.hQT d σ n u * g u
      = ∑ i : Fin 7, c i * F i u
        + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), ∑ i : Fin 4, c' i * G l i u :=
    fun u => by
      rw [hsum u]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, c, F, Matrix.cons_val_zero,
        Matrix.cons_val_succ]
      unfold VarianceGeneral3.hQT
      ring
  have hB1 : BM fun u => ∑ i : Fin 7, c i * F i u :=
    BM.sum _ _ fun i _ => (BM.const (c i)).mul (hF i)
  have hB2 : BM fun u => ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), ∑ i : Fin 4, c' i * G l i u :=
    BM.sum _ _ fun l _ => BM.sum _ _ fun i _ => (BM.const (c' i)).mul (hG l i)
  rw [show (fun u => VarianceGeneral3.hQT d σ n u * g u) = _ from funext e,
    integral_add hB1.integrable (hB2.const_mul _).integrable, int_comb _ c F hF,
    integral_const_mul, integral_finset_sum _ fun l _ => (BM.sum _ _ fun i _ =>
      (BM.const (c' i)).mul (hG l i)).integrable]
  simp_rw [int_comb _ c' (G _) (hG _)]
  have vQ' : ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)), ∑ i : Fin 4,
      c' i * ∫ u, G l i u ∂flatTorusMeasure d
      = 4 * (Sg d σ n 2 g - n * (m * a)) - 4 * (Sg d σ n 3 g - n * (m * a))
        + (Sg d σ n 4 g - n * (m * a)) := by
    rw [← vQ]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, c', G, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  rw [vQ']
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, c, F, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  rw [vC, vA, vB, vEE, vEB, vBB, vS]
  ring

end Sum

open PiBound VarianceOne VarianceTwo CTG.Reals.TorusReduction
open WalkCount BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 VarianceGeneral

/-! ## (c), (d): `hsym = H_k / 2` almost everywhere, `v'_k = v_k`, `prop:variance` for every `k` -/

section Final

variable {d : ℕ} {σ : ℝ}

theorem neg_int (f : FlatTorus d → ℝ) :
    ∫ u, f (-u) ∂flatTorusMeasure d = ∫ u, f u ∂flatTorusMeasure d := VarianceGeneral.neg_inv_int d f

theorem Hk_bm (hσ : 0 < σ) (k : ℕ) : BM (Hk d σ k) := by
  obtain ⟨C, hC⟩ := bound_of_cont d (Hk_cont hσ d k)
  exact ⟨(Hk_cont hσ d k).measurable, C, hC⟩

/-- **(c) The symmetrised pair kernel of `QT` is `H_k / 2` almost everywhere, for every
    `k = n + 1`.** -/
theorem hS_ae (hσ : 0 < σ) (n : ℕ) :
    VarianceGeneral3.hS d σ n =ᵐ[flatTorusMeasure d] fun u => 1 / 2 * Hk d σ (n + 1) u := by
  have hQ : BM (VarianceGeneral3.hQT d σ n) := (VarianceGeneral3.hQT_ZM hσ n).1
  have hQn : BM fun u => VarianceGeneral3.hQT d σ n (-u) :=
    ⟨hQ.meas.comp measurable_neg, hQ.bdd.imp fun C h u => h _⟩
  have hSb : BM (VarianceGeneral3.hS d σ n) := by
    have : BM fun u => 1 / 2 * (VarianceGeneral3.hQT d σ n u + VarianceGeneral3.hQT d σ n (-u)) :=
      (hQ.add hQn).const_mul _
    exact this
  have hH : BM fun u => 1 / 2 * Hk d σ (n + 1) u := (Hk_bm hσ (n + 1)).const_mul _
  refine VarianceGeneral4.ae_of_test hSb hH fun g hg hg0 hgC => ?_
  obtain ⟨C, hC⟩ := hgC
  have hgb : BM g := ⟨hg, C, fun u => by rw [abs_of_nonneg (hg0 u)]; exact hC u⟩
  have hgn : BM fun u => g (-u) := ⟨hg.comp measurable_neg, C, fun u => by
    rw [abs_of_nonneg (hg0 _)]; exact hC _⟩
  set gs : FlatTorus d → ℝ := fun u => 1 / 2 * (g u + g (-u)) with hgs
  have hgsb : BM gs := (hgb.add hgn).const_mul _
  have hgse : ∀ u, gs (-u) = gs u := fun u => by simp only [hgs, neg_neg]; ring
  -- the left side
  have L : ∫ u, VarianceGeneral3.hS d σ n u * g u ∂flatTorusMeasure d
      = ∫ u, VarianceGeneral3.hQT d σ n u * gs u ∂flatTorusMeasure d := by
    have e1 : ∀ u, VarianceGeneral3.hS d σ n u * g u
        = 1 / 2 * (VarianceGeneral3.hQT d σ n u * g u)
          + 1 / 2 * (VarianceGeneral3.hQT d σ n (-u) * g u) := fun u => by
      unfold VarianceGeneral3.hS; ring
    have e2 : ∀ u, VarianceGeneral3.hQT d σ n u * gs u
        = 1 / 2 * (VarianceGeneral3.hQT d σ n u * g u)
          + 1 / 2 * (VarianceGeneral3.hQT d σ n u * g (-u)) := fun u => by
      simp only [hgs]; ring
    simp_rw [e1, e2]
    rw [integral_add ((hQ.mul hgb).const_mul _).integrable ((hQn.mul hgb).const_mul _).integrable,
      integral_add ((hQ.mul hgb).const_mul _).integrable ((hQ.mul hgn).const_mul _).integrable]
    simp only [integral_const_mul]
    congr 2
    rw [← neg_int (fun u => VarianceGeneral3.hQT d σ n u * g (-u))]
    simp only [neg_neg]
  -- the right side
  have R : ∫ u, 1 / 2 * Hk d σ (n + 1) u * g u ∂flatTorusMeasure d
      = ∫ u, 1 / 2 * Hk d σ (n + 1) u * gs u ∂flatTorusMeasure d := by
    have hHb := Hk_bm (d := d) hσ (n + 1)
    have e2 : ∀ u, 1 / 2 * Hk d σ (n + 1) u * gs u
        = 1 / 2 * (1 / 2 * Hk d σ (n + 1) u * g u) + 1 / 2 * (1 / 2 * Hk d σ (n + 1) u * g (-u)) :=
      fun u => by simp only [hgs]; ring
    simp_rw [e2]
    rw [integral_add ((hH.mul hgb).const_mul _).integrable ((hH.mul hgn).const_mul _).integrable]
    simp only [integral_const_mul]
    rw [← neg_int (fun u => 1 / 2 * Hk d σ (n + 1) u * g (-u))]
    simp only [neg_neg, Hk_even]
    ring
  rw [L, R, hQT_test hσ n hgsb hgse, target_test hσ n hgsb]

/-- **(c) `v'_k = v_k` for every `k = n + 1`** (no hypothesis). -/
theorem vq_eq_vk_ae (hσ : 0 < σ) (n : ℕ) :
    VarianceGeneral3.vq d σ n = vk d σ (n + 1) := by
  unfold VarianceGeneral3.vq vk
  rw [integral_congr_ae ((hS_ae (d := d) hσ n).mono fun u hu => by
    show VarianceGeneral3.hS d σ n u ^ 2 = (1 / 2 * Hk d σ (n + 1) u) ^ 2
    rw [hu])]
  have e : ∀ u, (1 / 2 * Hk d σ (n + 1) u) ^ 2 = 1 / 4 * Hk d σ (n + 1) u ^ 2 := fun u => by ring
  simp_rw [e]
  rw [integral_const_mul]; ring

/-- **(d) `prop:variance` for every `k = n + 1` with `v_k = ½ ∫ H_k²`, unconditional**:
    independent uniform points on the flat torus `FlatTorus d` (`d ≥ 1`), Gaussian kernel of
    variance `σ ≤ 1` with self-loops, `N ≥ 2`, `kernelC1 d · δ' ≤ 1` with `δ' = √(M log N / N)`,
    and every `θ > 0`:
    `|Var Tr P^k - v_k (N-1)/N³| ≤ θ v_k (N-1)/N³ + (1 + 1/θ) · Rest`, with exactly the rest of
    `VarianceGeneral3.variance_general_v'_sample` (where `v'_k` is now replaced by `v_k` through
    `vq_eq_vk_ae`).  The constants are those of the files and are not evaluated. -/
theorem variance_general {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1)
    (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * (2 * ((BiasGeneral6.gK n * (TorusReductionL1.normC d * δp) * torusM d σ 1) ^ 2
            * (TorusReductionL1.normC d * δp) ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + BiasGeneral6.CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 3))
          + 2 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * BiasGeneral5.B4 d σ n ^ 2
            / (N : ℝ) ^ 3))) := by
  rw [← vq_eq_vk_ae hσ n]
  exact VarianceGeneral3.variance_general_v'_sample hσ hσ1 d hd X h_indep hX hlaw N hN2 hMp hδp
    hrange n hθ

end Final

end VarianceGeneral5

namespace VarianceNoLoops

/-! # A108: `prop:variance` for the graph WITHOUT self-loops (`ρ = 0`), every `k ≥ 2`

Route (as for the bias in `BiasNoLoops`): comparison of the walk without self-loops `P°` with the
walk with self-loops `P`.  With `c = m₁/N`, `P̃ = Bh`, `S = Tr P̃^k`, `Sn = Tr P̃^{k-1}`:
`Tr P°^k - Tr P^k = k c (S - Sn) + [k = 2] c² N + O(c δ + δ³)` on the normalisation event
(`det_torus`, `D_expand`), and `E (S - m_k)² = O(N⁻²)` (`oracle_torus_all`).  Hence
`Var(Tr P°^k - Tr P^k) = O(N⁻⁴) + O((c δ + δ³)²) + O(N²) · P(bad)` (`noloop_diff_cv`), and the
variance of `Tr P°^k` has the same leading term `v_k (N-1)/N³` as with self-loops: the pair kernel
`H_k` of the proposition does not depend on `ρ` for `k ≥ 2` (`μ_k = m_k`), in accordance with
`rem:variance`(i).  No new pair kernel is needed: the pair statistic is the one of the loop walk
(`VarianceGeneral3.Uq`, `Var = v'_k (N-1)/N³`, `v'_k = v_k` by `VarianceGeneral5.vq_eq_vk_ae`). -/

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 BiasGeneral6
  PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance4 NoLoops BiasNoLoops VarianceOne

section Consts

/-- The deterministic error of the comparison on the normalisation event (`M = m₁`, `c = M/N`). -/
noncomputable def EbNL (d : ℕ) (σ : ℝ) (N n : ℕ) (δ : ℝ) : ℝ :=
  gK n * ((δ + torusM d σ 1 / N) * torusM d σ 1 * (2 * δ ^ 2 + 2 * (torusM d σ 1 / N) ^ 2))
    + gK n * (δ * torusM d σ 1 * δ ^ 2)
    + CdetT n (torusM d σ 1) * (torusM d σ 1 / N) * (δ + torusM d σ 1 / N)

/-- The binomial remainder of `D_expand`. -/
noncomputable def RbNL (d : ℕ) (σ : ℝ) (N n : ℕ) : ℝ :=
  (torusM d σ 1 / N) ^ 2 * (2 ^ (n + 1) * torusM d σ 1 ^ (n + 1) + torusM d σ 1)

/-- The bound of `|Tr P°^k - Tr P^k - …|` off the normalisation event. -/
noncomputable def BoffNL (d : ℕ) (σ : ℝ) (N n : ℕ) : ℝ :=
  2 * N + 2 * torusM d σ 1 ^ (n + 1) + ((n : ℝ) + 1) * torusM d σ 1 ^ (n + 2)

/-- The bound of `Var(Tr P°^k - Tr P^k)` without the bad-event term. -/
noncomputable def DbNL (d : ℕ) (σ : ℝ) (N n : ℕ) (δ : ℝ) : ℝ :=
  3 * ((n : ℝ) + 1) ^ 2 * (torusM d σ 1 / N) ^ 2
      * ((3 * ((n : ℝ) + 1) ^ 2 * torusM d σ 1 ^ (n + 1) / N) ^ 2
        + (3 * (n : ℝ) ^ 2 * torusM d σ 1 ^ n / N) ^ 2)
    + 6 * (EbNL d σ N n δ + RbNL d σ N n) ^ 2

end Consts

section Det

/-- `(a - b + r)² ≤ 3a² + 3b² + 3w²` for `|r| ≤ w`. -/
theorem sq3 {a b r w : ℝ} (h : |r| ≤ w) : (a - b + r) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * w ^ 2 := by
  have h2 : r ^ 2 ≤ w ^ 2 := by
    have := abs_nonneg r
    rw [← sq_abs]; exact pow_le_pow_left₀ this h 2
  nlinarith [_root_.sq_nonneg (a + b), _root_.sq_nonneg (a - r), _root_.sq_nonneg (b + r)]

end Det

section Diff

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

set_option maxHeartbeats 4000000 in
/-- **The variance of the difference of the traces with and without self-loops**, every
    `k = n + 1 ≥ 2`, heat kernel on the flat torus, general normalisation event.  For independent
    uniform points, `N ≥ 1`, `0 ≤ δ`, `δ + m₁/N ≤ 1/8`:
    `Var(Tr P°^k - Tr P^k) ≤ DbNL + 6 · BoffNL² · P(max_a |ρ_a - 1| > δ)`;
    `DbNL = 3 k² c² ((3k² m₁^k/N)² + (3(k-1)² m₁^{k-1}/N)²) + 6 (EbNL + RbNL)²`, `c = m₁/N`;
    `EbNL = O(c δ + δ³)`, `RbNL = O(c²)`. -/
theorem noloop_diff_cv [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hu : δ + torusM d σ 1 / N ≤ 1 / 8) (n : ℕ) (hn : 1 ≤ n) :
    BM (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
    ∧ cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
      ≤ DbNL d σ N n δ + 6 * BoffNL d σ N n ^ 2
          * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hN' : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hcN : 0 ≤ M / N := div_nonneg hM0 hNp.le
  have hc8 : M / N ≤ 1 / 8 := by rw [hMd]; linarith
  -- the five random variables
  obtain ⟨T0, hT0⟩ : ∃ T0 : Ω → ℝ, T0 = fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Ω → ℝ, T = fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace :=
    ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Ω → ℝ, S = fun ω => ((Bh d σ N (fun j => X j ω)) ^ (n + 1)).trace :=
    ⟨_, rfl⟩
  obtain ⟨Sn, hSn⟩ : ∃ Sn : Ω → ℝ, Sn = fun ω => ((Bh d σ N (fun j => X j ω)) ^ n).trace :=
    ⟨_, rfl⟩
  obtain ⟨Dx, hDx⟩ : ∃ Dx : Ω → ℝ, Dx = fun ω =>
      ((Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace
        - ((Bh d σ N (fun j => X j ω)) ^ (n + 1)).trace := ⟨_, rfl⟩
  -- entry bounds
  have hBe : ∀ ω (a b : Fin N), 0 ≤ Bh d σ N (fun j => X j ω) a b
      ∧ Bh d σ N (fun j => X j ω) a b ≤ M / N := fun ω a b => by
    rw [hMd]; exact Bh_entries hσ d N _ a b
  have hB'e : ∀ ω (a b : Fin N),
      0 ≤ (Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) a b
      ∧ (Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) a b ≤ M / N :=
    fun ω a b => by rw [hMd]; exact Bh_noloop_entries hσ d N _ a b
  have hSb : ∀ ω, 0 ≤ S ω ∧ S ω ≤ M ^ (n + 1) := fun ω => by
    rw [hS]; exact trB_le hN' _ hM0 (fun a b => (hBe ω a b).1) (fun a b => (hBe ω a b).2) n
  have hSnb : ∀ ω, 0 ≤ Sn ω ∧ Sn ω ≤ M ^ n := fun ω => by
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [hSn]; simp only; rw [hj]
    exact trB_le hN' _ hM0 (fun a b => (hBe ω a b).1) (fun a b => (hBe ω a b).2) j
  have hS'b : ∀ ω, 0 ≤ ((Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ))
        ^ (n + 1)).trace
      ∧ ((Bh d σ N (fun j => X j ω) - (M / N) • (1 : Matrix (Fin N) (Fin N) ℝ)) ^ (n + 1)).trace
        ≤ M ^ (n + 1) := fun ω =>
    trB_le hN' _ hM0 (fun a b => (hB'e ω a b).1) (fun a b => (hB'e ω a b).2) n
  have hDb : ∀ ω, |Dx ω| ≤ 2 * M ^ (n + 1) := fun ω => by
    rw [hDx]; simp only
    obtain ⟨a1, a2⟩ := hS'b ω
    obtain ⟨b1, b2⟩ := hSb ω
    rw [hS] at b1 b2; simp only at b1 b2
    rw [abs_le]; constructor <;> linarith
  have hT0b : ∀ ω, |T0 ω| ≤ N := fun ω => by
    rw [hT0]
    exact trace_unit_bound _ fun a => walk_pow_diag_unit _ _
      (fun i j => by split_ifs; exacts [le_rfl, heatTorus_nonneg hc d _])
      (fun i => rho_noloop_nonneg hσ _ i) (n + 1) a
  have hTb : ∀ ω, |T ω| ≤ N := fun ω => by
    rw [hT]
    exact trace_unit_bound _ fun a => walk_pow_diag_unit _ _ (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) (n + 1) a
  -- measurability
  have mBh : ∀ a b : Fin N, Measurable fun ω => Bh d σ N (fun j => X j ω) a b :=
    fun a b => Bh_entry_measurable hσ d X hX N a b
  have bT0 : BM T0 := ⟨by
      rw [hT0]
      exact ExceptionalSets.pow_trace_measurable (fun ω => noloopWalk d σ N (fun j => X j ω))
        (fun a b => Reals2Sets.noloop_entry_measurable hσ d X hX N a b) (n + 1), N, hT0b⟩
  have bT : BM T := ⟨by
      rw [hT]
      exact Finset.measurable_sum _ fun a _ => walk_pow_entry_measurable hσ d X hX N (n + 1) a a,
    N, hTb⟩
  have bS : BM S := ⟨by
      rw [hS]
      exact ExceptionalSets.pow_trace_measurable (fun ω => Bh d σ N (fun j => X j ω)) mBh (n + 1),
    M ^ (n + 1), fun ω => by rw [abs_of_nonneg (hSb ω).1]; exact (hSb ω).2⟩
  have bSn : BM Sn := ⟨by
      rw [hSn]
      exact ExceptionalSets.pow_trace_measurable (fun ω => Bh d σ N (fun j => X j ω)) mBh n,
    M ^ n, fun ω => by rw [abs_of_nonneg (hSnb ω).1]; exact (hSnb ω).2⟩
  have bD : BM (fun ω => T0 ω - T ω) := bT0.sub bT
  have eD : (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace) = fun ω => T0 ω - T ω := by
    rw [hT0, hT]
  rw [eD]
  refine ⟨bD, ?_⟩
  -- the binomial remainder
  obtain ⟨ite1, hite1⟩ : ∃ t : ℝ, t = if n = 1 then (M / N) ^ 2 * N else 0 := ⟨_, rfl⟩
  have hRp : ∀ ω, |Dx ω + ((n : ℝ) + 1) * (M / N) * Sn ω - ite1|
      ≤ (M / N) ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M) := fun ω => by
    have h := D_expand hN' (Bh d σ N (fun j => X j ω)) (fun a b => (hBe ω a b).1)
      (fun a b => (hBe ω a b).2) hM1 hcN (by linarith) (le_of_eq (by field_simp)) n hn
    rw [hDx, hSn, hite1]; simp only
    convert h using 2
  -- the event
  have hGm : MeasurableSet {ω | ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => measurableSet_le
      (continuous_abs.measurable.comp
        ((heatRho_sample_measurable hσ d X hX N a).sub measurable_const)) measurable_const
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Set Ω,
      Gc = {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  have hGcm : MeasurableSet Gc := by rw [hGc]; exact hGm.compl
  rw [← hGc]
  have hgK := gK_nonneg n
  have hCd := CdetT_nonneg n hM0
  obtain ⟨Eb, hEb⟩ : ∃ Eb : ℝ, Eb = EbNL d σ N n δ := ⟨_, rfl⟩
  obtain ⟨Rb, hRb⟩ : ∃ Rb : ℝ, Rb = RbNL d σ N n := ⟨_, rfl⟩
  obtain ⟨Bo, hBo⟩ : ∃ Bo : ℝ, Bo = BoffNL d σ N n := ⟨_, rfl⟩
  have eEb : Eb = gK n * ((δ + M / N) * M * (2 * δ ^ 2 + 2 * (M / N) ^ 2))
      + gK n * (δ * M * δ ^ 2) + CdetT n M * (M / N) * (δ + M / N) := by
    rw [hEb, hMd]; rfl
  have eRb : Rb = (M / N) ^ 2 * (2 ^ (n + 1) * M ^ (n + 1) + M) := by rw [hRb, hMd]; rfl
  have eBo : Bo = 2 * N + 2 * M ^ (n + 1) + ((n : ℝ) + 1) * M ^ (n + 2) := by rw [hBo, hMd]; rfl
  have hEb0 : 0 ≤ Eb := by rw [eEb]; positivity
  have hRb0 : 0 ≤ Rb := by rw [eRb]; positivity
  have hBo0 : 0 ≤ Bo := by rw [eBo]; positivity
  -- the comparison, pointwise
  have hpt : ∀ ω, |T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω|
      ≤ Eb + Bo * Gc.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ
    · have hnot : ω ∉ Gc := by rw [hGc]; exact fun h => h hω
      rw [Set.indicator_of_notMem hnot, mul_zero, add_zero]
      have h := det_torus hσ hN' (fun j => X j ω) hδ0 hu hω n hn
      rw [← hMd] at h
      have hSε : 1 / (N : ℝ) * ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2 ≤ δ ^ 2 := by
        have hi : ∀ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2 ≤ δ ^ 2 := fun i => by
          have e : eV d σ N (fun j => X j ω) i = heatRho d σ N (fun j => X j ω) i - 1 :=
            (eps_row d σ hN' (fun j => X j ω) i).symm
          rw [e, ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hω i) 2
        have hs : ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2 ≤ N * δ ^ 2 := by
          calc ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2 ≤ ∑ _i : Fin N, δ ^ 2 :=
                Finset.sum_le_sum fun i _ => hi i
            _ = N * δ ^ 2 := by simp
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hNp]; linarith
      have hSε0 : 0 ≤ 1 / (N : ℝ) * ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2 :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => _root_.sq_nonneg _)
      rw [hT0, hT, hDx, hS]; simp only
      refine h.trans ?_
      rw [eEb]
      have k1 : gK n * ((δ + M / N) * M * (2 * (1 / (N : ℝ) * ∑ i : Fin N,
            eV d σ N (fun j => X j ω) i ^ 2) + 2 * (M / N) ^ 2))
          ≤ gK n * ((δ + M / N) * M * (2 * δ ^ 2 + 2 * (M / N) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hgK
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      have k2 : gK n * (δ * M * (1 / (N : ℝ) * ∑ i : Fin N, eV d σ N (fun j => X j ω) i ^ 2))
          ≤ gK n * (δ * M * δ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hgK
        exact mul_le_mul_of_nonneg_left hSε (by positivity)
      linarith
    · have hin : ω ∈ Gc := by rw [hGc]; exact hω
      rw [Set.indicator_of_mem hin, mul_one]
      have hcS : ((n : ℝ) + 1) * (M / N) * |S ω| ≤ ((n : ℝ) + 1) * M ^ (n + 2) := by
        rw [abs_of_nonneg (hSb ω).1]
        have hc1 : M / N ≤ M := div_le_self hM0 hN1
        have : (M / N) * S ω ≤ M * M ^ (n + 1) :=
          mul_le_mul hc1 (hSb ω).2 (hSb ω).1 hM0
        rw [pow_succ, mul_comm (M ^ (n + 1)) M, mul_assoc]
        exact mul_le_mul_of_nonneg_left this (by positivity)
      have e1 := hT0b ω
      have e2 := hTb ω
      have e3 := hDb ω
      have e4 : |((n : ℝ) + 1) * (M / N) * S ω| = ((n : ℝ) + 1) * (M / N) * |S ω| := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * (M / N))]
      have : |T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω|
          ≤ |T0 ω| + |T ω| + |Dx ω| + |((n : ℝ) + 1) * (M / N) * S ω| := by
        have := abs_sub (T0 ω - T ω - Dx ω) (((n : ℝ) + 1) * (M / N) * S ω)
        have := abs_sub (T0 ω - T ω) (Dx ω)
        have := abs_sub (T0 ω) (T ω)
        linarith
      rw [eBo]
      linarith
  -- the centred quantity `Y`
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ite1 + ((n : ℝ) + 1) * (M / N)
      * (torusM d σ (n + 1) - torusM d σ n) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Ω → ℝ, G = fun ω =>
      3 * (((n : ℝ) + 1) * (M / N)) ^ 2 * (S ω - torusM d σ (n + 1)) ^ 2
        + 3 * (((n : ℝ) + 1) * (M / N)) ^ 2 * (Sn ω - torusM d σ n) ^ 2
        + 6 * (Eb + Rb) ^ 2 + 6 * Bo ^ 2 * Gc.indicator (fun _ => (1 : ℝ)) ω := ⟨_, rfl⟩
  have hYG : ∀ ω, (T0 ω - T ω + -κ) ^ 2 ≤ G ω := by
    intro ω
    have hr : |(T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω)
        + (Dx ω + ((n : ℝ) + 1) * (M / N) * Sn ω - ite1)|
        ≤ (Eb + Rb) + Bo * Gc.indicator (fun _ => (1 : ℝ)) ω := by
      have := abs_add_le (T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω)
        (Dx ω + ((n : ℝ) + 1) * (M / N) * Sn ω - ite1)
      have h2 := hRp ω
      rw [← eRb] at h2
      linarith [hpt ω]
    have e : T0 ω - T ω + -κ
        = ((n : ℝ) + 1) * (M / N) * (S ω - torusM d σ (n + 1))
          - ((n : ℝ) + 1) * (M / N) * (Sn ω - torusM d σ n)
          + ((T0 ω - T ω - Dx ω - ((n : ℝ) + 1) * (M / N) * S ω)
            + (Dx ω + ((n : ℝ) + 1) * (M / N) * Sn ω - ite1)) := by rw [hκ]; ring
    rw [e]
    refine (sq3 hr).trans ?_
    have hind : (Gc.indicator (fun _ => (1 : ℝ)) ω) ^ 2 = Gc.indicator (fun _ => (1 : ℝ)) ω := by
      by_cases h : ω ∈ Gc
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    have hI0 : 0 ≤ Gc.indicator (fun _ => (1 : ℝ)) ω := Set.indicator_nonneg (fun _ _ => zero_le_one) ω
    have hw : ((Eb + Rb) + Bo * Gc.indicator (fun _ => (1 : ℝ)) ω) ^ 2
        ≤ 2 * (Eb + Rb) ^ 2 + 2 * Bo ^ 2 * Gc.indicator (fun _ => (1 : ℝ)) ω := by
      have := _root_.sq_nonneg ((Eb + Rb) - Bo * Gc.indicator (fun _ => (1 : ℝ)) ω)
      have e2 : (Bo * Gc.indicator (fun _ => (1 : ℝ)) ω) ^ 2
          = Bo ^ 2 * Gc.indicator (fun _ => (1 : ℝ)) ω := by rw [mul_pow, hind]
      nlinarith
    rw [hG]; simp only
    nlinarith [hw]
  -- integrate
  have bY : BM (fun ω => T0 ω - T ω + -κ) := bD.add (BM.const _)
  have hcvY : cv μ (fun ω => T0 ω - T ω) = cv μ (fun ω => T0 ω - T ω + -κ) :=
    (cv_add_const bD (-κ)).symm
  rw [hcvY]
  refine (cv_le_sq bY).trans ?_
  have iInd : Integrable (fun ω => Gc.indicator (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const (1 : ℝ)).indicator hGcm
  have bS1 : BM (fun ω => (S ω - torusM d σ (n + 1)) ^ 2) := (bS.sub (BM.const _)).sqr
  have bS2 : BM (fun ω => (Sn ω - torusM d σ n) ^ 2) := (bSn.sub (BM.const _)).sqr
  have k1 : Integrable (fun ω => 3 * (((n : ℝ) + 1) * (M / N)) ^ 2
      * (S ω - torusM d σ (n + 1)) ^ 2) μ := bS1.integrable.const_mul _
  have k2 : Integrable (fun ω => 3 * (((n : ℝ) + 1) * (M / N)) ^ 2
      * (Sn ω - torusM d σ n) ^ 2) μ := bS2.integrable.const_mul _
  have k3 : Integrable (fun ω => 6 * Bo ^ 2 * Gc.indicator (fun _ => (1 : ℝ)) ω) μ :=
    iInd.const_mul _
  have iG : Integrable G μ := by
    rw [hG]; exact ((k1.add k2).add (integrable_const _)).add k3
  have hmono := integral_mono bY.sqr.integrable iG hYG
  have eG : ∫ ω, G ω ∂μ
      = 3 * (((n : ℝ) + 1) * (M / N)) ^ 2 * ∫ ω, (S ω - torusM d σ (n + 1)) ^ 2 ∂μ
        + 3 * (((n : ℝ) + 1) * (M / N)) ^ 2 * ∫ ω, (Sn ω - torusM d σ n) ^ 2 ∂μ
        + 6 * (Eb + Rb) ^ 2 + 6 * Bo ^ 2 * μ.real Gc := by
    have i12 : Integrable (fun ω => 3 * (((n : ℝ) + 1) * (M / N)) ^ 2
        * (S ω - torusM d σ (n + 1)) ^ 2 + 3 * (((n : ℝ) + 1) * (M / N)) ^ 2
        * (Sn ω - torusM d σ n) ^ 2) μ := k1.add k2
    have i123 : Integrable (fun ω => 3 * (((n : ℝ) + 1) * (M / N)) ^ 2
        * (S ω - torusM d σ (n + 1)) ^ 2 + 3 * (((n : ℝ) + 1) * (M / N)) ^ 2
        * (Sn ω - torusM d σ n) ^ 2 + 6 * (Eb + Rb) ^ 2) μ := i12.add (integrable_const _)
    rw [hG]; simp only []
    rw [integral_add i123 k3, integral_add i12 (integrable_const _), integral_add k1 k2,
      integral_const_mul, integral_const_mul, integral_const, probReal_univ,
      one_smul]
    simp only [integral_const_mul, integral_indicator_const (1 : ℝ) hGcm, smul_eq_mul, mul_one]
  rw [eG] at hmono
  refine hmono.trans ?_
  -- the oracle bounds
  have eB : ∀ ω, Bh d σ N (fun j => X j ω)
      = Matrix.of fun a b : Fin N => pker d σ (X a ω - X b ω) / N := by
    intro ω; ext a b; simp [Bh, VarianceGeneral5.hp1]
  have o1 := SmallGaps.oracle_torus_all X h_indep hX hlaw hσ N (n + 1) hN (by omega) (μ := μ)
  have o2 := SmallGaps.oracle_torus_all X h_indep hX hlaw hσ N n hN hn (μ := μ)
  have eS : ∀ ω, S ω = Matrix.trace ((Matrix.of fun a b : Fin N =>
      pker d σ (X a ω - X b ω) / N) ^ (n + 1)) := fun ω => by rw [hS]; simp only; rw [eB]
  have eSn : ∀ ω, Sn ω = Matrix.trace ((Matrix.of fun a b : Fin N =>
      pker d σ (X a ω - X b ω) / N) ^ n) := fun ω => by rw [hSn]; simp only; rw [eB]
  simp_rw [eS, eSn]
  rw [← hMd] at o1 o2
  have hk2 : 0 ≤ 3 * (((n : ℝ) + 1) * (M / N)) ^ 2 := by positivity
  have m1 := mul_le_mul_of_nonneg_left o1 hk2
  have m2 := mul_le_mul_of_nonneg_left o2 hk2
  have eDb : DbNL d σ N n δ = 3 * (((n : ℝ) + 1) * (M / N)) ^ 2
        * (3 * ((n + 1 : ℕ) : ℝ) ^ 2 * M ^ (n + 1) / N) ^ 2
      + 3 * (((n : ℝ) + 1) * (M / N)) ^ 2 * (3 * (n : ℝ) ^ 2 * M ^ n / N) ^ 2
      + 6 * (Eb + Rb) ^ 2 := by
    rw [hEb, hRb]; unfold DbNL; rw [← hMd]; push_cast; ring
  rw [eDb, ← hBo]
  linarith

/-- **`prop:variance` for the graph WITHOUT self-loops, every `k = n + 1 ≥ 2`, with the
    coefficient `v'_k = vq d σ n`, general normalisation event.**  For independent uniform points
    on the flat torus, `N ≥ 1`, `0 ≤ δ`, `δ + m₁/N ≤ 1/8`, `θ > 0`:
    `|Var Tr P°^k - v'_k (N-1)/N³| ≤ θ v'_k (N-1)/N³ + (1 + 1/θ)(4 E₁ + 4 R + 2 D)` with
    `E₁` of `trace_QT_sq`, `R` of `QT_pair` (both for the walk WITH self-loops) and
    `D = DbNL + 6 BoffNL² P(max_a |ρ_a - 1| > δ)` of `noloop_diff_cv`.  `ρ_a` is the
    normalisation WITH self-loops (`ρ°_a = ρ_a - m₁/N`). -/
theorem variance_noloops_v' [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hu : δ + torusM d σ 1 / N ≤ 1 / 8) (n : ℕ) (hn : 1 ≤ n)
    {θ : ℝ} (hθ : 0 < θ) :
    |cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - VarianceGeneral3.vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (VarianceGeneral3.vq d σ n * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * (4 * ((gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2
            * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ})
          + 4 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))
          + 2 * (DbNL d σ N n δ + 6 * BoffNL d σ N n ^ 2
            * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ})) := by
  have hN' : 0 < N := hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : δ ≤ 1 / 8 := by
    have : 0 ≤ torusM d σ 1 / N := div_nonneg (zero_le_one.trans (torusM_one_ge hσ d)) hNp.le
    linarith
  obtain ⟨bU, hcvU⟩ := VarianceGeneral3.Uq_var X h_indep hX hlaw hσ n N
  obtain ⟨bT, _⟩ := VarianceGeneral.trace_pow_bm hσ X hX N (n + 1)
  have bQ := VarianceGeneral.QT_bm (μ := μ) hσ d X hX (N := N) (n := n)
  have hsq := VarianceGeneral.trace_QT_sq X h_indep hX hlaw hσ N hN hδ0 hδ n
  obtain ⟨_, hR⟩ := VarianceGeneral3.QT_pair X h_indep hX hlaw hσ hN' n
  obtain ⟨bD, hD⟩ := noloop_diff_cv X h_indep hX hlaw hσ N hN hδ0 hu n hn
  have eU : ∀ ω, VarianceGeneral3.Uq d σ n X N ω
      = 1 / (N : ℝ) ^ 2 * Soff (VarianceGeneral3.hQT d σ n) X N ω := fun ω => by
    unfold VarianceGeneral3.Uq; rw [VarianceGeneral3.Soff_hS]
  have hR' : cv μ (fun ω => QT d σ N n (fun j => X j ω) - VarianceGeneral3.Uq d σ n X N ω)
      ≤ VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3) := by
    simp_rw [eU]; exact hR
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ, E1 = (gK n * δ * torusM d σ 1) ^ 2 * δ ^ 2
      * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2
        * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R : ℝ, R = VarianceGeneral3.Cq n
      * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3) := ⟨_, rfl⟩
  obtain ⟨Dd, hDd⟩ : ∃ Dd : ℝ, Dd = DbNL d σ N n δ + 6 * BoffNL d σ N n ^ 2
      * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ δ} := ⟨_, rfl⟩
  rw [← hE1] at hsq ⊢
  rw [← hRd] at hR' ⊢
  rw [← hDd] at hD ⊢
  have bTQ : BM (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - QT d σ N n (fun j => X j ω)) := bT.sub bQ
  have bQU : BM (fun ω => QT d σ N n (fun j => X j ω) - VarianceGeneral3.Uq d σ n X N ω) :=
    bQ.sub bU
  have hTQ := cv_le_sq (μ := μ) bTQ
  have hg1 : cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - VarianceGeneral3.Uq d σ n X N ω) ≤ 2 * E1 + 2 * R := by
    have e : (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - VarianceGeneral3.Uq d σ n X N ω)
        = fun ω => (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - QT d σ N n (fun j => X j ω))
          + (QT d σ N n (fun j => X j ω) - VarianceGeneral3.Uq d σ n X N ω) := by funext ω; ring
    rw [e]
    have := cv_add_le (μ := μ) bTQ bQU
    linarith only [this, hTQ, hsq, hR']
  have bTU : BM (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - VarianceGeneral3.Uq d σ n X N ω) := bT.sub bU
  have hg : cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - VarianceGeneral3.Uq d σ n X N ω) ≤ 4 * E1 + 4 * R + 2 * Dd := by
    have e : (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - VarianceGeneral3.Uq d σ n X N ω)
        = fun ω => (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - VarianceGeneral3.Uq d σ n X N ω)
          + (((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
            - ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace) := by funext ω; ring
    rw [e]
    have := cv_add_le (μ := μ) bTU bD
    linarith only [this, hg1, hD]
  have bT0U : BM (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - VarianceGeneral3.Uq d σ n X N ω) := by
    have e : (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - VarianceGeneral3.Uq d σ n X N ω)
        = fun ω => (((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
          - VarianceGeneral3.Uq d σ n X N ω)
          + (((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
            - ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace) := by funext ω; ring
    rw [e]; exact bTU.add bD
  have hper := cv_perturb (μ := μ) bU bT0U hθ
  have e : (fun ω => VarianceGeneral3.Uq d σ n X N ω
      + (((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - VarianceGeneral3.Uq d σ n X N ω))
      = fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace := by
    funext ω; ring
  rw [e, hcvU] at hper
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left hg hθ'
  linarith only [hper, this]

end Diff

section Sample

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`prop:variance` for the graph WITHOUT self-loops, every `k = n + 1 ≥ 2`, with `v_k`, sample
    form.**  Under the hypotheses of `norm_sample` (`σ ≤ 1`, `d ≥ 1`, `N ≥ 2`, `kernelC1 d · δ' ≤ 1`,
    `δ' = √(m₁ log N / N)`) and, ADDITIONALLY, `normC d · δ' + m₁/N ≤ 1/8`: for every `θ > 0`,
    `|Var Tr P°^k - v_k (N-1)/N³| ≤ θ v_k (N-1)/N³ + (1 + 1/θ) · Rest°`, with
    `Rest° = 4 E₁ + 4 R + 2 (DbNL(normC δ') + 6 BoffNL²/N³)`,
    `E₁ = (gK δ m₁)² δ² (2m₁²/N) + (N + CQT)²/N³` at `δ = normC δ'`, `R = Cq · cA · B4²/N³`.
    `v_k = ½ ∫ H_k²` is the coefficient of the walk WITH self-loops (`H_k` does not depend on
    `ρ` for `k ≥ 2`).  The terms `(N + CQT)²/N³` and `6 BoffNL²/N³` are of the order `1/N` (they
    come from the bound `1/N³` of `norm_sample` for the bad event and the bound `O(N)` of the traces
    there), so this form is not informative against `v_k/N²` for large `N`; the general form
    `variance_noloops_v'` keeps the probability of the bad event explicit. -/
theorem variance_noloops [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ)
    (hN2 : 2 ≤ N) {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) (hrange : kernelC1 d * δp ≤ 1)
    (hu : TorusReductionL1.normC d * δp + torusM d σ 1 / N ≤ 1 / 8)
    (n : ℕ) (hn : 1 ≤ n) {θ : ℝ} (hθ : 0 < θ) :
    |cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ θ * (VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + 1 / θ) * (4 * ((gK n * (TorusReductionL1.normC d * δp) * torusM d σ 1) ^ 2
            * (TorusReductionL1.normC d * δp) ^ 2 * (2 * torusM d σ 1 ^ 2 / N)
          + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 3))
          + 4 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))
          + 2 * (DbNL d σ N n (TorusReductionL1.normC d * δp)
            + 6 * BoffNL d σ N n ^ 2 * (1 / (N : ℝ) ^ 3))) := by
  rw [← VarianceGeneral5.vq_eq_vk_ae hσ n]
  have hr : kernelC1 d * δp * Real.sqrt ((1 : ℕ) : ℝ) ≤ 1 := by
    rw [Nat.cast_one, Real.sqrt_one, mul_one]; exact hrange
  obtain ⟨_, hp⟩ := TorusReductionL1.norm_sample hσ hσ1 d hd X h_indep hX hlaw N 1 hN2
    Nat.one_pos hMp hδp hr
  have hδ0 : 0 ≤ TorusReductionL1.normC d * δp := by
    rw [hδp]; exact mul_nonneg (TorusReductionL1.normC_nonneg d) (Real.sqrt_nonneg _)
  have h := variance_noloops_v' X h_indep hX hlaw hσ N (by omega) hδ0 hu n hn hθ
  refine h.trans ?_
  have hc : (0 : ℝ) ≤ (N + CQT d σ n) ^ 2 := _root_.sq_nonneg _
  have hc2 : (0 : ℝ) ≤ 6 * BoffNL d σ N n ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hp hc
  have h2 := mul_le_mul_of_nonneg_left hp hc2
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  gcongr

end Sample

end VarianceNoLoops

namespace VarianceSharp

/-! # A110: `prop:variance` with a remainder that is smaller than the main term

Route (A) of the task: a normalisation event of probability `≤ N⁻⁵` instead of `N⁻³`.
`rho_event_le` is the general Bernstein bound for `max_a |ρ_a - 1|` (net with `g^d` points,
`heat_normalisation_whp`); with `g = N` and `ε = 3 √(N m₁ T)`, `T = log(2 N^{d+5})`, the
threshold is `deltaN = (ε + 2 Lip)/N = O(√(log N / N))` and the probability is `≤ N⁻⁵`
(`deltaN_event`).  Inserted into `VarianceGeneral3.variance_general_v'` (with self-loops) and
`VarianceNoLoops.variance_noloops_v'` (without), with `θ = N^{-1/2}`, this gives remainders
`O((log N)² N^{-5/2})` resp. `O((log N)³ N^{-5/2})` against the main term `v_k (N-1)/N³`. -/

open WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 BiasGeneral6
  PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance4 NoLoops BiasNoLoops VarianceOne

section Defs

/-- The Lipschitz constant of `heatTorus_lipschitz` for the kernel of variance `σ`. -/
noncomputable def lipT (d : ℕ) (σ : ℝ) : ℝ :=
  2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ)) * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d

/-- `T = log (2 N^{d+5})`. -/
noncomputable def TN (d N : ℕ) : ℝ := Real.log (2 * (N : ℝ) ^ (d + 5))

/-- `ε = 3 √(N m₁ T)`. -/
noncomputable def epsN (d : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  3 * Real.sqrt (N * torusM d σ 1 * TN d N)

/-- The threshold `δ_N = (ε + 2 N Lip / N)/N` of the normalisation event. -/
noncomputable def deltaN (d : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  (epsN d σ N + 2 * (N * lipT d σ) * (1 / ((N : ℕ) : ℝ))) / N

theorem lipT_nonneg {σ : ℝ} (hσ : 0 < σ) (d : ℕ) : 0 ≤ lipT d σ := by
  have := Real.pi_pos; unfold lipT; positivity

theorem TN_nonneg {N : ℕ} (hN : 1 ≤ N) (d : ℕ) : 0 ≤ TN d N := by
  unfold TN
  apply Real.log_nonneg
  have : (1 : ℝ) ≤ (N : ℝ) ^ (d + 5) := one_le_pow₀ (by exact_mod_cast hN)
  linarith

theorem deltaN_nonneg {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) : 0 ≤ deltaN d σ N := by
  have := lipT_nonneg hσ d
  unfold deltaN epsN; positivity

end Defs

section Event

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The normalisation event, general parameters.** Independent uniform points, `N ≥ 1`, net
    parameter `g > 0`, `ε > 0`:
    `P(max_a |ρ_a - 1| > (ε + 2 N Lip/g)/N) ≤ g^d · 2 exp(-ε²/(4 N m₁ + 2 m₁ ε))`. -/
theorem rho_event_le [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ) (hN : 1 ≤ N) {g : ℕ} (hg : 0 < g)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1|
        ≤ (ε + 2 * (N * lipT d σ) * (1 / (g : ℝ))) / N}
      ≤ (g : ℝ) ^ d * (2 * Real.exp (-ε ^ 2
          / (4 * (N * torusM d σ 1) + 2 * torusM d σ 1 * ε))) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ torusM d σ 1 := fun u => by
    rw [torusM_one]; exact heatTorus_le_zero hc d _
  have h := heat_normalisation_whp hσ d X h_indep hX hlaw N hg hM
    (fun u u' => heatTorus_lipschitz hc d u u') (lipT_nonneg hσ d) hε
  refine (measureReal_mono ?_ (measure_ne_top _ _)).trans h
  intro ω hω
  simp only [Set.mem_setOf_eq, not_forall, not_le] at hω
  obtain ⟨a, ha⟩ := hω
  refine ⟨X a ω, ?_⟩
  have e : ∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω) - N
      = N * (heatRho d σ N (fun j => X j ω) a - 1) := by
    unfold heatRho; field_simp
  show ε + 2 * (N * lipT d σ) * (1 / g)
    < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω) - N|
  rw [e, abs_mul, abs_of_nonneg hNpos.le]
  have := mul_lt_mul_of_pos_left ha hNpos
  rw [mul_div_cancel₀ _ hNpos.ne'] at this
  exact this

/-- **The normalisation event with probability `≤ N⁻⁵`.** If `δ_N ≤ 1/8` (`N ≥ 2`):
    `P(max_a |ρ_a - 1| > δ_N) ≤ 1/N⁵`. -/
theorem deltaN_event [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ) (hN2 : 2 ≤ N)
    (hδ : deltaN d σ N ≤ 1 / 8) :
    μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ deltaN d σ N}
      ≤ 1 / (N : ℝ) ^ 5 := by
  have hN : 1 ≤ N := by omega
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  have hT0 := TN_nonneg hN d
  have hL0 := lipT_nonneg hσ d
  have hTpos : 0 < TN d N := by
    unfold TN
    apply Real.log_pos
    have : (1 : ℝ) ≤ (N : ℝ) ^ (d + 5) := one_le_pow₀ (by linarith)
    linarith
  have hεpos : 0 < epsN d σ N := by
    unfold epsN
    have : 0 < (N : ℝ) * torusM d σ 1 * TN d N := by positivity
    have := Real.sqrt_pos.mpr this
    linarith
  have hgN : 0 < N := by omega
  have h := rho_event_le hσ d X h_indep hX hlaw N hN hgN hεpos
  have eδ : (epsN d σ N + 2 * (N * lipT d σ) * (1 / ((N : ℕ) : ℝ))) / N = deltaN d σ N := rfl
  rw [eδ] at h
  refine h.trans ?_
  -- `ε ≤ N`
  have hεN : epsN d σ N ≤ N := by
    have h1 : epsN d σ N / N ≤ deltaN d σ N := by
      unfold deltaN
      apply div_le_div_of_nonneg_right _ hNpos.le
      have : 0 ≤ 2 * (N * lipT d σ) * (1 / ((N : ℕ) : ℝ)) := by positivity
      linarith
    have h2 : epsN d σ N / N ≤ 1 := by linarith
    rwa [div_le_one hNpos] at h2
  have hε2 : epsN d σ N ^ 2 = 9 * (N * torusM d σ 1 * TN d N) := by
    unfold epsN
    rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 4 * (N * torusM d σ 1) + 2 * torusM d σ 1 * epsN d σ N :=
    ⟨_, rfl⟩
  rw [← hD]
  have hDpos : 0 < D := by rw [hD]; positivity
  have hDle : D ≤ 6 * (N * torusM d σ 1) := by
    rw [hD]; nlinarith
  have hratio : TN d N ≤ epsN d σ N ^ 2 / D := by
    rw [le_div_iff₀ hDpos, hε2]
    have := mul_le_mul_of_nonneg_left hDle hT0
    nlinarith [mul_nonneg (mul_nonneg hNpos.le (by linarith : (0:ℝ) ≤ torusM d σ 1)) hT0]
  have hexp : Real.exp (-epsN d σ N ^ 2 / D) ≤ Real.exp (-TN d N) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]; linarith
  have hexpT : Real.exp (-TN d N) = 1 / (2 * (N : ℝ) ^ (d + 5)) := by
    unfold TN
    rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hg0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) ^ d := by positivity
  calc ((N : ℕ) : ℝ) ^ d * (2 * Real.exp (-epsN d σ N ^ 2 / D))
      ≤ ((N : ℕ) : ℝ) ^ d * (2 * Real.exp (-TN d N)) := by gcongr
    _ = 1 / (N : ℝ) ^ 5 := by
      rw [hexpT, pow_add]; field_simp

end Event

section Sharp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`prop:variance` for every `k = n + 1`, with self-loops, sharp form.** Independent uniform
    points on `FlatTorus d`, Gaussian kernel of variance `σ > 0`, `N ≥ 2` and `δ_N ≤ 1/8`
    (`δ_N = deltaN d σ N = O(√(log N / N))`):
    `|Var Tr P^k - v_k (N-1)/N³| ≤ N^{-1/2} v_k (N-1)/N³
       + (1 + √N)(2 ((gK δ_N m₁)² δ_N² (2m₁²/N) + (N + CQT)²/N⁵) + 2 Cq cA B4²/N³)`. -/
theorem variance_general_sharp [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN2 : 2 ≤ N)
    (hδ : deltaN d σ N ≤ 1 / 8) (n : ℕ) :
    |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ 1 / Real.sqrt N * (VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + Real.sqrt N) * (2 * ((gK n * deltaN d σ N * torusM d σ 1) ^ 2 * deltaN d σ N ^ 2
            * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 5))
          + 2 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2
            / (N : ℝ) ^ 3))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hθ : 0 < 1 / Real.sqrt N := by positivity
  rw [← VarianceGeneral5.vq_eq_vk_ae hσ n]
  obtain ⟨_, h⟩ := VarianceGeneral3.variance_general_v' X h_indep hX hlaw hσ N (by omega)
    (deltaN_nonneg hσ d N) hδ n hθ
  rw [one_div_one_div] at h
  have hP := deltaN_event hσ d X h_indep hX hlaw N hN2 hδ
  refine h.trans ?_
  gcongr

end Sharp

section Rate

/-- `K₀ = 18 m₁ (d+6) + 8 Lip²`: `δ_N² ≤ K₀ (log N + 1)/N`. -/
noncomputable def K0 (d : ℕ) (σ : ℝ) : ℝ := 18 * torusM d σ 1 * ((d : ℝ) + 6) + 8 * lipT d σ ^ 2

theorem K0_nonneg {σ : ℝ} (hσ : 0 < σ) (d : ℕ) : 0 ≤ K0 d σ := by
  have := torusM_one_ge hσ d; unfold K0; positivity

theorem TN_le {N : ℕ} (hN2 : 2 ≤ N) (d : ℕ) : TN d N ≤ ((d : ℝ) + 6) * (Real.log N + 1) := by
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hl2 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2r
  unfold TN
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  push_cast
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

theorem deltaN_sq {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {N : ℕ} (hN2 : 2 ≤ N) :
    deltaN d σ N ^ 2 ≤ K0 d σ * (Real.log N + 1) / N := by
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hM1 : 1 ≤ torusM d σ 1 := torusM_one_ge hσ d
  have hL0 := lipT_nonneg hσ d
  have hT0 := TN_nonneg (by omega : 1 ≤ N) d
  have hT := TN_le hN2 d
  have e : deltaN d σ N = (epsN d σ N + 2 * lipT d σ) / N := by
    unfold deltaN
    congr 1
    field_simp
  have hε2 : epsN d σ N ^ 2 = 9 * (N * torusM d σ 1 * TN d N) := by
    unfold epsN
    rw [mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  rw [e, div_pow, div_le_div_iff₀ (by positivity) hNpos]
  have h1 : (epsN d σ N + 2 * lipT d σ) ^ 2 ≤ 2 * epsN d σ N ^ 2 + 8 * lipT d σ ^ 2 := by
    nlinarith [_root_.sq_nonneg (epsN d σ N - 2 * lipT d σ)]
  rw [hε2] at h1
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 : 18 * (N * torusM d σ 1 * TN d N) * N
      ≤ 18 * torusM d σ 1 * ((d : ℝ) + 6) * (Real.log N + 1) * (N : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 18 * torusM d σ 1 * N * N)
    nlinarith [this]
  have h3 : 8 * lipT d σ ^ 2 * N ≤ 8 * lipT d σ ^ 2 * (Real.log N + 1) * (N : ℝ) ^ 2 := by
    have hA : (N : ℝ) ≤ (Real.log N + 1) * (N : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 8 * lipT d σ ^ 2)
    nlinarith [this]
  have h4 := mul_le_mul_of_nonneg_right h1 hNpos.le
  unfold K0
  nlinarith [h2, h3, h4]

/-- **The algebra of the closing step**: with `s = √N ≥ 1`, `W ≥ 1`, `X ≤ c W / N³`:
    `N^{-1/2} V (N-1)/N³ + (1 + s) X ≤ (V + 2c) W / (N² s)`. -/
theorem rate_alg {N s W V X c : ℝ} (hs1 : 1 ≤ s) (hsN : s ^ 2 = N) (hW : 1 ≤ W) (hV : 0 ≤ V)
    (hc : 0 ≤ c) (hX : X ≤ c * W / N ^ 3) :
    1 / s * (V * (N - 1) / N ^ 3) + (1 + s) * X ≤ (V + 2 * c) * W / (N ^ 2 * s) := by
  subst hsN
  have hs0 : 0 < s := by linarith
  have e1 : 1 / s * (V * (s ^ 2 - 1) / (s ^ 2) ^ 3) = V * (s ^ 2 - 1) / s ^ 7 := by
    field_simp <;> ring
  have e2 : (V + 2 * c) * W / ((s ^ 2) ^ 2 * s) = V * W / s ^ 5 + 2 * c * W / s ^ 5 := by
    field_simp <;> ring
  have h1 : V * (s ^ 2 - 1) / s ^ 7 ≤ V * W / s ^ 5 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key : 0 ≤ V * s ^ 5 * (W * s ^ 2 - s ^ 2 + 1) :=
      mul_nonneg (by positivity) (by nlinarith)
    nlinarith [key]
  have h6 : ((s ^ 2) ^ 3) = s ^ 6 := by ring
  rw [h6] at hX
  have h2 : (1 + s) * X ≤ 2 * c * W / s ^ 5 := by
    calc (1 + s) * X ≤ (1 + s) * (c * W / s ^ 6) := mul_le_mul_of_nonneg_left hX (by linarith)
      _ ≤ (2 * s) * (c * W / s ^ 6) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 2 * c * W / s ^ 5 := by field_simp <;> ring
  rw [e1, e2]; linarith

/-- The constant of the closing corollary (with self-loops), without `v_k`. -/
noncomputable def rateC1 (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  2 * gK n ^ 2 * torusM d σ 1 ^ 4 * K0 d σ ^ 2 + (1 + CQT d σ n) ^ 2
    + VarianceGeneral3.Cq n * VarianceGeneral3.cA n * B4 d σ n ^ 2

/-- The constant of the closing corollary (with self-loops). -/
noncomputable def rateC (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  VarianceGeneral.vk d σ (n + 1) + 2 * (2 * rateC1 d σ n)

theorem CQT_nonneg {σ : ℝ} (hσ : 0 < σ) (d n : ℕ) : 0 ≤ CQT d σ n := by
  have := B4_nonneg hσ d n; have := torusM_one_ge hσ d; unfold CQT; positivity

theorem Cq_nonneg (n : ℕ) : 0 ≤ VarianceGeneral3.Cq n := by
  unfold VarianceGeneral3.Cq; positivity

/-- The bracket of `variance_general_sharp` is `≤ 2 rateC1 (log N + 1)² / N³`. -/
theorem bracket_le {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {N : ℕ} (hN2 : 2 ≤ N) (n : ℕ) :
    2 * ((gK n * deltaN d σ N * torusM d σ 1) ^ 2 * deltaN d σ N ^ 2
        * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 5))
      + 2 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))
      ≤ 2 * rateC1 d σ n * (Real.log N + 1) ^ 2 / (N : ℝ) ^ 3 := by
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log N + 1 := ⟨_, rfl⟩
  rw [← hΛ]
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  have hΛ2 : 1 ≤ Λ ^ 2 := one_le_pow₀ hΛ1
  have hδ2 := deltaN_sq hσ d hN2
  rw [← hΛ] at hδ2
  have hK0 := K0_nonneg hσ d
  have hCQ := CQT_nonneg hσ d n
  have hCq := Cq_nonneg n
  have hcA := VarianceGeneral3.cA_nonneg n
  have hB4 := B4_nonneg hσ d n
  obtain ⟨D2, hD2⟩ : ∃ D2 : ℝ, D2 = deltaN d σ N ^ 2 := ⟨_, rfl⟩
  have hD20 : 0 ≤ D2 := by rw [hD2]; positivity
  rw [← hD2] at hδ2
  have pA : (gK n * deltaN d σ N * torusM d σ 1) ^ 2 * deltaN d σ N ^ 2
      * (2 * torusM d σ 1 ^ 2 / N)
      ≤ 2 * gK n ^ 2 * torusM d σ 1 ^ 4 * K0 d σ ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3) := by
    have e : (gK n * deltaN d σ N * torusM d σ 1) ^ 2 * deltaN d σ N ^ 2
        * (2 * torusM d σ 1 ^ 2 / N) = 2 * gK n ^ 2 * torusM d σ 1 ^ 4 * D2 ^ 2 / N := by
      rw [hD2]; ring
    rw [e]
    have hsq : D2 ^ 2 ≤ (K0 d σ * Λ / N) ^ 2 := pow_le_pow_left₀ hD20 hδ2 2
    calc 2 * gK n ^ 2 * torusM d σ 1 ^ 4 * D2 ^ 2 / N
        ≤ 2 * gK n ^ 2 * torusM d σ 1 ^ 4 * (K0 d σ * Λ / N) ^ 2 / N := by gcongr
      _ = 2 * gK n ^ 2 * torusM d σ 1 ^ 4 * K0 d σ ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3) := by
          field_simp
  have pQ : (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 5) ≤ (1 + CQT d σ n) ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3) := by
    have h1 : (N : ℝ) + CQT d σ n ≤ N * (1 + CQT d σ n) := by nlinarith
    have h2 : ((N : ℝ) + CQT d σ n) ^ 2 ≤ (N * (1 + CQT d σ n)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    calc (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 5) ≤ (N * (1 + CQT d σ n)) ^ 2 * (1 / (N : ℝ) ^ 5) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (1 + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 3) := by field_simp
      _ ≤ (1 + CQT d σ n) ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3) := by gcongr
  have pR : VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3)
      ≤ VarianceGeneral3.Cq n * VarianceGeneral3.cA n * B4 d σ n ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3) := by
    calc VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3)
        = VarianceGeneral3.Cq n * VarianceGeneral3.cA n * B4 d σ n ^ 2 * (1 / (N : ℝ) ^ 3) := by
          ring
      _ ≤ _ := by gcongr
  have e2 : 2 * rateC1 d σ n * Λ ^ 2 / (N : ℝ) ^ 3
      = 2 * (2 * gK n ^ 2 * torusM d σ 1 ^ 4 * K0 d σ ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3)
        + (1 + CQT d σ n) ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3)
        + VarianceGeneral3.Cq n * VarianceGeneral3.cA n * B4 d σ n ^ 2 * (Λ ^ 2 / (N : ℝ) ^ 3)) := by
    unfold rateC1; ring
  rw [e2]
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Closing corollary, with self-loops**: under the hypotheses of `variance_general_sharp`
    (independent uniform points, `σ > 0`, `N ≥ 2`, `δ_N ≤ 1/8`):
    `|Var Tr P^k - v_k (N-1)/N³| ≤ rateC · (log N + 1)² · N^{-5/2}`, where `rateC` depends only on
    `d`, `σ`, `k`.  Since the main term is `v_k (N-1)/N³ ≍ v_k N⁻²`, the remainder is
    `o(N⁻²)`. -/
theorem variance_general_rate [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN2 : 2 ≤ N)
    (hδ : deltaN d σ N ≤ 1 / 8) (n : ℕ) :
    |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ rateC d σ n * (Real.log N + 1) ^ 2 / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have h := variance_general_sharp X h_indep hX hlaw hσ N hN2 hδ n
  refine h.trans ?_
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have hW : 1 ≤ (Real.log N + 1) ^ 2 := one_le_pow₀ (by linarith)
  have hc : 0 ≤ 2 * rateC1 d σ n := by
    have := K0_nonneg hσ d; have := CQT_nonneg hσ d n; have := Cq_nonneg n
    have := VarianceGeneral3.cA_nonneg n
    unfold rateC1; positivity
  have hX' := bracket_le hσ d hN2 n
  have hX'' : 2 * ((gK n * deltaN d σ N * torusM d σ 1) ^ 2 * deltaN d σ N ^ 2
        * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 5))
      + 2 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))
      ≤ 2 * rateC1 d σ n * (Real.log N + 1) ^ 2 / (N : ℝ) ^ 3 := hX'
  have := rate_alg hs1 hsN hW (VarianceGeneral.vk_nonneg d σ (n + 1)) hc hX''
  unfold rateC
  exact this

end Rate

section NoLoops

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **`prop:variance` WITHOUT self-loops, every `k = n + 1 ≥ 2`, sharp form.** Independent uniform
    points, `σ > 0`, `N ≥ 2`, `δ_N + m₁/N ≤ 1/8`:
    `|Var Tr P°^k - v_k (N-1)/N³| ≤ N^{-1/2} v_k (N-1)/N³ + (1 + √N)(4 E₁ + 4 R + 2 D)` with
    `E₁ = (gK δ_N m₁)² δ_N² (2m₁²/N) + (N + CQT)²/N⁵`, `R = Cq cA B4²/N³`,
    `D = DbNL(δ_N) + 6 BoffNL²/N⁵`. -/
theorem variance_noloops_sharp [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN2 : 2 ≤ N)
    (hu : deltaN d σ N + torusM d σ 1 / N ≤ 1 / 8) (n : ℕ) (hn : 1 ≤ n) :
    |cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ 1 / Real.sqrt N * (VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3)
        + (1 + Real.sqrt N) * (4 * ((gK n * deltaN d σ N * torusM d σ 1) ^ 2 * deltaN d σ N ^ 2
            * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 5))
          + 4 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))
          + 2 * (VarianceNoLoops.DbNL d σ N n (deltaN d σ N)
            + 6 * VarianceNoLoops.BoffNL d σ N n ^ 2 * (1 / (N : ℝ) ^ 5))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hθ : 0 < 1 / Real.sqrt N := by positivity
  have hδ : deltaN d σ N ≤ 1 / 8 := by
    have : 0 ≤ torusM d σ 1 / N := div_nonneg (zero_le_one.trans (torusM_one_ge hσ d)) hNpos.le
    linarith
  rw [← VarianceGeneral5.vq_eq_vk_ae hσ n]
  have h := VarianceNoLoops.variance_noloops_v' X h_indep hX hlaw hσ N (by omega)
    (deltaN_nonneg hσ d N) hu n hn hθ
  rw [one_div_one_div] at h
  have hP := deltaN_event hσ d X h_indep hX hlaw N hN2 hδ
  refine h.trans ?_
  gcongr

/-- `K₁ = 2 K₀ + 2 m₁²`: `(δ_N + m₁/N)² ≤ K₁ (log N + 1)/N`. -/
noncomputable def K1 (d : ℕ) (σ : ℝ) : ℝ := 2 * K0 d σ + 2 * torusM d σ 1 ^ 2

set_option maxHeartbeats 1000000 in
/-- The algebra of the comparison error: `(Eb + Rb)² ≤ (50 g² M² K₁³ + 2 (Cd + Cr)² M² K₁) Λ³/N³`. -/
theorem eb_alg {g M Cd Cr δ c K Λ N : ℝ} (hg : 0 ≤ g) (hM : 0 ≤ M) (hCd : 0 ≤ Cd) (hCr : 0 ≤ Cr)
    (hδ : 0 ≤ δ) (hN : 1 ≤ N) (hcd : c = M / N) (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (hr : (δ + c) ^ 2 ≤ K * Λ / N) :
    (g * ((δ + c) * M * (2 * δ ^ 2 + 2 * c ^ 2)) + g * (δ * M * δ ^ 2) + Cd * c * (δ + c)
        + c ^ 2 * Cr) ^ 2
      ≤ (50 * g ^ 2 * M ^ 2 * K ^ 3 + 2 * (Cd + Cr) ^ 2 * M ^ 2 * K) * Λ ^ 3 / N ^ 3 := by
  have hNpos : 0 < N := by linarith
  have hc : 0 ≤ c := by rw [hcd]; positivity
  obtain ⟨r, hrd⟩ : ∃ r, r = δ + c := ⟨_, rfl⟩
  rw [← hrd] at hr ⊢
  have hr0 : 0 ≤ r := by rw [hrd]; linarith
  have hδr : δ ≤ r := by rw [hrd]; linarith
  have hcr : c ≤ r := by rw [hrd]; linarith
  have hE : g * (r * M * (2 * δ ^ 2 + 2 * c ^ 2)) + g * (δ * M * δ ^ 2) + Cd * c * r + c ^ 2 * Cr
      ≤ 5 * g * M * r ^ 3 + (Cd + Cr) * c * r := by
    have a1 : 2 * δ ^ 2 + 2 * c ^ 2 ≤ 4 * r ^ 2 := by nlinarith
    have a2 : δ * δ ^ 2 ≤ r ^ 3 := by
      have : δ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hδ hδr 3
      nlinarith
    have a3 : c ^ 2 ≤ c * r := by nlinarith
    have b1 := mul_le_mul_of_nonneg_left a1 (by positivity : 0 ≤ g * (r * M))
    have b2 := mul_le_mul_of_nonneg_left a2 (by positivity : 0 ≤ g * M)
    have b3 := mul_le_mul_of_nonneg_right a3 hCr
    linarith [b1, b2, b3]
  have hE0 : 0 ≤ g * (r * M * (2 * δ ^ 2 + 2 * c ^ 2)) + g * (δ * M * δ ^ 2) + Cd * c * r
      + c ^ 2 * Cr := by positivity
  have hsq := pow_le_pow_left₀ hE0 hE 2
  have h2 : (5 * g * M * r ^ 3 + (Cd + Cr) * c * r) ^ 2
      ≤ 2 * (25 * g ^ 2 * M ^ 2 * (r ^ 2) ^ 3) + 2 * ((Cd + Cr) ^ 2 * c ^ 2 * r ^ 2) := by
    nlinarith [_root_.sq_nonneg (5 * g * M * r ^ 3 - (Cd + Cr) * c * r)]
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have h3 : (r ^ 2) ^ 3 ≤ (K * Λ / N) ^ 3 := pow_le_pow_left₀ hr2 hr 3
  have h4 : c ^ 2 * r ^ 2 ≤ (M / N) ^ 2 * (K * Λ / N) := by
    rw [hcd]; exact mul_le_mul_of_nonneg_left hr (by positivity)
  have hΛ3 : Λ ≤ Λ ^ 3 := by
    have h1 : 1 ≤ Λ ^ 2 := one_le_pow₀ hΛ
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Λ)
    have e : Λ * Λ ^ 2 = Λ ^ 3 := by ring
    linarith
  have e1 : (K * Λ / N) ^ 3 = K ^ 3 * Λ ^ 3 / N ^ 3 := by field_simp
  have e2 : (M / N) ^ 2 * (K * Λ / N) = M ^ 2 * K * Λ / N ^ 3 := by field_simp
  have h5 : M ^ 2 * K * Λ / N ^ 3 ≤ M ^ 2 * K * Λ ^ 3 / N ^ 3 := by gcongr
  rw [e1] at h3; rw [e2] at h4
  have h6 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * (25 * g ^ 2 * M ^ 2))
  have h7 := mul_le_mul_of_nonneg_left (h4.trans h5) (by positivity : (0 : ℝ) ≤ 2 * (Cd + Cr) ^ 2)
  have e3 : (50 * g ^ 2 * M ^ 2 * K ^ 3 + 2 * (Cd + Cr) ^ 2 * M ^ 2 * K) * Λ ^ 3 / N ^ 3
      = 2 * (25 * g ^ 2 * M ^ 2) * (K ^ 3 * Λ ^ 3 / N ^ 3)
        + 2 * (Cd + Cr) ^ 2 * (M ^ 2 * K * Λ ^ 3 / N ^ 3) := by ring
  rw [e3]
  linarith [hsq, h2, h6, h7]

/-- The constant of the comparison part of the closing corollary without self-loops. -/
noncomputable def DbC (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  3 * ((n : ℝ) + 1) ^ 2 * torusM d σ 1 ^ 2
      * ((3 * ((n : ℝ) + 1) ^ 2 * torusM d σ 1 ^ (n + 1)) ^ 2
        + (3 * (n : ℝ) ^ 2 * torusM d σ 1 ^ n) ^ 2)
    + 6 * (50 * gK n ^ 2 * torusM d σ 1 ^ 2 * K1 d σ ^ 3
      + 2 * (CdetT n (torusM d σ 1) + (2 ^ (n + 1) * torusM d σ 1 ^ (n + 1) + torusM d σ 1)) ^ 2
        * torusM d σ 1 ^ 2 * K1 d σ)

/-- `BoffNL ≤ N · BoC`. -/
noncomputable def BoC (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  2 + 2 * torusM d σ 1 ^ (n + 1) + ((n : ℝ) + 1) * torusM d σ 1 ^ (n + 2)

/-- The constant of the closing corollary without self-loops, without `v_k`. -/
noncomputable def rateNL1 (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ := 2 * rateC1 d σ n + DbC d σ n + 6 * BoC d σ n ^ 2

/-- The constant of the closing corollary without self-loops. -/
noncomputable def rateNC (d : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  VarianceGeneral.vk d σ (n + 1) + 2 * (2 * rateNL1 d σ n)

set_option maxHeartbeats 1000000 in
theorem DbNL_le {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {N : ℕ} (hN2 : 2 ≤ N) (n : ℕ) :
    VarianceNoLoops.DbNL d σ N n (deltaN d σ N) ≤ DbC d σ n * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3 := by
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = Real.log N + 1 := ⟨_, rfl⟩
  rw [← hΛ]
  have hΛ1 : 1 ≤ Λ := by rw [hΛ]; linarith
  have hΛ3 : 1 ≤ Λ ^ 3 := one_le_pow₀ hΛ1
  have hM1 := torusM_one_ge hσ d
  have hM0 : 0 ≤ torusM d σ 1 := by linarith
  have hK0 := K0_nonneg hσ d
  have hK1 : 0 ≤ K1 d σ := by unfold K1; positivity
  have hδ0 := deltaN_nonneg hσ d N
  have hδ2 := deltaN_sq hσ d hN2
  rw [← hΛ] at hδ2
  -- `(δ + c)² ≤ K₁ Λ / N`
  have hr : (deltaN d σ N + torusM d σ 1 / N) ^ 2 ≤ K1 d σ * Λ / N := by
    have h1 : (deltaN d σ N + torusM d σ 1 / N) ^ 2
        ≤ 2 * deltaN d σ N ^ 2 + 2 * (torusM d σ 1 / N) ^ 2 := by
      nlinarith [_root_.sq_nonneg (deltaN d σ N - torusM d σ 1 / N)]
    have h2 : (torusM d σ 1 / N) ^ 2 ≤ torusM d σ 1 ^ 2 * Λ / N := by
      rw [div_pow, div_le_div_iff₀ (by positivity) hNpos]
      have : (N : ℝ) ≤ Λ * (N : ℝ) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ torusM d σ 1 ^ 2)]
    have e : K1 d σ * Λ / N = 2 * (K0 d σ * Λ / N) + 2 * (torusM d σ 1 ^ 2 * Λ / N) := by
      unfold K1; ring
    rw [e]; linarith
  have hgK := gK_nonneg n
  have hCd := CdetT_nonneg n hM0
  have hEb := eb_alg (g := gK n) (M := torusM d σ 1) (Cd := CdetT n (torusM d σ 1))
    (Cr := 2 ^ (n + 1) * torusM d σ 1 ^ (n + 1) + torusM d σ 1) hgK hM0 hCd (by positivity)
    hδ0 hN1 rfl hΛ1 hK1 hr
  have eEb : VarianceNoLoops.EbNL d σ N n (deltaN d σ N) + VarianceNoLoops.RbNL d σ N n
      = gK n * ((deltaN d σ N + torusM d σ 1 / N) * torusM d σ 1
          * (2 * deltaN d σ N ^ 2 + 2 * (torusM d σ 1 / N) ^ 2))
        + gK n * (deltaN d σ N * torusM d σ 1 * deltaN d σ N ^ 2)
        + CdetT n (torusM d σ 1) * (torusM d σ 1 / N) * (deltaN d σ N + torusM d σ 1 / N)
        + (torusM d σ 1 / N) ^ 2 * (2 ^ (n + 1) * torusM d σ 1 ^ (n + 1) + torusM d σ 1) := by
    unfold VarianceNoLoops.EbNL VarianceNoLoops.RbNL; ring
  -- the first term
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 3 * ((n : ℝ) + 1) ^ 2 * torusM d σ 1 ^ 2
      * ((3 * ((n : ℝ) + 1) ^ 2 * torusM d σ 1 ^ (n + 1)) ^ 2
        + (3 * (n : ℝ) ^ 2 * torusM d σ 1 ^ n) ^ 2) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have e1 : 3 * ((n : ℝ) + 1) ^ 2 * (torusM d σ 1 / N) ^ 2
      * ((3 * ((n : ℝ) + 1) ^ 2 * torusM d σ 1 ^ (n + 1) / N) ^ 2
        + (3 * (n : ℝ) ^ 2 * torusM d σ 1 ^ n / N) ^ 2) = P / (N : ℝ) ^ 4 := by
    rw [hP]; field_simp
  have h1 : P / (N : ℝ) ^ 4 ≤ P * Λ ^ 3 / (N : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h34 : (N : ℝ) ^ 3 ≤ (N : ℝ) ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have h44 : (N : ℝ) ^ 4 ≤ Λ ^ 3 * (N : ℝ) ^ 4 :=
      le_mul_of_one_le_left (by positivity) hΛ3
    have := mul_le_mul_of_nonneg_left (h34.trans h44) hP0
    linarith
  unfold VarianceNoLoops.DbNL
  rw [e1, eEb]
  have e3 : DbC d σ n * Λ ^ 3 / (N : ℝ) ^ 3 = P * Λ ^ 3 / (N : ℝ) ^ 3
      + 6 * ((50 * gK n ^ 2 * torusM d σ 1 ^ 2 * K1 d σ ^ 3
        + 2 * (CdetT n (torusM d σ 1) + (2 ^ (n + 1) * torusM d σ 1 ^ (n + 1) + torusM d σ 1)) ^ 2
          * torusM d σ 1 ^ 2 * K1 d σ) * Λ ^ 3 / (N : ℝ) ^ 3) := by
    rw [hP]; unfold DbC; ring
  rw [e3]
  linarith

theorem Boff_le {σ : ℝ} (hσ : 0 < σ) (d : ℕ) {N : ℕ} (hN2 : 2 ≤ N) (n : ℕ) :
    6 * VarianceNoLoops.BoffNL d σ N n ^ 2 * (1 / (N : ℝ) ^ 5)
      ≤ 6 * BoC d σ n ^ 2 * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3 := by
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hΛ3 : 1 ≤ (Real.log N + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hM1 := torusM_one_ge hσ d
  have hb : VarianceNoLoops.BoffNL d σ N n ≤ N * BoC d σ n := by
    unfold VarianceNoLoops.BoffNL BoC
    have h1 : 1 ≤ torusM d σ 1 ^ (n + 1) := one_le_pow₀ hM1
    have h2 : 1 ≤ torusM d σ 1 ^ (n + 2) := one_le_pow₀ hM1
    have := mul_nonneg (by linarith : 0 ≤ (N : ℝ) - 1)
      (by positivity : 0 ≤ 2 * torusM d σ 1 ^ (n + 1) + ((n : ℝ) + 1) * torusM d σ 1 ^ (n + 2))
    linarith
  have hb0 : 0 ≤ VarianceNoLoops.BoffNL d σ N n := by unfold VarianceNoLoops.BoffNL; positivity
  have hsq := pow_le_pow_left₀ hb0 hb 2
  calc 6 * VarianceNoLoops.BoffNL d σ N n ^ 2 * (1 / (N : ℝ) ^ 5)
      ≤ 6 * (N * BoC d σ n) ^ 2 * (1 / (N : ℝ) ^ 5) := by gcongr
    _ = 6 * BoC d σ n ^ 2 * 1 / (N : ℝ) ^ 3 := by field_simp
    _ ≤ 6 * BoC d σ n ^ 2 * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3 := by gcongr

/-- **Closing corollary WITHOUT self-loops**: under the hypotheses of `variance_noloops_sharp`
    (`σ > 0`, `N ≥ 2`, `δ_N + m₁/N ≤ 1/8`, `k = n + 1 ≥ 2`):
    `|Var Tr P°^k - v_k (N-1)/N³| ≤ rateNC · (log N + 1)³ · N^{-5/2}`, `rateNC` depending only on
    `d`, `σ`, `k`; `o(N⁻²)` against the main term `v_k (N-1)/N³`. -/
theorem variance_noloops_rate [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN2 : 2 ≤ N)
    (hu : deltaN d σ N + torusM d σ 1 / N ≤ 1 / 8) (n : ℕ) (hn : 1 ≤ n) :
    |cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
        - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ rateNC d σ n * (Real.log N + 1) ^ 3 / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have h := variance_noloops_sharp X h_indep hX hlaw hσ N hN2 hu n hn
  refine h.trans ?_
  have hs1 : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have hW : 1 ≤ (Real.log N + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hW2 : (Real.log N + 1) ^ 2 ≤ (Real.log N + 1) ^ 3 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hC1 : 0 ≤ rateC1 d σ n := by
    have := K0_nonneg hσ d; have := CQT_nonneg hσ d n; have := Cq_nonneg n
    have := VarianceGeneral3.cA_nonneg n
    unfold rateC1; positivity
  have hDbC : 0 ≤ DbC d σ n := by
    have := torusM_one_ge hσ d; have := gK_nonneg n
    have := CdetT_nonneg n (zero_le_one.trans (torusM_one_ge hσ d))
    have := K0_nonneg hσ d
    unfold DbC K1; positivity
  have hc : 0 ≤ rateNL1 d σ n := by unfold rateNL1; positivity
  have hB := bracket_le hσ d hN2 n
  have hB' : 2 * rateC1 d σ n * (Real.log N + 1) ^ 2 / (N : ℝ) ^ 3
      ≤ 2 * rateC1 d σ n * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3 := by gcongr
  have hD := DbNL_le hσ d hN2 n
  have hBo := Boff_le hσ d hN2 n
  have hX : 4 * ((gK n * deltaN d σ N * torusM d σ 1) ^ 2 * deltaN d σ N ^ 2
            * (2 * torusM d σ 1 ^ 2 / N) + (N + CQT d σ n) ^ 2 * (1 / (N : ℝ) ^ 5))
          + 4 * (VarianceGeneral3.Cq n * (VarianceGeneral3.cA n * B4 d σ n ^ 2 / (N : ℝ) ^ 3))
          + 2 * (VarianceNoLoops.DbNL d σ N n (deltaN d σ N)
            + 6 * VarianceNoLoops.BoffNL d σ N n ^ 2 * (1 / (N : ℝ) ^ 5))
      ≤ 2 * rateNL1 d σ n * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3 := by
    have e : 2 * rateNL1 d σ n * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3
        = 2 * (2 * rateC1 d σ n * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3)
          + 2 * (DbC d σ n * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3)
          + 2 * (6 * BoC d σ n ^ 2 * (Real.log N + 1) ^ 3 / (N : ℝ) ^ 3) := by
      unfold rateNL1; ring
    rw [e]
    linarith
  have hc2 : 0 ≤ 2 * rateNL1 d σ n := by linarith
  have := rate_alg hs1 hsN hW (VarianceGeneral.vk_nonneg d σ (n + 1)) hc2 hX
  unfold rateNC
  exact this

end NoLoops

end VarianceSharp

namespace VarianceLimit

/-! # A111, stage 1: the hypothesis `δ_N ≤ 1/8` holds for all large `N`; limit statements

`deltaN d σ N = O(√(log N / N)) → 0` (`deltaN_tendsto`), hence `δ_N ≤ 1/8` and
`δ_N + m₁/N ≤ 1/8` hold eventually.  Inserted into `VarianceSharp.variance_general_rate` and
`VarianceSharp.variance_noloops_rate`, this gives the eventual bounds without the numerical
hypothesis and the limits `N² · Var Tr P_N^k → v_k` (with self-loops, every `k ≥ 1`;
without self-loops, every `k ≥ 2`).  The sample of size `N` is the first `N` points of one
sequence of independent uniform points. -/

open Filter Topology WalkCount Function BiasGeneral BiasGeneral2 BiasGeneral3 BiasGeneral4
  BiasGeneral5 BiasGeneral6 PiBound CTG.Reals.TorusReduction BiasVariance BiasVariance4 NoLoops
  BiasNoLoops VarianceOne VarianceSharp

/-- `(log x + 1)^p ≤ 9^p x^{p/8}` for `x ≥ 1`. -/
theorem log_add_one_pow_le {x : ℝ} (hx : 1 ≤ x) (p : ℕ) :
    (Real.log x + 1) ^ p ≤ 9 ^ p * x ^ ((p : ℝ) / 8) := by
  have h0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have h1 : Real.log x ≤ x ^ ((1 : ℝ) / 8) / (1 / 8) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have h3 : Real.log x + 1 ≤ 9 * x ^ ((1 : ℝ) / 8) := by
    have h2 : 1 ≤ x ^ ((1 : ℝ) / 8) := Real.one_le_rpow hx (by norm_num)
    have e : x ^ ((1 : ℝ) / 8) / (1 / 8) = 8 * x ^ ((1 : ℝ) / 8) := by ring
    linarith
  calc (Real.log x + 1) ^ p ≤ (9 * x ^ ((1 : ℝ) / 8)) ^ p := pow_le_pow_left₀ (by linarith) h3 p
    _ = 9 ^ p * x ^ ((p : ℝ) / 8) := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ _), ← Real.rpow_mul (by linarith)]
      congr 2; ring

/-- `(log N + 1)^p / √N → 0` for `p ≤ 3`. -/
theorem tendsto_log_pow_div_sqrt (p : ℕ) (hp : p ≤ 3) :
    Tendsto (fun N : ℕ => (Real.log N + 1) ^ p / Real.sqrt N) atTop (𝓝 0) := by
  have hneg : 0 < -((p : ℝ) / 8 - 1 / 2) := by
    have : (p : ℝ) ≤ 3 := by exact_mod_cast hp
    linarith
  have hlim : Tendsto (fun N : ℕ => 9 ^ p * (N : ℝ) ^ ((p : ℝ) / 8 - 1 / 2)) atTop (𝓝 0) := by
    have h1 := (tendsto_rpow_neg_atTop hneg).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul ((9 : ℝ) ^ p)
    rw [mul_zero] at h2
    refine h2.congr (fun N => ?_)
    simp only [Function.comp_apply, neg_neg]
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  rw [Real.sqrt_eq_rpow, Real.rpow_sub hNpos, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (log_add_one_pow_le hN1 p) (by positivity)

/-- **`δ_N → 0`** for fixed `d` and `σ > 0`. -/
theorem deltaN_tendsto {σ : ℝ} (hσ : 0 < σ) (d : ℕ) :
    Tendsto (fun N : ℕ => deltaN d σ N) atTop (𝓝 0) := by
  have hq : Tendsto (fun N : ℕ => (Real.log N + 1) / N) atTop (𝓝 0) := by
    have h1 := tendsto_log_pow_div_sqrt 1 (by norm_num)
    simp only [pow_one] at h1
    refine squeeze_zero' ?_ ?_ h1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : 0 ≤ Real.log N := Real.log_nonneg hN1
      positivity
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : 0 ≤ Real.log N := Real.log_nonneg hN1
      have hs : Real.sqrt N ≤ N := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      exact div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr (by linarith)) hs
  have hlim : Tendsto (fun N : ℕ => Real.sqrt (K0 d σ * ((Real.log N + 1) / N))) atTop (𝓝 0) := by
    have := (hq.const_mul (K0 d σ)).sqrt
    rwa [mul_zero, Real.sqrt_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun N => deltaN_nonneg hσ d N) ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with N hN
  have h := Real.abs_le_sqrt (deltaN_sq hσ d hN)
  rw [abs_of_nonneg (deltaN_nonneg hσ d N), mul_div_assoc] at h
  exact h

/-- `δ_N ≤ 1/8` for all large `N`. -/
theorem deltaN_eventually {σ : ℝ} (hσ : 0 < σ) (d : ℕ) :
    ∀ᶠ N : ℕ in atTop, deltaN d σ N ≤ 1 / 8 :=
  ((deltaN_tendsto hσ d).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8)).mono
    fun _ h => h.le

/-- `δ_N + m₁/N ≤ 1/8` for all large `N`. -/
theorem deltaN_add_eventually {σ : ℝ} (hσ : 0 < σ) (d : ℕ) :
    ∀ᶠ N : ℕ in atTop, deltaN d σ N + torusM d σ 1 / N ≤ 1 / 8 := by
  have h := (deltaN_tendsto hσ d).add (tendsto_const_div_atTop_nhds_zero_nat (torusM d σ 1))
  rw [add_zero] at h
  exact (h.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8)).mono fun _ h => h.le

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Eventual rate, with self-loops, without the hypothesis `δ_N ≤ 1/8`.** Independent uniform
    points on `FlatTorus d`, `σ > 0`, every `k = n + 1`: for all large `N`,
    `|Var Tr P_N^k - v_k (N-1)/N³| ≤ rateC (log N + 1)² N^{-5/2}`. -/
theorem variance_general_rate_eventually [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      |cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
          - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
        ≤ rateC d σ n * (Real.log N + 1) ^ 2 / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  filter_upwards [eventually_ge_atTop 2, deltaN_eventually hσ d] with N hN hδ
  exact variance_general_rate X h_indep hX hlaw hσ N hN hδ n

/-- **Eventual rate, without self-loops, without the hypothesis `δ_N + m₁/N ≤ 1/8`.** Every
    `k = n + 1 ≥ 2`: for all large `N`,
    `|Var Tr P°_N^k - v_k (N-1)/N³| ≤ rateNC (log N + 1)³ N^{-5/2}`. -/
theorem variance_noloops_rate_eventually [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ N : ℕ in atTop,
      |cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace)
          - VarianceGeneral.vk d σ (n + 1) * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
        ≤ rateNC d σ n * (Real.log N + 1) ^ 3 / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  filter_upwards [eventually_ge_atTop 2, deltaN_add_eventually hσ d] with N hN hu
  exact variance_noloops_rate X h_indep hX hlaw hσ N hN hu n hn

/-- The passage from the eventual rate to the limit `N² V_N → v`. -/
theorem limit_of_rate {V : ℕ → ℝ} {v C : ℝ} {p : ℕ} (hp : p ≤ 3)
    (h : ∀ᶠ N : ℕ in atTop, |V N - v * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
      ≤ C * (Real.log N + 1) ^ p / ((N : ℝ) ^ 2 * Real.sqrt N)) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * V N) atTop (𝓝 v) := by
  have hdiff : Tendsto (fun N : ℕ => (N : ℝ) ^ 2 * V N - v * (1 - 1 / (N : ℝ))) atTop (𝓝 0) := by
    have ha := (tendsto_log_pow_div_sqrt p hp).const_mul |C|
    rw [mul_zero] at ha
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNpos : (0 : ℝ) < N := by linarith
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
    have e : (N : ℝ) ^ 2 * V N - v * (1 - 1 / (N : ℝ))
        = (N : ℝ) ^ 2 * (V N - v * ((N : ℝ) - 1) / (N : ℝ) ^ 3) := by
      field_simp
    rw [Real.norm_eq_abs, e, abs_mul, abs_of_nonneg (by positivity)]
    have hl : 0 ≤ Real.log N := Real.log_nonneg hN1r
    calc (N : ℝ) ^ 2 * |V N - v * ((N : ℝ) - 1) / (N : ℝ) ^ 3|
        ≤ (N : ℝ) ^ 2 * (C * (Real.log N + 1) ^ p / ((N : ℝ) ^ 2 * Real.sqrt N)) :=
          mul_le_mul_of_nonneg_left hN (by positivity)
      _ = C * ((Real.log N + 1) ^ p / Real.sqrt N) := by field_simp
      _ ≤ |C| * ((Real.log N + 1) ^ p / Real.sqrt N) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have hg : Tendsto (fun N : ℕ => v * (1 - 1 / (N : ℝ))) atTop (𝓝 v) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) - 1 / (N : ℝ)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    have := h1.const_mul v
    rwa [sub_zero, mul_one] at this
  have h2 := hdiff.add hg
  rw [zero_add] at h2
  exact h2.congr (fun N => sub_add_cancel _ _)

/-- **Limit, with self-loops.** Independent uniform points on `FlatTorus d` (the sample of size
    `N` is `X 0, …, X (N-1)`), `σ > 0`, every `k = n + 1 ≥ 1`:
    `N² · Var(Tr P_N^k) → v_k` as `N → ∞`. -/
theorem variance_general_limit [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2
        * cv μ (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace))
      atTop (𝓝 (VarianceGeneral.vk d σ (n + 1))) :=
  limit_of_rate (by norm_num) (variance_general_rate_eventually X h_indep hX hlaw hσ n)

/-- **Limit, without self-loops.** Every `k = n + 1 ≥ 2`: `N² · Var(Tr P°_N^k) → v_k`. -/
theorem variance_noloops_limit [IsProbabilityMeasure μ] {d : ℕ}
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ 2
        * cv μ (fun ω => ((noloopWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace))
      atTop (𝓝 (VarianceGeneral.vk d σ (n + 1))) :=
  limit_of_rate le_rfl (variance_noloops_rate_eventually X h_indep hX hlaw hσ n hn)

end VarianceLimit

namespace DegenerateGeneral

/-! # A111, stage 2: Lemma `lem:degenerate`(a) for a general number of indices

Setting: an independent sample `X_0, X_1, …` with law `ν` (`VarianceOne.SP`), a bounded measurable
kernel `F` of `n + 1` points, degenerate in the last argument, whose conditional mean given the
last point vanishes (`hcond`; on the flat torus this follows from translation invariance,
`degenerate_a_general_torus`).  The norms of the lemma enter as upper bounds in sample form:
`V ≥ E F(X_ι)²` for injective index maps (`‖F‖₂²`), `ρ ≥ E|F(X_ι)|` for index maps whose image has
exactly `n` elements, i.e. one pair of positions identified (`ϱ(F)`), `B ≥ sup |F|`.  Then
`E |N^{-(n+1)} ∑_ι F(X_ι)| ≤ (n+1)² √V / N + (n+1)² ρ / N + (n+1)^{n+1} B / N²`.
The proof is that of the paper: the products of two injective summands vanish in the mean unless
the images have at least two common elements (`int_set`, `pair_zero`), there are at most
`(n+1)⁴ N^{2n}` such pairs (`twoPairs_card`); the non-injective maps are counted
(`noninj_count`, `image_card_count`). -/

open PiBound VarianceOne VarianceGeneral2

section Abstract

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*}
  [MeasurableSpace G] {ν : Measure G} {X : ℕ → Ω → G}

/-- **Integrating out one private coordinate** of the first tuple in a product of two tuple
    functions. -/
theorem step_int [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n n' : ℕ} (ι : Fin n → ℕ) (ι' : Fin n' → ℕ) (v : Fin n)
    (hv : ∀ m, m ≠ v → ι m ≠ ι v) (hv' : ∀ m, ι' m ≠ ι v)
    (F : (Fin n → G) → ℝ) (F' : (Fin n' → G) → ℝ) (hF : BM F) (hF' : BM F') :
    ∫ ω, F (fun m => X (ι m) ω) * F' (fun m => X (ι' m) ω) ∂μ
      = ∫ ω, Av ν v F (fun m => X (ι m) ω) * F' (fun m => X (ι' m) ω) ∂μ := by
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : ((Fin n ⊕ Fin n') → G) → ℝ,
      Φ = fun y => F (fun m => y (Sum.inl m)) * F' (fun m => y (Sum.inr m)) := ⟨_, rfl⟩
  have hΦ : BM Φ := by
    rw [hΦd]
    exact BM.mul
      ⟨hF.meas.comp (measurable_pi_lambda _ fun m => measurable_pi_apply _),
        hF.bdd.imp fun _ h _ => h _⟩
      ⟨hF'.meas.comp (measurable_pi_lambda _ fun m => measurable_pi_apply _),
        hF'.bdd.imp fun _ h _ => h _⟩
  have hside : ∀ m : Fin n ⊕ Fin n', m ≠ Sum.inl v →
      Sum.elim ι ι' m ≠ Sum.elim ι ι' (Sum.inl v) := by
    rintro (m | m) hm
    · exact hv m fun h => hm (by rw [h])
    · exact hv' m
  have h := H.integrate_iso (Sum.elim ι ι') (Sum.inl v) hside Φ hΦ
  have key : ∀ (ω : Ω) (z : G),
      Φ (Function.update (fun m => X (Sum.elim ι ι' m) ω) (Sum.inl v) z)
        = F (Function.update (fun m => X (ι m) ω) v z) * F' (fun m => X (ι' m) ω) := by
    intro ω z
    rw [hΦd]
    have a1 : (fun m : Fin n => Function.update (fun m => X (Sum.elim ι ι' m) ω) (Sum.inl v) z
        (Sum.inl m)) = Function.update (fun m => X (ι m) ω) v z := by
      funext m
      by_cases hm : m = v
      · subst hm; simp
      · rw [Function.update_of_ne (Sum.inl_injective.ne hm), Function.update_of_ne hm]; rfl
    have a2 : (fun m : Fin n' => Function.update (fun m => X (Sum.elim ι ι' m) ω) (Sum.inl v) z
        (Sum.inr m)) = fun m => X (ι' m) ω := by
      funext m
      rw [Function.update_of_ne Sum.inr_ne_inl]; rfl
    show F _ * F' _ = _
    rw [a1, a2]
  have hL : ∫ ω, Φ (fun m => X (Sum.elim ι ι' m) ω) ∂μ
      = ∫ ω, F (fun m => X (ι m) ω) * F' (fun m => X (ι' m) ω) ∂μ := by
    simp only [hΦd, Sum.elim_inl, Sum.elim_inr]
  rw [← hL, h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp_rw [key]
  rw [integral_mul_const]
  rfl

/-- **Integrating out a set `W` of private coordinates** of the first tuple. -/
theorem int_set [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n n' : ℕ} (ι : Fin n → ℕ) (ι' : Fin n' → ℕ)
    (F : (Fin n → G) → ℝ) (F' : (Fin n' → G) → ℝ) (hF : BM F) (hF' : BM F')
    (W : Finset (Fin n)) (hW : ∀ v ∈ W, (∀ m, m ≠ v → ι m ≠ ι v) ∧ ∀ m, ι' m ≠ ι v) :
    ∫ ω, F (fun m => X (ι m) ω) * F' (fun m => X (ι' m) ω) ∂μ
      = ∫ ω, AW ν W F (fun m => X (ι m) ω) * F' (fun m => X (ι' m) ω) ∂μ := by
  induction W using Finset.induction_on with
  | empty => rw [AW_empty]
  | insert v W hv ih =>
    rw [ih (fun w hw => hW w (Finset.mem_insert_of_mem hw)), AW_insert hv hF]
    exact step_int H ι ι' v (hW v (Finset.mem_insert_self v W)).1
      (hW v (Finset.mem_insert_self v W)).2 _ F' (AW_bm W hF) hF'

/-- **Second moment with a mean bound on the non-vanishing products.** -/
theorem sm_le_V [IsProbabilityMeasure μ]
    (H : SP μ ν X) {n N : ℕ} (I : Finset (Fin n → Fin N)) (F : (Fin n → G) → ℝ) (hF : BM F)
    {V : ℝ} (hV0 : 0 ≤ V) (P : Finset ((Fin n → Fin N) × (Fin n → Fin N)))
    (hzero : ∀ ι ∈ I, ∀ ι' ∈ I, (ι, ι') ∉ P →
      ∫ ω, F (fun m => X (ι m) ω) * F (fun m => X (ι' m) ω) ∂μ = 0)
    (hpair : ∀ ι ∈ I, ∀ ι' ∈ I,
      ∫ ω, F (fun m => X (ι m) ω) * F (fun m => X (ι' m) ω) ∂μ ≤ V) :
    ∫ ω, (∑ ι ∈ I, F (fun m => X (ι m) ω)) ^ 2 ∂μ ≤ P.card * V := by
  classical
  have bm : ∀ ι : Fin n → Fin N, BM (fun ω => F (fun m => X (ι m) ω)) := fun ι =>
    H.bm (fun m => (ι m : ℕ)) hF
  have e : ∀ ω, (∑ ι ∈ I, F (fun m => X (ι m) ω)) ^ 2
      = ∑ q ∈ I ×ˢ I, F (fun m => X (q.1 m) ω) * F (fun m => X (q.2 m) ω) := by
    intro ω; rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  simp_rw [e]
  rw [integral_finset_sum _ fun q _ => ((bm q.1).mul (bm q.2)).integrable]
  have hterm : ∀ q ∈ I ×ˢ I, ∫ ω, F (fun m => X (q.1 m) ω) * F (fun m => X (q.2 m) ω) ∂μ
      ≤ if q ∈ P then V else 0 := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    split_ifs with hP
    · exact hpair q.1 h1 q.2 h2
    · exact (hzero q.1 h1 q.2 h2 hP).le
  calc ∑ q ∈ I ×ˢ I, ∫ ω, F (fun m => X (q.1 m) ω) * F (fun m => X (q.2 m) ω) ∂μ
      ≤ ∑ q ∈ I ×ˢ I, (if q ∈ P then V else 0) := Finset.sum_le_sum hterm
    _ = (((I ×ˢ I).filter (· ∈ P)).card : ℝ) * V := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ P.card * V := by
        apply mul_le_mul_of_nonneg_right _ hV0
        exact_mod_cast Finset.card_le_card (fun q hq => (Finset.mem_filter.mp hq).2)

end Abstract

section Count

/-- The pairs of index maps whose first map is injective and whose images have at least two
    common elements. -/
def twoPairs (n N : ℕ) : Finset ((Fin n → Fin N) × (Fin n → Fin N)) :=
  Finset.univ.filter fun q => Function.Injective q.1 ∧
    ∃ a b a' b', a ≠ b ∧ q.2 a' = q.1 a ∧ q.2 b' = q.1 b

/-- `N² · #twoPairs ≤ n⁴ N^{2n}`. -/
theorem twoPairs_card (n N : ℕ) :
    (N : ℝ) ^ 2 * ((twoPairs n N).card : ℝ) ≤ (n : ℝ) ^ 4 * ((N : ℝ) ^ n) ^ 2 := by
  classical
  have hfib : ∀ (a b a' b' : Fin n) (x : Fin n → Fin N), a' ≠ b' →
      N ^ 2 * (Fintype.piFinset (fun i : Fin n => if i = a' then ({x a} : Finset (Fin N))
        else if i = b' then {x b} else Finset.univ)).card = N ^ n := by
    intro a b a' b' x hab
    rw [Fintype.card_piFinset]
    have e : ∀ i : Fin n, (if i = a' then ({x a} : Finset (Fin N))
        else if i = b' then {x b} else Finset.univ).card
        = if i ∈ ({a', b'} : Finset (Fin n)) then 1 else N := by
      intro i
      by_cases h1 : i = a'
      · subst h1; simp
      · by_cases h2 : i = b'
        · subst h2; simp [h1]
        · simp [h1, h2]
    simp_rw [e]
    rw [prod_ite_mem n {a', b'} 1 N, Finset.card_pair hab, one_pow, one_mul, ← pow_add]
    have hn2 : 2 ≤ n := by
      have := Finset.card_le_univ ({a', b'} : Finset (Fin n))
      rw [Finset.card_pair hab, Fintype.card_fin] at this; exact this
    congr 1; omega
  obtain ⟨Cov, hCov⟩ : ∃ Cov : Finset ((Fin n → Fin N) × (Fin n → Fin N)), Cov =
      (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).biUnion fun t =>
        if t.2.2.1 = t.2.2.2 then ∅ else
          (Finset.univ : Finset (Fin n → Fin N)).biUnion fun x =>
            ({x} : Finset (Fin n → Fin N)) ×ˢ Fintype.piFinset (fun i : Fin n =>
              if i = t.2.2.1 then ({x t.1} : Finset (Fin N))
              else if i = t.2.2.2 then {x t.2.1} else Finset.univ) := ⟨_, rfl⟩
  have hsub : twoPairs n N ⊆ Cov := by
    intro q hq
    obtain ⟨hinj, a, b, a', b', hab, h1, h2⟩ := (Finset.mem_filter.mp hq).2
    have ha'b' : a' ≠ b' := by
      intro h; apply hab; apply hinj; rw [← h1, ← h2, h]
    rw [hCov]
    refine Finset.mem_biUnion.mpr ⟨(a, b, a', b'), Finset.mem_univ _, ?_⟩
    simp only
    rw [if_neg ha'b']
    refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    by_cases e1 : i = a'
    · subst e1; simp [h1]
    · by_cases e2 : i = b'
      · subst e2; simp [e1, h2]
      · simp [e1, e2]
  have hcard : N ^ 2 * Cov.card ≤ n ^ 4 * (N ^ n * N ^ n) := by
    rw [hCov]
    calc N ^ 2 * ((Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).biUnion fun t =>
          if t.2.2.1 = t.2.2.2 then ∅ else
            (Finset.univ : Finset (Fin n → Fin N)).biUnion fun x =>
              ({x} : Finset (Fin n → Fin N)) ×ˢ Fintype.piFinset (fun i : Fin n =>
                if i = t.2.2.1 then ({x t.1} : Finset (Fin N))
                else if i = t.2.2.2 then {x t.2.1} else Finset.univ)).card
        ≤ N ^ 2 * ∑ t : Fin n × Fin n × Fin n × Fin n, (if t.2.2.1 = t.2.2.2 then ∅ else
            (Finset.univ : Finset (Fin n → Fin N)).biUnion fun x =>
              ({x} : Finset (Fin n → Fin N)) ×ˢ Fintype.piFinset (fun i : Fin n =>
                if i = t.2.2.1 then ({x t.1} : Finset (Fin N))
                else if i = t.2.2.2 then {x t.2.1} else Finset.univ)).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ t : Fin n × Fin n × Fin n × Fin n, N ^ 2 * (if t.2.2.1 = t.2.2.2 then ∅ else
            (Finset.univ : Finset (Fin n → Fin N)).biUnion fun x =>
              ({x} : Finset (Fin n → Fin N)) ×ˢ Fintype.piFinset (fun i : Fin n =>
                if i = t.2.2.1 then ({x t.1} : Finset (Fin N))
                else if i = t.2.2.2 then {x t.2.1} else Finset.univ)).card := Finset.mul_sum _ _ _
      _ ≤ ∑ _t : Fin n × Fin n × Fin n × Fin n, N ^ n * N ^ n := by
          refine Finset.sum_le_sum fun t _ => ?_
          split_ifs with h
          · simp
          · calc N ^ 2 * ((Finset.univ : Finset (Fin n → Fin N)).biUnion fun x =>
                  ({x} : Finset (Fin n → Fin N)) ×ˢ Fintype.piFinset (fun i : Fin n =>
                    if i = t.2.2.1 then ({x t.1} : Finset (Fin N))
                    else if i = t.2.2.2 then {x t.2.1} else Finset.univ)).card
                ≤ N ^ 2 * ∑ x : Fin n → Fin N, (({x} : Finset (Fin n → Fin N)) ×ˢ
                    Fintype.piFinset (fun i : Fin n =>
                    if i = t.2.2.1 then ({x t.1} : Finset (Fin N))
                    else if i = t.2.2.2 then {x t.2.1} else Finset.univ)).card :=
                  Nat.mul_le_mul_left _ Finset.card_biUnion_le
              _ = ∑ _x : Fin n → Fin N, N ^ n := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun x _ => ?_
                  rw [Finset.card_product, Finset.card_singleton, one_mul]
                  exact hfib t.1 t.2.1 t.2.2.1 t.2.2.2 x h
              _ = N ^ n * N ^ n := by simp [Finset.sum_const, Finset.card_univ]
      _ = n ^ 4 * (N ^ n * N ^ n) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
          simp only [Fintype.card_prod, Fintype.card_fin]; ring
  have h1 : N ^ 2 * (twoPairs n N).card ≤ n ^ 4 * (N ^ n * N ^ n) :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans hcard
  have h2 : ((N ^ 2 * (twoPairs n N).card : ℕ) : ℝ) ≤ ((n ^ 4 * (N ^ n * N ^ n) : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  linarith only [h2, show ((N : ℝ) ^ n) ^ 2 = (N : ℝ) ^ n * (N : ℝ) ^ n by ring]

/-- **Maps with a small image**: `#{x : Fin m → Fin N | #image x ≤ k} ≤ m^m N^k`. -/
theorem image_card_count (m N k : ℕ) (hN : 0 < N) :
    ((Finset.univ.filter fun x : Fin m → Fin N => (Finset.univ.image x).card ≤ k).card : ℝ)
      ≤ (m : ℝ) ^ m * (N : ℝ) ^ k := by
  classical
  obtain ⟨rep, hrep⟩ : ∃ rep : (Fin m → Fin N) → Fin m → Fin m, rep = fun (x : Fin m → Fin N) (i : Fin m) =>
      (Finset.univ.filter fun j => x j = x i).min' ⟨i, by simp⟩ := ⟨_, rfl⟩
  have rep_spec : ∀ (x : Fin m → Fin N) (i : Fin m), x (rep x i) = x i := by
    intro x i
    have h := Finset.min'_mem (Finset.univ.filter fun j => x j = x i) ⟨i, by simp⟩
    rw [hrep]; exact (Finset.mem_filter.mp h).2
  have rep_le : ∀ (x : Fin m → Fin N) (i j : Fin m), x j = x i → rep x i ≤ j := by
    intro x i j h; rw [hrep]; exact Finset.min'_le _ _ (by simp [h])
  have rep_eq : ∀ (x : Fin m → Fin N) (i j : Fin m), x i = x j → rep x i = rep x j := by
    intro x i j h
    apply le_antisymm
    · exact rep_le x i _ (by rw [rep_spec x j]; exact h.symm)
    · exact rep_le x j _ (by rw [rep_spec x i]; exact h)
  have rep_rep : ∀ (x : Fin m → Fin N) (i : Fin m), rep x (rep x i) = rep x i := fun x i => rep_eq x _ _ (rep_spec x i)
  obtain ⟨z0⟩ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨enc, henc⟩ : ∃ enc : (Fin m → Fin N) → (Fin m → Fin m) × (Fin m → Fin N),
      enc = fun x => (rep x, fun i => if rep x i = i then x i else z0) := ⟨_, rfl⟩
  have enc_inj : Function.Injective enc := by
    intro x y hxy
    rw [henc] at hxy
    have h1 : rep x = rep y := congrArg Prod.fst hxy
    have h2 := congrArg Prod.snd hxy
    funext i
    have h3 := congrFun h2 (rep x i)
    simp only at h3
    rw [← h1, if_pos (rep_rep x i), if_pos (rep_rep x i)] at h3
    rw [← rep_spec x i, h3, h1, rep_spec y i]
  obtain ⟨T, hT⟩ : ∃ T : Finset ((Fin m → Fin m) × (Fin m → Fin N)), T =
      (Finset.univ.filter fun g : Fin m → Fin m =>
        (Finset.univ.filter fun i => g i = i).card ≤ k).biUnion
        fun g => ({g} : Finset (Fin m → Fin m)) ×ˢ Fintype.piFinset (fun i =>
          if g i = i then (Finset.univ : Finset (Fin N)) else {z0}) := ⟨_, rfl⟩
  have hmaps : ∀ x ∈ (Finset.univ.filter fun x : Fin m → Fin N =>
      (Finset.univ.image x).card ≤ k), enc x ∈ T := by
    intro x hx
    have hk := (Finset.mem_filter.mp hx).2
    rw [hT, henc]
    refine Finset.mem_biUnion.mpr ⟨rep x, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, le_trans ?_ hk⟩
      refine Finset.card_le_card_of_injOn x
        (fun i _ => Finset.mem_image_of_mem x (Finset.mem_univ i)) ?_
      intro i hi j hj hij
      have hi' : rep x i = i := (Finset.mem_filter.mp hi).2
      have hj' : rep x j = j := (Finset.mem_filter.mp hj).2
      rw [← hi', ← hj']; exact rep_eq x i j hij
    · refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, ?_⟩
      rw [Fintype.mem_piFinset]; intro i
      by_cases h : rep x i = i
      · simp [h]
      · simp [h]
  have hle := Finset.card_le_card_of_injOn enc hmaps enc_inj.injOn
  have h2 : ∀ g ∈ (Finset.univ.filter fun g : Fin m → Fin m =>
      (Finset.univ.filter fun i => g i = i).card ≤ k),
      (({g} : Finset (Fin m → Fin m)) ×ˢ Fintype.piFinset (fun i =>
          if g i = i then (Finset.univ : Finset (Fin N)) else {z0})).card ≤ N ^ k := by
    intro g hg
    rw [Finset.card_product, Finset.card_singleton, one_mul, Fintype.card_piFinset]
    have e : ∀ i, (if g i = i then (Finset.univ : Finset (Fin N)) else {z0}).card
        = if g i = i then N else 1 := by
      intro i; split_ifs <;> simp
    simp_rw [e]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
    exact Nat.pow_le_pow_right hN (Finset.mem_filter.mp hg).2
  have hTn : T.card ≤ m ^ m * N ^ k := by
    rw [hT]
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum fun g hg => h2 g hg).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    refine Nat.mul_le_mul_right _ ?_
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have h3 : ((Finset.univ.filter fun x : Fin m → Fin N =>
      (Finset.univ.image x).card ≤ k).card : ℝ) ≤ ((m ^ m * N ^ k : ℕ) : ℝ) := by
    exact_mod_cast hle.trans hTn
  push_cast at h3
  exact h3

/-- The maps of `n + 1` points with at most `n - 1` image points: `N² · # ≤ (n+1)^{n+1} N^{n+1}`. -/
theorem low_image_count (n N : ℕ) (hN : 0 < N) :
    (N : ℝ) ^ 2 * ((Finset.univ.filter fun x : Fin (n + 1) → Fin N =>
        (Finset.univ.image x).card ≤ n - 1).card : ℝ)
      ≤ ((n : ℝ) + 1) ^ (n + 1) * (N : ℝ) ^ (n + 1) := by
  rcases n with _ | n
  · have e : (Finset.univ.filter fun x : Fin (0 + 1) → Fin N =>
        (Finset.univ.image x).card ≤ 0 - 1) = ∅ := by
      apply Finset.filter_false_of_mem
      intro x _
      have : (Finset.univ.image x).Nonempty := Finset.univ_nonempty.image x
      exact Nat.not_le.mpr (Finset.card_pos.mpr this)
    rw [e, Finset.card_empty]
    simp
  · have h := image_card_count (n + 1 + 1) N n hN
    have e : n + 1 - 1 = n := by omega
    rw [e]
    have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left h hN2
    have e2 : (N : ℝ) ^ 2 * (((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1 + 1) * (N : ℝ) ^ n)
        = (((n + 1 : ℕ) : ℝ) + 1) ^ (n + 1 + 1) * (N : ℝ) ^ (n + 1 + 1) := by
      push_cast; ring
    linarith only [h4, e2]

end Count

section MainA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*}
  [MeasurableSpace G] {ν : Measure G} {X : ℕ → Ω → G}

theorem image_val_card {n N : ℕ} (ι : Fin n → Fin N) :
    (Finset.univ.image fun m => (ι m : ℕ)).card = (Finset.univ.image ι).card := by
  have e : (Finset.univ.image fun m => (ι m : ℕ)) = (Finset.univ.image ι).image Fin.val := by
    rw [Finset.image_image]; rfl
  rw [e, Finset.card_image_of_injective _ Fin.val_injective]

/-- **Lemma `lem:degenerate`(a) for `n + 1` indices, abstract form.** HYPOTHESES as in the
    section header: independent sample with law `ν`; `F` bounded (`|F| ≤ B`) and measurable;
    degenerate in the last argument (`hdeg`); conditional mean given the last point zero
    (`hcond`); `V`, `ρ` upper bounds for `‖F‖₂²`, `ϱ(F)` in sample form.  For `N ≥ 1`:
    `E |N^{-(n+1)} ∑_{ι : Fin (n+1) → Fin N} F(X_ι)|
       ≤ (n+1)² √V / N + (n+1)² ρ / N + (n+1)^{n+1} B / N²`. -/
theorem degenerate_a_general [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) (hF : BM F) {B V ρ : ℝ}
    (hB : ∀ x, |F x| ≤ B) (hρ0 : 0 ≤ ρ)
    (hdeg : ∀ x, ∫ z, F (Function.update x (Fin.last n) z) ∂ν = 0)
    (hcond : ∀ x, AW ν (Finset.univ.erase (Fin.last n)) F x = 0)
    (hV : ∀ ι : Fin (n + 1) → ℕ, Function.Injective ι →
      ∫ ω, F (fun m => X (ι m) ω) ^ 2 ∂μ ≤ V)
    (hρ : ∀ ι : Fin (n + 1) → ℕ, (Finset.univ.image ι).card = n →
      ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ρ)
    (N : ℕ) (hN : 0 < N) :
    ∫ ω, |1 / (N : ℝ) ^ (n + 1) * sAll X N F ω| ∂μ
      ≤ ((n : ℝ) + 1) ^ 2 * Real.sqrt V / N + ((n : ℝ) + 1) ^ 2 * ρ / N
        + ((n : ℝ) + 1) ^ (n + 1) * B / (N : ℝ) ^ 2 := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => X 0 ω0))
  have hV0 : 0 ≤ V := (integral_nonneg fun ω => _root_.sq_nonneg _).trans
    (hV (fun m => (m : ℕ)) (fun a b h => Fin.ext h))
  have bm : ∀ ι : Fin (n + 1) → Fin N, BM (fun ω => F (fun m => X (ι m) ω)) := fun ι =>
    H.bmι hF ι
  -- the injective part
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin (n + 1) → Fin N),
      I = Finset.univ.filter fun ι : Fin (n + 1) → Fin N => Function.Injective ι := ⟨_, rfl⟩
  have hzero : ∀ ι ∈ I, ∀ ι' ∈ I, (ι, ι') ∉ twoPairs (n + 1) N →
      ∫ ω, F (fun m => X (ι m) ω) * F (fun m => X (ι' m) ω) ∂μ = 0 := by
    intro ι hι ι' _ hP
    rw [hI] at hι
    have hinj : Function.Injective ι := (Finset.mem_filter.mp hι).2
    have hinjN : Function.Injective fun m => (ι m : ℕ) := fun a b h => hinj (Fin.ext h)
    by_cases hlast : ∃ a', ι' a' = ι (Fin.last n)
    · -- the last point is common; then it is the only common point
      have hcom : ∀ v m, v ≠ Fin.last n → (ι' m : ℕ) ≠ (ι v : ℕ) := by
        intro v m hv h
        obtain ⟨a', ha'⟩ := hlast
        apply hP
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj, Fin.last n, v, a', m,
          fun h' => hv h'.symm, ha', Fin.ext h⟩
      rw [int_set H (fun m => (ι m : ℕ)) (fun m => (ι' m : ℕ)) F F hF hF
        (Finset.univ.erase (Fin.last n))
        (fun v hv => ⟨fun m hm h => hm (hinjN h), fun m => hcom v m (Finset.ne_of_mem_erase hv)⟩)]
      simp [hcond]
    · push Not at hlast
      exact H.pair_vanish (fun m => (ι m : ℕ)) (fun m => (ι' m : ℕ)) (Fin.last n)
        (fun m hm h => hm (hinjN h)) (fun m h => hlast m (Fin.ext h)) F F hF hF hdeg
  have hpair : ∀ ι ∈ I, ∀ ι' ∈ I,
      ∫ ω, F (fun m => X (ι m) ω) * F (fun m => X (ι' m) ω) ∂μ ≤ V := by
    intro ι hι ι' hι'
    rw [hI] at hι hι'
    have v1 := hV (fun m => (ι m : ℕ)) (fun a b h => (Finset.mem_filter.mp hι).2 (Fin.ext h))
    have v2 := hV (fun m => (ι' m : ℕ)) (fun a b h => (Finset.mem_filter.mp hι').2 (Fin.ext h))
    have i1 : Integrable (fun ω => F (fun m => X (ι m) ω) ^ 2) μ := (bm ι).sqr.integrable
    have i2 : Integrable (fun ω => F (fun m => X (ι' m) ω) ^ 2) μ := (bm ι').sqr.integrable
    have i3 := ((bm ι).mul (bm ι')).integrable (μ := μ)
    calc ∫ ω, F (fun m => X (ι m) ω) * F (fun m => X (ι' m) ω) ∂μ
        ≤ ∫ ω, (1 / 2 * F (fun m => X (ι m) ω) ^ 2 + 1 / 2 * F (fun m => X (ι' m) ω) ^ 2) ∂μ :=
          integral_mono i3 ((i1.const_mul _).add (i2.const_mul _)) (fun ω => by
            nlinarith [_root_.sq_nonneg (F (fun m => X (ι m) ω) - F (fun m => X (ι' m) ω))])
      _ = 1 / 2 * ∫ ω, F (fun m => X (ι m) ω) ^ 2 ∂μ
            + 1 / 2 * ∫ ω, F (fun m => X (ι' m) ω) ^ 2 ∂μ := by
          rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
      _ ≤ V := by linarith
  have hsq := sm_le_V H I F hF hV0 (twoPairs (n + 1) N) hzero hpair
  have hcard := twoPairs_card (n + 1) N
  have hc2 : ((twoPairs (n + 1) N).card : ℝ) ≤ ((n : ℝ) + 1) ^ 4 * ((N : ℝ) ^ n) ^ 2 := by
    have e : ((N : ℝ) ^ (n + 1)) ^ 2 = (N : ℝ) ^ 2 * ((N : ℝ) ^ n) ^ 2 := by ring
    push_cast at hcard
    rw [e] at hcard
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    nlinarith
  have hInjSq : ∫ ω, sInj X N F ω ^ 2 ∂μ ≤ ((n : ℝ) + 1) ^ 4 * ((N : ℝ) ^ n) ^ 2 * V := by
    have e : (fun ω => sInj X N F ω ^ 2)
        = fun ω => (∑ ι ∈ I, F (fun m => X (ι m) ω)) ^ 2 := by
      funext ω; unfold sInj; rw [hI]
    rw [e]
    exact hsq.trans (mul_le_mul_of_nonneg_right hc2 hV0)
  have hInj : ∫ ω, |sInj X N F ω| ∂μ ≤ ((n : ℝ) + 1) ^ 2 * (N : ℝ) ^ n * Real.sqrt V := by
    refine ((H.sInj_bm N hF).abs_le_sqrt hInjSq).trans (le_of_eq ?_)
    have e : ((n : ℝ) + 1) ^ 4 * ((N : ℝ) ^ n) ^ 2 * V
        = (((n : ℝ) + 1) ^ 2 * (N : ℝ) ^ n) ^ 2 * V := by ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  -- the non-injective part
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin (n + 1) → Fin N),
      J = Finset.univ.filter fun ι : Fin (n + 1) → Fin N => ¬ Function.Injective ι := ⟨_, rfl⟩
  have hterm : ∀ ι ∈ J, ∫ ω, |F (fun m => X (ι m) ω)| ∂μ
      ≤ ρ * (if Function.Injective ι then (0 : ℝ) else 1)
        + B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0) := by
    intro ι hι
    rw [hJ] at hι
    have hni : ¬ Function.Injective ι := (Finset.mem_filter.mp hι).2
    rw [if_neg hni, mul_one]
    have hlt : (Finset.univ.image ι).card ≤ n := by
      have h1 : (Finset.univ.image ι).card ≤ n + 1 := by
        have := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n + 1)))) (f := ι)
        simpa using this
      have h2 : (Finset.univ.image ι).card ≠ n + 1 := by
        intro h
        apply hni
        have h3 : (Finset.univ.image ι).card = (Finset.univ : Finset (Fin (n + 1))).card := by
          simpa using h
        have := Finset.card_image_iff.mp h3
        intro a b hab
        exact this (Finset.mem_coe.mpr (Finset.mem_univ a))
          (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
      omega
    by_cases hc : (Finset.univ.image ι).card = n
    · have h := hρ (fun m => (ι m : ℕ)) (by rw [image_val_card]; exact hc)
      have : 0 ≤ B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0) := by
        split_ifs <;> simp [hB0]
      linarith
    · have hc' : (Finset.univ.image ι).card ≤ n - 1 := by omega
      rw [if_pos hc', mul_one]
      have hle : ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ B := by
        calc ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ∫ _ω, B ∂μ :=
              integral_mono (bm ι).absv.integrable (integrable_const _) (fun ω => hB _)
          _ = B := by simp
      linarith
  have hNon : ∫ ω, ∑ ι ∈ J, |F (fun m => X (ι m) ω)| ∂μ
      ≤ ρ * ∑ ι : Fin (n + 1) → Fin N, (if Function.Injective ι then (0 : ℝ) else 1)
        + B * ((Finset.univ.filter fun x : Fin (n + 1) → Fin N =>
            (Finset.univ.image x).card ≤ n - 1).card : ℝ) := by
    rw [integral_finset_sum _ fun ι _ => (bm ι).absv.integrable]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hs1 : ∑ ι ∈ J, (if Function.Injective ι then (0 : ℝ) else 1)
        ≤ ∑ ι : Fin (n + 1) → Fin N, (if Function.Injective ι then (0 : ℝ) else 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by split_ifs <;> norm_num)
    have hs2 : ∑ ι ∈ J, (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0)
        ≤ ((Finset.univ.filter fun x : Fin (n + 1) → Fin N =>
            (Finset.univ.image x).card ≤ n - 1).card : ℝ) := by
      rw [Finset.card_filter]; push_cast
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => by split_ifs <;> norm_num)
    have := mul_le_mul_of_nonneg_left hs1 hρ0
    have := mul_le_mul_of_nonneg_left hs2 hB0
    linarith
  -- assembling
  have bJ : BM (fun ω => ∑ ι ∈ J, |F (fun m => X (ι m) ω)|) :=
    BM.sum _ _ fun ι _ => (bm ι).absv
  have hpt : ∀ ω, |sAll X N F ω| ≤ |sInj X N F ω| + ∑ ι ∈ J, |F (fun m => X (ι m) ω)| := by
    intro ω
    rw [sAll_split]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    unfold sNon; rw [hJ]
    exact Finset.abs_sum_le_sum_abs _ _
  have hAll : ∫ ω, |sAll X N F ω| ∂μ
      ≤ ((n : ℝ) + 1) ^ 2 * (N : ℝ) ^ n * Real.sqrt V
        + (ρ * ∑ ι : Fin (n + 1) → Fin N, (if Function.Injective ι then (0 : ℝ) else 1)
        + B * ((Finset.univ.filter fun x : Fin (n + 1) → Fin N =>
            (Finset.univ.image x).card ≤ n - 1).card : ℝ)) := by
    have hmono := integral_mono_of_nonneg (μ := μ)
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)
      ((H.sInj_bm N hF).absv.add bJ).integrable (Filter.Eventually.of_forall hpt)
    refine hmono.trans ?_
    rw [integral_add (H.sInj_bm N hF).absv.integrable bJ.integrable]
    linarith
  -- counts
  have hc1 := BiasVariance3.noninj_count (n + 1) N
  have hc3 := low_image_count n N hN
  obtain ⟨s1, hs1⟩ : ∃ s1 : ℝ, s1 = ∑ ι : Fin (n + 1) → Fin N,
      (if Function.Injective ι then (0 : ℝ) else 1) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2 : ℝ, s2 = ((Finset.univ.filter fun x : Fin (n + 1) → Fin N =>
      (Finset.univ.image x).card ≤ n - 1).card : ℝ) := ⟨_, rfl⟩
  rw [← hs1, ← hs2] at hAll
  rw [← hs1] at hc1
  rw [← hs2] at hc3
  push_cast at hc1
  -- normalise
  have e : ∀ ω, |1 / (N : ℝ) ^ (n + 1) * sAll X N F ω|
      = 1 / (N : ℝ) ^ (n + 1) * |sAll X N F ω| := fun ω => by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (n + 1))]
  simp_rw [e]
  rw [integral_const_mul]
  have hq : 0 < (N : ℝ) ^ (n + 1) := by positivity
  have h1 : 1 / (N : ℝ) ^ (n + 1) * (((n : ℝ) + 1) ^ 2 * (N : ℝ) ^ n * Real.sqrt V)
      = ((n : ℝ) + 1) ^ 2 * Real.sqrt V / N := by
    field_simp; ring
  have h2 : 1 / (N : ℝ) ^ (n + 1) * (ρ * s1) ≤ ((n : ℝ) + 1) ^ 2 * ρ / N := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hq hNpos]
    have := mul_le_mul_of_nonneg_left hc1 hρ0
    nlinarith
  have h3 : 1 / (N : ℝ) ^ (n + 1) * (B * s2) ≤ ((n : ℝ) + 1) ^ (n + 1) * B / (N : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hq (by positivity)]
    have := mul_le_mul_of_nonneg_left hc3 hB0
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left hAll (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (n + 1))
  have e2 : 1 / (N : ℝ) ^ (n + 1) * (((n : ℝ) + 1) ^ 2 * (N : ℝ) ^ n * Real.sqrt V
        + (ρ * s1 + B * s2))
      = 1 / (N : ℝ) ^ (n + 1) * (((n : ℝ) + 1) ^ 2 * (N : ℝ) ^ n * Real.sqrt V)
        + 1 / (N : ℝ) ^ (n + 1) * (ρ * s1) + 1 / (N : ℝ) ^ (n + 1) * (B * s2) := by ring
  rw [e2] at h4
  linarith

end MainA

section TorusA

variable {G : Type*} [MeasurableSpace G] {ν : Measure G}

theorem Alist_zero {n : ℕ} (l : List (Fin n)) :
    Alist ν l (fun _ => (0 : ℝ)) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons v l ih => rw [Alist_cons, ih]; funext x; simp [Av]

theorem AW_zero {n : ℕ} (W : Finset (Fin n)) : AW ν W (fun _ => (0 : ℝ)) = fun _ => 0 :=
  Alist_zero _

/-- Integrating out `v` commutes with integrating out a set `W ∌ v`. -/
theorem Av_AW_comm [IsProbabilityMeasure ν] {n : ℕ} (v : Fin n) (W : Finset (Fin n))
    (hv : v ∉ W) {F : (Fin n → G) → ℝ} (hF : BM F) :
    Av ν v (AW ν W F) = AW ν W (Av ν v F) := by
  induction W using Finset.induction_on with
  | empty => rw [AW_empty, AW_empty]
  | insert w W hw ih =>
    have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self w W)
    have hvW : v ∉ W := fun h => hv (Finset.mem_insert_of_mem h)
    rw [AW_insert hw hF, AW_insert hw (Av_bm v hF), Av_comm v w (AW_bm W hF), ih hvW]

/-- **The conditional mean given the last point vanishes** for a translation-invariant kernel that
    is degenerate in its last argument (`ν` translation invariant). -/
theorem cond_of_TI {G : Type*} [AddCommGroup G] [MeasurableSpace G] {ν : Measure G}
    [IsProbabilityMeasure ν]
    (hinv : ∀ f : G → ℝ, Measurable f → ∀ c, ∫ z, f (z + c) ∂ν = ∫ z, f z ∂ν)
    {n : ℕ} {F : (Fin (n + 1) → G) → ℝ} (hF : BM F) (hT : TI F)
    (hdeg : ∀ x, ∫ z, F (Function.update x (Fin.last n) z) ∂ν = 0) (x : Fin (n + 1) → G) :
    AW ν (Finset.univ.erase (Fin.last n)) F x = 0 := by
  have h1 := AW_le1_const hinv hF hT (S := {Fin.last n}) (by simp) x
  rw [Finset.compl_singleton] at h1
  rw [h1]
  have hu : (Finset.univ : Finset (Fin (n + 1))) = insert (Fin.last n) (Finset.univ.erase (Fin.last n)) :=
    (Finset.insert_erase (Finset.mem_univ _)).symm
  have hA : Av ν (Fin.last n) F = fun _ => 0 := funext fun y => hdeg y
  rw [hu, AW_insert (Finset.notMem_erase _ _) hF,
    Av_AW_comm (Fin.last n) _ (Finset.notMem_erase _ _) hF, hA, AW_zero]

end TorusA

/-- **Lemma `lem:degenerate`(a) for `n + 1` indices on the flat torus.** Independent uniform points
    `X_j` on `FlatTorus d`; `F` measurable, `|F| ≤ B`, invariant under simultaneous translations,
    with `∫ F(y₁,…,y_n, z) dz = 0`; `V ≥ ‖F‖₂²` (injective index maps) and `ρ ≥ ϱ(F)` (index maps
    identifying exactly one pair of positions) in sample form, `ρ ≥ 0`.  For `N ≥ 1`:
    `E |N^{-(n+1)} ∑_ι F(X_ι)| ≤ (n+1)² √V / N + (n+1)² ρ / N + (n+1)^{n+1} B / N²`,
    i.e. part (a) of the lemma with `C_{n+1} = (n+1)^{n+1}` (`(n+1)²` for the first two terms). -/
theorem degenerate_a_general_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {n : ℕ} (F : (Fin (n + 1) → FlatTorus d) → ℝ) (hFm : Measurable F) {B V ρ : ℝ}
    (hB : ∀ x, |F x| ≤ B) (hT : TI F) (hρ0 : 0 ≤ ρ)
    (hdeg : ∀ x, ∫ z, F (Function.update x (Fin.last n) z) ∂flatTorusMeasure d = 0)
    (hV : ∀ ι : Fin (n + 1) → ℕ, Function.Injective ι →
      ∫ ω, F (fun m => X (ι m) ω) ^ 2 ∂μ ≤ V)
    (hρ : ∀ ι : Fin (n + 1) → ℕ, (Finset.univ.image ι).card = n →
      ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ρ)
    (N : ℕ) (hN : 0 < N) :
    ∫ ω, |1 / (N : ℝ) ^ (n + 1) * sAll X N F ω| ∂μ
      ≤ ((n : ℝ) + 1) ^ 2 * Real.sqrt V / N + ((n : ℝ) + 1) ^ 2 * ρ / N
        + ((n : ℝ) + 1) ^ (n + 1) * B / (N : ℝ) ^ 2 := by
  have hF : BM F := ⟨hFm, B, hB⟩
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  exact degenerate_a_general H F hF hB hρ0 hdeg
    (cond_of_TI (torus_hinv d) hF hT hdeg) hV hρ N hN



open PiBound VarianceOne VarianceGeneral2

/-! ## Part (b) of `lem:degenerate` for `n + 1` indices

`Z¹ = N^{-(n+2)} ∑_{ι, v} F(x_ι) c(x_{ι(a)} - x_v)` is the statistic of the kernel
`F̃(y) = F(y₀,…,y_n) c(y_a - y_{n+1})` of `n + 2` points (`Ft`), which is degenerate in its last
argument.  The products of two injective summands vanish unless the images have two common
elements (`pair_zero`); with exactly two common elements they are at most `M² L²`
(`Ft_pair_two`), with three or more at most `M V` (`Ft_sq_le`); the non-injective summands are
bounded one by one (`Ft_noninj_le`). -/

section Count3

/-- The pairs of index maps whose first map is injective and whose images have at least three
    common elements. -/
def threePairs (n N : ℕ) : Finset ((Fin n → Fin N) × (Fin n → Fin N)) :=
  Finset.univ.filter fun q => Function.Injective q.1 ∧
    ∃ a b c a' b' c', a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ q.2 a' = q.1 a ∧ q.2 b' = q.1 b ∧ q.2 c' = q.1 c

/-- `N³ · #threePairs ≤ n⁶ N^{2n}`. -/
theorem threePairs_card (n N : ℕ) :
    (N : ℝ) ^ 3 * ((threePairs n N).card : ℝ) ≤ (n : ℝ) ^ 6 * ((N : ℝ) ^ n) ^ 2 := by
  classical
  have hfib : ∀ (a b c a' b' c' : Fin n) (x : Fin n → Fin N), a' ≠ b' → a' ≠ c' → b' ≠ c' →
      N ^ 3 * (Fintype.piFinset (fun i : Fin n => if i = a' then ({x a} : Finset (Fin N))
        else if i = b' then {x b} else if i = c' then {x c} else Finset.univ)).card = N ^ n := by
    intro a b c a' b' c' x hab hac hbc
    rw [Fintype.card_piFinset]
    have e : ∀ i : Fin n, (if i = a' then ({x a} : Finset (Fin N))
        else if i = b' then {x b} else if i = c' then {x c} else Finset.univ).card
        = if i ∈ ({a', b', c'} : Finset (Fin n)) then 1 else N := by
      intro i
      by_cases h1 : i = a'
      · subst h1; simp
      · by_cases h2 : i = b'
        · subst h2; simp [h1]
        · by_cases h3 : i = c'
          · subst h3; simp [h1, h2]
          · simp [h1, h2, h3]
    simp_rw [e]
    have hcard : ({a', b', c'} : Finset (Fin n)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
    rw [prod_ite_mem n {a', b', c'} 1 N, hcard, one_pow, one_mul, ← pow_add]
    have hn3 : 3 ≤ n := by
      have := Finset.card_le_univ ({a', b', c'} : Finset (Fin n))
      rw [hcard, Fintype.card_fin] at this; exact this
    congr 1; omega
  obtain ⟨Cov, hCov⟩ : ∃ Cov : Finset ((Fin n → Fin N) × (Fin n → Fin N)), Cov =
      (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n × Fin n × Fin n)).biUnion fun t =>
        if t.2.2.2.1 = t.2.2.2.2.1 ∨ t.2.2.2.1 = t.2.2.2.2.2 ∨ t.2.2.2.2.1 = t.2.2.2.2.2 then ∅
        else (Finset.univ : Finset (Fin n → Fin N)).biUnion fun x =>
            ({x} : Finset (Fin n → Fin N)) ×ˢ Fintype.piFinset (fun i : Fin n =>
              if i = t.2.2.2.1 then ({x t.1} : Finset (Fin N))
              else if i = t.2.2.2.2.1 then {x t.2.1}
              else if i = t.2.2.2.2.2 then {x t.2.2.1} else Finset.univ) := ⟨_, rfl⟩
  have hsub : threePairs n N ⊆ Cov := by
    intro q hq
    obtain ⟨hinj, a, b, c, a', b', c', hab, hac, hbc, h1, h2, h3⟩ := (Finset.mem_filter.mp hq).2
    have hab' : a' ≠ b' := by intro h; apply hab; apply hinj; rw [← h1, ← h2, h]
    have hac' : a' ≠ c' := by intro h; apply hac; apply hinj; rw [← h1, ← h3, h]
    have hbc' : b' ≠ c' := by intro h; apply hbc; apply hinj; rw [← h2, ← h3, h]
    rw [hCov]
    refine Finset.mem_biUnion.mpr ⟨(a, b, c, a', b', c'), Finset.mem_univ _, ?_⟩
    simp only
    rw [if_neg (by tauto)]
    refine Finset.mem_biUnion.mpr ⟨q.1, Finset.mem_univ _, ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    by_cases e1 : i = a'
    · subst e1; simp [h1]
    · by_cases e2 : i = b'
      · subst e2; simp [e1, h2]
      · by_cases e3 : i = c'
        · subst e3; simp [e1, e2, h3]
        · simp [e1, e2, e3]
  have hcard : N ^ 3 * Cov.card ≤ n ^ 6 * (N ^ n * N ^ n) := by
    rw [hCov]
    refine (Nat.mul_le_mul_left _ Finset.card_biUnion_le).trans ?_
    rw [Finset.mul_sum]
    calc ∑ t : Fin n × Fin n × Fin n × Fin n × Fin n × Fin n, N ^ 3 * (if t.2.2.2.1 = t.2.2.2.2.1
          ∨ t.2.2.2.1 = t.2.2.2.2.2 ∨ t.2.2.2.2.1 = t.2.2.2.2.2 then ∅
          else (Finset.univ : Finset (Fin n → Fin N)).biUnion fun x =>
            ({x} : Finset (Fin n → Fin N)) ×ˢ Fintype.piFinset (fun i : Fin n =>
              if i = t.2.2.2.1 then ({x t.1} : Finset (Fin N))
              else if i = t.2.2.2.2.1 then {x t.2.1}
              else if i = t.2.2.2.2.2 then {x t.2.2.1} else Finset.univ)).card
        ≤ ∑ _t : Fin n × Fin n × Fin n × Fin n × Fin n × Fin n, N ^ n * N ^ n := by
          refine Finset.sum_le_sum fun t _ => ?_
          split_ifs with h
          · simp
          · push Not at h
            refine (Nat.mul_le_mul_left _ Finset.card_biUnion_le).trans ?_
            rw [Finset.mul_sum]
            calc ∑ x : Fin n → Fin N, N ^ 3 * (({x} : Finset (Fin n → Fin N)) ×ˢ
                  Fintype.piFinset (fun i : Fin n =>
                  if i = t.2.2.2.1 then ({x t.1} : Finset (Fin N))
                  else if i = t.2.2.2.2.1 then {x t.2.1}
                  else if i = t.2.2.2.2.2 then {x t.2.2.1} else Finset.univ)).card
                = ∑ _x : Fin n → Fin N, N ^ n := by
                  refine Finset.sum_congr rfl fun x _ => ?_
                  rw [Finset.card_product, Finset.card_singleton, one_mul]
                  exact hfib _ _ _ _ _ _ x h.1 h.2.1 h.2.2
              _ = N ^ n * N ^ n := by simp [Finset.sum_const, Finset.card_univ]
              _ ≤ N ^ n * N ^ n := le_rfl
      _ = n ^ 6 * (N ^ n * N ^ n) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
          simp only [Fintype.card_prod, Fintype.card_fin]; ring
  have h1 : N ^ 3 * (threePairs n N).card ≤ n ^ 6 * (N ^ n * N ^ n) :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans hcard
  have h2 : ((N ^ 3 * (threePairs n N).card : ℕ) : ℝ) ≤ ((n ^ 6 * (N ^ n * N ^ n) : ℕ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  linarith only [h2, show ((N : ℝ) ^ n) ^ 2 = (N : ℝ) ^ n * (N : ℝ) ^ n by ring]

end Count3

section PartB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*}
  [MeasurableSpace G] {ν : Measure G} {X : ℕ → Ω → G}

/-- `pair_zero`: products of two injective summands whose images have at most one common element
    vanish (for a kernel degenerate in the last argument with vanishing conditional mean given the
    last point). -/
theorem pair_zero [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n N : ℕ} (F : (Fin (n + 1) → G) → ℝ) (hF : BM F)
    (hdeg : ∀ x, ∫ z, F (Function.update x (Fin.last n) z) ∂ν = 0)
    (hcond : ∀ x, AW ν (Finset.univ.erase (Fin.last n)) F x = 0)
    (ι ι' : Fin (n + 1) → Fin N) (hinj : Function.Injective ι)
    (hP : (ι, ι') ∉ twoPairs (n + 1) N) :
    ∫ ω, F (fun m => X (ι m) ω) * F (fun m => X (ι' m) ω) ∂μ = 0 := by
  have hinjN : Function.Injective fun m => (ι m : ℕ) := fun a b h => hinj (Fin.ext h)
  by_cases hlast : ∃ a', ι' a' = ι (Fin.last n)
  · have hcom : ∀ v m, v ≠ Fin.last n → (ι' m : ℕ) ≠ (ι v : ℕ) := by
      intro v m hv h
      obtain ⟨a', ha'⟩ := hlast
      apply hP
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj, Fin.last n, v, a', m,
        fun h' => hv h'.symm, ha', Fin.ext h⟩
    rw [int_set H (fun m => (ι m : ℕ)) (fun m => (ι' m : ℕ)) F F hF hF
      (Finset.univ.erase (Fin.last n))
      (fun v hv => ⟨fun m hm h => hm (hinjN h), fun m => hcom v m (Finset.ne_of_mem_erase hv)⟩)]
    simp [hcond]
  · push Not at hlast
    exact H.pair_vanish (fun m => (ι m : ℕ)) (fun m => (ι' m : ℕ)) (Fin.last n)
      (fun m hm h => hm (hinjN h)) (fun m h => hlast m (Fin.ext h)) F F hF hF hdeg

/-- `E |F(X_ι)| ≤ L` for an injective index map, if the conditional mean of `|F|` given one point
    is at most `L`. -/
theorem abs_le_L [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) (hF : BM F) {L : ℝ}
    (hcabs : ∀ w x, AW ν (Finset.univ.erase w) (fun y => |F y|) x ≤ L)
    (ι : Fin (n + 1) → ℕ) (hι : Function.Injective ι) :
    ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ L := by
  have h := int_set H ι (Fin.elim0 : Fin 0 → ℕ) (fun y => |F y|) (fun _ => (1 : ℝ)) hF.absv
    (BM.const 1) (Finset.univ.erase 0) (fun v _ => ⟨fun m hm h => hm (hι h), fun m => m.elim0⟩)
  simp only [mul_one] at h
  rw [h]
  have hb : BM (fun ω => AW ν (Finset.univ.erase 0) (fun y => |F y|) (fun m => X (ι m) ω)) :=
    H.bm ι (AW_bm _ hF.absv)
  calc ∫ ω, AW ν (Finset.univ.erase 0) (fun y => |F y|) (fun m => X (ι m) ω) ∂μ
      ≤ ∫ _ω, L ∂μ := integral_mono hb.integrable (integrable_const _) (fun ω => hcabs _ _)
    _ = L := by simp

/-- `E |F(X_ι)| |F(X_ι')| ≤ L²` if the images of the injective maps `ι`, `ι'` have at most one
    common element. -/
theorem abs_pair_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) (hF : BM F) {L : ℝ} (hL0 : 0 ≤ L)
    (hcabs : ∀ w x, AW ν (Finset.univ.erase w) (fun y => |F y|) x ≤ L)
    (ι ι' : Fin (n + 1) → ℕ) (hι : Function.Injective ι) (hι' : Function.Injective ι')
    (hone : ∀ b b' m m', ι b = ι' m → ι b' = ι' m' → b = b') :
    ∫ ω, |F (fun m => X (ι m) ω)| * |F (fun m => X (ι' m) ω)| ∂μ ≤ L * L := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Fin (n + 1), ∀ v, v ≠ b → ∀ m, ι' m ≠ ι v := by
    by_cases hex : ∃ b m, ι b = ι' m
    · obtain ⟨b, m0, hb⟩ := hex
      exact ⟨b, fun v hv m h => hv (hone v b m m0 h.symm hb)⟩
    · push Not at hex
      exact ⟨0, fun v _ m h => hex v m h.symm⟩
  have h := int_set H ι ι' (fun y => |F y|) (fun y => |F y|) hF.absv hF.absv
    (Finset.univ.erase b) (fun v hv => ⟨fun m hm h => hm (hι h),
      fun m => hb v (Finset.ne_of_mem_erase hv) m⟩)
  rw [h]
  have hb1 : BM (fun ω => AW ν (Finset.univ.erase b) (fun y => |F y|) (fun m => X (ι m) ω)) :=
    H.bm ι (AW_bm _ hF.absv)
  have hb2 : BM (fun ω => |F (fun m => X (ι' m) ω)|) := (H.bm ι' hF).absv
  calc ∫ ω, AW ν (Finset.univ.erase b) (fun y => |F y|) (fun m => X (ι m) ω)
        * |F (fun m => X (ι' m) ω)| ∂μ
      ≤ ∫ ω, L * |F (fun m => X (ι' m) ω)| ∂μ :=
        integral_mono (hb1.mul hb2).integrable (hb2.const_mul L).integrable
          (fun ω => mul_le_mul_of_nonneg_right (hcabs _ _) (abs_nonneg _))
    _ = L * ∫ ω, |F (fun m => X (ι' m) ω)| ∂μ := integral_const_mul _ _
    _ ≤ L * L := mul_le_mul_of_nonneg_left (abs_le_L H F hF hcabs ι' hι') hL0

/-- **Second moment with two classes of non-vanishing products.** -/
theorem sm_le_two [IsProbabilityMeasure μ]
    (H : SP μ ν X) {n N : ℕ} (I : Finset (Fin n → Fin N)) (F : (Fin n → G) → ℝ) (hF : BM F)
    {A C : ℝ} (hA0 : 0 ≤ A) (hC0 : 0 ≤ C) (P Q : Finset ((Fin n → Fin N) × (Fin n → Fin N)))
    (hb : ∀ ι ∈ I, ∀ ι' ∈ I, ∫ ω, F (fun m => X (ι m) ω) * F (fun m => X (ι' m) ω) ∂μ
      ≤ (if (ι, ι') ∈ P then A else 0) + (if (ι, ι') ∈ Q then C else 0)) :
    ∫ ω, (∑ ι ∈ I, F (fun m => X (ι m) ω)) ^ 2 ∂μ ≤ P.card * A + Q.card * C := by
  classical
  have bm : ∀ ι : Fin n → Fin N, BM (fun ω => F (fun m => X (ι m) ω)) := fun ι =>
    H.bm (fun m => (ι m : ℕ)) hF
  have e : ∀ ω, (∑ ι ∈ I, F (fun m => X (ι m) ω)) ^ 2
      = ∑ q ∈ I ×ˢ I, F (fun m => X (q.1 m) ω) * F (fun m => X (q.2 m) ω) := by
    intro ω; rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  simp_rw [e]
  rw [integral_finset_sum _ fun q _ => ((bm q.1).mul (bm q.2)).integrable]
  have hterm : ∀ q ∈ I ×ˢ I, ∫ ω, F (fun m => X (q.1 m) ω) * F (fun m => X (q.2 m) ω) ∂μ
      ≤ (if q ∈ P then A else 0) + (if q ∈ Q then C else 0) := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    exact hb q.1 h1 q.2 h2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have c1 : (((I ×ˢ I).filter (· ∈ P)).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_le_card (fun q hq => (Finset.mem_filter.mp hq).2)
  have c2 : (((I ×ˢ I).filter (· ∈ Q)).card : ℝ) ≤ Q.card := by
    exact_mod_cast Finset.card_le_card (fun q hq => (Finset.mem_filter.mp hq).2)
  have := mul_le_mul_of_nonneg_right c1 hA0
  have := mul_le_mul_of_nonneg_right c2 hC0
  linarith

variable [AddCommGroup G] [MeasurableSub₂ G]

/-- The kernel `F̃(y) = F(y₀,…,y_n) c(y_a - y_{n+1})` of the statistic `Z¹`. -/
def Ft {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) (c : G → ℝ) (a : Fin (n + 1))
    (y : Fin (n + 2) → G) : ℝ :=
  F (Fin.init y) * c (y (Fin.castSucc a) - y (Fin.last (n + 1)))

omit [MeasurableSpace G] [MeasurableSub₂ G] in
theorem Ft_update {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) (c : G → ℝ) (a : Fin (n + 1))
    (y : Fin (n + 2) → G) (z : G) :
    Ft F c a (Function.update y (Fin.last (n + 1)) z) = F (Fin.init y) * c (y (Fin.castSucc a) - z) := by
  unfold Ft
  rw [Fin.init_update_last, Function.update_self,
    Function.update_of_ne (Fin.castSucc_ne_last a)]

omit [MeasurableSpace G] [MeasurableSub₂ G] in
theorem Ft_abs_le {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) {c : G → ℝ} {M : ℝ}
    (hcM : ∀ u, |c u| ≤ M) (a : Fin (n + 1)) (y : Fin (n + 2) → G) :
    |Ft F c a y| ≤ M * |F (Fin.init y)| := by
  unfold Ft; rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hcM _) (abs_nonneg _)

theorem Ft_bm {n : ℕ} {F : (Fin (n + 1) → G) → ℝ} (hF : BM F) {c : G → ℝ} (hc : Measurable c)
    {M : ℝ} (hcM : ∀ u, |c u| ≤ M) (a : Fin (n + 1)) : BM (Ft F c a) := by
  obtain ⟨B, hB⟩ := hF.bdd
  refine ⟨(hF.meas.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).mul
    (hc.comp ((measurable_pi_apply _).sub (measurable_pi_apply _))), M * B, fun y => ?_⟩
  refine (Ft_abs_le F hcM a y).trans ?_
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcM 0)
  exact mul_le_mul_of_nonneg_left (hB _) hM

omit [MeasurableSub₂ G] in
theorem Ft_deg {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) {c : G → ℝ}
    (hc_mean : ∀ x, ∫ z, c (x - z) ∂ν = 0) (a : Fin (n + 1)) (y : Fin (n + 2) → G) :
    ∫ z, Ft F c a (Function.update y (Fin.last (n + 1)) z) ∂ν = 0 := by
  simp_rw [Ft_update]
  rw [integral_const_mul, hc_mean, mul_zero]

/-- `E F̃(X_κ)² ≤ M V` for an injective index map `κ`. -/
theorem Ft_sq_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n : ℕ} {F : (Fin (n + 1) → G) → ℝ} (hF : BM F) {c : G → ℝ}
    (hc : Measurable c) {M V : ℝ} (hcM : ∀ u, |c u| ≤ M)
    (hc_sq : ∀ x, ∫ z, c (x - z) ^ 2 ∂ν ≤ M) (a : Fin (n + 1))
    (hV : ∀ ι : Fin (n + 1) → ℕ, Function.Injective ι →
      ∫ ω, F (fun m => X (ι m) ω) ^ 2 ∂μ ≤ V)
    (κ : Fin (n + 2) → ℕ) (hκ : Function.Injective κ) :
    ∫ ω, Ft F c a (fun m => X (κ m) ω) ^ 2 ∂μ ≤ M * V := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcM 0)
  have h := H.integrate_iso κ (Fin.last (n + 1)) (fun m hm h => hm (hκ h))
    (fun y => Ft F c a y ^ 2) (Ft_bm hF hc hcM a).sqr
  simp only at h
  rw [h]
  have hin : ∀ ω, (fun z => Ft F c a (Function.update (fun m => X (κ m) ω) (Fin.last (n + 1)) z) ^ 2)
      = fun z => F (fun m => X (κ (Fin.castSucc m)) ω) ^ 2
          * c (X (κ (Fin.castSucc a)) ω - z) ^ 2 := fun ω => funext fun z => by
    rw [Ft_update, mul_pow]; rfl
  have hle : ∀ ω, ∫ z, Ft F c a (Function.update (fun m => X (κ m) ω) (Fin.last (n + 1)) z) ^ 2 ∂ν
      ≤ M * F (fun m => X (κ (Fin.castSucc m)) ω) ^ 2 := by
    intro ω
    rw [hin ω, integral_const_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hc_sq _) (_root_.sq_nonneg _)
  have hg : BM (fun ω => M * F (fun m => X (κ (Fin.castSucc m)) ω) ^ 2) :=
    BM.const_mul M (H.bm (fun m => κ (Fin.castSucc m)) hF).sqr
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
    integral_nonneg fun z => _root_.sq_nonneg _) hg.integrable
    (Filter.Eventually.of_forall hle)).trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hV _ fun x y h => Fin.castSucc_injective _ (hκ h)) hM

/-- **Products with exactly two common elements**: at most `M² L²`. -/
theorem Ft_pair_two [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n N : ℕ} {F : (Fin (n + 1) → G) → ℝ} (hF : BM F) {c : G → ℝ}
    (hc : Measurable c) {M L : ℝ} (hcM : ∀ u, |c u| ≤ M) (hL0 : 0 ≤ L) (a : Fin (n + 1))
    (hdegt : ∀ x, ∫ z, Ft F c a (Function.update x (Fin.last (n + 1)) z) ∂ν = 0)
    (hcabs : ∀ w x, AW ν (Finset.univ.erase w) (fun y => |F y|) x ≤ L)
    (κ κ' : Fin (n + 2) → Fin N) (hκ : Function.Injective κ) (hκ' : Function.Injective κ')
    (h3 : (κ, κ') ∉ threePairs (n + 2) N) :
    ∫ ω, Ft F c a (fun m => X (κ m) ω) * Ft F c a (fun m => X (κ' m) ω) ∂μ ≤ M ^ 2 * (L * L) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcM 0)
  have hR : 0 ≤ M ^ 2 * (L * L) := by positivity
  have hbt := Ft_bm hF hc hcM a
  have hinjN : Function.Injective fun m => (κ m : ℕ) := fun x y h => hκ (Fin.ext h)
  have hinjN' : Function.Injective fun m => (κ' m : ℕ) := fun x y h => hκ' (Fin.ext h)
  by_cases hA : ∃ m, κ' m = κ (Fin.last (n + 1))
  · by_cases hB : ∃ m, κ m = κ' (Fin.last (n + 1))
    · obtain ⟨m0, hm0⟩ := hA
      have hone : ∀ b b' m m', ((κ (Fin.castSucc b) : ℕ)) = κ' (Fin.castSucc m) →
          ((κ (Fin.castSucc b') : ℕ)) = κ' (Fin.castSucc m') → b = b' := by
        intro b b' m m' h1 h2
        by_contra hbb
        apply h3
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hκ, Fin.castSucc b, Fin.castSucc b',
          Fin.last (n + 1), Fin.castSucc m, Fin.castSucc m', m0,
          fun h => hbb (Fin.castSucc_injective _ h), Fin.castSucc_ne_last b,
          Fin.castSucc_ne_last b', (Fin.ext h1).symm, (Fin.ext h2).symm, hm0⟩
      have b1 : BM (fun ω => |F (fun m => X (κ (Fin.castSucc m)) ω)|) :=
        (H.bm (fun m => (κ (Fin.castSucc m) : ℕ)) hF).absv
      have b2 : BM (fun ω => |F (fun m => X (κ' (Fin.castSucc m)) ω)|) :=
        (H.bm (fun m => (κ' (Fin.castSucc m) : ℕ)) hF).absv
      have hpt : ∀ ω, Ft F c a (fun m => X (κ m) ω) * Ft F c a (fun m => X (κ' m) ω)
          ≤ M ^ 2 * (|F (fun m => X (κ (Fin.castSucc m)) ω)|
            * |F (fun m => X (κ' (Fin.castSucc m)) ω)|) := by
        intro ω
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        have e1 := Ft_abs_le F hcM a (fun m => X (κ m) ω)
        have e2 := Ft_abs_le F hcM a (fun m => X (κ' m) ω)
        calc |Ft F c a (fun m => X (κ m) ω)| * |Ft F c a (fun m => X (κ' m) ω)|
            ≤ (M * |F (fun m => X (κ (Fin.castSucc m)) ω)|)
              * (M * |F (fun m => X (κ' (Fin.castSucc m)) ω)|) :=
              mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
          _ = _ := by ring
      calc ∫ ω, Ft F c a (fun m => X (κ m) ω) * Ft F c a (fun m => X (κ' m) ω) ∂μ
          ≤ ∫ ω, M ^ 2 * (|F (fun m => X (κ (Fin.castSucc m)) ω)|
            * |F (fun m => X (κ' (Fin.castSucc m)) ω)|) ∂μ :=
            integral_mono ((H.bm _ hbt).mul (H.bm _ hbt)).integrable
              ((b1.mul b2).const_mul _).integrable hpt
        _ = M ^ 2 * ∫ ω, |F (fun m => X (κ (Fin.castSucc m)) ω)|
            * |F (fun m => X (κ' (Fin.castSucc m)) ω)| ∂μ := integral_const_mul _ _
        _ ≤ M ^ 2 * (L * L) := mul_le_mul_of_nonneg_left
            (abs_pair_le H F hF hL0 hcabs (fun m => (κ (Fin.castSucc m) : ℕ))
              (fun m => (κ' (Fin.castSucc m) : ℕ))
              (fun x y h => Fin.castSucc_injective _ (hκ (Fin.ext h)))
              (fun x y h => Fin.castSucc_injective _ (hκ' (Fin.ext h))) hone) (by positivity)
    · push Not at hB
      have h0 := H.pair_vanish (fun m => (κ' m : ℕ)) (fun m => (κ m : ℕ)) (Fin.last (n + 1))
        (fun m hm h => hm (hinjN' h)) (fun m h => hB m (Fin.ext h)) _ _ hbt hbt hdegt
      have e : ∫ ω, Ft F c a (fun m => X (κ m) ω) * Ft F c a (fun m => X (κ' m) ω) ∂μ
          = ∫ ω, Ft F c a (fun m => X (κ' m) ω) * Ft F c a (fun m => X (κ m) ω) ∂μ := by
        congr 1; funext ω; ring
      rw [e, h0]; exact hR
  · push Not at hA
    rw [H.pair_vanish (fun m => (κ m : ℕ)) (fun m => (κ' m : ℕ)) (Fin.last (n + 1))
      (fun m hm h => hm (hinjN h)) (fun m h => hA m (Fin.ext h)) _ _ hbt hbt hdegt]
    exact hR

omit [MeasurableSpace G] [AddCommGroup G] [MeasurableSub₂ G] in
theorem inj_of_init {n N : ℕ} (κ : Fin (n + 1) → Fin N) (h1 : Function.Injective (Fin.init κ))
    (h2 : ∀ m, κ (Fin.castSucc m) ≠ κ (Fin.last n)) : Function.Injective κ := by
  intro x y hxy
  induction x using Fin.lastCases with
  | last =>
    induction y using Fin.lastCases with
    | last => rfl
    | cast j => exact absurd hxy.symm (h2 j)
  | cast i =>
    induction y using Fin.lastCases with
    | last => exact absurd hxy (h2 i)
    | cast j => exact congrArg _ (h1 hxy)

end PartB



open PiBound VarianceOne VarianceGeneral2

section PartB2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*}
  [MeasurableSpace G] {ν : Measure G} {X : ℕ → Ω → G}

/-- The bound for `E|F(X_ι)|` used for the non-injective summands. -/
theorem eF_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n N : ℕ} (F : (Fin (n + 1) → G) → ℝ) (hF : BM F) {B L ρ : ℝ}
    (hB : ∀ x, |F x| ≤ B) (hρ0 : 0 ≤ ρ)
    (hcabs : ∀ w x, AW ν (Finset.univ.erase w) (fun y => |F y|) x ≤ L)
    (hρ : ∀ ι : Fin (n + 1) → ℕ, (Finset.univ.image ι).card = n →
      ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ρ)
    (ι : Fin (n + 1) → Fin N) :
    ∫ ω, |F (fun m => X (ι m) ω)| ∂μ
      ≤ if Function.Injective ι then L
        else ρ + B * (if (Finset.univ.image ι).card ≤ n - 1 then 1 else 0) := by
  classical
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => X 0 ω0))
  by_cases hinj : Function.Injective ι
  · rw [if_pos hinj]
    exact abs_le_L H F hF hcabs (fun m => (ι m : ℕ)) (fun x y h => hinj (Fin.ext h))
  · rw [if_neg hinj]
    have hlt : (Finset.univ.image ι).card ≤ n := by
      have h1 : (Finset.univ.image ι).card ≤ n + 1 := by
        have := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n + 1)))) (f := ι)
        simpa using this
      have h2 : (Finset.univ.image ι).card ≠ n + 1 := by
        intro h
        apply hinj
        have h3 : (Finset.univ.image ι).card = (Finset.univ : Finset (Fin (n + 1))).card := by
          simpa using h
        have := Finset.card_image_iff.mp h3
        intro x y hxy
        exact this (Finset.mem_coe.mpr (Finset.mem_univ x))
          (Finset.mem_coe.mpr (Finset.mem_univ y)) hxy
      omega
    by_cases hc : (Finset.univ.image ι).card = n
    · have h := hρ (fun m => (ι m : ℕ)) (by rw [image_val_card]; exact hc)
      have : 0 ≤ B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0) := by
        split_ifs <;> simp [hB0]
      linarith
    · have hc' : (Finset.univ.image ι).card ≤ n - 1 := by omega
      rw [if_pos hc', mul_one]
      have hle : ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ B := by
        calc ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ∫ _ω, B ∂μ :=
              integral_mono (H.bmι hF ι).absv.integrable (integrable_const _) (fun ω => hB _)
          _ = B := by simp
      linarith

/-- The bound for one non-injective summand of `Z¹`, as a function of `ι = init κ` and
    `v = κ (n+1)`. -/
noncomputable def hNI (M L B ρ : ℝ) (n : ℕ) {N : ℕ} (ι : Fin (n + 1) → Fin N) (v : Fin N) : ℝ :=
  if Function.Injective ι then (if v ∈ Finset.univ.image ι then (2 + M) * L else 0)
  else (2 + M * (if v ∈ Finset.univ.image ι then 1 else 0))
    * (ρ + B * (if (Finset.univ.image ι).card ≤ n - 1 then 1 else 0))

theorem hNI_nonneg {M L B ρ : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (n : ℕ)
    {N : ℕ} (ι : Fin (n + 1) → Fin N) (v : Fin N) : 0 ≤ hNI M L B ρ n ι v := by
  unfold hNI
  split_ifs <;> positivity

theorem sum_snoc_split {n N : ℕ} (f : (Fin n → Fin N) → Fin N → ℝ) :
    ∑ κ : Fin (n + 1) → Fin N, f (Fin.init κ) (κ (Fin.last n))
      = ∑ ι : Fin n → Fin N, ∑ v : Fin N, f ι v := by
  rw [← (Fin.snocEquiv fun _ => Fin N).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp [Fin.snocEquiv, Fin.init_snoc, Fin.snoc_last]

variable [AddCommGroup G] [MeasurableSub₂ G]

omit [MeasurableSpace G] [MeasurableSub₂ G] in
/-- The paper's form of `Z¹` (times `N^{n+2}`) is the statistic of `F̃`. -/
theorem sAll_Ft (X : ℕ → Ω → G) (N : ℕ) {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) (c : G → ℝ)
    (a : Fin (n + 1)) (ω : Ω) :
    sAll X N (Ft F c a) ω = ∑ ι : Fin (n + 1) → Fin N, ∑ v : Fin N,
      F (fun m => X (ι m) ω) * c (X (ι a) ω - X v ω) := by
  unfold sAll
  exact sum_snoc_split (fun ι v => F (fun m => X (ι m) ω) * c (X (ι a) ω - X v ω))

/-- **One non-injective summand of `Z¹`.** -/
theorem Ft_noninj_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n N : ℕ} {F : (Fin (n + 1) → G) → ℝ} (hF : BM F) {c : G → ℝ}
    (hc : Measurable c) {M L B ρ : ℝ} (hcM : ∀ u, |c u| ≤ M)
    (hc_abs : ∀ x, ∫ z, |c (x - z)| ∂ν ≤ 2) (hB : ∀ x, |F x| ≤ B) (hρ0 : 0 ≤ ρ)
    (hL0 : 0 ≤ L) (a : Fin (n + 1))
    (hcabs : ∀ w x, AW ν (Finset.univ.erase w) (fun y => |F y|) x ≤ L)
    (hρ : ∀ ι : Fin (n + 1) → ℕ, (Finset.univ.image ι).card = n →
      ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ρ)
    (κ : Fin (n + 2) → Fin N) (hκ : ¬ Function.Injective κ) :
    ∫ ω, |Ft F c a (fun m => X (κ m) ω)| ∂μ
      ≤ hNI M L B ρ n (Fin.init κ) (κ (Fin.last (n + 1))) := by
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcM 0)
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => X 0 ω0))
  have he := eF_le H F hF hB hρ0 hcabs hρ (Fin.init κ)
  have hbF : BM (fun ω => |F (fun m => X (Fin.init κ m) ω)|) := (H.bmι hF _).absv
  have hbt : BM (fun ω => |Ft F c a (fun m => X (κ m) ω)|) :=
    (H.bm (fun m => (κ m : ℕ)) (Ft_bm hF hc hcM a)).absv
  by_cases hv : κ (Fin.last (n + 1)) ∈ Finset.univ.image (Fin.init κ)
  · have h1 : ∫ ω, |Ft F c a (fun m => X (κ m) ω)| ∂μ
        ≤ M * ∫ ω, |F (fun m => X (Fin.init κ m) ω)| ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono hbt.integrable (hbF.const_mul M).integrable
        (fun ω => Ft_abs_le F hcM a (fun m => X (κ m) ω))
    refine h1.trans ?_
    unfold hNI
    by_cases hi : Function.Injective (Fin.init κ)
    · rw [if_pos hi, if_pos hv]
      rw [if_pos hi] at he
      have h2 := mul_le_mul_of_nonneg_left he hM
      have e : (2 + M) * L = 2 * L + M * L := by ring
      linarith
    · rw [if_neg hi, if_pos hv, mul_one]
      rw [if_neg hi] at he
      have hK : 0 ≤ ρ + B * (if (Finset.univ.image (Fin.init κ)).card ≤ n - 1 then (1 : ℝ) else 0) := by
        split_ifs <;> positivity
      have h2 := mul_le_mul_of_nonneg_left he hM
      have e : (2 + M) * (ρ + B * (if (Finset.univ.image (Fin.init κ)).card ≤ n - 1 then (1 : ℝ) else 0))
          = 2 * (ρ + B * (if (Finset.univ.image (Fin.init κ)).card ≤ n - 1 then (1 : ℝ) else 0))
            + M * (ρ + B * (if (Finset.univ.image (Fin.init κ)).card ≤ n - 1 then (1 : ℝ) else 0)) := by
        ring
      linarith
  · have hni : ¬ Function.Injective (Fin.init κ) := by
      intro hi
      apply hκ
      refine inj_of_init κ hi fun m h => hv ?_
      exact Finset.mem_image.mpr ⟨m, Finset.mem_univ _, h⟩
    have hpriv : ∀ m, m ≠ Fin.last (n + 1) → (κ m : ℕ) ≠ (κ (Fin.last (n + 1)) : ℕ) := by
      intro m hm h
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hm
      exact hv (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, Fin.ext h⟩)
    have hI := H.integrate_iso (fun m => (κ m : ℕ)) (Fin.last (n + 1)) hpriv
      (fun y => |Ft F c a y|) (Ft_bm hF hc hcM a).absv
    simp only at hI
    rw [hI]
    have hin : ∀ ω, ∫ z, |Ft F c a (Function.update (fun m => X (κ m) ω) (Fin.last (n + 1)) z)| ∂ν
        ≤ 2 * |F (fun m => X (Fin.init κ m) ω)| := by
      intro ω
      have e : (fun z => |Ft F c a (Function.update (fun m => X (κ m) ω) (Fin.last (n + 1)) z)|)
          = fun z => |F (fun m => X (Fin.init κ m) ω)| * |c (X (κ (Fin.castSucc a)) ω - z)| :=
        funext fun z => by rw [Ft_update, abs_mul]; rfl
      rw [e, integral_const_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hc_abs _) (abs_nonneg _)
    have h1 : ∫ ω, ∫ z, |Ft F c a (Function.update (fun m => X (κ m) ω) (Fin.last (n + 1)) z)| ∂ν ∂μ
        ≤ 2 * ∫ ω, |F (fun m => X (Fin.init κ m) ω)| ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
        integral_nonneg fun z => abs_nonneg _) (hbF.const_mul 2).integrable
        (Filter.Eventually.of_forall hin)
    refine h1.trans ?_
    unfold hNI
    rw [if_neg hni] at he
    rw [if_neg hni, if_neg hv, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_left he (by norm_num)

/-- `√(x + y) ≤ √x + √y`. -/
theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have := Real.sq_sqrt hx; have := Real.sq_sqrt hy
    have := mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)
    nlinarith
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)

set_option maxHeartbeats 1600000 in
/-- **Lemma `lem:degenerate`(b) for `n + 1` indices, abstract form.** HYPOTHESES: independent sample
    with law `ν`; `F` bounded (`|F| ≤ B`) and measurable; `c` measurable with `|c| ≤ M`,
    `∫ c(x - z) dz = 0`, `∫ |c(x - z)| dz ≤ 2`, `∫ c(x - z)² dz ≤ M`; the kernel
    `F̃ = F(y_{≤n}) c(y_a - y_{n+1})` has vanishing conditional mean given its last point
    (`hcondt`); the conditional mean of `|F|` given one point is `≤ L` (`hcabs`; `L ≥ ‖F‖₁`);
    `V ≥ ‖F‖₂²`, `ρ ≥ ϱ(F)` in sample form.  For `N ≥ 1`:
    `E |N^{-(n+2)} ∑_{ι, v} F(X_ι) c(X_{ι(a)} - X_v)|
       ≤ (n+2)² M L / N + (n+2)³ √(M V / N) / N + (n+1)(2 + M) L / N
         + (2 + (n+1) M / N) ((n+1)² ρ / N + (n+1)^{n+1} B / N²)`. -/
theorem degenerate_b_general [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : SP μ ν X) {n : ℕ} (F : (Fin (n + 1) → G) → ℝ) (hF : BM F) {B M L V ρ : ℝ}
    (hB : ∀ x, |F x| ≤ B) (c : G → ℝ) (hc : Measurable c) (hcM : ∀ u, |c u| ≤ M)
    (hc_mean : ∀ x, ∫ z, c (x - z) ∂ν = 0) (hc_abs : ∀ x, ∫ z, |c (x - z)| ∂ν ≤ 2)
    (hc_sq : ∀ x, ∫ z, c (x - z) ^ 2 ∂ν ≤ M) (a : Fin (n + 1)) (hL0 : 0 ≤ L) (hρ0 : 0 ≤ ρ)
    (hcondt : ∀ x, AW ν (Finset.univ.erase (Fin.last (n + 1))) (Ft F c a) x = 0)
    (hcabs : ∀ w x, AW ν (Finset.univ.erase w) (fun y => |F y|) x ≤ L)
    (hV : ∀ ι : Fin (n + 1) → ℕ, Function.Injective ι →
      ∫ ω, F (fun m => X (ι m) ω) ^ 2 ∂μ ≤ V)
    (hρ : ∀ ι : Fin (n + 1) → ℕ, (Finset.univ.image ι).card = n →
      ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ρ)
    (N : ℕ) (hN : 0 < N) :
    ∫ ω, |1 / (N : ℝ) ^ (n + 2) * ∑ ι : Fin (n + 1) → Fin N, ∑ v : Fin N,
        F (fun m => X (ι m) ω) * c (X (ι a) ω - X v ω)| ∂μ
      ≤ ((n : ℝ) + 2) ^ 2 * M * L / N + ((n : ℝ) + 2) ^ 3 * Real.sqrt (M * V / N) / N
        + ((n : ℝ) + 1) * (2 + M) * L / N
        + (2 + ((n : ℝ) + 1) * M / N) * (((n : ℝ) + 1) ^ 2 * ρ / N
          + ((n : ℝ) + 1) ^ (n + 1) * B / (N : ℝ) ^ 2) := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : 0 ≤ M := (abs_nonneg _).trans (hcM 0)
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (fun _ => X 0 ω0))
  have hV0 : 0 ≤ V := (integral_nonneg fun ω => _root_.sq_nonneg _).trans
    (hV (fun m => (m : ℕ)) (fun a b h => Fin.ext h))
  simp_rw [← sAll_Ft X N F c a]
  have hdegt := Ft_deg F hc_mean a (ν := ν)
  have hbt := Ft_bm hF hc hcM a
  have bm : ∀ κ : Fin (n + 2) → Fin N, BM (fun ω => Ft F c a (fun m => X (κ m) ω)) :=
    fun κ => H.bmι hbt κ
  -- the injective part
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin (n + 2) → Fin N),
      I = Finset.univ.filter fun κ : Fin (n + 2) → Fin N => Function.Injective κ := ⟨_, rfl⟩
  have hsqκ : ∀ κ ∈ I, ∫ ω, Ft F c a (fun m => X (κ m) ω) ^ 2 ∂μ ≤ M * V := by
    intro κ hκ
    rw [hI] at hκ
    exact Ft_sq_le H hF hc hcM hc_sq a hV (fun m => (κ m : ℕ))
      (fun x y h => (Finset.mem_filter.mp hκ).2 (Fin.ext h))
  have hb : ∀ κ ∈ I, ∀ κ' ∈ I,
      ∫ ω, Ft F c a (fun m => X (κ m) ω) * Ft F c a (fun m => X (κ' m) ω) ∂μ
        ≤ (if (κ, κ') ∈ twoPairs (n + 2) N then M ^ 2 * (L * L) else 0)
          + (if (κ, κ') ∈ threePairs (n + 2) N then M * V else 0) := by
    intro κ hκ κ' hκ'
    have hinj : Function.Injective κ := by rw [hI] at hκ; exact (Finset.mem_filter.mp hκ).2
    have hinj' : Function.Injective κ' := by rw [hI] at hκ'; exact (Finset.mem_filter.mp hκ').2
    have hA0 : (0 : ℝ) ≤ (if (κ, κ') ∈ twoPairs (n + 2) N then M ^ 2 * (L * L) else 0) := by
      split_ifs <;> positivity
    have hC0 : (0 : ℝ) ≤ (if (κ, κ') ∈ threePairs (n + 2) N then M * V else 0) := by
      split_ifs <;> positivity
    by_cases h3 : (κ, κ') ∈ threePairs (n + 2) N
    · rw [if_pos h3]
      have v1 := hsqκ κ hκ
      have v2 := hsqκ κ' hκ'
      have i1 := (bm κ).sqr.integrable (μ := μ)
      have i2 := (bm κ').sqr.integrable (μ := μ)
      have i3 := ((bm κ).mul (bm κ')).integrable (μ := μ)
      have hcs : ∫ ω, Ft F c a (fun m => X (κ m) ω) * Ft F c a (fun m => X (κ' m) ω) ∂μ
          ≤ M * V := by
        calc ∫ ω, Ft F c a (fun m => X (κ m) ω) * Ft F c a (fun m => X (κ' m) ω) ∂μ
            ≤ ∫ ω, (1 / 2 * Ft F c a (fun m => X (κ m) ω) ^ 2
                + 1 / 2 * Ft F c a (fun m => X (κ' m) ω) ^ 2) ∂μ :=
              integral_mono i3 ((i1.const_mul _).add (i2.const_mul _)) (fun ω => by
                nlinarith [_root_.sq_nonneg (Ft F c a (fun m => X (κ m) ω)
                  - Ft F c a (fun m => X (κ' m) ω))])
          _ = 1 / 2 * ∫ ω, Ft F c a (fun m => X (κ m) ω) ^ 2 ∂μ
                + 1 / 2 * ∫ ω, Ft F c a (fun m => X (κ' m) ω) ^ 2 ∂μ := by
              rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
                integral_const_mul]
          _ ≤ M * V := by linarith
      linarith
    · rw [if_neg h3, add_zero]
      by_cases h2 : (κ, κ') ∈ twoPairs (n + 2) N
      · rw [if_pos h2]
        exact Ft_pair_two H hF hc hcM hL0 a hdegt hcabs κ κ' hinj hinj' h3
      · rw [if_neg h2]
        exact (pair_zero H (Ft F c a) hbt hdegt hcondt κ κ' hinj h2).le
  have hsq := sm_le_two H I (Ft F c a) hbt (by positivity) (mul_nonneg hM hV0)
    (twoPairs (n + 2) N) (threePairs (n + 2) N) hb
  have c2 := twoPairs_card (n + 2) N
  have c3 := threePairs_card (n + 2) N
  push_cast at c2 c3
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((N : ℝ) ^ (n + 1)) ^ 2 := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have eQ : ((N : ℝ) ^ (n + 2)) ^ 2 = (N : ℝ) ^ 2 * Q := by rw [hQ]; ring
  rw [eQ] at c2 c3
  have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have c2' : ((twoPairs (n + 2) N).card : ℝ) ≤ ((n : ℝ) + 2) ^ 4 * Q := by
    have : (N : ℝ) ^ 2 * ((twoPairs (n + 2) N).card : ℝ) ≤ (N : ℝ) ^ 2 * (((n : ℝ) + 2) ^ 4 * Q) := by
      linarith
    exact le_of_mul_le_mul_left this hN2
  have c3' : (N : ℝ) * ((threePairs (n + 2) N).card : ℝ) ≤ ((n : ℝ) + 2) ^ 6 * Q := by
    have : (N : ℝ) ^ 2 * ((N : ℝ) * ((threePairs (n + 2) N).card : ℝ))
        ≤ (N : ℝ) ^ 2 * (((n : ℝ) + 2) ^ 6 * Q) := by
      nlinarith
    exact le_of_mul_le_mul_left this hN2
  have c3'' : ((threePairs (n + 2) N).card : ℝ) ≤ ((n : ℝ) + 2) ^ 6 * Q / N := by
    rw [le_div_iff₀ hNpos]; linarith
  have hInjSq : ∫ ω, sInj X N (Ft F c a) ω ^ 2 ∂μ
      ≤ ((n : ℝ) + 2) ^ 4 * Q * (M ^ 2 * (L * L)) + ((n : ℝ) + 2) ^ 6 * Q / N * (M * V) := by
    have e : (fun ω => sInj X N (Ft F c a) ω ^ 2)
        = fun ω => (∑ κ ∈ I, Ft F c a (fun m => X (κ m) ω)) ^ 2 := by
      funext ω; unfold sInj; rw [hI]
    rw [e]
    refine hsq.trans ?_
    have := mul_le_mul_of_nonneg_right c2' (by positivity : (0 : ℝ) ≤ M ^ 2 * (L * L))
    have := mul_le_mul_of_nonneg_right c3'' (mul_nonneg hM hV0)
    linarith
  have hInj : ∫ ω, |sInj X N (Ft F c a) ω| ∂μ
      ≤ ((n : ℝ) + 2) ^ 2 * (N : ℝ) ^ (n + 1) * M * L
        + ((n : ℝ) + 2) ^ 3 * (N : ℝ) ^ (n + 1) * Real.sqrt (M * V / N) := by
    refine ((H.sInj_bm N hbt).abs_le_sqrt hInjSq).trans ?_
    refine (sqrt_add_le' (by positivity) (by positivity)).trans (le_of_eq ?_)
    have e1 : ((n : ℝ) + 2) ^ 4 * Q * (M ^ 2 * (L * L))
        = (((n : ℝ) + 2) ^ 2 * (N : ℝ) ^ (n + 1) * M * L) ^ 2 := by rw [hQ]; ring
    have e2 : ((n : ℝ) + 2) ^ 6 * Q / N * (M * V)
        = (((n : ℝ) + 2) ^ 3 * (N : ℝ) ^ (n + 1)) ^ 2 * (M * V / N) := by rw [hQ]; ring
    rw [e1, e2, Real.sqrt_sq (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  -- the non-injective part
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin (n + 2) → Fin N),
      J = Finset.univ.filter fun κ : Fin (n + 2) → Fin N => ¬ Function.Injective κ := ⟨_, rfl⟩
  have hNon1 : ∫ ω, ∑ κ ∈ J, |Ft F c a (fun m => X (κ m) ω)| ∂μ
      ≤ ∑ κ : Fin (n + 2) → Fin N, hNI M L B ρ n (Fin.init κ) (κ (Fin.last (n + 1))) := by
    rw [integral_finset_sum _ fun κ _ => (bm κ).absv.integrable]
    calc ∑ κ ∈ J, ∫ ω, |Ft F c a (fun m => X (κ m) ω)| ∂μ
        ≤ ∑ κ ∈ J, hNI M L B ρ n (Fin.init κ) (κ (Fin.last (n + 1))) :=
          Finset.sum_le_sum fun κ hκ => by
            rw [hJ] at hκ
            exact Ft_noninj_le H hF hc hcM hc_abs hB hρ0 hL0 a hcabs hρ κ
              (Finset.mem_filter.mp hκ).2
      _ ≤ ∑ κ : Fin (n + 2) → Fin N, hNI M L B ρ n (Fin.init κ) (κ (Fin.last (n + 1))) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun κ _ _ => hNI_nonneg hM hL0 hB0 hρ0 n _ _)
  rw [sum_snoc_split (fun ι v => hNI M L B ρ n ι v)] at hNon1
  have hrow : ∀ ι : Fin (n + 1) → Fin N, ∑ v : Fin N, hNI M L B ρ n ι v
      ≤ ((n : ℝ) + 1) * ((2 + M) * L)
        + (2 * N + ((n : ℝ) + 1) * M) * (ρ * (if Function.Injective ι then (0 : ℝ) else 1)
          + B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0)) := by
    intro ι
    have hS : ((Finset.univ.image ι).card : ℝ) ≤ (n : ℝ) + 1 := by
      have := Finset.card_image_le (s := (Finset.univ : Finset (Fin (n + 1)))) (f := ι)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    have hind : ∑ v : Fin N, (if v ∈ Finset.univ.image ι then (1 : ℝ) else 0)
        = (Finset.univ.image ι).card := by
      rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hK0 : 0 ≤ ρ * (if Function.Injective ι then (0 : ℝ) else 1)
        + B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0) := by
      split_ifs <;> positivity
    have hT0 : 0 ≤ (2 * N + ((n : ℝ) + 1) * M) := by positivity
    unfold hNI
    by_cases hi : Function.Injective ι
    · simp only [if_pos hi]
      have e : ∑ v : Fin N, (if v ∈ Finset.univ.image ι then (2 + M) * L else 0)
          = (Finset.univ.image ι).card * ((2 + M) * L) := by
        rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]
      rw [e]
      have := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ (2 + M) * L)
      have hK1 : 0 ≤ (2 * N + ((n : ℝ) + 1) * M)
          * (ρ * 0 + B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0)) :=
        mul_nonneg hT0 (by split_ifs <;> simp [hB0])
      linarith
    · simp only [if_neg hi, mul_one]
      have e : ∑ v : Fin N, (2 + M * (if v ∈ Finset.univ.image ι then (1 : ℝ) else 0))
            * (ρ + B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0))
          = (2 * N + M * (Finset.univ.image ι).card)
            * (ρ + B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0)) := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hind, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      rw [e]
      have hK0' : 0 ≤ ρ + B * (if (Finset.univ.image ι).card ≤ n - 1 then (1 : ℝ) else 0) := by
        split_ifs <;> positivity
      have h1 : 2 * (N : ℝ) + M * (Finset.univ.image ι).card ≤ 2 * N + ((n : ℝ) + 1) * M := by
        nlinarith
      have := mul_le_mul_of_nonneg_right h1 hK0'
      have : 0 ≤ ((n : ℝ) + 1) * ((2 + M) * L) := by positivity
      linarith
  obtain ⟨s1, hs1⟩ : ∃ s1 : ℝ, s1 = ∑ ι : Fin (n + 1) → Fin N,
      (if Function.Injective ι then (0 : ℝ) else 1) := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s2 : ℝ, s2 = ((Finset.univ.filter fun x : Fin (n + 1) → Fin N =>
      (Finset.univ.image x).card ≤ n - 1).card : ℝ) := ⟨_, rfl⟩
  have hNon : ∫ ω, ∑ κ ∈ J, |Ft F c a (fun m => X (κ m) ω)| ∂μ
      ≤ (N : ℝ) ^ (n + 1) * (((n : ℝ) + 1) * ((2 + M) * L))
        + (2 * N + ((n : ℝ) + 1) * M) * (ρ * s1 + B * s2) := by
    refine hNon1.trans ((Finset.sum_le_sum fun ι _ => hrow ι).trans (le_of_eq ?_))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.mul_sum,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs1, hs2, Finset.card_filter]
    simp only [nsmul_eq_mul, Fintype.card_pi, Fintype.card_fin, Finset.prod_const,
      Finset.card_univ]
    push_cast
    ring
  -- assembling
  have bJ : BM (fun ω => ∑ κ ∈ J, |Ft F c a (fun m => X (κ m) ω)|) :=
    BM.sum _ _ fun κ _ => (bm κ).absv
  have hpt : ∀ ω, |sAll X N (Ft F c a) ω|
      ≤ |sInj X N (Ft F c a) ω| + ∑ κ ∈ J, |Ft F c a (fun m => X (κ m) ω)| := by
    intro ω
    rw [sAll_split]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    unfold sNon; rw [hJ]
    exact Finset.abs_sum_le_sum_abs _ _
  have hAll : ∫ ω, |sAll X N (Ft F c a) ω| ∂μ
      ≤ (((n : ℝ) + 2) ^ 2 * (N : ℝ) ^ (n + 1) * M * L
        + ((n : ℝ) + 2) ^ 3 * (N : ℝ) ^ (n + 1) * Real.sqrt (M * V / N))
        + ((N : ℝ) ^ (n + 1) * (((n : ℝ) + 1) * ((2 + M) * L))
        + (2 * N + ((n : ℝ) + 1) * M) * (ρ * s1 + B * s2)) := by
    have hmono := integral_mono_of_nonneg (μ := μ)
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)
      ((H.sInj_bm N hbt).absv.add bJ).integrable (Filter.Eventually.of_forall hpt)
    refine hmono.trans ?_
    rw [integral_add (H.sInj_bm N hbt).absv.integrable bJ.integrable]
    linarith
  -- counts
  have hc1 := BiasVariance3.noninj_count (n + 1) N
  have hc3 := low_image_count n N hN
  rw [← hs1] at hc1
  rw [← hs2] at hc3
  push_cast at hc1
  have hs1' : 0 ≤ s1 := by rw [hs1]; exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hs2' : 0 ≤ s2 := by rw [hs2]; positivity
  -- normalise
  have e : ∀ ω, |1 / (N : ℝ) ^ (n + 2) * sAll X N (Ft F c a) ω|
      = 1 / (N : ℝ) ^ (n + 2) * |sAll X N (Ft F c a) ω| := fun ω => by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (n + 2))]
  simp_rw [e]
  rw [integral_const_mul]
  have hq : 0 < (N : ℝ) ^ (n + 1) := by positivity
  have h4 := mul_le_mul_of_nonneg_left hAll (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ) ^ (n + 2))
  have hρs : ρ * s1 / (N : ℝ) ^ (n + 1) ≤ ((n : ℝ) + 1) ^ 2 * ρ / N := by
    rw [div_le_div_iff₀ hq hNpos]
    have := mul_le_mul_of_nonneg_left hc1 hρ0
    linarith [show ρ * s1 * N = ρ * (N * s1) by ring,
      show ((n : ℝ) + 1) ^ 2 * ρ * (N : ℝ) ^ (n + 1) = ρ * (((n : ℝ) + 1) ^ 2 * (N : ℝ) ^ (n + 1))
        by ring]
  have hBs : B * s2 / (N : ℝ) ^ (n + 1) ≤ ((n : ℝ) + 1) ^ (n + 1) * B / (N : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hq (by positivity)]
    have := mul_le_mul_of_nonneg_left hc3 hB0
    linarith [show B * s2 * (N : ℝ) ^ 2 = B * ((N : ℝ) ^ 2 * s2) by ring,
      show ((n : ℝ) + 1) ^ (n + 1) * B * (N : ℝ) ^ (n + 1)
        = B * (((n : ℝ) + 1) ^ (n + 1) * (N : ℝ) ^ (n + 1)) by ring]
  have hfac : 0 ≤ 2 + ((n : ℝ) + 1) * M / N := by positivity
  have e2 : 1 / (N : ℝ) ^ (n + 2) * ((((n : ℝ) + 2) ^ 2 * (N : ℝ) ^ (n + 1) * M * L
        + ((n : ℝ) + 2) ^ 3 * (N : ℝ) ^ (n + 1) * Real.sqrt (M * V / N))
        + ((N : ℝ) ^ (n + 1) * (((n : ℝ) + 1) * ((2 + M) * L))
        + (2 * N + ((n : ℝ) + 1) * M) * (ρ * s1 + B * s2)))
      = ((n : ℝ) + 2) ^ 2 * M * L / N + ((n : ℝ) + 2) ^ 3 * Real.sqrt (M * V / N) / N
        + ((n : ℝ) + 1) * (2 + M) * L / N
        + (2 + ((n : ℝ) + 1) * M / N) * (ρ * s1 / (N : ℝ) ^ (n + 1)
          + B * s2 / (N : ℝ) ^ (n + 1)) := by
    field_simp
    ring
  rw [e2] at h4
  have := mul_le_mul_of_nonneg_left (add_le_add hρs hBs) hfac
  linarith

end PartB2



open PiBound VarianceOne VarianceGeneral2 CTG.Reals.TorusReduction

section TorusB

theorem Ft_TI {G : Type*} [AddCommGroup G] {n : ℕ} {F : (Fin (n + 1) → G) → ℝ} (hT : TI F)
    (c : G → ℝ) (a : Fin (n + 1)) : TI (Ft F c a) := by
  intro x t
  unfold Ft
  exact congrArg₂ (· * ·) (hT (Fin.init x) t) (by rw [add_sub_add_right_eq_sub])

/-- `AW univ G y` does not depend on `y`. -/
theorem AW_univ_const {G : Type*} [AddCommGroup G] [MeasurableSpace G] {ν : Measure G} [IsProbabilityMeasure ν]
    {n : ℕ} {F : (Fin n → G) → ℝ} (hF : BM F) (x y : Fin n → G) :
    AW ν Finset.univ F x = AW ν Finset.univ F y :=
  AW_off _ hF _ _ fun i hi => absurd (Finset.mem_univ i) hi

/-- **Lemma `lem:degenerate`(b) for `n + 1` indices on the flat torus.** Independent uniform points
    on `FlatTorus d`, `c_{jv} = p(x_j - x_v) - 1` with the periodised Gaussian `p` of variance
    `σ > 0` and `M = sup p = p(0)`; `F` measurable, `|F| ≤ B`, invariant under simultaneous
    translations; `L ≥ ‖F‖₁`, `V ≥ ‖F‖₂²` (injective index maps) and `ρ ≥ ϱ(F)` in sample form,
    `ρ ≥ 0`; `a` any position.  For `N ≥ 1`:
    `E |N^{-(n+2)} ∑_{ι, v} F(X_ι) c(X_{ι(a)} - X_v)|
       ≤ (n+2)² M L / N + (n+2)³ √(M V / N) / N + (n+1)(2 + M) L / N
         + (2 + (n+1) M / N) ((n+1)² ρ / N + (n+1)^{n+1} B / N²)`. -/
theorem degenerate_b_general_torus {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ)
    (hX : ∀ j, Measurable (X j)) (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d)
    {σ : ℝ} (hσ : 0 < σ)
    {n : ℕ} (F : (Fin (n + 1) → FlatTorus d) → ℝ) (hFm : Measurable F) {B L V ρ : ℝ}
    (hB : ∀ x, |F x| ≤ B) (hT : TI F) (a : Fin (n + 1)) (hρ0 : 0 ≤ ρ)
    (hl1 : ∀ ι : Fin (n + 1) → ℕ, Function.Injective ι →
      ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ L)
    (hV : ∀ ι : Fin (n + 1) → ℕ, Function.Injective ι →
      ∫ ω, F (fun m => X (ι m) ω) ^ 2 ∂μ ≤ V)
    (hρ : ∀ ι : Fin (n + 1) → ℕ, (Finset.univ.image ι).card = n →
      ∫ ω, |F (fun m => X (ι m) ω)| ∂μ ≤ ρ)
    (N : ℕ) (hN : 0 < N) :
    ∫ ω, |1 / (N : ℝ) ^ (n + 2) * ∑ ι : Fin (n + 1) → Fin N, ∑ v : Fin N,
        F (fun m => X (ι m) ω) * (pker d σ (X (ι a) ω - X v ω) - 1)| ∂μ
      ≤ ((n : ℝ) + 2) ^ 2 * torusM d σ 1 * L / N
        + ((n : ℝ) + 2) ^ 3 * Real.sqrt (torusM d σ 1 * V / N) / N
        + ((n : ℝ) + 1) * (2 + torusM d σ 1) * L / N
        + (2 + ((n : ℝ) + 1) * torusM d σ 1 / N) * (((n : ℝ) + 1) ^ 2 * ρ / N
          + ((n : ℝ) + 1) ^ (n + 1) * B / (N : ℝ) ^ 2) := by
  have hF : BM F := ⟨hFm, B, hB⟩
  have H : SP μ (flatTorusMeasure d) X := ⟨h_indep, hX, hlaw⟩
  -- the facts about `c = p - 1`, read off from the `n = 3` structure with `F = 0`
  have HC := DegenerateB.torus_degB3 X h_indep hX hlaw hσ (F := fun _ _ _ => (0 : ℝ))
    (B := 0) (L := 0) (V := 0) (ρ := 0) measurable_const (fun _ _ _ => by simp)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ _ _ => by simp) (fun _ _ _ _ _ _ => by simp)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  have hL0 : 0 ≤ L := (integral_nonneg fun ω => abs_nonneg _).trans
    (hl1 (fun m => (m : ℕ)) (fun x y h => Fin.ext h))
  have hinv := torus_hinv d
  have hFa : BM (fun y => |F y|) := hF.absv
  have hTa : TI (fun y : Fin (n + 1) → FlatTorus d => |F y|) := fun x t => by
    show |F (fun i => x i + t)| = |F x|
    rw [hT x t]
  have hcabs : ∀ w x, AW (flatTorusMeasure d) (Finset.univ.erase w) (fun y => |F y|) x ≤ L := by
    intro w x
    have h1 := AW_le1_const hinv hFa hTa (S := {w}) (by simp) x
    rw [Finset.compl_singleton] at h1
    rw [h1]
    have h2 := int_set H (fun m => (m : ℕ)) (Fin.elim0 : Fin 0 → ℕ) (fun y => |F y|)
      (fun _ => (1 : ℝ)) hFa (BM.const 1) Finset.univ
      (fun v _ => ⟨fun m hm h => hm (Fin.ext h), fun m => m.elim0⟩)
    simp only [mul_one] at h2
    have h3 : ∫ ω, AW (flatTorusMeasure d) Finset.univ (fun y => |F y|)
        (fun m => X (m : ℕ) ω) ∂μ = AW (flatTorusMeasure d) Finset.univ (fun y => |F y|) 0 := by
      simp_rw [AW_univ_const hFa _ (0 : Fin (n + 1) → FlatTorus d)]
      simp
    rw [← h3, ← h2]
    exact hl1 (fun m => (m : ℕ)) (fun x y h => Fin.ext h)
  have hcond := cond_of_TI hinv (Ft_bm hF HC.c_meas HC.c_bound a) (Ft_TI hT _ a)
    (Ft_deg F HC.c_mean1 a)
  exact degenerate_b_general H F hF hB (fun u => pker d σ u - 1) HC.c_meas HC.c_bound
    HC.c_mean1 HC.c_abs HC.c_sq a hL0 hρ0 hcond hcabs hV hρ N hN

end TorusB


end DegenerateGeneral

namespace BiasSharp

open PiBound CTG.Reals.TorusReduction BiasVariance BiasGeneral

/-! ## Part 1 (deterministic): the vertex factor with a CUBIC remainder -/

/-- `x y² ≤ x³ + y³` for `x, y ≥ 0`. -/
theorem amgm_xyy {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x * y ^ 2 ≤ x ^ 3 + y ^ 3 := by
  nlinarith [mul_nonneg (_root_.sq_nonneg (x - y)) (add_nonneg hx (mul_nonneg zero_le_two hy)),
    pow_nonneg hy 3, pow_nonneg hx 3]

/-- `(x + y + z)³ ≤ 9 (x³ + y³ + z³)` for `x, y, z ≥ 0`. -/
theorem cube_sum3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (x + y + z) ^ 3 ≤ 9 * (x ^ 3 + y ^ 3 + z ^ 3) := by
  have p1 : x ^ 2 * y + x * y ^ 2 ≤ x ^ 3 + y ^ 3 := by
    nlinarith only [mul_nonneg (add_nonneg hx hy) (_root_.sq_nonneg (x - y))]
  have p2 : x ^ 2 * z + x * z ^ 2 ≤ x ^ 3 + z ^ 3 := by
    nlinarith only [mul_nonneg (add_nonneg hx hz) (_root_.sq_nonneg (x - z))]
  have p3 : y ^ 2 * z + y * z ^ 2 ≤ y ^ 3 + z ^ 3 := by
    nlinarith only [mul_nonneg (add_nonneg hy hz) (_root_.sq_nonneg (y - z))]
  have p4 : 3 * (x * y * z) ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
    nlinarith only [mul_nonneg (add_nonneg (add_nonneg hx hy) hz)
      (add_nonneg (add_nonneg (_root_.sq_nonneg (x - y)) (_root_.sq_nonneg (y - z)))
        (_root_.sq_nonneg (z - x)))]
  have e : (x + y + z) ^ 3 = x ^ 3 + y ^ 3 + z ^ 3
      + 3 * ((x ^ 2 * y + x * y ^ 2) + (x ^ 2 * z + x * z ^ 2) + (y ^ 2 * z + y * z ^ 2))
      + 6 * (x * y * z) := by ring
  rw [e]; linarith only [p1, p2, p3, p4]

/-- `(x + y + z)² ≤ 3 (x² + y² + z²)`. -/
theorem sq_sum3 (x y z : ℝ) : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith only [_root_.sq_nonneg (x - y), _root_.sq_nonneg (x - z), _root_.sq_nonneg (y - z)]

/-- **Step 2 of `prop:bias` with a cubic remainder** (abstract form).  `e = ε_i`, `b = (P̃ε)_i`,
    `s = (P̃ε²)_i`, `z = (P̃ϑ)_i`, `t = (P̃|ε|³)_i`; the hypotheses are those available on the
    fixed event `max |ε| ≤ 1/8`.  Then
    `|γ - (1 + φ¹ + φ²)| ≤ 40 (|e|³ + |b|³ + t)`. -/
theorem gamma_cubic {e b s z t γ : ℝ} (he : |e| ≤ 1 / 8) (hb : |b| ≤ 9 / 64) (hs0 : 0 ≤ s)
    (hs : s ≤ 9 / 512) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 256) (hz : |z| ≤ 2 * t)
    (hxs : ∀ x : ℝ, 0 ≤ x → x * s ≤ x ^ 3 + t)
    (hγ : γ * ((1 + e) * (1 + (e - b + (s + z)))) = 1) :
    |γ - (1 - 2 * e + b + 3 * e ^ 2 - 3 * e * b + b ^ 2 - s)|
      ≤ 40 * (|e| ^ 3 + |b| ^ 3 + t) := by
  have heabs := he
  obtain ⟨A, hA⟩ : ∃ A, A = |e| := ⟨_, rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb, Bb = |b| := ⟨_, rfl⟩
  rw [← hA, ← hBb]
  rw [← hA] at he
  rw [← hBb] at hb
  have hA0 : 0 ≤ A := hA ▸ abs_nonneg e
  have hB0 : 0 ≤ Bb := hBb ▸ abs_nonneg b
  have hA3 : 0 ≤ A ^ 3 := pow_nonneg hA0 3
  have hB3 : 0 ≤ Bb ^ 3 := pow_nonneg hB0 3
  have he2 : e ^ 2 = A ^ 2 := by rw [hA, sq_abs]
  -- s² ≤ 2t
  have hss : s ^ 2 ≤ 2 * t := by
    have h := hxs s hs0
    have h3 : s * s ^ 2 ≤ 9 / 512 * s ^ 2 := mul_le_mul_of_nonneg_right hs (_root_.sq_nonneg s)
    have e3 : s ^ 3 = s * s ^ 2 := by ring
    have e2 : s * s = s ^ 2 := by ring
    rw [e3] at h; rw [e2] at h
    nlinarith only [h, h3, _root_.sq_nonneg s, ht0]
  have hAs : A * s ≤ A ^ 3 + t := hxs A hA0
  have hBs : Bb * s ≤ Bb ^ 3 + t := hxs Bb hB0
  have hABB : A * Bb ^ 2 ≤ A ^ 3 + Bb ^ 3 := amgm_xyy hA0 hB0
  have hAAB : Bb * A ^ 2 ≤ Bb ^ 3 + A ^ 3 := amgm_xyy hB0 hA0
  obtain ⟨hz1, hz2⟩ := abs_le.mp hz
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = s + z := ⟨_, rfl⟩
  have hwa : |w| ≤ s + 2 * t := by
    rw [hw, abs_le]; constructor <;> linarith only [hz1, hz2, hs0]
  obtain ⟨W, hW⟩ : ∃ W, W = |w| := ⟨_, rfl⟩
  rw [← hW] at hwa
  have hW0 : 0 ≤ W := hW ▸ abs_nonneg w
  have hw2' : w ^ 2 = W ^ 2 := by rw [hW, sq_abs]
  have hWW : W ^ 2 ≤ 3 * t := by
    have h1 : W ^ 2 ≤ (s + 2 * t) ^ 2 := pow_le_pow_left₀ hW0 hwa 2
    have e1 : (s + 2 * t) ^ 2 = s ^ 2 + 4 * (s * t) + 4 * (t * t) := by ring
    have h2 : s * t ≤ 9 / 512 * t := mul_le_mul_of_nonneg_right hs ht0
    have h3 : t * t ≤ 1 / 256 * t := mul_le_mul_of_nonneg_right ht ht0
    linarith only [h1, e1, hss, h2, h3, ht0]
  have hWs : W ≤ 1 / 32 := by linarith only [hwa, hs, ht]
  have hAW : A * W ≤ A ^ 3 + 2 * t := by
    have h1 := mul_le_mul_of_nonneg_left hwa hA0
    have h2 : A * t ≤ 1 / 8 * t := mul_le_mul_of_nonneg_right he ht0
    have e1 : A * (s + 2 * t) = A * s + 2 * (A * t) := by ring
    linarith only [h1, h2, e1, hAs, ht0]
  have hBW : Bb * W ≤ Bb ^ 3 + 2 * t := by
    have h1 := mul_le_mul_of_nonneg_left hwa hB0
    have h2 : Bb * t ≤ 9 / 64 * t := mul_le_mul_of_nonneg_right hb ht0
    have e1 : Bb * (s + 2 * t) = Bb * s + 2 * (Bb * t) := by ring
    linarith only [h1, h2, e1, hBs, ht0]
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ, χ = e - b + w := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = |χ| := ⟨_, rfl⟩
  have hχa : X ≤ A + Bb + W := by
    rw [hX, hχ, hA, hBb, hW]
    calc |e - b + w| ≤ |e - b| + |w| := abs_add_le _ _
      _ ≤ |e| + |b| + |w| := by linarith only [abs_sub e b]
  have hX0 : 0 ≤ X := hX ▸ abs_nonneg χ
  have hχ2 : χ ^ 2 = X ^ 2 := by rw [hX, sq_abs]
  have hXs : X ≤ 3 / 10 := by linarith only [hχa, he, hb, hWs]
  have hX2 : X ^ 2 ≤ 3 * (A ^ 2 + Bb ^ 2 + W ^ 2) := by
    have h1 : X ^ 2 ≤ (A + Bb + W) ^ 2 := pow_le_pow_left₀ hX0 hχa 2
    exact h1.trans (sq_sum3 A Bb W)
  have hX3 : X ^ 3 ≤ 9 * (A ^ 3 + Bb ^ 3 + W ^ 3) := by
    have h1 : X ^ 3 ≤ (A + Bb + W) ^ 3 := pow_le_pow_left₀ hX0 hχa 3
    exact h1.trans (cube_sum3 hA0 hB0 hW0)
  have hW3 : W ^ 3 ≤ 1 / 10 * t := by
    have e1 : W ^ 3 = W * W ^ 2 := by ring
    have h1 := mul_le_mul_of_nonneg_left hWW hW0
    have h2 : W * (3 * t) ≤ 1 / 32 * (3 * t) := mul_le_mul_of_nonneg_right hWs (by linarith only [ht0])
    rw [e1]; linarith only [h1, h2, ht0]
  have hAW2 : A * W ^ 2 ≤ 3 / 8 * t := by
    have h1 := mul_le_mul_of_nonneg_right he (_root_.sq_nonneg W)
    have h2 : 1 / 8 * W ^ 2 ≤ 1 / 8 * (3 * t) := mul_le_mul_of_nonneg_left hWW (by norm_num)
    linarith only [h1, h2]
  have hAX2 : A * X ^ 2 ≤ 6 * A ^ 3 + 3 * Bb ^ 3 + 2 * t := by
    have h1 := mul_le_mul_of_nonneg_left hX2 hA0
    have e1 : A * (3 * (A ^ 2 + Bb ^ 2 + W ^ 2)) = 3 * A ^ 3 + 3 * (A * Bb ^ 2) + 3 * (A * W ^ 2) := by
      ring
    linarith only [h1, e1, hABB, hAW2, ht0]
  have he1 := abs_le.mp heabs
  have h1e : 7 / 8 ≤ 1 + e := by linarith only [he1.1]
  have hχb : |χ| ≤ 3 / 10 := by rw [← hX]; exact hXs
  have h1χ : 7 / 10 ≤ 1 + χ := by linarith only [(abs_le.mp hχb).1]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (1 + e) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1 + χ) := ⟨_, rfl⟩
  have ha1 : a * (1 + e) = 1 := by rw [ha]; exact one_div_mul_cancel (by linarith only [h1e])
  have hc1 : c * (1 + χ) = 1 := by rw [hc]; exact one_div_mul_cancel (by linarith only [h1χ])
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg zero_le_one (by linarith only [h1e])
  have hc0 : 0 ≤ c := by rw [hc]; exact div_nonneg zero_le_one (by linarith only [h1χ])
  have ha8 : a ≤ 8 / 7 := by
    have := mul_le_mul_of_nonneg_left h1e ha0; linarith only [this, ha1]
  have hc8 : c ≤ 10 / 7 := by
    have := mul_le_mul_of_nonneg_left h1χ hc0; linarith only [this, hc1]
  have hγac : γ = a * c := by
    have h : γ * ((1 + e) * (1 + χ)) = 1 := by rw [hχ, hw]; exact hγ
    calc γ = γ * ((a * (1 + e)) * (c * (1 + χ))) := by rw [ha1, hc1]; ring
      _ = (γ * ((1 + e) * (1 + χ))) * (a * c) := by ring
      _ = a * c := by rw [h]; ring
  have hAe : a = 1 - e + e ^ 2 - e ^ 3 * a := by linear_combination (1 - e + e ^ 2) * ha1
  have hCe : c = 1 - χ + χ ^ 2 - χ ^ 3 * c := by linear_combination (1 - χ + χ ^ 2) * hc1
  have hdec : γ - (1 - 2 * e + b + 3 * e ^ 2 - 3 * e * b + b ^ 2 - s)
      = (-z + w ^ 2 + 3 * e * w - 2 * b * w - e * χ ^ 2 - e ^ 2 * χ + e ^ 2 * χ ^ 2)
        - (1 - e + e ^ 2) * (χ * χ ^ 2 * c) - e * e ^ 2 * (a * c) := by
    rw [hγac]
    subst hχ
    subst hw
    linear_combination c * hAe + (1 - e + e ^ 2) * hCe
  -- the nine terms
  have b1 : |-z| ≤ 2 * t := by rw [abs_neg]; exact hz
  have b2 : |w ^ 2| ≤ 3 * t := by rw [abs_of_nonneg (_root_.sq_nonneg w), hw2']; exact hWW
  have b3 : |3 * e * w| ≤ 3 * A ^ 3 + 6 * t := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), ← hA, ← hW]
    linarith only [hAW]
  have b4 : |2 * b * w| ≤ 2 * Bb ^ 3 + 4 * t := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), ← hBb, ← hW]
    linarith only [hBW]
  have b5 : |e * χ ^ 2| ≤ 6 * A ^ 3 + 3 * Bb ^ 3 + 2 * t := by
    rw [abs_mul, abs_of_nonneg (_root_.sq_nonneg χ), hχ2, ← hA]; exact hAX2
  have b6 : |e ^ 2 * χ| ≤ 3 * A ^ 3 + Bb ^ 3 + t := by
    rw [abs_mul, abs_of_nonneg (_root_.sq_nonneg e), he2, ← hX]
    have h1 := mul_le_mul_of_nonneg_left hχa (_root_.sq_nonneg A)
    have h2 : A ^ 2 * W ≤ 1 / 8 * (A ^ 3 + 2 * t) := by
      have e1 : A ^ 2 * W = A * (A * W) := by ring
      rw [e1]
      have h3 := mul_le_mul_of_nonneg_right he (mul_nonneg hA0 hW0)
      have h4 : 1 / 8 * (A * W) ≤ 1 / 8 * (A ^ 3 + 2 * t) := mul_le_mul_of_nonneg_left hAW (by norm_num)
      linarith only [h3, h4]
    have e1 : A ^ 2 * (A + Bb + W) = A ^ 3 + Bb * A ^ 2 + A ^ 2 * W := by ring
    linarith only [h1, e1, h2, hAAB, hA3, ht0]
  have b7 : |e ^ 2 * χ ^ 2| ≤ 6 * A ^ 3 + 3 * Bb ^ 3 + 2 * t := by
    rw [abs_mul, abs_of_nonneg (_root_.sq_nonneg e), abs_of_nonneg (_root_.sq_nonneg χ), he2, hχ2]
    have e1 : A ^ 2 * X ^ 2 = A * (A * X ^ 2) := by ring
    rw [e1]
    have h0 : 0 ≤ A * X ^ 2 := mul_nonneg hA0 (_root_.sq_nonneg X)
    have h3 := mul_le_mul_of_nonneg_right he h0
    linarith only [h3, hAX2, h0]
  have hU : |1 - e + e ^ 2| ≤ 5 / 4 := by
    have hee : e ^ 2 ≤ (1 / 8) ^ 2 := by rw [he2]; exact pow_le_pow_left₀ hA0 he 2
    have hee0 := _root_.sq_nonneg e
    rw [abs_le]; constructor <;> linarith only [he1.1, he1.2, hee, hee0]
  have b8 : |(1 - e + e ^ 2) * (χ * χ ^ 2 * c)| ≤ 17 * (A ^ 3 + Bb ^ 3) + 2 * t := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (_root_.sq_nonneg χ), abs_of_nonneg hc0, hχ2,
      ← hX]
    have e3 : X * X ^ 2 = X ^ 3 := by ring
    rw [e3]
    have h1 : X ^ 3 * c ≤ X ^ 3 * (10 / 7) := mul_le_mul_of_nonneg_left hc8 (pow_nonneg hX0 3)
    have h2 : 0 ≤ X ^ 3 * c := mul_nonneg (pow_nonneg hX0 3) hc0
    have h3 := mul_le_mul hU h1 h2 (by norm_num)
    linarith only [h3, hX3, hW3, hA3, hB3, ht0]
  have b9 : |e * e ^ 2 * (a * c)| ≤ 2 * A ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (_root_.sq_nonneg e), abs_of_nonneg (mul_nonneg ha0 hc0),
      he2, ← hA]
    have hac : a * c ≤ 8 / 7 * (10 / 7) := mul_le_mul ha8 hc8 hc0 (by norm_num)
    have e1 : A * A ^ 2 = A ^ 3 := by ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hac hA3
    linarith only [this, hA3]
  rw [hdec]
  obtain ⟨l1, u1⟩ := abs_le.mp b1
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  obtain ⟨l3, u3⟩ := abs_le.mp b3
  obtain ⟨l4, u4⟩ := abs_le.mp b4
  obtain ⟨l5, u5⟩ := abs_le.mp b5
  obtain ⟨l6, u6⟩ := abs_le.mp b6
  obtain ⟨l7, u7⟩ := abs_le.mp b7
  obtain ⟨l8, u8⟩ := abs_le.mp b8
  obtain ⟨l9, u9⟩ := abs_le.mp b9
  rw [abs_le]
  constructor <;> linarith only [l1, u1, l2, u2, l3, u3, l4, u4, l5, u5, l6, u6, l7, u7, l8, u8,
    l9, u9, hA3, hB3, ht0]

/-! ## Part 2 (deterministic): the product of `k` vertex factors with a cubic remainder -/

/-- The arithmetic of one induction step of `prod_cubic`. -/
theorem step_cubic {k G W0 SW E R0 g0' a0 c0 C S2 A : ℝ} (hk : 0 ≤ k)
    (hG : 0 ≤ G) (hW0 : 0 ≤ W0) (hSW : 0 ≤ SW)
    (hE : |E| ≤ G * SW) (hR0 : |R0| ≤ W0) (hg0 : |g0'| ≤ 2)
    (hC : |a0 * C| ≤ 5 * (k * W0 + SW))
    (hS2 : |a0 * S2| ≤ (k + 1) / 2 * (k * W0 + SW))
    (hS1b : |A + C + S2| ≤ k + k * (k + 1) / 8)
    (hcA : |c0 * A| ≤ 5 * (SW + k * W0)) (hcC : |c0 * C| ≤ 25 * (k * W0 + SW))
    (hcS : |c0 * S2| ≤ 5 * (k + 1) / 4 * (SW + k * W0)) :
    |g0' * E + R0 + a0 * C + a0 * S2 + (c0 + R0) * (A + C + S2)|
      ≤ (2 * G + 200 * (k + 1) ^ 2) * (W0 + SW) := by
  have t1 : |g0' * E| ≤ 2 * (G * SW) := by
    rw [abs_mul]; exact mul_le_mul hg0 hE (abs_nonneg _) (by norm_num)
  have t2 : |R0 * (A + C + S2)| ≤ W0 * (k + k * (k + 1) / 8) := by
    rw [abs_mul]; exact mul_le_mul hR0 hS1b (abs_nonneg _) hW0
  have t3 : |c0 * (A + C + S2)| ≤ |c0 * A| + |c0 * C| + |c0 * S2| := by
    rw [mul_add, mul_add]
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have e : g0' * E + R0 + a0 * C + a0 * S2 + (c0 + R0) * (A + C + S2)
      = g0' * E + R0 + a0 * C + a0 * S2 + c0 * (A + C + S2) + R0 * (A + C + S2) := by ring
  rw [e]
  have tot : |g0' * E + R0 + a0 * C + a0 * S2 + c0 * (A + C + S2) + R0 * (A + C + S2)|
      ≤ |g0' * E| + |R0| + |a0 * C| + |a0 * S2| + |c0 * (A + C + S2)| + |R0 * (A + C + S2)| := by
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact abs_add_le _ _
  refine tot.trans ?_
  have p1 : 0 ≤ k * W0 := mul_nonneg hk hW0
  have p2 : 0 ≤ k * k * W0 := mul_nonneg (mul_nonneg hk hk) hW0
  have p3 : 0 ≤ k * SW := mul_nonneg hk hSW
  have p4 : 0 ≤ k * k * SW := mul_nonneg (mul_nonneg hk hk) hSW
  have p5 : 0 ≤ G * W0 := mul_nonneg hG hW0
  nlinarith only [t1, t2, t3, hC, hS2, hcA, hcC, hcS, hR0, p1, p2, p3, p4, p5, hW0, hSW, hk]

/-- **The product of `k` vertex factors to second order, cubic remainder.** Hypotheses per
    position: `|g - (1 + a + c)| ≤ W`, `|a| ≤ 1/2`, `|a|³ ≤ W`, `|c| ≤ 5q`, `0 ≤ q ≤ 1/16`,
    `x q ≤ x³ + W` for all `x ≥ 0` (this encodes `q^{3/2} ≲ W`), `|g| ≤ 2`, `W ≥ 0`.  Then
    `|∏ g - (1 + ∑ (a + c) + ((∑ a)² - ∑ a²)/2)| ≤ gC k · ∑ W`. -/
theorem prod_cubic :
    ∀ (k : ℕ) (g a c q W : Fin k → ℝ), (∀ t, 0 ≤ W t) → (∀ t, 0 ≤ q t) → (∀ t, q t ≤ 1 / 16) →
      (∀ t, |g t - (1 + a t + c t)| ≤ W t) → (∀ t, |a t| ≤ 1 / 2) → (∀ t, |a t| ^ 3 ≤ W t) →
      (∀ t, |c t| ≤ 5 * q t) → (∀ t x, 0 ≤ x → x * q t ≤ x ^ 3 + W t) → (∀ t, |g t| ≤ 2) →
      |∏ t, g t - (1 + ∑ t, (a t + c t) + ((∑ t, a t) ^ 2 - ∑ t, a t ^ 2) / 2)|
        ≤ BiasGeneral.gC k * ∑ t, W t := by
  intro k
  induction k with
  | zero => intro g a c q W _ _ _ _ _ _ _ _ _; simp [BiasGeneral.gC]
  | succ k ih =>
    intro g a c q W hW hq hq16 hg ha ha3 hc hxq hg2
    have IH := ih (fun t => g t.succ) (fun t => a t.succ) (fun t => c t.succ) (fun t => q t.succ)
      (fun t => W t.succ) (fun t => hW _) (fun t => hq _) (fun t => hq16 _) (fun t => hg _)
      (fun t => ha _) (fun t => ha3 _) (fun t => hc _) (fun t => hxq _) (fun t => hg2 _)
    simp only [Fin.prod_univ_succ, Fin.sum_univ_succ]
    obtain ⟨P, hP⟩ : ∃ P, P = ∏ t : Fin k, g t.succ := ⟨_, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A, A = ∑ t : Fin k, a t.succ := ⟨_, rfl⟩
    obtain ⟨C, hC⟩ : ∃ C, C = ∑ t : Fin k, c t.succ := ⟨_, rfl⟩
    obtain ⟨Q2, hQ2⟩ : ∃ Q2, Q2 = ∑ t : Fin k, a t.succ ^ 2 := ⟨_, rfl⟩
    obtain ⟨SW, hSW⟩ : ∃ SW, SW = ∑ t : Fin k, W t.succ := ⟨_, rfl⟩
    have hS1e : ∑ t : Fin k, (a t.succ + c t.succ) = A + C := by
      rw [hA, hC, Finset.sum_add_distrib]
    rw [← hP, ← hQ2, ← hSW, hS1e, ← hA] at IH
    rw [← hP, ← hA, ← hQ2, ← hSW, hS1e]
    obtain ⟨E, hE⟩ : ∃ E, E = P - (1 + (A + C) + (A ^ 2 - Q2) / 2) := ⟨_, rfl⟩
    obtain ⟨R0, hR0⟩ : ∃ R0, R0 = g 0 - (1 + a 0 + c 0) := ⟨_, rfl⟩
    rw [← hE] at IH
    have e : g 0 * P - (1 + (a 0 + c 0 + (A + C)) + ((a 0 + A) ^ 2 - (a 0 ^ 2 + Q2)) / 2)
        = g 0 * E + R0 + a 0 * C + a 0 * ((A ^ 2 - Q2) / 2)
          + (c 0 + R0) * (A + C + (A ^ 2 - Q2) / 2) := by
      rw [hE, hR0]; ring
    rw [e]
    obtain ⟨kr, hkr⟩ : ∃ kr : ℝ, kr = k := ⟨_, rfl⟩
    have hk0 : (0 : ℝ) ≤ kr := by rw [hkr]; exact Nat.cast_nonneg k
    have hSW0 : 0 ≤ SW := by rw [hSW]; exact Finset.sum_nonneg fun t _ => hW _
    have hW0 := hW 0
    have hcard : ∀ x : ℝ, ∑ _t : Fin k, x = kr * x := fun x => by
      rw [hkr]; simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- basic facts
    have hq2 : ∀ t, q t ^ 2 ≤ 2 * W t := by
      intro t
      have h := hxq t (q t) (hq t)
      have h3 : q t ^ 2 * q t ≤ q t ^ 2 * (1 / 16) :=
        mul_le_mul_of_nonneg_left (hq16 t) (_root_.sq_nonneg (q t))
      have e1 : q t ^ 3 = q t ^ 2 * q t := by ring
      have e2 : q t * q t = q t ^ 2 := by ring
      rw [e1, e2] at h
      nlinarith only [h, h3, hW t, _root_.sq_nonneg (q t)]
    have hA0 : |a 0| ^ 3 ≤ W 0 := ha3 0
    have hAb : |A| ≤ kr / 2 := by
      rw [hA]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_sum fun (t : Fin k) (_ : t ∈ Finset.univ) => ha t.succ
      rw [hcard] at this; linarith
    have hCb : |C| ≤ 5 * kr / 16 := by
      rw [hC]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_sum fun (t : Fin k) (_ : t ∈ Finset.univ) =>
        (hc t.succ).trans (by linarith [hq16 t.succ] : 5 * q t.succ ≤ 5 / 16)
      rw [hcard] at this; linarith
    have hQ20 : 0 ≤ Q2 := by rw [hQ2]; exact Finset.sum_nonneg fun t _ => _root_.sq_nonneg _
    have hQ2b : Q2 ≤ kr / 4 := by
      rw [hQ2]
      have := Finset.sum_le_sum fun (t : Fin k) (_ : t ∈ Finset.univ) =>
        (show a t.succ ^ 2 ≤ 1 / 4 by
          rw [← sq_abs]
          calc |a t.succ| ^ 2 ≤ (1 / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (ha t.succ) 2
            _ = 1 / 4 := by norm_num)
      rw [hcard] at this; linarith
    have hA2 : A ^ 2 ≤ kr * Q2 := by rw [hA, hQ2, hkr]; exact BiasGeneral.sq_sum_le_fin (fun t => a t.succ)
    have hS2abs : |(A ^ 2 - Q2) / 2| ≤ (kr + 1) / 2 * Q2 := by
      rw [abs_le]; constructor <;> nlinarith only [_root_.sq_nonneg A, hA2, hQ20, mul_nonneg hk0 hQ20]
    have hS1b : |A + C + (A ^ 2 - Q2) / 2| ≤ kr + kr * (kr + 1) / 8 := by
      have h1 : (kr + 1) / 2 * Q2 ≤ (kr + 1) / 2 * (kr / 4) :=
        mul_le_mul_of_nonneg_left hQ2b (by positivity)
      calc |A + C + (A ^ 2 - Q2) / 2| ≤ |A| + |C| + |(A ^ 2 - Q2) / 2| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ ≤ kr / 2 + 5 * kr / 16 + (kr + 1) / 2 * (kr / 4) := by linarith
        _ ≤ kr + kr * (kr + 1) / 8 := by nlinarith only [hk0]
    -- |a0| Σ q_t ≤ kr W0 + SW, and so on
    have haq : |a 0| * ∑ t : Fin k, q t.succ ≤ kr * W 0 + SW := by
      rw [Finset.mul_sum, hSW, ← hcard, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun t _ => (hxq t.succ |a 0| (abs_nonneg _)).trans (by linarith)
    have hsumc : |C| ≤ 5 * ∑ t : Fin k, q t.succ := by
      rw [hC, Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hc _)
    have bC : |a 0 * C| ≤ 5 * (kr * W 0 + SW) := by
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_left hsumc (abs_nonneg (a 0))
      nlinarith only [this, haq]
    have haQ : |a 0| * Q2 ≤ kr * W 0 + SW := by
      rw [hQ2, Finset.mul_sum, hSW, ← hcard, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun t _ => ?_
      have h := amgm_xyy (abs_nonneg (a 0)) (abs_nonneg (a t.succ))
      rw [sq_abs] at h
      linarith [ha3 t.succ]
    have bS2 : |a 0 * ((A ^ 2 - Q2) / 2)| ≤ (kr + 1) / 2 * (kr * W 0 + SW) := by
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_left hS2abs (abs_nonneg (a 0))
      have h2 : |a 0| * ((kr + 1) / 2 * Q2) = (kr + 1) / 2 * (|a 0| * Q2) := by ring
      rw [h2] at this
      exact this.trans (mul_le_mul_of_nonneg_left haQ (by positivity))
    have hc0 : |c 0| ≤ 5 * q 0 := hc 0
    -- c0 · A
    have bcA : |c 0 * A| ≤ 5 * (SW + kr * W 0) := by
      have hsa : |A| ≤ ∑ t : Fin k, |a t.succ| := by
        rw [hA]; exact Finset.abs_sum_le_sum_abs _ _
      rw [abs_mul]
      have h1 : |c 0| * |A| ≤ 5 * q 0 * ∑ t : Fin k, |a t.succ| :=
        mul_le_mul hc0 hsa (abs_nonneg _) (by linarith [hq 0])
      have h2 : q 0 * ∑ t : Fin k, |a t.succ| ≤ SW + kr * W 0 := by
        rw [Finset.mul_sum, hSW, ← hcard, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun t _ => ?_
        have := hxq 0 |a t.succ| (abs_nonneg _)
        linarith [ha3 t.succ]
      nlinarith only [h1, h2]
    -- c0 · C
    have bcC : |c 0 * C| ≤ 25 * (kr * W 0 + SW) := by
      rw [abs_mul]
      have h1 : |c 0| * |C| ≤ 5 * q 0 * (5 * ∑ t : Fin k, q t.succ) :=
        mul_le_mul hc0 hsumc (abs_nonneg _) (by linarith [hq 0])
      have h2 : q 0 * ∑ t : Fin k, q t.succ ≤ kr * W 0 + SW := by
        rw [Finset.mul_sum, hSW, ← hcard, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun t _ => ?_
        nlinarith only [_root_.sq_nonneg (q 0 - q t.succ), hq2 0, hq2 t.succ]
      nlinarith only [h1, h2]
    -- c0 · S2
    have bcS : |c 0 * ((A ^ 2 - Q2) / 2)| ≤ 5 * (kr + 1) / 4 * (SW + kr * W 0) := by
      rw [abs_mul]
      have h1 : |c 0| * |(A ^ 2 - Q2) / 2| ≤ 5 * q 0 * ((kr + 1) / 2 * Q2) :=
        mul_le_mul hc0 hS2abs (abs_nonneg _) (by linarith [hq 0])
      have h2 : q 0 * Q2 ≤ (SW + kr * W 0) / 2 := by
        rw [hQ2, Finset.mul_sum, hSW, ← hcard]
        have : (∑ t : Fin k, W t.succ + ∑ _t : Fin k, W 0) / 2
            = ∑ t : Fin k, (W t.succ + W 0) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
        rw [this]
        refine Finset.sum_le_sum fun t _ => ?_
        have hx := hxq 0 |a t.succ| (abs_nonneg _)
        have hat := ha t.succ
        have h3 := ha3 t.succ
        have hsq : a t.succ ^ 2 = |a t.succ| * |a t.succ| := by rw [← sq_abs]; ring
        rw [hsq]
        have hq0 := hq 0
        have : q 0 * (|a t.succ| * |a t.succ|) ≤ q 0 * (|a t.succ| * (1 / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hat (abs_nonneg _)) hq0
        nlinarith only [this, hx, h3]
      have h3 : 5 * q 0 * ((kr + 1) / 2 * Q2) = 5 * (kr + 1) / 2 * (q 0 * Q2) := by ring
      rw [h3] at h1
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 5 * (kr + 1) / 2)
      nlinarith only [h1, this]
    have hR0b : |R0| ≤ W 0 := by rw [hR0]; exact hg 0
    have := step_cubic hk0 (BiasGeneral.gC_nonneg k) hW0 hSW0 IH hR0b (hg2 0) bC bS2 hS1b bcA bcC
      bcS
    have e2 : BiasGeneral.gC (k + 1) * (W 0 + SW)
        = (2 * BiasGeneral.gC k + 200 * (kr + 1) ^ 2) * (W 0 + SW) := by
      simp only [BiasGeneral.gC, hkr]
    rw [e2]
    exact this

/-! ## Part 3 (deterministic): one vertex, then Steps 1–3 for every `k` with a cubic remainder -/

/-- **Step 2 at one vertex with a cubic remainder, on the fixed event `max |ε| ≤ 1/8`.**
    `b = (P̃ε)_i`, `s = (P̃ε²)_i`, `t = (P̃|ε|³)_i`, `a = φ¹_i = -2ε_i + b`,
    `c = φ²_i = 3ε_i² - 3ε_i b + b² - s`, `q = ε_i² + s`, `W = 120 (|ε_i|³ + t)`,
    `γ_i = u_i / r_i`.  Then the hypotheses of `prod_cubic` hold at this vertex. -/
theorem vertex_cubic {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ) (ρ ε : Fin N → ℝ)
    (hK0 : ∀ i j, 0 ≤ K i j) (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1)
    (hεδ : ∀ i, |ε i| ≤ 1 / 8) (i : Fin N) {b s t γ W : ℝ}
    (hbd : b = 1 / (N : ℝ) * ∑ l, K i l * ε l)
    (hsd : s = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    (htd : t = 1 / (N : ℝ) * ∑ l, K i l * |ε l| ^ 3)
    (hγd : γ = 1 / ρ i * (1 / (1 / (N : ℝ) * ∑ l, K i l / ρ l)))
    (hW : W = 120 * (|ε i| ^ 3 + t)) :
    |γ - (1 + (-2 * ε i + b) + (3 * ε i ^ 2 - 3 * ε i * b + b ^ 2 - s))| ≤ W
    ∧ |-2 * ε i + b| ≤ 1 / 2 ∧ |-2 * ε i + b| ^ 3 ≤ W
    ∧ |3 * ε i ^ 2 - 3 * ε i * b + b ^ 2 - s| ≤ 5 * (ε i ^ 2 + s)
    ∧ 0 ≤ ε i ^ 2 + s ∧ ε i ^ 2 + s ≤ 1 / 16
    ∧ (∀ x : ℝ, 0 ≤ x → x * (ε i ^ 2 + s) ≤ x ^ 3 + W)
    ∧ |γ| ≤ 2 ∧ 0 ≤ t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  have hl : ∀ l, -(1 / 8 : ℝ) ≤ ε l ∧ ε l ≤ 1 / 8 := fun l => abs_le.mp (hεδ l)
  have hρe : ∀ l, ρ l = 1 + ε l := fun l => by rw [hε l]; ring
  have hρlo : 7 / 8 ≤ ρ i := by rw [hρe i]; linarith only [(hl i).1]
  have hρhi : ρ i ≤ 9 / 8 := by rw [hρe i]; linarith only [(hl i).2]
  have H := row_bounds hN (K i) ε (fun l => hK0 i l) (le_refl (1 / 8 : ℝ)) hεδ (hρ i) hρhi
  obtain ⟨h1, h2, h3, h4, _h5, h6⟩ := H
  obtain ⟨z, hz⟩ : ∃ z : ℝ,
      z = 1 / (N : ℝ) * ∑ l, K i l * (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 / (N : ℝ) * ∑ l, K i l / (1 + ε l) := ⟨_, rfl⟩
  rw [← hz, ← hR, ← hbd, ← hsd] at h6
  rw [← hbd] at h1 h2
  rw [← hsd] at h2 h3 h4
  -- t
  have hS0 : 0 ≤ ∑ l, K i l := Finset.sum_nonneg fun l _ => hK0 i l
  have hinvS : 1 / (N : ℝ) * ∑ l, K i l = ρ i := by rw [hρ i]; field_simp
  have ht0 : 0 ≤ t := htd ▸ mul_nonneg hinv.le (Finset.sum_nonneg fun l _ =>
    mul_nonneg (hK0 i l) (pow_nonneg (abs_nonneg _) 3))
  have hε3 : ∀ l, |ε l| ^ 3 ≤ 1 / 512 := fun l => by
    have := pow_le_pow_left₀ (abs_nonneg (ε l)) (hεδ l) 3; norm_num at this ⊢; linarith only [this]
  have ht : t ≤ 1 / 256 := by
    rw [htd]
    have h : 1 / (N : ℝ) * ∑ l, K i l * |ε l| ^ 3 ≤ 1 / (N : ℝ) * ∑ l, K i l * (1 / 512) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (hε3 l) (hK0 i l)) hinv.le
    have e : 1 / (N : ℝ) * ∑ l, K i l * (1 / 512) = ρ i / 512 := by
      rw [← Finset.sum_mul, ← mul_assoc, hinvS]; ring
    linarith only [h, e, hρhi]
  -- z
  have hϑ : ∀ l, |1 / (1 + ε l) - (1 - ε l + ε l ^ 2)| ≤ 8 / 7 * |ε l| ^ 3 := by
    intro l
    have h1' : 7 / 8 ≤ 1 + ε l := by linarith only [(hl l).1]
    have hne : 1 + ε l ≠ 0 := by linarith only [h1']
    have e1 : (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)) * (1 + ε l) = -(ε l * ε l ^ 2) := by
      field_simp; ring
    have e2 : |1 / (1 + ε l) - (1 - ε l + ε l ^ 2)| * (1 + ε l) = |ε l| ^ 3 := by
      have := congrArg abs e1
      rw [abs_mul, abs_neg, abs_mul, abs_of_pos (by linarith only [h1'] : 0 < 1 + ε l)] at this
      rw [this, abs_pow]; ring
    have e4 := mul_le_mul_of_nonneg_left h1' (abs_nonneg (1 / (1 + ε l) - (1 - ε l + ε l ^ 2)))
    nlinarith only [e2, e4, pow_nonneg (abs_nonneg (ε l)) 3]
  have hzb : |z| ≤ 2 * t := by
    have h1 : |∑ l, K i l * (1 / (1 + ε l) - (1 - ε l + ε l ^ 2))|
        ≤ ∑ l, K i l * (8 / 7 * |ε l| ^ 3) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [abs_mul, abs_of_nonneg (hK0 i l)]
      exact mul_le_mul_of_nonneg_left (hϑ l) (hK0 i l)
    have e1 : ∑ l, K i l * (8 / 7 * |ε l| ^ 3) = 8 / 7 * ∑ l, K i l * |ε l| ^ 3 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    have h2 : |z| ≤ 8 / 7 * t := by
      rw [hz, htd, abs_mul, abs_of_pos hinv]
      have := mul_le_mul_of_nonneg_left h1 hinv.le
      rw [e1] at this; linarith only [this]
    linarith only [h2, ht0]
  -- x s ≤ (3/8) x³ + (2/3) t
  have hxs' : ∀ x : ℝ, 0 ≤ x → x * s ≤ 3 / 8 * x ^ 3 + 2 / 3 * t := by
    intro x hx
    have hterm : ∀ l, K i l * (x * ε l ^ 2) ≤ K i l * (x ^ 3 / 3 + 2 / 3 * |ε l| ^ 3) := by
      intro l
      refine mul_le_mul_of_nonneg_left ?_ (hK0 i l)
      have h := mul_nonneg (_root_.sq_nonneg (x - |ε l|)) (add_nonneg hx
        (mul_nonneg zero_le_two (abs_nonneg (ε l))))
      have : ε l ^ 2 = |ε l| ^ 2 := (sq_abs _).symm
      rw [this]; nlinarith only [h, pow_nonneg hx 3, pow_nonneg (abs_nonneg (ε l)) 3]
    have hsum := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hterm l
    have e1 : x * s = 1 / (N : ℝ) * ∑ l, K i l * (x * ε l ^ 2) := by
      rw [hsd, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e0 : ∑ l, K i l * (x ^ 3 / 3 + 2 / 3 * |ε l| ^ 3)
        = (∑ l, K i l) * (x ^ 3 / 3) + 2 / 3 * ∑ l, K i l * |ε l| ^ 3 := by
      rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    have e2 : 1 / (N : ℝ) * ∑ l, K i l * (x ^ 3 / 3 + 2 / 3 * |ε l| ^ 3)
        = ρ i * (x ^ 3 / 3) + 2 / 3 * t := by
      rw [e0, htd, mul_add, ← mul_assoc, hinvS]; ring
    have h3' := mul_le_mul_of_nonneg_left hsum hinv.le
    have h4' : ρ i * (x ^ 3 / 3) ≤ 9 / 8 * (x ^ 3 / 3) :=
      mul_le_mul_of_nonneg_right hρhi (by positivity)
    linarith only [e1, e2, h3', h4']
  have hxs : ∀ x : ℝ, 0 ≤ x → x * s ≤ x ^ 3 + t := fun x hx => by
    have := hxs' x hx; nlinarith only [this, pow_nonneg hx 3, ht0]
  -- |b|³ ≤ 2t
  have hb3 : |b| ^ 3 ≤ 2 * t := by
    have hbs := hxs' |b| (abs_nonneg b)
    have e : |b| ^ 3 = |b| * b ^ 2 := by rw [← sq_abs b]; ring
    have h := mul_le_mul_of_nonneg_left h2 (abs_nonneg b)
    nlinarith only [e, hbs, h, pow_nonneg (abs_nonneg b) 3, ht0]
  -- γ
  have hRpos : 0 < R := by
    obtain ⟨z1, _⟩ := abs_le.mp hzb
    obtain ⟨b1, b2⟩ := abs_le.mp h1
    rw [h6]; linarith only [hρlo, b2, z1, h3, ht]
  have hρi : ρ i ≠ 0 := by linarith only [hρlo]
  have hsumR : 1 / (N : ℝ) * ∑ l, K i l / ρ l = R := by
    rw [hR]
    have : ∑ l, K i l / ρ l = ∑ l, K i l / (1 + ε l) :=
      Finset.sum_congr rfl fun l _ => by rw [hρe l]
    rw [this]
  have hγR : γ = 1 / ρ i * (1 / R) := by rw [hγd, hsumR]
  have hγ : γ * ((1 + ε i) * (1 + (ε i - b + (s + z)))) = 1 := by
    have e : 1 + (ε i - b + (s + z)) = R := by rw [h6, hρe i]; ring
    rw [e, ← hρe i, hγR]
    field_simp
  have hg := gamma_cubic (hεδ i) (by linarith only [h1]) h3 (by linarith only [h4]) ht0 ht hzb hxs hγ
  have hA3 : 0 ≤ |ε i| ^ 3 := pow_nonneg (abs_nonneg _) 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ht0⟩
  · rw [hW]
    have e : 1 + (-2 * ε i + b) + (3 * ε i ^ 2 - 3 * ε i * b + b ^ 2 - s)
        = 1 - 2 * ε i + b + 3 * ε i ^ 2 - 3 * ε i * b + b ^ 2 - s := by ring
    rw [e]; refine hg.trans ?_; linarith only [hb3, hA3, ht0]
  · obtain ⟨b1, b2⟩ := abs_le.mp h1
    rw [abs_le]; constructor <;> linarith only [b1, b2, (hl i).1, (hl i).2]
  · rw [hW]
    have h := cube_sum3 (abs_nonneg (ε i)) (abs_nonneg (ε i)) (abs_nonneg b)
    have hab : |-2 * ε i + b| ≤ |ε i| + |ε i| + |b| := by
      calc |-2 * ε i + b| ≤ |-2 * ε i| + |b| := abs_add_le _ _
        _ = |ε i| + |ε i| + |b| := by rw [abs_mul, show |(-2 : ℝ)| = 2 by norm_num]; ring
    have := pow_le_pow_left₀ (abs_nonneg _) hab 3
    nlinarith only [this, h, hb3, hA3, ht0]
  · rw [abs_le]
    constructor
    · nlinarith only [_root_.sq_nonneg (ε i - b), _root_.sq_nonneg (ε i + b), h2, h3,
        _root_.sq_nonneg (ε i), _root_.sq_nonneg b]
    · nlinarith only [_root_.sq_nonneg (ε i - b), _root_.sq_nonneg (ε i + b), h2, h3,
        _root_.sq_nonneg (ε i), _root_.sq_nonneg b]
  · exact add_nonneg (_root_.sq_nonneg _) h3
  · have : ε i ^ 2 ≤ (1 / 8) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hεδ i) 2
    linarith only [this, h4]
  · intro x hx
    rw [hW]
    have h1' : x * ε i ^ 2 ≤ x ^ 3 / 3 + 2 / 3 * |ε i| ^ 3 := by
      have h := mul_nonneg (_root_.sq_nonneg (x - |ε i|)) (add_nonneg hx
        (mul_nonneg zero_le_two (abs_nonneg (ε i))))
      have : ε i ^ 2 = |ε i| ^ 2 := (sq_abs _).symm
      rw [this]; nlinarith only [h, pow_nonneg hx 3, hA3]
    have := hxs' x hx
    nlinarith only [h1', this, pow_nonneg hx 3, hA3, ht0]
  · rw [hγR]
    have hR' : 7 / 10 ≤ R := by
      obtain ⟨z1, _⟩ := abs_le.mp hzb
      obtain ⟨b1, b2⟩ := abs_le.mp h1
      rw [h6]; linarith only [hρlo, b2, z1, h3, ht]
    have hpos : 0 < 1 / ρ i * (1 / R) := by positivity
    rw [abs_of_pos hpos]
    have e1 : 1 / ρ i ≤ 8 / 7 := by
      rw [div_le_iff₀ (by linarith only [hρlo])]; linarith only [hρlo]
    have e2 : 1 / R ≤ 10 / 7 := by
      rw [div_le_iff₀ hRpos]; linarith only [hR']
    have := mul_le_mul e1 e2 (by positivity) (by norm_num)
    linarith only [this]

/-- **Steps 1–3 of the proof of `prop:bias` for every `k = n + 1`, deterministic, cubic
    remainder.** Hypotheses as in `BiasGeneral.trace_expansion` with the fixed threshold
    `|ε_i| ≤ 1/8`; the remainder is `gC(k) k (9/8)^n · 255 · M (1/N) ∑ |ε_i|³` instead of
    `gC(k) k (9/8)^n (17/8) δ M (1/N) ∑ ε_i²`. -/
theorem trace_expansion3 {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ) (ρ ε bv sv : Fin N → ℝ)
    {M : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hKM : ∀ i j, K i j ≤ M) (hsym : ∀ i j, K i j = K j i)
    (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1)
    (hbv : ∀ i, bv i = 1 / (N : ℝ) * ∑ l, K i l * ε l)
    (hsv : ∀ i, sv i = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    (hεδ : ∀ i, |ε i| ≤ 1 / 8) (n : ℕ) :
    |((walkMatrix K ρ) ^ (n + 1)).trace
        - ∑ v : Fin (n + 1) → Fin N, cw (fun i j => K i j / (N : ℝ)) v
          * (1 + ∑ t, ((-2 * ε (v t) + bv (v t))
                + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
              + ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2
                - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2) / 2)|
      ≤ gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * 255
          * (M * (1 / (N : ℝ) * ∑ i, |ε i| ^ 3)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv : 0 < 1 / (N : ℝ) := by positivity
  have hM0 : 0 ≤ M := (hK0 ⟨0, hN⟩ ⟨0, hN⟩).trans (hKM _ _)
  have hl : ∀ l, -(1 / 8 : ℝ) ≤ ε l ∧ ε l ≤ 1 / 8 := fun l => abs_le.mp (hεδ l)
  have hρe : ∀ l, ρ l = 1 + ε l := fun l => by rw [hε l]; ring
  have hρlo : ∀ l, 7 / 8 ≤ ρ l := fun l => by rw [hρe l]; linarith only [(hl l).1]
  have hρhi : ∀ l, ρ l ≤ 9 / 8 := fun l => by rw [hρe l]; linarith only [(hl l).2]
  have hρ0 : ∀ l, ρ l ≠ 0 := fun l => by linarith only [hρlo l]
  obtain ⟨γ, hγd⟩ : ∃ γ : Fin N → ℝ,
      γ = fun i => 1 / ρ i * (1 / (1 / (N : ℝ) * ∑ l, K i l / ρ l)) := ⟨_, rfl⟩
  obtain ⟨tv, htv⟩ : ∃ tv : Fin N → ℝ, tv = fun i => 1 / (N : ℝ) * ∑ l, K i l * |ε l| ^ 3 :=
    ⟨_, rfl⟩
  obtain ⟨Wv, hWv⟩ : ∃ Wv : Fin N → ℝ, Wv = fun i => 120 * (|ε i| ^ 3 + tv i) := ⟨_, rfl⟩
  have hv : ∀ i, |γ i - (1 + (-2 * ε i + bv i)
        + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))| ≤ Wv i
      ∧ |-2 * ε i + bv i| ≤ 1 / 2 ∧ |-2 * ε i + bv i| ^ 3 ≤ Wv i
      ∧ |3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i| ≤ 5 * (ε i ^ 2 + sv i)
      ∧ 0 ≤ ε i ^ 2 + sv i ∧ ε i ^ 2 + sv i ≤ 1 / 16
      ∧ (∀ x : ℝ, 0 ≤ x → x * (ε i ^ 2 + sv i) ≤ x ^ 3 + Wv i)
      ∧ |γ i| ≤ 2 ∧ 0 ≤ tv i := by
    intro i
    exact vertex_cubic hN K ρ ε hK0 hρ hε hεδ i (hbv i) (hsv i) (by rw [htv]) (by rw [hγd])
      (by rw [hWv])
  have hW0 : ∀ i, 0 ≤ Wv i := fun i => by
    rw [hWv]; have := (hv i).2.2.2.2.2.2.2.2
    have := pow_nonneg (abs_nonneg (ε i)) 3
    simp only; positivity
  -- the trace as a sum over closed walks
  obtain ⟨A, hA⟩ : ∃ A : Fin N → Fin N → ℝ, A = fun i j => K i j / (N : ℝ) := ⟨_, rfl⟩
  have htr : ((walkMatrix K ρ) ^ (n + 1)).trace
      = ∑ v : Fin (n + 1) → Fin N, cw A v * ∏ t, γ (v t) := by
    have e := BiasVariance2.trace_pow_gamma K ρ hρ0 (n + 1)
    rw [← hγd] at e
    have hB : (Matrix.of (fun i j => K i j / (N : ℝ)) * Matrix.diagonal γ : Matrix (Fin N) (Fin N) ℝ)
        = fun i j => A i j * γ j := by
      funext i j; rw [Matrix.mul_diagonal, Matrix.of_apply, hA]
    rw [e, hB, trace_pow_cw]
    exact Finset.sum_congr rfl fun v _ => cw_mul_diag A γ v
  rw [htr, ← hA]
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  have hA0 : ∀ i j, 0 ≤ A i j := fun i j => by rw [hA]; exact div_nonneg (hK0 i j) hNpos.le
  have hAM : ∀ i j, A i j ≤ M / N := fun i j => by
    rw [hA]; exact div_le_div_of_nonneg_right (hKM i j) hNpos.le
  have hrow : ∀ i, ∑ j, A i j ≤ 9 / 8 := fun i => by
    have : ∑ j, A i j = ρ i := by
      rw [hA]; simp only; rw [← Finset.sum_div, hρ i]; field_simp
    rw [this]; exact hρhi i
  have hcolt : ∑ i, tv i ≤ 9 / 8 * ∑ i, |ε i| ^ 3 := by
    simp only [htv]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    rw [← Finset.sum_mul]
    have : ∑ i, K i l = N * ρ l := by
      rw [← hρ l]; exact Finset.sum_congr rfl fun i _ => hsym i l
    rw [this]
    have h1 := mul_le_mul_of_nonneg_right (hρhi l) (pow_nonneg (abs_nonneg (ε l)) 3)
    have e : 1 / (N : ℝ) * (N * ρ l * |ε l| ^ 3) = ρ l * |ε l| ^ 3 := by field_simp
    rw [e]; exact h1
  have hSW : ∑ i, Wv i ≤ 255 * ∑ i, |ε i| ^ 3 := by
    rw [hWv]; simp only
    rw [← Finset.mul_sum, Finset.sum_add_distrib]; linarith only [hcolt]
  have hterm : ∀ v : Fin (n + 1) → Fin N,
      |cw A v * (∏ t, γ (v t)
          - (1 + ∑ t, ((-2 * ε (v t) + bv (v t))
                + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
              + ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2
                - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2) / 2))|
        ≤ gC (n + 1) * ∑ t, cw A v * Wv (v t) := by
    intro v
    have hp := prod_cubic (n + 1) (fun t => γ (v t)) (fun t => -2 * ε (v t) + bv (v t))
      (fun t => 3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t))
      (fun t => ε (v t) ^ 2 + sv (v t)) (fun t => Wv (v t)) (fun t => hW0 _)
      (fun t => (hv _).2.2.2.2.1) (fun t => (hv _).2.2.2.2.2.1)
      (fun t => (hv (v t)).1) (fun t => (hv _).2.1) (fun t => (hv _).2.2.1)
      (fun t => (hv _).2.2.2.1) (fun t x hx => (hv _).2.2.2.2.2.2.1 x hx)
      (fun t => (hv _).2.2.2.2.2.2.2.1)
    rw [abs_mul, abs_of_nonneg (cw_nonneg A hA0 v), ← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left hp (cw_nonneg A hA0 v)
    exact h.trans (le_of_eq (by ring))
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => hterm v)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hpos : ∀ t : Fin (n + 1), ∑ v : Fin (n + 1) → Fin N, cw A v * Wv (v t)
      ≤ M / N * (9 / 8) ^ n * ∑ i, Wv i := fun t =>
    sum_cw_pos_le A hA0 hAM hrow (div_nonneg hM0 hNpos.le) (by norm_num) Wv hW0 t
  have hsum := Finset.sum_le_sum fun (t : Fin (n + 1)) (_ : t ∈ Finset.univ) => hpos t
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hG := gC_nonneg (n + 1)
  have h1 := mul_le_mul_of_nonneg_left hsum hG
  have hc : 0 ≤ ((n + 1 : ℕ) : ℝ) * (M / N * (9 / 8) ^ n) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (div_nonneg hM0 hNpos.le) (by positivity))
  have h2 : ((n + 1 : ℕ) : ℝ) * (M / N * (9 / 8) ^ n * ∑ i, Wv i)
      ≤ ((n + 1 : ℕ) : ℝ) * (M / N * (9 / 8) ^ n) * (255 * ∑ i, |ε i| ^ 3) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hSW hc
  have h3 := mul_le_mul_of_nonneg_left h2 hG
  refine h1.trans (h3.trans (le_of_eq ?_))
  push_cast
  field_simp

/-- **`eq:bias-trace` of `prop:bias` for every `k = n + 1` with a cubic remainder** (form of
    `BiasGeneral.trace_expansion_paper`, fixed threshold `1/8`). -/
theorem trace_expansion_paper3 {N : ℕ} (hN : 0 < N) (K : Fin N → Fin N → ℝ)
    (ρ ε bv sv : Fin N → ℝ)
    {M : ℝ} (hK0 : ∀ i j, 0 ≤ K i j) (hKM : ∀ i j, K i j ≤ M) (hsym : ∀ i j, K i j = K j i)
    (hρ : ∀ i, ∑ l, K i l = N * ρ i) (hε : ∀ i, ε i = ρ i - 1)
    (hbv : ∀ i, bv i = 1 / (N : ℝ) * ∑ l, K i l * ε l)
    (hsv : ∀ i, sv i = 1 / (N : ℝ) * ∑ l, K i l * ε l ^ 2)
    (hεδ : ∀ i, |ε i| ≤ 1 / 8) (n : ℕ) :
    |((walkMatrix K ρ) ^ (n + 1)).trace
        - ((Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)).trace
          + ((n : ℝ) + 1) * ∑ i, (Matrix.of (fun i j => K i j / (N : ℝ)) ^ (n + 1)) i i
              * ((-2 * ε i + bv i) + (3 * ε i ^ 2 - 3 * ε i * bv i + bv i ^ 2 - sv i))
          + ((n : ℝ) + 1) / 2 * ∑ l ∈ Finset.univ.erase (0 : Fin (n + 1)),
              ∑ v : Fin (n + 1) → Fin N, cw (fun i j => K i j / (N : ℝ)) v
                * ((-2 * ε (v 0) + bv (v 0)) * (-2 * ε (v l) + bv (v l))))|
      ≤ gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * 255
          * (M * (1 / (N : ℝ) * ∑ i, |ε i| ^ 3)) := by
  have h := trace_expansion3 hN K ρ ε bv sv hK0 hKM hsym hρ hε hbv hsv hεδ n
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin N) (Fin N) ℝ, B = Matrix.of (fun i j => K i j / (N : ℝ)) :=
    ⟨_, rfl⟩
  have hBf : (fun i j => K i j / (N : ℝ)) = (B : Fin N → Fin N → ℝ) := by rw [hB]; rfl
  rw [hBf] at h
  rw [← hB, hBf]
  have e0 := trace_pow_cw B n
  have e1 := sum_cw_lin B (n := n) (fun i => (-2 * ε i + bv i) + (3 * ε i ^ 2 - 3 * ε i * bv i
    + bv i ^ 2 - sv i))
  have e2 := sum_cw_pairs (B : Fin N → Fin N → ℝ) (n := n) (fun i => -2 * ε i + bv i)
  have esplit : ∑ v : Fin (n + 1) → Fin N, cw B v
        * (1 + ∑ t, ((-2 * ε (v t) + bv (v t))
              + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
            + ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2 - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2) / 2)
      = ∑ v : Fin (n + 1) → Fin N, cw B v
        + ∑ v : Fin (n + 1) → Fin N, cw B v * ∑ t, ((-2 * ε (v t) + bv (v t))
              + (3 * ε (v t) ^ 2 - 3 * ε (v t) * bv (v t) + bv (v t) ^ 2 - sv (v t)))
        + (∑ v : Fin (n + 1) → Fin N, cw B v
            * ((∑ t, (-2 * ε (v t) + bv (v t))) ^ 2 - ∑ t, (-2 * ε (v t) + bv (v t)) ^ 2)) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [esplit, e1, e2, ← e0] at h
  refine (le_of_eq ?_).trans h
  congr 1
  ring

/-! ## Part 4: moments of the normalisation errors (Task (1)) -/

section Moments

theorem bm_pow {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (hf : BM f) (m : ℕ) :
    BM (fun ω => f ω ^ m) := by
  obtain ⟨Bf, hBf⟩ := hf.bdd
  exact ⟨hf.meas.pow_const m, Bf ^ m, fun ω => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBf ω) m⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {c κ₂ : G → ℝ}
  {B c3 c4 : ℝ}

/-- A power of a partial row sum against a `c`-edge to a fresh index has mean zero. -/
theorem zero_moment [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (a j : ℕ) (R : Finset ℕ) (ha : a ∉ R) (hj : j ∉ R)
    (hja : j ≠ a) (m : ℕ) :
    ∫ ω, (∑ v ∈ R, c (X a ω - X v ω)) ^ m * c (X a ω - X j ω) ∂μ = 0 := by
  classical
  have hjT : j ∉ insert a R := by
    rw [Finset.mem_insert, not_or]; exact ⟨hja, hj⟩
  let F : (↥(insert a R) → G) → ℝ := fun y =>
    (∑ v ∈ R.attach, c (y ⟨a, Finset.mem_insert_self a R⟩
      - y ⟨v.1, Finset.mem_insert_of_mem v.2⟩)) ^ m
  have hF : Measurable F := by
    refine Measurable.pow_const ?_ m
    refine Finset.measurable_sum _ fun v _ => H.c_meas.comp ?_
    exact (measurable_pi_apply _).sub (measurable_pi_apply _)
  have hB0 : 0 ≤ B := H.B_nonneg
  have hFb : ∀ y, |F y| ≤ (R.card * B) ^ m := by
    intro y
    show |(∑ v ∈ R.attach, c (y ⟨a, Finset.mem_insert_self a R⟩
      - y ⟨v.1, Finset.mem_insert_of_mem v.2⟩)) ^ m| ≤ _
    rw [abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ m
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_sum fun (v : R) (_ : v ∈ R.attach) =>
      H.bound (y ⟨a, Finset.mem_insert_self a R⟩ - y ⟨v.1, Finset.mem_insert_of_mem v.2⟩)
    simp only [Finset.sum_const, Finset.card_attach, nsmul_eq_mul] at this
    exact this
  have h := H.tail_single (insert a R) ⟨a, Finset.mem_insert_self a R⟩ j hjT F hF hFb
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  show (∑ v ∈ R, c (X a ω - X v ω)) ^ m * c (X a ω - X j ω)
    = (∑ v ∈ R.attach, c (X a ω - X v.1 ω)) ^ m * c (X a ω - X j ω)
  rw [Finset.sum_attach R (fun v => c (X a ω - X v ω))]

/-- **Second and fourth moments of a partial row sum** over indices `R ∌ a`:
    `E S² ≤ |R| B²`, `E S⁴ ≤ 7 |R|² B⁴`, `S = ∑_{v ∈ R} c(X_a - X_v)`. -/
theorem partial_moments [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (a : ℕ) (R : Finset ℕ) (ha : a ∉ R) :
    ∫ ω, (∑ v ∈ R, c (X a ω - X v ω)) ^ 2 ∂μ ≤ R.card * B ^ 2
    ∧ ∫ ω, (∑ v ∈ R, c (X a ω - X v ω)) ^ 4 ∂μ ≤ 7 * (R.card : ℝ) ^ 2 * B ^ 4 := by
  classical
  have hB0 : 0 ≤ B := H.B_nonneg
  induction R using Finset.induction_on with
  | empty => simp
  | insert j R hjR ih =>
    have haR : a ∉ R := fun h => ha (Finset.mem_insert_of_mem h)
    have hja : j ≠ a := fun h => ha (h ▸ Finset.mem_insert_self j R)
    obtain ⟨ih2, ih4⟩ := ih haR
    obtain ⟨S, hS⟩ : ∃ S : Ω → ℝ, S = fun ω => ∑ v ∈ R, c (X a ω - X v ω) := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y : Ω → ℝ, Y = fun ω => c (X a ω - X j ω) := ⟨_, rfl⟩
    have bS : BM S := by rw [hS]; exact BM.sum _ _ fun v _ => H.bmc a v
    have bY : BM Y := by rw [hY]; exact H.bmc a j
    have hYb : ∀ ω, Y ω ^ 2 ≤ B ^ 2 := fun ω => by
      rw [hY, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (H.bound _) 2
    have hsplit : ∀ ω, ∑ v ∈ insert j R, c (X a ω - X v ω) = S ω + Y ω := fun ω => by
      rw [Finset.sum_insert hjR, hS, hY, add_comm]
    simp_rw [hsplit]
    have ih2' : ∫ ω, S ω ^ 2 ∂μ ≤ R.card * B ^ 2 := by rw [hS]; exact ih2
    have ih4' : ∫ ω, S ω ^ 4 ∂μ ≤ 7 * (R.card : ℝ) ^ 2 * B ^ 4 := by rw [hS]; exact ih4
    have z1 : ∫ ω, S ω * Y ω ∂μ = 0 := by
      have := zero_moment H a j R haR hjR hja 1
      simp only [pow_one] at this
      rw [hS, hY]; exact this
    have z3 : ∫ ω, S ω ^ 3 * Y ω ∂μ = 0 := by
      have := zero_moment H a j R haR hjR hja 3
      rw [hS, hY]; exact this
    have hcard : ((insert j R).card : ℝ) = R.card + 1 := by
      rw [Finset.card_insert_of_notMem hjR]; push_cast; ring
    rw [hcard]
    have iS2 := bS.sqr.integrable (μ := μ)
    have iSY := (bS.mul bY).integrable (μ := μ)
    have iY2 := bY.sqr.integrable (μ := μ)
    constructor
    · have e : ∀ ω, (S ω + Y ω) ^ 2 = S ω ^ 2 + 2 * (S ω * Y ω) + Y ω ^ 2 := fun ω => by ring
      simp_rw [e]
      rw [integral_add (show Integrable (fun ω => S ω ^ 2 + 2 * (S ω * Y ω)) μ from
          iS2.add (iSY.const_mul 2)) iY2, integral_add iS2 (iSY.const_mul 2),
        integral_const_mul, z1]
      have hY2 : ∫ ω, Y ω ^ 2 ∂μ ≤ B ^ 2 := by
        calc ∫ ω, Y ω ^ 2 ∂μ ≤ ∫ _ω, B ^ 2 ∂μ := integral_mono iY2 (integrable_const _) hYb
          _ = B ^ 2 := by simp
      nlinarith only [ih2', hY2]
    · have iS4 := (bm_pow bS 4).integrable (μ := μ)
      have iS3Y := ((bm_pow bS 3).mul bY).integrable (μ := μ)
      obtain ⟨Z, hZ⟩ : ∃ Z : Ω → ℝ,
          Z = fun ω => 6 * (S ω ^ 2 * Y ω ^ 2) + 4 * (S ω * Y ω ^ 3) + Y ω ^ 4 := ⟨_, rfl⟩
      have bZ : BM Z := by
        rw [hZ]
        exact ((BM.const_mul 6 ((bm_pow bS 2).mul (bm_pow bY 2))).add
          (BM.const_mul 4 (bS.mul (bm_pow bY 3)))).add (bm_pow bY 4)
      have e : ∀ ω, (S ω + Y ω) ^ 4 = S ω ^ 4 + 4 * (S ω ^ 3 * Y ω) + Z ω := fun ω => by
        simp only [hZ]; ring
      simp_rw [e]
      rw [integral_add (show Integrable (fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * Y ω)) μ from
          iS4.add (iS3Y.const_mul 4)) bZ.integrable,
        integral_add iS4 (iS3Y.const_mul 4), integral_const_mul, z3]
      have hZb : ∀ ω, Z ω ≤ 8 * B ^ 2 * S ω ^ 2 + 3 * B ^ 4 := by
        intro ω
        have h1 := hYb ω
        have h2 : Y ω ^ 4 ≤ B ^ 4 := by
          have : Y ω ^ 4 = (Y ω ^ 2) ^ 2 := by ring
          rw [this, show B ^ 4 = (B ^ 2) ^ 2 by ring]
          exact pow_le_pow_left₀ (_root_.sq_nonneg _) h1 2
        have h3 := mul_le_mul_of_nonneg_left h1 (_root_.sq_nonneg (S ω))
        simp only [hZ]
        nlinarith only [mul_nonneg (_root_.sq_nonneg (Y ω)) (_root_.sq_nonneg (S ω - Y ω)), h2, h3]
      have hZi : ∫ ω, Z ω ∂μ ≤ 8 * B ^ 2 * ∫ ω, S ω ^ 2 ∂μ + 3 * B ^ 4 := by
        calc ∫ ω, Z ω ∂μ ≤ ∫ ω, (8 * B ^ 2 * S ω ^ 2 + 3 * B ^ 4) ∂μ :=
              integral_mono bZ.integrable ((iS2.const_mul _).add (integrable_const _)) hZb
          _ = 8 * B ^ 2 * ∫ ω, S ω ^ 2 ∂μ + 3 * B ^ 4 := by
              rw [integral_add (iS2.const_mul _) (integrable_const _), integral_const_mul]
              simp
      have hB4 : 0 ≤ B ^ 4 := by positivity
      have hr : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
      have h8 := mul_le_mul_of_nonneg_left ih2' (by positivity : (0 : ℝ) ≤ 8 * B ^ 2)
      nlinarith only [ih4', hZi, h8, mul_nonneg hr hB4]

end Moments

section RowMoments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {G : Type*} [AddCommGroup G]
  [MeasurableSpace G] [MeasurableSub₂ G] {ν : Measure G} {X : ℕ → Ω → G} {c κ₂ : G → ℝ}
  {B c3 c4 : ℝ}

/-- **Moments of the row sums** `Nε_a = Hrow c X N a` (`a < N`, self-loop term included):
    `E (Nε_a)² ≤ 4 N B²`, `E (Nε_a)⁴ ≤ 64 N² B⁴`, `E |Nε_a|³ ≤ 34 N √N B³`.  In terms of
    `ε_a`: `E ε_a² ≤ 4B²/N`, `E ε_a⁴ ≤ 64 B⁴/N²`, `E |ε_a|³ ≤ 34 B³/N^{3/2}` (Task (1)). -/
theorem hrow_moments [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : BVK μ ν X c κ₂ B c3 c4) (N a : ℕ) (ha : a < N) :
    ∫ ω, Hrow c X N a ω ^ 2 ∂μ ≤ 4 * N * B ^ 2
    ∧ ∫ ω, Hrow c X N a ω ^ 4 ∂μ ≤ 64 * (N : ℝ) ^ 2 * B ^ 4
    ∧ ∫ ω, |Hrow c X N a ω| ^ 3 ∂μ ≤ 34 * (N * Real.sqrt N) * B ^ 3 := by
  classical
  have hB1 : 1 ≤ B := H.B_one
  have hB0 : 0 ≤ B := H.B_nonneg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.one_le_of_lt ha)
  set R := (Finset.range N).erase a with hR
  have haR : a ∉ R := Finset.notMem_erase a _
  have hcardR : (R.card : ℝ) ≤ N := by
    have : R.card ≤ N := (Finset.card_erase_le).trans (Finset.card_range N).le
    exact_mod_cast this
  obtain ⟨m2, m4⟩ := partial_moments H a R haR
  obtain ⟨S, hS⟩ : ∃ S : Ω → ℝ, S = fun ω => ∑ v ∈ R, c (X a ω - X v ω) := ⟨_, rfl⟩
  replace m2 : ∫ ω, S ω ^ 2 ∂μ ≤ R.card * B ^ 2 := by rw [hS]; exact m2
  replace m4 : ∫ ω, S ω ^ 4 ∂μ ≤ 7 * (R.card : ℝ) ^ 2 * B ^ 4 := by rw [hS]; exact m4
  have hsplit : ∀ ω, Hrow c X N a ω = c 0 + S ω := fun ω => by
    unfold Hrow
    rw [hS, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr ha), sub_self]
  have bS : BM S := by rw [hS]; exact BM.sum _ _ fun v _ => H.bmc a v
  have bH : BM (Hrow c X N a) := H.bmH N a
  have hc0 : |c 0| ≤ B := H.bound 0
  have hc02 : c 0 ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc0 2
  have hc04 : c 0 ^ 4 ≤ B ^ 4 := by
    have : c 0 ^ 4 = (c 0 ^ 2) ^ 2 := by ring
    rw [this, show B ^ 4 = (B ^ 2) ^ 2 by ring]
    exact pow_le_pow_left₀ (_root_.sq_nonneg _) hc02 2
  have iS2 := (bm_pow bS 2).integrable (μ := μ)
  have iS4 := (bm_pow bS 4).integrable (μ := μ)
  have iH2 := (bm_pow bH 2).integrable (μ := μ)
  have iH4 := (bm_pow bH 4).integrable (μ := μ)
  have h2 : ∫ ω, Hrow c X N a ω ^ 2 ∂μ ≤ 4 * N * B ^ 2 := by
    have hpt : ∀ ω, Hrow c X N a ω ^ 2 ≤ 2 * B ^ 2 + 2 * S ω ^ 2 := fun ω => by
      rw [hsplit]; nlinarith only [hc02, _root_.sq_nonneg (c 0 - S ω)]
    have := integral_mono iH2 (show Integrable (fun ω => 2 * B ^ 2 + 2 * S ω ^ 2) μ from
      (integrable_const _).add (iS2.const_mul 2)) hpt
    rw [integral_add (integrable_const _) (show Integrable (fun ω => 2 * S ω ^ 2) μ from iS2.const_mul 2),
      integral_const_mul] at this
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul, smul_eq_mul, one_mul] at this
    have h1 : (R.card : ℝ) * B ^ 2 ≤ N * B ^ 2 := mul_le_mul_of_nonneg_right hcardR (by positivity)
    nlinarith only [this, m2, h1, hN1, _root_.sq_nonneg B]
  have h4 : ∫ ω, Hrow c X N a ω ^ 4 ∂μ ≤ 64 * (N : ℝ) ^ 2 * B ^ 4 := by
    have hpt : ∀ ω, Hrow c X N a ω ^ 4 ≤ 8 * B ^ 4 + 8 * S ω ^ 4 := fun ω => by
      rw [hsplit]
      have h : (c 0 + S ω) ^ 4 ≤ 8 * (c 0 ^ 4 + S ω ^ 4) := by
        nlinarith only [_root_.sq_nonneg (c 0 - S ω), _root_.sq_nonneg (c 0 + S ω),
          mul_nonneg (_root_.sq_nonneg (c 0 - S ω)) (_root_.sq_nonneg (c 0 + S ω)),
          _root_.sq_nonneg (c 0 ^ 2 - S ω ^ 2), _root_.sq_nonneg (c 0 * S ω)]
      linarith only [h, hc04]
    have := integral_mono iH4 (show Integrable (fun ω => 8 * B ^ 4 + 8 * S ω ^ 4) μ from
      (integrable_const _).add (iS4.const_mul 8)) hpt
    rw [integral_add (integrable_const _) (show Integrable (fun ω => 8 * S ω ^ 4) μ from iS4.const_mul 8),
      integral_const_mul] at this
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul, smul_eq_mul, one_mul] at this
    have hc2 : (R.card : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardR 2
    have h1 : 7 * (R.card : ℝ) ^ 2 * B ^ 4 ≤ 7 * (N : ℝ) ^ 2 * B ^ 4 := by
      have := mul_le_mul_of_nonneg_right hc2 (by positivity : (0 : ℝ) ≤ 7 * B ^ 4)
      linarith only [this]
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1]
    have hB4 : 0 ≤ B ^ 4 := by positivity
    nlinarith only [this, m4, h1, hN2, hB4]
  refine ⟨h2, h4, ?_⟩
  -- the third absolute moment
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith only [hN1])
  have hsqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith only [hN1])
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.sqrt N * B := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; exact mul_pos hsq (by linarith only [hB1])
  have hpt : ∀ ω, |Hrow c X N a ω| ^ 3
      ≤ 1 / (2 * l) * Hrow c X N a ω ^ 4 + l / 2 * Hrow c X N a ω ^ 2 := by
    intro ω
    obtain ⟨y, hy⟩ : ∃ y, y = |Hrow c X N a ω| := ⟨_, rfl⟩
    have e4 : Hrow c X N a ω ^ 4 = y ^ 4 := by
      rw [hy, show |Hrow c X N a ω| ^ 4 = (|Hrow c X N a ω| ^ 2) ^ 2 by ring, sq_abs]; ring
    have e2 : Hrow c X N a ω ^ 2 = y ^ 2 := by rw [hy, sq_abs]
    rw [e4, e2, ← hy]
    have h0 : 0 ≤ y ^ 2 * (y - l) ^ 2 := mul_nonneg (_root_.sq_nonneg _) (_root_.sq_nonneg _)
    have e : 1 / (2 * l) * y ^ 4 + l / 2 * y ^ 2 - y ^ 3 = y ^ 2 * (y - l) ^ 2 / (2 * l) := by
      field_simp; ring
    have : 0 ≤ y ^ 2 * (y - l) ^ 2 / (2 * l) := div_nonneg h0 (by linarith only [hl0])
    linarith only [e, this]
  have i3 := (bm_pow bH.absv 3).integrable (μ := μ)
  have := integral_mono i3 (show Integrable (fun ω => 1 / (2 * l) * Hrow c X N a ω ^ 4
    + l / 2 * Hrow c X N a ω ^ 2) μ from (iH4.const_mul _).add (iH2.const_mul _)) hpt
  rw [integral_add (show Integrable (fun ω => 1 / (2 * l) * Hrow c X N a ω ^ 4) μ from
    iH4.const_mul _) (show Integrable (fun ω => l / 2 * Hrow c X N a ω ^ 2) μ from
    iH2.const_mul _), integral_const_mul,
    integral_const_mul] at this
  have t1 : 1 / (2 * l) * ∫ ω, Hrow c X N a ω ^ 4 ∂μ ≤ 1 / (2 * l) * (64 * (N : ℝ) ^ 2 * B ^ 4) :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have t2 : l / 2 * ∫ ω, Hrow c X N a ω ^ 2 ∂μ ≤ l / 2 * (4 * N * B ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e1 : 1 / (2 * l) * (64 * (N : ℝ) ^ 2 * B ^ 4) = 32 * (N * Real.sqrt N) * B ^ 3 := by
    rw [hl]
    have hB' : B ≠ 0 := by linarith only [hB1]
    have hs' : Real.sqrt N ≠ 0 := hsq.ne'
    field_simp
    rw [Real.sq_sqrt (by linarith only [hN1])]; ring
  have e2 : l / 2 * (4 * N * B ^ 2) = 2 * (N * Real.sqrt N) * B ^ 3 := by rw [hl]; ring
  linarith only [this, t1, t2, e1, e2]

end RowMoments

/-! ## Part 5: the flat torus with the heat kernel (Task (2), (3)) -/

open WalkCount Function BiasGeneral2 BiasGeneral3 BiasGeneral4 BiasGeneral5 BiasGeneral6
  BiasVariance4

section Good3

/-- **On the fixed normalisation event** `|ρ_a - 1| ≤ 1/8`, for every `k = n + 1`:
    `|Tr P^k - QT| ≤ gC(k) k (9/8)^n · 255 · m₁ (1/N) ∑_a |ε_a|³` (deterministic). -/
theorem trace_QT_good3 {d : ℕ} {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 0 < N) (n : ℕ)
    (x : ℕ → FlatTorus d) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ 1 / 8) :
    |((torusWalk d σ N x) ^ (n + 1)).trace - QT d σ N n x|
      ≤ gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * 255
          * (torusM d σ 1 * (1 / (N : ℝ) * ∑ i : Fin N, |eV d σ N x i| ^ 3)) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hKP : torusK d σ N x = fun i j : Fin N => heatP d σ 1 (x i - x j) := by
    funext i j; exact heatTorus_eq_heatP d σ _
  have h := trace_expansion_paper3 hN (torusK d σ N x) (torusRho d σ N x)
    (fun i => eV d σ N x i) (fun i => bV d σ N x i) (fun i => sV d σ N x i)
    (M := torusM d σ 1)
    (fun i j => heatTorus_nonneg hc d _)
    (fun i j => by
      show heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j) ≤ torusM d σ 1
      rw [torusM_one]; exact heatTorus_le_zero hc d _)
    (fun i j => by
      show heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x j)
        = heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x i)
      rw [← neg_sub (x j) (x i), heatTorus_even])
    (fun i => by
      show ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l) = N * heatRho d σ N x i
      rw [Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)) N]
      unfold heatRho
      field_simp)
    (fun i => (eps_row d σ hN x i).symm)
    (fun i => by
      show 1 / (N : ℝ) * ∑ q : Fin N, heatP d σ 1 (x i - x q) * eV d σ N x q
        = 1 / (N : ℝ) * ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l) * eV d σ N x l
      simp only [heatTorus_eq_heatP])
    (fun i => by
      show 1 / (N : ℝ) * ∑ q : Fin N, heatP d σ 1 (x i - x q) * eV d σ N x q ^ 2
        = 1 / (N : ℝ) * ∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (x i - x l)
          * eV d σ N x l ^ 2
      simp only [heatTorus_eq_heatP])
    (fun i => by
      show |eV d σ N x i| ≤ 1 / 8
      rw [show eV d σ N x i = heatRho d σ N x i - 1 from (eps_row d σ hN x i).symm]
      exact hρ i) n
  rw [← QT_eq N n x (torusK d σ N x) hKP]
  exact h

theorem eV_cube_sum {Ω : Type*} {d : ℕ} (σ : ℝ) {N : ℕ} (hN : 0 < N) (X : ℕ → Ω → FlatTorus d)
    (ω : Ω) :
    1 / (N : ℝ) * ∑ i : Fin N, |eV d σ N (fun j => X j ω) i| ^ 3
      = 1 / (N : ℝ) ^ 4 * ∑ q ∈ Finset.range N, |Hrow (cK d σ) X N q ω| ^ 3 := by
  have hq : ∀ q : ℕ, eV d σ N (fun j => X j ω) q = 1 / (N : ℝ) * Hrow (cK d σ) X N q ω :=
    fun q => (eps_row d σ hN (fun j => X j ω) q).symm.trans
      (SecondStageTrace2.eps_eq_Hrow d σ N hN X ω q)
  simp only [hq]
  rw [Fin.sum_univ_eq_sum_range (fun i => |1 / (N : ℝ) * Hrow (cK d σ) X N i ω| ^ 3) N,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ))]
  field_simp

end Good3

section Final3

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The constant of the cubic expansion remainder: `gC(k) k (9/8)^n · 255` for `k = n + 1`. -/
noncomputable def gK3 (n : ℕ) : ℝ := gC (n + 1) * ((n : ℝ) + 1) * (9 / 8) ^ n * 255

theorem gK3_nonneg (n : ℕ) : 0 ≤ gK3 n := by
  unfold gK3; have := gC_nonneg (n + 1); positivity

/-- **`prop:bias` for every `k = n + 1 ≥ 2` with self-loops, fixed normalisation event
    `max |ρ_a - 1| ≤ 1/8`, NO logarithm in the main remainder.** For independent uniform points
    on the flat torus and `N ≥ 1`:
    `|E Tr P^k - m_k - β_k/N| ≤ 34 gK3 m₁⁴/(N √N) + Ctot/N² + (N + CQT) · P(max_a |ρ_a - 1| > 1/8)`. -/
theorem bias_sharp_event [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (N : ℕ) (hN : 1 ≤ N)
    (n : ℕ) (hn : 1 ≤ n) :
    |∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - (torusM d σ (n + 1) + betaK d σ (n + 1) / N)|
      ≤ 34 * gK3 n * torusM d σ 1 ^ 4 / (N * Real.sqrt N) + Ctot d σ n / (N : ℝ) ^ 2
        + (N + CQT d σ n)
          * μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8} := by
  have H := torus_bvk X h_indep hX hlaw hσ
  have hN' : 0 < N := hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  have hQm := meanQT hσ d X h_indep hX hlaw hN hn
  rw [Mt_eq] at hQm
  have hQi := QT_integrable hσ d X h_indep hX hlaw (N := N) (n := n)
  rw [← hMd]
  have hT01 : ∀ ω (a : Fin N), 0 ≤ ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)) a a
      ∧ ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)) a a ≤ 1 := fun ω a =>
    walk_pow_diag_unit _ _ (fun i j => heatTorus_nonneg hc d _)
      (fun i => div_nonneg (Finset.sum_nonneg fun l _ => heatTorus_nonneg hc d _)
        (Nat.cast_nonneg N)) (n + 1) a
  have hTb : ∀ ω, |((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace| ≤ N := by
    intro ω
    have h0 : 0 ≤ ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace :=
      Finset.sum_nonneg fun a _ => (hT01 ω a).1
    rw [abs_of_nonneg h0]
    calc ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        ≤ ∑ _a : Fin N, (1 : ℝ) := Finset.sum_le_sum fun a _ => (hT01 ω a).2
      _ = N := by simp
  have bT : BM (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace) :=
    ⟨Finset.measurable_sum _ fun a _ => walk_pow_entry_measurable hσ d X hX N (n + 1) a a, N, hTb⟩
  have hGm : MeasurableSet {ω | ∀ a : Fin N,
      |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun a => measurableSet_le
      (continuous_abs.measurable.comp
        ((heatRho_sample_measurable hσ d X hX N a).sub measurable_const)) measurable_const
  obtain ⟨Gc, hGc⟩ : ∃ Gc : Set Ω,
      Gc = {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8} := ⟨_, rfl⟩
  have hGcm : MeasurableSet Gc := by rw [hGc]; exact hGm.compl
  rw [← hGc]
  have bS3 : BM (fun ω => ∑ q ∈ Finset.range N, |Hrow (cK d σ) X N q ω| ^ 3) :=
    BM.sum _ _ fun q _ => bm_pow (H.bmH N q).absv 3
  have hS3n : ∀ ω, 0 ≤ ∑ q ∈ Finset.range N, |Hrow (cK d σ) X N q ω| ^ 3 := fun ω =>
    Finset.sum_nonneg fun q _ => pow_nonneg (abs_nonneg _) 3
  have hgK := gK3_nonneg n
  have hpt : ∀ ω, |((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - QT d σ N n (fun j => X j ω)|
      ≤ gK3 n * M * (1 / (N : ℝ) ^ 4 * ∑ q ∈ Finset.range N, |Hrow (cK d σ) X N q ω| ^ 3)
        + (N + CQT d σ n) * Gc.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hω : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8
    · have hnot : ω ∉ Gc := by rw [hGc]; exact fun h => h hω
      rw [Set.indicator_of_notMem hnot, mul_zero, add_zero, hMd]
      have h := trace_QT_good3 hσ hN' n (fun j => X j ω) hω
      rw [eV_cube_sum σ hN' X ω] at h
      refine h.trans (le_of_eq ?_)
      unfold gK3; ring
    · have hin : ω ∈ Gc := by rw [hGc]; exact hω
      rw [Set.indicator_of_mem hin, mul_one]
      have hq := QT_abs hσ d hN n (fun j => X j ω)
      have h0 : 0 ≤ gK3 n * M * (1 / (N : ℝ) ^ 4 * ∑ q ∈ Finset.range N,
          |Hrow (cK d σ) X N q ω| ^ 3) :=
        mul_nonneg (mul_nonneg hgK hM0) (mul_nonneg (by positivity) (hS3n ω))
      obtain ⟨q1, q2⟩ := abs_le.mp hq
      obtain ⟨s1, s2⟩ := abs_le.mp (hTb ω)
      rw [abs_le]; constructor <;> linarith only [q1, q2, s1, s2, h0]
  have bg1 := BM.const_mul (gK3 n * M) (BM.const_mul (1 / (N : ℝ) ^ 4) bS3)
  have ig2 : Integrable (fun ω => (N + CQT d σ n) * Gc.indicator (fun _ => (1 : ℝ)) ω) μ :=
    ((integrable_const (1 : ℝ)).indicator hGcm).const_mul _
  obtain ⟨g1, hg1⟩ : ∃ g1 : Ω → ℝ, g1 = fun ω => gK3 n * M * (1 / (N : ℝ) ^ 4
      * ∑ q ∈ Finset.range N, |Hrow (cK d σ) X N q ω| ^ 3) := ⟨_, rfl⟩
  obtain ⟨g2, hg2⟩ : ∃ g2 : Ω → ℝ,
      g2 = fun ω => (N + CQT d σ n) * Gc.indicator (fun _ => (1 : ℝ)) ω := ⟨_, rfl⟩
  have ig1' : Integrable g1 μ := by rw [hg1]; exact bg1.integrable
  have ig2' : Integrable g2 μ := by rw [hg2]; exact ig2
  have ig : Integrable (fun ω => g1 ω + g2 ω) μ := ig1'.add ig2'
  have hpt' : ∀ ω, |((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
        - QT d σ N n (fun j => X j ω)| ≤ g1 ω + g2 ω := by rw [hg1, hg2]; exact hpt
  have iD : Integrable (fun ω => ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace
      - QT d σ N n (fun j => X j ω)) μ := bT.integrable.sub hQi
  have hint := abs_int_le_int iD ig hpt'
  rw [integral_sub bT.integrable hQi, integral_add ig1' ig2', hg1, hg2,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_indicator_const (1 : ℝ) hGcm, smul_eq_mul, mul_one] at hint
  -- the third absolute moments of the row sums
  have hS3 : ∫ ω, ∑ q ∈ Finset.range N, |Hrow (cK d σ) X N q ω| ^ 3 ∂μ
      ≤ N * (34 * (N * Real.sqrt N) * M ^ 3) := by
    rw [integral_finset_sum _ fun q _ => (bm_pow (H.bmH N q).absv 3).integrable]
    have := Finset.sum_le_sum fun q (hq : q ∈ Finset.range N) =>
      (hrow_moments H N q (Finset.mem_range.mp hq)).2.2
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    rw [hMd]; exact this
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsqsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hfirst : gK3 n * M * (1 / (N : ℝ) ^ 4 * ∫ ω, ∑ q ∈ Finset.range N,
      |Hrow (cK d σ) X N q ω| ^ 3 ∂μ) ≤ 34 * gK3 n * M ^ 4 / (N * Real.sqrt N) := by
    have h1 : 1 / (N : ℝ) ^ 4 * ∫ ω, ∑ q ∈ Finset.range N, |Hrow (cK d σ) X N q ω| ^ 3 ∂μ
        ≤ 1 / (N : ℝ) ^ 4 * (N * (34 * (N * Real.sqrt N) * M ^ 3)) :=
      mul_le_mul_of_nonneg_left hS3 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hgK hM0)
    have e : gK3 n * M * (1 / (N : ℝ) ^ 4 * (N * (34 * (N * Real.sqrt N) * M ^ 3)))
        = 34 * gK3 n * M ^ 4 / (N * Real.sqrt N) := by
      have hs' : Real.sqrt N ≠ 0 := hsq.ne'
      field_simp
      rw [Real.sq_sqrt hNpos.le]
    linarith only [h2, e]
  obtain ⟨i1, i2⟩ := abs_le.mp hint
  obtain ⟨m1, m2⟩ := abs_le.mp hQm
  rw [abs_le]; constructor <;> linarith only [i1, i2, m1, m2, hfirst]

end Final3

section Closing

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- `x³ e^{-x} ≤ 27` for `x ≥ 0`. -/
theorem cube_exp_neg_le {x : ℝ} (hx : 0 ≤ x) : x ^ 3 * Real.exp (-x) ≤ 27 := by
  have h1 : x / 3 ≤ Real.exp (x / 3) := by linarith [Real.add_one_le_exp (x / 3)]
  have h2 : (x / 3) ^ 3 ≤ Real.exp (x / 3) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : Real.exp (x / 3) ^ 3 = Real.exp x := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h4 : x ^ 3 ≤ 27 * Real.exp x := by
    have : (x / 3) ^ 3 = x ^ 3 / 27 := by ring
    rw [this, h3] at h2; linarith
  have h5 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have h6 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (-x)).le
  calc x ^ 3 * Real.exp (-x) ≤ 27 * Real.exp x * Real.exp (-x) := h6
    _ = 27 := by rw [mul_assoc, h5, mul_one]

/-- **Task (3): `prop:bias` for every `k = n + 1 ≥ 2` with self-loops on the flat torus with the
    heat kernel, remainder `C · N^{-3/2}` WITHOUT a logarithm.**  For independent uniform points
    and fixed `σ > 0`, `n ≥ 1` there is a constant `C` (depending on `d, σ, n`) such that for every
    `N ≥ 1`:  `|E Tr P^{n+1} - m_{n+1} - β_{n+1}/N| ≤ C / (N √N)`, with `β = betaK`. -/
theorem bias_sharp [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
          - (torusM d σ (n + 1) + betaK d σ (n + 1) / N)| ≤ C / (N * Real.sqrt N) := by
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = torusM d σ 1 := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by rw [hMd]; exact torusM_one_ge hσ d
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  obtain ⟨Lip, hLipd⟩ : ∃ Lip : ℝ, Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d := ⟨_, rfl⟩
  have hLip0 : 0 ≤ Lip := by rw [hLipd]; have := Real.pi_pos; positivity
  obtain ⟨g, hgd⟩ : ∃ g : ℕ, g = ⌈32 * Lip⌉₊ + 1 := ⟨_, rfl⟩
  have hg : 0 < g := by rw [hgd]; omega
  have hgL : 32 * Lip ≤ g := by
    rw [hgd]; push_cast; linarith [Nat.le_ceil (32 * Lip)]
  have hMb : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ M := fun u => by
    rw [hMd, torusM_one]; exact heatTorus_le_zero hc d _
  have hLip : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u - heatTorus d (2 * Real.pi ^ 2 * σ) u'|
      ≤ Lip * dist u u' := fun u u' => by rw [hLipd]; exact heatTorus_lipschitz hc d u u'
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = 1 / (1056 * M) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [had]; positivity
  have hgd0 : (0 : ℝ) ≤ (g : ℝ) ^ d := by positivity
  refine ⟨34 * gK3 n * M ^ 4 + |Ctot d σ n|
    + (1 + |CQT d σ n|) * ((g : ℝ) ^ d * 2) * (27 / a ^ 3), ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hsqN : Real.sqrt N ≤ N := by
    rw [Real.sqrt_le_left hNpos.le]; nlinarith only [hN1]
  have hD : 0 < (N : ℝ) * Real.sqrt N := mul_pos hNpos hsq
  have h := bias_sharp_event X h_indep hX hlaw hσ N hN n hn
  have hp := VarianceOne.p8_le hσ d X h_indep hX hlaw N hN hg hMb hLip hLip0 hgL
  rw [← hMd] at h
  obtain ⟨P, hPd⟩ : ∃ P : ℝ,
      P = μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ 1 / 8} := ⟨_, rfl⟩
  rw [← hPd] at h hp
  have hP0 : 0 ≤ P := by rw [hPd]; exact measureReal_nonneg
  have hexp : -((N : ℝ) / 16) ^ 2 / (4 * (N * M) + 2 * M * ((N : ℝ) / 16)) = -(a * N) := by
    have hden : 4 * ((N : ℝ) * M) + 2 * M * ((N : ℝ) / 16) ≠ 0 := by positivity
    rw [had]; field_simp [hden, hM0.ne']; ring
  rw [hexp] at hp
  -- the three terms
  have t1 : 34 * gK3 n * M ^ 4 / (N * Real.sqrt N) = (34 * gK3 n * M ^ 4) / (N * Real.sqrt N) :=
    rfl
  have t2 : Ctot d σ n / (N : ℝ) ^ 2 ≤ |Ctot d σ n| / (N * Real.sqrt N) := by
    have hNN : (N : ℝ) * Real.sqrt N ≤ (N : ℝ) ^ 2 := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hsqN hNpos.le
    calc Ctot d σ n / (N : ℝ) ^ 2 ≤ |Ctot d σ n| / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |Ctot d σ n| / (N * Real.sqrt N) :=
          div_le_div_of_nonneg_left (abs_nonneg _) hD hNN
  have t3 : (N + CQT d σ n) * P
      ≤ (1 + |CQT d σ n|) * ((g : ℝ) ^ d * 2) * (27 / a ^ 3) / (N * Real.sqrt N) := by
    have hq : (N + CQT d σ n) * P ≤ (1 + |CQT d σ n|) * N * P := by
      have : (N : ℝ) + CQT d σ n ≤ (1 + |CQT d σ n|) * N := by
        have := le_abs_self (CQT d σ n)
        nlinarith only [this, hN1, abs_nonneg (CQT d σ n)]
      exact mul_le_mul_of_nonneg_right this hP0
    have hcube : (N : ℝ) ^ 3 * Real.exp (-(a * N)) ≤ 27 / a ^ 3 := by
      have := cube_exp_neg_le (mul_nonneg ha0.le hNpos.le)
      rw [le_div_iff₀ (by positivity)]
      have e : (a * N) ^ 3 = (N : ℝ) ^ 3 * a ^ 3 := by ring
      rw [e] at this; linarith only [this]
    have hNP : (N : ℝ) * P * (N * Real.sqrt N) ≤ (g : ℝ) ^ d * 2 * (27 / a ^ 3) := by
      have h1 : (N : ℝ) * (N * Real.sqrt N) ≤ (N : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_left hsqN (mul_nonneg hNpos.le hNpos.le)
        nlinarith only [this]
      have h2 : P ≤ (g : ℝ) ^ d * 2 * Real.exp (-(a * N)) := by linarith only [hp]
      calc (N : ℝ) * P * (N * Real.sqrt N) = P * (N * (N * Real.sqrt N)) := by ring
        _ ≤ ((g : ℝ) ^ d * 2 * Real.exp (-(a * N))) * (N : ℝ) ^ 3 :=
            mul_le_mul h2 h1 (by positivity) (by positivity)
        _ = (g : ℝ) ^ d * 2 * ((N : ℝ) ^ 3 * Real.exp (-(a * N))) := by ring
        _ ≤ (g : ℝ) ^ d * 2 * (27 / a ^ 3) :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
    have hfin : (1 + |CQT d σ n|) * N * P
        ≤ (1 + |CQT d σ n|) * ((g : ℝ) ^ d * 2) * (27 / a ^ 3) / (N * Real.sqrt N) := by
      rw [le_div_iff₀ hD]
      have hc1 : 0 ≤ 1 + |CQT d σ n| := by positivity
      have := mul_le_mul_of_nonneg_left hNP hc1
      calc (1 + |CQT d σ n|) * N * P * (N * Real.sqrt N)
          = (1 + |CQT d σ n|) * ((N : ℝ) * P * (N * Real.sqrt N)) := by ring
        _ ≤ (1 + |CQT d σ n|) * ((g : ℝ) ^ d * 2 * (27 / a ^ 3)) := this
        _ = (1 + |CQT d σ n|) * ((g : ℝ) ^ d * 2) * (27 / a ^ 3) := by ring
    exact hq.trans hfin
  have hsum : (34 * gK3 n * M ^ 4 + |Ctot d σ n|
      + (1 + |CQT d σ n|) * ((g : ℝ) ^ d * 2) * (27 / a ^ 3)) / (N * Real.sqrt N)
      = 34 * gK3 n * M ^ 4 / (N * Real.sqrt N) + |Ctot d σ n| / (N * Real.sqrt N)
        + (1 + |CQT d σ n|) * ((g : ℝ) ^ d * 2) * (27 / a ^ 3) / (N * Real.sqrt N) := by
    rw [add_div, add_div]
  rw [hsum]
  linarith only [h, t2, t3]

/-- **Task (3), the limit:** `N (E Tr P^{n+1} - m_{n+1}) → β_{n+1}` as `N → ∞` (for `n ≥ 1`,
    fixed `σ > 0`, self-loops, independent uniform points on the flat torus). -/
theorem bias_sharp_limit [IsProbabilityMeasure μ] {d : ℕ} (X : ℕ → Ω → FlatTorus d)
    (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto (fun N : ℕ => (N : ℝ)
        * (∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ - torusM d σ (n + 1)))
      Filter.atTop (nhds (betaK d σ (n + 1))) := by
  obtain ⟨C, hC⟩ := bias_sharp X h_indep hX hlaw hσ n hn
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((|C| / ε) ^ 2)
  refine ⟨max 1 N0, fun N hN => ?_⟩
  have hN1' : 1 ≤ N := le_of_max_le_left hN
  have hN0' : N0 ≤ N := le_of_max_le_right hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1'
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hb := hC N hN1'
  rw [Real.dist_eq]
  have e : (N : ℝ) * (∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - torusM d σ (n + 1)) - betaK d σ (n + 1)
      = N * (∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - (torusM d σ (n + 1) + betaK d σ (n + 1) / N)) := by
    field_simp; ring
  rw [e, abs_mul, abs_of_pos hNpos]
  have h1 : (N : ℝ) * |∫ ω, ((torusWalk d σ N (fun j => X j ω)) ^ (n + 1)).trace ∂μ
        - (torusM d σ (n + 1) + betaK d σ (n + 1) / N)| ≤ N * (C / (N * Real.sqrt N)) :=
    mul_le_mul_of_nonneg_left hb hNpos.le
  have e2 : (N : ℝ) * (C / (N * Real.sqrt N)) = C / Real.sqrt N := by
    field_simp
  rw [e2] at h1
  have hgt : |C| / ε < Real.sqrt N := by
    rw [Real.lt_sqrt (div_nonneg (abs_nonneg C) hε.le)]
    have : (N0 : ℝ) ≤ N := by exact_mod_cast hN0'
    linarith
  have h2 : C / Real.sqrt N ≤ |C| / Real.sqrt N :=
    div_le_div_of_nonneg_right (le_abs_self C) hsq.le
  have h3 : |C| / Real.sqrt N < ε := by
    rw [div_lt_iff₀ hsq]
    rw [div_lt_iff₀ hε] at hgt
    linarith
  linarith

end Closing

end BiasSharp

end CTG.Reals2
