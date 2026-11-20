import CorrelationsToGeometryReal
/-!
# From Correlations to Geometry: continuation of the Mathlib file

Third Lean file of the project. It imports `CorrelationsToGeometryReal.lean` unchanged and continues it.
Reason for the split (20 November 2026): checking the second file as a whole needs about 2.4 GB of memory,
more than the author-side machine reliably has; new material goes here and is checked against the compiled
second file (`check_real2.sh`). No `sorry`, no `axiom`, no `native_decide`.
Unproved inputs are hypotheses, marked HYPOTHESIS in the comments.
-/
open MeasureTheory ProbabilityTheory CTG.Reals Matrix

namespace CTG.Reals2

/-! ### The reduction for the sampled graph with the normalisation, (H3) and (H4) on one event -/

namespace TorusReductionL1

open CTG.Reals.TorusReduction

/-- The constant of the normalisation: `|ρ_a - 1| ≤ normC d · δ'`. -/
noncomputable def normC (d : ℕ) : ℝ :=
  6 * Real.sqrt (3 * (d : ℝ) + 5) * (1 + Real.sqrt (2 * Real.pi)) ^ d

/-- The constant of the `ℓ¹` kernel bound against the `δ'` of the main file
    (`M = (1 + (2πσ)^(-1/2))^d`). -/
noncomputable def l1C (d : ℕ) : ℝ :=
  9 / 7 * (27 * Real.sqrt (3 * (d : ℝ) + 5) + 2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d)))

/-- The constant `c_E` of (H4) against `δ' = √(p_σ(0) log N / N)`. -/
noncomputable def h4C (d : ℕ) : ℝ := l1C d * (1 + Real.sqrt (2 * Real.pi)) ^ d

theorem normC_nonneg (d : ℕ) : 0 ≤ normC d := by
  unfold normC
  positivity

theorem l1C_nonneg (d : ℕ) : 0 ≤ l1C d := by
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  unfold l1C
  positivity

theorem h4C_nonneg (d : ℕ) : 0 ≤ h4C d := by
  have h := l1C_nonneg d
  unfold h4C
  positivity

theorem h4C_ge (d : ℕ) : 9 / 2 * normC d ≤ h4C d := by
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hAa : 0 ≤ Real.sqrt (3 * (d : ℝ) + 5) := Real.sqrt_nonneg _
  have hA : 0 ≤ (1 + Real.sqrt (2 * Real.pi)) ^ d := by positivity
  have hcA : 0 ≤ 3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d) := by positivity
  have h1 : 27 * Real.sqrt (3 * (d : ℝ) + 5)
      ≤ 9 / 7 * (27 * Real.sqrt (3 * (d : ℝ) + 5) + 2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Real.sqrt (3 * (d : ℝ) + 5) * rateRA d))) := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hA
  unfold h4C l1C normC
  calc 9 / 2 * (6 * Real.sqrt (3 * (d : ℝ) + 5) * (1 + Real.sqrt (2 * Real.pi)) ^ d)
      = 27 * Real.sqrt (3 * (d : ℝ) + 5) * (1 + Real.sqrt (2 * Real.pi)) ^ d := by ring
    _ ≤ _ := h2

/-- Arithmetic of the `ℓ¹` bound. -/
theorem l1_arith {Nr δ0 a s1 s2 Aa cA δp : ℝ} (hN : 0 ≤ Nr) (hδ0 : 0 ≤ δ0) (hδ8 : δ0 ≤ 1 / 8)
    (hδle : δ0 ≤ 6 * Aa * δp) (ha : a ≤ cA * δp) (hs10 : 0 ≤ s1) (hs12 : s1 ≤ s2)
    (hs2 : 1 ≤ s2) (hAa : 0 ≤ Aa) (hcA : 0 ≤ cA) (hδp : 0 ≤ δp) :
    9 / 7 * (Nr * (4 * δ0 * (1 + δ0) + 2 * a * s1))
      ≤ Nr * (9 / 7 * (27 * Aa + 2 * cA) * δp * s2) := by
  have p1 : 4 * δ0 * (1 + δ0) ≤ 27 * Aa * δp := by
    have h1 : 4 * δ0 * (1 + δ0) ≤ 4 * δ0 * (9 / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have h27 : 0 ≤ 27 * Aa * δp := by positivity
  have p2 : 27 * Aa * δp ≤ 27 * Aa * δp * s2 := le_mul_of_one_le_right h27 hs2
  have hs20 : 0 ≤ s2 := by linarith
  have hcd : 0 ≤ cA * δp := mul_nonneg hcA hδp
  have p3 : a * s1 ≤ cA * δp * s2 := mul_le_mul ha hs12 hs10 hcd
  have p4 : 4 * δ0 * (1 + δ0) + 2 * a * s1 ≤ 27 * Aa * δp * s2 + 2 * (cA * δp * s2) := by
    linarith
  calc 9 / 7 * (Nr * (4 * δ0 * (1 + δ0) + 2 * a * s1))
      ≤ 9 / 7 * (Nr * (27 * Aa * δp * s2 + 2 * (cA * δp * s2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left p4 hN) (by norm_num)
    _ = Nr * (9 / 7 * (27 * Aa + 2 * cA) * δp * s2) := by ring

/-- A measure bound from an inclusion in a union of three sets. -/
theorem real_le_of_subset3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S A B C : Set Ω} {a b c t : ℝ} (hA : μ.real A ≤ a)
    (hB : μ.real B ≤ b) (hC : μ.real C ≤ c) (hsub : S ⊆ A ∪ B ∪ C) (ht : a + b + c = t) :
    μ.real S ≤ t := by
  have h0 : μ.real S ≤ μ.real (A ∪ B ∪ C) := measureReal_mono hsub (measure_ne_top μ _)
  have h1 : μ.real (A ∪ B ∪ C) ≤ μ.real (A ∪ B) + μ.real C := measureReal_union_le _ _
  have h2 : μ.real (A ∪ B) ≤ μ.real A + μ.real B := measureReal_union_le _ _
  linarith

set_option maxHeartbeats 6400000 in
/-- **The `ℓ¹` kernel bound with probability, in terms of the `δ'` of the main file.**
    Hypotheses of `heat_kernel_rate_paper_g3` (`M = (1 + (2πσ)^(-1/2))^d`, `δ' = √(M log N/N)`,
    `12 ≤ N`, `1 ≤ K ≤ N`, Lipschitz condition, `rateCfin3 d · δ' √K ≤ 1`). Except on an event of
    probability at most `2/N³`: for all `2 ≤ l ≤ K` and every `i`,
    `∑_a |N P^l(a,i) - p_{lσ}(x_a - x_i)| ≤ N · l1C d · δ' √l` (sum over the FIRST index). -/
theorem l1_g3 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN12 : 12 ≤ N) (hK : 0 < K)
    (hKN : K ≤ N)
    {M Lip δp : ℝ} (hMdef : M = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hLipdef : Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d)
    (hδp : δp = Real.sqrt (M * Real.log N / N))
    (hLipc : 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * M * Real.log N)))
    (hsmall : rateCfin3 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ l, 2 ≤ l → l ≤ K → ∀ i : Fin N,
        ∑ a : Fin N, |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ l) a i
            - heatP d σ l (X a ω - X i ω)|
          ≤ (N : ℝ) * (l1C d * δp * Real.sqrt l)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hN : 0 < N := by omega
  have hNr : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKr : (K : ℝ) ≤ N := by exact_mod_cast hKN
  have hpi := Real.pi_pos
  have hMpos : 0 < M := by rw [hMdef]; positivity
  have hLip0 : 0 ≤ Lip := by rw [hLipdef]; positivity
  have hc := cvConst_nonneg
  -- logarithms
  obtain ⟨lg, hlg⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  rw [← hlg] at hδp hLipc
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.log ((2 + 4 * K) * (2 * ((N ^ 3 : ℕ) : ℝ) ^ d) * (N : ℝ) ^ 3) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (4 * K * (N : ℝ) ^ 5) := ⟨_, rfl⟩
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hg3 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; rfl
  have hNd : (1 : ℝ) ≤ ((N : ℝ) ^ 3) ^ d := one_le_pow₀ hN3
  rw [hg3] at hT
  have hargpos : 0 < (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3 := by positivity
  have hTle : T ≤ (3 * (d : ℝ) + 5) * lg := by
    have h1 : (2 + 4 * (K : ℝ)) * 2 ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (3 * d + 5) := by
      calc (2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3
          = ((2 + 4 * (K : ℝ)) * 2) * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (3 * d + 5) := by rw [← pow_mul]; ring
    rw [hT, hlg]
    calc Real.log ((2 + 4 * (K : ℝ)) * (2 * ((N : ℝ) ^ 3) ^ d) * (N : ℝ) ^ 3)
        ≤ Real.log ((N : ℝ) ^ (3 * d + 5)) := Real.log_le_log hargpos h2
      _ = (3 * (d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hTge : lg ≤ T := by
    rw [hT, hlg]
    refine Real.log_le_log hNpos ?_
    have h6 : (6 : ℝ) ≤ 2 + 4 * K := by linarith
    have h2 : (2 : ℝ) ≤ 2 * ((N : ℝ) ^ 3) ^ d := by linarith
    have h3 : (N : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1), sq_nonneg (N : ℝ)]
    have h12 : (12 : ℝ) ≤ (2 + 4 * K) * (2 * ((N : ℝ) ^ 3) ^ d) := by nlinarith
    have h13 := mul_le_mul_of_nonneg_right h12 (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 3)
    linarith
  have hLle : L ≤ 7 * lg := by
    have h1 : 4 * (K : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 7 := by
      calc 4 * (K : ℝ) * (N : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ 5 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ 7 := by ring
    rw [hL, hlg]
    calc Real.log (4 * (K : ℝ) * (N : ℝ) ^ 5) ≤ Real.log ((N : ℝ) ^ 7) :=
          Real.log_le_log (by positivity) h2
      _ = 7 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have hLpos : 0 < L := by
    rw [hL]; apply Real.log_pos
    have : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by linarith)
    nlinarith
  have hTpos : 0 < T := by linarith
  -- δ' and the square roots
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * M * lg) := ⟨_, rfl⟩
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hQeq : Q = δp * N := by
    have hsq : (δp * N) ^ 2 = N * M * lg := by
      rw [mul_pow, hδp, Real.sq_sqrt (by positivity)]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt (3 * (d : ℝ) + 5) := ⟨_, rfl⟩
  have hAa0 : 0 ≤ Aa := by rw [hAa]; exact Real.sqrt_nonneg _
  have hAa1 : 1 ≤ Aa := by
    rw [hAa, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hsqT : Real.sqrt (N * M * T) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ N * M)
    exact this.trans (le_of_eq (by ring))
  have hsqTge : Q ≤ Real.sqrt (N * M * T) := by
    rw [hQ]; exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTge (by positivity))
  -- the constant
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, Cf = rateCfin3 d := ⟨_, rfl⟩
  obtain ⟨mx, hmx⟩ : ∃ mx : ℝ, mx = max
      (2 * (3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d)))
      (3 * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d)) := ⟨_, rfl⟩
  have hCK0 : 0 ≤ rateCK d := by unfold rateCK; positivity
  have hRA0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hRB0 : 0 ≤ rateRA d := Real.sqrt_nonneg _
  have hmx0 : 0 ≤ mx := by rw [hmx]; exact le_max_of_le_right (by positivity)
  have hCfeq : Cf = 48 * Aa + 3 * 2 ^ d * mx := by rw [hCf, hmx, hAa]; unfold rateCfin3; rfl
  rw [← hCf] at hsmall
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hCf48 : 48 * Aa ≤ Cf := by
    rw [hCfeq]
    have : 0 ≤ 3 * 2 ^ d * mx := by positivity
    linarith
  have hCf0 : 0 ≤ Cf := by linarith
  have h48 : 48 * Aa * δp ≤ 1 := by
    have h1 : 48 * Aa * δp ≤ Cf * δp := mul_le_mul_of_nonneg_right hCf48 hδp0
    have h2 : Cf * δp ≤ Cf * δp * Real.sqrt K :=
      le_mul_of_one_le_right (mul_nonneg hCf0 hδp0) hsK1
    linarith
  have hδK : δp * Real.sqrt K ≤ 1 := by
    have h1 : 1 * (δp * Real.sqrt K) ≤ Cf * (δp * Real.sqrt K) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : Cf * (δp * Real.sqrt K) = Cf * δp * Real.sqrt K := by ring
    linarith
  -- the parameters of the explicit theorem
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 6 * Real.sqrt (N * M * T) / N := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K / N := ⟨_, rfl⟩
  have hkb0 : 0 ≤ heatKbar d σ := by unfold heatKbar; positivity
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδle : δ ≤ 6 * Aa * δp := by
    rw [hδ, div_le_iff₀ hNpos]
    calc 6 * Real.sqrt (N * M * T) ≤ 6 * (Aa * Q) := by linarith
      _ = 6 * Aa * δp * N := by rw [hQeq]; ring
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hsm : 6 * Real.sqrt (N * M * T) ≤ N / 8 := by
    have : 6 * Real.sqrt (N * M * T) = δ * N := by rw [hδ]; field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_right hδ8 hNpos.le
    linarith
  have hgc : 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤ 3 * Real.sqrt (N * M * T) := by
    rw [hg3]
    have hN2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have e : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ) ^ 3) = 2 * Lip / (N : ℝ) ^ 2 := by field_simp
    rw [e, div_le_iff₀ hN2]
    calc 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Q) := by rw [hQ]; exact hLipc
      _ ≤ 3 * Real.sqrt (N * M * T) * (N : ℝ) ^ 2 := by nlinarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθle : θ ≤ 16 * (rateCK d + 1) * δp := by
    have hkb := heatKbar_le_M hσ d
    rw [← hMdef] at hkb
    have h1 : 2 * L + 2 ≤ 16 * lg := by linarith
    have h2 : heatKbar d σ + M ≤ (rateCK d + 1) * M := by linarith
    have h3 : (2 * L + 2) * (heatKbar d σ + M) ≤ 16 * lg * ((rateCK d + 1) * M) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have hδp2 : δp ^ 2 = M * lg / N := by rw [hδp, Real.sq_sqrt (by positivity)]
    rw [hθ, div_le_iff₀ hNpos]
    calc (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K
        ≤ 16 * lg * ((rateCK d + 1) * M) * Real.sqrt K :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ = 16 * (rateCK d + 1) * (δp ^ 2 * N) * Real.sqrt K := by rw [hδp2]; field_simp
      _ = 16 * (rateCK d + 1) * δp * N * (δp * Real.sqrt K) := by ring
      _ ≤ 16 * (rateCK d + 1) * δp * N * 1 :=
          mul_le_mul_of_nonneg_left hδK (by positivity)
      _ = 16 * (rateCK d + 1) * δp * N := by ring
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = Real.sqrt (N * M * L) / N := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hSle : S ≤ Real.sqrt 7 * δp := by
    rw [hS, div_le_iff₀ hNpos]
    calc Real.sqrt (N * M * L) ≤ Real.sqrt (7 * (N * M * lg)) := by
          apply Real.sqrt_le_sqrt
          have := mul_le_mul_of_nonneg_left hLle (by positivity : (0 : ℝ) ≤ N * M)
          exact this.trans (le_of_eq (by ring))
      _ = Real.sqrt 7 * Q := by rw [hQ, Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 7 * δp * N := by rw [hQeq]; ring
  -- the parameters of the `ℓ¹` theorem
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * M * T) := ⟨_, rfl⟩
  have hsq : 0 < Real.sqrt (N * M * T) := Real.sqrt_pos.mpr (by positivity)
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε2 : ε ^ 2 = 9 * (N * M * T) := by
    rw [hεdef, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
  obtain ⟨δ0, hδ0def⟩ :
      ∃ δ0 : ℝ, δ0 = (ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ))) / N := ⟨_, rfl⟩
  have hgc0 : 0 ≤ 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) := by positivity
  have hδ00 : 0 ≤ δ0 := by
    rw [hδ0def]
    exact div_nonneg (by linarith) hNpos.le
  have hδ0le : δ0 ≤ δ := by
    rw [hδ0def, hδ]
    exact div_le_div_of_nonneg_right (by rw [hεdef]; linarith) hNpos.le
  have hδ0le' : δ0 ≤ 6 * Aa * δp := hδ0le.trans hδle
  have hδ08 : δ0 ≤ 1 / 8 := hδ0le.trans hδ8
  have hsmall' : ε + 2 * ((N : ℝ) * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) ≤ N / 8 := by
    rw [hεdef]; linarith
  have hθ' : (2 * L + 2) * (heatKbar d σ + M) * Real.sqrt K ≤ θ * N := by
    rw [hθ, div_mul_cancel₀ _ hNpos.ne']
  obtain ⟨cA, hcA⟩ : ∃ cA : ℝ, cA = 3 * (9 / 8) * ((5 / 4) * (16 * (rateCK d + 1) + 2 * Real.sqrt 7 * rateRA d)
        + 12 * Aa * rateRA d) := ⟨_, rfl⟩
  have hcA0 : 0 ≤ cA := by rw [hcA]; positivity
  have habA := (rate_ab_bound hδ00 hδ08 hδ0le' hθ0 hθle hS0 hSle hRA0 hδp0
    (by positivity : (0 : ℝ) ≤ 16 * (rateCK d + 1)) hAa0).1
  have hA : heatRateA d N M L δ0 θ ≤ cA * δp := by
    rw [hcA]; unfold heatRateA; rw [← hS]; exact habA
  have hl1C : l1C d = 9 / 7 * (27 * Aa + 2 * cA) := by
    rw [hcA, hAa]; rfl
  have hTcond : T * (4 * (N * M) + 2 * M * ε) ≤ ε ^ 2 := by
    rw [hε2]
    have h1 : 2 * M * ε * T ≤ 5 * (N * M * T) := by
      have : ε ≤ 5 * N / 2 := by rw [hεdef]; linarith
      have hMT : 0 ≤ M * T := by positivity
      nlinarith [mul_le_mul_of_nonneg_left this hMT]
    nlinarith
  have h := heat_kernel_l1_sample_all hσ hσ1 d X h_indep hX hlaw N K hN (pow_pos hN 3) hMdef
    hLipdef hLpos hε hsmall' hδ0def hθ0 hθ'
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) (h.trans ?_)
  · intro ω hω hgood
    apply hω
    intro l hl2 hlK i
    obtain ⟨j, rfl⟩ : ∃ j, l = j + 2 := ⟨l - 2, by omega⟩
    have h1 := hgood j (by omega) i
    refine h1.trans ?_
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hs1 : (1 : ℝ) ≤ Real.sqrt ((j + 2 : ℕ) : ℝ) := by
      have h12 : (1 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + 2)
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt h12
    have hs12 : Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ Real.sqrt ((j + 2 : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (by omega : j + 1 ≤ j + 2))
    rw [hl1C]
    exact l1_arith hNpos.le hδ00 hδ08 hδ0le' hA (Real.sqrt_nonneg _) hs12 hs1 hAa0 hcA0 hδp0
  · rw [hg3]
    obtain ⟨Gd, hGd⟩ : ∃ Gd : ℝ, Gd = ((N : ℝ) ^ 3) ^ d := ⟨_, rfl⟩
    rw [← hGd] at hT ⊢
    have hGdpos : 0 < Gd := by rw [hGd]; positivity
    have hKpos : (0 : ℝ) < K := by linarith
    obtain ⟨Ar, hAr⟩ : ∃ Ar : ℝ, Ar = (2 + 4 * (K : ℝ)) * (2 * Gd) * (N : ℝ) ^ 3 := ⟨_, rfl⟩
    have hArpos : 0 < Ar := by rw [hAr]; positivity
    have hD : 0 < 4 * (N * M) + 2 * M * ε := by positivity
    have hTA : T = Real.log Ar := by rw [hAr]; exact hT
    rw [hTA] at hTcond
    have he1 : Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ 1 / Ar := by
      have h1 : -ε ^ 2 / (4 * (N * M) + 2 * M * ε) ≤ -Real.log Ar := by
        rw [neg_div, neg_le_neg_iff, le_div_iff₀ hD]; exact hTcond
      calc Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε)) ≤ Real.exp (-Real.log Ar) :=
            Real.exp_le_exp.mpr h1
        _ = 1 / Ar := by rw [Real.exp_neg, Real.exp_log hArpos, one_div]
    have hN5pos : (0 : ℝ) < 4 * K * (N : ℝ) ^ 5 := by positivity
    have he2 : Real.exp (-L) = 1 / (4 * K * (N : ℝ) ^ 5) := by
      rw [hL, Real.exp_neg, Real.exp_log hN5pos, one_div]
    have hp : (2 + 4 * (K : ℝ)) * (Gd * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
        ≤ 1 / (N : ℝ) ^ 3 := by
      calc (2 + 4 * (K : ℝ)) * (Gd * (2 * Real.exp (-ε ^ 2 / (4 * (N * M) + 2 * M * ε))))
          ≤ (2 + 4 * (K : ℝ)) * (Gd * (2 * (1 / Ar))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith) hGdpos.le
        _ = 1 / (N : ℝ) ^ 3 := by
            rw [hAr]
            have h2K : (2 + 4 * (K : ℝ)) ≠ 0 := by positivity
            have hGd0 : Gd ≠ 0 := hGdpos.ne'
            have hN30 : (N : ℝ) ^ 3 ≠ 0 := by positivity
            first | (field_simp; done) | (field_simp; ring)
    have hq : (K : ℝ) * ((N : ℝ) ^ 2 * (2 * Real.exp (-L))) = 1 / (2 * (N : ℝ) ^ 3) := by
      rw [he2]
      have hK0 : (K : ℝ) ≠ 0 := hKpos.ne'
      have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
      first | (field_simp; done) | (field_simp; ring)
    have e3 : 2 / (N : ℝ) ^ 3
        = 1 / (N : ℝ) ^ 3 + (1 / (2 * (N : ℝ) ^ 3) + 1 / (2 * (N : ℝ) ^ 3)) := by
      have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
      first | (field_simp; done) | (field_simp; ring)
    rw [hq, e3]
    linarith

set_option maxHeartbeats 6400000 in
/-- **The normalisation event and the `ℓ¹` event under the hypotheses of `kernel_theorem_G28`.**
    `M = p_σ(0)`, `δ' = √(M log N/N)`, `kernelC1 d · δ' √K ≤ 1`. Then `normC d · δ' ≤ 1/8`;
    except on an event of probability at most `1/N³`, `|ρ_a - 1| ≤ normC d · δ'` for all `a`;
    except on an event of probability at most `2/N³`, for all `2 ≤ l ≤ K` and every `i`,
    `∑_a |N P^l(a,i) - p_{lσ}(x_a - x_i)| ≤ N · h4C d · δ' √l`. -/
theorem good_events {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    normC d * δp ≤ 1 / 8 ∧
    μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ normC d * δp}
      ≤ 1 / (N : ℝ) ^ 3 ∧
    μ.real {ω | ¬ ∀ l, 2 ≤ l → l ≤ K → ∀ i : Fin N,
        ∑ a : Fin N, |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ l) a i
            - heatP d σ l (X a ω - X i ω)|
          ≤ (N : ℝ) * (h4C d * δp * Real.sqrt l)}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  -- the logarithm
  obtain ⟨lg, hlgdef⟩ : ∃ lg : ℝ, lg = Real.log N := ⟨_, rfl⟩
  have hlg : (1 / 2 : ℝ) ≤ lg := by
    rw [hlgdef, Real.le_log_iff_exp_le hNpos]
    have h1 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
      have := Real.add_one_le_exp (-(1 / 2) : ℝ); linarith
    have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by rw [← Real.exp_add]; norm_num
    have h3 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith
  rw [← hlgdef] at hδp
  -- the two kernel bounds
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 + Real.sqrt (2 * Real.pi)) ^ d := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hA]; exact one_le_pow₀ (by linarith [Real.sqrt_nonneg (2 * Real.pi)])
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ)) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  have hyy : y * y = Real.pi / (2 * Real.pi ^ 2 * σ) := by
    rw [hy]; exact Real.mul_self_sqrt (by positivity)
  obtain ⟨ML, hML⟩ : ∃ ML : ℝ, ML = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d :=
    ⟨_, rfl⟩
  have hMLy : ML = (1 + y) ^ d := by rw [hML, hy]
  have hMp1 : 1 ≤ Mp := by rw [hMp]; exact heatTorus_zero_ge_one hcσ d
  have hMpML : Mp ≤ ML := by rw [hMp, hML]; exact heatTorus_le hcσ d 0
  have hML1 : 1 ≤ ML := hMp1.trans hMpML
  have hMLA : ML ≤ A * Mp := by
    have h := heatMu_le_m hσ d 1 le_rfl (by simpa using hσ1)
    unfold heatMu heatM at h
    rw [if_neg one_ne_zero] at h
    simp only [Nat.cast_one, one_mul] at h
    rw [hML, hA, hMp]; exact h
  have hyML : 1 + y ≤ ML := by
    rw [hMLy]
    calc 1 + y = (1 + y) ^ 1 := (pow_one _).symm
      _ ≤ (1 + y) ^ d := pow_le_pow_right₀ (by linarith) hd
  -- δ' of the file
  obtain ⟨δL, hδL⟩ : ∃ δL : ℝ, δL = Real.sqrt (ML * lg / N) := ⟨_, rfl⟩
  have hδL0 : 0 ≤ δL := by rw [hδL]; exact Real.sqrt_nonneg _
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hδLle : δL ≤ A * δp := by
    have h1 : ML * lg / N ≤ A ^ 2 * (Mp * lg / N) := by
      have h2 : ML ≤ A ^ 2 * Mp := by nlinarith
      have h3 : 0 ≤ lg / N := by positivity
      calc ML * lg / N = ML * (lg / N) := by ring
        _ ≤ A ^ 2 * Mp * (lg / N) := mul_le_mul_of_nonneg_right h2 h3
        _ = A ^ 2 * (Mp * lg / N) := by ring
    calc δL = Real.sqrt (ML * lg / N) := hδL
      _ ≤ Real.sqrt (A ^ 2 * (Mp * lg / N)) := Real.sqrt_le_sqrt h1
      _ = A * δp := by rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA0, hδp]
  have hδL2 : δL ^ 2 = ML * lg / N := by rw [hδL, Real.sq_sqrt (by positivity)]
  -- the constant
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = rateCfin3 d := ⟨_, rfl⟩
  obtain ⟨Aa, hAa⟩ : ∃ Aa : ℝ, Aa = Real.sqrt (3 * (d : ℝ) + 5) := ⟨_, rfl⟩
  have hAa1 : 1 ≤ Aa := by
    rw [hAa, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by linarith [Nat.cast_nonneg (α := ℝ) d])
  have hCAa : 48 * Aa ≤ C := by rw [hC, hAa]; exact (rateCfin3_ge d).1
  have hC2d : (2 : ℝ) ^ d ≤ C := by rw [hC]; exact (rateCfin3_ge d).2
  have hC48 : 48 ≤ C := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hC1 : kernelC1 d = C * A ^ 2 := by unfold kernelC1; rw [hC, hA]
  rw [hC1] at hrange
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hsmallL : C * δL * Real.sqrt K ≤ 1 := by
    have h1 : C * δL ≤ C * A ^ 2 * δp := by
      have h2 : A * δp ≤ A ^ 2 * δp := by nlinarith [mul_nonneg hA0 hδp0]
      have h3 := mul_le_mul_of_nonneg_left (hδLle.trans h2) hC0
      linarith
    exact (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)).trans hrange
  have hCδL : C * δL ≤ 1 := by
    have h1 : C * δL ≤ C * δL * Real.sqrt K := le_mul_of_one_le_right (by positivity) hsK1
    linarith
  -- N is large
  have hNbig : C ^ 2 * (ML * lg) ≤ N := by
    have h1 : (C * δL) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ C * δL := by positivity
      nlinarith
    rw [mul_pow, hδL2] at h1
    have h2 : C ^ 2 * (ML * lg / N) * N ≤ 1 * N := mul_le_mul_of_nonneg_right h1 hNpos.le
    have e : C ^ 2 * (ML * lg / N) * N = C ^ 2 * (ML * lg) := by field_simp
    linarith
  have hMLlg : (1 / 2 : ℝ) ≤ ML * lg := by nlinarith
  have hC2 : (2304 : ℝ) ≤ C ^ 2 := by nlinarith
  have hNr12 : (12 : ℝ) ≤ N := by nlinarith
  have hN12 : 12 ≤ N := by exact_mod_cast hNr12
  have hKN : K ≤ N := by
    have h1 : (C * δL * Real.sqrt K) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ C * δL * Real.sqrt K := by positivity
      nlinarith
    have hKsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt (by positivity)
    have h2 : C ^ 2 * (ML * lg / N) * K ≤ 1 := by
      have e : (C * δL * Real.sqrt K) ^ 2 = C ^ 2 * δL ^ 2 * Real.sqrt K ^ 2 := by ring
      rw [e, hδL2, hKsq] at h1; exact h1
    have h3 : C ^ 2 * (ML * lg) * K ≤ N := by
      have h4 := mul_le_mul_of_nonneg_right h2 hNpos.le
      have e : C ^ 2 * (ML * lg / N) * K * N = C ^ 2 * (ML * lg) * K := by field_simp
      linarith
    have h5 : (1 : ℝ) ≤ C ^ 2 * (ML * lg) := by nlinarith
    have h6 : (K : ℝ) ≤ N := by nlinarith
    exact_mod_cast h6
  -- the Lipschitz constant
  obtain ⟨Lip, hLip⟩ : ∃ Lip : ℝ, Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d := ⟨_, rfl⟩
  have hLip0 : 0 ≤ Lip := by rw [hLip]; positivity
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.sqrt (N * ML * lg) := ⟨_, rfl⟩
  have hQeq : Q = δL * N := by
    have hsq : (δL * N) ^ 2 = N * ML * lg := by
      rw [mul_pow, hδL2]; field_simp
    rw [hQ, ← hsq, Real.sqrt_sq (by positivity)]
  have hLipML : Lip ≤ 4 * (2 : ℝ) ^ d * (ML * ML * ML) := by
    have e1 : 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ)) = 4 * (y * y) := by
      rw [hyy]; field_simp; ring
    have e2 : Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ)) = Real.sqrt 2 * y := by
      rw [hy, ← Real.sqrt_mul (by norm_num)]
      congr 1; ring
    have hs2 : Real.sqrt 2 ≤ 2 := by
      have := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 4 by norm_num)
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    have h1 : 1 + Real.sqrt 2 * y ≤ 2 * (1 + y) := by nlinarith [Real.sqrt_nonneg 2]
    have h2 : (1 + Real.sqrt 2 * y) ^ d ≤ 2 ^ d * ML := by
      calc (1 + Real.sqrt 2 * y) ^ d ≤ (2 * (1 + y)) ^ d :=
            pow_le_pow_left₀ (by positivity) h1 d
        _ = 2 ^ d * ML := by rw [mul_pow, hMLy]
    have h3 : y * y ≤ ML * ML := by nlinarith
    rw [hLip, e1, e2]
    calc 4 * (y * y) * (1 + Real.sqrt 2 * y) ^ d
        ≤ 4 * (ML * ML) * (2 ^ d * ML) :=
          mul_le_mul (by linarith) h2 (by positivity) (by positivity)
      _ = 4 * (2 : ℝ) ^ d * (ML * ML * ML) := by ring
  have hNa : 24 * C * ML ≤ N := by
    have h1 : 24 ≤ C * lg := by nlinarith
    have h2 : 0 ≤ C * ML := by positivity
    have h3 : C * ML * 24 ≤ C * ML * (C * lg) := mul_le_mul_of_nonneg_left h1 h2
    have e : C ^ 2 * (ML * lg) = C * ML * (C * lg) := by ring
    linarith
  have hNb : ML ≤ N := by
    have h1 : ML ≤ 24 * C * ML := by nlinarith
    linarith
  have hQge : 24 * ML ≤ Q := by
    have h1 : 24 * ML ≤ δL * N := by
      -- (24 ML)² ≤ δL² N² = ML lg N
      have h2 : (24 * ML) ^ 2 ≤ (δL * N) ^ 2 := by
        have e2 : (δL * N) ^ 2 = ML * lg * N := by
          rw [mul_pow, hδL2]; field_simp
        rw [e2]
        have h3 : (1152 : ℝ) * ML ≤ N := by
          have h30 : 2304 * (ML * lg) ≤ C ^ 2 * (ML * lg) :=
            mul_le_mul_of_nonneg_right hC2 (by positivity)
          have h31 : ML * (1 / 2) ≤ ML * lg := mul_le_mul_of_nonneg_left hlg (by linarith)
          linarith
        have h4 : ML / 2 ≤ ML * lg := by
          have := mul_le_mul_of_nonneg_left hlg (by linarith : (0 : ℝ) ≤ ML)
          linarith
        have h5 : ML / 2 * (1152 * ML) ≤ ML * lg * N :=
          mul_le_mul h4 h3 (by positivity) (by positivity)
        nlinarith
      exact abs_le_of_sq_le_sq' h2 (by positivity) |>.2
    rw [hQeq]; exact h1
  have hLipc : 2 * Lip ≤ 3 * ((N : ℝ) ^ 2 * Real.sqrt (N * ML * Real.log N)) := by
    rw [← hlgdef, ← hQ]
    have h1 : 24 * C * ML * ML ≤ (N : ℝ) * N := mul_le_mul hNa hNb (by positivity) hNpos.le
    have h2 : 24 * C * ML * ML * (24 * ML) ≤ (N : ℝ) * N * Q :=
      mul_le_mul h1 hQge (by positivity) (by positivity)
    have h3 : 2 * Lip ≤ 8 * C * (ML * ML * ML) := by
      have h4 : 4 * (2 : ℝ) ^ d * (ML * ML * ML) ≤ 4 * C * (ML * ML * ML) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hP : 0 ≤ C * (ML * ML * ML) := by positivity
    nlinarith
  have hδLdef : δL = Real.sqrt (ML * Real.log N / N) := by rw [hδL, hlgdef]
  have hEL := l1_g3 hσ hσ1 d X h_indep hX hlaw N K hN12 hK hKN hML hLip
    hδLdef hLipc (by rw [← hC]; exact hsmallL)
  obtain ⟨TB, hTB⟩ : ∃ TB : ℝ, TB = Real.log (2 * ((N ^ 3 : ℕ) : ℝ) ^ d * (N : ℝ) ^ 3) :=
    ⟨_, rfl⟩
  have hg3 : ((N ^ 3 : ℕ) : ℝ) = (N : ℝ) ^ 3 := by push_cast; rfl
  have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ (by linarith)
  have hNd : (1 : ℝ) ≤ ((N : ℝ) ^ 3) ^ d := one_le_pow₀ hN3
  have hBarg : (2 : ℝ) ≤ 2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3 := by nlinarith
  have hTB0 : 0 < TB := by
    rw [hTB, hg3]; exact Real.log_pos (by linarith)
  have hTBle : TB ≤ (3 * (d : ℝ) + 5) * lg := by
    have h2 : 2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3 ≤ (N : ℝ) ^ (3 * d + 5) := by
      have h1 : (2 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      calc 2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3
          = 2 * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) := by ring
        _ ≤ (N : ℝ) ^ 2 * (((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (N : ℝ) ^ (3 * d + 5) := by rw [← pow_mul]; ring
    rw [hTB, hg3, hlgdef]
    calc Real.log (2 * ((N : ℝ) ^ 3) ^ d * (N : ℝ) ^ 3)
        ≤ Real.log ((N : ℝ) ^ (3 * d + 5)) := Real.log_le_log (by linarith) h2
      _ = (3 * (d : ℝ) + 5) * Real.log N := by rw [Real.log_pow]; push_cast; ring
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 3 * Real.sqrt (N * ML * TB) := ⟨_, rfl⟩
  have hsqTB : Real.sqrt (N * ML * TB) ≤ Aa * Q := by
    rw [hAa, hQ, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hTBle (by positivity : (0 : ℝ) ≤ N * ML)
    exact this.trans (le_of_eq (by ring))
  have hεpos : 0 < ε := by
    rw [hε]; have : 0 < Real.sqrt (N * ML * TB) := Real.sqrt_pos.mpr (by positivity)
    linarith
  have hεle : ε ≤ 3 * Aa * δL * N := by
    rw [hε]
    calc 3 * Real.sqrt (N * ML * TB) ≤ 3 * (Aa * Q) := by linarith
      _ = 3 * Aa * δL * N := by rw [hQeq]; ring
  have hAaδ : 48 * Aa * δL ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hCAa hδL0
    linarith
  have hεN : ε ≤ N / 16 := by
    have h1 : 3 * Aa * δL * N ≤ 1 / 16 * N := mul_le_mul_of_nonneg_right (by linarith) hNpos.le
    linarith
  obtain ⟨thr, hthr⟩ : ∃ thr : ℝ, thr = ε + 2 * (N * Lip) * (1 / ((N ^ 3 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hthrle : thr ≤ 6 * Aa * δL * N := by
    have hN2' : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    have e : 2 * ((N : ℝ) * Lip) * (1 / (N : ℝ) ^ 3) = 2 * Lip / (N : ℝ) ^ 2 := by field_simp
    have h1 : 2 * Lip / (N : ℝ) ^ 2 ≤ 3 * Q := by
      rw [div_le_iff₀ hN2']
      have := hLipc
      rw [← hlgdef, ← hQ] at this
      linarith
    rw [hthr, hg3, e]
    have h2 : 3 * Q = 3 * δL * N := by rw [hQeq]; ring
    have h3 : 3 * δL * N ≤ 3 * Aa * δL * N := by
      have : 0 ≤ δL * N := by positivity
      nlinarith
    linarith
  have hthr0 : 0 ≤ thr := by rw [hthr]; positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = thr / N := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδle : δ ≤ 6 * Aa * δL := by
    rw [hδ, div_le_iff₀ hNpos]; exact hthrle
  have hδ8 : δ ≤ 1 / 8 := by linarith
  have hconstM : ∀ u, heatTorus d (2 * Real.pi ^ 2 * σ) u ≤ ML := fun u => by
    rw [hML]; exact heatTorus_le hcσ d u
  have hconstL : ∀ u u', |heatTorus d (2 * Real.pi ^ 2 * σ) u - heatTorus d (2 * Real.pi ^ 2 * σ) u'|
      ≤ Lip * dist u u' := fun u u' => by
    rw [hLip]; exact heatTorus_lipschitz hcσ d u u'
  have hEB0 := heat_normalisation_whp hσ d X h_indep hX hlaw N (pow_pos hN 3) hconstM hconstL
    hLip0 hεpos
  rw [← hthr] at hEB0
  have hEB : μ.real {ω | ∃ x : FlatTorus d,
      thr < |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N|}
      ≤ 1 / (N : ℝ) ^ 3 := by
    refine hEB0.trans ?_
    rw [hg3]
    have hε2 : ε ^ 2 = 9 * (N * ML * TB) := by
      rw [hε, mul_pow, Real.sq_sqrt (by positivity)]; norm_num
    exact g28_prob_arith hNpos (by linarith) hTB0 (by positivity : (0 : ℝ) < ((N : ℝ) ^ 3) ^ d)
      (by positivity : (0 : ℝ) < (N : ℝ) ^ 3) (by rw [hTB, hg3]) hεpos (by linarith) hε2
  -- the three statements
  have hAa0 : 0 ≤ Aa := by linarith
  have hnC : normC d * δp = 6 * Aa * (A * δp) := by
    rw [hAa, hA]; unfold normC; ring
  have hnormle : δ ≤ normC d * δp := by
    have h6 : 0 ≤ 6 * Aa := by positivity
    have h1 : 6 * Aa * δL ≤ 6 * Aa * (A * δp) := mul_le_mul_of_nonneg_left hδLle h6
    rw [hnC]; linarith
  have hn8 : normC d * δp ≤ 1 / 8 := by
    have hAδ : 0 ≤ A * δp := mul_nonneg hA0 hδp0
    have hA2 : A * δp ≤ A ^ 2 * δp := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hA1) hA0) hδp0]
    have h1 : 48 * Aa * (A * δp) ≤ C * (A ^ 2 * δp) := mul_le_mul hCAa hA2 hAδ hC0
    have h0 : 0 ≤ C * A ^ 2 * δp := by positivity
    have h2 : C * A ^ 2 * δp ≤ C * A ^ 2 * δp * Real.sqrt K := le_mul_of_one_le_right h0 hsK1
    rw [hnC]; linarith
  have hPN : μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ normC d * δp}
      ≤ 1 / (N : ℝ) ^ 3 := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) hEB
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    by_contra hcon
    apply hω
    intro j
    have hgoodB : ∀ x : FlatTorus d,
        |∑ j ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x - X j ω) - N| ≤ thr := by
      intro x
      by_contra h
      exact hcon ⟨x, not_le.mp h⟩
    have h := hgoodB (X j ω)
    have e : heatRho d σ N (fun j => X j ω) j - 1
        = (∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X l ω) - N) / N := by
      unfold heatRho; field_simp
    rw [e, abs_div, abs_of_pos hNpos]
    refine le_trans (div_le_div_of_nonneg_right h hNpos.le) ?_
    rw [← hδ]; exact hnormle
  have hPL : μ.real {ω | ¬ ∀ l, 2 ≤ l → l ≤ K → ∀ i : Fin N,
        ∑ a : Fin N, |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ l) a i
            - heatP d σ l (X a ω - X i ω)|
          ≤ (N : ℝ) * (h4C d * δp * Real.sqrt l)}
      ≤ 2 / (N : ℝ) ^ 3 := by
    refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) hEL
    intro ω hω hgood
    apply hω
    intro l hl2 hlK i
    refine (hgood l hl2 hlK i).trans ?_
    have hl0 := l1C_nonneg d
    have e : h4C d = l1C d * A := by rw [hA]; rfl
    rw [e]
    have h1 : l1C d * δL ≤ l1C d * (A * δp) := mul_le_mul_of_nonneg_left hδLle hl0
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (l : ℝ))
    have h3 := mul_le_mul_of_nonneg_left h2 hNpos.le
    calc _ ≤ _ := h3
      _ = _ := by ring
  exact ⟨hn8, hPN, hPL⟩

/-- **Target (1): the normalisation with probability.** Under the hypotheses of
    `kernel_theorem_G28`: `normC d · δ' ≤ 1/8`, and except on an event of probability at most
    `1/N³`, `|ρ_a - 1| ≤ normC d · δ'` for all `a`. -/
theorem norm_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    normC d * δp ≤ 1 / 8 ∧
    μ.real {ω | ¬ ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ normC d * δp}
      ≤ 1 / (N : ℝ) ^ 3 :=
  ⟨(good_events hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange).1, (good_events hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange).2.1⟩

/-- **Target (2), `l = 1`: the `ℓ¹` kernel bound for one step, deterministic.** On the
    normalisation event `|ρ_a - 1| ≤ δ ≤ 1/8`:
    `∑_i |N P(i,b) - p_σ(x_i - x_b)| ≤ N · 4δ(1 + δ)` (from (H1), (H1a), (H2)). -/
theorem H4_one {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) (hN : 1 ≤ N) (x : ℕ → FlatTorus d)
    {δ : ℝ} (hδ : δ ≤ 1 / 8) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ) (b : Fin N) :
    ∑ i : Fin N, |(N : ℝ) * ((torusWalk d σ N x) ^ 1) i b - torusQ d σ N x 1 i b|
      ≤ (N : ℝ) * (4 * δ * (1 + δ)) := by
  obtain ⟨hδ0, hP0, hrow, hq0, hqm, hqd, hH1, hH1a, hH1b, hH2⟩ := torus_hyps hσ d N hN x hδ hρ
  have hterm : ∀ i : Fin N,
      |(N : ℝ) * ((torusWalk d σ N x) ^ 1) i b - torusQ d σ N x 1 i b|
        ≤ 4 * δ * torusQ d σ N x 1 i b := by
    intro i
    have hq := hq0 1 le_rfl i b
    have hθ := hH1a i b
    have h1 := hH1 i b
    have e : ∀ q θ : ℝ, q * (1 + θ) - q = q * θ := fun q θ => by ring
    rw [pow_one, h1, e, abs_mul, abs_of_nonneg hq]
    have h2 := mul_le_mul_of_nonneg_left hθ hq
    linarith
  have h4 : 0 ≤ 4 * δ := by linarith
  calc ∑ i : Fin N, |(N : ℝ) * ((torusWalk d σ N x) ^ 1) i b - torusQ d σ N x 1 i b|
      ≤ ∑ i : Fin N, 4 * δ * torusQ d σ N x 1 i b := Finset.sum_le_sum fun i _ => hterm i
    _ = 4 * δ * ∑ i : Fin N, torusQ d σ N x 1 i b := by rw [Finset.mul_sum]
    _ ≤ 4 * δ * ((N : ℝ) * (1 + δ)) := mul_le_mul_of_nonneg_left (hH2 b) h4
    _ = (N : ℝ) * (4 * δ * (1 + δ)) := by ring

/-- HYPOTHESES (H5a)--(H5d) in the instantiated closed form, as one proposition
    (`TorusReduction.RemainingHyps` without (H4)). -/
def RemainingH5 (d : ℕ) (σ : ℝ) (N : ℕ) (x : ℕ → FlatTorus d) (k : ℕ)
    (hh : ℕ → Fin N → Fin N → ℝ) (cα cβ η : ℝ) : Prop :=
  (∀ m, 1 ≤ m → m ≤ k → ∀ i b : Fin N,
      |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
          - torusQ d σ N x (m + 1) b i) - hh m i b|
        ≤ cα * η ^ 2 * (1 / Real.sqrt m) * torusM d σ (6 * m)) ∧
  (∀ m, 1 ≤ m → m ≤ k → ∀ i : Fin N,
      ∑ b : Fin N, |((∑ j : Fin N, torusWalk d σ N x b j * torusQ d σ N x m j i)
          - torusQ d σ N x (m + 1) b i) - hh m i b|
        ≤ (N : ℝ) * (cα * η ^ 2 * (1 / Real.sqrt m))) ∧
  (∀ m, 1 ≤ m → m ≤ k → ∀ i b : Fin N,
      |hh m i b| ≤ cβ * η * (1 / Real.sqrt m) * torusM d σ (6 * m)) ∧
  (∀ m, 1 ≤ m → m ≤ k → ∀ i : Fin N,
      ∑ b : Fin N, |hh m i b| ≤ (N : ℝ) * (cβ * η * (1 / Real.sqrt m)))

/-- **Target (3): the reduction for a random sample, with (N), (H3), (H4) discharged.**
    Under the hypotheses of `kernel_theorem_G28`, except on an event of probability at most
    `6/N³` (the event of `kernel_theorem_G28`, the normalisation event, the `ℓ¹` event), for
    every `1 ≤ k ≤ K`: whenever HYPOTHESES (H5a)--(H5d) hold at this sample point
    (`RemainingH5`, with `η = δ'`, for an arbitrary family `hh` and constants `cα, cβ ≥ 0`),
    the closed bound of `torus_reduction_closed` holds with `c_δ = normC d`,
    `c_D = kernelC1 d`, `c_E = h4C d` ((H4) in the `ℓ¹` form, without the factor `m_l`). -/
theorem torus_reduction_sample_l1 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (cα cβ : ℝ) (hh : ℕ → Fin N → Fin N → ℝ),
          0 ≤ cα → 0 ≤ cβ →
          RemainingH5 d σ N (fun j => X j ω) k hh cα cβ δp →
          |((torusWalk d σ N (fun j => X j ω)) ^ (k + 1)).trace - torusM d σ (k + 1)
              - torusPi d σ N (fun j => X j ω) k hh|
            ≤ (Real.sqrt 2) ^ d
                * (2 * (4 * normC d) * kernelC1 d + 2 * (14 * normC d ^ 2) + cα
                    + 2 * (2 * (Real.sqrt 2) ^ d * cα + cα
                        + (Real.sqrt 2) ^ d * kernelC1 d * cβ + h4C d * cβ))
                * δp ^ 2 * k * torusM d σ (k + 1)}
      ≤ 6 / (N : ℝ) ^ 3 := by
  have hG := kernel_theorem_G28 hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  obtain ⟨hn8, hPN, hPL⟩ := good_events hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  refine real_le_of_subset3 hG hPN hPL ?_ (by ring)
  intro ω hbad
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  obtain ⟨⟨hgG, hgN⟩, hgL⟩ := hcon
  apply hbad
  intro k hk1 hkK cα cβ hh hcα hcβ hrem
  obtain ⟨H5a, H5b, H5c, H5d⟩ := hrem
  have hη : 0 ≤ δp := by
    rw [hδp]
    exact Real.sqrt_nonneg _
  have hC : 0 ≤ kernelC1 d := TraceG29.kernelC1_nonneg d
  have hcδ : 0 ≤ normC d := normC_nonneg d
  have hcE : 0 ≤ h4C d := h4C_nonneg d
  have hkK' : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hkK
  have hrange' : kernelC1 d * δp * Real.sqrt k ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkK') (mul_nonneg hC hη)).trans hrange
  have hρ : ∀ a : Fin N, |heatRho d σ N (fun j => X j ω) a - 1| ≤ normC d * δp := hgN
  have H3 : ∀ l, 1 ≤ l → l ≤ k → ∀ a i : Fin N,
      |(N : ℝ) * ((torusWalk d σ N (fun j => X j ω)) ^ l) a i
          - torusQ d σ N (fun j => X j ω) l a i|
        ≤ kernelC1 d * δp * Real.sqrt l * torusM d σ l :=
    fun l hl hlk a i => hgG l hl (hlk.trans hkK) a i
  have H4 : ∀ l, 1 ≤ l → l ≤ k → ∀ b : Fin N,
      ∑ i : Fin N, |(N : ℝ) * ((torusWalk d σ N (fun j => X j ω)) ^ l) i b
          - torusQ d σ N (fun j => X j ω) l i b|
        ≤ (N : ℝ) * (h4C d * δp * Real.sqrt l) := by
    intro l hl hlk b
    rcases Nat.lt_or_ge l 2 with h2 | h2
    · have hl1 : l = 1 := by omega
      subst hl1
      refine (H4_one hσ d N (by omega) (fun j => X j ω) hn8 hρ b).trans ?_
      simp only [Nat.cast_one, Real.sqrt_one, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      have h := h4C_ge d
      have hnd : 0 ≤ normC d * δp := mul_nonneg hcδ hη
      have h1 : 4 * (normC d * δp) * (1 + normC d * δp) ≤ 4 * (normC d * δp) * (9 / 8) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h2' := mul_le_mul_of_nonneg_right h hη
      linarith
    · exact hgL l h2 (hlk.trans hkK) b
  exact torus_reduction_closed hσ d N (by omega) (fun j => X j ω) hn8 hρ k hk1 hh
    hcα hcβ hC hcE hcδ hη le_rfl hrange' H3 H4 H5a H5b H5c H5d

end TorusReductionL1

/-! ### Delocalisation: the inequality of `cor:deloc` before the choice of the number of steps -/

namespace Delocalisation

/-- Powers of a matrix on an eigenvector. -/
theorem pow_mulVec_eig {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ) (u : n → ℝ)
    (s : ℝ) (hSu : S *ᵥ u = s • u) (k : ℕ) : (S ^ k) *ᵥ u = s ^ k • u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hSu, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- **Delocalisation, deterministic step.** For a real symmetric matrix `S`, a vector `u` with
    `S u = s u`, `s ≠ 0`, `∑ u_a² = 1` and every `k`:
    `u_a² ≤ (S^{2k})_{aa} / s^{2k}`. -/
theorem deloc_det {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ) (hS : S.IsHermitian)
    (u : n → ℝ) (s : ℝ) (hs : s ≠ 0) (hSu : S *ᵥ u = s • u) (hu : ∑ a, u a ^ 2 = 1)
    (k : ℕ) (a : n) :
    u a ^ 2 ≤ (S ^ (2 * k)) a a / s ^ (2 * k) := by
  have hk := pow_mulVec_eig S u s hSu k
  have e1 : s ^ k * u a = ∑ b, (S ^ k) a b * u b := by
    have h := congrFun hk a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hsym : ∀ b, (S ^ k) b a = (S ^ k) a b := fun b => by
    have h := (hS.pow k).apply a b
    simpa using h
  have e2 : (S ^ (2 * k)) a a = ∑ b, (S ^ k) a b ^ 2 := by
    rw [two_mul, pow_add, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [hsym b, pow_two]
  have cs : (∑ b, (S ^ k) a b * u b) ^ 2 ≤ (∑ b, (S ^ k) a b ^ 2) * ∑ b, u b ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => (S ^ k) a b) u
  rw [← e1, ← e2, hu, mul_one] at cs
  have e3 : s ^ (2 * k) = (s ^ k) ^ 2 := pow_mul' s 2 k
  have hsk : s ^ k ≠ 0 := pow_ne_zero k hs
  have hpos : 0 < (s ^ k) ^ 2 := by positivity
  rw [e3, le_div_iff₀ hpos]
  calc u a ^ 2 * (s ^ k) ^ 2 = (s ^ k * u a) ^ 2 := by ring
    _ ≤ (S ^ (2 * k)) a a := cs

/-- **The diagonals of the powers of `S` and of `P` coincide.** `S = D^{1/2} P D^{-1/2}`. -/
theorem symGraph_pow_diag {n : Type} [Fintype n] [DecidableEq n] (K : n → n → ℝ) (rho : n → ℝ)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) (k : ℕ) (a : n) :
    (symGraph K rho ^ k) a a = (walkMatrix K rho ^ k) a a := by
  have h := conj_pow_entry (symGraph K rho) (walkMatrix K rho)
    (fun i => Real.sqrt (∑ j, K i j / (rho i * rho j)))
    (fun i => Real.sqrt_pos.mpr (hD i)) (fun i l => symGraph_conj K rho hD i l) k
  rw [h a a]
  exact mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (hD a)).ne'

/-- **Delocalisation for a graph, deterministic.** Symmetric kernel `K`, positive degrees,
    `S = symGraph K rho`, `P = walkMatrix K rho`. If the diagonal entry of `P^{2k}` satisfies
    `|N (P^{2k})_{aa} - m| ≤ D` with `D ≤ m`, then for every `u` with `S u = s u`, `s > 0`,
    `∑ u² = 1`: `u_a² ≤ 2 m / (N s^{2k})`. -/
theorem deloc_graph {n : Type} [Fintype n] [DecidableEq n] (K : n → n → ℝ) (rho : n → ℝ)
    (hK : ∀ i j, K i j = K j i) (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l))
    {N m D s : ℝ} (hN : 0 < N) (hs : 0 < s) (k : ℕ) (a : n)
    (hker : |N * (walkMatrix K rho ^ (2 * k)) a a - m| ≤ D) (hDm : D ≤ m)
    (u : n → ℝ) (hSu : symGraph K rho *ᵥ u = s • u) (hu : ∑ b, u b ^ 2 = 1) :
    u a ^ 2 ≤ 2 * m / (N * s ^ (2 * k)) := by
  have h := deloc_det (symGraph K rho) (symGraph_isHermitian K rho hK) u s hs.ne' hSu hu k a
  rw [symGraph_pow_diag K rho hD (2 * k) a] at h
  have hP : (walkMatrix K rho ^ (2 * k)) a a ≤ 2 * m / N := by
    rw [le_div_iff₀ hN]
    have := (abs_le.mp hker).2
    linarith
  have hsp : 0 < s ^ (2 * k) := pow_pos hs _
  calc u a ^ 2 ≤ (walkMatrix K rho ^ (2 * k)) a a / s ^ (2 * k) := h
    _ ≤ (2 * m / N) / s ^ (2 * k) := by gcongr
    _ = 2 * m / (N * s ^ (2 * k)) := by rw [div_div]

/-- **Delocalisation on the event of the kernel theorem (inequality of the proof of `cor:deloc`
    before the choice of `k`).** Under the hypotheses of `kernel_theorem_G28`, except on its event
    (probability at most `3/N³`): for all `k ≥ 1` with `2k ≤ K`, every index `a` and every vector
    `u` with `S u = s u`, `s > 0`, `∑ u² = 1`:
    `u_a² ≤ 2 m_{2k} / (N s^{2k})`, `m_{2k} = p_{2kσ}(0)`. -/
theorem deloc_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → 2 * k ≤ K → ∀ (a : Fin N) (u : Fin N → ℝ) (s : ℝ), 0 < s →
        symGraph (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
            (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) *ᵥ u = s • u →
        ∑ b, u b ^ 2 = 1 →
        u a ^ 2 ≤ 2 * heatTorus d (2 * Real.pi ^ 2 * (((2 * k : ℕ) : ℝ) * σ)) 0
            / ((N : ℝ) * s ^ (2 * k))}
      ≤ 3 / (N : ℝ) ^ 3 := by
  have h := kernel_theorem_G28 hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk hkK a u s hs hSu hu
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hKsymm : ∀ a j : Fin N,
      heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω)
        = heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X a ω) := fun a j => by
    rw [← heatTorus_even d _ (X j ω - X a ω), neg_sub]
  have hrho : ∀ a : Fin N, 0 < heatRho d σ N (fun j => X j ω) a := fun a => by
    unfold heatRho
    exact div_pos (Finset.sum_pos (fun l _ => heatTorus_pos hcσ d _)
      ⟨0, Finset.mem_range.mpr hN⟩) hNpos
  have hD : ∀ i : Fin N, 0 < ∑ l : Fin N,
      heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)
        / (heatRho d σ N (fun j => X j ω) i * heatRho d σ N (fun j => X j ω) l) := fun i =>
    Finset.sum_pos (fun l _ => div_pos (heatTorus_pos hcσ d _) (mul_pos (hrho i) (hrho l)))
      Finset.univ_nonempty
  have h1 := hgood (2 * k) (by omega) hkK a a
  rw [sub_self, heatP_of_ne d σ (by omega)] at h1
  have hc : 0 ≤ kernelC1 d * δp := by
    rw [hδp]; exact mul_nonneg (TraceG29.kernelC1_nonneg d) (Real.sqrt_nonneg _)
  have hcast : (((2 * k : ℕ) : ℝ)) ≤ (K : ℝ) := by exact_mod_cast hkK
  have hc1 : kernelC1 d * δp * Real.sqrt ((2 * k : ℕ) : ℝ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcast) hc) hrange
  have hm0 : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * (((2 * k : ℕ) : ℝ) * σ)) 0 :=
    (heatTorus_pos (by
      have : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
      positivity) d 0).le
  exact deloc_graph (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
    (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) hKsymm hD hNpos hs k a h1
    (mul_le_of_le_one_left hm0 hc1) u hSu hu

end Delocalisation

/-! ### The corrected estimator on the sampled graph, in series form (`cor:kernel-corrected`, finite form) -/

namespace Corrected

open CTG.Reals.TraceG29

/-- The sequence `b` with its value at the index `0` replaced by `0`. -/
noncomputable def zs (b : ℕ → ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else b j

theorem zs_zero (b : ℕ → ℝ) : zs b 0 = 0 := by simp [zs]

theorem zs_succ (b : ℕ → ℝ) (j : ℕ) : zs b (j + 1) = b (j + 1) := by simp [zs]

theorem zs_of_pos (b : ℕ → ℝ) {j : ℕ} (hj : 1 ≤ j) : zs b j = b j := by
  have h : j ≠ 0 := by omega
  simp [zs, h]

/-- The `j`-th term of the corrected series:
    `w_j(τ) [ b°_j - (τ/2) (b_{j+2} - 2 b_{j+1} + b°_j) ]`. -/
noncomputable def corrTerm (τ : ℝ) (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  pw τ j * (zs b j - τ / 2 * (b (j + 2) - 2 * b (j + 1) + zs b j))

/-- The corrected quantity in series form. -/
noncomputable def corrSeries (τ : ℝ) (b : ℕ → ℝ) : ℝ := ∑' j : ℕ, corrTerm τ b j

theorem abs_sub_le' (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

/-- `∑_{j≥0} w_j b°_j = ∑_{j≥1} w_j b_j`. -/
theorem zs_hasSum {τ : ℝ} {b : ℕ → ℝ} {E0 : ℝ}
    (h : HasSum (fun j : ℕ => pw τ (j + 1) * b (j + 1)) E0) :
    HasSum (fun j : ℕ => pw τ j * zs b j) E0 := by
  have h1 : HasSum (fun j : ℕ => (fun i : ℕ => pw τ i * zs b i) (j + 1)) E0 := by
    have hf : (fun j : ℕ => (fun i : ℕ => pw τ i * zs b i) (j + 1))
        = fun j : ℕ => pw τ (j + 1) * b (j + 1) := by
      funext j
      show pw τ (j + 1) * zs b (j + 1) = pw τ (j + 1) * b (j + 1)
      rw [zs_succ]
    rw [hf]
    exact h
  have h2 := (hasSum_nat_add_iff (f := fun i : ℕ => pw τ i * zs b i) 1).1 h1
  have e : E0 + ∑ i ∈ Finset.range 1, (fun i : ℕ => pw τ i * zs b i) i = E0 := by
    rw [Finset.sum_range_one]
    show E0 + pw τ 0 * zs b 0 = E0
    rw [zs_zero]
    ring
  rw [e] at h2
  exact h2

/-- **(1) The corrected series through the three Poisson means.** If
    `E0 = ∑_{j≥1} w_j b_j`, `E1 = ∑_{i≥0} w_i b_{i+1}`, `E2 = ∑_{i≥0} w_i b_{i+2}`, then the corrected
    series converges to `(1 - τ/2) E0 + τ E1 - (τ/2) E2 = E0 - (τ/2)(E2 - 2 E1 + E0)`. -/
theorem corr_hasSum {τ : ℝ} {b : ℕ → ℝ} {E0 E1 E2 : ℝ}
    (h0 : HasSum (fun j : ℕ => pw τ (j + 1) * b (j + 1)) E0)
    (h1 : HasSum (fun j : ℕ => pw τ j * b (j + 1)) E1)
    (h2 : HasSum (fun j : ℕ => pw τ j * b (j + 2)) E2) :
    HasSum (corrTerm τ b) ((1 - τ / 2) * E0 + τ * E1 - τ / 2 * E2) := by
  have h := (((zs_hasSum h0).mul_left (1 - τ / 2)).add (h1.mul_left τ)).sub
    (h2.mul_left (τ / 2))
  have hf : corrTerm τ b = fun j : ℕ => (1 - τ / 2) * (pw τ j * zs b j)
      + τ * (pw τ j * b (j + 1)) - τ / 2 * (pw τ j * b (j + 2)) := by
    funext j
    unfold corrTerm
    ring
  rw [hf]
  exact h

/-- One term of the difference of two corrected series. -/
theorem term_bound {τ w e0 e1 e2 E0 E1 E2 : ℝ} (hτ : 0 ≤ τ) (hw : 0 ≤ w)
    (h0 : |e0| ≤ E0) (h1 : |e1| ≤ E1) (h2 : |e2| ≤ E2) :
    |w * ((1 - τ / 2) * e0 + τ * e1 - τ / 2 * e2)|
      ≤ w * ((1 + τ / 2) * E0 + τ * E1 + τ / 2 * E2) := by
  rw [abs_mul, abs_of_nonneg hw]
  refine mul_le_mul_of_nonneg_left ?_ hw
  have a0 := abs_le.mp h0
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have p0 : τ * e0 ≤ τ * E0 := mul_le_mul_of_nonneg_left a0.2 hτ
  have p0' : τ * (-E0) ≤ τ * e0 := mul_le_mul_of_nonneg_left a0.1 hτ
  have p1 : τ * e1 ≤ τ * E1 := mul_le_mul_of_nonneg_left a1.2 hτ
  have p1' : τ * (-E1) ≤ τ * e1 := mul_le_mul_of_nonneg_left a1.1 hτ
  have p2 : τ * e2 ≤ τ * E2 := mul_le_mul_of_nonneg_left a2.2 hτ
  have p2' : τ * (-E2) ≤ τ * e2 := mul_le_mul_of_nonneg_left a2.1 hτ
  rw [abs_le]
  constructor <;> linarith

/-- **(2) Deterministic comparison, abstract form.** `τ ≥ 2`; sequences `a_j`, `m_j` with
    `m_j ≥ 0` non-increasing for `j ≥ 1`; `T = ∑_{j≥1} w_j m_j`; `|a_j - m_j| ≤ c √j m_j` for
    `1 ≤ j ≤ J + 2`; `|a_j| ≤ B`, `|m_j| ≤ B'` for `j > J`. Then the corrected series of `m`
    converges and
    `|corr(a) - corr(m)| ≤ (1 + (11/4) τ) c √(J+2) T + (1 + 2τ)(B + B') ∑_{j>J} w_j`.
    HYPOTHESIS: the corrected series of `a` converges, with sum `CA` (`hCA`). -/
theorem corr_split {τ : ℝ} (hτ : 2 ≤ τ) (a m : ℕ → ℝ) (J : ℕ) {CA T B B' c : ℝ} (hc : 0 ≤ c)
    (hm0 : ∀ j, 1 ≤ j → 0 ≤ m j) (hanti : ∀ j, 1 ≤ j → m (j + 1) ≤ m j)
    (hT : HasSum (fun j : ℕ => pw τ (j + 1) * m (j + 1)) T)
    (hCA : HasSum (corrTerm τ a) CA)
    (hlow : ∀ j, 1 ≤ j → j ≤ J + 2 → |a j - m j| ≤ c * Real.sqrt j * m j)
    (hB : ∀ j, J < j → |a j| ≤ B) (hB' : ∀ j, J < j → |m j| ≤ B') :
    |CA - corrSeries τ m| ≤ (1 + 11 / 4 * τ) * (c * Real.sqrt ((J + 2 : ℕ) : ℝ)) * T
        + (1 + 2 * τ) * (B + B') * ptail τ J := by
  have hτ0 : 0 ≤ τ := by linarith
  have hpw : ∀ j, 0 ≤ pw τ j := fun j => pw_nonneg hτ0 j
  have hle1 : ∀ j, m (j + 1) ≤ m 1 := by
    intro j
    induction j with
    | zero => exact le_refl _
    | succ k ih => exact le_trans (hanti (k + 1) (by omega)) ih
  -- the two shifted Poisson means
  have hs : Summable (fun j : ℕ => pw τ j * m 1) := (pw_hasSum τ).summable.mul_right _
  have hs1 : Summable (fun j : ℕ => pw τ j * m (j + 1)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hpw j) (hm0 (j + 1) (by omega)))
      (fun j => mul_le_mul_of_nonneg_left (hle1 j) (hpw j)) hs
  have hs2 : Summable (fun j : ℕ => pw τ j * m (j + 2)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hpw j) (hm0 (j + 2) (by omega)))
      (fun j => mul_le_mul_of_nonneg_left (hle1 (j + 1)) (hpw j)) hs
  obtain ⟨T1, hT1⟩ : ∃ T1 : ℝ, HasSum (fun j : ℕ => pw τ j * m (j + 1)) T1 := ⟨_, hs1.hasSum⟩
  obtain ⟨T2, hT2⟩ : ∃ T2 : ℝ, HasSum (fun j : ℕ => pw τ j * m (j + 2)) T2 := ⟨_, hs2.hasSum⟩
  have hCM := corr_hasSum hT hT1 hT2
  have eCM : corrSeries τ m = (1 - τ / 2) * T + τ * T1 - τ / 2 * T2 := by
    unfold corrSeries
    exact hCM.tsum_eq
  rw [eCM]
  -- `T2 ≤ T1 ≤ (3/2) T`
  have hm1 : 0 ≤ m 1 := hm0 1 (le_refl _)
  have hEm : 0 ≤ Real.exp (-τ) * m 1 := mul_nonneg (Real.exp_pos _).le hm1
  have h1T : pw τ 1 * m 1 ≤ T :=
    le_hasSum hT 0 (fun j _ => mul_nonneg (hpw (j + 1)) (hm0 (j + 1) (by omega)))
  have hpw1 : pw τ 1 = Real.exp (-τ) * τ := by
    unfold pw
    simp
  have h1T' : 2 * (Real.exp (-τ) * m 1) ≤ T := by
    rw [hpw1] at h1T
    have h := mul_le_mul_of_nonneg_right hτ hEm
    have e : τ * (Real.exp (-τ) * m 1) = Real.exp (-τ) * τ * m 1 := by ring
    linarith
  have hT0 : 0 ≤ T := by linarith
  have hT12 : T1 ≤ T + Real.exp (-τ) * m 1 := by
    have h := (hasSum_nat_add_iff' (f := fun i : ℕ => pw τ i * m (i + 1)) 1).2 hT1
    have e0 : ∑ i ∈ Finset.range 1, (fun i : ℕ => pw τ i * m (i + 1)) i
        = Real.exp (-τ) * m 1 := by
      rw [Finset.sum_range_one]
      show pw τ 0 * m 1 = Real.exp (-τ) * m 1
      rw [pw_zero]
    rw [e0] at h
    have hterm : ∀ j : ℕ, (fun i : ℕ => pw τ i * m (i + 1)) (j + 1)
        ≤ pw τ (j + 1) * m (j + 1) :=
      fun j => mul_le_mul_of_nonneg_left (hanti (j + 1) (by omega)) (hpw (j + 1))
    have hle := hasSum_le hterm h hT
    linarith
  have hT21 : T2 ≤ T1 :=
    hasSum_le (fun j => mul_le_mul_of_nonneg_left (hanti (j + 1) (by omega)) (hpw j)) hT2 hT1
  have hT1' : T1 ≤ 3 / 2 * T := by linarith
  have hT2' : T2 ≤ 3 / 2 * T := by linarith
  -- the majorant of the low terms
  obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, u = fun j : ℕ =>
      pw τ j * ((1 + τ / 2) * zs m j + τ * m (j + 1) + τ / 2 * m (j + 2)) := ⟨_, rfl⟩
  have hu' : ∀ j, u j = pw τ j * ((1 + τ / 2) * zs m j + τ * m (j + 1) + τ / 2 * m (j + 2)) := by
    intro j
    rw [hu]
  have hU : HasSum u ((1 + τ / 2) * T + τ * T1 + τ / 2 * T2) := by
    have h := (((zs_hasSum hT).mul_left (1 + τ / 2)).add (hT1.mul_left τ)).add
      (hT2.mul_left (τ / 2))
    have hf : u = fun j : ℕ => (1 + τ / 2) * (pw τ j * zs m j) + τ * (pw τ j * m (j + 1))
        + τ / 2 * (pw τ j * m (j + 2)) := by
      funext j
      rw [hu' j]
      ring
    rw [hf]
    exact h
  have hzs0 : ∀ j, 0 ≤ zs m j := by
    intro j
    by_cases hj : j = 0
    · rw [hj, zs_zero]
    · rw [zs_of_pos m (by omega)]
      exact hm0 j (by omega)
  have hu0 : ∀ j, 0 ≤ u j := by
    intro j
    rw [hu' j]
    exact mul_nonneg (hpw j) (add_nonneg (add_nonneg (mul_nonneg (by linarith) (hzs0 j))
      (mul_nonneg hτ0 (hm0 (j + 1) (by omega)))) (mul_nonneg (by linarith) (hm0 (j + 2) (by omega))))
  obtain ⟨cs, hcs⟩ : ∃ cs : ℝ, cs = c * Real.sqrt ((J + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hcs]
  have hcs0 : 0 ≤ cs := by
    rw [hcs]
    exact mul_nonneg hc (Real.sqrt_nonneg _)
  have hlow' : ∀ k, 1 ≤ k → k ≤ J + 2 → |a k - m k| ≤ cs * m k := by
    intro k hk hkJ
    have hkR : ((k : ℕ) : ℝ) ≤ ((J + 2 : ℕ) : ℝ) := by exact_mod_cast hkJ
    have h1 : c * Real.sqrt (k : ℝ) ≤ cs := by
      rw [hcs]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hkR) hc
    exact le_trans (hlow k hk hkJ) (mul_le_mul_of_nonneg_right h1 (hm0 k hk))
  -- termwise comparison
  have hkey : ∀ j : ℕ, |corrTerm τ a j - corrTerm τ m j|
      ≤ (if j < J + 1 then cs * u j else 0)
        + (1 + 2 * τ) * (B + B') * (if j < J + 1 then 0 else pw τ j) := by
    intro j
    have e : corrTerm τ a j - corrTerm τ m j = pw τ j * ((1 - τ / 2) * (zs a j - zs m j)
        + τ * (a (j + 1) - m (j + 1)) - τ / 2 * (a (j + 2) - m (j + 2))) := by
      unfold corrTerm
      ring
    rw [e]
    by_cases hj : j < J + 1
    · simp only [if_pos hj, mul_zero, add_zero]
      have h0 : |zs a j - zs m j| ≤ cs * zs m j := by
        by_cases hj0 : j = 0
        · rw [hj0, zs_zero, zs_zero]
          simp
        · rw [zs_of_pos a (by omega), zs_of_pos m (by omega)]
          exact hlow' j (by omega) (by omega)
      have h1 := hlow' (j + 1) (by omega) (by omega)
      have h2 := hlow' (j + 2) (by omega) (by omega)
      have h := term_bound hτ0 (hpw j) h0 h1 h2
      have e2 : cs * u j = pw τ j * ((1 + τ / 2) * (cs * zs m j) + τ * (cs * m (j + 1))
          + τ / 2 * (cs * m (j + 2))) := by
        rw [hu' j]
        ring
      rw [e2]
      exact h
    · simp only [if_neg hj, zero_add]
      have hj1 : 1 ≤ j := by omega
      have h0 : |zs a j - zs m j| ≤ B + B' := by
        rw [zs_of_pos a hj1, zs_of_pos m hj1]
        exact le_trans (abs_sub_le' _ _) (add_le_add (hB j (by omega)) (hB' j (by omega)))
      have h1 : |a (j + 1) - m (j + 1)| ≤ B + B' :=
        le_trans (abs_sub_le' _ _) (add_le_add (hB (j + 1) (by omega)) (hB' (j + 1) (by omega)))
      have h2 : |a (j + 2) - m (j + 2)| ≤ B + B' :=
        le_trans (abs_sub_le' _ _) (add_le_add (hB (j + 2) (by omega)) (hB' (j + 2) (by omega)))
      have h := term_bound hτ0 (hpw j) h0 h1 h2
      have e2 : (1 + 2 * τ) * (B + B') * pw τ j = pw τ j * ((1 + τ / 2) * (B + B')
          + τ * (B + B') + τ / 2 * (B + B')) := by ring
      rw [e2]
      exact h
  have h2 : HasSum (fun j : ℕ => if j < J + 1 then cs * u j else 0)
      (∑ j ∈ Finset.range (J + 1), cs * u j) := by
    have h : HasSum (fun j : ℕ => if j < J + 1 then cs * u j else 0)
        (∑ j ∈ Finset.range (J + 1), (if j < J + 1 then cs * u j else 0)) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by rw [Finset.mem_range] at hb; simp [hb])
    have e : ∑ j ∈ Finset.range (J + 1), (if j < J + 1 then cs * u j else 0)
        = ∑ j ∈ Finset.range (J + 1), cs * u j :=
      Finset.sum_congr rfl (fun j hj => by rw [if_pos (Finset.mem_range.mp hj)])
    rw [e] at h
    exact h
  have h3 := h2.add ((ptail_hasSum' τ J).mul_left ((1 + 2 * τ) * (B + B')))
  have hmain := abs_le_of_hasSum (hCA.sub hCM) h3 hkey
  have hfin : ∑ j ∈ Finset.range (J + 1), cs * u j
      ≤ cs * ((1 + τ / 2) * T + τ * T1 + τ / 2 * T2) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun j _ => hu0 j) hU) hcs0
  have p1 : τ * T1 ≤ τ * (3 / 2 * T) := mul_le_mul_of_nonneg_left hT1' hτ0
  have p2 : τ * T2 ≤ τ * (3 / 2 * T) := mul_le_mul_of_nonneg_left hT2' hτ0
  have hU' : (1 + τ / 2) * T + τ * T1 + τ / 2 * T2 ≤ (1 + 11 / 4 * τ) * T := by linarith
  have hfin2 := mul_le_mul_of_nonneg_left hU' hcs0
  have e3 : cs * ((1 + 11 / 4 * τ) * T) = (1 + 11 / 4 * τ) * cs * T := by ring
  rw [e3] at hfin2
  linarith

/-! ### The sampled side: real symmetric matrices -/

/-- `∑_{j≥0} w_j Tr S^{j+k} = ∑_i s_i^k e^{-τ(1 - s_i)}` for a real symmetric matrix. -/
theorem shifted_trace_hasSum {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (τ : ℝ) (k : ℕ) :
    HasSum (fun j : ℕ => pw τ j * (S ^ (j + k)).trace)
      (∑ i, hS.eigenvalues i ^ k * Real.exp (-(τ * (1 - hS.eigenvalues i)))) := by
  have h : ∀ i ∈ (Finset.univ : Finset n),
      HasSum (fun j : ℕ => pw τ j * hS.eigenvalues i ^ (j + k))
        (hS.eigenvalues i ^ k * Real.exp (-(τ * (1 - hS.eigenvalues i)))) := by
    intro i _
    have h1 := (real_hasSum_exp (τ * hS.eigenvalues i)).mul_left
      (Real.exp (-τ) * hS.eigenvalues i ^ k)
    have e0 : Real.exp (-(τ * (1 - hS.eigenvalues i)))
        = Real.exp (-τ) * Real.exp (τ * hS.eigenvalues i) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e : Real.exp (-τ) * hS.eigenvalues i ^ k * Real.exp (τ * hS.eigenvalues i)
        = hS.eigenvalues i ^ k * Real.exp (-(τ * (1 - hS.eigenvalues i))) := by
      rw [e0]
      ring
    rw [e] at h1
    have hf : (fun j : ℕ => pw τ j * hS.eigenvalues i ^ (j + k))
        = fun j : ℕ => Real.exp (-τ) * hS.eigenvalues i ^ k
            * ((τ * hS.eigenvalues i) ^ j / (j.factorial : ℝ)) := by
      funext j
      unfold pw
      ring
    rw [hf]
    exact h1
  have h2 := hasSum_sum h
  have hf : (fun j : ℕ => pw τ j * (S ^ (j + k)).trace)
      = fun j : ℕ => ∑ i, pw τ j * hS.eigenvalues i ^ (j + k) := by
    funext j
    rw [trace_pow_eq_sum_eigenvalues S hS (j + k), Finset.mul_sum]
  rw [hf]
  exact h2

/-- **The corrected series of the traces `Tr S^j` in spectral form** (no hypotheses): it converges
    to `∑_i e^{-τ(1-s_i)} (1 - (τ/2)(1-s_i)²) - N e^{-τ} (1 - τ/2)`; with `z_i = τ(1-s_i)` this is
    the expression `∑_i [a_i (1 - z_i²/(2τ)) - e^{-τ}(1 - τ/2)]` in the proof of Theorem
    "Corrected estimator". -/
theorem corr_matrix_hasSum {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (τ : ℝ) :
    HasSum (corrTerm τ (fun j : ℕ => (S ^ j).trace))
      (∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i))) * (1 - τ / 2 * (1 - hS.eigenvalues i) ^ 2)
        - (Fintype.card n : ℝ) * Real.exp (-τ) * (1 - τ / 2)) := by
  have h := corr_hasSum (b := fun j : ℕ => (S ^ j).trace) (subtracted_trace_hasSum S hS τ)
    (shifted_trace_hasSum S hS τ 1) (shifted_trace_hasSum S hS τ 2)
  have key : ∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i)))
        * (1 - τ / 2 * (1 - hS.eigenvalues i) ^ 2)
      = (1 - τ / 2) * ∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i)))
        + τ * ∑ i, hS.eigenvalues i ^ 1 * Real.exp (-(τ * (1 - hS.eigenvalues i)))
        - τ / 2 * ∑ i, hS.eigenvalues i ^ 2 * Real.exp (-(τ * (1 - hS.eigenvalues i))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [trace_exp_heat S hS τ] at h
  have e : ∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i)))
          * (1 - τ / 2 * (1 - hS.eigenvalues i) ^ 2)
        - (Fintype.card n : ℝ) * Real.exp (-τ) * (1 - τ / 2)
      = (1 - τ / 2) * (∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i)))
            - (Fintype.card n : ℝ) * Real.exp (-τ))
        + τ * ∑ i, hS.eigenvalues i ^ 1 * Real.exp (-(τ * (1 - hS.eigenvalues i)))
        - τ / 2 * ∑ i, hS.eigenvalues i ^ 2 * Real.exp (-(τ * (1 - hS.eigenvalues i))) := by
    rw [key]
    ring
  rw [e]
  exact h

theorem corrSeries_matrix {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (τ : ℝ) :
    corrSeries τ (fun j : ℕ => (S ^ j).trace)
      = ∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i))) * (1 - τ / 2 * (1 - hS.eigenvalues i) ^ 2)
        - (Fintype.card n : ℝ) * Real.exp (-τ) * (1 - τ / 2) := by
  unfold corrSeries
  exact (corr_matrix_hasSum S hS τ).tsum_eq

theorem hasDerivAt_exp_lin (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (a * y)) (a * Real.exp (a * x)) x := by
  have h : HasDerivAt (fun y : ℝ => a * y) a x := by
    have h0 := (hasDerivAt_id' x).const_mul a
    exact h0.congr_deriv (mul_one a)
  exact h.exp.congr_deriv (mul_comm _ _)

/-- **The sampled side with derivatives.** For a real symmetric matrix `S` and
    `F(x) = Tr exp(x(S-1)) - N e^{-x}`, the quantity `F(τ) - (τ/2) F''(τ)` (derivatives in `τ`)
    equals the corrected series of the traces `Tr S^j`. No hypotheses. -/
theorem corr_matrix_deriv {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (τ : ℝ) :
    (NormedSpace.exp (τ • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-τ)
      - τ / 2 * deriv (deriv (fun x : ℝ =>
          (NormedSpace.exp (x • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-x))) τ
    = corrSeries τ (fun j : ℕ => (S ^ j).trace) := by
  have hf : (fun x : ℝ =>
        (NormedSpace.exp (x • (S - 1))).trace - (Fintype.card n : ℝ) * Real.exp (-x))
      = fun x : ℝ => ∑ i, Real.exp ((hS.eigenvalues i - 1) * x)
          - (Fintype.card n : ℝ) * Real.exp ((-1) * x) := by
    funext x
    rw [trace_exp_heat S hS x]
    have e1 : ∀ i, Real.exp (-(x * (1 - hS.eigenvalues i)))
        = Real.exp ((hS.eigenvalues i - 1) * x) := fun i => by
      congr 1
      ring
    have e2 : Real.exp (-x) = Real.exp ((-1) * x) := by
      congr 1
      ring
    rw [e2, Finset.sum_congr rfl (fun i _ => e1 i)]
  have hd1 : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∑ i, Real.exp ((hS.eigenvalues i - 1) * y)
        - (Fintype.card n : ℝ) * Real.exp ((-1) * y))
      (∑ i, (hS.eigenvalues i - 1) * Real.exp ((hS.eigenvalues i - 1) * x)
        - (Fintype.card n : ℝ) * ((-1) * Real.exp ((-1) * x))) x := by
    intro x
    have hA : HasDerivAt (fun y : ℝ => ∑ i, Real.exp ((hS.eigenvalues i - 1) * y))
        (∑ i, (hS.eigenvalues i - 1) * Real.exp ((hS.eigenvalues i - 1) * x)) x :=
      HasDerivAt.fun_sum (fun i _ => hasDerivAt_exp_lin (hS.eigenvalues i - 1) x)
    have hBd : HasDerivAt (fun y : ℝ => (Fintype.card n : ℝ) * Real.exp ((-1) * y))
        ((Fintype.card n : ℝ) * ((-1) * Real.exp ((-1) * x))) x :=
      (hasDerivAt_exp_lin (-1) x).const_mul _
    exact hA.sub hBd
  have hderiv1 : deriv (fun y : ℝ => ∑ i, Real.exp ((hS.eigenvalues i - 1) * y)
        - (Fintype.card n : ℝ) * Real.exp ((-1) * y))
      = fun x : ℝ => ∑ i, (hS.eigenvalues i - 1) * Real.exp ((hS.eigenvalues i - 1) * x)
        - (Fintype.card n : ℝ) * ((-1) * Real.exp ((-1) * x)) := by
    funext x
    exact (hd1 x).deriv
  have hd2 : HasDerivAt (fun y : ℝ =>
        ∑ i, (hS.eigenvalues i - 1) * Real.exp ((hS.eigenvalues i - 1) * y)
        - (Fintype.card n : ℝ) * ((-1) * Real.exp ((-1) * y)))
      (∑ i, (hS.eigenvalues i - 1) * ((hS.eigenvalues i - 1)
          * Real.exp ((hS.eigenvalues i - 1) * τ))
        - (Fintype.card n : ℝ) * ((-1) * ((-1) * Real.exp ((-1) * τ)))) τ := by
    have hA : HasDerivAt (fun y : ℝ =>
          ∑ i, (hS.eigenvalues i - 1) * Real.exp ((hS.eigenvalues i - 1) * y))
        (∑ i, (hS.eigenvalues i - 1) * ((hS.eigenvalues i - 1)
          * Real.exp ((hS.eigenvalues i - 1) * τ))) τ :=
      HasDerivAt.fun_sum (fun i _ =>
        (hasDerivAt_exp_lin (hS.eigenvalues i - 1) τ).const_mul (hS.eigenvalues i - 1))
    have hBd : HasDerivAt (fun y : ℝ => (Fintype.card n : ℝ) * ((-1) * Real.exp ((-1) * y)))
        ((Fintype.card n : ℝ) * ((-1) * ((-1) * Real.exp ((-1) * τ)))) τ :=
      ((hasDerivAt_exp_lin (-1) τ).const_mul (-1)).const_mul _
    exact hA.sub hBd
  rw [hf, hderiv1, hd2.deriv, corrSeries_matrix S hS τ, trace_exp_heat S hS τ]
  have e1 : ∀ i, Real.exp ((hS.eigenvalues i - 1) * τ)
      = Real.exp (-(τ * (1 - hS.eigenvalues i))) := fun i => by
    congr 1
    ring
  have e2 : Real.exp ((-1) * τ) = Real.exp (-τ) := by
    congr 1
    ring
  have key : ∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i)))
        * (1 - τ / 2 * (1 - hS.eigenvalues i) ^ 2)
      = ∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i)))
        - τ / 2 * ∑ i, (hS.eigenvalues i - 1) * ((hS.eigenvalues i - 1)
          * Real.exp ((hS.eigenvalues i - 1) * τ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [e1 i]
    ring
  rw [key, e2]
  ring

/-! ### The sampled graph -/

/-- **(2) Deterministic comparison for the sampled graph.** Points `x_0, …, x_{N-1}` on the flat
    torus, kernel of variance `σ`, graph with self-loops, `P` the walk and `S` the symmetric
    matrix, `m_j = p_{jσ}(0)`, `T = ∑_{j≥1} w_j m_j`, `M = p_σ(0)`, `τ ≥ 2`, `J ≥ 1`. If
    `|Tr P^k - m_k| ≤ c √k m_k` for `1 ≤ k ≤ J + 2` (HYPOTHESIS `hgood`: the conclusion of the
    kernel theorem) and `c √(J+2) ≤ 1`, then
    `|corr(Tr S^·) - corr(m)| ≤ (1 + (11/4) τ) c √(J+2) T + (3 + 6τ) M ∑_{j>J} w_j`. -/
theorem corrected_det {σ : ℝ} (hσ : 0 < σ) (d N J : ℕ) (hN : 0 < N) (hJ : 1 ≤ J)
    (x : ℕ → FlatTorus d) {τ c : ℝ} (hτ : 2 ≤ τ) (hc : 0 ≤ c)
    (hc1 : c * Real.sqrt ((J + 2 : ℕ) : ℝ) ≤ 1)
    (hgood : ∀ k, 1 ≤ k → k ≤ J + 2 →
      |((walkMatrix (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ k).trace - heatMode d σ k|
        ≤ c * Real.sqrt k * heatMode d σ k) :
    |corrSeries τ (fun k : ℕ => ((symGraph
            (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
            (fun a : Fin N => heatRho d σ N x a)) ^ k).trace)
        - corrSeries τ (heatMode d σ)|
      ≤ (1 + 11 / 4 * τ) * (c * Real.sqrt ((J + 2 : ℕ) : ℝ)) * poissonMean d σ τ
        + (3 + 6 * τ) * heatTorus d (2 * Real.pi ^ 2 * σ) 0 * ptail τ J := by
  have hpi := Real.pi_pos
  have hτ0 : 0 ≤ τ := by linarith
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Fin N → Fin N → ℝ,
      K = fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j) := ⟨_, rfl⟩
  obtain ⟨rho, hrhodef⟩ : ∃ rho : Fin N → ℝ,
      rho = fun a : Fin N => heatRho d σ N x a := ⟨_, rfl⟩
  rw [← hKdef, ← hrhodef] at hgood ⊢
  obtain ⟨Mp, hMp⟩ : ∃ Mp : ℝ, Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0 := ⟨_, rfl⟩
  rw [← hMp]
  have hKpos : ∀ a j, 0 < K a j := fun a j => by rw [hKdef]; exact heatTorus_pos hcσ d _
  have hKsymm : ∀ a j, K a j = K j a := fun a j => by
    rw [hKdef]
    show heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j)
      = heatTorus d (2 * Real.pi ^ 2 * σ) (x j - x a)
    rw [← heatTorus_even d _ (x j - x a), neg_sub]
  have hrho : ∀ a, 0 < rho a := fun a => by
    rw [hrhodef]
    show 0 < heatRho d σ N x a
    unfold heatRho
    exact div_pos (Finset.sum_pos (fun l _ => heatTorus_pos hcσ d _)
      ⟨0, Finset.mem_range.mpr hN⟩) (by exact_mod_cast hN)
  have hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l) := fun i =>
    Finset.sum_pos (fun l _ => div_pos (hKpos i l) (mul_pos (hrho i) (hrho l)))
      Finset.univ_nonempty
  have hS := symGraph_isHermitian K rho hKsymm
  have hm1 : ∀ j, 1 ≤ j → 1 ≤ heatMode d σ j := fun j hj => heatMode_ge_one hσ d hj
  have hmM : ∀ j, 1 ≤ j → heatMode d σ j ≤ Mp := fun j hj => by
    rw [hMp]; exact heatMode_le hσ d hj
  have hanti : ∀ j, 1 ≤ j → heatMode d σ (j + 1) ≤ heatMode d σ j := by
    intro j hj
    have hj' : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
    have hjσ : 0 < (j : ℝ) * σ := mul_pos hj' hσ
    have hc0 : 0 < 2 * Real.pi ^ 2 * ((j : ℝ) * σ) := by positivity
    unfold heatMode
    refine heatTorus_zero_anti hc0 ?_ d
    have h1 : (j : ℝ) * σ ≤ ((j + 1 : ℕ) : ℝ) * σ := by
      push_cast
      nlinarith [hσ.le]
    have h2 : (0 : ℝ) ≤ 2 * Real.pi ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left h1 h2
  have hlow : ∀ j, 1 ≤ j → j ≤ J + 2 →
      |(symGraph K rho ^ j).trace - heatMode d σ j| ≤ c * Real.sqrt j * heatMode d σ j := by
    intro j hj hjJ
    rw [symGraph_trace_pow K rho hD j]
    exact hgood j hj hjJ
  -- the second moment
  have h2 : (symGraph K rho ^ 2).trace ≤ 2 * Mp := by
    have h := hlow 2 (by omega) (by omega)
    have hsq : c * Real.sqrt ((2 : ℕ) : ℝ) ≤ 1 := by
      have h2J : (((2 : ℕ) : ℝ)) ≤ ((J + 2 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 2 ≤ J + 2)
      exact le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2J) hc) hc1
    have hm0 : 0 ≤ heatMode d σ 2 := le_trans zero_le_one (hm1 2 (by omega))
    have h' := mul_le_mul_of_nonneg_right hsq hm0
    have h'' := (abs_le.mp h).2
    have := hmM 2 (by omega)
    linarith
  have hB : ∀ j, J < j → |(symGraph K rho ^ j).trace| ≤ 2 * Mp := fun j hj =>
    le_trans ((symGraph_trace_bounds K rho hKsymm (fun a j => (hKpos a j).le) hrho hD j).2
      (by omega)) h2
  have hB' : ∀ j, J < j → |heatMode d σ j| ≤ Mp := fun j hj => by
    rw [abs_of_nonneg (le_trans zero_le_one (hm1 j (by omega)))]
    exact hmM j (by omega)
  have hCA : HasSum (corrTerm τ (fun k : ℕ => (symGraph K rho ^ k).trace))
      (corrSeries τ (fun k : ℕ => (symGraph K rho ^ k).trace)) := by
    unfold corrSeries
    exact (corr_matrix_hasSum (symGraph K rho) hS τ).summable.hasSum
  have h := corr_split hτ (fun k : ℕ => (symGraph K rho ^ k).trace) (heatMode d σ) J hc
    (fun j hj => le_trans zero_le_one (hm1 j hj)) hanti (poissonMean_hasSum hσ d hτ0) hCA
    hlow hB hB'
  have e : (1 + 2 * τ) * (2 * Mp + Mp) * ptail τ J = (3 + 6 * τ) * Mp * ptail τ J := by ring
  rw [e] at h
  exact h

/-- **(3) Sample statement: a finite form of the estimate of Corollary "corrected estimator on
    the sampled graph", in series form.** Independent uniform points on the flat torus of
    dimension `d ≥ 1`, periodised Gaussian kernel of variance `σ ≤ 1`, graph with self-loops,
    `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`, `C₁ = kernelC1 d`, an integer `J ≥ 1` with
    `C₁ δ' √(J+2) ≤ 1`. Except on an event of probability at most `3/N³`, for ALL `τ ≥ 2`,
    `|corr(Tr S^·)(τ) - corr(m)(τ)| ≤ (1 + 3τ) C₁ δ' √(J+2) T(τ) + (3 + 6τ) M ∑_{j>J} w_j(τ)`,
    with `T = poissonMean d σ τ`. -/
theorem corrected_G30 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 1 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ) ≤ 1) :
    μ.real {ω | ¬ ∀ τ : ℝ, 2 ≤ τ →
        |corrSeries τ (fun k : ℕ => ((symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace)
            - corrSeries τ (heatMode d σ)|
          ≤ (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ)) * poissonMean d σ τ
            + (3 + 6 * τ) * Mp * ptail τ J}
      ≤ 3 / (N : ℝ) ^ 3 := by
  have h := kernel_trace_G28 hσ hσ1 d hd X h_indep hX hlaw N (J + 2) hN2 (by omega) hMp hδp
    hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro τ hτ
  have hτ0 : 0 ≤ τ := by linarith
  have hc : 0 ≤ kernelC1 d * δp := by
    rw [hδp]; exact mul_nonneg (kernelC1_nonneg d) (Real.sqrt_nonneg _)
  have hdet := corrected_det hσ d N J (by omega) hJ (fun j => X j ω) hτ hc hrange
    (fun k hk hkJ => hgood k hk hkJ)
  rw [← hMp] at hdet
  refine le_trans hdet ?_
  have hT0 : 0 ≤ poissonMean d σ τ := by
    have h1 := poissonMean_ge hσ d hτ0
    have h2 := exp_neg_le_quarter hτ
    linarith
  have hcs0 : 0 ≤ kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ) :=
    mul_nonneg hc (Real.sqrt_nonneg _)
  have h3 : (1 + 11 / 4 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ))
        * poissonMean d σ τ
      ≤ (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ)) * poissonMean d σ τ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hcs0) hT0
  linarith

/-- **(3) with the Poisson tail evaluated.** In the situation of `corrected_G30`: except on an
    event of probability at most `3/N³`, for ALL `τ ≥ 2` with `3τ + 2 log N ≤ J + 1`,
    `|corr(Tr S^·)(τ) - corr(m)(τ)| ≤ (1 + 3τ) C₁ δ' √(J+2) T(τ) + (3 + 6τ) M / N²`. -/
theorem corrected_G30_tail {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N J : ℕ) (hN2 : 2 ≤ N) (hJ : 1 ≤ J)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ) ≤ 1) :
    μ.real {ω | ¬ ∀ τ : ℝ, 2 ≤ τ → 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1 →
        |corrSeries τ (fun k : ℕ => ((symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k).trace)
            - corrSeries τ (heatMode d σ)|
          ≤ (1 + 3 * τ) * (kernelC1 d * δp * Real.sqrt ((J + 2 : ℕ) : ℝ)) * poissonMean d σ τ
            + (3 + 6 * τ) * Mp / (N : ℝ) ^ 2}
      ≤ 3 / (N : ℝ) ^ 3 := by
  have h := corrected_G30 hσ hσ1 d hd X h_indep hX hlaw N J hN2 hJ hMp hδp hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro τ hτ hJτ
  have hpi := Real.pi_pos
  have hτ0 : 0 ≤ τ := by linarith
  have hpt := ptail_le_inv_sq hτ0 J N (by omega) hJτ
  have hMp0 : 0 ≤ Mp := by
    rw [hMp]; exact le_trans zero_le_one (heatTorus_zero_ge_one (by positivity) d)
  have h1 := hgood τ hτ
  have h2 : (3 + 6 * τ) * Mp * ptail τ J ≤ (3 + 6 * τ) * Mp * (1 / (N : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hpt (mul_nonneg (by linarith) hMp0)
  have e : (3 + 6 * τ) * Mp / (N : ℝ) ^ 2 = (3 + 6 * τ) * Mp * (1 / (N : ℝ) ^ 2) := by ring
  rw [e]
  linarith

end Corrected

end CTG.Reals2
