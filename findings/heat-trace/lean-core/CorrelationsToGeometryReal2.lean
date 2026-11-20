import CorrelationsToGeometryReal
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Countable.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
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

/-! ### Delocalisation in the shell parameter (`cor:deloc`, with explicit conditions per shell) -/

namespace DelocalisationFinal

/-! ### Copied block -/

/-- Powers of a matrix on an eigenvector. -/
theorem pow_mulVec_eig {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ) (u : n → ℝ)
    (s : ℝ) (hSu : S *ᵥ u = s • u) (k : ℕ) : (S ^ k) *ᵥ u = s ^ k • u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hSu, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
      mul_comm]

/-- Deterministic step: `u_a² ≤ (S^{2k})_{aa} / s^{2k}`. -/
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

/-- The diagonals of the powers of `S` and of `P` coincide. -/
theorem symGraph_pow_diag {n : Type} [Fintype n] [DecidableEq n] (K : n → n → ℝ) (rho : n → ℝ)
    (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l)) (k : ℕ) (a : n) :
    (symGraph K rho ^ k) a a = (walkMatrix K rho ^ k) a a := by
  have h := conj_pow_entry (symGraph K rho) (walkMatrix K rho)
    (fun i => Real.sqrt (∑ j, K i j / (rho i * rho j)))
    (fun i => Real.sqrt_pos.mpr (hD i)) (fun i l => symGraph_conj K rho hD i l) k
  rw [h a a]
  exact mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (hD a)).ne'

/-- Variant of `deloc_graph` with `s ≠ 0` instead of `0 < s`. -/
theorem deloc_graph' {n : Type} [Fintype n] [DecidableEq n] (K : n → n → ℝ) (rho : n → ℝ)
    (hK : ∀ i j, K i j = K j i) (hD : ∀ i, 0 < ∑ l, K i l / (rho i * rho l))
    {N m D s : ℝ} (hN : 0 < N) (hs : s ≠ 0) (k : ℕ) (a : n)
    (hker : |N * (walkMatrix K rho ^ (2 * k)) a a - m| ≤ D) (hDm : D ≤ m)
    (u : n → ℝ) (hSu : symGraph K rho *ᵥ u = s • u) (hu : ∑ b, u b ^ 2 = 1) :
    u a ^ 2 ≤ 2 * m / (N * s ^ (2 * k)) := by
  have h := deloc_det (symGraph K rho) (symGraph_isHermitian K rho hK) u s hs hSu hu k a
  rw [symGraph_pow_diag K rho hD (2 * k) a] at h
  have hP : (walkMatrix K rho ^ (2 * k)) a a ≤ 2 * m / N := by
    rw [le_div_iff₀ hN]
    have := (abs_le.mp hker).2
    linarith
  have hsk : s ^ k ≠ 0 := pow_ne_zero k hs
  have hsp : 0 < s ^ (2 * k) := by
    rw [pow_mul' s 2 k]
    exact lt_of_le_of_ne (_root_.sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsk))
  calc u a ^ 2 ≤ (walkMatrix K rho ^ (2 * k)) a a / s ^ (2 * k) := h
    _ ≤ (2 * m / N) / s ^ (2 * k) := div_le_div_of_nonneg_right hP hsp.le
    _ = 2 * m / (N * s ^ (2 * k)) := by rw [div_div]

/-! ### (1) The deterministic final step -/

/-- **Final step.** From `u² ≤ 2m/(N s^{2k})` and `s^k ≥ c > 0`: `u² ≤ 2m/(N c²)`. -/
theorem final_step {N m s c u : ℝ} (k : ℕ) (hN : 0 < N) (hm : 0 ≤ m) (hc : 0 < c)
    (hsk : c ≤ s ^ k) (h : u ^ 2 ≤ 2 * m / (N * s ^ (2 * k))) :
    u ^ 2 ≤ 2 * m / (N * c ^ 2) := by
  have e : s ^ (2 * k) = (s ^ k) ^ 2 := pow_mul' s 2 k
  have h2 : c ^ 2 ≤ s ^ (2 * k) := by rw [e]; exact pow_le_pow_left₀ hc.le hsk 2
  refine h.trans ?_
  exact div_le_div_of_nonneg_left (mul_nonneg zero_le_two hm) (mul_pos hN (pow_pos hc 2))
    (mul_le_mul_of_nonneg_left h2 hN.le)

/-- **Final step, absolute value.** From `u² ≤ 2B/(N c²)`: `|u| ≤ √(2B)/(c √N)`. -/
theorem final_step_abs {N B c u : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hc : 0 < c)
    (h : u ^ 2 ≤ 2 * B / (N * c ^ 2)) : |u| ≤ Real.sqrt (2 * B) / (c * Real.sqrt N) := by
  have h0 : 0 ≤ Real.sqrt (2 * B) / (c * Real.sqrt N) :=
    div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hc.le (Real.sqrt_nonneg _))
  have e : (Real.sqrt (2 * B) / (c * Real.sqrt N)) ^ 2 = 2 * B / (N * c ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (mul_nonneg zero_le_two hB), Real.sq_sqrt hN.le,
      mul_comm (c ^ 2) N]
  exact abs_le_of_sq_le_sq (by rw [e]; exact h) h0

/-- The constant: `2m/(N (e^{-1}/2)²) = 8 e² m/N`. -/
theorem const_eq (N m : ℝ) (hN : 0 < N) :
    2 * m / (N * (Real.exp (-1) / 2) ^ 2) = 8 * Real.exp 1 ^ 2 * m / N := by
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hE : Real.exp 1 * (Real.exp 1)⁻¹ = 1 := mul_inv_cancel₀ hE0.ne'
  have h4 : ((Real.exp 1)⁻¹ / 2) ^ 2 * Real.exp 1 ^ 2 = 1 / 4 := by
    calc ((Real.exp 1)⁻¹ / 2) ^ 2 * Real.exp 1 ^ 2
        = (Real.exp 1 * (Real.exp 1)⁻¹) ^ 2 / 4 := by ring
      _ = 1 / 4 := by rw [hE]; norm_num
  rw [Real.exp_neg,
    div_eq_div_iff (mul_pos hN (pow_pos (div_pos (inv_pos.mpr hE0) two_pos) 2)).ne' hN.ne']
  linear_combination (-(8 * m * N)) * h4

/-! ### (2) The lower bound for `s^k` -/

/-- **Lower bound.** If `|s^k - α^k| ≤ err`, `α^k = e^{-x}` with `x ≤ 1` and `err ≤ e^{-1}/2`,
    then `s^k ≥ e^{-1}/2 = 1/(2e)`. -/
theorem pow_lower {s α err x : ℝ} (k : ℕ) (hx : x ≤ 1) (hα : α ^ k = Real.exp (-x))
    (herr : err ≤ Real.exp (-1) / 2) (h : |s ^ k - α ^ k| ≤ err) :
    Real.exp (-1) / 2 ≤ s ^ k := by
  have h1 := (abs_le.mp h).1
  have h2 : Real.exp (-1) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  rw [hα] at h1
  linarith

/-! ### Auxiliary bounds -/

theorem eigC3_nonneg (d : ℕ) : 0 ≤ eigC3 d := by
  unfold eigC3
  have h1 := TraceG29.kernelC1_nonneg d
  have h2 : 0 ≤ (6 * (6 * Real.sqrt (3 * (d : ℝ) + 5)) + 2
      + Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) * (1 + 2 * Real.sqrt 2 ^ d))
    * ((1 + Real.sqrt (2 * Real.pi)) ^ d) ^ 2 := by positivity
  linarith

/-- `((1 + √(2π r))^d)² ≤ (4π(1 + r))^d`. -/
theorem shell_sq_le {r : ℝ} (hr : 0 ≤ r) (d : ℕ) :
    ((1 + Real.sqrt (2 * Real.pi * r)) ^ d) ^ 2 ≤ (4 * Real.pi * (1 + r)) ^ d := by
  have hpi := Real.two_le_pi
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi * r by positivity)
  have hs0 := Real.sqrt_nonneg (2 * Real.pi * r)
  have hb : (1 + Real.sqrt (2 * Real.pi * r)) ^ 2 ≤ 4 * Real.pi * (1 + r) := by
    nlinarith [_root_.sq_nonneg (1 - Real.sqrt (2 * Real.pi * r))]
  calc ((1 + Real.sqrt (2 * Real.pi * r)) ^ d) ^ 2
      = ((1 + Real.sqrt (2 * Real.pi * r)) ^ 2) ^ d := pow_right_comm _ d 2
    _ ≤ (4 * Real.pi * (1 + r)) ^ d := pow_le_pow_left₀ (_root_.sq_nonneg _) hb d

/-- From a bound for the fourth power to a bound for the absolute value, with real exponents. -/
theorem fourth_root_bound {u C A N : ℝ} (d : ℕ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hN : 0 < N)
    (h : u ^ 4 ≤ C * A ^ d / N ^ 2) :
    |u| ≤ C ^ (1 / 4 : ℝ) * A ^ ((d : ℝ) / 4) / Real.sqrt N := by
  have c1 : (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 := by norm_num
  have c2 : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = (d : ℝ) := by push_cast; ring
  have e1 : (C ^ (1 / 4 : ℝ)) ^ 4 = C := by
    rw [← Real.rpow_mul_natCast hC, c1, Real.rpow_one]
  have e2 : (A ^ ((d : ℝ) / 4)) ^ 4 = A ^ d := by
    rw [← Real.rpow_mul_natCast hA, c2, Real.rpow_natCast]
  have e3 : Real.sqrt N ^ 4 = N ^ 2 := by
    calc Real.sqrt N ^ 4 = (Real.sqrt N ^ 2) ^ 2 := by ring
      _ = N ^ 2 := by rw [Real.sq_sqrt hN.le]
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = C ^ (1 / 4 : ℝ) * A ^ ((d : ℝ) / 4) / Real.sqrt N := ⟨_, rfl⟩
  rw [← hR]
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hC _) (Real.rpow_nonneg hA _))
      (Real.sqrt_nonneg _)
  have e4 : R ^ 4 = C * A ^ d / N ^ 2 := by
    rw [hR, div_pow, mul_pow, e1, e2, e3]
  have h4 : (u ^ 2) ^ 2 ≤ (R ^ 2) ^ 2 := by
    calc (u ^ 2) ^ 2 = u ^ 4 := by ring
      _ ≤ C * A ^ d / N ^ 2 := h
      _ = R ^ 4 := e4.symm
      _ = (R ^ 2) ^ 2 := by ring
  have h2 := abs_le_of_sq_le_sq h4 (_root_.sq_nonneg R)
  rw [abs_of_nonneg (_root_.sq_nonneg u)] at h2
  exact abs_le_of_sq_le_sq h2 hR0

/-! ### (3) The sample theorems -/

set_option maxHeartbeats 3200000 in
/-- **Delocalisation, sample form with a free number of steps.** Hypotheses of
    `kernel_theorem_G28` and `eig_theorem_G38_i`. Except on the union of their two exceptional
    sets (probability at most `3/N³ + 6/N³ = 9/N³`): for every `k ≥ 1` with `2k ≤ K`, every shell
    `r > 0` and every index `j` of the shell (counted from zero, as in `eig_theorem_G38_i`) with
    `k · 2π²σ r ≤ 1` and `C₃ δ' √k m_k ≤ e^{-1}/2`, every vector `u` with
    `S u = s_j u` (`s_j = hS.eigenvalues₀ j`) and `∑ u² = 1` satisfies
    `u_a² ≤ 8 e² m_{2k} / N` for all `a`. -/
theorem deloc_sample_k {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N] (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → 2 * k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))) (r : ℝ), 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            (k : ℝ) * (2 * Real.pi ^ 2 * σ * r) ≤ 1 →
            eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0
              ≤ Real.exp (-1) / 2 →
            ∀ (u : Fin N → ℝ) (a : Fin N),
              symGraph
                (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
                (fun i : Fin N =>
                  (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) *ᵥ u
                = hS.eigenvalues₀ j • u →
              ∑ b, u b ^ 2 = 1 →
              u a ^ 2 ≤ 8 * Real.exp 1 ^ 2
                * heatTorus d (2 * Real.pi ^ 2 * (((2 * k : ℕ) : ℝ) * σ)) 0 / N}
      ≤ 9 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  obtain ⟨Bk, hBkd⟩ : ∃ Bk : Set Ω, Bk = {ω | ¬ ∀ k, 1 ≤ k → k ≤ K → ∀ a i : Fin N,
      |(N : ℝ) * ((walkMatrix
            (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
            (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
          - heatP d σ k (X a ω - X i ω)|
        ≤ kernelC1 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0} :=
    ⟨_, rfl⟩
  have hBk : μ.real Bk ≤ 3 / (N : ℝ) ^ 3 := by
    rw [hBkd]
    exact kernel_theorem_G28 hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  obtain ⟨Bi, hBid⟩ : ∃ Bi : Set Ω, Bi = {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → hS.eigenvalues₀ j = 1)
          ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ eigC3 d * δp * Real.sqrt k
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0} := ⟨_, rfl⟩
  have hBi : μ.real Bi ≤ 6 / (N : ℝ) ^ 3 := by
    rw [hBid]
    exact eig_theorem_G38_i hσ hσ1 d N K hd X h_indep hX hlaw hN2 hK hMp hδp hrange
  refine le_trans (measureReal_mono (s₂ := Bk ∪ Bi) ?_ (measure_ne_top μ _)) ?_
  swap
  · have hun := measureReal_union_le (μ := μ) Bk Bi
    have e : 3 / (N : ℝ) ^ 3 + 6 / (N : ℝ) ^ 3 = 9 / (N : ℝ) ^ 3 := by ring
    linarith
  intro ω hω
  by_contra hcon
  simp only [Set.mem_union, not_or] at hcon
  obtain ⟨hk, hi⟩ := hcon
  rw [hBkd] at hk
  rw [hBid] at hi
  have hkern := not_not.mp hk
  have heig := not_not.mp hi
  apply hω
  intro k hk1 hkK hS j r hr Hlt Hle hlt hle h1 h2 hx hsmall u a hSu hu
  -- the lower bound for the power of the eigenvalue
  have hpw := (heig k hk1 (by omega) hS j).2 r hr Hlt Hle hlt hle h1 h2
  have e : Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k
      = Real.exp (-((k : ℝ) * (2 * Real.pi ^ 2 * σ * r))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hlow : Real.exp (-1) / 2 ≤ hS.eigenvalues₀ j ^ k := pow_lower k hx e hsmall hpw
  have hc0 : 0 < Real.exp (-1) / 2 := by positivity
  have hs : hS.eigenvalues₀ j ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : k ≠ 0)] at hlow
    linarith
  -- the two forms of the normalisation coincide
  have hrho : (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)
      = (fun i : Fin N =>
          (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) := by
    funext b
    simp only [heatRho]
    rw [Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (X b ω - X l ω)) N]
  have h1k := hkern (2 * k) (by omega) hkK a a
  rw [hrho, sub_self, heatP_of_ne d σ (by omega)] at h1k
  have hc : 0 ≤ kernelC1 d * δp := by
    rw [hδp]; exact mul_nonneg (TraceG29.kernelC1_nonneg d) (Real.sqrt_nonneg _)
  have hcast : (((2 * k : ℕ) : ℝ)) ≤ (K : ℝ) := by exact_mod_cast hkK
  have hc1 : kernelC1 d * δp * Real.sqrt ((2 * k : ℕ) : ℝ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcast) hc) hrange
  have hm0 : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * (((2 * k : ℕ) : ℝ) * σ)) 0 :=
    (heatTorus_pos (by
      have : (0 : ℝ) < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * k)
      positivity) d 0).le
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hKsymm : ∀ a j : Fin N,
      heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω)
        = heatTorus d (2 * Real.pi ^ 2 * σ) (X j ω - X a ω) := fun a j => by
    rw [← heatTorus_even d _ (X j ω - X a ω), neg_sub]
  have hrhopos : ∀ i : Fin N,
      0 < (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N := fun i =>
    div_pos (Finset.sum_pos (fun l _ => heatTorus_pos hcσ d _) Finset.univ_nonempty) hNpos
  have hD : ∀ i : Fin N, 0 < ∑ l : Fin N,
      heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)
        / ((∑ l' : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l' ω)) / N
          * ((∑ l' : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X l ω - X l' ω)) / N)) := fun i =>
    Finset.sum_pos (fun l _ => div_pos (heatTorus_pos hcσ d _) (mul_pos (hrhopos i) (hrhopos l)))
      Finset.univ_nonempty
  have hg := deloc_graph'
    (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
    (fun i : Fin N => (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)
    hKsymm hD hNpos hs k a h1k (mul_le_of_le_one_left hm0 hc1) u hSu hu
  have hf := final_step k hNpos hm0 hc0 hlow hg
  rw [const_eq _ _ hNpos] at hf
  exact hf

set_option maxHeartbeats 3200000 in
/-- **Delocalisation of the eigenvectors, sample form in the shell parameter (a form of
    `cor:deloc`).** Hypotheses of `kernel_theorem_G28` and `eig_theorem_G38_i`. Except on the
    union of their two exceptional sets (probability at most `9/N³`): for every shell `r > 0`
    (`λ = 4π² r`) with `2π²σ r ≤ 1/2`, `1 ≤ K π²σ r` and
    `2 e C₃ δ' (1 + √(2π r))^d ≤ √(2π²σ r)`, every index `j` of the shell (counted from zero) and
    every vector `u` with `S u = s_j u` (`s_j = hS.eigenvalues₀ j`), `∑ u² = 1`, for all `a`:
    `u_a² ≤ 8 e² (1 + √(2π r))^d / N`, `u_a⁴ ≤ 64 e⁴ (4π(1+r))^d / N²` and
    `|u_a| ≤ (64 e⁴)^{1/4} (4π(1+r))^{d/4} / √N`. -/
theorem deloc_sample_shell {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N] (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))) (r : ℝ), 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            2 * Real.pi ^ 2 * σ * r ≤ 1 / 2 →
            1 ≤ (K : ℝ) * (Real.pi ^ 2 * σ * r) →
            2 * Real.exp 1 * (eigC3 d * δp) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d
              ≤ Real.sqrt (2 * Real.pi ^ 2 * σ * r) →
            ∀ (u : Fin N → ℝ) (a : Fin N),
              symGraph
                (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
                (fun i : Fin N =>
                  (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) *ᵥ u
                = hS.eigenvalues₀ j • u →
              ∑ b, u b ^ 2 = 1 →
              u a ^ 2 ≤ 8 * Real.exp 1 ^ 2 * (1 + Real.sqrt (2 * Real.pi * r)) ^ d / N
              ∧ u a ^ 4 ≤ 64 * Real.exp 1 ^ 4 * (4 * Real.pi * (1 + r)) ^ d / (N : ℝ) ^ 2
              ∧ |u a| ≤ (64 * Real.exp 1 ^ 4) ^ (1 / 4 : ℝ)
                  * (4 * Real.pi * (1 + r)) ^ ((d : ℝ) / 4) / Real.sqrt N}
      ≤ 9 / (N : ℝ) ^ 3 := by
  have h := deloc_sample_k hσ hσ1 d N K hd X h_indep hX hlaw hN2 hK hMp hδp hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro hS j r hr Hlt Hle hlt hle h1 h2 hx hK' hsm u a hSu hu
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < 2 * Real.pi ^ 2 * σ * r := by positivity
  have hy : 0 < Real.pi ^ 2 * σ * r := by positivity
  obtain ⟨k, hk2, hlo, hhi⟩ := exists_step hx0 hx
  have hkr : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkx0 : 0 ≤ (k : ℝ) * (2 * Real.pi ^ 2 * σ * r) := mul_nonneg hkr hx0.le
  have h2kK : 2 * k ≤ K := by
    have h3 : ((2 * k : ℕ) : ℝ) ≤ K := by
      push_cast
      by_contra hc
      rw [not_le] at hc
      have h4 := mul_lt_mul_of_pos_right hc hy
      nlinarith [h4, hhi, hK']
    exact_mod_cast h3
  -- the heat kernel at the origin at the chosen steps
  have hmk : heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0
      ≤ (1 + Real.sqrt (2 * Real.pi * r)) ^ d := by
    have h5 := heatP_le_mu hσ d k (0 : FlatTorus d)
    rw [heatP_of_ne d σ (by omega)] at h5
    exact h5.trans (heatMu_le_shell hσ hr d k (by omega) (by linarith [hlo]))
  have hm2k : heatTorus d (2 * Real.pi ^ 2 * (((2 * k : ℕ) : ℝ) * σ)) 0
      ≤ (1 + Real.sqrt (2 * Real.pi * r)) ^ d := by
    have h5 := heatP_le_mu hσ d (2 * k) (0 : FlatTorus d)
    rw [heatP_of_ne d σ (by omega)] at h5
    exact h5.trans (heatMu_le_shell hσ hr d (2 * k) (by omega)
      (by push_cast; nlinarith [hlo, hkx0]))
  -- the smallness condition at the chosen step
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hE0 : 0 ≤ eigC3 d * δp := mul_nonneg (eigC3_nonneg d) hδp0
  have hsk0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hsk : Real.sqrt (k : ℝ) * Real.sqrt (2 * Real.pi ^ 2 * σ * r) ≤ 1 := by
    rw [← Real.sqrt_mul hkr]
    calc Real.sqrt ((k : ℝ) * (2 * Real.pi ^ 2 * σ * r)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hhi
      _ = 1 := Real.sqrt_one
  have hee : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  have he2 : 0 ≤ Real.exp (-1) / 2 := by positivity
  have h5 := mul_le_mul_of_nonneg_left hsm he2
  have h6 : Real.exp (-1) / 2
        * (2 * Real.exp 1 * (eigC3 d * δp) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d)
      = (Real.exp (-1) * Real.exp 1)
        * ((eigC3 d * δp) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d) := by ring
  rw [h6, hee, one_mul] at h5
  have hsmall : eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0
      ≤ Real.exp (-1) / 2 := by
    calc eigC3 d * δp * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0
        ≤ eigC3 d * δp * Real.sqrt k * (1 + Real.sqrt (2 * Real.pi * r)) ^ d :=
          mul_le_mul_of_nonneg_left hmk (mul_nonneg hE0 hsk0)
      _ = Real.sqrt k * ((eigC3 d * δp) * (1 + Real.sqrt (2 * Real.pi * r)) ^ d) := by ring
      _ ≤ Real.sqrt k * (Real.exp (-1) / 2 * Real.sqrt (2 * Real.pi ^ 2 * σ * r)) :=
          mul_le_mul_of_nonneg_left h5 hsk0
      _ = (Real.sqrt k * Real.sqrt (2 * Real.pi ^ 2 * σ * r)) * (Real.exp (-1) / 2) := by ring
      _ ≤ 1 * (Real.exp (-1) / 2) := mul_le_mul_of_nonneg_right hsk he2
      _ = Real.exp (-1) / 2 := one_mul _
  have hA := hgood k (by omega) h2kK hS j r hr Hlt Hle hlt hle h1 h2 hhi hsmall u a hSu hu
  have hB0 : 0 ≤ (1 + Real.sqrt (2 * Real.pi * r)) ^ d := by positivity
  have hsq : u a ^ 2 ≤ 8 * Real.exp 1 ^ 2 * (1 + Real.sqrt (2 * Real.pi * r)) ^ d / N :=
    hA.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm2k (by positivity)) hNpos.le)
  have h4 : u a ^ 4 ≤ 64 * Real.exp 1 ^ 4 * (4 * Real.pi * (1 + r)) ^ d / (N : ℝ) ^ 2 := by
    calc u a ^ 4 = (u a ^ 2) ^ 2 := by ring
      _ ≤ (8 * Real.exp 1 ^ 2 * (1 + Real.sqrt (2 * Real.pi * r)) ^ d / N) ^ 2 :=
          pow_le_pow_left₀ (_root_.sq_nonneg _) hsq 2
      _ = 64 * Real.exp 1 ^ 4 * ((1 + Real.sqrt (2 * Real.pi * r)) ^ d) ^ 2 / (N : ℝ) ^ 2 := by
          ring
      _ ≤ 64 * Real.exp 1 ^ 4 * (4 * Real.pi * (1 + r)) ^ d / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (shell_sq_le hr.le d) (by positivity)) (by positivity)
  exact ⟨hsq, h4, fourth_root_bound d (by positivity) (by positivity) hNpos h4⟩

end DelocalisationFinal

/-! ### Enumeration of the lattice by non-decreasing norm; part (i) of the eigenvalue theorem for all indices -/

namespace LatticeEnumeration

/-- `|n|²` as a natural number. -/
def nsq {d : ℕ} (n : Fin d → ℤ) : ℕ := ∑ i, (n i).natAbs ^ 2

theorem nsq_cast {d : ℕ} (n : Fin d → ℤ) :
    ((nsq n : ℕ) : ℝ) = ∑ i, ((n i : ℤ) : ℝ) ^ 2 := by
  unfold nsq
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (((n i).natAbs : ℤ)) ^ 2 = (n i) ^ 2 := by
    rw [Int.natCast_natAbs, sq_abs]
  calc (((n i).natAbs ^ 2 : ℕ) : ℝ) = ((((n i).natAbs : ℤ) ^ 2 : ℤ) : ℝ) := by
        rw [Int.cast_pow, Int.cast_natCast, Nat.cast_pow]
    _ = (((n i) ^ 2 : ℤ) : ℝ) := by rw [h]
    _ = ((n i : ℤ) : ℝ) ^ 2 := by rw [Int.cast_pow]

theorem natAbs_le_nsq {d : ℕ} (n : Fin d → ℤ) (i : Fin d) : (n i).natAbs ≤ nsq n := by
  have h1 : (n i).natAbs ^ 2 ≤ nsq n := by
    unfold nsq
    exact Finset.single_le_sum (f := fun j => (n j).natAbs ^ 2) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : (n i).natAbs ≤ (n i).natAbs ^ 2 := Nat.le_self_pow (n := 2) (by decide) _
  exact h2.trans h1

theorem nsq_zero {d : ℕ} : nsq (0 : Fin d → ℤ) = 0 := by
  unfold nsq
  exact Finset.sum_eq_zero fun i _ => by simp

theorem nsq_eq_zero {d : ℕ} {n : Fin d → ℤ} (h : nsq n = 0) : n = 0 := by
  funext i
  have h3 := natAbs_le_nsq n i
  have h4 : (n i).natAbs = 0 := by omega
  exact Int.natAbs_eq_zero.mp h4

/-- The finite set of lattice points with `|n|² < q`. -/
noncomputable def ball (d q : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(q : ℤ)) q).filter fun n => nsq n < q

theorem mem_ball {d q : ℕ} (n : Fin d → ℤ) : n ∈ ball d q ↔ nsq n < q := by
  unfold ball
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Fintype.mem_piFinset]
  intro i
  have h3 : (n i).natAbs < q := lt_of_le_of_lt (natAbs_le_nsq n i) h
  rw [Finset.mem_Icc]
  omega

/-- An auxiliary code: strictly increasing in `|n|²`, and injective if `f` is. -/
noncomputable def code {d : ℕ} (f : (Fin d → ℤ) → ℕ) (n : Fin d → ℤ) : ℕ :=
  (∑ m ∈ ball d (nsq n), (f m + 1)) + f n

theorem code_lt {d : ℕ} (f : (Fin d → ℤ) → ℕ) {n n' : Fin d → ℤ} (h : nsq n < nsq n') :
    code f n < code f n' := by
  have hsub : insert n (ball d (nsq n)) ⊆ ball d (nsq n') := by
    intro m hm
    rw [Finset.mem_insert] at hm
    rw [mem_ball]
    rcases hm with hm | hm
    · rw [hm]; exact h
    · rw [mem_ball] at hm; omega
  have hnot : n ∉ ball d (nsq n) := by
    rw [mem_ball]; omega
  have h1 := Finset.sum_le_sum_of_subset (f := fun m => f m + 1) hsub
  rw [Finset.sum_insert hnot] at h1
  have h1' : f n + 1 + ∑ m ∈ ball d (nsq n), (f m + 1) ≤ ∑ m ∈ ball d (nsq n'), (f m + 1) := h1
  unfold code
  omega

theorem code_injective {d : ℕ} {f : (Fin d → ℤ) → ℕ} (hf : Function.Injective f) :
    Function.Injective (code f) := by
  intro n n' h
  rcases Nat.lt_trichotomy (nsq n) (nsq n') with hlt | hq | hgt
  · have := code_lt f hlt
    omega
  · apply hf
    unfold code at h
    rw [hq] at h
    omega
  · have := code_lt f hgt
    omega

/-- **Existence of the enumeration (natural-number form).** For `d ≥ 1` there is a bijection
    `e : ℕ → ℤ^d` along which `|n|²` is non-decreasing. -/
theorem exists_enum {d : ℕ} (hd : 1 ≤ d) :
    ∃ e : ℕ → (Fin d → ℤ), Function.Bijective e ∧ ∀ i j, i ≤ j → nsq (e i) ≤ nsq (e j) := by
  obtain ⟨f, hf⟩ := exists_injective_nat (Fin d → ℤ)
  haveI hinf : Infinite (Fin d → ℤ) :=
    Infinite.of_injective (fun (z : ℤ) (_ : Fin d) => z) (fun a b h => congrFun h ⟨0, hd⟩)
  have hcinj : Function.Injective (code f) := code_injective hf
  have hsinf : (Set.range (code f)).Infinite := Set.infinite_range_of_injective hcinj
  haveI : Infinite (Set.range (code f)) := hsinf.to_subtype
  obtain ⟨φ, _⟩ : ∃ φ : ℕ ≃o Set.range (code f), True :=
    ⟨Nat.Subtype.orderIsoOfNat (Set.range (code f)), trivial⟩
  have hex : ∀ j, ∃ a, code f a = ((φ j : Set.range (code f)) : ℕ) := fun j => (φ j).2
  choose e he using hex
  refine ⟨e, ⟨?_, ?_⟩, ?_⟩
  · intro i j hij
    have h1 : ((φ i : Set.range (code f)) : ℕ) = ((φ j : Set.range (code f)) : ℕ) := by
      rw [← he i, ← he j, hij]
    exact φ.injective (Subtype.ext h1)
  · intro a
    refine ⟨φ.symm ⟨code f a, a, rfl⟩, hcinj ?_⟩
    rw [he, OrderIso.apply_symm_apply]
  · intro i j hij
    by_contra hlt
    have h1 : code f (e j) < code f (e i) := code_lt f (not_le.mp hlt)
    have h2 : φ i ≤ φ j := φ.monotone hij
    have h3 : ((φ i : Set.range (code f)) : ℕ) ≤ ((φ j : Set.range (code f)) : ℕ) := h2
    have e1 := he i
    have e2 := he j
    omega

/-- **Existence of the enumeration (form used by `shell_position`).** -/
theorem exists_enum_real {d : ℕ} (hd : 1 ≤ d) :
    ∃ e : ℕ → (Fin d → ℤ), Function.Bijective e ∧
      ∀ i j, i ≤ j → ∑ t, ((e i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2 := by
  obtain ⟨e, he, hmono⟩ := exists_enum hd
  refine ⟨e, he, fun i j hij => ?_⟩
  rw [← nsq_cast, ← nsq_cast]
  exact_mod_cast hmono i j hij

/-! ## Consequences for any such enumeration -/

/-- The enumeration starts at the origin. -/
theorem enum_zero {d : ℕ} (e : ℕ → (Fin d → ℤ)) (he : Function.Bijective e)
    (hmono : ∀ i j, i ≤ j → ∑ t, ((e i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2) :
    e 0 = 0 := by
  obtain ⟨j0, hj0⟩ := he.2 0
  have h := hmono 0 j0 (Nat.zero_le _)
  rw [← nsq_cast, ← nsq_cast, hj0, nsq_zero] at h
  have h' : nsq (e 0) ≤ 0 := by exact_mod_cast h
  exact nsq_eq_zero (by omega)

/-- For `j ≥ 1` the value `|e_j|²` is at least `1`. -/
theorem enum_pos {d : ℕ} (e : ℕ → (Fin d → ℤ)) (he : Function.Bijective e)
    (hmono : ∀ i j, i ≤ j → ∑ t, ((e i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2)
    {j : ℕ} (hj : 1 ≤ j) : 1 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2 := by
  have h0 := enum_zero e he hmono
  have hne : e j ≠ 0 := by
    intro h
    have : j = 0 := he.1 (h.trans h0.symm)
    omega
  have h1 : 1 ≤ nsq (e j) := by
    by_contra hc
    exact hne (nsq_eq_zero (by omega))
  rw [← nsq_cast]
  exact_mod_cast h1

/-- The Finsets of lexicographically positive frequencies below a natural level exist. -/
theorem shell_sets (d q : ℕ) : ∃ Hlt Hle : Finset (Fin d → ℤ),
    (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < (q : ℝ)) ∧
    (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ (q : ℝ)) := by
  classical
  refine ⟨(ball d q).filter (lexPos d), (ball d (q + 1)).filter (lexPos d),
    fun n => ?_, fun n => ?_⟩
  · rw [Finset.mem_filter, mem_ball, ← nsq_cast n, Nat.cast_lt]
    exact and_comm
  · rw [Finset.mem_filter, mem_ball, ← nsq_cast n, Nat.cast_le, Nat.lt_succ_iff]
    exact and_comm

/-- **The shell condition along the enumeration.** For `j ≥ 1` and `r = |e_j|²`, the Finsets
    `Hlt`, `Hle` of the eigenvalue theorems exist, and for ANY Finsets with these membership
    characterisations the index condition `1 + 2 #Hlt ≤ j ≤ 2 #Hle` holds. -/
theorem enum_shell {d : ℕ} (e : ℕ → (Fin d → ℤ)) (he : Function.Bijective e)
    (hmono : ∀ i j, i ≤ j → ∑ t, ((e i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2)
    {j : ℕ} (hj : 1 ≤ j) :
    (∃ Hlt Hle : Finset (Fin d → ℤ),
      (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < ∑ t, ((e j t : ℤ) : ℝ) ^ 2) ∧
      (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2)) ∧
    ∀ Hlt Hle : Finset (Fin d → ℤ),
      (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < ∑ t, ((e j t : ℤ) : ℝ) ^ 2) →
      (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2) →
      1 + 2 * Hlt.card ≤ j ∧ j ≤ 2 * Hle.card := by
  have hpos : (0 : ℝ) < ∑ t, ((e j t : ℤ) : ℝ) ^ 2 :=
    lt_of_lt_of_le one_pos (enum_pos e he hmono hj)
  refine ⟨?_, fun Hlt Hle hlt hle =>
    (ShellAndWalk.shell_position e he hmono hpos hlt hle j).mpr rfl⟩
  obtain ⟨Hlt, Hle, hlt, hle⟩ := shell_sets d (nsq (e j))
  rw [nsq_cast] at hlt hle
  exact ⟨Hlt, Hle, hlt, hle⟩

/-- **The sequence of values does not depend on the enumeration.** Any two bijections
    `ℕ → ℤ^d` along which `|n|²` is non-decreasing take the same value of `|n|²` at every
    position. -/
theorem enum_value_unique {d : ℕ} (e e' : ℕ → (Fin d → ℤ))
    (he : Function.Bijective e) (he' : Function.Bijective e')
    (hmono : ∀ i j, i ≤ j → ∑ t, ((e i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2)
    (hmono' : ∀ i j, i ≤ j → ∑ t, ((e' i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e' j t : ℤ) : ℝ) ^ 2)
    (j : ℕ) : ∑ t, ((e' j t : ℤ) : ℝ) ^ 2 = ∑ t, ((e j t : ℤ) : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · rw [hj, enum_zero e he hmono, enum_zero e' he' hmono']
  · have hpos : (0 : ℝ) < ∑ t, ((e j t : ℤ) : ℝ) ^ 2 :=
      lt_of_lt_of_le one_pos (enum_pos e he hmono hj)
    obtain ⟨⟨Hlt, Hle, hlt, hle⟩, hall⟩ := enum_shell e he hmono hj
    exact (ShellAndWalk.shell_position e' he' hmono' hpos hlt hle j).mp (hall Hlt Hle hlt hle)

/-! ## The sample statement -/

theorem eigC3_nonneg (d : ℕ) : 0 ≤ eigC3 d := by
  unfold eigC3
  exact add_nonneg (TraceG29.kernelC1_nonneg d) (by positivity)

/-- **Part (i) of the eigenvalue theorem with the comparison value indexed by an enumeration
    of the lattice.** Hypotheses of `eig_theorem_G38_i`; `e` is ANY bijection `ℕ → ℤ^d` along
    which `|n|²` is non-decreasing (one exists by `exists_enum_real`). Except on an event of
    probability at most `6/N³` (the set is contained in that of `eig_theorem_G38_i`), for all
    `1 ≤ k ≤ K` and ALL indices `j` (counted from zero):
    `|s_j^k - exp(-2π²σ |e_j|²)^k| ≤ C₃ δ' √k m_k`.

    That `4π²|n|²` are the eigenvalues of `-Δ` on the flat unit torus is NOT part of this
    statement and is not formalised. -/
theorem eig_theorem_G38_i_enum {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N] (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1)
    (e : ℕ → (Fin d → ℤ)) (he : Function.Bijective e)
    (hmono : ∀ i j, i ≤ j → ∑ t, ((e i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          |hS.eigenvalues₀ j ^ k
              - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ t, ((e j.val t : ℤ) : ℝ) ^ 2) ^ k|
            ≤ eigC3 d * δp * Real.sqrt k
              * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ≤ 6 / (N : ℝ) ^ 3 := by
  have h := eig_theorem_G38_i hσ hσ1 d N K hd X h_indep hX hlaw hN2 hK hMp hδp hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) h
  intro ω hω hgood
  apply hω
  intro k hk hkK hS j
  obtain ⟨h0, hr⟩ := hgood k hk hkK hS j
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · have hz : ∑ t, ((e j.val t : ℤ) : ℝ) ^ 2 = 0 := by
      rw [hj0, enum_zero e he hmono]
      simp
    rw [hz, h0 hj0, mul_zero, Real.exp_zero, sub_self, abs_zero]
    have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hc : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) :=
      mul_pos (mul_pos two_pos (pow_pos Real.pi_pos 2)) (mul_pos hkpos hσ)
    exact mul_nonneg (mul_nonneg (mul_nonneg (eigC3_nonneg d) hδp0) (Real.sqrt_nonneg _))
      (heatTorus_nonneg hc d 0)
  · have hpos : (0 : ℝ) < ∑ t, ((e j.val t : ℤ) : ℝ) ^ 2 :=
      lt_of_lt_of_le one_pos (enum_pos e he hmono hjpos)
    obtain ⟨⟨Hlt, Hle, hlt, hle⟩, hall⟩ := enum_shell e he hmono hjpos
    obtain ⟨h1, h2⟩ := hall Hlt Hle hlt hle
    exact hr _ hpos Hlt Hle hlt hle h1 h2

/-- **Non-vacuous form.** For `d ≥ 1` there IS an enumeration `e` of `ℤ^d` (bijective, `|n|²`
    non-decreasing, `e 0 = 0`) for which the sample statement holds; by `enum_value_unique` the
    comparison values `|e_j|²` are the same for every such enumeration. -/
theorem eig_theorem_G38_i_enum_exists {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d N K : ℕ) [NeZero N] (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    ∃ e : ℕ → (Fin d → ℤ), Function.Bijective e ∧
      (∀ i j, i ≤ j → ∑ t, ((e i t : ℤ) : ℝ) ^ 2 ≤ ∑ t, ((e j t : ℤ) : ℝ) ^ 2) ∧
      e 0 = 0 ∧
      μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          |hS.eigenvalues₀ j ^ k
              - Real.exp (-(2 * Real.pi ^ 2 * σ) * ∑ t, ((e j.val t : ℤ) : ℝ) ^ 2) ^ k|
            ≤ eigC3 d * δp * Real.sqrt k
              * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ≤ 6 / (N : ℝ) ^ 3 := by
  obtain ⟨e, he, hmono⟩ := exists_enum_real hd
  exact ⟨e, he, hmono, enum_zero e he hmono,
    eig_theorem_G38_i_enum hσ hσ1 d N K hd X h_indep hX hlaw hN2 hK hMp hδp hrange e he hmono⟩

end LatticeEnumeration

/-! ### Deterministic steps of `cor:eigspace`: spectral step, Schur test, approximate eigenvectors -/

namespace EigenspaceSteps

/-- The `i`-th eigenvector of the orthonormal eigenbasis of Mathlib, as a function `n → ℝ`. -/
noncomputable def evec {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (i : n) : n → ℝ := ⇑(hA.eigenvectorBasis i)

theorem mulVec_evec {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (i : n) : A *ᵥ evec hA i = hA.eigenvalues i • evec hA i :=
  hA.mulVec_eigenvectorBasis i

theorem unitary_apply {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (a i : n) :
    (hA.eigenvectorUnitary : Matrix n n ℝ) a i = evec hA i a := rfl

/-- The coordinate `v_i · x` is the `i`-th entry of `Uᵀ x`. -/
theorem coord_eq {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (x : n → ℝ) (i : n) :
    evec hA i ⬝ᵥ x = ((star (hA.eigenvectorUnitary : Matrix n n ℝ)) *ᵥ x) i := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  simp only [mulVec, dotProduct, transpose_apply, unitary_apply]

/-- Parseval in the eigenbasis: `x · x = ∑_i (v_i · x)^2`. -/
theorem parseval {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (x : n → ℝ) : x ⬝ᵥ x = ∑ i, (evec hA i ⬝ᵥ x) ^ 2 := by
  rw [(quad_form_eig A hA x).2]
  exact Finset.sum_congr rfl (fun i _ => by rw [coord_eq A hA x i])

/-- The eigenvectors are orthonormal for the dot product. -/
theorem evec_orthonormal {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (i j : n) : evec hA i ⬝ᵥ evec hA j = if i = j then 1 else 0 := by
  have h1 : star (hA.eigenvectorUnitary : Matrix n n ℝ) * (hA.eigenvectorUnitary : Matrix n n ℝ)
      = 1 := Unitary.coe_star_mul_self _
  have h2 := congrFun (congrFun h1 i) j
  rw [Matrix.one_apply] at h2
  rw [← h2, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  simp only [Matrix.mul_apply, dotProduct, transpose_apply, unitary_apply]

/-- Every eigenvector of `S` is an eigenvector of `S^k` for the `k`-th power of the eigenvalue. -/
theorem pow_mulVec_evec {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (k : ℕ) (i : n) :
    (S ^ k) *ᵥ evec hS i = hS.eigenvalues i ^ k • evec hS i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ S k, ← mulVec_mulVec, mulVec_evec S hS i, mulVec_smul, ih, smul_smul,
      ← pow_succ']

/-- The coordinates of `S^k w` in the eigenbasis of `S`. -/
theorem coord_pow {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (k : ℕ) (w : n → ℝ) (i : n) :
    evec hS i ⬝ᵥ ((S ^ k) *ᵥ w) = hS.eigenvalues i ^ k * (evec hS i ⬝ᵥ w) := by
  have hT : (S ^ k)ᵀ = S ^ k := by
    have h := (hS.pow k).eq
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  rw [dotProduct_mulVec, ← mulVec_transpose, hT, pow_mulVec_evec S hS k i, smul_dotProduct,
    smul_eq_mul]

/-- **Spectral step for a power of a real symmetric matrix, over a set of indices.** `S` real
    symmetric with the orthonormal eigenbasis `v_i` and eigenvalues `s_i` of Mathlib. If
    `‖S^k w - α w‖² ≤ ε²` (Euclidean norm) and `|s_i^k - α| ≥ g > 0` for all `i` in a set `T` of
    indices, then `∑_{i ∈ T} (v_i · w)² ≤ ε²/g²`. -/
theorem spectral_step_pow_set {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (k : ℕ) (w : n → ℝ) {α ε g : ℝ} (hg : 0 < g)
    (hres : ∑ a, (((S ^ k) *ᵥ w) a - α * w a) ^ 2 ≤ ε ^ 2)
    (T : Finset n) (hT : ∀ i ∈ T, g ≤ |hS.eigenvalues i ^ k - α|) :
    ∑ i ∈ T, (evec hS i ⬝ᵥ w) ^ 2 ≤ ε ^ 2 / g ^ 2 := by
  obtain ⟨z, hz⟩ : ∃ z : n → ℝ, z = (S ^ k) *ᵥ w - α • w := ⟨_, rfl⟩
  have hcz : ∀ i, evec hS i ⬝ᵥ z = (hS.eigenvalues i ^ k - α) * (evec hS i ⬝ᵥ w) := by
    intro i
    rw [hz, dotProduct_sub, coord_pow S hS k w i, dotProduct_smul, smul_eq_mul]
    ring
  have hpz : z ⬝ᵥ z = ∑ i, ((hS.eigenvalues i ^ k - α) * (evec hS i ⬝ᵥ w)) ^ 2 := by
    rw [parseval S hS z]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcz i])
  have hzz : z ⬝ᵥ z = ∑ a, (((S ^ k) *ᵥ w) a - α * w a) ^ 2 := by
    simp only [hz, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have h1 : ∑ i ∈ T, g ^ 2 * (evec hS i ⬝ᵥ w) ^ 2
      ≤ ∑ i, ((hS.eigenvalues i ^ k - α) * (evec hS i ⬝ᵥ w)) ^ 2 := by
    calc ∑ i ∈ T, g ^ 2 * (evec hS i ⬝ᵥ w) ^ 2
        ≤ ∑ i ∈ T, ((hS.eigenvalues i ^ k - α) * (evec hS i ⬝ᵥ w)) ^ 2 := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have h2 := pow_le_pow_left₀ hg.le (hT i hi) 2
          rw [sq_abs] at h2
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right h2 (_root_.sq_nonneg _)
      _ ≤ ∑ i, ((hS.eigenvalues i ^ k - α) * (evec hS i ⬝ᵥ w)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => _root_.sq_nonneg _)
  have h3 : (∑ i ∈ T, (evec hS i ⬝ᵥ w) ^ 2) * g ^ 2
      = ∑ i ∈ T, g ^ 2 * (evec hS i ⬝ᵥ w) ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [le_div_iff₀ (pow_pos hg 2), h3]
  linarith [hpz, hzz]

/-- **(1) Spectral step for a real symmetric matrix.** If `∑_a ((A w)_a - α w_a)² ≤ ε²` and
    `g > 0`, then the squared norm of the component of `w` in the span of the eigenvectors with
    `|eigenvalue - α| ≥ g` is at most `ε²/g²`. -/
theorem spectral_step {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (w : n → ℝ) {α ε g : ℝ} (hg : 0 < g)
    (hres : ∑ a, ((A *ᵥ w) a - α * w a) ^ 2 ≤ ε ^ 2) :
    ∑ i ∈ Finset.univ.filter (fun i => g ≤ |hA.eigenvalues i - α|), (evec hA i ⬝ᵥ w) ^ 2
      ≤ ε ^ 2 / g ^ 2 := by
  have hres' : ∑ a, (((A ^ 1) *ᵥ w) a - α * w a) ^ 2 ≤ ε ^ 2 := by
    rw [pow_one]; exact hres
  refine spectral_step_pow_set A hA 1 w hg hres' _ (fun i hi => ?_)
  rw [pow_one]
  exact (Finset.mem_filter.mp hi).2

/-- **(2) Spectral step for `S^k` in the eigenbasis of `S`**, with the set of all indices whose
    `k`-th power of the eigenvalue is at a distance at least `g` from `α`. -/
theorem spectral_step_pow {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (k : ℕ) (w : n → ℝ) {α ε g : ℝ} (hg : 0 < g)
    (hres : ∑ a, (((S ^ k) *ᵥ w) a - α * w a) ^ 2 ≤ ε ^ 2) :
    ∑ i ∈ Finset.univ.filter (fun i => g ≤ |hS.eigenvalues i ^ k - α|), (evec hS i ⬝ᵥ w) ^ 2
      ≤ ε ^ 2 / g ^ 2 :=
  spectral_step_pow_set S hS k w hg hres _ (fun i hi => (Finset.mem_filter.mp hi).2)

/-! ### The orthogonal projection onto the span of the eigenvectors of a set `J` of indices -/

/-- `Π_J w = ∑_{i ∈ J} (v_i · w) v_i`. -/
noncomputable def specProj {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (J : Finset n) (w : n → ℝ) : n → ℝ :=
  fun a => ∑ i ∈ J, (evec hA i ⬝ᵥ w) * evec hA i a

theorem coord_comb {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (J : Finset n) (c : n → ℝ) (j : n) :
    (evec hA j ⬝ᵥ fun a => ∑ i ∈ J, c i * evec hA i a) = if j ∈ J then c j else 0 := by
  have h : (evec hA j ⬝ᵥ fun a => ∑ i ∈ J, c i * evec hA i a)
      = ∑ i ∈ J, c i * (evec hA j ⬝ᵥ evec hA i) := by
    simp only [dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun a _ => by ring))
  rw [h]
  simp only [evec_orthonormal, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

theorem coord_specProj {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (J : Finset n) (w : n → ℝ) (j : n) :
    evec hA j ⬝ᵥ specProj hA J w = if j ∈ J then evec hA j ⬝ᵥ w else 0 :=
  coord_comb A hA J (fun i => evec hA i ⬝ᵥ w) j

/-- `‖(1 - Π_J) w‖² = ∑_{i ∉ J} (v_i · w)²`. -/
theorem residual_norm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (J : Finset n) (w : n → ℝ) :
    (w - specProj hA J w) ⬝ᵥ (w - specProj hA J w) = ∑ i ∈ Jᶜ, (evec hA i ⬝ᵥ w) ^ 2 := by
  rw [parseval A hA]
  have hc : ∀ j, evec hA j ⬝ᵥ (w - specProj hA J w)
      = if j ∈ J then 0 else evec hA j ⬝ᵥ w := by
    intro j
    rw [dotProduct_sub, coord_specProj A hA J w j]
    split_ifs <;> simp
  have hs : ∑ j ∈ Jᶜ, (if j ∈ J then (0 : ℝ) else evec hA j ⬝ᵥ w) ^ 2
      = ∑ j, (if j ∈ J then (0 : ℝ) else evec hA j ⬝ᵥ w) ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hjJ : j ∈ J := by simpa using hj
    simp [hjJ]
  have he : ∑ j, (evec hA j ⬝ᵥ (w - specProj hA J w)) ^ 2
      = ∑ j, (if j ∈ J then (0 : ℝ) else evec hA j ⬝ᵥ w) ^ 2 :=
    Finset.sum_congr rfl (fun j _ => by rw [hc j])
  rw [he, ← hs]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjJ : j ∉ J := Finset.mem_compl.mp hj
  simp [hjJ]

/-- **Spectral step in the form of the corollary.** `S` real symmetric, `J` a set of indices of
    its eigenbasis (the cluster). HYPOTHESES: `‖S^k w - α w‖² ≤ ε²` and every eigenvalue outside
    the cluster has `|s_i^k - α| ≥ g > 0`. Then `‖(1 - Π_J) w‖² ≤ ε²/g²`, where `Π_J` is the
    orthogonal projection onto the span of the eigenvectors `v_i`, `i ∈ J`. -/
theorem spectral_proj {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) (k : ℕ) (w : n → ℝ) {α ε g : ℝ} (hg : 0 < g)
    (hres : ∑ a, (((S ^ k) *ᵥ w) a - α * w a) ^ 2 ≤ ε ^ 2)
    (J : Finset n) (hJ : ∀ i, i ∉ J → g ≤ |hS.eigenvalues i ^ k - α|) :
    (w - specProj hS J w) ⬝ᵥ (w - specProj hS J w) ≤ ε ^ 2 / g ^ 2 := by
  rw [residual_norm S hS J w]
  exact spectral_step_pow_set S hS k w hg hres Jᶜ (fun i hi => hJ i (Finset.mem_compl.mp hi))

/-! ### (3) Schur test in the Euclidean norm and the approximate eigenvector -/

/-- Schur test: if all absolute row sums and all absolute column sums of `E` are at most `η`,
    then `‖E w‖² ≤ η² ‖w‖²`. -/
theorem schur_l2 {n : Type} [Fintype n] (E : Matrix n n ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hrow : ∀ i, ∑ j, |E i j| ≤ η) (hcol : ∀ j, ∑ i, |E i j| ≤ η) (w : n → ℝ) :
    ∑ a, ((E *ᵥ w) a) ^ 2 ≤ η ^ 2 * (w ⬝ᵥ w) := by
  have hrowsq : ∀ a, ((E *ᵥ w) a) ^ 2 ≤ η * ∑ j, |E a j| * w j ^ 2 := by
    intro a
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (Finset.univ : Finset n)
      (r := fun j => E a j * w j) (f := fun j => |E a j|) (g := fun j => |E a j| * w j ^ 2)
      (fun j _ => abs_nonneg _) (fun j _ => mul_nonneg (abs_nonneg _) (_root_.sq_nonneg _))
      (fun j _ => by
        show (E a j * w j) ^ 2 = |E a j| * (|E a j| * w j ^ 2)
        rw [mul_pow, ← sq_abs (E a j)]; ring)
    have hnn : 0 ≤ ∑ j, |E a j| * w j ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (_root_.sq_nonneg _))
    calc ((E *ᵥ w) a) ^ 2 = (∑ j, E a j * w j) ^ 2 := by simp only [mulVec, dotProduct]
      _ ≤ (∑ j, |E a j|) * ∑ j, |E a j| * w j ^ 2 := hcs
      _ ≤ η * ∑ j, |E a j| * w j ^ 2 := mul_le_mul_of_nonneg_right (hrow a) hnn
  have hww : ∑ j, w j ^ 2 = w ⬝ᵥ w := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  calc ∑ a, ((E *ᵥ w) a) ^ 2 ≤ ∑ a, η * ∑ j, |E a j| * w j ^ 2 :=
        Finset.sum_le_sum (fun a _ => hrowsq a)
    _ = η * ∑ j, (∑ a, |E a j|) * w j ^ 2 := by
        rw [← Finset.mul_sum Finset.univ (fun a => ∑ j, |E a j| * w j ^ 2) η]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_mul])
    _ ≤ η * ∑ j, η * w j ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hcol j) (_root_.sq_nonneg _))) hη
    _ = η ^ 2 * (w ⬝ᵥ w) := by
        rw [← Finset.mul_sum Finset.univ (fun j => w j ^ 2) η, hww]; ring

/-- The triangle inequality of the Euclidean norm, in squared form. -/
theorem l2_triangle {n : Type} [Fintype n] (x y : n → ℝ) {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hx : ∑ a, x a ^ 2 ≤ X ^ 2) (hy : ∑ a, y a ^ 2 ≤ Y ^ 2) :
    ∑ a, (x a + y a) ^ 2 ≤ (X + Y) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset n) x y
  have hyn : 0 ≤ ∑ a, y a ^ 2 := Finset.sum_nonneg (fun a _ => _root_.sq_nonneg _)
  have h1 : (∑ a, x a * y a) ^ 2 ≤ (X * Y) ^ 2 := by
    calc (∑ a, x a * y a) ^ 2 ≤ (∑ a, x a ^ 2) * ∑ a, y a ^ 2 := hcs
      _ ≤ X ^ 2 * Y ^ 2 := mul_le_mul hx hy hyn (_root_.sq_nonneg X)
      _ = (X * Y) ^ 2 := by ring
  have h2 : ∑ a, x a * y a ≤ X * Y := (abs_le_of_sq_le_sq' h1 (mul_nonneg hX hY)).2
  have h3 : ∑ a, (x a + y a) ^ 2 = ∑ a, x a ^ 2 + 2 * ∑ a, x a * y a + ∑ a, y a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [h3]
  nlinarith [h2, hx, hy]

/-- **(3) Approximate eigenvector from a bound for the row and column sums.** If all absolute
    row and column sums of `S^k - Q` are at most `η`, `‖w‖² ≤ W²` and `‖Q w - α w‖² ≤ εQ²`, then
    `‖S^k w - α w‖² ≤ (η W + εQ)²`. No symmetry is used. -/
theorem approx_eigvec {n : Type} [Fintype n] [DecidableEq n] (S Q : Matrix n n ℝ) (k : ℕ)
    (w : n → ℝ) {α η εQ W : ℝ} (hη : 0 ≤ η) (hεQ : 0 ≤ εQ) (hW : 0 ≤ W)
    (hrow : ∀ i, ∑ l, |(S ^ k) i l - Q i l| ≤ η)
    (hcol : ∀ l, ∑ i, |(S ^ k) i l - Q i l| ≤ η)
    (hw : w ⬝ᵥ w ≤ W ^ 2)
    (hQ : ∑ a, ((Q *ᵥ w) a - α * w a) ^ 2 ≤ εQ ^ 2) :
    ∑ a, (((S ^ k) *ᵥ w) a - α * w a) ^ 2 ≤ (η * W + εQ) ^ 2 := by
  have h1 := schur_l2 (S ^ k - Q) hη (fun i => by simpa using hrow i)
    (fun l => by simpa using hcol l) w
  have h1' : ∑ a, (((S ^ k - Q) *ᵥ w) a) ^ 2 ≤ (η * W) ^ 2 := by
    calc ∑ a, (((S ^ k - Q) *ᵥ w) a) ^ 2 ≤ η ^ 2 * (w ⬝ᵥ w) := h1
      _ ≤ η ^ 2 * W ^ 2 := mul_le_mul_of_nonneg_left hw (_root_.sq_nonneg η)
      _ = (η * W) ^ 2 := by ring
  have h := l2_triangle (fun a => ((S ^ k - Q) *ᵥ w) a) (fun a => (Q *ᵥ w) a - α * w a)
    (mul_nonneg hη hW) hεQ h1' hQ
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [sub_mulVec, Pi.sub_apply]
  ring

/-- The same for symmetric `S` and `Q`, where the column sums follow from the row sums. -/
theorem approx_eigvec_sym {n : Type} [Fintype n] [DecidableEq n] (S Q : Matrix n n ℝ)
    (hS : S.IsHermitian) (hQs : ∀ i j, Q i j = Q j i) (k : ℕ)
    (w : n → ℝ) {α η εQ W : ℝ} (hη : 0 ≤ η) (hεQ : 0 ≤ εQ) (hW : 0 ≤ W)
    (hrow : ∀ i, ∑ l, |(S ^ k) i l - Q i l| ≤ η)
    (hw : w ⬝ᵥ w ≤ W ^ 2)
    (hQ : ∑ a, ((Q *ᵥ w) a - α * w a) ^ 2 ≤ εQ ^ 2) :
    ∑ a, (((S ^ k) *ᵥ w) a - α * w a) ^ 2 ≤ (η * W + εQ) ^ 2 := by
  have hsym : ∀ i l, (S ^ k) i l = (S ^ k) l i := by
    intro i l
    have := congrFun (congrFun (hS.pow k) l) i
    simpa using this
  have hcol : ∀ l, ∑ i, |(S ^ k) i l - Q i l| ≤ η := fun l => by
    have e : ∑ i, |(S ^ k) i l - Q i l| = ∑ i, |(S ^ k) l i - Q l i| :=
      Finset.sum_congr rfl (fun i _ => by rw [hsym i l, hQs i l])
    rw [e]; exact hrow l
  exact approx_eigvec S Q k w hη hεQ hW hrow hcol hw hQ

/-- **Deterministic core of the corollary for a general comparison matrix.** `S`, `Q` real
    symmetric. HYPOTHESES: absolute row sums of `S^k - Q` at most `η`; `‖w‖² ≤ W²`;
    `‖Q w - α w‖² ≤ εQ²`; all eigenvalues of `S` outside the cluster `J` have
    `|s_i^k - α| ≥ g > 0`. Then `‖(1 - Π_J) w‖² ≤ (η W + εQ)²/g²`. -/
theorem eigspace_det {n : Type} [Fintype n] [DecidableEq n] (S Q : Matrix n n ℝ)
    (hS : S.IsHermitian) (hQs : ∀ i j, Q i j = Q j i) (k : ℕ)
    (w : n → ℝ) {α η εQ W g : ℝ} (hη : 0 ≤ η) (hεQ : 0 ≤ εQ) (hW : 0 ≤ W) (hg : 0 < g)
    (hrow : ∀ i, ∑ l, |(S ^ k) i l - Q i l| ≤ η)
    (hw : w ⬝ᵥ w ≤ W ^ 2)
    (hQ : ∑ a, ((Q *ᵥ w) a - α * w a) ^ 2 ≤ εQ ^ 2)
    (J : Finset n) (hJ : ∀ i, i ∉ J → g ≤ |hS.eigenvalues i ^ k - α|) :
    (w - specProj hS J w) ⬝ᵥ (w - specProj hS J w) ≤ (η * W + εQ) ^ 2 / g ^ 2 :=
  spectral_proj S hS k w hg (approx_eigvec_sym S Q hS hQs k w hη hεQ hW hrow hw hQ) J hJ

/-! ### (3b) The sampled mode and a finite-rank kernel matrix -/

/-- **A column of `v` is an approximate eigenvector of the finite-rank kernel matrix.**
    `Q_ij = ∑_f a_f v_if v_jf`. HYPOTHESIS: the Gram matrix `vᵀ v` is entrywise within `γ` of the
    identity. Then for the column `w = v_{·f0}`:
    `‖Q w - a_{f0} w‖² ≤ (1 + γ) (γ ∑_f |a_f|)²`. -/
theorem finite_rank_approx_eigvec {n F : Type} [Fintype n] [Fintype F] [DecidableEq F]
    (v : Matrix n F ℝ) (a : F → ℝ) (Q : Matrix n n ℝ)
    (hQ : ∀ i j, Q i j = ∑ f, a f * v i f * v j f) (f0 : F) {γ : ℝ}
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ γ) :
    ∑ i, ((Q *ᵥ fun j => v j f0) i - a f0 * v i f0) ^ 2 ≤ (1 + γ) * (γ * ∑ f, |a f|) ^ 2 := by
  have hγ : 0 ≤ γ := le_trans (abs_nonneg _) (hG f0 f0)
  obtain ⟨G, hGd⟩ : ∃ G : F → F → ℝ, ∀ f g, G f g = ∑ i, v i f * v i g := ⟨_, fun _ _ => rfl⟩
  have hG' : ∀ f g, |G f g - (if f = g then 1 else 0)| ≤ γ := fun f g => by
    rw [hGd]; exact hG f g
  obtain ⟨b, hbd⟩ : ∃ b : F → ℝ, ∀ f, b f = a f * (G f f0 - (if f = f0 then 1 else 0)) :=
    ⟨_, fun _ => rfl⟩
  have hres : ∀ i, (Q *ᵥ fun j => v j f0) i - a f0 * v i f0 = ∑ f, b f * v i f := by
    intro i
    have e1 : (Q *ᵥ fun j => v j f0) i = ∑ f, a f * G f f0 * v i f := by
      have e0 : (Q *ᵥ fun j => v j f0) i = ∑ j, ∑ f, a f * v i f * v j f * v j f0 := by
        simp only [mulVec, dotProduct, hQ, Finset.sum_mul]
      rw [e0, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [hGd, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have e2 : a f0 * v i f0 = ∑ f, a f * (if f = f0 then 1 else 0) * v i f := by
      rw [Finset.sum_eq_single f0]
      · simp
      · intro f _ hf; simp [hf]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [e1, e2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun f _ => by rw [hbd]; ring)
  have hi : ∀ i, (∑ f, b f * v i f) ^ 2 = ∑ f, ∑ g, b f * b g * (v i f * v i g) := by
    intro i
    rw [pow_two, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun g _ => by ring))
  have hsq : ∑ i, (∑ f, b f * v i f) ^ 2 = ∑ f, ∑ g, b f * b g * G f g := by
    calc ∑ i, (∑ f, b f * v i f) ^ 2
        = ∑ i, ∑ f, ∑ g, b f * b g * (v i f * v i g) := Finset.sum_congr rfl (fun i _ => hi i)
      _ = ∑ f, ∑ i, ∑ g, b f * b g * (v i f * v i g) := Finset.sum_comm
      _ = ∑ f, ∑ g, ∑ i, b f * b g * (v i f * v i g) :=
          Finset.sum_congr rfl (fun f _ => Finset.sum_comm)
      _ = ∑ f, ∑ g, b f * b g * G f g :=
          Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun g _ => by
            rw [hGd, Finset.mul_sum]))
  have hGb : ∀ f g, |G f g| ≤ 1 + γ := by
    intro f g
    have h := hG' f g
    split_ifs at h <;> (rw [abs_le] at h ⊢; constructor <;> linarith [h.1, h.2])
  have hbb : ∀ f, |b f| ≤ γ * |a f| := by
    intro f
    rw [hbd, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hG' f f0) (abs_nonneg _)
  have hterm : ∀ f g, b f * b g * G f g ≤ (1 + γ) * (|b f| * |b g|) := by
    intro f g
    calc b f * b g * G f g ≤ |b f * b g * G f g| := le_abs_self _
      _ = |b f| * |b g| * |G f g| := by rw [abs_mul, abs_mul]
      _ ≤ |b f| * |b g| * (1 + γ) :=
          mul_le_mul_of_nonneg_left (hGb f g) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (1 + γ) * (|b f| * |b g|) := by ring
  have hsumb : ∑ f, |b f| ≤ γ * ∑ f, |a f| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun f _ => hbb f)
  have hbn : 0 ≤ ∑ f, |b f| := Finset.sum_nonneg (fun f _ => abs_nonneg _)
  calc ∑ i, ((Q *ᵥ fun j => v j f0) i - a f0 * v i f0) ^ 2
      = ∑ i, (∑ f, b f * v i f) ^ 2 := Finset.sum_congr rfl (fun i _ => by rw [hres i])
    _ = ∑ f, ∑ g, b f * b g * G f g := hsq
    _ ≤ ∑ f, ∑ g, (1 + γ) * (|b f| * |b g|) :=
        Finset.sum_le_sum (fun f _ => Finset.sum_le_sum (fun g _ => hterm f g))
    _ = (1 + γ) * (∑ f, |b f|) ^ 2 := by
        rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun f _ => by rw [Finset.mul_sum])
    _ ≤ (1 + γ) * (γ * ∑ f, |a f|) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbn hsumb 2) (by linarith)

/-- **Deterministic steps of Corollary "Eigenspaces on a flat torus", combined.** `S` real
    symmetric with eigenbasis `v_i` and eigenvalues `s_i`; `Q_ij = ∑_f a_f v_if v_jf` a
    finite-rank kernel matrix; `w = v_{·f0}` a sampled mode. HYPOTHESES: (`hG`) the Gram matrix
    of the sampled modes is entrywise within `γ` of the identity; (`hrow`) every absolute row sum
    of `S^k - Q` is at most `η`; (`hJ`) every eigenvalue of `S` outside the cluster `J` has
    `|s_i^k - a_{f0}| ≥ g > 0`. CONCLUSION:
    `‖(1 - Π_J) w‖² ≤ ((1 + γ) (η + γ ∑_f |a_f|))² / g²`. -/
theorem eigspace_from_gram {n F : Type} [Fintype n] [DecidableEq n] [Fintype F] [DecidableEq F]
    (S Q : Matrix n n ℝ) (hS : S.IsHermitian) (k : ℕ) (v : Matrix n F ℝ) (a : F → ℝ)
    (hQ : ∀ i j, Q i j = ∑ f, a f * v i f * v j f) (f0 : F) {γ η g : ℝ} (hη : 0 ≤ η)
    (hg : 0 < g)
    (hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ γ)
    (hrow : ∀ i, ∑ l, |(S ^ k) i l - Q i l| ≤ η)
    (J : Finset n) (hJ : ∀ i, i ∉ J → g ≤ |hS.eigenvalues i ^ k - a f0|) :
    ((fun j => v j f0) - specProj hS J (fun j => v j f0))
        ⬝ᵥ ((fun j => v j f0) - specProj hS J (fun j => v j f0))
      ≤ ((1 + γ) * (η + γ * ∑ f, |a f|)) ^ 2 / g ^ 2 := by
  have hγ : 0 ≤ γ := le_trans (abs_nonneg _) (hG f0 f0)
  have hsa : 0 ≤ ∑ f, |a f| := Finset.sum_nonneg (fun f _ => abs_nonneg _)
  have hQs : ∀ i j, Q i j = Q j i := by
    intro i j
    rw [hQ, hQ]
    exact Finset.sum_congr rfl (fun f _ => by ring)
  have hw : (fun j => v j f0) ⬝ᵥ (fun j => v j f0) ≤ (1 + γ) ^ 2 := by
    have h := hG f0 f0
    rw [if_pos rfl, abs_le] at h
    have e : (fun j => v j f0) ⬝ᵥ (fun j => v j f0) = ∑ i, v i f0 * v i f0 := by
      simp only [dotProduct]
    rw [e]
    nlinarith [h.2]
  have hεQ : 0 ≤ (1 + γ) * (γ * ∑ f, |a f|) :=
    mul_nonneg (by linarith) (mul_nonneg hγ hsa)
  have hQw : ∑ i, ((Q *ᵥ fun j => v j f0) i - a f0 * v i f0) ^ 2
      ≤ ((1 + γ) * (γ * ∑ f, |a f|)) ^ 2 := by
    refine le_trans (finite_rank_approx_eigvec v a Q hQ f0 hG) ?_
    have hx : 0 ≤ (γ * ∑ f, |a f|) ^ 2 := _root_.sq_nonneg _
    nlinarith [mul_nonneg hγ hx, mul_nonneg (mul_nonneg hγ hγ) hx]
  have h := eigspace_det S Q hS hQs k (fun j => v j f0) hη hεQ (by linarith : (0 : ℝ) ≤ 1 + γ)
    hg hrow hw hQw J hJ
  have e : η * (1 + γ) + (1 + γ) * (γ * ∑ f, |a f|) = (1 + γ) * (η + γ * ∑ f, |a f|) := by ring
  rw [e] at h
  exact h

end EigenspaceSteps

/-! ### Eigenvalues through column sums (`thm:eigtorus-l1`, first half of part (i): comparison with the kernel matrix) -/

namespace EigenvaluesL1

open CTG.Reals.TorusReduction TorusReductionL1

/-! ### New material -/

/-- Powers of a matrix with row sums one have row sums one. -/
theorem pow_row_sum {n : Type} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hrow : ∀ i, ∑ l, P i l = 1) (k : ℕ) (i : n) : ∑ l, (P ^ k) i l = 1 := by
  induction k generalizing i with
  | zero => simp [Matrix.one_apply]
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hrow, mul_one]
    exact ih i

/-- **Target (1): absolute row sums of `S^k - G/N` from the `ℓ¹` kernel bound (deterministic).**
    `S i l = r i · P i l / r l` symmetric, `P ≥ 0` row-stochastic, `|r i / r l - 1| ≤ θ`, `G` symmetric.
    HYPOTHESIS `hL1`: `∑_a |N (P^k) a i - G a i| ≤ N e` for every `i` (sum over the FIRST index).
    Then (a) every column sum of `P^k` is at most `(1 + θ)²` (reversibility, read off from the
    symmetry of `S^k`), and (b) every absolute row sum of `S^k - G/N` is at most `θ (1 + θ)² + e`.
    The row sum at `i` is rewritten as the column sum at `i` by the symmetry of `S^k` and `G`. -/
theorem l1_row_sums {n : Type} [Fintype n] [DecidableEq n] (S P G : Matrix n n ℝ) (r : n → ℝ)
    {N θ e : ℝ} (hN : 0 < N) (hr : ∀ i, 0 < r i)
    (hSP : ∀ i l, S i l = r i * P i l / r l) (hS : S.IsHermitian)
    (hP0 : ∀ i l, 0 ≤ P i l) (hrow : ∀ i, ∑ l, P i l = 1)
    (hθ : ∀ i l, |r i / r l - 1| ≤ θ) (hG : ∀ i l, G i l = G l i) (k : ℕ)
    (hL1 : ∀ i, ∑ a, |N * (P ^ k) a i - G a i| ≤ N * e) (i : n) :
    (∑ l, (P ^ k) l i ≤ (1 + θ) ^ 2) ∧
    ∑ l, |(S ^ k) i l - G i l / N| ≤ θ * (1 + θ) ^ 2 + e := by
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (hθ i i)
  have hSk : (S ^ k).IsHermitian := hS.pow k
  have hsym : ∀ a b, (S ^ k) a b = (S ^ k) b a := by
    intro a b
    have := congrFun (congrFun hSk b) a
    simpa using this
  have hconj := conj_pow_entry S P r hr hSP k
  have hPk0 := pow_entries_nonneg P hP0 k
  have hPkrow := pow_row_sum P hrow k
  have hrev : ∀ l, (P ^ k) l i = (r i / r l) ^ 2 * (P ^ k) i l := by
    intro l
    have h := hsym l i
    rw [hconj l i, hconj i l, div_eq_div_iff (hr i).ne' (hr l).ne'] at h
    rw [div_pow, div_mul_eq_mul_div, eq_div_iff (pow_pos (hr l) 2).ne']
    linear_combination h
  have hratio : ∀ l, (r i / r l) ^ 2 ≤ (1 + θ) ^ 2 := by
    intro l
    have h1 := (abs_le.mp (hθ i l)).2
    exact pow_le_pow_left₀ (div_pos (hr i) (hr l)).le (by linarith) 2
  have hcol : ∑ l, (P ^ k) l i ≤ (1 + θ) ^ 2 := by
    calc ∑ l, (P ^ k) l i = ∑ l, (r i / r l) ^ 2 * (P ^ k) i l :=
          Finset.sum_congr rfl fun l _ => hrev l
      _ ≤ ∑ l, (1 + θ) ^ 2 * (P ^ k) i l :=
          Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hratio l) (hPk0 i l)
      _ = (1 + θ) ^ 2 := by rw [← Finset.mul_sum, hPkrow i, mul_one]
  refine ⟨hcol, ?_⟩
  have hterm : ∀ l, |(S ^ k) i l - G i l / N|
      ≤ θ * (P ^ k) l i + |N * (P ^ k) l i - G l i| / N := by
    intro l
    rw [hsym i l, hG i l, hconj l i]
    have e1 : r l * (P ^ k) l i / r i - G l i / N
        = (r l / r i - 1) * (P ^ k) l i + (N * (P ^ k) l i - G l i) / N := by
      rw [sub_div, mul_div_cancel_left₀ _ hN.ne']
      ring
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_div, abs_of_pos hN, abs_of_nonneg (hPk0 l i)]
    have := mul_le_mul_of_nonneg_right (hθ l i) (hPk0 l i)
    linarith
  calc ∑ l, |(S ^ k) i l - G i l / N|
      ≤ ∑ l, (θ * (P ^ k) l i + |N * (P ^ k) l i - G l i| / N) :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = θ * ∑ l, (P ^ k) l i + (∑ l, |N * (P ^ k) l i - G l i|) / N := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    _ ≤ θ * (1 + θ) ^ 2 + e := by
        have h1 := mul_le_mul_of_nonneg_left hcol hθ0
        have h2 : (∑ l, |N * (P ^ k) l i - G l i|) / N ≤ e := by
          rw [div_le_iff₀ hN]; linarith [hL1 i]
        linarith

/-- **Target (2): Weyl (deterministic).** In the situation of `l1_row_sums`, with `Q = G/N` and
    nonnegative eigenvalues of `S`: the `k`-th power of the `j`-th ordered eigenvalue of `S` is
    within `θ (1 + θ)² + e` of the `j`-th ordered eigenvalue of `Q`. No factor `m_k`. -/
theorem l1_eig {n : Type} [Fintype n] [DecidableEq n] (S P G Q : Matrix n n ℝ) (r : n → ℝ)
    {N θ e : ℝ} (hN : 0 < N) (hr : ∀ i, 0 < r i)
    (hSP : ∀ i l, S i l = r i * P i l / r l) (hS : S.IsHermitian)
    (hP0 : ∀ i l, 0 ≤ P i l) (hrow : ∀ i, ∑ l, P i l = 1)
    (hθ : ∀ i l, |r i / r l - 1| ≤ θ) (hG : ∀ i l, G i l = G l i)
    (hQ : Q.IsHermitian) (hQG : ∀ i l, Q i l = G i l / N)
    (hnn : ∀ j, 0 ≤ hS.eigenvalues₀ j) (k : ℕ)
    (hL1 : ∀ i, ∑ a, |N * (P ^ k) a i - G a i| ≤ N * e) (j : Fin (Fintype.card n)) :
    |hS.eigenvalues₀ j ^ k - hQ.eigenvalues₀ j| ≤ θ * (1 + θ) ^ 2 + e := by
  have hSk : (S ^ k).IsHermitian := hS.pow k
  have hw := weyl_row_sums (S ^ k) Q hSk hQ (fun i => by
    simp only [hQG]
    exact (l1_row_sums S P G r hN hr hSP hS hP0 hrow hθ hG k hL1 i).2) j
  rwa [eigenvalues₀_pow S hS hnn k hSk j] at hw

/-- The kernel after `k` steps is even. -/
theorem heatP_even (d : ℕ) (σ : ℝ) (k : ℕ) (u : FlatTorus d) :
    heatP d σ k (-u) = heatP d σ k u := by
  unfold heatP
  split_ifs
  · rfl
  · exact heatTorus_even d _ u

/-- The kernel matrix `Q_k = (p_{kσ}(x_a - x_i)/N)` is symmetric. -/
theorem kernelQ_isHermitian (d : ℕ) (σ : ℝ) (N k : ℕ) (x : ℕ → FlatTorus d) :
    (Matrix.of fun a i : Fin N => heatP d σ k (x a - x i) / (N : ℝ)).IsHermitian := by
  ext a i
  simp only [conjTranspose_apply, of_apply, star_trivial]
  rw [← heatP_even, neg_sub]

/-- **Targets (1)+(2) for the sampled graph on the torus (deterministic).** Points `x_0, …, x_{N-1}`,
    kernel `p_σ` (variance `σ`), self-loops, `ρ = heatRho`, `P = walkMatrix`, `S = symGraph`.
    HYPOTHESES: the normalisation `|ρ_a - 1| ≤ δ ≤ 1/8` and the `ℓ¹` kernel bound
    `∑_a |N (P^k) a i - p_{kσ}(x_a - x_i)| ≤ N e` for every `i`. Then for every `j`
    `|s_j^k - μ_j(Q_k)| ≤ 3δ (1 + 3δ)² + e`, where `μ_j(Q_k)` are the ordered eigenvalues of the
    kernel matrix `Q_k = (p_{kσ}(x_a - x_i)/N)` (indices from `0`, decreasing order). -/
theorem torus_eig_l1_det {σ δ e : ℝ} (hσ : 0 < σ) (d N : ℕ) [NeZero N] (x : ℕ → FlatTorus d)
    (hδ : δ ≤ 1 / 8) (hρ : ∀ a : Fin N, |heatRho d σ N x a - 1| ≤ δ) (k : ℕ)
    (hL1 : ∀ i : Fin N, ∑ a : Fin N, |(N : ℝ) * ((walkMatrix
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
          (fun a : Fin N => heatRho d σ N x a)) ^ k) a i
        - heatP d σ k (x a - x i)| ≤ (N : ℝ) * e)
    (hS : (symGraph (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j))
        (fun a : Fin N => heatRho d σ N x a)).IsHermitian)
    (hQ : (Matrix.of fun a i : Fin N => heatP d σ k (x a - x i) / (N : ℝ)).IsHermitian)
    (j : Fin (Fintype.card (Fin N))) :
    |hS.eigenvalues₀ j ^ k - hQ.eigenvalues₀ j| ≤ 3 * δ * (1 + 3 * δ) ^ 2 + e := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hcard : (Fintype.card (Fin N) : ℝ) = N := by simp
  have hc : 0 < 2 * Real.pi ^ 2 * σ := by have := Real.pi_pos; positivity
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hρ ⟨0, hN0⟩)
  set Kf : Fin N → Fin N → ℝ := fun a j => heatTorus d (2 * Real.pi ^ 2 * σ) (x a - x j)
    with hKdef
  set rho : Fin N → ℝ := fun a => heatRho d σ N x a with hrhodef
  have hK0 : ∀ a j, 0 ≤ Kf a j := fun a j => heatTorus_nonneg hc d _
  have hKsym : ∀ a j, Kf a j = Kf j a := fun a j => by
    simp only [hKdef]; rw [← heatTorus_even, neg_sub]
  have hrho1 : ∀ b, |rho b - 1| ≤ δ := hρ
  have hrhopos : ∀ b, 0 < rho b := fun b => by
    have := abs_le.mp (hrho1 b); linarith [this.1]
  have hrhoeq : ∀ b, (Fintype.card (Fin N) : ℝ) * rho b = ∑ l, Kf b l := fun b => by
    rw [hcard]
    have h1 : (∑ l : Fin N, Kf b l)
        = ∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l) :=
      Fin.sum_univ_eq_sum_range (fun l => heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l)) N
    rw [h1]
    show (N : ℝ) * ((∑ l ∈ Finset.range N, heatTorus d (2 * Real.pi ^ 2 * σ) (x b - x l)) / N) = _
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hNpos.ne']
  have hDb := fun i => graph_degree_bounds Kf hK0 rho hδ0 hδ hrhoeq hrho1 i
  have hcardpos : (0 : ℝ) < (Fintype.card (Fin N) : ℝ) := by rw [hcard]; exact hNpos
  have hDpos : ∀ i, 0 < ∑ l, Kf i l / (rho i * rho l) := fun i =>
    lt_of_lt_of_le (div_pos hcardpos (by linarith)) (hDb i).1
  have hθ : ∀ i l, |Real.sqrt (∑ m, Kf i m / (rho i * rho m))
      / Real.sqrt (∑ m, Kf l m / (rho l * rho m)) - 1| ≤ 3 * δ :=
    fun i l => sqrt_ratio_bound hcardpos hδ0 hδ (hDb i) (hDb l)
  have hP0 : ∀ i l, 0 ≤ walkMatrix Kf rho i l := fun i l => by
    simp only [walkMatrix, Matrix.of_apply]
    exact div_nonneg (div_nonneg (hK0 i l) (mul_pos (hrhopos i) (hrhopos l)).le) (hDpos i).le
  have hrow : ∀ i, ∑ l, walkMatrix Kf rho i l = 1 := fun i =>
    walkMatrix_row_sum Kf rho i (hDpos i).ne'
  have hnn : ∀ j, 0 ≤ hS.eigenvalues₀ j := fun j =>
    symGraph_eig_nonneg Kf rho
      (fun y => heatTorus_quadform_nonneg hc d (fun a : Fin N => x a) y) hS j
  exact l1_eig (symGraph Kf rho) (walkMatrix Kf rho)
    (Matrix.of fun a i : Fin N => heatP d σ k (x a - x i))
    (Matrix.of fun a i : Fin N => heatP d σ k (x a - x i) / (N : ℝ))
    (fun i => Real.sqrt (∑ m, Kf i m / (rho i * rho m))) hNpos
    (fun i => Real.sqrt_pos.mpr (hDpos i)) (fun i l => symGraph_conj Kf rho hDpos i l) hS hP0 hrow
    hθ (fun i l => by simp only [Matrix.of_apply]; rw [← heatP_even, neg_sub]) hQ
    (fun i l => rfl) hnn k hL1 j

/-- A measure bound from an inclusion in a union of two sets. -/
theorem real_le_of_subset2 {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S A B : Set Ω} {a b t : ℝ} (hA : μ.real A ≤ a)
    (hB : μ.real B ≤ b) (hsub : S ⊆ A ∪ B) (ht : a + b = t) :
    μ.real S ≤ t := by
  have h0 : μ.real S ≤ μ.real (A ∪ B) := measureReal_mono hsub (measure_ne_top μ _)
  have h1 : μ.real (A ∪ B) ≤ μ.real A + μ.real B := measureReal_union_le _ _
  linarith

/-- The constant of the sample statement: `6 · normC d + h4C d` (depends on `d` only). -/
noncomputable def eigL1C (d : ℕ) : ℝ := 6 * normC d + h4C d

/-- **Target (3): eigenvalues of the sampled graph against those of the kernel matrix, from the
    `ℓ¹` kernel bound, for a random sample.** Hypotheses of `kernel_theorem_G28` (independent
    uniform points on the flat torus, kernel of variance `σ ≤ 1`, self-loops, `M = p_σ(0)`,
    `δ' = √(M log N/N)`, `kernelC1 d · δ' √K ≤ 1`). Except on an event of probability at most
    `3/N³` (normalisation event and `ℓ¹` event of `good_events`): for all `1 ≤ k ≤ K` and all `j`
    `|s_j^k - μ_j(Q_k)| ≤ eigL1C d · δ' √k`,
    where `s_j` are the ordered eigenvalues of `S = symGraph` and `μ_j(Q_k)` the ordered eigenvalues
    of the KERNEL MATRIX `Q_k = (p_{kσ}(x_a - x_i)/N)` (not `e^{-kσλ_j}`). No factor `m_k`. -/
theorem eig_l1_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (hQ : (Matrix.of fun a i : Fin N =>
              heatP d σ k (X a ω - X i ω) / (N : ℝ)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          |hS.eigenvalues₀ j ^ k - hQ.eigenvalues₀ j| ≤ eigL1C d * δp * Real.sqrt k}
      ≤ 3 / (N : ℝ) ^ 3 := by
  obtain ⟨hn8, hPN, hPL⟩ := good_events hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange
  haveI : NeZero N := ⟨by omega⟩
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have hη : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  have hcδ := normC_nonneg d
  have hcE := h4C_nonneg d
  refine real_le_of_subset2 hPN hPL ?_ (by ring)
  intro ω hbad
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
  obtain ⟨hgN, hgL⟩ := hcon
  apply hbad
  intro k hk1 hkK hS hQ j
  have hk1r : (1 : ℝ) ≤ Real.sqrt k := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk1)
  have hnd : 0 ≤ normC d * δp := mul_nonneg hcδ hη
  have hL1 : ∀ i : Fin N, ∑ a : Fin N, |(N : ℝ) * ((walkMatrix
          (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
          (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)) ^ k) a i
        - heatP d σ k (X a ω - X i ω)| ≤ (N : ℝ) * (h4C d * δp * Real.sqrt k) := by
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have hk : k = 1 := by omega
      intro i
      rw [hk]
      refine (H4_one hσ d N (by omega) (fun j => X j ω) hn8 hgN i).trans ?_
      simp only [Nat.cast_one, Real.sqrt_one, mul_one]
      refine mul_le_mul_of_nonneg_left ?_ hNpos.le
      have h := h4C_ge d
      have h1 : 4 * (normC d * δp) * (1 + normC d * δp) ≤ 4 * (normC d * δp) * (9 / 8) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      have h2' := mul_le_mul_of_nonneg_right h hη
      linarith
    · exact hgL k h2 hkK
  have hdet := torus_eig_l1_det hσ d N (fun j => X j ω) hn8 hgN k hL1 hS hQ j
  refine hdet.trans ?_
  have ht2 : (normC d * δp) * (normC d * δp) ≤ (normC d * δp) * (1 / 8) :=
    mul_le_mul_of_nonneg_left hn8 hnd
  have hs : (1 + 3 * (normC d * δp)) ^ 2 ≤ 2 := by nlinarith [ht2, hn8, hnd]
  have h1 : 3 * (normC d * δp) * (1 + 3 * (normC d * δp)) ^ 2 ≤ 3 * (normC d * δp) * 2 :=
    mul_le_mul_of_nonneg_left hs (by linarith)
  have h2 : 6 * (normC d * δp) * 1 ≤ 6 * (normC d * δp) * Real.sqrt k :=
    mul_le_mul_of_nonneg_left hk1r (by linarith)
  have e : eigL1C d * δp * Real.sqrt k
      = 6 * (normC d * δp) * Real.sqrt k + h4C d * δp * Real.sqrt k := by
    unfold eigL1C; ring
  rw [e]
  linarith

end EigenvaluesL1

/-! ## Measurability of the exceptional sets of the three assembled statements
(`Assembled.eig_theorem_G38_i_all`, `Assembled.eig_theorem_G38_i_all_shell`, `Assembled.heat_trace_G29_uniform`). -/

namespace AssembledSets

open CTG.Reals.Assembled CTG.Reals.ExceptionalSets CTG.Reals.TraceG29

open Filter Topology

/-! ### Small lemmas on measurable sets given by predicates -/

theorem ms_and {α : Type*} [MeasurableSpace α] {P Q : α → Prop}
    (hP : MeasurableSet {x | P x}) (hQ : MeasurableSet {x | Q x}) :
    MeasurableSet {x | P x ∧ Q x} := hP.inter hQ

theorem ms_imp {α : Type*} [MeasurableSpace α] {p : Prop} {Q : α → Prop}
    (hQ : MeasurableSet {x | Q x}) : MeasurableSet {x | p → Q x} := by
  by_cases hp : p
  · have e : {x | p → Q x} = {x | Q x} := by
      ext x; exact ⟨fun h => h hp, fun h _ => h⟩
    rw [e]; exact hQ
  · have e : {x | p → Q x} = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ h => (hp h).elim⟩
    rw [e]; exact MeasurableSet.univ

theorem ms_exists {α : Type*} [MeasurableSpace α] {ι : Type*} [Countable ι] {Q : ι → α → Prop}
    (h : ∀ i, MeasurableSet {x | Q i x}) : MeasurableSet {x | ∃ i, Q i x} := by
  rw [Set.setOf_exists]
  exact MeasurableSet.iUnion h

/-! ### (1), (2) The exceptional sets of the eigenvalue statements for all indices -/

/-- The exceptional set of `Assembled.eig_theorem_G38_i_all_shell`, verbatim, is measurable. -/
theorem eig_theorem_G38_i_all_shell_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d N K : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → hS.eigenvalues₀ j = 1)
          ∧ (1 ≤ j.val →
            |hS.eigenvalues₀ j ^ k
                - Real.exp (-(2 * Real.pi ^ 2 * σ) * (shellIndex d j.val : ℝ)) ^ k|
              ≤ eigC3 d * δp * Real.sqrt k
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)} := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Fin (Fintype.card (Fin N)) → Set ℝ, T = fun (k : ℕ) (j : Fin (Fintype.card (Fin N))) => {x : ℝ |
      (j.val = 0 → x = 1)
      ∧ (1 ≤ j.val →
        |x ^ k
            - Real.exp (-(2 * Real.pi ^ 2 * σ) * (shellIndex d j.val : ℝ)) ^ k|
          ≤ eigC3 d * δp * Real.sqrt k
            * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)} := ⟨_, rfl⟩
  have hTm : ∀ k j, MeasurableSet (T k j) := by
    intro k j
    rw [hT]
    refine ms_and ?_ ?_
    · exact ms_imp (isClosed_eq continuous_id continuous_const).measurableSet
    · exact ms_imp (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hset : {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → hS.eigenvalues₀ j = 1)
          ∧ (1 ≤ j.val →
            |hS.eigenvalues₀ j ^ k
                - Real.exp (-(2 * Real.pi ^ 2 * σ) * (shellIndex d j.val : ℝ)) ^ k|
              ≤ eigC3 d * δp * Real.sqrt k
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)}
      = {ω | ∀ k, 1 ≤ k → k ≤ K → ∀ j : Fin (Fintype.card (Fin N)),
          eigTot N j (fun a b => symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) a b)
            ∈ T k j}ᶜ := by
    ext ω
    refine not_congr (forall_congr' fun k => imp_congr_right fun _ => imp_congr_right fun _ => ?_)
    rw [hT]
    exact forall_herm_iff (symGraph
        (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
        (fun i : Fin N =>
          (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N))
      (symGraph_sample_isHermitian (σ := σ) d N X ω)
      (fun j x => (j.val = 0 → x = 1)
        ∧ (1 ≤ j.val →
          |x ^ k
              - Real.exp (-(2 * Real.pi ^ 2 * σ) * (shellIndex d j.val : ℝ)) ^ k|
            ≤ eigC3 d * δp * Real.sqrt k
              * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0))
  rw [hset]
  refine MeasurableSet.compl ?_
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun j => ?_
  exact (eig_sample_measurable hσ d N X hX j) (hTm k j)

/-- The exceptional set of `Assembled.eig_theorem_G38_i_all`, verbatim, is measurable. -/
theorem eig_theorem_G38_i_all_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d N K : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j))
    (δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → hS.eigenvalues₀ j = 1)
          ∧ (1 ≤ j.val → ∃ q : ℕ, 1 ≤ q
            ∧ (∃ Hlt Hle : Finset (Fin d → ℤ),
                (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < (q : ℝ)) ∧
                (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ (q : ℝ)) ∧
                1 + 2 * Hlt.card ≤ j.val ∧ j.val ≤ 2 * Hle.card)
            ∧ |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * (q : ℝ)) ^ k|
              ≤ eigC3 d * δp * Real.sqrt k
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)} := by
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Fin (Fintype.card (Fin N)) → Set ℝ, T = fun (k : ℕ) (j : Fin (Fintype.card (Fin N))) => {x : ℝ |
      (j.val = 0 → x = 1)
      ∧ (1 ≤ j.val → ∃ q : ℕ, 1 ≤ q
        ∧ (∃ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < (q : ℝ)) ∧
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ (q : ℝ)) ∧
            1 + 2 * Hlt.card ≤ j.val ∧ j.val ≤ 2 * Hle.card)
        ∧ |x ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * (q : ℝ)) ^ k|
          ≤ eigC3 d * δp * Real.sqrt k
            * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)} := ⟨_, rfl⟩
  have hTm : ∀ k j, MeasurableSet (T k j) := by
    intro k j
    rw [hT]
    refine ms_and ?_ ?_
    · exact ms_imp (isClosed_eq continuous_id continuous_const).measurableSet
    · refine ms_imp (ms_exists fun q => ms_and (MeasurableSet.const _)
        (ms_and (MeasurableSet.const _) ?_))
      exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hset : {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → hS.eigenvalues₀ j = 1)
          ∧ (1 ≤ j.val → ∃ q : ℕ, 1 ≤ q
            ∧ (∃ Hlt Hle : Finset (Fin d → ℤ),
                (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < (q : ℝ)) ∧
                (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ (q : ℝ)) ∧
                1 + 2 * Hlt.card ≤ j.val ∧ j.val ≤ 2 * Hle.card)
            ∧ |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * (q : ℝ)) ^ k|
              ≤ eigC3 d * δp * Real.sqrt k
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)}
      = {ω | ∀ k, 1 ≤ k → k ≤ K → ∀ j : Fin (Fintype.card (Fin N)),
          eigTot N j (fun a b => symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N) a b)
            ∈ T k j}ᶜ := by
    ext ω
    refine not_congr (forall_congr' fun k => imp_congr_right fun _ => imp_congr_right fun _ => ?_)
    rw [hT]
    exact forall_herm_iff (symGraph
        (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X j ω))
        (fun i : Fin N =>
          (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ) (X i ω - X l ω)) / N))
      (symGraph_sample_isHermitian (σ := σ) d N X ω)
      (fun j x => (j.val = 0 → x = 1)
        ∧ (1 ≤ j.val → ∃ q : ℕ, 1 ≤ q
          ∧ (∃ Hlt Hle : Finset (Fin d → ℤ),
              (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < (q : ℝ)) ∧
              (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ (q : ℝ)) ∧
              1 + 2 * Hlt.card ≤ j.val ∧ j.val ≤ 2 * Hle.card)
          ∧ |x ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * (q : ℝ)) ^ k|
            ≤ eigC3 d * δp * Real.sqrt k
              * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0))
  rw [hset]
  refine MeasurableSet.compl ?_
  simp only [Set.setOf_forall]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun j => ?_
  exact (eig_sample_measurable hσ d N X hX j) (hTm k j)

/-! ### (3) The exceptional set of the trace estimate uniform in `τ` -/

/-- A bound for all parameters in a set is a measurable condition, if the bounded quantity is
    measurable in `ω` for each parameter and continuous in the parameter on the set
    (reduction to a countable dense subset of the parameter set). -/
theorem forall_param_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p q : ℝ → Prop}
    {h : Ω → ℝ → ℝ} {c : ℝ} (hm : ∀ τ, Measurable fun ω => h ω τ)
    (hc : ∀ ω, ContinuousOn (h ω) {τ | p τ ∧ q τ}) :
    MeasurableSet {ω | ∀ τ : ℝ, p τ → q τ → h ω τ ≤ c} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ↥{τ : ℝ | p τ ∧ q τ}
  have e : {ω | ∀ τ : ℝ, p τ → q τ → h ω τ ≤ c}
      = ⋂ t ∈ D, {ω | h ω (t : ℝ) ≤ c} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro H t _
      exact H t t.2.1 t.2.2
    · intro H τ hp hq
      have hcont : Continuous (Set.restrict {τ : ℝ | p τ ∧ q τ} (h ω)) :=
        continuousOn_iff_continuous_restrict.1 (hc ω)
      have hcl : IsClosed {t : ↥{τ : ℝ | p τ ∧ q τ} |
          Set.restrict {τ : ℝ | p τ ∧ q τ} (h ω) t ≤ c} :=
        isClosed_le hcont continuous_const
      have hsub : D ⊆ {t : ↥{τ : ℝ | p τ ∧ q τ} |
          Set.restrict {τ : ℝ | p τ ∧ q τ} (h ω) t ≤ c} := fun t ht => H t ht
      have hcl2 := hcl.closure_subset_iff.2 hsub
      have hmem : (⟨τ, ⟨hp, hq⟩⟩ : ↥{τ : ℝ | p τ ∧ q τ}) ∈ closure D := hDd _
      exact hcl2 hmem
  rw [e]
  exact MeasurableSet.biInter hDc fun t _ => measurableSet_le (hm t) measurable_const

/-- The Poisson mean is continuous in `τ` on bounded sets of nonnegative `τ`. -/
theorem poissonMean_continuousOn {σ : ℝ} (hσ : 0 < σ) (d : ℕ) (B : ℝ) :
    ContinuousOn (fun τ => poissonMean d σ τ) (Set.Icc 0 B) := by
  unfold poissonMean
  have hM0 : ∀ j : ℕ, 0 ≤ heatMode d σ (j + 1) := fun j =>
    le_trans zero_le_one (heatMode_ge_one hσ d (by omega))
  refine continuousOn_tsum
    (u := fun j : ℕ => B ^ (j + 1) / ((j + 1).factorial : ℝ)
      * heatTorus d (2 * Real.pi ^ 2 * σ) 0) (fun j => ?_) ?_ (fun j τ hτ => ?_)
  · have h1 : Continuous fun τ : ℝ => pw τ (j + 1) := by
      unfold pw
      fun_prop
    exact (h1.mul continuous_const).continuousOn
  · exact ((summable_nat_add_iff 1).2 (Real.summable_pow_div_factorial B)).mul_right _
  · have hτ0 : 0 ≤ τ := hτ.1
    have hw := pw_nonneg hτ0 (j + 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw, abs_of_nonneg (hM0 j)]
    have hfac : (0 : ℝ) ≤ ((j + 1).factorial : ℝ) := Nat.cast_nonneg _
    have h1 : pw τ (j + 1) ≤ B ^ (j + 1) / ((j + 1).factorial : ℝ) := by
      unfold pw
      have he : Real.exp (-τ) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      have hp : τ ^ (j + 1) / ((j + 1).factorial : ℝ) ≤ B ^ (j + 1) / ((j + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hτ0 hτ.2 (j + 1)) hfac
      have hp0 : 0 ≤ τ ^ (j + 1) / ((j + 1).factorial : ℝ) :=
        div_nonneg (pow_nonneg hτ0 _) hfac
      calc Real.exp (-τ) * (τ ^ (j + 1) / ((j + 1).factorial : ℝ))
          ≤ 1 * (B ^ (j + 1) / ((j + 1).factorial : ℝ)) :=
            mul_le_mul he hp hp0 zero_le_one
        _ = B ^ (j + 1) / ((j + 1).factorial : ℝ) := one_mul _
    exact mul_le_mul h1 (heatMode_le hσ d (by omega)) (hM0 j) (le_trans hw h1)

/-- The trace of `exp(τ(S - 1))` is continuous in `τ` for a symmetric matrix. -/
theorem trace_exp_continuous {n : Type} [Fintype n] [DecidableEq n] (S : Matrix n n ℝ)
    (hS : S.IsHermitian) :
    Continuous fun τ : ℝ => (NormedSpace.exp (τ • (S - 1))).trace := by
  have e : (fun τ : ℝ => (NormedSpace.exp (τ • (S - 1))).trace)
      = fun τ : ℝ => ∑ i, Real.exp (-(τ * (1 - hS.eigenvalues i))) :=
    funext fun τ => trace_exp_heat S hS τ
  rw [e]
  fun_prop

/-- The exceptional set of `Assembled.heat_trace_G29_uniform`, verbatim, is measurable. -/
theorem heat_trace_G29_uniform_set_measurable {Ω : Type*} {mΩ : MeasurableSpace Ω} {σ : ℝ}
    (hσ : 0 < σ) (d : ℕ) (X : ℕ → Ω → FlatTorus d) (hX : ∀ j, Measurable (X j)) (N J : ℕ)
    (Mp δp : ℝ) :
    MeasurableSet {ω | ¬ ∀ τ : ℝ, 2 ≤ τ → 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1 →
        |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|
          ≤ kernelC1 d * δp * Real.sqrt J + 4 * Mp / (N : ℝ) ^ 2} := by
  refine MeasurableSet.compl ?_
  refine forall_param_measurable (p := fun τ : ℝ => 2 ≤ τ)
    (q := fun τ : ℝ => 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1)
    (h := fun ω τ => |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d σ τ - 1|)
    (c := kernelC1 d * δp * Real.sqrt J + 4 * Mp / (N : ℝ) ^ 2) ?_ ?_
  · intro τ
    exact ((((heat_trace_sample_measurable hσ d X hX N τ).sub measurable_const).div_const _).sub
      measurable_const).abs
  · intro ω
    have hH : (symGraph
        (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
        (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian := by
      refine symGraph_isHermitian _ _ fun i j => ?_
      rw [← heatTorus_even d (2 * Real.pi ^ 2 * σ) (X j ω - X i ω), neg_sub]
    have hF := (trace_exp_continuous _ hH).continuousOn
      (s := {τ : ℝ | 2 ≤ τ ∧ 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1})
    have hE : ContinuousOn (fun τ : ℝ => (N : ℝ) * Real.exp (-τ))
        {τ : ℝ | 2 ≤ τ ∧ 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1} := by
      have : Continuous fun τ : ℝ => (N : ℝ) * Real.exp (-τ) := by fun_prop
      exact this.continuousOn
    have hT : ContinuousOn (fun τ : ℝ => poissonMean d σ τ)
        {τ : ℝ | 2 ≤ τ ∧ 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1} := by
      refine (poissonMean_continuousOn hσ d (((J : ℝ) + 1 - 2 * Real.log N) / 3)).mono ?_
      intro τ hτ
      have h1 : (2 : ℝ) ≤ τ := hτ.1
      have h2 : 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1 := hτ.2
      exact ⟨by linarith, by linarith⟩
    have hT0 : ∀ τ ∈ {τ : ℝ | 2 ≤ τ ∧ 3 * τ + 2 * Real.log N ≤ (J : ℝ) + 1},
        poissonMean d σ τ ≠ 0 := by
      intro τ hτ
      have h1 : (2 : ℝ) ≤ τ := hτ.1
      have h2 := poissonMean_ge hσ d (τ := τ) (by linarith)
      have h3 := exp_neg_le_quarter h1
      linarith
    exact (((hF.sub hE).div hT hT0).sub continuousOn_const).abs

end AssembledSets

/-! ## Almost sure versions (Borel–Cantelli) of the kernel, trace and eigenvalue statements.
The regime (smallness) condition is a HYPOTHESIS, required eventually in `N`. -/

namespace AlmostSure

open Filter Topology
open CTG.Reals.TraceG29 CTG.Reals.Assembled

/-- Borel–Cantelli for probabilities of order `N⁻³`: if `P(B_N) ≤ C/N³` for all large `N`, then
    almost surely `B_N` occurs for only finitely many `N`. (Outer measure; no measurability.) -/
theorem ae_eventually_of_cube_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (B : ℕ → Set Ω) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ᶠ N : ℕ in atTop, μ.real (B N) ≤ C / (N : ℝ) ^ 3) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ω ∉ B N := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hB
  have hsum : Summable (fun N : ℕ => C / (N : ℝ) ^ 3) := by
    have h1 : Summable (fun N : ℕ => ((N : ℝ) ^ 3)⁻¹) :=
      Real.summable_nat_pow_inv.mpr (by norm_num)
    simpa [div_eq_mul_inv] using h1.mul_left C
  have hnn : ∀ N : ℕ, 0 ≤ C / (N : ℝ) ^ 3 := fun N => by positivity
  have key : ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, ω ∉ (if N0 ≤ N then B N else (∅ : Set Ω)) := by
    apply ae_eventually_notMem
    have hle : ∀ N, μ (if N0 ≤ N then B N else (∅ : Set Ω))
        ≤ ENNReal.ofReal (C / (N : ℝ) ^ 3) := by
      intro N
      by_cases h : N0 ≤ N
      · rw [if_pos h, ← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (hN0 N h)
      · rw [if_neg h]; simp
    have hfin : ∑' N : ℕ, ENNReal.ofReal (C / (N : ℝ) ^ 3) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum hle)
  filter_upwards [key] with ω hω
  filter_upwards [hω, eventually_ge_atTop N0] with N hN hge
  rwa [if_pos hge] at hN

/-- The same for a family of properties: if `P(not P_N) ≤ C/N³` for all large `N`, then almost
    surely `P_N` holds for all large `N`. -/
theorem ae_eventually_of_cube {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (P : ℕ → Ω → Prop) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ᶠ N : ℕ in atTop, μ.real {ω | ¬ P N ω} ≤ C / (N : ℝ) ^ 3) :
    ∀ᵐ ω ∂μ, ∀ᶠ N in atTop, P N ω := by
  filter_upwards [ae_eventually_of_cube_bound (μ := μ) (fun N => {ω | ¬ P N ω}) hC hB] with ω hω
  filter_upwards [hω] with N hN
  exact Classical.not_not.mp hN

/-- **Kernel estimate, almost surely for all large `N`.** Independent uniform points on the flat
    torus of dimension `d ≥ 1`; kernel variance `σ_N` and step range `K_N` may depend on `N`.
    HYPOTHESIS (the regime condition, NOT derived here): for all large `N`, `0 < σ_N ≤ 1`,
    `K_N ≥ 1` and `C₁ δ'_N √K_N ≤ 1` with `δ'_N = √(M_N log N / N)`, `M_N = p_{σ_N}(0)`.
    Then almost surely, for all large `N`, for all `1 ≤ k ≤ K_N` and all entries,
    `|N P^k(a,i) - p_{kσ_N}(x_a - x_i)| ≤ C₁ δ'_N √k m_k`. -/
theorem kernel_theorem_G28_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) (K : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hK : ∀ᶠ N in atTop, 0 < K N)
    (hrange : ∀ᶠ N : ℕ in atTop, kernelC1 d
        * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
        * Real.sqrt (K N) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K N → ∀ a i : Fin N,
        |(N : ℝ) * ((walkMatrix
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a)) ^ k) a i
            - heatP d (σ N) k (X a ω - X i ω)|
          ≤ kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
            * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0 := by
  apply ae_eventually_of_cube (μ := μ) _ (C := 3) (by norm_num)
  filter_upwards [hσ, hK, hrange, eventually_ge_atTop 2] with N h1 h2 h3 h4
  exact kernel_theorem_G28 h1.1 h1.2 d hd X h_indep hX hlaw N (K N) h4 h2 rfl rfl h3

/-- **Subtracted heat trace, relative form, almost surely for all large `N`.** Parameters `σ_N`,
    `J_N` may depend on `N`. HYPOTHESIS (regime condition, NOT derived here): for all large `N`,
    `0 < σ_N ≤ 1`, `J_N ≥ 2` and `C₁ δ'_N √J_N ≤ 1`. Then almost surely, for all large `N`, for
    ALL `τ ≥ 2` with `3τ + 2 log N ≤ J_N + 1` (this range of `τ` is EMPTY, and the statement says
    nothing, unless `J_N ≥ 5 + 2 log N`; in particular for a fixed `J`):
    `|(Tr exp(τ(S-1)) - N e^{-τ}) / T(τ) - 1| ≤ C₁ δ'_N √J_N + 4 M_N / N²`. -/
theorem heat_trace_G29_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) (J : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hJ : ∀ᶠ N in atTop, 2 ≤ J N)
    (hrange : ∀ᶠ N : ℕ in atTop, kernelC1 d
        * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
        * Real.sqrt (J N) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop,
      ∀ τ : ℝ, 2 ≤ τ → 3 * τ + 2 * Real.log N ≤ (J N : ℝ) + 1 →
        |((NormedSpace.exp (τ • (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X a ω - X j ω))
              (fun a : Fin N => heatRho d (σ N) N (fun j => X j ω) a) - 1))).trace
            - (N : ℝ) * Real.exp (-τ)) / poissonMean d (σ N) τ - 1|
          ≤ kernelC1 d * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
              * Real.sqrt (J N)
            + 4 * heatTorus d (2 * Real.pi ^ 2 * σ N) 0 / (N : ℝ) ^ 2 := by
  apply ae_eventually_of_cube (μ := μ) _ (C := 3) (by norm_num)
  filter_upwards [hσ, hJ, hrange, eventually_ge_atTop 2] with N h1 h2 h3 h4
  exact heat_trace_G29_uniform h1.1 h1.2 d hd X h_indep hX hlaw N (J N) h4 h2 rfl rfl h3

/-- **Eigenvalues, part (i), almost surely for all large `N`.** Parameters `σ_N`, `K_N` may
    depend on `N`. HYPOTHESIS (regime condition, NOT derived here): for all large `N`,
    `0 < σ_N ≤ 1`, `K_N ≥ 1` and `C₁ δ'_N √K_N ≤ 1`. Then almost surely, for all large `N`, for
    all `1 ≤ k ≤ K_N` and all indices `j` (counted from zero): `s_0 = 1`, and for `j ≥ 1`, with
    `q = shellIndex d j`, `|s_j^k - e^{-k 2π²σ_N q}| ≤ C₃ δ'_N √k m_k`. -/
theorem eig_theorem_G38_i_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (σ : ℕ → ℝ) (K : ℕ → ℕ)
    (hσ : ∀ᶠ N in atTop, 0 < σ N ∧ σ N ≤ 1) (hK : ∀ᶠ N in atTop, 0 < K N)
    (hrange : ∀ᶠ N : ℕ in atTop, kernelC1 d
        * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
        * Real.sqrt (K N) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ᶠ N : ℕ in atTop, ∀ k, 1 ≤ k → k ≤ K N →
        ∀ (hS : (symGraph
            (fun i j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ N) (X i ω - X j ω))
            (fun i : Fin N =>
              (∑ l : Fin N, heatTorus d (2 * Real.pi ^ 2 * σ N) (X i ω - X l ω)) / N)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → hS.eigenvalues₀ j = 1)
          ∧ (1 ≤ j.val →
            |hS.eigenvalues₀ j ^ k
                - Real.exp (-(2 * Real.pi ^ 2 * σ N) * (shellIndex d j.val : ℝ)) ^ k|
              ≤ eigC3 d
                * Real.sqrt (heatTorus d (2 * Real.pi ^ 2 * σ N) 0 * Real.log N / N)
                * Real.sqrt k * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ N)) 0) := by
  apply ae_eventually_of_cube (μ := μ) _ (C := 6) (by norm_num)
  filter_upwards [hσ, hK, hrange, eventually_ge_atTop 2] with N h1 h2 h3 h4
  haveI : NeZero N := ⟨by omega⟩
  exact eig_theorem_G38_i_all_shell h1.1 h1.2 d N (K N) hd X h_indep hX hlaw h4 h2 rfl rfl h3

end AlmostSure

namespace KernelMatrix

open CTG.Reals.TorusReduction TorusReductionL1

/-! ## New material (A16): the spectrum of the kernel matrix `Q_k` itself -/

/-- The ordered eigenvalues depend only on the matrix. -/
theorem eig_congr {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℝ} (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (j : Fin (Fintype.card n)) :
    hA.eigenvalues₀ j = hB.eigenvalues₀ j := by
  subst h; rfl

/-- A symmetric matrix with nonnegative quadratic form has nonnegative ordered eigenvalues. -/
theorem psd_eigenvalues₀_nonneg {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (hA : A.IsHermitian) (hpsd : ∀ y : n → ℝ, 0 ≤ ∑ i, ∑ j, y i * y j * A i j)
    (j : Fin (Fintype.card n)) : 0 ≤ hA.eigenvalues₀ j := by
  have hps : A.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg hA fun y => ?_
    have e : star y ⬝ᵥ (A *ᵥ y) = ∑ i, ∑ l, y i * y l * A i l := by
      simp only [dotProduct, mulVec, star_trivial, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact hpsd _
  have h := hps.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  simpa [IsHermitian.eigenvalues] using h

/-- The coefficients of the modes are at most one. -/
theorem modeCoeff_le_one (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (f : Option ((Fin d → ℤ) × Bool)) :
    modeCoeff d c f ≤ 1 := by
  rcases f with _ | ⟨n, b⟩
  · simp [modeCoeff]
  · simp only [modeCoeff]
    apply Real.exp_le_one_iff.mpr
    have h1 : 0 ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2 := Finset.sum_nonneg fun i _ => _root_.sq_nonneg _
    nlinarith

theorem abs_div_sub_le {p y N t : ℝ} (hN : 0 < N) (h : |p - N * y| ≤ t) :
    |p / N - y| ≤ t / N := by
  have hN' : N ≠ 0 := hN.ne'
  have e : p / N - y = (p - N * y) / N := by field_simp
  rw [e, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right h hN.le

set_option maxHeartbeats 3200000 in
/-- **Target (1), general form: the kernel matrix alone, deterministic on a Gram event.**
    Points `x_1..x_N` on the flat torus, `Q = (p_c(x_a - x_i)/N)` with `p_c = heatTorus d c`,
    `H` a half set of frequencies with cut-off `R`, HYPOTHESIS `hgram`: the Gram matrix of the sampled
    modes of `H` is within `eta` of the identity. No kernel-theorem input, no normalisation.
    Conclusions for the `j`-th ordered eigenvalue `μ_j` of `Q` (decreasing order, from `0`):
    `μ_j ≥ 0`; if `α > 0` is the `j`-th largest mode coefficient (two counts), then
    `|μ_j - α| ≤ t + eta Σ_g √a_g` (`t` = Fourier tail); beyond the number of modes, `μ_j ≤` the same. -/
theorem kernelQ_eig_det {c : ℝ} (hc : 0 < c) (d N : ℕ) [NeZero N] (x : Fin N → FlatTorus d)
    (H : Finset (Fin d → ℤ)) (hH0 : ∀ n ∈ H, n ≠ 0) (hH2 : ∀ m ∈ H, ∀ n ∈ H, m + n ≠ 0)
    {R eta t : ℝ}
    (hR : ∀ n : Fin d → ℤ, n ≠ 0 → n ∉ H → -n ∉ H → R ≤ ∑ i, ((n i : ℤ) : ℝ) ^ 2)
    (heta : 0 ≤ eta)
    (hgram : ∀ f g : modeSet d H, |∑ i, torusMode d f.1 (x i) * torusMode d g.1 (x i)
        - N * (if f = g then (1 : ℝ) else 0)| ≤ N * eta)
    (ht : Real.exp (-c * R / 2) * (1 + Real.sqrt (2 * Real.pi / c)) ^ d ≤ t)
    (hQ : (Matrix.of fun a i : Fin N => heatTorus d c (x a - x i) / (N : ℝ)).IsHermitian)
    (j : Fin (Fintype.card (Fin N))) :
    0 ≤ hQ.eigenvalues₀ j
      ∧ (∀ α : ℝ, 0 < α →
          (Finset.univ.filter fun f : modeSet d H => α < modeCoeff d c f.1).card ≤ j.val →
          j.val < (Finset.univ.filter fun f : modeSet d H => α ≤ modeCoeff d c f.1).card →
          |hQ.eigenvalues₀ j - α|
            ≤ t + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d c g.1))
      ∧ (Fintype.card (modeSet d H) ≤ j.val →
          hQ.eigenvalues₀ j
            ≤ t + eta * 1 * ∑ g : modeSet d H, Real.sqrt (modeCoeff d c g.1)) := by
  classical
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  set a : modeSet d H → ℝ := fun f => modeCoeff d c f.1 with hadef
  set v : Matrix (Fin N) (modeSet d H) ℝ :=
    Matrix.of fun i f => torusMode d f.1 (x i) / Real.sqrt N with hvdef
  have ha : ∀ f, 0 ≤ a f := fun f => modeCoeff_nonneg d _ f.1
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hsqpos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hs : ∀ f, Real.sqrt (a f) ≤ 1 := fun f => by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (modeCoeff_le_one d hc.le f.1)
  have hG : ∀ f g, |∑ i, v i f * v i g - (if f = g then 1 else 0)| ≤ eta := by
    intro f g
    have e : ∑ i, v i f * v i g - (if f = g then (1 : ℝ) else 0)
        = (∑ i, torusMode d f.1 (x i) * torusMode d g.1 (x i)
            - N * (if f = g then (1 : ℝ) else 0)) / N := by
      simp only [hvdef, of_apply]
      rw [sub_div, Finset.sum_div, mul_div_cancel_left₀ _ hNpos.ne']
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [div_mul_div_comm, hsqN]
    rw [e, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
    linarith [hgram f g]
  have hQ' := gram_hermitian (Matrix.of fun i f => Real.sqrt (a f) * v i f)
  have h1 := pad_hermitian₁ (F := modeSet d H) _ hQ'
  have hD := pad_hermitian₂ (n := Fin N) a
  have htail : ∀ i l, |heatTorus d c (x i - x l) - (N : ℝ) *
      ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
        (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t := by
    intro i l
    rw [finite_rank_kernel_entry v a ha i l]
    have e : (N : ℝ) * ∑ f, a f * v i f * v l f
        = 1 + ∑ n ∈ H, 2 * Real.exp (-c * ∑ i, ((n i : ℤ) : ℝ) ^ 2)
            * (torusChar d n (x i - x l)).re := by
      rw [← modeSet_kernel d c H (x i) (x l),
        ← Finset.sum_coe_sort (modeSet d H), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      simp only [hvdef, hadef, of_apply]
      field_simp
      rw [Real.sq_sqrt hNpos.le]; ring
    rw [e]
    exact (heatTorus_truncation_half hc d H hH0 hH2 hR _).trans ht
  have hterm : ∀ i l,
      |(Matrix.of fun a' i' : Fin N => heatTorus d c (x a' - x i') / (N : ℝ)) i l
        - ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
          (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t / (N : ℝ) := by
    intro i l
    show |heatTorus d c (x i - x l) / (N : ℝ) - _| ≤ t / (N : ℝ)
    exact abs_div_sub_le hNpos (htail i l)
  have hrow : ∀ i, ∑ l,
      |(Matrix.of fun a' i' : Fin N => heatTorus d c (x a' - x i') / (N : ℝ)) i l
        - ((Matrix.of fun i f => Real.sqrt (a f) * v i f) *
          (Matrix.of fun i f => Real.sqrt (a f) * v i f)ᵀ) i l| ≤ t := by
    intro i
    refine (Finset.sum_le_sum fun l _ => hterm i l).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_div_assoc']
    exact mul_div_cancel_left₀ t hNpos.ne'
  have hw := weyl_row_sums _ _ hQ hQ' hrow j
  have hj : j.val < Fintype.card (Fin N ⊕ modeSet d H) := by
    rw [Fintype.card_sum]; exact lt_of_lt_of_le j.2 (Nat.le_add_right _ _)
  have hsp := finite_rank_kernel_spectrum v a ha heta zero_le_one hs hG hQ' h1 hD j hj
  have hmain : |hQ.eigenvalues₀ j - hD.eigenvalues₀ ⟨j.val, hj⟩|
      ≤ t + eta * 1 * ∑ g, Real.sqrt (a g) := by
    have h1' := abs_le.mp hw
    have h2' := abs_le.mp hsp
    rw [abs_le]; constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]
  have hnn : 0 ≤ hQ.eigenvalues₀ j := by
    refine psd_eigenvalues₀_nonneg _ hQ (fun y => ?_) j
    have e : ∑ i, ∑ l, y i * y l
          * (Matrix.of fun a' i' : Fin N => heatTorus d c (x a' - x i') / (N : ℝ)) i l
        = (∑ i, ∑ l, y i * y l * heatTorus d c (x i - x l)) / N := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun l _ => ?_
      show y i * y l * (heatTorus d c (x i - x l) / (N : ℝ)) = _
      rw [mul_div_assoc]
    rw [e]
    exact div_nonneg (heatTorus_quadform_nonneg hc d x y) hNpos.le
  refine ⟨hnn, ?_, ?_⟩
  · intro α hα hc1 hc2
    have hDj : hD.eigenvalues₀ ⟨j.val, hj⟩ = α :=
      diag_pad_eigenvalue a hD hα ⟨j.val, hj⟩ hc1 hc2
    rw [hDj] at hmain
    exact hmain
  · intro hcardF
    have hz := diag_pad_eigenvalue_nonpos a hD ⟨j.val, hj⟩ hcardF
    have h5 : hQ.eigenvalues₀ j
        ≤ (t + eta * 1 * ∑ g, Real.sqrt (a g)) + hD.eigenvalues₀ ⟨j.val, hj⟩ := by
      linarith [(abs_le.mp hmain).2]
    have h6 : hQ.eigenvalues₀ j ≤ t + eta * 1 * ∑ g, Real.sqrt (a g) := by linarith
    exact h6

/-- The error of the kernel matrix: Fourier tail beyond the cut-off `R` plus the Gram term. -/
noncomputable def kernelQErr (d : ℕ) (σ : ℝ) (k m : ℕ) (η R : ℝ) : ℝ :=
  Real.exp (-((k : ℝ) * (2 * Real.pi ^ 2 * σ)) * R / 2)
      * (1 + Real.sqrt (2 * Real.pi / ((k : ℝ) * (2 * Real.pi ^ 2 * σ)))) ^ d
    + η * 1 * ∑ g : modeSet d (halfFreq d m R),
        Real.sqrt (modeCoeff d ((k : ℝ) * (2 * Real.pi ^ 2 * σ)) g.1)

set_option maxHeartbeats 3200000 in
/-- **Target (1): `lem:kernelmatrix` in the file's form, deterministic on a Gram event, all shells.**
    `Q_k = (p_{kσ}(x_a - x_i)/N)`, `H = halfFreq d m R`. HYPOTHESIS `hgram` (Gram event). For every
    `k ≥ 1` and every index `j` (from `0`): `μ_j(Q_k) ≥ 0`, `|μ_0(Q_k) - 1| ≤ err`, and for every
    shell `|n|² = r > 0` (below or above the cut-off) and every index `j` of the shell
    `|μ_j(Q_k) - e^{-k 2π²σ r}| ≤ err`, `err = kernelQErr` (tail + `η Σ_g √a_g`). -/
theorem kernelQ_eig_shell {σ η R : ℝ} (hσ : 0 < σ) (d N m : ℕ) [NeZero N]
    (x : ℕ → FlatTorus d) (hRm : R ≤ (m : ℝ) ^ 2) (hR0 : 0 ≤ R) (hη0 : 0 ≤ η)
    (hgram : ∀ f g : modeSet d (halfFreq d m R),
      |∑ i : Fin N, torusMode d f.1 (x i) * torusMode d g.1 (x i)
        - N * (if f = g then (1 : ℝ) else 0)| ≤ N * η)
    (k : ℕ) (hk1 : 1 ≤ k)
    (hQ : (Matrix.of fun a i : Fin N => heatP d σ k (x a - x i) / (N : ℝ)).IsHermitian)
    (j : Fin (Fintype.card (Fin N))) :
    0 ≤ hQ.eigenvalues₀ j
      ∧ (j.val = 0 → |hQ.eigenvalues₀ j - 1| ≤ kernelQErr d σ k m η R)
      ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
          |hQ.eigenvalues₀ j - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
            ≤ kernelQErr d σ k m η R := by
  have hpi := Real.pi_pos
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  obtain ⟨ck, hck⟩ : ∃ ck : ℝ, ck = (k : ℝ) * (2 * Real.pi ^ 2 * σ) := ⟨_, rfl⟩
  have hck0 : 0 < ck := by rw [hck]; positivity
  have hpow : ∀ r : ℝ, Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k = Real.exp (-ck * r) := by
    intro r
    rw [← Real.exp_nat_mul, hck]; congr 1; ring
  have eck : 2 * Real.pi ^ 2 * ((k : ℝ) * σ) = ck := by rw [hck]; ring
  have hmat : (Matrix.of fun a i : Fin N => heatP d σ k (x a - x i) / (N : ℝ))
      = Matrix.of fun a i : Fin N => heatTorus d ck (x a - x i) / (N : ℝ) := by
    ext a i
    simp only [Matrix.of_apply]
    rw [heatP_of_ne d σ (by omega), eck]
  have hQ' : (Matrix.of fun a i : Fin N => heatTorus d ck (x a - x i) / (N : ℝ)).IsHermitian := by
    rw [← hmat]; exact hQ
  rw [eig_congr hmat hQ hQ' j]
  obtain ⟨p1, p2, p3, p4⟩ := halfFreq_props d m hRm
  obtain ⟨g1, g3, g4⟩ := kernelQ_eig_det hck0 d N (fun i : Fin N => x i) (halfFreq d m R) p1 p2 p3
    hη0 hgram le_rfl hQ' j
  have hE : kernelQErr d σ k m η R
      = Real.exp (-ck * R / 2) * (1 + Real.sqrt (2 * Real.pi / ck)) ^ d
        + η * 1 * ∑ g : modeSet d (halfFreq d m R), Real.sqrt (modeCoeff d ck g.1) := by
    unfold kernelQErr; rw [hck]
  rw [hE]
  refine ⟨g1, ?_, ?_⟩
  · intro hj0
    have hnone : (none : Option ((Fin d → ℤ) × Bool)) ∈ modeSet d (halfFreq d m R) := by
      unfold modeSet; simp
    have hc0 : (Finset.univ.filter fun f : modeSet d (halfFreq d m R) =>
        (1 : ℝ) < modeCoeff d ck f.1).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro f _
      exact not_lt.mpr (modeCoeff_le_one d hck0.le f.1)
    have hpos : 0 < (Finset.univ.filter fun f : modeSet d (halfFreq d m R) =>
        (1 : ℝ) ≤ modeCoeff d ck f.1).card := by
      rw [Finset.card_pos]
      exact ⟨⟨none, hnone⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [modeCoeff]⟩⟩
    exact g3 1 one_pos (by rw [hc0]; exact Nat.zero_le _) (by rw [hj0]; exact hpos)
  · intro r hr Hlt Hle hlt hle hj1 hj2
    rw [hpow r]
    by_cases hrR : r < R
    · have hflt : (halfFreq d m R).filter (fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) = Hlt := by
        ext n
        rw [Finset.mem_filter, mem_halfFreq hRm, hlt]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
      have hfle : (halfFreq d m R).filter (fun n => ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) = Hle := by
        ext n
        rw [Finset.mem_filter, mem_halfFreq hRm, hle]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith⟩, h3⟩
      obtain ⟨c1, c2⟩ := mode_counts_general d hck0 hr (halfFreq d m R)
      rw [hflt] at c1
      rw [hfle] at c2
      exact g3 (Real.exp (-ck * r)) (Real.exp_pos _) (c1.trans hj1)
        (lt_of_lt_of_le (by omega) c2)
    · have hRr : R ≤ r := not_lt.mp hrR
      have hsub : halfFreq d m R ⊆ Hlt := by
        intro n hn
        rw [mem_halfFreq hRm] at hn
        rw [hlt]; exact ⟨hn.1, lt_of_lt_of_le hn.2 hRr⟩
      have hcd := Finset.card_le_card hsub
      have hmc := modeSet_card_le d (halfFreq d m R)
      have hs := g4 (by omega)
      have hSig : 0 ≤ η * 1 * ∑ g : modeSet d (halfFreq d m R),
          Real.sqrt (modeCoeff d ck g.1) :=
        mul_nonneg (mul_nonneg hη0 zero_le_one) (Finset.sum_nonneg fun g _ => Real.sqrt_nonneg _)
      have hα : Real.exp (-ck * r) ≤ Real.exp (-ck * R / 2) := by
        apply Real.exp_le_exp.mpr
        have h1 : ck * R ≤ ck * r := mul_le_mul_of_nonneg_left hRr hck0.le
        have h2 : 0 ≤ ck * R := mul_nonneg hck0.le hR0
        linarith
      have hpw : 1 ≤ (1 + Real.sqrt (2 * Real.pi / ck)) ^ d :=
        one_le_pow₀ (by linarith [Real.sqrt_nonneg (2 * Real.pi / ck)])
      have hT : Real.exp (-ck * r)
          ≤ Real.exp (-ck * R / 2) * (1 + Real.sqrt (2 * Real.pi / ck)) ^ d :=
        hα.trans (le_mul_of_one_le_right (Real.exp_pos _).le hpw)
      have hαpos := Real.exp_pos (-ck * r)
      rw [abs_le]
      constructor <;> linarith

/-- The constant of the kernel-matrix bound; it depends only on `d`. -/
noncomputable def kernelQC (d : ℕ) : ℝ :=
  (2 + Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) * (1 + 2 * Real.sqrt 2 ^ d))
    * (1 + Real.sqrt (2 * Real.pi)) ^ d

set_option maxHeartbeats 6400000 in
/-- **Target (2): `lem:kernelmatrix` for random samples, in the file's form.** Independent uniform
    points on the flat torus of dimension `d`, `Q_k = (p_{kσ}(x_a - x_i)/N)` (kernel of variance
    `kσ`), `N ≥ 12`, `2^d ≤ N`, `1/σ ≤ 8N²`. Except on an event of probability at most `2/N³` (the
    Gram event of the modes of `halfFreq d m R`, `R = log(2^d N)/(2π²σ)`, `m = ⌈√R⌉`), for ALL `k ≥ 1`
    and all `j`: `μ_j(Q_k) ≥ 0`, `|μ_0(Q_k) - 1| ≤ B_k`, and for every shell `|n|² = r > 0` and every
    index `j` of the shell (from zero) `|μ_j(Q_k) - e^{-k 2π²σ r}| ≤ B_k`,
    `B_k = kernelQC d · √(log N/N) · m_k`, `m_k = p_{kσ}(0)`. -/
theorem kernelQ_sample {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d N : ℕ) [NeZero N]
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N)
    (h2d : (2 : ℝ) ^ d ≤ N) (h1σ : 1 / σ ≤ 8 * (N : ℝ) ^ 2) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k →
        ∀ (hQ : (Matrix.of fun a i : Fin N =>
              heatP d σ k (X a ω - X i ω) / (N : ℝ)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          0 ≤ hQ.eigenvalues₀ j
          ∧ (j.val = 0 → |hQ.eigenvalues₀ j - 1|
              ≤ kernelQC d * Real.sqrt (Real.log N / N)
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
          ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            |hQ.eigenvalues₀ j - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ kernelQC d * Real.sqrt (Real.log N / N)
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ≤ 2 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr12 : (12 : ℝ) ≤ N := by exact_mod_cast hN12
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 + Real.sqrt (2 * Real.pi)) ^ d := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hA]; exact one_le_pow₀ (by linarith [Real.sqrt_nonneg (2 * Real.pi)])
  have hA0 : 0 ≤ A := by linarith
  have hlg1 : (1 : ℝ) ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNpos]
    have := exp_one_le_four
    linarith
  obtain ⟨δ0, hδ0d⟩ : ∃ δ0 : ℝ, δ0 = Real.sqrt (Real.log N / N) := ⟨_, rfl⟩
  have hδ00 : 0 ≤ δ0 := by rw [hδ0d]; exact Real.sqrt_nonneg _
  have hδ0' : δ0 = Real.sqrt (1 * Real.log N / N) := by rw [one_mul]; exact hδ0d
  have hlN0 : 0 ≤ Real.log N / N := div_nonneg (by linarith) hNpos.le
  have hδ02 : δ0 ^ 2 = Real.log N / N := by rw [hδ0d, Real.sq_sqrt hlN0]
  have hδN : 1 / (N : ℝ) ≤ δ0 := by
    have h1 : (1 / (N : ℝ)) ^ 2 ≤ Real.log N / N := by
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) hNpos]
      have hN2nn : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
      have ha := mul_le_mul_of_nonneg_right hlg1 hN2nn
      have hb := mul_nonneg hNpos.le (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1)
      linarith
    calc 1 / (N : ℝ) = Real.sqrt ((1 / (N : ℝ)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.log N / N) := Real.sqrt_le_sqrt h1
      _ = δ0 := hδ0d.symm
  obtain ⟨hR0, hRm, hF, -, -⟩ := g38_cutoff hσ d N hN12 h1σ h2d hδN
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = Real.log (2 ^ d * (N : ℝ)) / (2 * Real.pi ^ 2 * σ) := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = Nat.ceil (Real.sqrt R) := ⟨_, rfl⟩
  rw [← hRdef] at hR0 hRm hF
  rw [← hmdef] at hRm hF
  -- the Gram tolerance
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) * δ0 :=
    ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hηdef]; exact mul_nonneg (Real.sqrt_nonneg _) hδ00
  obtain ⟨q1, q2, q3, q4⟩ := halfFreq_props d m hRm
  have hcard : Fintype.card (modeSet d (halfFreq d m R)) ≤ N ^ (3 * d + 1) :=
    (modeSet_card_le d (halfFreq d m R)).trans
      ((Nat.add_le_add_left (Nat.mul_le_mul_left 2 q4) 1).trans hF)
  have hgc := gram_choice hN2 hcard (le_refl (1 : ℝ)) hδ0'
  rw [← hηdef] at hgc
  -- the bound of the error
  have hbound : ∀ k : ℕ, 1 ≤ k →
      kernelQErr d σ k m η R
        ≤ kernelQC d * Real.sqrt (Real.log N / N)
          * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := by
    intro k hk1
    have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    obtain ⟨s2, hs2⟩ : ∃ s2 : ℝ, s2 = Real.sqrt 2 := ⟨_, rfl⟩
    have hs21 : 1 ≤ s2 := by
      rw [hs2, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs20 : 0 ≤ s2 := by linarith
    have hs2s : s2 * s2 = 2 := by rw [hs2]; exact Real.mul_self_sqrt (by norm_num)
    have hW0 : 0 ≤ s2 ^ d := pow_nonneg hs20 d
    have hWW : s2 ^ d * s2 ^ d = 2 ^ d := by rw [← mul_pow, hs2s]
    have hsq2 : ∀ z : ℝ, Real.sqrt (2 * z) = s2 * Real.sqrt z := fun z => by
      rw [hs2]; exact Real.sqrt_mul (by norm_num) z
    obtain ⟨mk, hmk⟩ : ∃ mk : ℝ, mk = heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := ⟨_, rfl⟩
    have hmk1 : 1 ≤ mk := by rw [hmk]; exact heatTorus_zero_ge_one (by positivity) d
    have hmuA0 : (1 + Real.sqrt (Real.pi / ((k : ℝ) * (2 * Real.pi ^ 2 * σ)))) ^ d ≤ A * mk := by
      have h := heatMu_le_m_all hσ d k hk1
      unfold heatMu heatM at h
      rw [if_neg (by omega)] at h
      rw [hA, hmk, show (k : ℝ) * (2 * Real.pi ^ 2 * σ) = 2 * Real.pi ^ 2 * ((k : ℝ) * σ) by ring]
      exact h
    have hSg0 : 0 ≤ ∑ g : modeSet d (halfFreq d m R),
        Real.sqrt (modeCoeff d ((k : ℝ) * (2 * Real.pi ^ 2 * σ)) g.1) :=
      Finset.sum_nonneg fun g _ => Real.sqrt_nonneg _
    have hSg1 := mode_sqrt_sum_le d (c := (k : ℝ) * (2 * Real.pi ^ 2 * σ)) (by positivity)
      (halfFreq d m R)
    have hle1 : (2 * Real.pi ^ 2 * σ) * R ≤ (k : ℝ) * (2 * Real.pi ^ 2 * σ) * R := by
      have h1 : (1 : ℝ) * ((2 * Real.pi ^ 2 * σ) * R) ≤ (k : ℝ) * ((2 * Real.pi ^ 2 * σ) * R) :=
        mul_le_mul_of_nonneg_right hk1r (by positivity)
      linarith
    obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.exp (-(2 * Real.pi ^ 2 * σ) * R / 2) := ⟨_, rfl⟩
    have hu0 : 0 ≤ u := by rw [hu]; exact (Real.exp_pos _).le
    have huu : u * u = 1 / (2 ^ d * (N : ℝ)) := by
      rw [hu, ← Real.exp_add, hRdef]
      have e0 : (2 * Real.pi ^ 2 * σ) * (Real.log (2 ^ d * (N : ℝ)) / (2 * Real.pi ^ 2 * σ))
          = Real.log (2 ^ d * (N : ℝ)) := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hcσ.ne']
      have e : -(2 * Real.pi ^ 2 * σ) * (Real.log (2 ^ d * (N : ℝ)) / (2 * Real.pi ^ 2 * σ)) / 2
          + -(2 * Real.pi ^ 2 * σ) * (Real.log (2 ^ d * (N : ℝ)) / (2 * Real.pi ^ 2 * σ)) / 2
          = -((2 * Real.pi ^ 2 * σ) * (Real.log (2 ^ d * (N : ℝ)) / (2 * Real.pi ^ 2 * σ))) := by
        ring
      rw [e, e0, Real.exp_neg, Real.exp_log (by positivity), one_div]
    have huW : u * s2 ^ d ≤ 2 * δ0 := by
      by_contra hcon
      have hlt : 2 * δ0 < u * s2 ^ d := lt_of_not_ge hcon
      have h1 : (2 * δ0) * (2 * δ0) < (u * s2 ^ d) * (u * s2 ^ d) :=
        mul_self_lt_mul_self (by positivity) hlt
      have h2 : (u * s2 ^ d) * (u * s2 ^ d) = 1 / (N : ℝ) := by
        have e : (u * s2 ^ d) * (u * s2 ^ d) = (u * u) * (s2 ^ d * s2 ^ d) := by ring
        rw [e, huu, hWW, div_mul_eq_mul_div, one_mul,
          div_eq_div_iff (by positivity) (by positivity)]
        ring
      have h3 : 1 / (N : ℝ) ≤ (2 * δ0) * (2 * δ0) := by
        have e : (2 * δ0) * (2 * δ0) = 4 * Real.log N / N := by
          have : (2 * δ0) * (2 * δ0) = 4 * δ0 ^ 2 := by ring
          rw [this, hδ02]; ring
        rw [e]
        exact div_le_div_of_nonneg_right (by linarith) hNpos.le
      linarith
    obtain ⟨ck, hck⟩ : ∃ ck : ℝ, ck = (k : ℝ) * (2 * Real.pi ^ 2 * σ) := ⟨_, rfl⟩
    have hck0 : 0 < ck := by rw [hck]; positivity
    rw [← hck] at hmuA0 hSg1 hSg0 hle1
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt (Real.pi / ck) := ⟨_, rfl⟩
    have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
    rw [← hy] at hmuA0
    have hY0 : 0 ≤ (1 + y) ^ d := pow_nonneg (by linarith) d
    have hmu1 : 1 ≤ (1 + y) ^ d := one_le_pow₀ (by linarith)
    have hbig : (1 + s2 * y) ^ d ≤ s2 ^ d * (1 + y) ^ d := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : s2 * (1 + y) = s2 + s2 * y := by ring
      linarith
    have hT : Real.exp (-ck * R / 2) * (1 + Real.sqrt (2 * Real.pi / ck)) ^ d
        ≤ 2 * δ0 * (1 + y) ^ d := by
      have e1 : 2 * Real.pi / ck = 2 * (Real.pi / ck) := by ring
      rw [e1, hsq2, ← hy]
      have hle : Real.exp (-ck * R / 2) ≤ u := by
        rw [hu]; apply Real.exp_le_exp.mpr
        linarith
      calc Real.exp (-ck * R / 2) * (1 + s2 * y) ^ d
          ≤ u * (s2 ^ d * (1 + y) ^ d) := mul_le_mul hle hbig (by positivity) hu0
        _ = (u * s2 ^ d) * (1 + y) ^ d := by ring
        _ ≤ 2 * δ0 * (1 + y) ^ d := mul_le_mul_of_nonneg_right huW hY0
    have hSg : ∑ g : modeSet d (halfFreq d m R), Real.sqrt (modeCoeff d ck g.1)
        ≤ (1 + 2 * s2 ^ d) * (1 + y) ^ d := by
      have e1 : Real.pi / (ck / 2) = 2 * (Real.pi / ck) := by
        rw [div_div_eq_mul_div]; ring
      rw [e1, hsq2, ← hy] at hSg1
      have e2 : (1 + 2 * s2 ^ d) * (1 + y) ^ d = (1 + y) ^ d + 2 * (s2 ^ d * (1 + y) ^ d) := by
        ring
      rw [e2]
      linarith
    obtain ⟨c2, hc2⟩ : ∃ c2 : ℝ, c2 = Real.sqrt (8 * (3 + 2 * ((3 * d + 1 : ℕ) : ℝ))) :=
      ⟨_, rfl⟩
    have hc20 : 0 ≤ c2 := by rw [hc2]; exact Real.sqrt_nonneg _
    have hη' : η = c2 * δ0 := by rw [hc2]; exact hηdef
    have hQC : kernelQC d = (2 + c2 * (1 + 2 * s2 ^ d)) * A := by
      unfold kernelQC; rw [hA, hs2, hc2]
    have hfin : Real.exp (-ck * R / 2) * (1 + Real.sqrt (2 * Real.pi / ck)) ^ d
        + η * 1 * ∑ g : modeSet d (halfFreq d m R), Real.sqrt (modeCoeff d ck g.1)
        ≤ kernelQC d * δ0 * mk := by
      obtain ⟨Sg, hSgd⟩ : ∃ Sg : ℝ,
          Sg = ∑ g : modeSet d (halfFreq d m R), Real.sqrt (modeCoeff d ck g.1) := ⟨_, rfl⟩
      rw [← hSgd] at hSg hSg0 ⊢
      obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (1 + y) ^ d := ⟨_, rfl⟩
      rw [← hY] at hT hSg hmuA0 hY0
      obtain ⟨T, hTd⟩ : ∃ T : ℝ,
          T = Real.exp (-ck * R / 2) * (1 + Real.sqrt (2 * Real.pi / ck)) ^ d := ⟨_, rfl⟩
      rw [← hTd] at hT ⊢
      have hcW : 0 ≤ c2 * s2 ^ d := mul_nonneg hc20 hW0
      have t1 : η * Sg ≤ c2 * δ0 * ((1 + 2 * s2 ^ d) * Y) := by
        rw [hη']; exact mul_le_mul_of_nonneg_left hSg (mul_nonneg hc20 hδ00)
      have hco : 0 ≤ (2 + c2 * (1 + 2 * s2 ^ d)) * δ0 :=
        mul_nonneg (by linarith) hδ00
      have t2 : (2 + c2 * (1 + 2 * s2 ^ d)) * δ0 * Y
          ≤ (2 + c2 * (1 + 2 * s2 ^ d)) * δ0 * (A * mk) :=
        mul_le_mul_of_nonneg_left hmuA0 hco
      rw [hQC]
      have e6 : η * 1 * Sg = η * Sg := by ring
      rw [e6]
      linarith
    unfold kernelQErr
    rw [hck, hmk, hδ0d] at hfin
    exact hfin
  -- the Gram event
  obtain ⟨Bg, hBgd⟩ : ∃ Bg : Set Ω, Bg = {ω | ∃ f g : modeSet d (halfFreq d m R),
      N * η ≤ |∑ j ∈ Finset.range N,
      torusMode d f.1 (X j ω) * torusMode d g.1 (X j ω)
      - N * (if f = g then (1 : ℝ) else 0)|} := ⟨_, rfl⟩
  have hBg : μ.real Bg ≤ 2 / (N : ℝ) ^ 3 := by
    rw [hBgd]
    exact (flatTorus_gram_whp (μ := μ) d X h_indep hX hlaw (modeSet d (halfFreq d m R))
      (fun n b h => q1 n ((mem_modeSet d _ n b).mp h))
      (fun n b n' b' h h' => q2 n ((mem_modeSet d _ n b).mp h) n' ((mem_modeSet d _ n' b').mp h'))
      N (ε := N * η) (mul_nonneg (Nat.cast_nonneg N) hη0)).trans hgc
  refine le_trans (measureReal_mono (s₂ := Bg) ?_ (measure_ne_top μ _)) hBg
  intro ω hω
  by_contra hgm
  rw [hBgd] at hgm
  apply hω
  intro k hk1 hQ j
  have hgramω : ∀ f g' : modeSet d (halfFreq d m R),
      |∑ i : Fin N, torusMode d f.1 (X i ω) * torusMode d g'.1 (X i ω)
        - N * (if f = g' then (1 : ℝ) else 0)| ≤ N * η := by
    intro f g'
    have h : |∑ j ∈ Finset.range N, torusMode d f.1 (X j ω) * torusMode d g'.1 (X j ω)
        - N * (if f = g' then (1 : ℝ) else 0)| < N * η := by
      by_contra h; exact hgm ⟨f, g', not_lt.mp h⟩
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => torusMode d f.1 (X j ω) * torusMode d g'.1 (X j ω)) N] at h
    exact h.le
  obtain ⟨key0, key1, key2⟩ := kernelQ_eig_shell hσ d N m (fun j => X j ω) hRm hR0 hη0
    hgramω k hk1 hQ j
  exact ⟨key0, fun hj0 => (key1 hj0).trans (hbound k hk1),
    fun r hr Hlt Hle hlt hle hj1 hj2 =>
      (key2 r hr Hlt Hle hlt hle hj1 hj2).trans (hbound k hk1)⟩

/-- **Target (3), conditional form.** HYPOTHESIS `hL1`: the conclusion of `eig_l1_sample`
    (eigenvalues of `S^k` against those of the kernel matrix, with a constant `C` and exceptional
    probability `3/N³`). Then, except on an event of probability at most `5/N³`, for all `1 ≤ k ≤ K`,
    all shells and shell indices: `|s_j^k - e^{-k 2π²σ r}| ≤ C δ' √k + kernelQC d √(log N/N) m_k`;
    for `j = 0` the same with `1` in place of the exponential. -/
theorem eig_G44_i_cond {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d N K : ℕ)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (hN12 : 12 ≤ N)
    (h2d : (2 : ℝ) ^ d ≤ N) (h1σ : 1 / σ ≤ 8 * (N : ℝ) ^ 2) {C δp : ℝ}
    (hL1 : μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (hQ : (Matrix.of fun a i : Fin N =>
              heatP d σ k (X a ω - X i ω) / (N : ℝ)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          |hS.eigenvalues₀ j ^ k - hQ.eigenvalues₀ j| ≤ C * δp * Real.sqrt k}
      ≤ 3 / (N : ℝ) ^ 3) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → |hS.eigenvalues₀ j ^ k - 1|
              ≤ C * δp * Real.sqrt k + kernelQC d * Real.sqrt (Real.log N / N)
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
          ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ C * δp * Real.sqrt k + kernelQC d * Real.sqrt (Real.log N / N)
                * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ≤ 5 / (N : ℝ) ^ 3 := by
  haveI : NeZero N := ⟨by omega⟩
  have hQs := kernelQ_sample hσ d N X h_indep hX hlaw hN12 h2d h1σ
  refine EigenvaluesL1.real_le_of_subset2 hL1 hQs ?_ (by ring)
  intro ω hbad
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hg1', hg2'⟩ := hcon
  have hg1 := not_not.mp hg1'
  have hg2 := not_not.mp hg2'
  apply hbad
  intro k hk1 hkK hS j
  have hQ := EigenvaluesL1.kernelQ_isHermitian d σ N k (fun j => X j ω)
  have h1 := hg1 k hk1 hkK hS hQ j
  obtain ⟨-, h20, h2r⟩ := hg2 k hk1 hQ j
  have a1 := abs_le.mp h1
  refine ⟨fun hj0 => ?_, fun r hr Hlt Hle hlt hle hj1 hj2 => ?_⟩
  · have a2 := abs_le.mp (h20 hj0)
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · have a2 := abs_le.mp (h2r r hr Hlt Hle hlt hle hj1 hj2)
    rw [abs_le]; constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

set_option maxHeartbeats 3200000 in
/-- **Target (3): `thm:eigtorus-l1`(i) in the file's form, for random samples.** Hypotheses of
    `kernel_theorem_G28` / `eig_l1_sample` (independent uniform points on the flat torus of dimension
    `d ≥ 1`, kernel of variance `σ ≤ 1`, self-loops, `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`,
    `kernelC1 d · δ' √K ≤ 1`). Except on an event of probability at most `5/N³`, for all `1 ≤ k ≤ K`,
    every shell `|n|² = r > 0` and every index `j` of the shell (from zero):
    `|s_j^k - e^{-k 2π²σ r}| ≤ eigL1C d · δ' √k + kernelQC d · √(log N/N) · m_k`,
    and `|s_0^k - 1| ≤` the same. The first term has NO factor `m_k`. -/
theorem eig_G44_i {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N K : ℕ) (hN2 : 2 ≤ N) (hK : 0 < K)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N))
    (hrange : kernelC1 d * δp * Real.sqrt K ≤ 1) :
    μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → |hS.eigenvalues₀ j ^ k - 1|
              ≤ EigenvaluesL1.eigL1C d * δp * Real.sqrt k
                + kernelQC d * Real.sqrt (Real.log N / N)
                  * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
          ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ EigenvaluesL1.eigL1C d * δp * Real.sqrt k
                + kernelQC d * Real.sqrt (Real.log N / N)
                  * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
      ≤ 5 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hN : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 + Real.sqrt (2 * Real.pi)) ^ d := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hA]; exact one_le_pow₀ (by linarith [Real.sqrt_nonneg (2 * Real.pi)])
  have hA0 : 0 ≤ A := by linarith
  have hC3nn := rateCfin3_nonneg d
  have hδp0 : 0 ≤ δp := by rw [hδp]; exact Real.sqrt_nonneg _
  obtain ⟨ML, hML⟩ : ∃ ML : ℝ, ML = (1 + Real.sqrt (Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d :=
    ⟨_, rfl⟩
  obtain ⟨Lip, hLip⟩ : ∃ Lip : ℝ, Lip = 2 * Real.pi * (2 / (2 * Real.pi ^ 2 * σ))
      * (1 + Real.sqrt (2 * Real.pi / (2 * Real.pi ^ 2 * σ))) ^ d := ⟨_, rfl⟩
  obtain ⟨δL, hδL⟩ : ∃ δL : ℝ, δL = Real.sqrt (ML * Real.log N / N) := ⟨_, rfl⟩
  have hδL0 : 0 ≤ δL := by rw [hδL]; exact Real.sqrt_nonneg _
  have hMp1 : 1 ≤ Mp := by rw [hMp]; exact heatTorus_zero_ge_one hcσ d
  have hMpML : Mp ≤ ML := by rw [hMp, hML]; exact heatTorus_le hcσ d 0
  have hMLA : ML ≤ A * Mp := by
    have h := heatMu_le_m hσ d 1 le_rfl (by simpa using hσ1)
    unfold heatMu heatM at h
    rw [if_neg one_ne_zero] at h
    simp only [Nat.cast_one, one_mul] at h
    rw [hML, hA, hMp]; exact h
  have hlg0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hδLle : δL ≤ A * δp := by
    have h1 : ML * Real.log N / N ≤ A ^ 2 * (Mp * Real.log N / N) := by
      have h2 : ML ≤ A ^ 2 * Mp := by nlinarith
      have h3 : 0 ≤ Real.log N / N := by positivity
      calc ML * Real.log N / N = ML * (Real.log N / N) := by ring
        _ ≤ A ^ 2 * Mp * (Real.log N / N) := mul_le_mul_of_nonneg_right h2 h3
        _ = A ^ 2 * (Mp * Real.log N / N) := by ring
    calc δL = Real.sqrt (ML * Real.log N / N) := hδL
      _ ≤ Real.sqrt (A ^ 2 * (Mp * Real.log N / N)) := Real.sqrt_le_sqrt h1
      _ = A * δp := by rw [Real.sqrt_mul (_root_.sq_nonneg A), Real.sqrt_sq hA0, hδp]
  have hC1 : kernelC1 d = rateCfin3 d * A ^ 2 := by unfold kernelC1; rw [hA]
  have hC1nn : 0 ≤ kernelC1 d := by rw [hC1]; positivity
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsK1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hK1
  have hsmallL : rateCfin3 d * δL * Real.sqrt K ≤ 1 := by
    have h1 : rateCfin3 d * δL ≤ rateCfin3 d * A ^ 2 * δp := by
      have h2 : A * δp ≤ A ^ 2 * δp := by nlinarith [mul_nonneg hA0 hδp0]
      have h3 := mul_le_mul_of_nonneg_left (hδLle.trans h2) hC3nn
      linarith
    have h4 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg (K : ℝ))
    rw [hC1] at hrange
    linarith
  have hCδL : rateCfin3 d * δL ≤ 1 := by
    have h1 : rateCfin3 d * δL ≤ rateCfin3 d * δL * Real.sqrt K :=
      le_mul_of_one_le_right (by positivity) hsK1
    linarith
  obtain ⟨hN12, hlg, hML1, hNbig, hLipc, h1σ, hCN⟩ :=
    g28_setup hσ d N hd hN2 hML hLip hδL hCδL
  have h2d : (2 : ℝ) ^ d ≤ N := (rateCfin3_ge d).2.trans hCN
  exact eig_G44_i_cond hσ d N K X h_indep hX hlaw hN12 h2d h1σ
    (EigenvaluesL1.eig_l1_sample hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hrange)


/-! ### Part (ii) of `thm:eigtorus-l1` from part (i) -/

open CTG.HeatTrace in
/-- From the `k`-th power to the eigenvalue, without the hypothesis `s ≤ 1`: if `0 ≤ s`,
    `a ∈ [0, 1]`, `|s^k - a^k| ≤ η` and `2η ≤ a^k`, then `k a^k |s - a| ≤ 2η`. -/
theorem pow_to_eig {s a η : ℝ} (hs0 : 0 ≤ s) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {k : ℕ} (hk : 1 ≤ k)
    (h : |s ^ k - a ^ k| ≤ η) (h3 : 2 * η ≤ a ^ k) :
    (k : ℝ) * (a ^ k * |s - a|) ≤ 2 * η := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hb := abs_le.mp h
  have hη0 : 0 ≤ η := (abs_nonneg _).trans h
  rcases le_total s 1 with hs1 | hs1
  · have r := eigenvalue_from_power (α := ℝ) hs0 hs1 ha0 ha1 k'
      (eta := η) (by rw [pw_eq, pw_eq]; linarith [hb.2])
      (by rw [pw_eq, pw_eq]; linarith [hb.1]) (by rw [pw_eq]; exact h3)
    rw [pw_eq, ncast_eq] at r
    rcases le_total a s with h' | h'
    · rw [abs_of_nonneg (sub_nonneg.mpr h')]; exact r.1
    · rw [abs_of_nonpos (sub_nonpos.mpr h'), neg_sub]; exact r.2
  · have has : a ≤ s := ha1.trans hs1
    have r := pw_diff_ge (α := ℝ) ha0 has k'
    simp only [pw_eq, ncast_eq] at r
    rw [abs_of_nonneg (sub_nonneg.mpr has)]
    have h1 : a ^ (k' + 1) ≤ a ^ k' := by
      rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg ha0 k') ha1
    have h2 : a ^ (k' + 1) * (s - a) ≤ a ^ k' * (s - a) :=
      mul_le_mul_of_nonneg_right h1 (sub_nonneg.mpr has)
    have h4 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (k' + 1))
    linarith [hb.2]

set_option maxHeartbeats 800000 in
/-- The arithmetic of part (ii): in the variables `s = 2π√r = √λ`, `ξ = √σ`, at a step `k` with
    `1/2 ≤ k · 2π²σ r ≤ 1` and with `m ≤ (1 + √(2π r))^d`, the right-hand side
    `η = C₈ δ' √k + C_Q L m` of part (i) satisfies `2η ≤ e^{-1}` and
    `2 e η/(k σ/2) ≤ 16 (C₈ + C_Q) [(δ'/ξ) s + L s^{d+2}]`, if
    `8 (C₈ + C_Q) [(δ'/ξ) s^{-1} + L s^d] ≤ 1`. -/
theorem g44_arith {C8 CQ δp Lg σ r m kk sk : ℝ} (d : ℕ) (hC8 : 0 ≤ C8) (hCQ : 0 ≤ CQ)
    (hδp0 : 0 ≤ δp) (hLg : 0 ≤ Lg) (hσ : 0 < σ) (hr : 1 ≤ r) (hkk : 0 < kk) (hsk : 0 ≤ sk)
    (hsk2 : sk * sk = kk) (hlo : 1 / 2 ≤ kk * (2 * Real.pi ^ 2 * σ) * r)
    (hhi : kk * (2 * Real.pi ^ 2 * σ) * r ≤ 1) (hm0 : 0 ≤ m)
    (hm : m ≤ (1 + Real.sqrt (2 * Real.pi * r)) ^ d)
    (hcond : 8 * (C8 + CQ) * (δp / Real.sqrt σ / (2 * Real.pi * Real.sqrt r)
        + Lg * (2 * Real.pi * Real.sqrt r) ^ d) ≤ 1) :
    2 * (C8 * δp * sk + CQ * Lg * m) ≤ Real.exp (-1)
      ∧ 2 * Real.exp 1 * (C8 * δp * sk + CQ * Lg * m) / (kk * (σ / 2))
        ≤ 16 * (C8 + CQ) * (δp / Real.sqrt σ * (2 * Real.pi * Real.sqrt r)
            + Lg * (2 * Real.pi * Real.sqrt r) ^ (d + 2)) := by
  have hpi := Real.pi_pos
  have hpi2 := Real.two_le_pi
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = Real.sqrt σ := ⟨_, rfl⟩
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.sqrt_pos.mpr hσ
  have hξξ : ξ * ξ = σ := by rw [hξ]; exact Real.mul_self_sqrt hσ.le
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt r := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by
    rw [hq, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hr
  have hqq : q * q = r := by rw [hq]; exact Real.mul_self_sqrt hr0
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 2 * Real.pi * q := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by
    have h := mul_le_mul hpi2 hq1 (by norm_num) hpi.le
    rw [hs]; linarith
  have hs0 : 0 < s := by linarith
  rw [← hξ, ← hq, ← hs] at hcond ⊢
  have hm' : m ≤ s ^ d := by
    refine hm.trans (pow_le_pow_left₀ (by positivity) ?_ d)
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = Real.sqrt (2 * Real.pi) := ⟨_, rfl⟩
    have hww : w * w = 2 * Real.pi := by rw [hw]; exact Real.mul_self_sqrt (by positivity)
    have hw0 : 0 ≤ w := by rw [hw]; exact Real.sqrt_nonneg _
    have hw2 : 2 ≤ w := by
      by_contra h'
      have h := not_le.mp h'
      have := mul_lt_mul'' h h hw0 hw0
      linarith
    have e : Real.sqrt (2 * Real.pi * r) = w * q := by
      rw [hw, hq, ← Real.sqrt_mul (by positivity)]
    have h1 : 2 ≤ w * q := by
      have h := mul_le_mul hw2 hq1 (by norm_num) hw0
      linarith
    have h2 : 2 * (w * q) ≤ w * (w * q) := mul_le_mul_of_nonneg_right hw2 (by linarith)
    rw [e, hs, ← hww]
    linarith [h1, h2]
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = sk * ξ * s := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy2 : y * y ≤ 2 := by
    have e : y * y = 2 * (kk * (2 * Real.pi ^ 2 * σ) * r) := by
      rw [hy, hs, ← hsk2, ← hξξ, ← hqq]; ring
    linarith
  have hy142 : y ≤ 1.42 := by
    by_contra h'
    have h := not_le.mp h'
    have := mul_lt_mul'' h h (by norm_num) (by norm_num)
    norm_num at this
    linarith
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = δp / ξ / s := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hδsk : δp * sk = U * y := by rw [hU, hy]; field_simp
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = Lg * s ^ d := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  have hLm : Lg * m ≤ V := by rw [hV]; exact mul_le_mul_of_nonneg_left hm' hLg
  rw [← hU, ← hV] at hcond
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = C8 * δp * sk + CQ * Lg * m := ⟨_, rfl⟩
  have a1 : 0 ≤ C8 * U := mul_nonneg hC8 hU0
  have a2 : 0 ≤ CQ * V := mul_nonneg hCQ hV0
  have a3 : 0 ≤ C8 * V := mul_nonneg hC8 hV0
  have a4 : 0 ≤ CQ * U := mul_nonneg hCQ hU0
  have hη0 : 0 ≤ η := by
    rw [hη]
    have := mul_nonneg (mul_nonneg hC8 hδp0) hsk
    have := mul_nonneg (mul_nonneg hCQ hLg) hm0
    linarith
  have hηle : η ≤ 1.42 * (C8 * U) + CQ * V := by
    have h0 : δp * sk ≤ 1.42 * U := by
      rw [hδsk]; linarith [mul_le_mul_of_nonneg_left hy142 hU0]
    have h1 := mul_le_mul_of_nonneg_left h0 hC8
    have h2 := mul_le_mul_of_nonneg_left hLm hCQ
    have e : C8 * δp * sk + CQ * Lg * m = C8 * (δp * sk) + CQ * (Lg * m) := by ring
    rw [hη, e]
    linarith [h1, h2]
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hG : 2 * Real.exp 1 * η ≤ 8 * (C8 + CQ) * (U + V) := by
    have b0 : 0 ≤ 1.42 * (C8 * U) + CQ * V := by linarith
    have b1 : Real.exp 1 * η ≤ 2.7182818286 * (1.42 * (C8 * U) + CQ * V) :=
      (mul_le_mul_of_nonneg_left hηle he0.le).trans (mul_le_mul_of_nonneg_right he.le b0)
    linarith [b1, a1, a2, a3, a4]
  rw [← hη]
  refine ⟨?_, ?_⟩
  · have h1 : 2 * η * Real.exp 1 ≤ 1 := by linarith
    have he1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    by_contra hc'
    have hc := not_le.mp hc'
    have := mul_lt_mul_of_pos_right hc he0
    linarith
  · rw [div_le_iff₀ (by positivity)]
    have hks : 1 / 2 ≤ s ^ 2 * (kk * (σ / 2)) := by
      have e : s ^ 2 * (kk * (σ / 2)) = kk * (2 * Real.pi ^ 2 * σ) * r := by
        rw [hs, ← hqq]; ring
      linarith
    have e2 : δp / ξ * s + Lg * s ^ (d + 2) = (U + V) * s ^ 2 := by
      rw [hU, hV]; field_simp; ring
    rw [e2]
    have hT : 0 ≤ 16 * (C8 + CQ) * (U + V) := by
      have : 0 ≤ (C8 + CQ) * (U + V) := mul_nonneg (by linarith) (by linarith)
      linarith
    have h5 := mul_le_mul_of_nonneg_left hks hT
    have e5 : 16 * (C8 + CQ) * ((U + V) * s ^ 2) * (kk * (σ / 2))
        = 16 * (C8 + CQ) * (U + V) * (s ^ 2 * (kk * (σ / 2))) := by ring
    rw [e5]
    linarith [h5, hG]

/-- The range of part (i) from the size condition: `(C₁ δ')² ≤ 2π²σ r`. -/
theorem g44_range {C1 C8 CQ δp Lg σ r : ℝ} (d : ℕ) (hC1 : 0 ≤ C1) (hC8 : 0 ≤ C8) (hCQ : 0 ≤ CQ)
    (hδp0 : 0 ≤ δp) (hLg : 0 ≤ Lg) (hσ : 0 < σ) (hr : 1 ≤ r)
    (hcond : 8 * (C1 + C8 + CQ) * (δp / Real.sqrt σ / (2 * Real.pi * Real.sqrt r)
        + Lg * (2 * Real.pi * Real.sqrt r) ^ d) ≤ 1) :
    (C1 * δp) ^ 2 ≤ (2 * Real.pi ^ 2 * σ) * r
      ∧ 8 * (C8 + CQ) * (δp / Real.sqrt σ / (2 * Real.pi * Real.sqrt r)
        + Lg * (2 * Real.pi * Real.sqrt r) ^ d) ≤ 1 := by
  have hpi := Real.pi_pos
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨ξ, hξ⟩ : ∃ ξ : ℝ, ξ = Real.sqrt σ := ⟨_, rfl⟩
  have hξ0 : 0 < ξ := by rw [hξ]; exact Real.sqrt_pos.mpr hσ
  have hξξ : ξ * ξ = σ := by rw [hξ]; exact Real.mul_self_sqrt hσ.le
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = Real.sqrt r := ⟨_, rfl⟩
  have hq1 : 1 ≤ q := by
    rw [hq, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hr
  have hqq : q * q = r := by rw [hq]; exact Real.mul_self_sqrt hr0
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 2 * Real.pi * q := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; positivity
  rw [← hξ, ← hq, ← hs] at hcond ⊢
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = δp / ξ / s := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = Lg * s ^ d := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  rw [← hU, ← hV] at hcond ⊢
  have a1 : 0 ≤ C1 * U := mul_nonneg hC1 hU0
  have a2 : 0 ≤ C1 * V := mul_nonneg hC1 hV0
  have a3 : 0 ≤ C8 * U := mul_nonneg hC8 hU0
  have a4 : 0 ≤ C8 * V := mul_nonneg hC8 hV0
  have a5 : 0 ≤ CQ * U := mul_nonneg hCQ hU0
  have a6 : 0 ≤ CQ * V := mul_nonneg hCQ hV0
  refine ⟨?_, by nlinarith⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = C1 * U := ⟨_, rfl⟩
  have hz0 : 0 ≤ z := by rw [hz]; exact a1
  have hz8 : z ≤ 1 / 8 := by rw [hz]; nlinarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ξ * s := ⟨_, rfl⟩
  have e : C1 * δp = z * t := by rw [hz, ht, hU]; field_simp
  have htt : t * t = 2 * ((2 * Real.pi ^ 2 * σ) * r) := by
    rw [ht, hs, ← hξξ, ← hqq]; ring
  have hzz : z * z ≤ 1 / 64 := by nlinarith
  have h1 : z * z * (t * t) ≤ 1 / 64 * (t * t) :=
    mul_le_mul_of_nonneg_right hzz (mul_self_nonneg t)
  rw [e]
  nlinarith

/-- **Part (i) ⇒ part (ii), deterministic step.** `s ≥ 0` a number (an eigenvalue of `S`), `r ≥ 1`
    a shell with `2π²σ r ≤ 1/2` (that is `λ = 4π² r ≤ ξ^{-2}`, `σ = ξ²`).
    HYPOTHESIS `hI`: part (i) for `s`, for all `1 ≤ k ≤ K`, with right-hand side
    `C₈ δ' √k + C_Q L m_k`. HYPOTHESIS `hKr`: every `k` with `k · 2π²σ r ≤ 1` is at most `K`.
    If `8 (C₈ + C_Q) [(δ'/ξ) λ^{-1/2} + L λ^{d/2}] ≤ 1`, then
    `|(1 - s)/(σ/2) - (1 - e^{-2π²σ r})/(σ/2)| ≤ 16 (C₈ + C_Q) [(δ'/ξ) λ^{1/2} + L λ^{(d+2)/2}]`. -/
theorem g44_step {s σ r δp Lg C8 CQ : ℝ} (d K : ℕ) (hs0 : 0 ≤ s) (hσ : 0 < σ) (hr : 1 ≤ r)
    (hx : (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2) (hC8 : 0 ≤ C8) (hCQ : 0 ≤ CQ)
    (hδp0 : 0 ≤ δp) (hLg : 0 ≤ Lg)
    (hKr : ∀ k : ℕ, (k : ℝ) * ((2 * Real.pi ^ 2 * σ) * r) ≤ 1 → k ≤ K)
    (hI : ∀ k : ℕ, 1 ≤ k → k ≤ K →
      |s ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
        ≤ C8 * δp * Real.sqrt k + CQ * Lg * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
    (hcond : 8 * (C8 + CQ) * (δp / Real.sqrt σ / (2 * Real.pi * Real.sqrt r)
        + Lg * (2 * Real.pi * Real.sqrt r) ^ d) ≤ 1) :
    |(1 - s) / (σ / 2) - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
      ≤ 16 * (C8 + CQ) * (δp / Real.sqrt σ * (2 * Real.pi * Real.sqrt r)
          + Lg * (2 * Real.pi * Real.sqrt r) ^ (d + 2)) := by
  have hpi := Real.pi_pos
  have hr0 : 0 < r := by linarith
  have hx0 : 0 < (2 * Real.pi ^ 2 * σ) * r := by positivity
  obtain ⟨k, hk2, hlo, hhi⟩ := exists_step hx0 hx
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hkK := hKr k hhi
  have hi := hI k hk1 hkK
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = Real.exp (-(2 * Real.pi ^ 2 * σ) * r) := ⟨_, rfl⟩
  rw [← hα] at hi ⊢
  have hα0 : 0 ≤ α := by rw [hα]; exact (Real.exp_pos _).le
  have hα1 : α ≤ 1 := by rw [hα]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hαk : Real.exp (-1) ≤ α ^ k := by
    rw [hα, ← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hc : 0 < 2 * Real.pi ^ 2 * ((k : ℝ) * σ) := by positivity
  have hm0 : 0 ≤ heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0 := (heatTorus_pos hc d 0).le
  have hm : heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0
      ≤ (1 + Real.sqrt (2 * Real.pi * r)) ^ d := by
    have h1 := heatTorus_le hc d 0
    have h2 := heatMu_le_shell hσ hr0 d k hk1 (by linarith)
    unfold heatMu heatM at h2
    rw [if_neg (by omega)] at h2
    exact h1.trans h2
  obtain ⟨hA, hB⟩ := g44_arith d hC8 hCQ hδp0 hLg hσ hr hkpos (Real.sqrt_nonneg (k : ℝ))
    (Real.mul_self_sqrt hkpos.le) (by linarith) (by linarith) hm0 hm hcond
  have hp := pow_to_eig hs0 hα0 hα1 hk1 hi (hA.trans hαk)
  have hl := lambda_from_power (by omega : 0 < k) (by positivity : 0 < σ / 2) hαk hp
  exact hl.trans hB

/-- **`thm:eigtorus-l1`(ii) for samples, conditional on part (i).** HYPOTHESIS `hI`: the
    conclusion of `eig_G44_i` (part (i) with constants `C₈`, `C_Q`, exceptional probability
    `5/N³`) for every `K ≥ 1` with `kernelC1 d · δ' √K ≤ 1`. The number of steps is chosen inside,
    `K = ⌊(kernelC1 d · δ')^{-2}⌋`, so that the exceptional event is the one of part (i) for this
    `K`. -/
theorem eig_G44_ii_cond {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (d N : ℕ)
    (X : ℕ → Ω → FlatTorus d) {δp C8 CQ : ℝ} (hδp0 : 0 < δp) (hC8 : 0 ≤ C8) (hCQ : 0 ≤ CQ)
    (hI : ∀ K : ℕ, 0 < K → kernelC1 d * δp * Real.sqrt K ≤ 1 →
      μ.real {ω | ¬ ∀ k, 1 ≤ k → k ≤ K →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))),
          (j.val = 0 → |hS.eigenvalues₀ j ^ k - 1|
              ≤ C8 * δp * Real.sqrt k + CQ * Real.sqrt (Real.log N / N)
                  * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0)
          ∧ ∀ r : ℝ, 0 < r → ∀ Hlt Hle : Finset (Fin d → ℤ),
            (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
            (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
            1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
            |hS.eigenvalues₀ j ^ k - Real.exp (-(2 * Real.pi ^ 2 * σ) * r) ^ k|
              ≤ C8 * δp * Real.sqrt k + CQ * Real.sqrt (Real.log N / N)
                  * heatTorus d (2 * Real.pi ^ 2 * ((k : ℝ) * σ)) 0}
        ≤ 5 / (N : ℝ) ^ 3) :
    μ.real {ω | ¬ ∀ r : ℝ, 1 ≤ r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
        8 * (kernelC1 d + C8 + CQ) * (δp / Real.sqrt σ / (2 * Real.pi * Real.sqrt r)
          + Real.sqrt (Real.log N / N) * (2 * Real.pi * Real.sqrt r) ^ d) ≤ 1 →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))) (Hlt Hle : Finset (Fin d → ℤ)),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ 16 * (C8 + CQ) * (δp / Real.sqrt σ * (2 * Real.pi * Real.sqrt r)
                + Real.sqrt (Real.log N / N) * (2 * Real.pi * Real.sqrt r) ^ (d + 2))}
      ≤ 5 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hC1 : 0 < kernelC1 d := by
    have h := (rateCfin3_ge d).2
    have h2 : (0 : ℝ) < 2 ^ d := by positivity
    unfold kernelC1
    have h3 : 0 < rateCfin3 d := by linarith
    positivity
  have hLg : 0 ≤ Real.sqrt (Real.log N / N) := Real.sqrt_nonneg _
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = kernelC1 d * δp := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc2 : 0 < c ^ 2 := by positivity
  by_cases hE : c ^ 2 ≤ 1 / 2
  swap
  · -- no shell satisfies the conditions
    have h5 : (0 : ℝ) ≤ 5 / (N : ℝ) ^ 3 := by positivity
    refine le_trans (measureReal_mono (s₂ := ∅) ?_ (measure_ne_top μ _)) (by simpa using h5)
    intro ω hω
    exfalso
    apply hω
    intro r hr1 hx hcond
    exfalso
    apply hE
    have h := (g44_range d hC1.le hC8 hCQ hδp0.le hLg hσ hr1 hcond).1
    rw [← hc] at h
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌊1 / c ^ 2⌋₊ := ⟨_, rfl⟩
  have hK2 : 2 ≤ K := by
    rw [hK]; apply Nat.le_floor
    rw [le_div_iff₀ hc2]; push_cast; linarith
  have hKle : (K : ℝ) ≤ 1 / c ^ 2 := by rw [hK]; exact Nat.floor_le (by positivity)
  have hKc : (K : ℝ) * c ^ 2 ≤ 1 := by rwa [le_div_iff₀ hc2] at hKle
  have hrange : kernelC1 d * δp * Real.sqrt K ≤ 1 := by
    rw [← hc]
    have hsq : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (Nat.cast_nonneg K)
    have h0 : 0 ≤ c * Real.sqrt K := by positivity
    have h1 : (c * Real.sqrt K) * (c * Real.sqrt K) ≤ 1 := by
      have e : (c * Real.sqrt K) * (c * Real.sqrt K) = (Real.sqrt K * Real.sqrt K) * c ^ 2 := by
        ring
      rw [e, hsq]; exact hKc
    nlinarith
  have hbad := hI K (by omega) hrange
  refine le_trans (measureReal_mono ?_ (measure_ne_top μ _)) hbad
  intro ω hω
  by_contra hgm
  have hg := not_not.mp hgm
  apply hω
  intro r hr1 hx hcond hS j Hlt Hle hlt hle hj1 hj2
  obtain ⟨hrg, hcond'⟩ := g44_range d hC1.le hC8 hCQ hδp0.le hLg hσ hr1 hcond
  rw [← hc] at hrg
  have hs0 : 0 ≤ hS.eigenvalues₀ j :=
    symGraph_eig_nonneg _ _
      (fun y => heatTorus_quadform_nonneg hcσ d (fun a : Fin N => X a ω) y) hS j
  refine g44_step d K hs0 hσ hr1 hx hC8 hCQ hδp0.le hLg ?_ ?_ hcond'
  · intro k hk
    rw [hK]; apply Nat.le_floor
    rw [le_div_iff₀ hc2]
    have h1 := mul_le_mul_of_nonneg_left hrg (Nat.cast_nonneg (α := ℝ) k)
    linarith
  · intro k hk1 hkK
    exact (hg k hk1 hkK hS j).2 r (by linarith) Hlt Hle hlt hle hj1 hj2

/-- The constant `C₉` of the size condition of part (ii); it depends only on `d`. -/
noncomputable def eigC9 (d : ℕ) : ℝ := 8 * (kernelC1 d + EigenvaluesL1.eigL1C d + kernelQC d)

/-- The constant `C₁₀` of the bound of part (ii); it depends only on `d`. -/
noncomputable def eigC10 (d : ℕ) : ℝ := 16 * (EigenvaluesL1.eigL1C d + kernelQC d)

/-- **`thm:eigtorus-l1`(ii) in the file's form, for random samples.** Independent uniform points
    on the flat torus of dimension `d ≥ 1`, periodised Gaussian kernel of variance `σ = ξ² ≤ 1`,
    graph with self-loops, `N ≥ 2`, `M = p_σ(0)`, `δ' = √(M log N/N)`. Except on an event of
    probability at most `5/N³` (the event of `eig_G44_i` for `K = ⌊(kernelC1 d · δ')^{-2}⌋`), for
    every shell `|n|² = r ≥ 1` with `λ = 4π² r ≤ ξ^{-2}` (that is `2π²σ r ≤ 1/2`) and
    `C₉ [(δ'/ξ) λ^{-1/2} + √(log N/N) λ^{d/2}] ≤ 1`, and every index `j` of the shell (from zero):
    `|λ_j^N - (1 - e^{-(ξ²/2) λ})/(ξ²/2)| ≤ C₁₀ [(δ'/ξ) λ^{1/2} + √(log N/N) λ^{(d+2)/2}]`,
    with `√λ = 2π√r`. The first term has NO factor `λ^{d/2}`. No further hypothesis. -/
theorem eig_G44_ii {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (X : ℕ → Ω → FlatTorus d) (h_indep : iIndepFun X μ) (hX : ∀ j, Measurable (X j))
    (hlaw : ∀ j, μ.map (X j) = flatTorusMeasure d) (N : ℕ) (hN2 : 2 ≤ N)
    {Mp δp : ℝ} (hMp : Mp = heatTorus d (2 * Real.pi ^ 2 * σ) 0)
    (hδp : δp = Real.sqrt (Mp * Real.log N / N)) :
    μ.real {ω | ¬ ∀ r : ℝ, 1 ≤ r → (2 * Real.pi ^ 2 * σ) * r ≤ 1 / 2 →
        eigC9 d * (δp / Real.sqrt σ / (2 * Real.pi * Real.sqrt r)
          + Real.sqrt (Real.log N / N) * (2 * Real.pi * Real.sqrt r) ^ d) ≤ 1 →
        ∀ (hS : (symGraph
              (fun a j : Fin N => heatTorus d (2 * Real.pi ^ 2 * σ) (X a ω - X j ω))
              (fun a : Fin N => heatRho d σ N (fun j => X j ω) a)).IsHermitian)
          (j : Fin (Fintype.card (Fin N))) (Hlt Hle : Finset (Fin d → ℤ)),
          (∀ n, n ∈ Hlt ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 < r) →
          (∀ n, n ∈ Hle ↔ lexPos d n ∧ ∑ i, ((n i : ℤ) : ℝ) ^ 2 ≤ r) →
          1 + 2 * Hlt.card ≤ j.val → j.val ≤ 2 * Hle.card →
          |(1 - hS.eigenvalues₀ j) / (σ / 2)
              - (1 - Real.exp (-(2 * Real.pi ^ 2 * σ) * r)) / (σ / 2)|
            ≤ eigC10 d * (δp / Real.sqrt σ * (2 * Real.pi * Real.sqrt r)
                + Real.sqrt (Real.log N / N) * (2 * Real.pi * Real.sqrt r) ^ (d + 2))}
      ≤ 5 / (N : ℝ) ^ 3 := by
  have hpi := Real.pi_pos
  have hcσ : 0 < 2 * Real.pi ^ 2 * σ := by positivity
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hMp1 : 1 ≤ Mp := by rw [hMp]; exact heatTorus_zero_ge_one hcσ d
  have hlg : 0 < Real.log N := Real.log_pos (by linarith)
  have hδpos : 0 < δp := by
    rw [hδp]
    exact Real.sqrt_pos.mpr (div_pos (mul_pos (by linarith) hlg) hNpos)
  have hC8 : 0 ≤ EigenvaluesL1.eigL1C d := by
    have h1 := TorusReductionL1.normC_nonneg d
    have h2 := TorusReductionL1.h4C_nonneg d
    unfold EigenvaluesL1.eigL1C
    linarith
  have hCQ : 0 ≤ kernelQC d := by unfold kernelQC; positivity
  unfold eigC9 eigC10
  exact eig_G44_ii_cond hσ d N X hδpos hC8 hCQ
    (fun K hK hr => eig_G44_i hσ hσ1 d hd X h_indep hX hlaw N K hN2 hK hMp hδp hr)


end KernelMatrix

end CTG.Reals2
